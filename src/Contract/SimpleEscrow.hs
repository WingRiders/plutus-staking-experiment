{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS -fplugin-opt Language.PlutusTx.Plugin:debug-context #-}

-- | This simple escrow contract (from plutus-apps)
module Contract.SimpleEscrow where

import           Control.Lens              (makeClassyPrisms, view)
import           Control.Monad             (void)
import           Control.Monad.Error.Lens  (throwing)
import           Data.Aeson                (FromJSON, ToJSON)
import           GHC.Generics              (Generic)
import           Ledger                    (Address (..),
                                            PaymentPubKeyHash (unPaymentPubKeyHash),
                                            getCardanoTxId, txSignedBy,
                                            valuePaidTo)
import qualified Ledger.Constraints        as Constraints
import           Ledger.Interval           (after, before)
import qualified Ledger.Interval           as Interval
import qualified Ledger.Tx                 as Tx
import qualified Ledger.Typed.Scripts      as Scripts
import           Ledger.Value              (geq)
import           Plutus.Contract
import qualified Plutus.Contract.Typed.Tx  as Typed
import           Plutus.V1.Ledger.Api
import qualified Plutus.V1.Ledger.Contexts as Validation
import qualified PlutusTx
import           PlutusTx.Prelude          hiding (Applicative (..),
                                            Semigroup (..), check, foldMap)
import           PlutusTx.Prelude          (check)
import           Prelude                   (Semigroup (..), foldMap)
import qualified Prelude                   as Haskell

data EscrowParams = EscrowParams
  { -- | The entity that needs to be paid the 'expecting' 'Value'.
    payee     :: PaymentPubKeyHash,
    -- | Value to be paid out to the redeemer.
    paying    :: Value,
    -- | Value to be received by the payee.
    expecting :: Value,
    -- | Time after which the contract expires.
    deadline  :: POSIXTime
  }
  deriving stock (Haskell.Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

type EscrowSchema =
  Endpoint "lock" EscrowParams
    .\/ Endpoint "refund" EscrowParams
    .\/ Endpoint "redeem" EscrowParams

data Action
  = Redeem
  | Refund

data RedeemFailReason = DeadlinePassed
  deriving stock (Haskell.Eq, Haskell.Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

data EscrowError
  = RedeemFailed RedeemFailReason
  | RefundFailed
  | EContractError ContractError
  deriving stock (Haskell.Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

makeClassyPrisms ''EscrowError

instance AsContractError EscrowError where
  _ContractError = _EContractError

newtype RefundSuccess = RefundSuccess TxId
  deriving newtype (Haskell.Eq, Haskell.Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

newtype RedeemSuccess = RedeemSuccess TxId
  deriving (Haskell.Eq, Haskell.Show)

data Escrow

instance Scripts.ValidatorTypes Escrow where
  type RedeemerType Escrow = Action
  type DatumType Escrow = EscrowParams

escrowAddress :: Ledger.Address
escrowAddress = Scripts.validatorAddress escrowInstance

escrowInstance :: Scripts.TypedValidator Escrow
escrowInstance =
  Scripts.mkTypedValidator @Escrow
    $$(PlutusTx.compile [||validate||])
    $$(PlutusTx.compile [||wrap||])
  where
    wrap = Scripts.wrapValidator @EscrowParams @Action

{-# INLINEABLE validate #-}
validate :: EscrowParams -> Action -> ScriptContext -> Bool
validate params action ScriptContext {scriptContextTxInfo = txInfo} =
  case action of
    Redeem ->
      -- Can't redeem after the deadline
      let notLapsed = deadline params `after` txInfoValidRange txInfo
          -- Payee has to have been paid
          paid = valuePaidTo txInfo (unPaymentPubKeyHash $ payee params) `geq` expecting params
       in traceIfFalse "escrow-deadline-lapsed" notLapsed
            && traceIfFalse "escrow-not-paid" paid
    Refund ->
      -- Has to be the person that locked value requesting the refund
      let signed = txInfo `txSignedBy` unPaymentPubKeyHash (payee params)
          -- And we only refund after the deadline has passed
          lapsed = (deadline params - 1) `before` txInfoValidRange txInfo
       in traceIfFalse "escrow-not-signed" signed
            && traceIfFalse "refund-too-early" lapsed

-- Staking rewards script
type WrappedStakeValidatorType = BuiltinData -> BuiltinData -> ()

{-# INLINEABLE wrapStakeValidator #-}
wrapStakeValidator ::
  PlutusTx.UnsafeFromData r =>
  (r -> Validation.ScriptContext -> Bool) ->
  WrappedStakeValidatorType
wrapStakeValidator f r p = check $ f (unsafeFromBuiltinData r) (unsafeFromBuiltinData p)

-- | A stake validator that checks whether the validator script was run
--   in the right transaction.
mkForwardingStakeValidator :: ValidatorHash -> StakeValidator
mkForwardingStakeValidator vshsh =
  mkStakeValidatorScript $
    $$(PlutusTx.compile [||\(hsh :: ValidatorHash) -> wrapStakeValidator (forwardToValidator hsh)||])
      `PlutusTx.applyCode` PlutusTx.liftCode vshsh

{-# INLINEABLE forwardToValidator #-}
forwardToValidator :: ValidatorHash -> () -> ScriptContext -> Bool
forwardToValidator h _ ScriptContext {scriptContextTxInfo = TxInfo {txInfoOutputs}, scriptContextPurpose} =
  let checkHash TxOut {txOutAddress = Address {addressCredential = ScriptCredential vh}} = vh == h
      checkHash _ = False
      result = all checkHash txInfoOutputs
   in case scriptContextPurpose of
        Rewarding _  -> result
        Certifying _ -> result
        _            -> False

-- Offchain

-- | Lock the 'paying' 'Value' in the output of this script, with the
-- requirement that the transaction validates before the 'deadline'.
lockEp :: Promise () EscrowSchema EscrowError ()
lockEp = endpoint @"lock" $ \params -> do
  let valRange = Interval.to (Haskell.pred $ deadline params)
      tx =
        Constraints.mustPayToTheScript params (paying params)
          <> Constraints.mustValidateIn valRange
  void $
    mkTxConstraints (Constraints.typedValidatorLookups escrowInstance) tx
      >>= submitUnbalancedTx . Constraints.adjustUnbalancedTx

-- | Attempts to redeem the 'Value' locked into this script by paying in from
-- the callers address to the payee.
redeemEp :: Promise () EscrowSchema EscrowError RedeemSuccess
redeemEp = endpoint @"redeem" redeem
  where
    redeem params = do
      time <- currentTime
      pk <- ownPaymentPubKeyHash
      unspentOutputs <- utxosAt escrowAddress

      let value = foldMap (view Tx.ciTxOutValue) unspentOutputs
          tx =
            Typed.collectFromScript unspentOutputs Redeem
              <> Constraints.mustValidateIn (Interval.to (Haskell.pred $ deadline params))
              -- Pay me the output of this script
              <> Constraints.mustPayToPubKey pk value
              -- Pay the payee their due
              <> Constraints.mustPayToPubKey (payee params) (expecting params)

      if time >= deadline params
        then throwing _RedeemFailed DeadlinePassed
        else do
          utx <-
            Constraints.adjustUnbalancedTx
              <$> mkTxConstraints
                ( Constraints.typedValidatorLookups escrowInstance
                    <> Constraints.unspentOutputs unspentOutputs
                )
                tx
          RedeemSuccess . getCardanoTxId <$> submitUnbalancedTx utx

-- | Refunds the locked amount back to the 'payee'.
refundEp :: Promise () EscrowSchema EscrowError RefundSuccess
refundEp = endpoint @"refund" refund
  where
    refund params = do
      unspentOutputs <- utxosAt escrowAddress

      let tx =
            Typed.collectFromScript unspentOutputs Refund
              <> Constraints.mustValidateIn (Interval.from (deadline params))

      if Constraints.modifiesUtxoSet tx
        then do
          utx <-
            Constraints.adjustUnbalancedTx
              <$> mkTxConstraints
                ( Constraints.typedValidatorLookups escrowInstance
                    <> Constraints.unspentOutputs unspentOutputs
                )
                tx
          RefundSuccess . getCardanoTxId <$> submitUnbalancedTx utx
        else throwing _RefundFailed ()

PlutusTx.unstableMakeIsData ''EscrowParams
PlutusTx.makeLift ''EscrowParams
PlutusTx.unstableMakeIsData ''Action
PlutusTx.makeLift ''Action
