-- Voting contract implemented using the [[Plutus]] interface.
-- This is the fully parallel version that collects all contributions
-- in a single transaction.
--
-- Note [Transactions in the voting campaign] explains the structure of
-- this contract on the blockchain.

import Control.Applicative (Applicative (pure))
import Control.Monad (void)
import Data.Default (Default (def))
import Data.Text (Text)
import Ledger (POSIXTime, POSIXTimeRange, PaymentPubKeyHash (unPaymentPubKeyHash), PubKeyHash, ScriptContext (..), TxInfo (..),
               Validator, getCardanoTxId)
import Ledger qualified
import Ledger.Contexts qualified as V
import Ledger.Interval qualified as Interval
import Ledger.Scripts qualified as Scripts
import Ledger.TimeSlot qualified as TimeSlot
import Ledger.Typed.Scripts qualified as Scripts hiding (validatorHash)
import Ledger.Value (Value)
import Playground.Contract
import Plutus.Contract
import Plutus.Contract.Constraints qualified as Constraints
import Plutus.Contract.Typed.Tx qualified as Typed
import PlutusTx qualified
import PlutusTx.Prelude hiding (Applicative (..), Semigroup (..))
import Prelude (Semigroup (..))
import Prelude qualified as Haskell
import Wallet.Emulator qualified as Emulator

-- | A voting campaign.
data Election = Election
    { electionDeadline           :: POSIXTime
    -- ^ The date by which the campaign funds can be contributed.
    , electionCollectionDeadline :: POSIXTime
    -- ^ The date by which the campaign owner has to collect the funds
    , candidate              :: PaymentPubKeyHash
    -- ^ Public key of the campaign owner. This key is entitled to retrieve the
    --   funds if the campaign is successful.
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''Election

-- | Action that can be taken by the participants in this contract. A value of
--   `ElectionAction` is provided as the redeemer. The validator script then
--   checks if the conditions for performing this action are met.
--
data ElectionAction = Collect | Refund

PlutusTx.unstableMakeIsData ''ElectionAction
PlutusTx.makeLift ''ElectionAction

type VoteSchema =
        Endpoint "schedule collection" ()
        .\/ Endpoint "vote" Vote

data Vote = Vote
        { voteValue :: Value
        , vote_Candidate :: PubKeyHash
        -- ^ how much to vote
        } deriving stock (Haskell.Eq, Show, Generic)
          deriving anyclass (ToJSON, FromJSON, ToSchema)

-- | Construct a 'Election' value from the campaign parameters,
--   using the wallet's public key.
mkElection :: POSIXTime -> POSIXTime -> Wallet -> Election
mkElection ddl collectionDdl ownerWallet =
    Election
        { electionDeadline = ddl
        , electionCollectionDeadline = collectionDdl
        , candidate = Emulator.mockWalletPaymentPubKeyHash ownerWallet
        }

-- | The 'POSIXTimeRange' during which the funds can be collected
collectionRange :: Election -> POSIXTimeRange
collectionRange vt =
    Interval.interval (electionDeadline vt) (electionCollectionDeadline vt - 1)

-- | The 'POSIXTimeRange' during which a refund may be claimed
refundRange :: Election -> POSIXTimeRange
refundRange vt =
    Interval.from (electionCollectionDeadline vt)

data Voting
instance Scripts.ValidatorTypes Voting where
    type instance RedeemerType Voting = ElectionAction
    type instance DatumType Voting = PaymentPubKeyHash

typedValidator :: Election -> Scripts.TypedValidator Voting
typedValidator = Scripts.mkTypedValidatorParam @Voting
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator

{-# INLINABLE validRefund #-}
validRefund :: Election -> PaymentPubKeyHash -> TxInfo -> Bool
validRefund campaign citizen txinfo =
    -- Check that the transaction falls in the refund range of the campaign
    (refundRange campaign `Interval.contains` txInfoValidRange txinfo)
    -- Check that the transaction is signed by the citizen
    && (txinfo `V.txSignedBy` unPaymentPubKeyHash citizen)

validCollection :: Election -> TxInfo -> Bool
validCollection campaign txinfo =
    -- Check that the transaction falls in the collection range of the campaign
    (collectionRange campaign `Interval.contains` txInfoValidRange txinfo)
    -- Check that the transaction is signed by the campaign owner
    && (txinfo `V.txSignedBy` unPaymentPubKeyHash (candidate campaign))

mkValidator :: Election -> PaymentPubKeyHash -> ElectionAction -> ScriptContext -> Bool
mkValidator c con act p = case act of
    -- the "refund" branch
    Refund  -> validRefund c con (scriptContextTxInfo p)
    -- the "collection" branch
    Collect -> validCollection c (scriptContextTxInfo p)

-- | The validator script that determines whether the campaign owner can
--   retrieve the funds or the contributors can claim a refund.
--
votingScript :: Election -> Validator
votingScript = Scripts.validatorScript . typedValidator

-- | The address of a [[Election]]
electionAddress :: Election -> Ledger.ValidatorHash
electionAddress = Scripts.validatorHash . votingScript

-- | The voting contract for the 'Election'.
voting :: AsContractError e => Election -> Contract () VoteSchema e ()
voting c = selectList [vote c, scheduleCollection c]

-- | A sample campaign
theElection :: POSIXTime -> Election
theElection startTime = Election
    { electionDeadline = startTime + 40000
    , electionCollectionDeadline = startTime + 60000
    , candidate = Emulator.mockWalletPaymentPubKeyHash (Emulator.knownWallet 1)
    }

vote :: AsContractError e => Election -> Promise () VoteSchema e ()
vote vt = endpoint @"vote" $ \Vote{voteValue,vote_Candidate} -> do
    citizen <- ownPaymentPubKeyHash
    let inst = typedValidator vt
        tx = Constraints.mustPayToTheScript citizen voteValue
                <> Constraints.mustValidateIn (Interval.to (electionDeadline vt))
    txid <- fmap getCardanoTxId $ mkTxConstraints (Constraints.typedValidatorLookups inst) tx
        >>= submitUnbalancedTx . Constraints.adjustUnbalancedTx

    utxo <- watchAddressUntilTime (Scripts.validatorAddress inst) (electionCollectionDeadline vt)

    let flt Ledger.TxOutRef{txOutRefId} _ = txid Haskell.== txOutRefId
        tx' = Typed.collectFromScriptFilter flt utxo Refund
                <> Constraints.mustValidateIn (refundRange vt)
                <> Constraints.mustBeSignedBy citizen
    if Constraints.modifiesUtxoSet tx'
    then do
        logInfo @Text "Claiming refund"
        void $ mkTxConstraints (Constraints.typedValidatorLookups inst
                             <> Constraints.unspentOutputs utxo) tx'
            >>= submitUnbalancedTx . Constraints.adjustUnbalancedTx
    else pure ()


scheduleCollection :: AsContractError e => Election -> Promise () VoteSchema e ()
scheduleCollection vt =

    endpoint @"schedule collection" $ \() -> do

        let inst = typedValidator vt

        _ <- awaitTime $ electionDeadline vt
        unspentOutputs <- utxosAt (Scripts.validatorAddress inst)

        let tx = Typed.collectFromScript unspentOutputs Collect
                <> Constraints.mustValidateIn (collectionRange vt)
        void $ submitTxConstraintsSpending inst unspentOutputs tx


endpoints :: AsContractError e => Contract () VoteSchema e ()
endpoints = voting (theElection $ TimeSlot.scSlotZeroTime def)

mkSchemaDefinitions ''VoteSchema

$(mkKnownCurrencies [])
