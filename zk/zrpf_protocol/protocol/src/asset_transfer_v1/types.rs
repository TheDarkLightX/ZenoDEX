use alloc::vec::Vec;
use core::cmp::Ordering;

use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

use super::hash::{derive_command_hash_v1, derive_state_root_v1};
use super::{
    AssetTransferErrorV1, ASSET_TRANSFER_COMMAND_VERSION_V1, ASSET_TRANSFER_LEAF_INPUT_VERSION_V1,
    ASSET_TRANSFER_STATE_VERSION_V1, MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1,
    MAX_ASSET_TRANSFER_STATE_ENTRIES_V1,
};
use crate::{AuthorizationSubjectIdV1, CommitmentV3};

macro_rules! nonzero_identifier_type {
    ($name:ident, $label:literal) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name([u8; 32]);

        impl $name {
            pub fn new(bytes: [u8; 32]) -> Result<Self, AssetTransferErrorV1> {
                if bytes == [0; 32] {
                    return Err(AssetTransferErrorV1::ZeroIdentifier($label));
                }
                Ok(Self(bytes))
            }

            pub const fn as_bytes(&self) -> &[u8; 32] {
                &self.0
            }

            pub const fn into_bytes(self) -> [u8; 32] {
                self.0
            }
        }

        impl Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                self.0.serialize(serializer)
            }
        }

        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                Self::new(<[u8; 32]>::deserialize(deserializer)?).map_err(de::Error::custom)
            }
        }
    };
}

nonzero_identifier_type!(AssetTransferAccountIdV1, "asset_transfer_account_id");
nonzero_identifier_type!(AssetTransferAssetIdV1, "asset_transfer_asset_id");
nonzero_identifier_type!(AssetTransferStateRootV1, "asset_transfer_state_root");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AssetTransferBalanceInputV1 {
    pub account_id: AssetTransferAccountIdV1,
    pub asset_id: AssetTransferAssetIdV1,
    pub amount_atoms: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct AssetTransferBalanceV1 {
    account_id: AssetTransferAccountIdV1,
    asset_id: AssetTransferAssetIdV1,
    amount_atoms: u128,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AssetTransferBalanceWireV1 {
    account_id: AssetTransferAccountIdV1,
    asset_id: AssetTransferAssetIdV1,
    amount_atoms: u128,
}

impl AssetTransferBalanceV1 {
    pub fn new(input: AssetTransferBalanceInputV1) -> Result<Self, AssetTransferErrorV1> {
        if input.amount_atoms == 0 || input.amount_atoms > MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1 {
            return Err(AssetTransferErrorV1::InvalidStoredBalance);
        }
        Ok(Self {
            account_id: input.account_id,
            asset_id: input.asset_id,
            amount_atoms: input.amount_atoms,
        })
    }

    pub const fn account_id(&self) -> AssetTransferAccountIdV1 {
        self.account_id
    }

    pub const fn asset_id(&self) -> AssetTransferAssetIdV1 {
        self.asset_id
    }

    pub const fn amount_atoms(&self) -> u128 {
        self.amount_atoms
    }

    fn key(&self) -> (AssetTransferAccountIdV1, AssetTransferAssetIdV1) {
        (self.account_id, self.asset_id)
    }
}

impl<'de> Deserialize<'de> for AssetTransferBalanceV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = AssetTransferBalanceWireV1::deserialize(deserializer)?;
        Self::new(AssetTransferBalanceInputV1 {
            account_id: wire.account_id,
            asset_id: wire.asset_id,
            amount_atoms: wire.amount_atoms,
        })
        .map_err(de::Error::custom)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssetTransferStateInputV1 {
    pub balances: Vec<AssetTransferBalanceV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AssetTransferStateV1 {
    state_version: u16,
    balances: Vec<AssetTransferBalanceV1>,
    state_root: AssetTransferStateRootV1,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AssetTransferStateWireV1 {
    state_version: u16,
    #[serde(deserialize_with = "deserialize_bounded_balances")]
    balances: Vec<AssetTransferBalanceV1>,
    state_root: AssetTransferStateRootV1,
}

impl AssetTransferStateV1 {
    pub fn new(mut input: AssetTransferStateInputV1) -> Result<Self, AssetTransferErrorV1> {
        require_balance_count(input.balances.len())?;
        input.balances.sort_by_key(AssetTransferBalanceV1::key);
        reject_duplicate_balances(&input.balances)?;
        let state_root = derive_state_root_v1(ASSET_TRANSFER_STATE_VERSION_V1, &input.balances)?;
        Ok(Self {
            state_version: ASSET_TRANSFER_STATE_VERSION_V1,
            balances: input.balances,
            state_root,
        })
    }

    fn from_wire(wire: AssetTransferStateWireV1) -> Result<Self, AssetTransferErrorV1> {
        if wire.state_version != ASSET_TRANSFER_STATE_VERSION_V1 {
            return Err(AssetTransferErrorV1::InvalidStateVersion(
                wire.state_version,
            ));
        }
        require_balance_count(wire.balances.len())?;
        require_canonical_balance_order(&wire.balances)?;
        if derive_state_root_v1(wire.state_version, &wire.balances)? != wire.state_root {
            return Err(AssetTransferErrorV1::InvalidStateRoot);
        }
        Ok(Self {
            state_version: wire.state_version,
            balances: wire.balances,
            state_root: wire.state_root,
        })
    }

    pub const fn state_root(&self) -> AssetTransferStateRootV1 {
        self.state_root
    }

    pub fn balances(&self) -> &[AssetTransferBalanceV1] {
        &self.balances
    }

    pub fn balance_of(
        &self,
        account_id: AssetTransferAccountIdV1,
        asset_id: AssetTransferAssetIdV1,
    ) -> u128 {
        self.balances
            .binary_search_by_key(&(account_id, asset_id), AssetTransferBalanceV1::key)
            .map(|index| self.balances[index].amount_atoms)
            .unwrap_or(0)
    }

    pub(super) fn asset_total_atoms(
        &self,
        asset_id: AssetTransferAssetIdV1,
    ) -> Result<u128, AssetTransferErrorV1> {
        self.balances
            .iter()
            .filter(|balance| balance.asset_id == asset_id)
            .try_fold(0_u128, |total, balance| {
                total
                    .checked_add(balance.amount_atoms)
                    .ok_or(AssetTransferErrorV1::ArithmeticOverflow("asset_total"))
            })
    }

    pub(super) fn with_transfer_post(
        &self,
        source_account_id: AssetTransferAccountIdV1,
        destination_account_id: AssetTransferAccountIdV1,
        asset_id: AssetTransferAssetIdV1,
        source_post_atoms: u128,
        destination_post_atoms: u128,
    ) -> Result<Self, AssetTransferErrorV1> {
        let mut balances = self
            .balances
            .iter()
            .copied()
            .filter(|balance| {
                balance.asset_id != asset_id
                    || (balance.account_id != source_account_id
                        && balance.account_id != destination_account_id)
            })
            .collect::<Vec<_>>();
        if source_post_atoms > 0 {
            balances.push(AssetTransferBalanceV1::new(AssetTransferBalanceInputV1 {
                account_id: source_account_id,
                asset_id,
                amount_atoms: source_post_atoms,
            })?);
        }
        if destination_post_atoms > 0 {
            balances.push(AssetTransferBalanceV1::new(AssetTransferBalanceInputV1 {
                account_id: destination_account_id,
                asset_id,
                amount_atoms: destination_post_atoms,
            })?);
        }
        Self::new(AssetTransferStateInputV1 { balances })
    }
}

impl<'de> Deserialize<'de> for AssetTransferStateV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::from_wire(AssetTransferStateWireV1::deserialize(deserializer)?)
            .map_err(de::Error::custom)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AssetTransferCommandInputV1 {
    pub source_account_id: AssetTransferAccountIdV1,
    pub destination_account_id: AssetTransferAccountIdV1,
    pub asset_id: AssetTransferAssetIdV1,
    pub amount_atoms: u128,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AssetTransferCommandV1 {
    command_version: u16,
    source_account_id: AssetTransferAccountIdV1,
    destination_account_id: AssetTransferAccountIdV1,
    asset_id: AssetTransferAssetIdV1,
    amount_atoms: u128,
    command_hash: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AssetTransferCommandWireV1 {
    command_version: u16,
    source_account_id: AssetTransferAccountIdV1,
    destination_account_id: AssetTransferAccountIdV1,
    asset_id: AssetTransferAssetIdV1,
    amount_atoms: u128,
    command_hash: CommitmentV3,
}

impl AssetTransferCommandV1 {
    pub fn new(input: AssetTransferCommandInputV1) -> Result<Self, AssetTransferErrorV1> {
        validate_command_shape(&input)?;
        let command_hash = derive_command_hash_v1(
            ASSET_TRANSFER_COMMAND_VERSION_V1,
            input.source_account_id,
            input.destination_account_id,
            input.asset_id,
            input.amount_atoms,
        )?;
        Ok(Self {
            command_version: ASSET_TRANSFER_COMMAND_VERSION_V1,
            source_account_id: input.source_account_id,
            destination_account_id: input.destination_account_id,
            asset_id: input.asset_id,
            amount_atoms: input.amount_atoms,
            command_hash,
        })
    }

    fn from_wire(wire: AssetTransferCommandWireV1) -> Result<Self, AssetTransferErrorV1> {
        if wire.command_version != ASSET_TRANSFER_COMMAND_VERSION_V1 {
            return Err(AssetTransferErrorV1::InvalidCommandVersion(
                wire.command_version,
            ));
        }
        let input = AssetTransferCommandInputV1 {
            source_account_id: wire.source_account_id,
            destination_account_id: wire.destination_account_id,
            asset_id: wire.asset_id,
            amount_atoms: wire.amount_atoms,
        };
        validate_command_shape(&input)?;
        let expected = derive_command_hash_v1(
            wire.command_version,
            wire.source_account_id,
            wire.destination_account_id,
            wire.asset_id,
            wire.amount_atoms,
        )?;
        if expected != wire.command_hash {
            return Err(AssetTransferErrorV1::InvalidCommandHash);
        }
        Ok(Self {
            command_version: wire.command_version,
            source_account_id: wire.source_account_id,
            destination_account_id: wire.destination_account_id,
            asset_id: wire.asset_id,
            amount_atoms: wire.amount_atoms,
            command_hash: wire.command_hash,
        })
    }

    pub const fn source_account_id(&self) -> AssetTransferAccountIdV1 {
        self.source_account_id
    }

    pub const fn destination_account_id(&self) -> AssetTransferAccountIdV1 {
        self.destination_account_id
    }

    pub const fn asset_id(&self) -> AssetTransferAssetIdV1 {
        self.asset_id
    }

    pub const fn amount_atoms(&self) -> u128 {
        self.amount_atoms
    }

    pub fn canonical_hash(&self) -> Result<CommitmentV3, AssetTransferErrorV1> {
        let expected = derive_command_hash_v1(
            self.command_version,
            self.source_account_id,
            self.destination_account_id,
            self.asset_id,
            self.amount_atoms,
        )?;
        if expected != self.command_hash {
            return Err(AssetTransferErrorV1::InvalidCommandHash);
        }
        Ok(self.command_hash)
    }
}

impl<'de> Deserialize<'de> for AssetTransferCommandV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::from_wire(AssetTransferCommandWireV1::deserialize(deserializer)?)
            .map_err(de::Error::custom)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AssetTransferLeafInputV1 {
    leaf_input_version: u16,
    pre_state: AssetTransferStateV1,
    command: AssetTransferCommandV1,
    expected_pre_state_root: AssetTransferStateRootV1,
    expected_command_hash: CommitmentV3,
    expected_authorization_subject_id: AuthorizationSubjectIdV1,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AssetTransferLeafInputWireV1 {
    leaf_input_version: u16,
    pre_state: AssetTransferStateV1,
    command: AssetTransferCommandV1,
    expected_pre_state_root: AssetTransferStateRootV1,
    expected_command_hash: CommitmentV3,
    expected_authorization_subject_id: AuthorizationSubjectIdV1,
}

impl AssetTransferLeafInputV1 {
    pub fn new(
        pre_state: AssetTransferStateV1,
        command: AssetTransferCommandV1,
        expected_pre_state_root: AssetTransferStateRootV1,
        expected_command_hash: CommitmentV3,
        expected_authorization_subject_id: AuthorizationSubjectIdV1,
    ) -> Result<Self, AssetTransferErrorV1> {
        command.canonical_hash()?;
        Ok(Self {
            leaf_input_version: ASSET_TRANSFER_LEAF_INPUT_VERSION_V1,
            pre_state,
            command,
            expected_pre_state_root,
            expected_command_hash,
            expected_authorization_subject_id,
        })
    }

    fn from_wire(wire: AssetTransferLeafInputWireV1) -> Result<Self, AssetTransferErrorV1> {
        if wire.leaf_input_version != ASSET_TRANSFER_LEAF_INPUT_VERSION_V1 {
            return Err(AssetTransferErrorV1::InvalidLeafInputVersion(
                wire.leaf_input_version,
            ));
        }
        wire.command.canonical_hash()?;
        Ok(Self {
            leaf_input_version: wire.leaf_input_version,
            pre_state: wire.pre_state,
            command: wire.command,
            expected_pre_state_root: wire.expected_pre_state_root,
            expected_command_hash: wire.expected_command_hash,
            expected_authorization_subject_id: wire.expected_authorization_subject_id,
        })
    }

    pub const fn pre_state(&self) -> &AssetTransferStateV1 {
        &self.pre_state
    }

    pub const fn command(&self) -> &AssetTransferCommandV1 {
        &self.command
    }

    pub const fn expected_pre_state_root(&self) -> AssetTransferStateRootV1 {
        self.expected_pre_state_root
    }

    pub const fn expected_command_hash(&self) -> CommitmentV3 {
        self.expected_command_hash
    }

    pub const fn expected_authorization_subject_id(&self) -> AuthorizationSubjectIdV1 {
        self.expected_authorization_subject_id
    }
}

impl<'de> Deserialize<'de> for AssetTransferLeafInputV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::from_wire(AssetTransferLeafInputWireV1::deserialize(deserializer)?)
            .map_err(de::Error::custom)
    }
}

fn validate_command_shape(input: &AssetTransferCommandInputV1) -> Result<(), AssetTransferErrorV1> {
    if input.amount_atoms == 0 || input.amount_atoms > MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1 {
        return Err(AssetTransferErrorV1::InvalidAmount);
    }
    if input.source_account_id == input.destination_account_id {
        return Err(AssetTransferErrorV1::SelfTransfer);
    }
    Ok(())
}

fn require_balance_count(actual: usize) -> Result<(), AssetTransferErrorV1> {
    if actual > MAX_ASSET_TRANSFER_STATE_ENTRIES_V1 {
        return Err(AssetTransferErrorV1::TooManyBalances {
            actual,
            maximum: MAX_ASSET_TRANSFER_STATE_ENTRIES_V1,
        });
    }
    Ok(())
}

fn reject_duplicate_balances(
    balances: &[AssetTransferBalanceV1],
) -> Result<(), AssetTransferErrorV1> {
    if balances
        .windows(2)
        .any(|pair| pair[0].key() == pair[1].key())
    {
        return Err(AssetTransferErrorV1::DuplicateBalanceKey);
    }
    Ok(())
}

fn require_canonical_balance_order(
    balances: &[AssetTransferBalanceV1],
) -> Result<(), AssetTransferErrorV1> {
    for pair in balances.windows(2) {
        match pair[0].key().cmp(&pair[1].key()) {
            Ordering::Less => {}
            Ordering::Equal => return Err(AssetTransferErrorV1::DuplicateBalanceKey),
            Ordering::Greater => return Err(AssetTransferErrorV1::NonCanonicalBalanceOrder),
        }
    }
    Ok(())
}

fn deserialize_bounded_balances<'de, D>(
    deserializer: D,
) -> Result<Vec<AssetTransferBalanceV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct BalancesVisitor;

    impl<'de> de::Visitor<'de> for BalancesVisitor {
        type Value = Vec<AssetTransferBalanceV1>;

        fn expecting(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(
                formatter,
                "at most {MAX_ASSET_TRANSFER_STATE_ENTRIES_V1} asset transfer balances"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: de::SeqAccess<'de>,
        {
            let declared = sequence.size_hint().unwrap_or(0);
            if declared > MAX_ASSET_TRANSFER_STATE_ENTRIES_V1 {
                return Err(de::Error::custom(
                    "asset transfer balance count exceeds bound",
                ));
            }
            let mut balances = Vec::with_capacity(declared);
            while let Some(balance) = sequence.next_element()? {
                if balances.len() == MAX_ASSET_TRANSFER_STATE_ENTRIES_V1 {
                    return Err(de::Error::custom(
                        "asset transfer balance count exceeds bound",
                    ));
                }
                balances.push(balance);
            }
            Ok(balances)
        }
    }

    deserializer.deserialize_seq(BalancesVisitor)
}
