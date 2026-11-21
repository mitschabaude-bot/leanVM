//! The seed a published salt gives the aggregation guest.

use super::deferred::stacked_bytecode;

/// The seed of a published salt for the aggregation guest: Keccak-256 of the salt, the proof system's version tag
/// ([`verifier::TAG`]) and the guest's stacked bytecode ([`verifier::seed_of_salt`]).
///
/// Every node of a tree is proved and verified under one seed: its proof's transcript starts from it, its memory
/// words 2 and 3 hold it, its statement's digest starts with it, and it keys every hash on data a prover chooses.
/// The guest reads it from its public input and never sees the salt, so its bytecode does not depend on the salt.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Seed([u8; 32]);

impl Seed {
    /// The seed of `salt`: one pass of Keccak-256 over the stacked bytecode, so a caller computes it once per salt.
    pub fn of_salt(salt: &[u8; 32]) -> Self {
        let words: Vec<u64> = stacked_bytecode().iter().map(|word| word.0).collect();
        Self(verifier::seed_of_salt(salt, &words))
    }

    /// Its 32 bytes, its four words little-endian.
    pub fn to_bytes(self) -> [u8; 32] {
        self.0
    }

    /// The key of its keyed hash.
    pub(super) fn key(self) -> fiat_shamir::merkle::Key {
        fiat_shamir::merkle::Key::new(&self.0)
    }
}
