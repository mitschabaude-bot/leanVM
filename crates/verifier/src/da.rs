//! LeanDA's membership challenge, which the statement of an aggregate binds with its root.
//!
//! A blob row is a codeword iff it is orthogonal to `L(X) = prod_j (1 + z^(2^j) * Vhat_j(X))`, `Vhat_j` the
//! normalized subspace polynomial of degree `2^j` (doc/leanvm annex D). The guest builds `L` from `z`; the verifier
//! derives `z` from the root here, outside the SNARK.

use crate::field::E;
use crate::hash::{Digest, Key, keccak_hash};
use crate::merkle::hash_pair;
use crate::transcript::Sponge;

const LABEL: &[u8] = b"leanDA/rs-membership/v1";

/// `z` under `seed`: the VM's transcript seeded with the seed as its IV, the root, and the label's hash, squeezed once.
pub fn membership_challenge(seed: &[u8; 32], root: &[u8; 32]) -> E {
    Sponge::new(Digest(*seed), Digest(*root), keccak_hash(LABEL)).sample()
}

/// What the statement of an aggregate under `seed` carries for its DA root: the keyed hash `H_seed(root ‖ z)`, `z` as
/// its three little-endian limbs and a zero word, or zeros without a root.
pub fn digest(seed: &[u8; 32], root: Option<[u8; 32]>) -> [u8; 32] {
    root.map_or([0; 32], |root| {
        let z = membership_challenge(seed, &root);
        let key = Key::new(&Digest(*seed));
        hash_pair(&key, &root, [z.c0, z.c1, z.c2, 0].map(u64::to_le_bytes).as_flattened()).0
    })
}
