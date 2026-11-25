//! Field-element encodings shared by the host and the guest.

use super::COUNT_RADIX;
use primitives::field::{F192, g_pow};

/// A count as the guest carries it: in the exponent, `g^n`.
pub(super) fn count(n: usize) -> F192 {
    F192::from(g_pow(n))
}

/// A node count as the guest's statement carries it: in the exponent, `g^n`.
pub(super) fn node_count_cell(n: u64) -> F192 {
    F192::from(primitives::field::F64::G.pow(u128::from(n)))
}

/// A child's node count as the guest reads it: its four digits in base [`COUNT_RADIX`], the
/// most significant first, each in the exponent. The count is at most
/// [`MAX_NODE_COUNT`](super::MAX_NODE_COUNT).
pub(super) fn node_count_digits(n: u64) -> Vec<F192> {
    assert!(n <= super::MAX_NODE_COUNT, "a node count has four digits");
    (0..4)
        .rev()
        .map(|k| count(((n / COUNT_RADIX.pow(k)) % COUNT_RADIX) as usize))
        .collect()
}

/// Bytes, each in the exponent: how the guest bounds a value it rebuilds
/// (`sp_from_bytes`).
pub(super) fn exponent_bytes(bytes: &[u8]) -> Vec<F192> {
    bytes.iter().map(|&b| count(b.into())).collect()
}

/// A field element as the decimal `u128` literal the zkDSL parser accepts.
pub(super) fn dsl_u128(value: F192) -> u128 {
    assert_eq!(value.c2, 0, "u128 DSL literal cannot encode the top F192 limb");
    (value.c0 as u128) | ((value.c1 as u128) << 64)
}

/// A 16-byte native value as one canonical 128-bit cell.
pub(super) fn pack_16_bytes(bytes: &[u8]) -> F192 {
    let word_at = |offset: usize| u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap());
    F192::new(word_at(0), word_at(8), 0)
}

/// A run of canonical 128-bit cells as the byte string the hash takes: each cell
/// is its two low limbs, little-endian, which is the order the VM's hash
/// instruction reads a memory cell in.
pub(super) fn cell_bytes(cells: impl IntoIterator<Item = F192>) -> Vec<u8> {
    let mut bytes = Vec::new();
    for cell in cells {
        bytes.extend_from_slice(&cell.c0.to_le_bytes());
        bytes.extend_from_slice(&cell.c1.to_le_bytes());
    }
    bytes
}
