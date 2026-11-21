//! Merkle openings: one full path per query, hashed under the proof's key.

use crate::field::K;
use crate::hash::{Digest, Key};

pub fn hash_pair(key: &Key, left: &[u8], right: &[u8]) -> Digest {
    let mut pair = [0u8; 64];
    pair[..32].copy_from_slice(left);
    pair[32..].copy_from_slice(right);
    key.hash(&pair)
}

fn hash_leaf(key: &Key, image: &[K]) -> Digest {
    key.hash(&image.iter().flat_map(|word| word.to_bytes()).collect::<Vec<u8>>())
}

/// One query's own opening, the form the Rust and Lean verifiers read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerklePath {
    pub leaf_index: u64,
    /// The whole leaf image, its zero prefix included.
    pub leaf: Vec<K>,
    /// Bottom level first.
    pub siblings: Vec<[u8; 32]>,
}

impl MerklePath {
    pub(crate) fn root(&self, key: &Key) -> Digest {
        let mut node = hash_leaf(key, &self.leaf);
        for (level, sibling) in self.siblings.iter().enumerate() {
            node = if self.leaf_index >> level & 1 == 0 {
                hash_pair(key, &node.0, sibling)
            } else {
                hash_pair(key, sibling, &node.0)
            };
        }
        node
    }
}
