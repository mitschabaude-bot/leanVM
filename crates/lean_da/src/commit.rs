//! A Merkle tree per blob, then one over the blob roots, every cell and node hashed with the keyed hash under the
//! seed of the tree of proofs the commitment is proved in ([`Key`]).
//!
//! A blob's leaves are its `ℓ = m/c` cell digests, so the left subtree of its root covers the
//! systematic payload and a sampled cell opens against its blob root. The blob roots, padded with
//! the zero codeword's to a power of two, are the leaves of the commitment's tree.

use fiat_shamir::merkle::{Hash, Key};
use primitives::hash::{OUT_LEN, hash_many_from_state};

use crate::{BLOB_SYMBOLS, BlobSizeError, CELL_SYMBOLS, CELLS_PER_ROW, CODEWORD_SYMBOLS, encode_rows, row_count};

/// Digests in one blob's flat tree.
const BLOB_TREE: usize = 2 * CELLS_PER_ROW - 1;

/// What the builder keeps, to answer samples and to feed the proof.
pub struct DaWitness {
    /// `n_rows · m` symbols, row-major. Padding rows are zero and not stored.
    pub codewords: Vec<u64>,
    /// One flat tree per blob of the padded matrix, `2ℓ - 1` digests each: its `ℓ` cell
    /// digests, then each level in turn, its root last.
    pub blob_trees: Vec<Hash>,
    /// The flat tree over the `n_padded` blob roots, laid out likewise.
    pub root_tree: Vec<Hash>,
}

impl DaWitness {
    /// Blob `i`'s flat tree, its cell digests first, for any `i` below `n_padded`.
    pub fn blob_tree(&self, i: usize) -> &[Hash] {
        &self.blob_trees[i * BLOB_TREE..(i + 1) * BLOB_TREE]
    }

    /// The `n_padded` blob roots, the padding blobs' included.
    pub fn blob_roots(&self) -> &[Hash] {
        &self.root_tree[..self.root_tree.len().div_ceil(2)]
    }
}

/// Commit under `seed` to payload rows of little-endian 64-bit symbols and their systematic encoding.
///
/// Returns the root, which the builder publishes: the root of the tree over the blob roots,
/// binding the matrix including its zero padding.
///
/// # Errors
///
/// If `rows` is not 1 to [`DA_MAX_ROWS`](crate::DA_MAX_ROWS) full blobs.
#[tracing::instrument(name = "Commit", skip_all)]
pub fn commit(seed: &[u8; 32], rows: &[u64]) -> Result<(Hash, DaWitness), BlobSizeError> {
    row_count(rows.len(), BLOB_SYMBOLS).ok_or(BlobSizeError { symbols: rows.len() })?;
    Ok(commit_codewords(seed, encode_rows(rows)))
}

/// [`commit`] over rows that are already encoded.
///
/// # Panics
///
/// If `codewords` is not 1 to [`DA_MAX_ROWS`](crate::DA_MAX_ROWS) whole codewords.
pub fn commit_codewords(seed: &[u8; 32], codewords: Vec<u64>) -> (Hash, DaWitness) {
    let key = Key::new(seed);
    let blob_trees = blob_trees(&key, &codewords);
    let blob_roots = blob_trees
        .as_chunks::<BLOB_TREE>()
        .0
        .iter()
        .map(|tree| tree[BLOB_TREE - 1]);
    let root_tree = tree_from_leaves(&key, blob_roots.collect());
    let root = *root_tree.last().unwrap();
    let witness = DaWitness {
        codewords,
        blob_trees,
        root_tree,
    };
    (root, witness)
}

/// The tree of a padding blob under `key`, over `ℓ` copies of the zero cell's digest.
fn padding_tree(key: &Key) -> Vec<Hash> {
    tree_from_leaves(
        key,
        vec![key.hash(&[0u8; CELL_SYMBOLS * size_of::<u64>()]); CELLS_PER_ROW],
    )
}

/// Every blob's tree under `key`, its leaves `e_{i,j} = H(W_{i,j})`, a padding blob's copied in.
#[tracing::instrument(name = "Hashing blobs", skip_all)]
fn blob_trees(key: &Key, codewords: &[u64]) -> Vec<Hash> {
    let m = CODEWORD_SYMBOLS;
    let n_rows = row_count(codewords.len(), m).expect("1..=DA_MAX_ROWS whole codewords");
    let padding = padding_tree(key);
    let mut trees = vec![Hash::default(); n_rows.next_power_of_two() * BLOB_TREE];
    parallel::chunks_mut(&mut trees, BLOB_TREE, |i, tree| {
        if i < n_rows {
            hash_many_from_state(
                as_bytes(&codewords[i * m..(i + 1) * m]),
                CELL_SYMBOLS * size_of::<u64>(),
                key.state(),
                tree[..CELLS_PER_ROW].as_flattened_mut(),
            );
            fill_levels(key, tree);
        } else {
            tree.copy_from_slice(&padding);
        }
    });
    trees
}

/// The flat Merkle tree under `key` over leaves that are already digests: see [`fill_levels`].
fn tree_from_leaves(key: &Key, mut tree: Vec<Hash>) -> Vec<Hash> {
    let n = tree.len();
    assert!(n.is_power_of_two(), "leaf count must be a power of two");
    tree.resize(2 * n - 1, Hash::default());
    fill_levels(key, &mut tree);
    tree
}

/// Fill a flat tree whose `n` leaves sit in `tree[..n]` under `key`: each level follows in turn, the root
/// last. Unlike [`pcs::merkle`] the leaves are not re-hashed, since a cell digest is already the leaf.
fn fill_levels(key: &Key, tree: &mut [Hash]) {
    let (mut base, mut width) = (0, tree.len().div_ceil(2));
    while width > 1 {
        let (read, write) = tree.split_at_mut(base + width);
        hash_many_from_state(
            read[base..].as_flattened(),
            2 * OUT_LEN,
            key.state(),
            write[..width / 2].as_flattened_mut(),
        );
        base += width;
        width /= 2;
    }
}

fn as_bytes(data: &[u64]) -> &[u8] {
    const { assert!(cfg!(target_endian = "little"), "digests use little-endian symbols") };
    primitives::cast_slice(data)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::merkle::hash_pair;

    const SEED: [u8; 32] = [0x17; 32];
    use rand::{Rng, SeedableRng, rngs::StdRng};

    fn payload(n_rows: usize, seed: u64) -> Vec<u64> {
        let mut rng = StdRng::seed_from_u64(seed);
        (0..n_rows * BLOB_SYMBOLS).map(|_| rng.random()).collect()
    }

    /// Rebuilt pairwise from scratch, independently of the flat layout's offsets: each blob root
    /// is the root over its own cells, and the commitment the root over the blob roots, padded
    /// with the zero codeword's.
    #[test]
    fn commitment_is_the_tree_of_blob_trees() {
        let key = Key::new(&SEED);
        let root = |mut level: Vec<Hash>| {
            while level.len() > 1 {
                level = level
                    .chunks(2)
                    .map(|pair| hash_pair(&key, &pair[0], &pair[1]))
                    .collect();
            }
            level[0]
        };
        let n_rows = 5usize;
        let codewords = encode_rows(&payload(n_rows, 1));
        let (commitment, witness) = commit_codewords(&SEED, codewords.clone());
        let zero = vec![0; CODEWORD_SYMBOLS];

        let mut blob_roots = Vec::new();
        for i in 0..n_rows.next_power_of_two() {
            let blob = codewords.chunks(CODEWORD_SYMBOLS).nth(i).unwrap_or(&zero);
            let cells: Vec<Hash> = blob.chunks(CELL_SYMBOLS).map(|cell| key.hash(as_bytes(cell))).collect();
            assert_eq!(witness.blob_tree(i)[..CELLS_PER_ROW], cells, "blob {i}'s leaves");
            blob_roots.push(root(cells));
            assert_eq!(witness.blob_tree(i)[BLOB_TREE - 1], blob_roots[i], "blob {i}'s root");
        }
        assert_eq!(witness.blob_roots(), blob_roots);
        assert_eq!(commitment, root(blob_roots));
    }

    /// Padding rows are zero codewords sharing one root. A payload whose
    /// real rows are unchanged must commit identically whether or not the row count
    /// happens to be a power of two, up to the padding the shape declares.
    #[test]
    fn padding_rows_are_the_zero_codeword() {
        let n_rows = 3usize;
        let rows = payload(n_rows, 3);
        let mut extended = rows.clone();
        extended.extend(std::iter::repeat_n(0, BLOB_SYMBOLS));

        let (short, _) = commit(&SEED, &rows).unwrap();
        let (long, _) = commit(&SEED, &extended).unwrap();
        assert_eq!(short, long);
    }
}
