//! The Lean data of the salted aggregation guest, written from leanVM's own sources beside the
//! deployed guest's (`LeanVM/SaltedGuest/Data/`), and the salted Rust's vectors. A child of
//! `aggregation` (the overlay's appended line), so `super::*` is everything `aggregation.rs`
//! defines, private items included, as the BLAKE2s-era in-tree tests had it.

use super::*;
// The module's pieces, since leanVM #670 split `aggregation.rs` (`build.rs` widens their items).
use super::{
    cells::*, child::*, claim_pool::*, coverage::*, deferred::*, error::*, guest::*, hints::*, node::*,
    placeholders::*, proof::*, seed::*, statement::*,
};
use leanvm_core::cpu::{Program, from_scalar};
use primitives::field::F192;
use primitives::multilinear::mle_eval_par;
use std::collections::BTreeMap;

pub mod bytecode;
#[cfg(test)]
mod node_diff;
pub mod manifest;
pub mod node_vectors;
pub mod source;

/// A generated file: its path relative to `lean_vm/` and its text.
pub struct File {
    pub path: String,
    pub text: String,
}

/// The compiled guest at its self-consistent size.
pub fn guest() -> &'static Program {
    unified_guest()
}

/// The salt the exported vectors are under.
pub const SALT: [u8; 32] = [0x5a; 32];

/// [`SALT`]'s seed for the guest (`Seed::of_salt`), computed once.
pub fn seed() -> &'static Seed {
    static SEED: std::sync::OnceLock<Seed> = std::sync::OnceLock::new();
    SEED.get_or_init(|| Seed::of_salt(&SALT))
}

/// The deployed placeholders, at the guest's log size.
pub fn placeholders() -> BTreeMap<String, String> {
    placeholder_map(guest().prog().len().trailing_zeros() as usize)
}

/// The guest's source text, as `aggregation.rs` includes it.
pub const GUEST_SOURCE: &str = include_str!(concat!(env!("OUT_DIR"), "/rec_aggregation/guests/lean_ethereum.py"));

/// Every file this crate writes.
pub fn all_files() -> Vec<File> {
    let mut files = bytecode::files(guest());
    files.extend(source::files());
    files.push(manifest::file());
    files.push(node_vectors::file());
    files
}
