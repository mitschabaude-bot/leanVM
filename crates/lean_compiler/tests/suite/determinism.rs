//! One source compiles to one program, always, and the same program it compiled
//! to yesterday.
//!
//! The bytecode digest leads the Fiat--Shamir transcript, so two builds of one
//! source that disagree are two incompatible proof systems, and the symptom is a
//! proof that stops verifying rather than a crash.
//!
//! Two different properties, and only the first is about determinism:
//!
//! * *Within a process*, compiling twice is a real perturbation rather than a
//!   repeat, since `RandomState` bumps its seed once per map, so the second
//!   compilation hashes with different keys than the first.
//! * *Across commits*, `GOLDEN` is a SNAPSHOT of the compiler's output. It does
//!   not prove determinism (nothing iterating a hash container reaches the
//!   bytecode today, and deliberately reversing the branch-output order at a join
//!   moves no digest). It earns its place a different way: a codegen change that
//!   was not intended shows up here and nowhere else, and every entry that moved
//!   this far was a change someone then had to justify.
//!
//! So a moved digest is a question, not a chore: update `GOLDEN` in the same
//! commit and say in the message which change moved it.

use std::collections::BTreeMap;
use std::fs;

use lean_compiler::{compile, parse};
use leanvm_core::cpu::Program;

/// `tests/programs/<name>.py` against the digest of the bytecode it compiles to.
/// The list is closed: a new program must be added here, so one cannot be added
/// without a digest.
#[rustfmt::skip]
const GOLDEN: &[(&str, &str)] = &[
    ("conditionals", "7bc2a2cd3e711695c8b50e6c2ba1e898e43bbe5c6c55741408d7622ed9e99566"),
    ("const_params", "9744aab8b656f7d092d791986b12376b5a41035c25a3c61af09760bde9bdb205"),
    ("fibonacci", "8cc4b25f40e0d6b38d5984130b520899ddaefbbe0ea8f7dd321c80d2bf3cd0af"),
    ("hash_heap_chain", "94ea992b4ccb4cf05af26bc027630d88f65fe5f26a70faa901c2d7ec8cfe62e8"),
    ("hash_slices", "0f97f5f445fa0466dfe04259100bf0e10d895bf5d6d3049018ce04bdad44c5b5"),
    ("heapbuf_dyn", "a7cebdbee9ab883f62731e29f48e59bde41d09b2a06cb57119bbb63e29d5bc15"),
    ("hint", "fa09dca6dd04e65c6e3378f84b35cd1a134ef819e2a1836943e3f29f9a431c9a"),
    ("identities", "b4db426893c4ff78512bc6b4277699b7b479bc448a70fa8713be6c7b6c3b67a7"),
    ("match", "e861a90843c5a7fa7b0444dea23aa8cad7d5b48e6ee416d8c6e29b2a6fef2f49"),
    ("match_arms", "1d7e33adb6a729c16a61f437a0c7aa95c012c05fa98bc1f01b173890ce0573c5"),
    ("nested", "ae30509d474382ce11909e8f389ac564b5ca484ddf82ed17524a94b01f3fb494"),
    ("runtime_loop", "70c30587a46f5d7488217c428675f62198cb1d1f2c143112a28bbbe0b1a00c1c"),
    ("scoping", "34ec53546beea93a98104eb9b3c0169e6b1ffeda9c049f1ef94a9141796246a7"),
    ("unroll", "1b26316ffd959d12869ad64d45169f30df26458f84bca9a5f96aad43ee6c8e6b"),
    ("wots_walk", "54294b9c8cbab253acb0063cdb545595824dffa5d36a239fdaeae9059820cc3f"),
];

fn digest(p: &Program) -> String {
    primitives::hash::hash(format!("{:?}", p.prog()).as_bytes())
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// Every program in `tests/programs/`, compiled twice.
#[test]
fn bytecode_is_reproducible() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let mut paths: Vec<_> = fs::read_dir(dir)
        .expect("tests/programs")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "py"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no .py programs found");

    let mut actual: Vec<(String, String)> = Vec::new();
    for path in &paths {
        let name = path.file_stem().expect("file stem").to_string_lossy().into_owned();
        let src = fs::read_to_string(path).unwrap_or_else(|e| panic!("{name}: read: {e}"));
        let one = compile(&parse(&src).unwrap_or_else(|e| panic!("{name}: parse: {e}")));
        let two = compile(&parse(&src).unwrap_or_else(|e| panic!("{name}: parse: {e}")));
        assert_eq!(
            digest(&one),
            digest(&two),
            "{name}: two compilations of one source produced different bytecode, \
             so the compiler is reading a hash seed"
        );
        actual.push((name, digest(&one)));
    }

    let want: BTreeMap<&str, &str> = GOLDEN.iter().copied().collect();
    let moved: Vec<&str> = actual
        .iter()
        .filter(|(n, d)| want.get(n.as_str()) != Some(&d.as_str()))
        .map(|(n, _)| n.as_str())
        .collect();
    let dropped: Vec<&str> = want
        .keys()
        .copied()
        .filter(|n| !actual.iter().any(|(a, _)| a == n))
        .collect();
    assert!(
        dropped.is_empty(),
        "GOLDEN names a program that no longer exists: {dropped:?}"
    );
    if !moved.is_empty() {
        let table: String = actual
            .iter()
            .map(|(n, d)| format!("    (\"{n}\", \"{d}\"),\n"))
            .collect();
        panic!("bytecode changed for {moved:?}\n\nif that was intended, GOLDEN is now:\n{table}");
    }
}
