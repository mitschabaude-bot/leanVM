//! `main` leaves memory words 2 and 3 to the seed, as it leaves words 0 and 1 to the public input.

use crate::common::{SEED, words};
use lean_compiler::{compile, parse};
use leanvm_core::cpu::{prove, verify};
use primitives::field::{F64, F192};

/// `main`'s first locals are written before it reads words 2 and 3, so they would land on the seed's halves, and
/// conflict with them, if `main`'s frame began there.
const READS_THE_SEED: &str = "\
def main():
    s = StackBuf(2)
    s[0] = 5
    s[1] = 7
    p = GEN ** 0
    p[1] = p[GEN ** 2] + s[0]
    p[GEN] = p[GEN ** 3] * s[1]
    return
";

#[test]
fn main_leaves_the_seed_words_to_the_statement() {
    let program = compile(&parse(READS_THE_SEED).expect("parse"));
    let [_, _, s0, s1] = words([F192::ZERO; 2]);
    let pi = [s0 + F192::from(F64(5)), s1 * F192::from(F64(7))];
    let execution = program
        .execute(words(pi))
        .expect("main's locals start past the public words");
    assert!(execution.unconstrained_reads.is_empty());
    let (proof, _) = prove(&program, &SEED, pi, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
    verify(&program, &SEED, &pi, &proof).expect("the seed's words verify");
}
