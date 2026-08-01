-- Byte-wise XOR encryption written in Boole, the intermediate verification
-- language embedded in Lean by CSLib (`leanprover/cslib`, `Boole-sandbox`
-- branch): https://github.com/leanprover/cslib/tree/Boole-sandbox/Cslib/Languages/Boole
--
-- This mirrors the Rust function verified elsewhere in this project via
-- Aeneas (`xor_cipher/src/lib.rs`):
--
--   pub fn xor_encrypt<const N: usize>(mut data: [u8; N], key: u8) -> [u8; N] {
--       let mut i: usize = 0;
--       while i < N {
--           data[i] = data[i] ^ key;
--           i += 1;
--       }
--       data
--   }
--
-- Boole has no fixed-size/const-generic arrays, so the array `[u8; N]` is
-- modeled as a `Sequence bv8` whose length stands in for `N`; there is no
-- separate `len` parameter since, unlike a slice, the Rust array is always
-- processed in full.
import StrataBoole.MetaVerifier
import Smt

open Strata

def xorEncryptBoole : StrataDDM.Program :=
#strata
program Boole;

procedure xor_encrypt(data: Sequence bv8, key: bv8)
  returns (cipher: Sequence bv8)
spec
{
  ensures Sequence.length(cipher) == Sequence.length(data);
  ensures (forall i : int :: 0 <= i && i < Sequence.length(data) ==>
    Sequence.select(cipher, i) == Sequence.select(data, i) ^ key);
}
{
  cipher := Sequence.take(data, 0);
  var i : int;
  i := 0;
  while (i < Sequence.length(data))
    decreases Sequence.length(data) - i
    invariant 0 <= i
    invariant i <= Sequence.length(data)
    invariant Sequence.length(cipher) == i
    invariant (forall j : int :: 0 <= j && j < i ==>
      Sequence.select(cipher, j) == Sequence.select(data, j) ^ key)
  {
    cipher := Sequence.build(cipher, Sequence.select(data, i) ^ key);
    i := i + 1;
  }
};

#end

-- Approach 1: discharge the verification conditions with an external SMT
-- solver (needs `cvc5` on PATH).
-- #eval Strata.Boole.verify "cvc5" xorEncryptBoole (options := .quiet)

-- Approach 2: discharge the verification conditions with Lean tactics.
theorem xorEncryptBoole_smtVCsCorrect : Strata.smtVCsCorrectBoole xorEncryptBoole := by
  gen_smt_vcs_boole
  all_goals (first | smt +mono | smt | omega | trivial | grind)
