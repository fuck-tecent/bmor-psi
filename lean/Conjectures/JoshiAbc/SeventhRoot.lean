import Mathlib

theorem Conjectures.JoshiAbc.SeventhRoot :
    let z : ZMod 29 := 7; orderOf z = 7 ∧ z^2 ≠ 0 ∧ 1+z^2 ≠ 0 := by
  intro z
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel
