import Mathlib

theorem PEqualNP.Outside.L_goldbach_residue_blocks_merge_scales :
    ∀ (q d k : ℕ), d ∣ q → k % q % d = k % d := by
  intro q d k h
  first
  | exact Nat.mod_mod_of_dvd k h
  | exact?
