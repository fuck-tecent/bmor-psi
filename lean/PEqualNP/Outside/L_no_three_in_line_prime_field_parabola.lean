import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_prime_field_parabola :
    ∀ (p : ℕ), Nat.Prime p → ∀ (a b c : ZMod p), a ≠ b → a ≠ c → b ≠ c → (b - a) * (c ^ 2 - a ^ 2) ≠ (b ^ 2 - a ^ 2) * (c - a) := by
  intro p hp a b c hab hac hbc h
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hzero : (b - a) * (c - a) * (c - b) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp hzero with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact (sub_ne_zero.mpr hab.symm) h''
    · exact (sub_ne_zero.mpr hac.symm) h''
  · exact hbc (sub_eq_zero.mp h').symm
