import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_residue_blocks_phase_center :
    ∀ (q : ℕ) (w u : Fin q → ℂ) (c : ℂ), (∑ a, w a) = 0 →
      (∑ a, w a * u a) = ∑ a, w a * (u a - c) := by
  intro q w u c hw
  have hconstant : (∑ a, w a * c) = 0 := by
    rw [← Finset.sum_mul, hw, zero_mul]
  simp only [mul_sub, Finset.sum_sub_distrib, hconstant, sub_zero]
