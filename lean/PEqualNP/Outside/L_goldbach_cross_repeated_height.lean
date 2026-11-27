import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_cross_repeated_height : ∀ (m : ℕ) (v : ℂ), (∑ i : Fin m, ∑ _j ∈ Finset.univ.erase i, (v * star v).re) = (m : ℝ)*((m : ℝ)-1)*‖v‖^2 := by
  classical
  intro m v
  have h : (v * star v).re = ‖v‖ ^ 2 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp_rw [h]
  cases m with
  | zero => simp
  | succ m =>
    simp [Finset.card_erase_of_mem, nsmul_eq_mul, Nat.cast_add]
    ring
