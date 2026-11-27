import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring

theorem PEqualNP.Outside.L_goldbach_cluster_balanced_energy :
    ∀ (m : ℕ) (u : Fin m → ℂ), (m : ℝ) * (∑ i, ‖u i‖ ^ 2) - ‖∑ i, u i‖ ^ 2 =
      (∑ i, ∑ j, ‖u i - u j‖ ^ 2) / 2 := by
  intro m u
  have cross : (∑ i, ∑ j, inner ℝ (u i) (u j)) = ‖∑ i, u i‖ ^ 2 := by
    simp_rw [← inner_sum]
    rw [← sum_inner, real_inner_self_eq_norm_sq]
  have row (i : Fin m) : (∑ j, ‖u i - u j‖ ^ 2) =
      (m : ℝ) * ‖u i‖ ^ 2 - 2 * (∑ j, inner ℝ (u i) (u j)) + ∑ j, ‖u j‖ ^ 2 := by
    simp only [norm_sub_sq_real, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [row]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    cross, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring
