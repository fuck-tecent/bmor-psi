import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin

private theorem block_aux (m : ℕ) (S : Fin m → ℂ) :
    ‖∑ i, S i‖ ^ 2 - (∑ i, ‖S i‖ ^ 2) = ∑ i, ∑ l ∈ Finset.univ.erase i, (S i * star (S l)).re := by
  have h1 : ∀ z : ℂ, ‖z‖ ^ 2 = (z * star z).re := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.mul_re]
  have h2 : ‖∑ i, S i‖ ^ 2 = ∑ i, ∑ l, (S i * star (S l)).re := by
    rw [h1, star_sum, Finset.sum_mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
  have h3 : ∀ i, ∑ l, (S i * star (S l)).re
      = ‖S i‖ ^ 2 + ∑ l ∈ Finset.univ.erase i, (S i * star (S l)).re := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), h1]
  rw [h2]
  simp only [h3, Finset.sum_add_distrib]
  ring

theorem PEqualNP.Outside.L_goldbach_cluster_block_remainder :
    ∀ (m k : ℕ) (u : Fin m → Fin k → ℂ), ‖∑ i, ∑ j, u i j‖^2-(∑ i, ‖∑ j, u i j‖^2) = ∑ i, ∑ l ∈ Finset.univ.erase i, ((∑ j, u i j)*star (∑ j, u l j)).re := by
  intro m k u
  exact block_aux m (fun i => ∑ j, u i j)
