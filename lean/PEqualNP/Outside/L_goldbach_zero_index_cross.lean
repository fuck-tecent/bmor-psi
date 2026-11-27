import Mathlib

theorem PEqualNP.Outside.L_goldbach_zero_index_cross :
    ∀ (m : ℕ) (u : Fin m → ℂ), (∑ j, u j) * (∑ j, star (u j)) - (∑ j, u j * star (u j)) = ∑ j, ∑ l ∈ Finset.univ.erase j, u j * star (u l) := by
  intro m u
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ j)]
