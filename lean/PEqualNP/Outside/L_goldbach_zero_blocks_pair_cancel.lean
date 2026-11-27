import Mathlib

theorem PEqualNP.Outside.L_goldbach_zero_blocks_pair_cancel :
    ∀ (n : ℕ) (a : Fin n → ℂ) (e : Fin n ≃ Fin n), (∀ i,a (e i) = -a i) → ∑ i,a i=0 := by
  intro n a e h
  have h1 : ∑ i, a (e i) = ∑ i, a i := Equiv.sum_comp e a
  have h2 : ∑ i, a (e i) = -∑ i, a i := by
    have h3 : ∑ i, a (e i) = ∑ i, (-a i) := Finset.sum_congr rfl fun i _ => h i
    rw [h3, Finset.sum_neg_distrib]
  have h5 : ∑ i, a i = -∑ i, a i := h1.symm.trans h2
  have h6 : (∑ i, a i) + ∑ i, a i = 0 := (eq_neg_iff_add_eq_zero).mp h5
  have h7 : (2:ℂ) * ∑ i, a i = 0 := by rw [two_mul]; exact h6
  exact (mul_eq_zero.mp h7).resolve_left (by norm_num)
