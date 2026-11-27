import Mathlib

theorem PEqualNP.Outside.L_goldbach_minor_shift_energy_anchor :
  ∀ (r : ℕ → ℝ) (n H : ℕ) (e : ℝ), 0 < H → 0 < e → (∑ j ∈ Finset.range H, (r (n + 2 * j)) ^ 2) < (H : ℝ) * e ^ 2 → ∃ j < H, |r (n + 2 * j)| < e := by
  intro r n H e _ he hlt
  by_contra hall
  push Not at hall
  have hge : ∑ _j ∈ Finset.range H, e ^ 2 ≤ ∑ j ∈ Finset.range H, (r (n + 2 * j)) ^ 2 := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hjH : j < H := Finset.mem_range.mp hj
    have habs : e ≤ |r (n + 2 * j)| := hall j hjH
    have hsq : e ^ 2 ≤ |r (n + 2 * j)| ^ 2 := by nlinarith [abs_nonneg (r (n + 2 * j))]
    rwa [sq_abs] at hsq
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hge
  linarith
