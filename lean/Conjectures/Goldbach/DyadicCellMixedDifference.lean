import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.DyadicCellMixedDifference :
    ∀ (H : ℕ) (a b : Fin H → ℝ),
      (∑ s, ∑ t, (a s - a t)*(b s - b t))
        = 2*((H:ℝ)*(∑ s, a s*b s) - (∑ s, a s)*(∑ t, b t)) := by
  intro H a b
  have hexp : ∀ s t : Fin H, (a s - a t)*(b s - b t)
      = a s*b s - a s*b t - a t*b s + a t*b t := fun s t => by ring
  have h1 : (∑ s : Fin H, ∑ t : Fin H, a s*b s) = (H:ℝ) * ∑ s, a s*b s := by
    have hinner : ∀ s : Fin H, (∑ t : Fin H, a s*b s) = (H:ℝ) * (a s*b s) := by
      intro s
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [hinner]
    rw [← Finset.mul_sum]
  have h2 : (∑ s : Fin H, ∑ t : Fin H, a s*b t) = (∑ s, a s) * (∑ t, b t) := by
    rw [Finset.sum_mul_sum]
  have h3 : (∑ s : Fin H, ∑ t : Fin H, a t*b s) = (∑ s, a s) * (∑ t, b t) := by
    rw [Finset.sum_comm, Finset.sum_mul_sum]
  have h4 : (∑ s : Fin H, ∑ t : Fin H, a t*b t) = (H:ℝ) * ∑ s, a s*b s := by
    have hinner : ∀ s : Fin H, (∑ t : Fin H, a t*b t) = ∑ t : Fin H, a t*b t := fun s => rfl
    rw [Finset.sum_comm]
    have hinner' : ∀ t : Fin H, (∑ s : Fin H, a t*b t) = (H:ℝ) * (a t*b t) := by
      intro t
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [hinner']
    rw [← Finset.mul_sum]
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3, h4]
  ring
