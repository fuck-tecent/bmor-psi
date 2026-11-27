import Mathlib

namespace PEqualNP.Outside

/-- Replacing factors with norm at most one changes the product by at most the
sum of the individual changes. Expand at one factor and use the triangle
inequality, then induct on the remaining factors. -/
theorem L_goldbach_euler_loss_contractive_swap :
    ∀ (n : ℕ) (u v : Fin n → ℂ), (∀ i, ‖u i‖ ≤ 1 ∧ ‖v i‖ ≤ 1) →
      ‖(∏ i, u i) - (∏ i, v i)‖ ≤ ∑ i, ‖u i - v i‖ := by
  intro n u v h
  have prod_v_bound (s : Finset (Fin n)) : ‖∏ i ∈ s, v i‖ ≤ 1 :=
    (Finset.norm_prod_le s v).trans
      (Finset.prod_le_one₀ (fun i _ ↦ norm_nonneg _) (fun i _ ↦ (h i).2))
  have bound (s : Finset (Fin n)) :
      ‖(∏ i ∈ s, u i) - (∏ i ∈ s, v i)‖ ≤ ∑ i ∈ s, ‖u i - v i‖ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
      let a := ∏ j ∈ s, u j
      let b := ∏ j ∈ s, v j
      change ‖u i * a - v i * b‖ ≤ ‖u i - v i‖ + ∑ j ∈ s, ‖u j - v j‖
      have first : ‖(u i - v i) * b‖ ≤ ‖u i - v i‖ := by
        simpa only [mul_one] using norm_mul_le_of_le le_rfl (prod_v_bound s)
      have second : ‖u i * (a - b)‖ ≤ ∑ j ∈ s, ‖u j - v j‖ := by
        simpa only [one_mul] using norm_mul_le_of_le (h i).1 ih
      calc
        ‖u i * a - v i * b‖ = ‖(u i - v i) * b + u i * (a - b)‖ := by ring_nf
        _ ≤ ‖(u i - v i) * b‖ + ‖u i * (a - b)‖ := norm_add_le _ _
        _ ≤ ‖u i - v i‖ + ∑ j ∈ s, ‖u j - v j‖ := add_le_add first second
  exact bound Finset.univ

end PEqualNP.Outside
