import Mathlib

theorem PEqualNP.Outside.L_goldbach_euler_loss_finite_lower :
    ∀ (n : ℕ) (z : Fin n → ℂ), (∀ i,‖z i‖≤1) → (∏ i, (1-‖z i‖))≤‖∏ i,(1-z i)‖ := by
  intro n z hz
  have key : ∀ (s : Finset (Fin n)), (∏ i ∈ s, (1 - ‖z i‖)) ≤ ‖∏ i ∈ s, (1 - z i)‖ := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, norm_mul]
        have h1 : (0:ℝ) ≤ 1 - ‖z a‖ := by linarith [hz a]
        have hQ : (0:ℝ) ≤ ‖∏ i ∈ s, (1 - z i)‖ := norm_nonneg _
        have hfac : 1 - ‖z a‖ ≤ ‖1 - z a‖ := by
          have := norm_sub_norm_le (1:ℂ) (z a)
          simpa using this
        calc (1 - ‖z a‖) * ∏ i ∈ s, (1 - ‖z i‖) ≤ (1 - ‖z a‖) * ‖∏ i ∈ s, (1 - z i)‖ :=
              mul_le_mul_of_nonneg_left ih h1
          _ ≤ ‖1 - z a‖ * ‖∏ i ∈ s, (1 - z i)‖ :=
              mul_le_mul_of_nonneg_right hfac hQ
  simpa using key Finset.univ
