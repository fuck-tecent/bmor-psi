import Mathlib

theorem PEqualNP.Outside.L_goldbach_euler_tail_defect :
    ∀ (T : Finset ℕ) (u : ℕ → ℝ), (∀ p ∈ T, 0≤u p ∧ u p≤1) → 1-Finset.prod T (fun p => 1-u p) ≤ Finset.sum T u := by
  intro T u
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p T hp ih =>
    intro h
    have hT : ∀ q ∈ T, 0 ≤ u q ∧ u q ≤ 1 :=
      fun q hq => h q (Finset.mem_insert_of_mem hq)
    obtain ⟨hp₀, hp₁⟩ := h p (Finset.mem_insert_self p T)
    have hsum : 0 ≤ Finset.sum T u := Finset.sum_nonneg fun q hq => (hT q hq).1
    rw [Finset.prod_insert hp, Finset.sum_insert hp]
    nlinarith [mul_le_mul_of_nonneg_left (ih hT) (sub_nonneg.mpr hp₁),
      mul_nonneg hp₀ hsum]
