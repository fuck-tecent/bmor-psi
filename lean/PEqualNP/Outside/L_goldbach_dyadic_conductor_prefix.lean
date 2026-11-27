import Mathlib

theorem PEqualNP.Outside.L_goldbach_dyadic_conductor_prefix :
    ∀ k : ℕ, 2≤k → (∑ j ∈ Finset.Icc 1 (k-2), 1/(2:ℝ)^j) = 1-4/(2:ℝ)^k := by
  have hsum (m : ℕ) : (∑ j ∈ Finset.Icc 1 m, 1/(2:ℝ)^j) = 1-1/(2:ℝ)^m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, pow_succ]
      ring
  intro k hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show 2+m-2 = m by omega, hsum, pow_add]
  norm_num
  ring
