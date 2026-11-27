import Mathlib

theorem Conjectures.Cuts.Taskf66d06f7b29c0f33233b4b7a :
    ∀ (x1 : ℕ), (3 : ℕ) ≤ x1 → Real.log ↑x1 ^ (2 : ℕ) * ↑{x3 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) | x1 < x3 ∧ (50 : ℕ) * x3 < (51 : ℕ) * x1 ∧ Nat.Prime x3 ∧ Nat.Prime (x3 + (2 : ℕ))}.card ≤ ∑ x3 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)), if x1 < x3 ∧ (50 : ℕ) * x3 < (51 : ℕ) * x1 ∧ Nat.Prime x3 ∧ Nat.Prime (x3 + (2 : ℕ)) then Real.log ↑x3 * Real.log ↑(x3 + (2 : ℕ)) else (0 : ℝ) := by
  intro X hX
  let I := Finset.range (2 * X + 1)
  let P : ℕ → Prop := fun n => X < n ∧ 50 * n < 51 * X ∧ n.Prime ∧ (n + 2).Prime
  let w : ℕ → ℝ := fun n => Real.log (n : ℝ) * Real.log ((n + 2 : ℕ) : ℝ)
  classical
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hXlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ X by omega))
  calc
    _ = ∑ n ∈ I.filter P, (Real.log (X : ℝ)) ^ 2 := by
      simp [I, P, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ n ∈ I.filter P, w n := by
      apply Finset.sum_le_sum
      intro n hn
      have hN : X < n := (Finset.mem_filter.mp hn).2.1
      have hlo : Real.log (X : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log hXreal (by exact_mod_cast hN.le)
      have hhi : Real.log (X : ℝ) ≤ Real.log ((n + 2 : ℕ) : ℝ) :=
        Real.log_le_log hXreal (by exact_mod_cast (show X ≤ n + 2 by omega))
      rw [pow_two]
      exact mul_le_mul hlo hhi hXlog (hXlog.trans hlo)
    _ = _ := by simp only [Finset.sum_filter, I, P, w]
