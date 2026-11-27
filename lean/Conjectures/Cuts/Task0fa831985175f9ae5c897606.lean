import Mathlib

theorem Conjectures.Cuts.Task0fa831985175f9ae5c897606 :
    ∀ (x1 : ℕ), ↑{x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) | x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1 ∧ Nat.Prime x2 ∧ Nat.Prime (x2 + (2 : ℕ))}.card ≤ ∑ x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)), if x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1 ∧ Nat.Prime x2 ∧ Nat.Prime (x2 + (2 : ℕ)) then Real.log ↑x2 * Real.log ↑(x2 + (2 : ℕ)) else (0 : ℝ) := by
  intro X
  calc
    _ = ∑ n ∈ (Finset.range (2*X+1)).filter (fun n =>
        X < n ∧ 50*n < 51*X ∧ n.Prime ∧ (n+2).Prime), (1 : ℝ) := by simp
    _ ≤ _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro n _
      by_cases h : X < n ∧ 50*n < 51*X ∧ n.Prime ∧ (n+2).Prime
      · simp only [ite_eq_left h]
        have h3 : 3 ≤ n := by
          have hL := h.1
          have hR := h.2.1
          omega
        have hLog {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
          rw [← Real.log_exp (1 : ℝ)]
          exact Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_three.le.trans hx)
        have hn : 1 ≤ Real.log (n : ℝ) := hLog (by exact_mod_cast h3)
        have hn2 : 1 ≤ Real.log ((n+2 : ℕ) : ℝ) := hLog (by exact_mod_cast (show 3 ≤ n+2 by omega))
        simpa only [one_mul] using mul_le_mul hn hn2 (by norm_num : 0 ≤ (1 : ℝ)) (zero_le_one.trans hn)
      · simp [h]
