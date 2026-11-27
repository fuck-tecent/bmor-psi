import Mathlib

theorem PEqualNP.Outside.L_goldbach_odd_conductor_divisor_budget :
    ∀ (n : ℕ) (Y : ℝ), (∑ d ∈ n.divisors.filter (fun d : ℕ => (d:ℝ) ≤ Y), (Nat.totient d:ℝ)) ≤ max 0 Y * (n.divisors.card:ℝ) := by
  intro n Y
  let S := n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ Y)
  change (∑ d ∈ S, (Nat.totient d : ℝ)) ≤ _
  calc
    _ ≤ ∑ _d ∈ S, max 0 Y := by
      apply Finset.sum_le_sum
      intro d hd
      have hφ : (Nat.totient d : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
      have hdY : (d : ℝ) ≤ Y := (Finset.mem_filter.mp hd).2
      exact hφ.trans (hdY.trans (le_max_right 0 Y))
    _ = max 0 Y * (S.card : ℝ) := by simp [mul_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (le_max_left 0 Y)
      exact_mod_cast n.divisors.card_filter_le (fun d : ℕ => (d : ℝ) ≤ Y)
