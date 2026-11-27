import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_finite_phase_bmor_tail_cost :
    (∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 8000000000 ≤ n → |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q| ≤ (n:ℝ)/(840 * Real.log (n:ℝ))) → let D := fun (q a n : ℕ) => (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/(Nat.totient q:ℝ); let J := fun (q a l u : ℕ) (β : ℝ) => 2 * Real.pi * |β| * (∑ m ∈ Finset.Ico l u, |D q a m|); let T : ℕ := 8000000000; ∀ (q a n : ℕ) (β : ℝ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 4000000000000000000 ≤ n → |β| ≤ 105/((q:ℝ)*n) → |D q a n| + J q a T n β ≤ (n:ℝ)/(840*Real.log n) + 105*Real.pi*n/(840*(q:ℝ)*Real.log T) := by
  intro hBMOR D J T q a n β hq hq' ha hcop hn hβ
  have hT : 1 < (T : ℝ) := by norm_num [T]
  have hlog : 0 < Real.log (T : ℝ) := Real.log_pos hT
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply add_le_add (hBMOR q a n hq hq' ha hcop (by omega))
  have hprefix (k : ℕ) : (∑ m ∈ Finset.range k, (m : ℝ)) ≤ (k : ℝ)^2 / 2 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Nat.cast_succ]
      linarith [sq_nonneg (k : ℝ)]
  have hsum : (∑ m ∈ Finset.Ico T n, |D q a m|) ≤ ((n : ℝ)^2 / 2) / (840 * Real.log T) := by
    calc
      _ ≤ ∑ m ∈ Finset.Ico T n, (m : ℝ) / (840 * Real.log T) := by
        apply Finset.sum_le_sum
        intro m hm
        have hTm := (Finset.mem_Ico.mp hm).1
        apply (hBMOR q a m hq hq' ha hcop hTm).trans
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by exact_mod_cast hTm)) (by norm_num)
      _ = (∑ m ∈ Finset.Ico T n, (m : ℝ)) / (840 * Real.log T) := by rw [Finset.sum_div]
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.range n) ?_ ?_) (hprefix n)
        · intro m hm
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp hm).2
        · intros; positivity
  change 2 * Real.pi * |β| * _ ≤ _
  calc
    _ ≤ (2 * Real.pi * (105 / ((q : ℝ) * n))) * (((n : ℝ)^2 / 2) / (840 * Real.log T)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hβ (by positivity)) hsum
      · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
      · positivity
    _ = _ := by field_simp
