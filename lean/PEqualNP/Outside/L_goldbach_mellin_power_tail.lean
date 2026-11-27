import Mathlib

private theorem power_tail_bound (a H N : ℕ) (hHN : H ≤ N) :
    (∑ k ∈ Finset.Ico H N, 1 / ((k : ℝ)+1)^(a+3)) ≤ 2 / ((H : ℝ)+1)^(a+2) := by
  let v := fun k : ℕ => 1 / ((k : ℝ) + 1)
  have ht : (∑ k ∈ Finset.Ico H N, (v k - v (k+1))) = v H - v N := by
    simpa only [Finset.sum_sub_distrib, neg_sub] using congrArg Neg.neg (Finset.sum_Ico_sub v hHN)
  calc
    _ ≤ ∑ k ∈ Finset.Ico H N, (2/((H : ℝ)+1)^(a+1)) * (v k-v (k+1)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hle : (H : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.mp hk).1
      have hden : 1/((k : ℝ)+1)^(a+1) ≤ 1/((H : ℝ)+1)^(a+1) := by gcongr
      have hdiff : 1/((k : ℝ)+1)^2 ≤ 2 * (v k-v (k+1)) := by
        dsimp [v]; push_cast
        field_simp
        nlinarith [Nat.cast_nonneg (α := ℝ) k]
      calc
        _ = (1/((k : ℝ)+1)^(a+1)) * (1/((k : ℝ)+1)^2) := by rw [one_div_mul_one_div, ← pow_add]
        _ ≤ (1/((H : ℝ)+1)^(a+1)) * (2 * (v k-v (k+1))) := mul_le_mul hden hdiff (by positivity) (by positivity)
        _ = _ := by ring
    _ = (2/((H : ℝ)+1)^(a+1))*(v H - v N) := by rw [← Finset.mul_sum, ht]
    _ ≤ (2/((H : ℝ)+1)^(a+1))*v H := by gcongr; exact sub_le_self _ (by dsimp [v]; positivity)
    _ = _ := by dsimp [v]; rw [pow_succ _ (a+1)]; field_simp

theorem PEqualNP.Outside.L_goldbach_mellin_power_tail :
    ∀ a : ℕ, ∃ C : ℝ, 0<C ∧ ∀ H B : ℕ, (∑ k ∈ Finset.Icc H B, 1/((k+1:ℕ):ℝ)^(a+3)) ≤ C/((H+1:ℕ):ℝ)^(a+2) := by
  intro a
  refine ⟨2, by norm_num, ?_⟩
  intro H B
  by_cases h : H ≤ B+1
  · have hI : Finset.Icc H B = Finset.Ico H (B+1) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hI]
    simpa only [Nat.cast_add, Nat.cast_one] using power_tail_bound a H (B+1) h
  · rw [Finset.Icc_eq_empty_of_lt (by omega), Finset.sum_empty]
    positivity
