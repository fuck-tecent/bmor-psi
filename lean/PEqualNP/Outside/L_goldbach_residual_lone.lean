import Mathlib

theorem PEqualNP.Outside.L_goldbach_residual_lone :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let h := fun k : ℕ => ArithmeticFunction.vonMangoldt k-w k; ∀ X : ℕ, 2≤X → Finset.sum (Finset.range (X+1)) h ≤ ((Nat.sqrt X+1:ℕ):ℝ)*((Nat.log 2 X+1:ℕ):ℝ)*Real.log (X:ℝ) := by
  classical
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
  let h := fun k : ℕ => ArithmeticFunction.vonMangoldt k - w k
  change ∀ X : ℕ, 2 ≤ X → Finset.sum (Finset.range (X + 1)) h ≤ _
  intro X hX
  let S := (Finset.range (X + 1)).filter (fun k => IsPrimePow k ∧ ¬ Nat.Prime k)
  let box := (Finset.range (Nat.sqrt X + 1)).product (Finset.range (Nat.log 2 X + 1))
  let power := fun a : ℕ × ℕ => a.1 ^ a.2
  have hcovered : S ⊆ box.image power := by
    intro k hk
    obtain ⟨hr, hpp, hnp⟩ := Finset.mem_filter.mp hk
    have hkX : k ≤ X := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    obtain ⟨p, j, hp, hj, heq⟩ := (isPrimePow_nat_iff k).mp hpp
    have hjne : j ≠ 1 := by
      rintro rfl
      apply hnp
      simp only [pow_one] at heq
      exact heq ▸ hp
    have hjtwo : 2 ≤ j := by omega
    have hpow : p ^ j ≤ X := heq.trans_le hkX
    have hbase : p ≤ Nat.sqrt X :=
      Nat.le_sqrt'.mpr ((Nat.pow_le_pow_right hp.pos hjtwo).trans hpow)
    have hheight : j ≤ Nat.log 2 X :=
      Nat.le_log_of_pow_le (by decide) ((Nat.pow_le_pow_left hp.two_le j).trans hpow)
    apply Finset.mem_image.mpr
    refine ⟨(p, j), Finset.mem_product.mpr ⟨?_, ?_⟩, heq⟩
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hbase)
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hheight)
  have hcard : S.card ≤ (Nat.sqrt X + 1) * (Nat.log 2 X + 1) := by
    calc
      S.card ≤ (box.image power).card := Finset.card_le_card hcovered
      _ ≤ box.card := Finset.card_image_le
      _ = _ := by simp [box, Finset.card_product]
  have hsum : Finset.sum S h = Finset.sum (Finset.range (X + 1)) h := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hnot
    by_cases hp : Nat.Prime k
    · simp [h, w, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · have hpp : ¬ IsPrimePow k := fun h' => hnot (Finset.mem_filter.mpr ⟨hk, h', hp⟩)
      simp [h, w, hp, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
  have hlog : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  rw [← hsum]
  calc
    Finset.sum S h ≤ Finset.sum S (fun _ => Real.log (X : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hr, hpp, hnp⟩ := Finset.mem_filter.mp hk
      have hkX := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hpp.pos
      have hlogle := Real.log_le_log hkpos (show (k : ℝ) ≤ (X : ℝ) by exact_mod_cast hkX)
      simpa only [h, w, if_neg hnp, sub_zero] using
        (ArithmeticFunction.vonMangoldt_le_log.trans hlogle)
    _ = (S.card : ℝ) * Real.log (X : ℝ) := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hlog
