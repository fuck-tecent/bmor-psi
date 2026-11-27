import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_chen_distinct_factor_band_cap :
    ∀ (n D E Q : ℕ) (w : ℕ → ℝ) (B : ℝ), 0 ≤ B → (∀ p ≤ n, w p ≤ B) → let P := (Finset.range (n+1)).filter (fun p => Nat.Prime p ∧ ((Finset.Ioc D E).filter (fun r => Nat.Prime r ∧ ((Finset.Ioc r Q).filter (fun q => Nat.Prime q ∧ p+r*q=n)).Nonempty)).Nonempty); (∑ p ∈ P, w p) ≤ B * (∑ r ∈ (Finset.Ioc D E).filter Nat.Prime, ((min Q (n/r)-r:ℕ):ℝ)) := by
  intro n D E Q w B hB hw P
  let R := (Finset.Ioc D E).filter Nat.Prime
  let F := fun r : ℕ => (Finset.Ioc r (min Q (n/r))).image (fun q => n-r*q)
  have hsub : P ⊆ R.biUnion F := by
    intro p hp
    obtain ⟨_, _, r, hr⟩ := Finset.mem_filter.mp hp
    obtain ⟨hrDE, hrprime, q, hq⟩ := Finset.mem_filter.mp hr
    obtain ⟨hqI, _, heq⟩ := Finset.mem_filter.mp hq
    obtain ⟨hrq, hqQ⟩ := Finset.mem_Ioc.mp hqI
    have hqr : q ≤ n/r := by
      apply (Nat.le_div_iff_mul_le hrprime.pos).mpr
      rw [Nat.mul_comm]
      omega
    apply Finset.mem_biUnion.mpr
    refine ⟨r, Finset.mem_filter.mpr ⟨hrDE, hrprime⟩, Finset.mem_image.mpr ?_⟩
    exact ⟨q, Finset.mem_Ioc.mpr ⟨hrq, le_min hqQ hqr⟩, by omega⟩
  have hc : P.card ≤ ∑ r ∈ R, (min Q (n/r)-r) := calc
    P.card ≤ (R.biUnion F).card := Finset.card_le_card hsub
    _ ≤ ∑ r ∈ R, (F r).card := Finset.card_biUnion_le
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r _
      simpa only [F, ← Nat.card_Ioc] using
        (Finset.card_image_le (s := Finset.Ioc r (min Q (n/r))) (f := fun q => n-r*q))
  calc
    (∑ p ∈ P, w p) ≤ ∑ _p ∈ P, B := by
      apply Finset.sum_le_sum
      intro p hp
      apply hw
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
    _ = B * (P.card : ℝ) := by simp [mul_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact_mod_cast hc
