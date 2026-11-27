import Mathlib
theorem Conjectures.Goldbach.FiniteWheelInjectiveProjectionLift : ∀ (P S : Finset ℕ) (b W B n : ℕ), b<W → B+2≤n → Nat.Coprime ((n+W-b) % W) W → P.card<S.card → (∀ p ∈ S, Nat.Prime p ∧ p≤B ∧ p % W=b) → (∀ r ∈ P, Nat.Prime r ∧ Set.InjOn (fun p : ℕ => p % r) (S : Set ℕ)) → ∃ p ∈ S, p≤B ∧ 2≤n-p ∧ Nat.Coprime (n-p) (W*(∏ r ∈ P, r)) := by
  intro P S b W B n hb hn hW hcard hS hP
  let bad := fun r : ℕ => S.filter (fun p => r ∣ n-p)
  let U := P.biUnion bad
  have hbad (r : ℕ) (hr : r ∈ P) : (bad r).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha c hc
    have haS : a ∈ S := (Finset.mem_filter.mp ha).1
    have hcS : c ∈ S := (Finset.mem_filter.mp hc).1
    have haN : a ≤ n := by have := (hS a haS).2.1; omega
    have hcN : c ≤ n := by have := (hS c hcS).2.1; omega
    have ham : a % r = n % r := by
      have hd : n-a ≡ 0 [MOD r] := Nat.modEq_zero_iff_dvd.mpr (Finset.mem_filter.mp ha).2
      have he := hd.add (Nat.ModEq.refl a)
      simpa [Nat.ModEq, Nat.sub_add_cancel haN] using he.symm
    have hcm : c % r = n % r := by
      have hd : n-c ≡ 0 [MOD r] := Nat.modEq_zero_iff_dvd.mpr (Finset.mem_filter.mp hc).2
      have he := hd.add (Nat.ModEq.refl c)
      simpa [Nat.ModEq, Nat.sub_add_cancel hcN] using he.symm
    exact (hP r hr).2 haS hcS (ham.trans hcm.symm)
  have hU : U.card ≤ P.card := by
    calc
      U.card ≤ ∑ r ∈ P, (bad r).card := Finset.card_biUnion_le
      _ ≤ ∑ r ∈ P, (1:ℕ) := Finset.sum_le_sum hbad
      _ = P.card := by simp
  have hnot : ¬ S ⊆ U := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨p, hpS, hpU⟩ := Finset.not_subset.mp hnot
  have hpB := (hS p hpS).2.1
  have hpN : p ≤ n := by omega
  refine ⟨p, hpS, hpB, by omega, ?_⟩
  apply Nat.Coprime.mul_right
  · have hnmod : n ≡ n+W [MOD W] := by simp [Nat.ModEq]
    have hpmod : p ≡ b [MOD W] := by simp [Nat.ModEq, Nat.mod_eq_of_lt hb, (hS p hpS).2.2]
    have hsub : n-p ≡ n+W-b [MOD W] := hnmod.sub hpN (by omega) hpmod
    unfold Nat.ModEq at hsub
    unfold Nat.Coprime at hW ⊢
    rw [Nat.gcd_comm (n-p) W, Nat.gcd_rec, hsub, Nat.gcd_comm]
    simpa [Nat.gcd_comm] using hW
  · apply Nat.Coprime.prod_right
    intro r hr
    have hrd : ¬ r ∣ n-p := by
      intro hd
      apply hpU
      exact Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_filter.mpr ⟨hpS, hd⟩⟩
    exact ((hP r hr).1.coprime_iff_not_dvd.mpr hrd).symm



