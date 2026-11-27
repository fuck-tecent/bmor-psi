import Mathlib

theorem Conjectures.TwinPrimes.RoughWindowFactorShapes :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X);
    let z := fun (X : ℕ) => Nat.sqrt X / 2;
    ∀ (X p : ℕ), 4096 ≤ X → p ∈ w X → z X ≤ (p+2).minFac → (p+2).Prime ∨ (∃ r s : ℕ, r.Prime ∧ s.Prime ∧ z X ≤ r ∧ r ≤ s ∧ r ≤ Nat.sqrt (2*X+2) ∧ p+2=r*s) := by
  intro w z X p hX hp hz
  have hp' : p ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X) := hp
  obtain ⟨hp2, hXp, h50⟩ := Finset.mem_filter.mp hp'
  have hNle : p + 2 ≤ 2*X + 2 := by omega
  have hzdef : z X = Nat.sqrt X / 2 := rfl
  rw [hzdef] at hz ⊢
  by_cases hprime : (p+2).Prime
  · exact Or.inl hprime
  · right
    have hpos : 0 < p+2 := by omega
    have hN1 : p+2 ≠ 1 := by omega
    have hrp : ((p+2).minFac).Prime := Nat.minFac_prime hN1
    have hrdvd : (p+2).minFac ∣ (p+2) := Nat.minFac_dvd _
    have hrs : (p+2).minFac ≤ (p+2)/(p+2).minFac := Nat.minFac_le_div hpos hprime
    have hN : (p+2).minFac * ((p+2)/(p+2).minFac) = (p+2) := Nat.mul_div_cancel' hrdvd
    have hbig : 2*X + 2 < (Nat.sqrt X / 2)^3 := by
      have hk2 : 64 ≤ Nat.sqrt X := by
        rw [Nat.le_sqrt]
        norm_num
        exact hX
      set j := Nat.sqrt X / 2 with hj
      have hj32 : 32 ≤ j := by omega
      have hk1 : X < (Nat.sqrt X + 1)^2 := by
        simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' X
      have hk3 : Nat.sqrt X + 1 ≤ 2*j + 2 := by omega
      have hs2 : (Nat.sqrt X + 1)^2 ≤ (2*j + 2)^2 := Nat.pow_le_pow_left hk3 2
      have hX' : X < (2*j + 2)^2 := lt_of_lt_of_le hk1 hs2
      have hkey2 : 8*j^2 + 16*j + 10 ≤ j^3 := by nlinarith [hj32]
      have hX2 : 2*X + 2 < 8*j^2 + 16*j + 10 := by nlinarith [hX']
      exact lt_of_lt_of_le hX2 hkey2
    have hsp : ((p+2)/(p+2).minFac).Prime := by
      by_contra hsp
      have hs0 : 0 < (p+2)/(p+2).minFac := by
        rcases Nat.eq_zero_or_pos ((p+2)/(p+2).minFac) with h | h
        · rw [h, mul_zero] at hN
          omega
        · exact h
      have hs1 : (p+2)/(p+2).minFac ≠ 1 := by
        intro h
        rw [h, mul_one] at hN
        exact hprime (hN ▸ hrp)
      have hmf : (((p+2)/(p+2).minFac).minFac).Prime := Nat.minFac_prime hs1
      have hmf2 : 2 ≤ ((p+2)/(p+2).minFac).minFac := hmf.two_le
      have hmfdvd : ((p+2)/(p+2).minFac).minFac ∣ ((p+2)/(p+2).minFac) := Nat.minFac_dvd _
      have hsdvd : (p+2)/(p+2).minFac ∣ (p+2) := ⟨(p+2).minFac, hN.symm.trans (mul_comm _ _)⟩
      have hmfdvdN : ((p+2)/(p+2).minFac).minFac ∣ (p+2) := dvd_trans hmfdvd hsdvd
      have hle : (p+2).minFac ≤ ((p+2)/(p+2).minFac).minFac := Nat.minFac_le_of_dvd hmf2 hmfdvdN
      have hmfle : ((p+2)/(p+2).minFac).minFac ≤ ((p+2)/(p+2).minFac)/((p+2)/(p+2).minFac).minFac := Nat.minFac_le_div hs0 hsp
      have hmul := Nat.mul_div_cancel' hmfdvd
      have hssq : ((p+2)/(p+2).minFac).minFac * ((p+2)/(p+2).minFac).minFac ≤ (p+2)/(p+2).minFac := by
        calc ((p+2)/(p+2).minFac).minFac * ((p+2)/(p+2).minFac).minFac
            ≤ ((p+2)/(p+2).minFac).minFac * (((p+2)/(p+2).minFac) / ((p+2)/(p+2).minFac).minFac) := Nat.mul_le_mul_left _ hmfle
          _ = (p+2)/(p+2).minFac := hmul
      have hr2le : (p+2).minFac * (p+2).minFac ≤ (p+2)/(p+2).minFac :=
        le_trans (Nat.mul_le_mul hle hle) hssq
      have hr3le : (p+2).minFac^3 ≤ (p+2) := by
        calc (p+2).minFac^3 = (p+2).minFac * ((p+2).minFac * (p+2).minFac) := by ring
          _ ≤ (p+2).minFac * ((p+2)/(p+2).minFac) := Nat.mul_le_mul_left _ hr2le
          _ = (p+2) := hN
      have hz3 : (Nat.sqrt X / 2)^3 ≤ (p+2).minFac^3 := Nat.pow_le_pow_left hz 3
      have hmid : (Nat.sqrt X / 2)^3 ≤ p+2 := le_trans hz3 hr3le
      omega
    have hsqrt : (p+2).minFac ≤ Nat.sqrt (2*X+2) := by
      rw [Nat.le_sqrt]
      calc (p+2).minFac * (p+2).minFac ≤ (p+2).minFac * ((p+2)/(p+2).minFac) := Nat.mul_le_mul_left _ hrs
        _ = (p+2) := hN
        _ ≤ 2*X + 2 := hNle
    exact ⟨(p+2).minFac, (p+2)/(p+2).minFac, hrp, hsp, hz, hrs, hsqrt, hN.symm⟩
