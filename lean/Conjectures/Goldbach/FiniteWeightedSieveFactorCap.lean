import Mathlib

open scoped BigOperators

noncomputable section

namespace WCap

lemma weighted_cap_core (n z y s r : ℕ) (hz : 2 ≤ z) (hzy : z < y)
    (hs : 2 ≤ s) (hsn : s < n)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ s → z ≤ p)
    (hny : n ≤ y ^ (r+1)) (hzn : n ≤ z * y^r)
    (hW : 0 < (2:ℤ)
      - ((((Finset.Ico z y).filter Nat.Prime).filter (fun p => p ∣ s)).card : ℤ)
      - ((((Finset.Ico z y).filter Nat.Prime).filter (fun p => p^2 ∣ s)).card : ℤ)) :
    s.primeFactorsList.length ≤ r := by
  classical
  set P : Finset ℕ := (Finset.Ico z y).filter Nat.Prime with hP
  set A : Finset ℕ := P.filter (fun p => p ∣ s) with hA
  set B : Finset ℕ := P.filter (fun p => p^2 ∣ s) with hB
  have hAB : A.card + B.card ≤ 1 := by
    have h : (A.card : ℤ) + (B.card : ℤ) < 2 := by
      have := hW
      rw [hA, hB, hP] at this
      omega
    omega
  have hs0 : s ≠ 0 := by omega
  set e : ℕ → ℕ := fun p => s.factorization p with he
  set supp : Finset ℕ := s.primeFactors with hsupp
  have hprod : s = ∏ p ∈ supp, p ^ e p := by
    rw [hsupp, he]; exact Nat.prod_primeFactors_pow_factorization hs0
  -- 长度 = 指数和
  have hlen_supp : s.primeFactorsList.length = ∑ p ∈ s.primeFactors, e p := by
    rw [← List.sum_toFinset_count_eq_length s.primeFactorsList]
    simp only [Nat.toFinset_factors]
    rw [he]
    exact Finset.sum_congr rfl (fun p _ => Nat.primeFactorsList_count_eq)
  have hlen : s.primeFactorsList.length = ∑ p ∈ supp, e p := by
    rw [hlen_supp, ← hsupp]
  set low : Finset ℕ := supp.filter (fun p => p < y) with hlow
  set high : Finset ℕ := supp.filter (fun p => ¬ p < y) with hhigh
  -- low 的每个元素在 A 中，且指数为 1
  have hlowA : ∀ p ∈ low, p ∈ A := by
    intro p hp
    rw [hlow, Finset.mem_filter] at hp
    obtain ⟨hpsupp, hpy⟩ := hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpsupp
    have hpdvd : p ∣ s := (Nat.mem_primeFactors.mp hpsupp).2.1
    have hpz : z ≤ p := hprime p hpp hpdvd
    rw [hA]
    refine Finset.mem_filter.mpr ⟨?_, hpdvd⟩
    rw [hP]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hpz, hpy⟩, hpp⟩
  have hlow_e : ∀ p ∈ low, e p = 1 := by
    intro p hp
    have hpsupp : p ∈ supp := (Finset.mem_filter.mp (by rwa [hlow] at hp)).1
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpsupp
    have hpdvd : p ∣ s := (Nat.mem_primeFactors.mp hpsupp).2.1
    have he1 : 1 ≤ e p := (hpp.dvd_iff_one_le_factorization hs0).mp hpdvd
    by_contra hne
    have he2 : 2 ≤ e p := by omega
    have hp2 : p^2 ∣ s := (hpp.pow_dvd_iff_le_factorization hs0).mpr he2
    have hpinB : p ∈ B := by
      have hpy : p < y := (Finset.mem_filter.mp hp).2
      have hpP : p ∈ P := by
        rw [hP]
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hprime p hpp hpdvd, hpy⟩, hpp⟩
      rw [hB, Finset.mem_filter]
      exact ⟨hpP, hp2⟩
    have hpinA : p ∈ A := (hA ▸ hlowA p hp)
    have hAcard : 1 ≤ A.card := Finset.card_pos.mpr ⟨p, hpinA⟩
    have hBcard : 1 ≤ B.card := Finset.card_pos.mpr ⟨p, hpinB⟩
    omega
  have hlow_card : low.card ≤ 1 := by
    by_contra h
    have h2 : 1 < low.card := by omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h2
    have hpA := hlowA p hp
    have hqA := hlowA q hq
    have hsub : ({p, q} : Finset ℕ) ⊆ A := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hpA
      · exact hqA
    have hcard : ({p, q} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hpq]), Finset.card_singleton]
    have := Finset.card_le_card hsub
    rw [hcard] at this
    omega
  -- 高因子：p ≥ y
  have hhigh_ge : ∀ p ∈ high, y ≤ p := by
    intro p hp
    rw [hhigh, Finset.mem_filter] at hp
    obtain ⟨hpsupp, hpy⟩ := hp
    have hpdvd : p ∣ s := (Nat.mem_primeFactors.mp hpsupp).2.1
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpsupp
    have hpz : z ≤ p := hprime p hpp hpdvd
    omega
  have hprod_low_le : (∏ p ∈ low, p) ≤ ∏ p ∈ low, p ^ e p := by
    refine Finset.prod_le_prod (fun p hp => ?_)
    have hpdvd : p ∣ s := (Nat.mem_primeFactors.mp ((Finset.mem_filter.mp (by rwa [hlow] at hp)).1)).2.1
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors ((Finset.mem_filter.mp (by rwa [hlow] at hp)).1)
    have he1 : 1 ≤ e p := (hpp.dvd_iff_one_le_factorization hs0).mp hpdvd
    have hle : p ^ 1 ≤ p ^ e p := Nat.pow_le_pow_right (Nat.Prime.pos hpp) he1
    simpa using hle
  have hprod_high_le : (∏ p ∈ high, y ^ e p) ≤ ∏ p ∈ high, p ^ e p := by
    refine Finset.prod_le_prod (fun p hp => ?_)
    have hyp : y ≤ p := hhigh_ge p hp
    exact Nat.pow_le_pow_left hyp (e p)
  -- 分解乘积
  have hprodsplit : (∏ p ∈ low, p ^ e p) * (∏ p ∈ high, p ^ e p) = s := by
    rw [hlow, hhigh]
    rw [Finset.prod_filter_mul_prod_filter_not supp (fun p => p < y) (fun p => p ^ e p)]
    exact hprod.symm
  have hlen_split : s.primeFactorsList.length = low.card + ∑ p ∈ high, e p := by
    rw [hlen]
    rw [← Finset.sum_filter_add_sum_filter_not supp (fun p => p < y) (fun p => e p)]
    have hlow_sum : (∑ p ∈ low, e p) = low.card := by
      rw [hlow]
      rw [Finset.sum_congr rfl (fun p hp => hlow_e p (by rw [hlow]; exact hp))]
      simp
    rw [hlow_sum, hlow, hhigh]
  -- 下界
  have hlow_prod_ge : (z : ℕ) ^ low.card ≤ ∏ p ∈ low, p := by
    rcases Nat.eq_zero_or_pos low.card with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0]; simp
    · have h1 : low.card = 1 := by omega
      obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp h1
      have hplow : p ∈ low := by rw [hp_eq]; simp
      have hpsupp : p ∈ supp := (Finset.mem_filter.mp (by rwa [hlow] at hplow)).1
      have hpz : z ≤ p :=
        hprime p (Nat.prime_of_mem_primeFactors hpsupp)
          ((Nat.mem_primeFactors.mp hpsupp).2.1)
      have hprod : (∏ x ∈ low, x) = p := by rw [hp_eq]; simp
      rw [h1, hprod]
      simpa using hpz
  have hhigh_prod_eq : (∏ p ∈ high, y ^ e p) = y ^ (∑ p ∈ high, e p) :=
    Finset.prod_pow_eq_pow_sum high e y
  -- 若长度 > r 则矛盾
  by_contra hle
  have hm : r + 1 ≤ s.primeFactorsList.length := by omega
  rcases Nat.eq_zero_or_pos low.card with h0 | hpos
  · -- low 空：m = highsum
    have hm' : r+1 ≤ ∑ p ∈ high, e p := by rw [hlen_split, h0] at hm; simpa using hm
    have hlowzero : (∏ p ∈ low, p^e p) = 1 := by
      rw [Finset.card_eq_zero.mp h0]
      simp
    have hsge : y ^ (r+1) ≤ s := by
      have h1 : y ^ (∑ p ∈ high, e p) ≤ s := by
        calc y ^ (∑ p ∈ high, e p) = ∏ p ∈ high, y ^ e p := hhigh_prod_eq.symm
          _ ≤ ∏ p ∈ high, p ^ e p := hprod_high_le
          _ = s := by
            have := hprodsplit
            rw [hlowzero, one_mul] at this
            exact this
      exact le_trans (pow_le_pow_right₀ (by omega : 1 ≤ y) hm') h1
    exact absurd hsn (not_lt.mpr (le_trans hny hsge))
  · have h1 : low.card = 1 := by omega
    have hm' : r ≤ ∑ p ∈ high, e p := by
      rw [hlen_split, h1] at hm; omega
    have hlowprod : z ≤ ∏ p ∈ low, p := by
      have := hlow_prod_ge
      rw [h1] at this; simpa using this
    have hhighprod : y ^ r ≤ ∏ p ∈ high, y ^ e p := by
      rw [hhigh_prod_eq]
      exact pow_le_pow_right₀ (by omega : 1 ≤ y) hm'
    have hsge : z * y^r ≤ s := by
      calc z * y^r ≤ (∏ p ∈ low, p) * (∏ p ∈ high, y^e p) :=
            Nat.mul_le_mul hlowprod hhighprod
        _ ≤ (∏ p ∈ low, p^e p) * (∏ p ∈ high, p^e p) :=
            Nat.mul_le_mul hprod_low_le hprod_high_le
        _ = s := hprodsplit
    exact absurd hsn (not_lt.mpr (le_trans hzn hsge))

end WCap

/-- 冻结 statement 的 wrapper。 -/
theorem PEqualNP.Outside.L_goldbach_finite_weighted_sieve_factor_cap :
    let W := fun (z y s : ℕ) => let P := (Finset.Ico z y).filter Nat.Prime; (2:ℤ)-((P.filter (fun p => p∣s)).card:ℤ)-((P.filter (fun p => p^2∣s)).card:ℤ); ∀ (n z y s r : ℕ), 2 ≤ z → z < y → 2 ≤ s → s < n → (∀ p : ℕ, p.Prime → (p ∣ s) → z ≤ p) → n ≤ y^(r+1) → n ≤ z*y^r → 0 < W z y s → s.primeFactorsList.length ≤ r := by
  dsimp only
  intro n z y s r hz hzy hs hsn hprime hny hzn hW
  exact WCap.weighted_cap_core n z y s r hz hzy hs hsn hprime hny hzn hW

/-- 新批提交口径的 module 名（Lead 裁定：module 名必须存在）。 -/
theorem Conjectures.Goldbach.FiniteWeightedSieveFactorCap :
    let W := fun (z y s : ℕ) => let P := (Finset.Ico z y).filter Nat.Prime; (2:ℤ)-((P.filter (fun p => p∣s)).card:ℤ)-((P.filter (fun p => p^2∣s)).card:ℤ); ∀ (n z y s r : ℕ), 2 ≤ z → z < y → 2 ≤ s → s < n → (∀ p : ℕ, p.Prime → (p ∣ s) → z ≤ p) → n ≤ y^(r+1) → n ≤ z*y^r → 0 < W z y s → s.primeFactorsList.length ≤ r :=
  PEqualNP.Outside.L_goldbach_finite_weighted_sieve_factor_cap
