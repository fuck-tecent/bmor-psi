import Mathlib

private lemma windowCard (n p : ℕ) (hp : p.Prime) (T : Finset ℕ)
    (bounds : ∀ a ∈ T, n ≤ 3*p^a ∧ 3*p^a ≤ 2*n) : T.card ≤ 2 := by
  by_cases hT : T.Nonempty
  · let m := T.min' hT
    have hm := (bounds m (T.min'_mem hT)).1
    have sub : T ⊆ Finset.Icc m (m+1) := by
      intro a ha
      refine Finset.mem_Icc.mpr ⟨T.min'_le _ ha, ?_⟩
      by_contra! h
      have ha' := (bounds a ha).2
      have hh := Nat.pow_le_pow_right hp.pos (show m+2 ≤ a by omega)
      rw [pow_add] at hh
      have hfour : 4 ≤ p^2 := by have := hp.two_le; nlinarith
      have mul := Nat.mul_le_mul_left (p^m) hfour
      have := pow_pos hp.pos m
      omega
    have hcount := Finset.card_le_card sub
    rw [Nat.card_Icc] at hcount
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hT]

private lemma totalRamified :
    ∀ n : ℕ, 2≤n → (∑ k ∈ (Finset.range (n+1)).filter (fun k => n≤3*k ∧ 3*k≤2*n ∧ ¬k.Coprime n), ArithmeticFunction.vonMangoldt k) ≤ 2*Real.log (n:ℝ) := by
  intro n hn
  let K := (Finset.range (n+1)).filter (fun k => n ≤ 3*k ∧ 3*k ≤ 2*n ∧ ¬k.Coprime n)
  let T := K.filter IsPrimePow
  let E (p : ℕ) := (Finset.range (n+1)).filter (fun a => 0 < a ∧ n ≤ 3*p^a ∧ 3*p^a ≤ 2*n)
  have repr {k : ℕ} (hk : k ∈ T) :
      k.minFac ∈ n.primeFactors ∧ ∃ a ∈ E k.minFac, k.minFac^a = k := by
    obtain ⟨hkK,hpp⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkN,hlo,hhi,hbad⟩ := Finset.mem_filter.mp hkK
    obtain ⟨p,a,hp,ha,rfl⟩ := (isPrimePow_nat_iff k).1 hpp
    rw [Nat.pow_minFac ha.ne', hp.minFac_eq]
    have hd : p ∣ n := by
      by_contra h
      exact hbad ((hp.coprime_iff_not_dvd.2 h).pow_left a)
    refine ⟨Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩, a, Finset.mem_filter.mpr ⟨?_,ha,hlo,hhi⟩, rfl⟩
    have hpow := Nat.pow_le_pow_left hp.two_le a
    have hsmall : a < 2^a := Nat.lt_two_pow_self
    exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hkN; omega)
  have fiber (p : ℕ) (hp : p ∈ n.primeFactors) :
      (∑ k ∈ T.filter (fun k => k.minFac=p), ArithmeticFunction.vonMangoldt k) ≤ 2*Real.log (p:ℝ) := by
    have hsub : T.filter (fun k => k.minFac=p) ⊆ (E p).image (fun a => p^a) := by
      intro k hk
      obtain ⟨hkT,hbase⟩ := Finset.mem_filter.mp hk
      have hrep := (repr hkT).2
      rw [hbase] at hrep
      exact Finset.mem_image.mpr hrep
    have hcard := windowCard n p (Nat.prime_of_mem_primeFactors hp) (E p)
      (fun a ha => (Finset.mem_filter.mp ha).2.2)
    have count := (Finset.card_le_card hsub).trans (Finset.card_image_le.trans hcard)
    calc
      _ = ∑ _k ∈ T.filter (fun k => k.minFac=p), Real.log (p:ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        obtain ⟨hkT,hbase⟩ := Finset.mem_filter.mp hk
        rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (Finset.mem_filter.mp hkT).2, hbase]
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast count)
          (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))
  have hlog : (∑ p ∈ n.primeFactors, Real.log (p:ℝ)) ≤ Real.log (n:ℝ) := by
    rw [← Real.log_prod (s := n.primeFactors) (f := fun p : ℕ => (p:ℝ)) (fun p hp => (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero : (p:ℝ) ≠ 0))]
    rw [← Nat.cast_prod]
    apply Real.log_le_log
    · exact_mod_cast Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    · exact_mod_cast Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
  change (∑ k ∈ K, ArithmeticFunction.vonMangoldt k) ≤ _
  calc
    _ = ∑ k ∈ T, ArithmeticFunction.vonMangoldt k := by
      symm
      exact Finset.sum_subset (Finset.filter_subset _ _) (fun k hk hout =>
        ArithmeticFunction.vonMangoldt_eq_zero_iff.2 (fun h => hout (Finset.mem_filter.mpr ⟨hk,h⟩)))
    _ = ∑ p ∈ n.primeFactors, ∑ k ∈ T.filter (fun k => k.minFac=p), ArithmeticFunction.vonMangoldt k :=
      (Finset.sum_fiberwise_of_maps_to (fun k hk => (repr hk).1) _).symm
    _ ≤ ∑ p ∈ n.primeFactors, 2*Real.log (p:ℝ) := Finset.sum_le_sum fiber
    _ ≤ _ := by rw [← Finset.mul_sum]; linarith

theorem PEqualNP.Outside.L_goldbach_primitive_induced_discrepancy :
    ∀ (n : ℕ) [NeZero n], 2<n → ∀ (χ : DirichletCharacter ℂ n) (v : ℕ → ℂ), (∀ k, ‖v k‖≤1) → ‖∑ k ∈ (Finset.range (n+1)).filter (fun k => n≤3*k ∧ 3*k≤2*n), (ArithmeticFunction.vonMangoldt k:ℂ)*v k*(χ (k:ZMod n)-χ.primitiveCharacter (k:ZMod χ.conductor))‖ ≤ 2*Real.log (n:ℝ) := by
  intro n _ hn χ v hv
  let T := (Finset.range (n+1)).filter (fun k => n≤3*k ∧ 3*k≤2*n)
  let Λ := ArithmeticFunction.vonMangoldt
  have estimate (k : ℕ) :
      ‖(Λ k : ℂ)*v k*(χ (k:ZMod n)-χ.primitiveCharacter (k:ZMod χ.conductor))‖ ≤
        if ¬ k.Coprime n then Λ k else 0 := by
    by_cases hc : k.Coprime n
    · have heq : χ.primitiveCharacter (k:ZMod χ.conductor) = χ (k:ZMod n) := by
        simpa using χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr hc)
      simp [heq, hc]
    · have heq : χ (k:ZMod n) = 0 := by
        simpa using (χ.apply_eq_zero_iff (k:ℤ)).2 (fun h => hc (Nat.isCoprime_iff_coprime.mp h))
      have hΛ : 0 ≤ Λ k := ArithmeticFunction.vonMangoldt_nonneg
      rw [ite_eq_left hc, heq, zero_sub, norm_mul, norm_mul, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg hΛ]
      calc
        _ ≤ (Λ k * 1) * 1 := by
          gcongr
          · exact hv k
          · exact χ.primitiveCharacter.norm_le_one _
        _ = _ := by ring
  have same : T.filter (fun k => ¬k.Coprime n) =
      (Finset.range (n+1)).filter (fun k => n ≤ 3*k ∧ 3*k ≤ 2*n ∧ ¬k.Coprime n) := by
    ext k
    simp only [T, Finset.mem_filter]
    tauto
  refine (norm_sum_le T _).trans ((Finset.sum_le_sum (fun k _ => estimate k)).trans ?_)
  rw [← Finset.sum_filter, same]
  exact totalRamified n (by omega)
