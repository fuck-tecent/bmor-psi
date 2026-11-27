import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_fixed_nonunit_mangoldt :
    ∀ q n : ℕ, 1 ≤ q → 1 ≤ n → (∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q), ArithmeticFunction.vonMangoldt k) ≤ (q.primeFactors.card:ℝ)*Real.log n := by
  intro q n hq hn
  let K := (Finset.range (n+1)).filter (fun k => ¬k.Coprime q)
  let T := K.filter IsPrimePow
  let E (p : ℕ) := (Finset.Icc 1 (Nat.log p n))
  have repr {k : ℕ} (hk : k ∈ T) :
      k.minFac ∈ q.primeFactors ∧ ∃ a ∈ E k.minFac, k.minFac^a = k := by
    obtain ⟨hkK,hpp⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkN,hbad⟩ := Finset.mem_filter.mp hkK
    obtain ⟨p,a,hp,ha,rfl⟩ := (isPrimePow_nat_iff k).1 hpp
    rw [Nat.pow_minFac ha.ne',hp.minFac_eq]
    have hd : p ∣ q := by
      by_contra h
      exact hbad ((hp.coprime_iff_not_dvd.2 h).pow_left a)
    refine ⟨Nat.mem_primeFactors.mpr ⟨hp,hd,by omega⟩,a,Finset.mem_Icc.mpr ⟨ha,?_⟩,rfl⟩
    exact Nat.le_log_of_pow_le hp.one_lt (by have := Finset.mem_range.mp hkN; omega)
  have fiber (p : ℕ) (hp : p ∈ q.primeFactors) :
      (∑ k ∈ T.filter (fun k => k.minFac=p), ArithmeticFunction.vonMangoldt k) ≤ Real.log n := by
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hsub : T.filter (fun k => k.minFac=p) ⊆ (E p).image (fun a => p^a) := by
      intro k hk
      obtain ⟨hkT,hbase⟩ := Finset.mem_filter.mp hk
      have hrep := (repr hkT).2
      rw [hbase] at hrep
      exact Finset.mem_image.mpr hrep
    have hc : (T.filter (fun k => k.minFac=p)).card ≤ Nat.log p n := by
      have := (Finset.card_le_card hsub).trans Finset.card_image_le
      simpa [E,Nat.card_Icc] using this
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpprime.one_le)
    calc
      _ = ∑ _k ∈ T.filter (fun k => k.minFac=p), Real.log (p:ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        obtain ⟨hkT,hbase⟩ := Finset.mem_filter.mp hk
        rw [ArithmeticFunction.vonMangoldt_apply,ite_eq_left (Finset.mem_filter.mp hkT).2,hbase]
      _ ≤ (Nat.log p n:ℝ)*Real.log p := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hlog
      _ = Real.log ((p:ℝ)^(Nat.log p n)) := (Real.log_pow _ _).symm
      _ ≤ Real.log n := Real.log_le_log (by exact_mod_cast pow_pos hpprime.pos _)
        (by exact_mod_cast Nat.pow_log_le_self p (by omega))
  change (∑ k ∈ K, ArithmeticFunction.vonMangoldt k) ≤ _
  calc
    _ = ∑ k ∈ T, ArithmeticFunction.vonMangoldt k := by
      symm
      exact Finset.sum_subset (Finset.filter_subset _ _) (fun k hk hout =>
        ArithmeticFunction.vonMangoldt_eq_zero_iff.2 (fun h => hout (Finset.mem_filter.mpr ⟨hk,h⟩)))
    _ = ∑ p ∈ q.primeFactors, ∑ k ∈ T.filter (fun k => k.minFac=p), ArithmeticFunction.vonMangoldt k :=
      (Finset.sum_fiberwise_of_maps_to (fun k hk => (repr hk).1) _).symm
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log n := Finset.sum_le_sum fiber
    _ = _ := by simp
