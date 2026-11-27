import Mathlib

open scoped Classical

private theorem oddCount :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); 2*odd.card=n.totient := by
  intro n _ hn odd
  have hz := DirichletCharacter.sum_characters_eq_zero ℂ
    (show (-1 : ZMod n) ≠ 1 from fun h => by rcases ZMod.neg_one_eq_one_iff.mp h with h | h <;> omega)
  have hm (χ : DirichletCharacter ℂ n) :
      χ (-1) = 1 - (if χ (-1) = -1 then (2 : ℂ) else 0) := by
    rcases χ.even_or_odd with h | h
    · rw [show χ (-1) = 1 from h]
      norm_num
    · rw [show χ (-1) = -1 from h]
      norm_num
  rw [Finset.sum_congr rfl (fun χ _ => hm χ)] at hz
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter] at hz
  have hc := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ n
  rw [Nat.card_eq_fintype_card] at hc
  simp [odd, hc] at hz ⊢
  exact_mod_cast (by linear_combination -hz :
    (2 : ℂ) * ((Finset.univ.filter (fun χ : DirichletCharacter ℂ n => χ (-1) = -1)).card : ℂ) = n.totient)


private theorem countSmall :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); ∀ d : ℕ, d∣n → 2<d → 2*(odd.filter (fun χ => χ.conductor ∣ d)).card = d.totient := by
  intro n _ hn odd d hd htd
  letI : NeZero d := ⟨by omega⟩
  let X := (Finset.univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ (-1) = -1)
  let l := DirichletCharacter.changeLevel (R := ℂ) hd
  have hs (χ : DirichletCharacter ℂ d) : l χ (-1) = χ (-1) := by
    simpa only [Int.cast_neg,Int.cast_one] using
      χ.changeLevel_eq_cast_of_dvd' hd (a := (-1 : ℤ))
        (show IsCoprime (-1 : ℤ) n from ⟨-1,0,by ring⟩)
  have hX : odd.filter (fun χ => χ.conductor ∣ d) = X.image l := by
    ext χ
    simp only [X, odd, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨ho,hc⟩
      obtain ⟨_,ψ,hψ⟩ := (χ.mem_conductorSet_iff_conductor_dvd hd).mpr hc
      exact ⟨ψ, (hs ψ).symm.trans (hψ ▸ ho), hψ.symm⟩
    · rintro ⟨ψ,ho,rfl⟩
      exact ⟨(hs ψ).trans ho, (DirichletCharacter.conductor_changeLevel ψ hd) ▸ ψ.conductor_dvd_level⟩
  rw [hX,Finset.card_image_of_injective X (DirichletCharacter.changeLevel_injective hd)]
  exact oddCount d htd


private theorem countTiny :
    ∀ (n : ℕ) [NeZero n], 2<n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); ∀ d:ℕ, d∣n → d≤2 → (odd.filter (fun χ => χ.conductor ∣ d)).card=0 := by
  intro n _ hn odd d hd hsmall
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro χ hχ
  obtain ⟨ho, hc⟩ := Finset.mem_filter.mp hχ
  have hsign := (Finset.mem_filter.mp ho).2
  have hprim := χ.primitiveCharacter_apply_of_isCoprime (a := (-1 : ℤ)) (show IsCoprime (-1 : ℤ) n from ⟨-1, 0, by ring⟩)
  have hprim' : χ.primitiveCharacter (-1) = -1 := by simpa using hprim.trans (by simpa using hsign)
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (NeZero.pos n)
  have hcp : 0 < χ.conductor := Nat.pos_of_dvd_of_pos χ.conductor_dvd_level (NeZero.pos n)
  have hle := Nat.le_of_dvd hdpos hc
  have heq : (-1 : ZMod χ.conductor) = 1 := ZMod.neg_one_eq_one_iff.mpr (by omega)
  rw [heq, map_one] at hprim'
  norm_num at hprim'


private theorem deficitLayer :
    ∀ (n : ℕ) [NeZero n], 2<n → ∀ χ : DirichletCharacter ℂ n, Real.log ((n:ℝ)/(χ.conductor:ℝ)) = ∑ p ∈ n.primeFactors, (Real.log (p:ℝ)) * (((Finset.Icc 1 (n.factorization p)).filter (fun j => χ.conductor ∣ n/p^j)).card : ℝ) := by
  intro n _ hn χ
  let c := χ.conductor
  let m := n / c
  have hc : c ∣ n := χ.conductor_dvd_level
  have hn0 := NeZero.ne n
  have hc0 : 0 < c := Nat.pos_of_dvd_of_pos hc (NeZero.pos n)
  have hm0 : 0 < m := Nat.div_pos (Nat.le_of_dvd (NeZero.pos n) hc) hc0
  have hmn : m ∣ n := Nat.div_dvd_of_dvd hc
  have card (p : ℕ) (hp : p ∈ n.primeFactors) :
      ((Finset.Icc 1 (n.factorization p)).filter (fun j => c ∣ n/p^j)).card = m.factorization p := by
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hle := (Nat.factorization_le_iff_dvd hm0.ne' hn0).mpr hmn p
    have hset : (Finset.Icc 1 (n.factorization p)).filter (fun j => c ∣ n/p^j) =
        Finset.Icc 1 (m.factorization p) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_Icc]
      by_cases hj : j ≤ n.factorization p
      · have hjd := (hp'.pow_dvd_iff_le_factorization hn0).mpr hj
        rw [Nat.dvd_div_iff_mul_dvd hjd, mul_comm (p^j) c, ← Nat.dvd_div_iff_mul_dvd hc]
        change (1 ≤ j ∧ j ≤ n.factorization p) ∧ p^j ∣ m ↔ _
        rw [hp'.pow_dvd_iff_le_factorization hm0.ne']; tauto
      · omega
    rw [hset,Nat.card_Icc]; omega
  have prod : m = ∏ p ∈ n.primeFactors, p ^ m.factorization p := by
    calc
      m = ∏ p ∈ m.primeFactors, p^m.factorization p := Nat.prod_primeFactors_pow_factorization hm0.ne'
      _ = _ := by
        apply Finset.prod_subset (Nat.primeFactors_mono hmn hn0)
        intro p hp hnmem
        have hzero : m.factorization p = 0 := by
          apply Finsupp.notMem_support_iff.mp
          simpa using hnmem
        rw [hzero,pow_zero]
  have realProd : (m:ℝ) = ∏ p ∈ n.primeFactors, (p:ℝ)^m.factorization p := by exact_mod_cast prod
  have ratio : (n:ℝ)/c = m := (Nat.cast_div hc (by exact_mod_cast hc0.ne' : (c:ℝ) ≠ 0)).symm
  change Real.log ((n:ℝ)/c) = _
  rw [ratio,realProd,Real.log_prod (fun p hp => pow_ne_zero _ (by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Real.log_pow,← card p hp]
  exact mul_comm _ _


theorem PEqualNP.Outside.L_goldbach_conductor_mean_exact :
    ∀ (n : ℕ) [NeZero n], 2<n → Even n → let odd := (Finset.univ : Finset (DirichletCharacter ℂ n)).filter (fun χ => χ (-1) = -1); (2/(n.totient:ℝ))*(∑ χ ∈ odd, Real.log ((n:ℝ)/(χ.conductor:ℝ))) = ∑ p ∈ n.primeFactors, Real.log (p:ℝ) * ∑ j ∈ Finset.Icc 1 (n.factorization p), (if 2<n/p^j then ((n/p^j).totient:ℝ)/(n.totient:ℝ) else 0) := by
  intro n _ hn _ odd
  have layer (p : ℕ) :
      (∑ χ ∈ odd, (((Finset.Icc 1 (n.factorization p)).filter (fun j => χ.conductor ∣ n/p^j)).card : ℝ)) =
      ∑ j ∈ Finset.Icc 1 (n.factorization p), ((odd.filter (fun χ => χ.conductor ∣ n/p^j)).card : ℝ) := by
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun χ _ => deficitLayer n hn χ), Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [←Finset.mul_sum,layer,mul_left_comm,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hpow := ((Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization (NeZero.ne n)).mpr
     (Finset.mem_Icc.mp hj).2
  have hd : n / p ^ j ∣ n := Nat.div_dvd_of_dvd hpow
  split_ifs with h
  · have hcard := countSmall n hn (n/p^j) hd h
    change 2 * (odd.filter _).card = _ at hcard
    have hreal : (2:ℝ) * ((odd.filter (fun χ => χ.conductor ∣ n/p^j)).card:ℝ) = ((n/p^j).totient:ℝ) := by exact_mod_cast hcard
    rw [div_mul_eq_mul_div₀,hreal]
  · have hcard := countTiny n hn (n/p^j) hd (le_of_not_gt h)
    change (odd.filter _).card = 0 at hcard
    simp [hcard]
