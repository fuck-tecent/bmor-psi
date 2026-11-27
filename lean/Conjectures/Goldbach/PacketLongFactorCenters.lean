import Mathlib

open scoped BigOperators

namespace PLFCAux

private noncomputable def ph (q a k : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((k : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ) : ℂ) * Complex.I)

private lemma ph_unit (q a k : ℕ) : ‖ph q a k‖ = 1 := by
  unfold ph
  exact Complex.norm_exp_ofReal_mul_I _

private theorem orth (q u v : ℕ) (hq : 0 < q) :
    (∑ a ∈ Finset.range q, ph q a u * (starRingEnd ℂ) (ph q a v)) =
      if u % q = v % q then (q : ℂ) else 0 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)
  have hζ : IsPrimitiveRoot ζ q := Complex.isPrimitiveRoot_exp q hq.ne'
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have phase (a k : ℕ) : ph q a k = (ζ ^ k) ^ a := by
    unfold ph
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have term (a : ℕ) : ph q a u * (starRingEnd ℂ) (ph q a v) =
      (ζ ^ u / ζ ^ v) ^ a := by
    rw [← Complex.inv_eq_conj (ph_unit q a v), phase, phase, div_pow, div_eq_mul_inv]
  simp_rw [term]
  have hpowiff (x y : ℕ) : ζ ^ x = ζ ^ y ↔ x % q = y % q := by
    have hfin := hζ.isOfFinOrder hq.ne'
    rw [hfin.pow_inj_mod, hζ.eq_orderOf]
  by_cases huv : u % q = v % q
  · have hbase : ζ ^ u / ζ ^ v = 1 :=
      (div_eq_one_iff_eq (pow_ne_zero v hζ0)).2 ((hpowiff u v).2 huv)
    rw [if_pos huv, hbase]
    simp
  · rw [if_neg huv, geom_sum_eq]
    · have hpow (x : ℕ) : (ζ ^ x) ^ q = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
      simp [div_pow, hpow]
    · intro hbase
      apply huv
      apply (hpowiff u v).1
      exact (div_eq_one_iff_eq (pow_ne_zero v hζ0)).1 hbase

private theorem second_moment (q m : ℕ) (k : ℕ → ℕ) (hq : 0 < q) :
    (∑ a ∈ Finset.range q, ‖∑ j ∈ Finset.range m, ph q a (k j)‖ ^ 2) =
      (q : ℝ) * ((((Finset.range m ×ˢ Finset.range m).filter
        (fun ij => k ij.1 % q = k ij.2 % q)).card : ℝ)) := by
  have expand (a : ℕ) :
      (∑ j ∈ Finset.range m, ph q a (k j)) *
          (starRingEnd ℂ) (∑ j ∈ Finset.range m, ph q a (k j)) =
        ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m,
          ph q a (k j) * (starRingEnd ℂ) (ph q a (k l)) := by
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', expand]
  have hswap :
      (∑ a ∈ Finset.range q, ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m,
        ph q a (k j) * (starRingEnd ℂ) (ph q a (k l))) =
      ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, ∑ a ∈ Finset.range q,
        ph q a (k j) * (starRingEnd ℂ) (ph q a (k l)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  rw [hswap]
  rw [Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun l _ => orth q (k j) (k l) hq))]
  rw [← Finset.sum_product']
  calc
    (∑ ij ∈ Finset.range m ×ˢ Finset.range m,
        if k ij.1 % q = k ij.2 % q then (q : ℂ) else 0) =
        (q : ℂ) * ∑ ij ∈ Finset.range m ×ˢ Finset.range m,
          if k ij.1 % q = k ij.2 % q then (1 : ℂ) else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ij _
            split_ifs <;> ring
    _ = (q : ℂ) * ((((Finset.range m ×ˢ Finset.range m).filter
        (fun ij => k ij.1 % q = k ij.2 % q)).card : ℂ)) := by
      rw [Finset.sum_boole]


private lemma block_card (q d H m i : ℕ) (hodd : Odd d) (hdq : d ∣ q)
    (hH : ∀ h : ℕ, 1 ≤ h → h ≤ H → ¬ d ∣ 2 ^ h - 1) :
    ((Finset.range m).filter (fun j => (2:ℕ)^(i+1) % q = (2:ℕ)^(j+1) % q)).card ≤ (m-1)/(H+1) + 1 := by
  have key : ∀ j j' : ℕ, j < j' → (2:ℕ)^(j+1) % q = (2:ℕ)^(j'+1) % q → H + 1 ≤ j' - j := by
    intro j j' hjj h
    by_contra hlt
    push_neg at hlt
    have h1 : (2:ℕ)^(j+1) ≡ (2:ℕ)^(j'+1) [MOD q] := h
    have h2 : (2:ℕ)^(j+1) ≡ (2:ℕ)^(j'+1) [MOD d] := h1.of_dvd hdq
    have hle : (2:ℕ)^(j+1) ≤ (2:ℕ)^(j'+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 := (Nat.modEq_iff_dvd' hle).1 h2
    have h4 : (2:ℕ)^(j'+1) - (2:ℕ)^(j+1) = 2^(j+1) * (2^(j'-j) - 1) := by
      have : (2:ℕ)^(j'+1) = 2^(j+1) * 2^(j'-j) := by
        rw [← pow_add]; congr 1; omega
      rw [this, Nat.mul_sub, mul_one]
    rw [h4] at h3
    have hcop : Nat.Coprime d (2^(j+1)) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd) 
    have h5 : d ∣ 2^(j'-j) - 1 := hcop.dvd_of_dvd_mul_left h3
    exact hH (j'-j) (by omega) (by omega) h5
  have hmap : Set.MapsTo (fun j => j / (H+1))
      ((Finset.range m).filter (fun j => (2:ℕ)^(i+1) % q = (2:ℕ)^(j+1) % q) : Finset ℕ)
      (Finset.range ((m-1)/(H+1) + 1) : Finset ℕ) := by
    intro j hj
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hj
    simp only [Finset.coe_range, Set.mem_Iio]
    have : j / (H+1) ≤ (m-1)/(H+1) := Nat.div_le_div_right (by omega)
    omega
  have hinj : Set.InjOn (fun j => j / (H+1))
      ((Finset.range m).filter (fun j => (2:ℕ)^(i+1) % q = (2:ℕ)^(j+1) % q) : Finset ℕ) := by
    intro j hj j' hj' hjj
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hj hj'
    simp only at hjj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := key j j' hlt (hj.2.symm.trans hj'.2)
      have h1 := Nat.div_mul_le_self j (H+1)
      have h2 := Nat.lt_div_mul_add (a := j) (b := H+1) (by omega)
      have h3 := Nat.div_mul_le_self j' (H+1)
      have h4 := Nat.lt_div_mul_add (a := j') (b := H+1) (by omega)
      rw [hjj] at h1 h2
      omega
    · have := key j' j hlt (hj'.2.symm.trans hj.2)
      have h1 := Nat.div_mul_le_self j (H+1)
      have h2 := Nat.lt_div_mul_add (a := j) (b := H+1) (by omega)
      have h3 := Nat.div_mul_le_self j' (H+1)
      have h4 := Nat.lt_div_mul_add (a := j') (b := H+1) (by omega)
      rw [hjj] at h1 h2
      omega
  have := Finset.card_le_card_of_injOn _ hmap hinj
  simpa using this

end PLFCAux

open PLFCAux in
theorem Conjectures.Goldbach.PacketLongFactorCenters :
    ∀ (q d H m : ℕ) (u : ℝ), 1 < q → 0 < m → 0 < u → Odd d → d ∣ q → (∀ h : ℕ, 1 ≤ h → h ≤ H → ¬ d ∣ 2 ^ h - 1) → let K := fun t : ℝ => (∑ j ∈ Finset.range m, Real.cos (2 * Real.pi * (2 : ℝ)^(j+1) * t)) / (m : ℝ); (m : ℝ) * u^2 * (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ u < K ((a:ℝ)/(q:ℝ)))).card : ℝ) ≤ (q : ℝ) * (((m-1)/(H+1) + 1 : ℕ) : ℝ) := by
  intro q d H m u hq hm hu hodd hdq hH K
  have hq0 : 0 < q := by omega
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  set R := (Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ u < K ((a:ℝ)/(q:ℝ))) with hR
  have hsub : R ⊆ Finset.range q := by
    intro a ha
    simp only [hR, Finset.mem_filter, Finset.mem_range] at ha ⊢
    by_contra hc
    have haq : a = q := by omega
    rw [haq, Nat.coprime_self] at ha
    omega
  have hre : ∀ a : ℕ, (∑ j ∈ Finset.range m, ph q a (2^(j+1))).re = (m:ℝ) * K ((a:ℝ)/(q:ℝ)) := by
    intro a
    simp only [K]
    rw [mul_div_cancel₀ _ hmR.ne', Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold ph
    rw [Complex.exp_ofReal_mul_I_re]
    congr 1
    push_cast
    ring
  have hterm : ∀ a ∈ R, ((m:ℝ) * u)^2 ≤ ‖∑ j ∈ Finset.range m, ph q a (2^(j+1))‖^2 := by
    intro a ha
    simp only [hR, Finset.mem_filter] at ha
    have h1 : (m:ℝ) * u ≤ (∑ j ∈ Finset.range m, ph q a (2^(j+1))).re := by
      rw [hre]; exact mul_le_mul_of_nonneg_left ha.2.2.le hmR.le
    have h2 := Complex.re_le_norm (∑ j ∈ Finset.range m, ph q a (2^(j+1)))
    have h0 : 0 ≤ (m:ℝ) * u := by positivity
    exact pow_le_pow_left₀ h0 (h1.trans h2) 2
  have hsum : (R.card : ℝ) * ((m:ℝ) * u)^2 ≤ ∑ a ∈ Finset.range q, ‖∑ j ∈ Finset.range m, ph q a (2^(j+1))‖^2 := by
    calc (R.card : ℝ) * ((m:ℝ) * u)^2 = ∑ a ∈ R, ((m:ℝ) * u)^2 := by simp
      _ ≤ ∑ a ∈ R, ‖∑ j ∈ Finset.range m, ph q a (2^(j+1))‖^2 := Finset.sum_le_sum hterm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  rw [second_moment q m (fun j => 2^(j+1)) hq0] at hsum
  have hN : ((((Finset.range m ×ˢ Finset.range m).filter
        (fun ij => 2^(ij.1+1) % q = 2^(ij.2+1) % q)).card : ℕ) : ℝ) ≤ (m:ℝ) * (((m-1)/(H+1) + 1 : ℕ) : ℝ) := by
    have : ((Finset.range m ×ˢ Finset.range m).filter
        (fun ij => 2^(ij.1+1) % q = 2^(ij.2+1) % q)).card ≤ m * ((m-1)/(H+1) + 1) := by
      rw [Finset.card_filter, Finset.sum_product]
      calc _ ≤ ∑ _i ∈ Finset.range m, ((m-1)/(H+1) + 1) := by
            apply Finset.sum_le_sum
            intro i _
            rw [← Finset.card_filter]
            exact block_card q d H m i hodd hdq hH
        _ = _ := by simp
    exact_mod_cast this
  have hqR : (0:ℝ) < q := by exact_mod_cast hq0
  have h3 : (R.card : ℝ) * ((m:ℝ) * u)^2 ≤ (q:ℝ) * ((m:ℝ) * (((m-1)/(H+1) + 1 : ℕ) : ℝ)) :=
    hsum.trans (mul_le_mul_of_nonneg_left hN hqR.le)
  have h4 : (m:ℝ) * ((m : ℝ) * u^2 * R.card) ≤ (m:ℝ) * ((q : ℝ) * (((m-1)/(H+1) + 1 : ℕ) : ℝ)) := by
    nlinarith [h3]
  exact le_of_mul_le_mul_left h4 hmR
