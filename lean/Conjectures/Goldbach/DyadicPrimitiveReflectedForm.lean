import Mathlib


private theorem kernelCriterion :
∀ (k : ℕ) (χ : DirichletCharacter ℂ (2^(k+1))), 1 ≤ k →
  (χ.IsPrimitive ↔ χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) = -1) := by
  intro k χ hk
  haveI : NeZero (2^(k+1)) := ⟨by positivity⟩
  have hd : 2^k ∣ 2^(k+1) := pow_dvd_pow 2 (Nat.le_succ k)
  have hlt : 1 < 2^k := by
    calc (1:ℕ) < 2^1 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have hodd : Odd (1 + 2^k) := by
    rw [add_comm, Nat.odd_add_one, Nat.not_odd_iff_even]
    exact ⟨2^(k-1), by rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hk]⟩
  have hcop : Nat.Coprime (1 + 2^k) (2^(k+1)) :=
    Nat.Coprime.pow_right (k+1) hodd.coprime_two_right
  have hker : ∀ x : (ZMod (2^(k+1)))ˣ, ZMod.unitsMap hd x = 1 →
      (x : ZMod (2^(k+1))) = 1 ∨
        (x : ZMod (2^(k+1))) = ((1 + 2^k : ℕ) : ZMod (2^(k+1))) := by
    intro x hx
    have hcast : (((x : ZMod (2^(k+1))).cast : ZMod (2^k))) = 1 := by
      have h := congrArg (fun y : (ZMod (2^k))ˣ => (y : ZMod (2^k))) hx
      simpa [ZMod.unitsMap_val] using h
    set a : ℕ := (x : ZMod (2^(k+1))).val with ha
    have haval : (a : ZMod (2^(k+1))) = (x : ZMod (2^(k+1))) := by
      rw [ha]
      exact ZMod.natCast_zmod_val _
    have hamod : a % 2^k = 1 := by
      have h1 : (a : ZMod (2^k)) = 1 := by
        rw [← ZMod.cast_natCast hd a, haval]
        exact hcast
      have h2 : a ≡ 1 [MOD 2^k] := (ZMod.natCast_eq_natCast_iff a 1 (2^k)).mp (by simpa using h1)
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hlt] using h2
    have haeq : a = 2^k * (a / 2^k) + 1 := by
      have h := Nat.div_add_mod a (2^k)
      rw [hamod] at h
      omega
    have hq : a / 2^k < 2 := by
      have halt : a < 2^k * 2 := by
        have h := ZMod.val_lt (x : ZMod (2^(k+1)))
        rw [← ha, pow_succ] at h
        exact h
      have h1 : 2^k * (a / 2^k) < 2^k * 2 := by omega
      exact Nat.lt_of_mul_lt_mul_left h1
    have hq2 : a / 2^k = 0 ∨ a / 2^k = 1 := by
      rcases Nat.eq_zero_or_pos (a / 2^k) with h0 | hpos
      · exact Or.inl h0
      · exact Or.inr (by omega)
    rcases hq2 with h0 | h1
    · left
      rw [← haval, haeq, h0, mul_zero, zero_add]
      norm_num
    · right
      rw [← haval, haeq, h1, mul_one]
      norm_num [Nat.add_comm]
  have hfac_iff : χ.FactorsThrough (2^k) ↔
      χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) = 1 := by
    have hu : ZMod.unitsMap hd (ZMod.unitOfCoprime (1 + 2^k) hcop) = 1 := by
      refine Units.ext ?_
      rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, Units.val_one, ZMod.cast_natCast hd]
      rw [Nat.cast_add, Nat.cast_one]
      have h : (((2:ℕ)^k : ℕ) : ZMod (2^k)) = 0 := ZMod.natCast_self _
      rw [h]
      ring
    constructor
    · intro hf
      have hker' := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mp hf
      have hmem : χ.toUnitHom (ZMod.unitOfCoprime (1 + 2^k) hcop) = 1 :=
        MonoidHom.mem_ker.mp (hker' (MonoidHom.mem_ker.mpr hu))
      have h := congrArg (fun y : ℂˣ => (y : ℂ)) hmem
      simpa [MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime] using h
    · intro hv
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
      intro x hx
      apply MonoidHom.mem_ker.mpr
      apply Units.ext
      rw [MulChar.coe_toUnitHom, Units.val_one]
      rcases hker x (MonoidHom.mem_ker.mp hx) with h | h
      · rw [h]
        exact MulChar.map_one χ
      · rw [h, hv]
  constructor
  ·
    intro hprim
    have hne : ¬ χ.FactorsThrough (2^k) := by
      intro hf
      have hmem : 2^k ∈ χ.conductorSet := (DirichletCharacter.mem_conductorSet_iff χ).mpr hf
      have hdvd : χ.conductor ∣ 2^k :=
        (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hd).mp hmem
      rw [(DirichletCharacter.isPrimitive_def χ).mp hprim] at hdvd
      have hle : k + 1 ≤ k := (Nat.pow_dvd_pow_iff_le_right (x := 2) (by norm_num)).mp hdvd
      omega
    have hne1 : χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) ≠ 1 := fun h => hne (hfac_iff.mpr h)
    have hsq : χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) ^ 2 = 1 := by
      have hkey : (((1 + 2^k : ℕ) : ZMod (2^(k+1))) ^ 2) = 1 := by
        have hnat : (1 + 2^k : ℕ) ^ 2 = 1 + 2^(k+1) * (1 + 2^(k-1)) := by
          have hm : 2 * 2^(k-1) = 2^k := by rw [← pow_succ', Nat.sub_add_cancel hk]
          have hA : 2^(k+1) = 2 * 2^k := pow_succ' 2 k
          nlinarith
        calc (((1 + 2^k : ℕ) : ZMod (2^(k+1))) ^ 2)
            = (((1 + 2^k : ℕ) ^ 2 : ℕ) : ZMod (2^(k+1))) := (Nat.cast_pow _ _).symm
          _ = ((1 + 2^(k+1) * (1 + 2^(k-1)) : ℕ) : ZMod (2^(k+1))) := by rw [hnat]
          _ = 1 := by
            rw [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
            have h : (((2:ℕ)^(k+1) : ℕ) : ZMod (2^(k+1))) = 0 := ZMod.natCast_self _
            rw [h]
            ring
      calc χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) ^ 2
          = χ (((1 + 2^k : ℕ) : ZMod (2^(k+1))) ^ 2) := (map_pow χ _ 2).symm
        _ = χ 1 := by rw [hkey]
        _ = 1 := MulChar.map_one χ
    rcases (sq_eq_one_iff.mp hsq) with h | h
    · exact absurd h hne1
    · exact h
  ·
    intro hv
    rw [DirichletCharacter.isPrimitive_def]
    have hnot : ¬ χ.FactorsThrough (2^k) := by
      intro hf
      have h1 : χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) = 1 := hfac_iff.mp hf
      rw [hv] at h1
      norm_num at h1
    have hdvd : χ.conductor ∣ 2^(k+1) := DirichletCharacter.conductor_dvd_level χ
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hdvd
    rw [hjeq]
    by_cases hjk : j = k + 1
    · rw [hjk]
    · exfalso
      have hjk' : j ≤ k := by omega
      have hdvd' : χ.conductor ∣ 2^k := by
        rw [hjeq]
        exact (Nat.pow_dvd_pow_iff_le_right (x := 2) (by norm_num)).mpr hjk'
      exact hnot ((DirichletCharacter.mem_conductorSet_iff χ).mp
        ((DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hd).mpr hdvd'))


private theorem extendUnits {m : ℕ} [NeZero m] {β : Type*} [AddCommMonoid β]
    (f : ZMod m → β) (h : ∀ x, ¬IsUnit x → f x = 0) :
    (∑ x : (ZMod m)ˣ, f (x:ZMod m)) = ∑ x, f x :=
  Fintype.sum_of_injective _ Units.val_injective _ _ (fun i hi => h i (fun ⟨u,hu⟩ => hi ⟨u,hu⟩)) (fun _ => rfl)



private theorem kernelSum (m : ℕ) [NeZero m] (a b : ZMod m) :
    (∑ χ : DirichletCharacter ℂ m, star (χ a) * χ b) =
      if IsUnit a ∧ a=b then (m.totient : ℂ) else 0 := by
  classical
  by_cases ha : IsUnit a
  · have h (χ : DirichletCharacter ℂ m) : star (χ a) = χ a⁻¹ := by
      obtain ⟨u,rfl⟩ := ha
      rw [MulChar.star_apply',MulChar.inv_apply,ZMod.inv_coe_unit,Ring.inverse_unit]
    simp_rw [h]
    simpa [ha] using DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha b
  · simp [MulChar.map_nonunit _ ha,ha]

private theorem unitRange {m : ℕ} [NeZero m] (w : ZMod m → ℂ) (hw : ∀ x, ¬IsUnit x → w x = 0) :
    (∑ x : (ZMod m)ˣ, w x) = ∑ j ∈ Finset.range m, w (j:ZMod m) := by
  rw [extendUnits w hw, ← Fin.sum_univ_eq_sum_range]
  let e : Fin m ≃ ZMod m := {
    toFun := fun x => (x.val : ZMod m)
    invFun := fun x => ⟨x.val,ZMod.val_lt x⟩
    left_inv := fun x => Fin.ext (ZMod.val_natCast_of_lt x.isLt)
    right_inv := fun x => ZMod.natCast_zmod_val x }
  exact (e.sum_comp w).symm

set_option maxHeartbeats 2000000 in
theorem Conjectures.Goldbach.DyadicPrimitiveReflectedForm :
    ∀ (N k : ℕ), Even N → 1 ≤ k →
      let q : ℕ := 2^k
      let m : ℕ := 2^(k+1)
      ∀ f : ZMod m → ℝ,
        let D := fun r : ℕ => f (r : ZMod m) - f ((r+q : ℕ) : ZMod m)
        let s := (Finset.univ : Finset (DirichletCharacter ℂ m)).filter (fun χ => χ.conductor = m)
        let v := fun χ : DirichletCharacter ℂ m =>
          (∑ x : (ZMod m)ˣ, (f (x : ZMod m) : ℂ) * star (χ (x : ZMod m))) /
            (Real.sqrt (m.totient : ℝ) : ℂ)
        let H := fun χ ψ : DirichletCharacter ℂ m =>
          (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m))) / (m.totient : ℂ)
        (∑ r ∈ (Finset.range q).filter (fun r => Odd r),
          (if (N+2*q-r) % (2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r) % q)) =
          2 * (∑ χ ∈ s, ∑ ψ ∈ s, star (v χ) * H χ ψ * v ψ).re := by
  classical
  intro N k hN hk q m f D C v H
  have hm : m = q+q := by dsimp [m,q]; rw [pow_succ]; omega
  haveI : NeZero m := ⟨by dsimp [m]; positivity⟩
  let T : ZMod m := ((1+q : ℕ):ZMod m)
  let S := (Finset.range q).filter Odd
  let A := fun (χ : DirichletCharacter ℂ m) (r : ℕ) => if χ ∈ C then star (χ (r:ZMod m)) else 0
  let c : ℝ := (m.totient:ℝ)/2
  have evenq : Even q := by exact even_two.pow_of_ne_zero (by omega : k≠0)
  have unitOdd (r : ℕ) : IsUnit (r:ZMod m) ↔ Odd r := by
    rw [ZMod.isUnit_iff_coprime,Nat.coprime_pow_right_iff (by omega : 0 < k+1),Nat.coprime_two_right]
  have qzero : (q:ZMod m)+(q:ZMod m)=0 := by
    rw [← Nat.cast_add, ← hm, ZMod.natCast_self]
  have shift (r : ℕ) (hr : Odd r) : ((r+q:ℕ):ZMod m) = T * r := by
    obtain ⟨j,hj⟩ := hr
    have er : (r:ZMod m) = 2*(j:ZMod m)+1 := by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] using congrArg (fun x : ℕ => (x:ZMod m)) hj
    dsimp [T]; push_cast; rw [er]; linear_combination -(j:ZMod m)*qzero
  have hsquare : T*T=1 := by
    have term : (q:ZMod m)*(q:ZMod m)=0 := by
      obtain ⟨j,hj⟩ := evenq
      have ej : (q:ZMod m)=(j:ZMod m)+(j:ZMod m) := by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] using congrArg (fun x : ℕ => (x:ZMod m)) hj
      calc _ = (q:ZMod m)*((j:ZMod m)+j) := congrArg _ ej
           _ = _ := by linear_combination (j:ZMod m)*qzero
    dsimp [T]; push_cast; linear_combination term+qzero
  have sign (χ : DirichletCharacter ℂ m) : χ T = if χ ∈ C then -1 else 1 := by
    have prim : χ ∈ C ↔ χ.IsPrimitive := by simp [C, DirichletCharacter.isPrimitive_def]
    by_cases hc : χ ∈ C
    · rw [if_pos hc]; exact (kernelCriterion k χ hk).mp (prim.mp hc)
    · rw [if_neg hc]
      have sqχ : χ T ^ 2=1 := by rw [sq,← map_mul, hsquare, map_one]
      exact (sq_eq_one_iff.mp sqχ).resolve_right (fun h => hc (prim.mpr ((kernelCriterion k χ hk).mpr h)))
  have orth (r : ℕ) (hr : r ∈ S) (j : ℕ) (hj : j ∈ S) :
      (∑ χ, A χ r * star (A χ j)) = if r=j then (c:ℂ) else 0 := by
    obtain ⟨hr',hro⟩ := Finset.mem_filter.mp hr
    obtain ⟨hj',hjo⟩ := Finset.mem_filter.mp hj
    have hrq := Finset.mem_range.mp hr'; have hjq := Finset.mem_range.mp hj'
    have neq : ((r+q:ℕ):ZMod m) ≠ (j:ZMod m) := by
      rw [ne_eq, ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt (by omega : r+q < m),Nat.mod_eq_of_lt (by omega : j < m)]
      omega
    have eqcast : (r:ZMod m)=(j:ZMod m) ↔ r=j := by
      rw [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt (by omega : r < m),Nat.mod_eq_of_lt (by omega : j < m)]
    have twice : 2*(∑ χ, A χ r * star (A χ j)) =
      (∑ χ : DirichletCharacter ℂ m, star (χ (r:ZMod m))*χ (j:ZMod m)) -
      (∑ χ : DirichletCharacter ℂ m, star (χ ((r+q:ℕ):ZMod m))*χ (j:ZMod m)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro χ _
      rw [shift r hro,map_mul, sign]
      by_cases hh : χ ∈ C <;> simp [A,hh] <;> ring
    rw [kernelSum,kernelSum] at twice
    simp only [neq,and_false,if_false,sub_zero,(unitOdd r).mpr hro,true_and,eqcast] at twice
    by_cases eq : r=j <;> simp [eq,c] at twice ⊢ <;> first | exact twice | linear_combination twice / 2
  have freq (χ : DirichletCharacter ℂ m) (hχ : χ ∈ C) :
      (∑ x : (ZMod m)ˣ, (f (x:ZMod m):ℂ) * star (χ (x:ZMod m))) =
      ∑ r ∈ S, A χ r * (D r:ℂ) := by
    let w := fun x : ZMod m => (f x:ℂ)*star (χ x)
    change (∑ x : (ZMod m)ˣ, w x) = _
    rw [unitRange w (fun x hx => by simp [w,MulChar.map_nonunit χ hx])]
    conv_lhs => arg 1; rw [hm]
    rw [Finset.sum_range_add, ← Finset.sum_add_distrib,Finset.sum_filter]
    apply Finset.sum_congr rfl; intro r _
    by_cases hr : Odd r
    · simp only [w,if_pos hr,A,if_pos hχ,D,Complex.ofReal_sub]
      rw [Nat.add_comm q r,shift r hr,map_mul,sign,if_pos hχ]
      simp; ring
    · have hr' : ¬Odd (q+r) := fun h => hr (by obtain ⟨j,hj⟩ := evenq; obtain ⟨u,hu⟩ := h; exact Nat.odd_iff.mpr (by omega))
      simp only [w,if_neg hr,MulChar.map_nonunit χ ((unitOdd r).not.mpr hr),MulChar.map_nonunit χ ((unitOdd (q+r)).not.mpr hr'),star_zero,mul_zero,add_zero]

  let L : ℝ := Real.sqrt (m.totient : ℝ)
  have hφ : 0 < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos m)
  have hL : 0 < L := Real.sqrt_pos.2 hφ
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLs : L^2 = (m.totient : ℝ) := Real.sq_sqrt hφ.le
  let F (x : ZMod m) : ℂ := ∑ χ ∈ C, v χ * χ x
  have hF (r : ℕ) (hr : r ∈ S) : F (r : ZMod m) = ((L / 2 * D r : ℝ) : ℂ) := by
    have hv (χ : DirichletCharacter ℂ m) (hχ : χ ∈ C) :
        v χ = (∑ j ∈ S, A χ j * (D j : ℂ)) / (L : ℂ) := by
      change (∑ x : (ZMod m)ˣ, (f (x : ZMod m) : ℂ) * star (χ (x : ZMod m))) / (L : ℂ) = _
      rw [freq χ hχ]
    have he : F (r : ZMod m) * (L : ℂ) =
        ∑ j ∈ S, (D j : ℂ) * (∑ χ : DirichletCharacter ℂ m, A χ j * star (A χ r)) := by
      dsimp only [F]
      rw [Finset.sum_mul]
      have hterm (χ : DirichletCharacter ℂ m) (hc : χ ∈ C) :
          v χ * χ (r : ZMod m) * (L : ℂ) =
            ∑ j ∈ S, (D j : ℂ) * (A χ j * star (A χ r)) := by
        rw [hv χ hc]
        have hcancel : ((∑ j ∈ S, A χ j * (D j : ℂ)) / (L : ℂ)) * (L : ℂ) =
            ∑ j ∈ S, A χ j * (D j : ℂ) := div_mul_cancel₀ _ hLc
        calc
          _ = (((∑ j ∈ S, A χ j * (D j : ℂ)) / (L : ℂ)) * (L : ℂ)) * χ (r : ZMod m) := by ring
          _ = _ := by
            rw [hcancel, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j hj
            simp only [A, if_pos hc, star_star]
            ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum]
      congr 1
      apply Finset.sum_subset (Finset.subset_univ _)
      intro χ _ hc
      simp [A,hc]
    have hs : (∑ j ∈ S, (D j : ℂ) * (∑ χ : DirichletCharacter ℂ m, A χ j * star (A χ r))) =
        ∑ j ∈ S, (D j : ℂ) * (if j=r then (c:ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [orth j hj r hr]
    rw [hs] at he
    have he' : (∑ j ∈ S, (D j : ℂ) * (if j=r then (c:ℂ) else 0)) = (D r:ℂ)*(c:ℂ) := by
      rw [Finset.sum_eq_single r]
      · simp
      · intro j hj hne
        simp [hne]
      · exact fun h => (h hr).elim
    rw [he'] at he
    apply (mul_right_cancel₀ hLc)
    rw [he]
    have hcL : (c:ℂ) = (L:ℂ)^2/2 := by
      have hh : c = L^2/2 := by dsimp only [c]; rw [hLs]
      exact_mod_cast hh
    rw [hcL]
    push_cast
    ring
  have hFshift (r : ℕ) (hr : Odd r) : F ((r+q : ℕ) : ZMod m) = -F (r : ZMod m) := by
    dsimp only [F]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [shift r hr, map_mul, sign, if_pos hχ]
    ring
  have hFzero (x : ZMod m) (hx : ¬ IsUnit x) : F x = 0 := by
    dsimp only [F]
    apply Finset.sum_eq_zero
    intro χ hχ
    rw [MulChar.map_nonunit χ hx, mul_zero]
  have hform : (∑ χ ∈ C, ∑ ψ ∈ C, star (v χ) * H χ ψ * v ψ) =
      (∑ x : (ZMod m)ˣ, star (F (x : ZMod m)) * F ((N : ZMod m) - (x : ZMod m))) / (m.totient : ℂ) := by
    have hterm (χ ψ : DirichletCharacter ℂ m) :
        star (v χ) * H χ ψ * v ψ =
          (∑ x : (ZMod m)ˣ, star (v χ * χ (x : ZMod m)) *
            (v ψ * ψ ((N : ZMod m) - (x : ZMod m)))) / (m.totient : ℂ) := by
      dsimp only [H]
      calc
        _ = (star (v χ) * (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m))) * v ψ) / (m.totient : ℂ) := by ring
        _ = _ := by
          congr 1
          rw [Finset.mul_sum,Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          rw [star_mul]
          ring
    simp_rw [hterm]
    simp_rw [← Finset.sum_div]
    congr 1
    have hswap : (∑ χ ∈ C, ∑ ψ ∈ C, ∑ x : (ZMod m)ˣ, star (v χ * χ (x : ZMod m)) * (v ψ * ψ ((N : ZMod m) - (x : ZMod m)))) =
        ∑ χ ∈ C, ∑ x : (ZMod m)ˣ, ∑ ψ ∈ C, star (v χ * χ (x : ZMod m)) * (v ψ * ψ ((N : ZMod m) - (x : ZMod m))) := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [Finset.sum_comm]
    rw [hswap, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    dsimp only [F]
    rw [star_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [Finset.mul_sum]
  let R (r : ℕ) : ℕ := (N+q-r) % q
  let U (r : ℕ) : ℕ := (N+2*q-r) % (2*q)
  let σ (r : ℕ) : ℝ := if U r < q then 1 else -1
  have hq : 0 < q := by positivity
  have h2q : 0 < 2*q := by omega
  have hR (r : ℕ) : R r < q := Nat.mod_lt _ hq
  have hU (r : ℕ) : U r < 2*q := Nat.mod_lt _ h2q
  have hUR (r : ℕ) (hr : r < q) : U r % q = R r := by
    dsimp only [U,R]
    rw [Nat.mod_mod_of_dvd _ (show q ∣ 2*q from ⟨2, by ring⟩)]
    rw [show N+2*q-r = (N+q-r)+q by omega, Nat.add_mod]
    simp
  have hRo (r : ℕ) (hr : r ∈ S) : R r ∈ S := by
    obtain ⟨hrlt,hro⟩ := Finset.mem_filter.mp hr
    have hrq := Finset.mem_range.mp hrlt
    have hh := Nat.mod_mod_of_dvd (N+q-r) (even_iff_two_dvd.mp evenq)
    have hN2 := Nat.even_iff.mp hN
    have hq2 := Nat.even_iff.mp evenq
    have hr2 := Nat.odd_iff.mp hro
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hR r), Nat.odd_iff.mpr (by dsimp only [R]; omega)⟩
  have hcastR (r : ℕ) (hr : r < q) :
      (U r : ZMod m) = (N : ZMod m) - (r : ZMod m) := by
    dsimp only [U]
    rw [show 2*q = m by omega, ZMod.natCast_mod, Nat.cast_sub (by omega)]
    have hm0 : (m : ZMod m) = 0 := ZMod.natCast_self _
    rw [Nat.cast_add,hm0,add_zero]
  have hsignF (r : ℕ) (hr : r ∈ S) :
      F ((N : ZMod m) - (r : ZMod m)) = (σ r : ℂ) * F (R r : ZMod m) := by
    have hrq := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    rw [← hcastR r hrq]
    by_cases hu : U r < q
    · have he : U r = R r := by simpa only [Nat.mod_eq_of_lt hu] using hUR r hrq
      rw [he]
      simp [σ,hu]
    · have he : U r = R r+q := by
        have hm' := hUR r hrq
        rw [Nat.mod_eq_sub_mod (by omega : q ≤ U r),Nat.mod_eq_of_lt (by have := hU r; omega : U r-q < q)] at hm'
        omega
      rw [he,hFshift _ (Finset.mem_filter.mp (hRo r hr)).2]
      simp [σ,hu]
  have hrefShift (r : ℕ) (hr : r ∈ S) :
      F ((N : ZMod m) - ((r+q : ℕ) : ZMod m)) =
        -F ((N : ZMod m) - (r : ZMod m)) := by
    have hrq := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have hoddU : Odd (U r) := by
      have hh := Nat.mod_mod_of_dvd (U r) (even_iff_two_dvd.mp evenq)
      rw [hUR r hrq] at hh
      have ho := Nat.odd_iff.mp (Finset.mem_filter.mp (hRo r hr)).2
      exact Nat.odd_iff.mpr (by omega)
    have he : ((N : ZMod m) - ((r+q : ℕ) : ZMod m)) = ((U r+q : ℕ) : ZMod m) := by
      push_cast
      rw [hcastR r hrq]
      linear_combination -qzero
    rw [he,hFshift _ hoddU,hcastR r hrq]
  let P (x : ZMod m) : ℂ := star (F x) * F ((N : ZMod m)-x)
  have hPzero (x : ZMod m) (hx : ¬IsUnit x) : P x=0 := by
    dsimp only [P]
    rw [hFzero x hx,star_zero,zero_mul]
  have hPsum : (∑ x : (ZMod m)ˣ, P (x : ZMod m)) = 2 * ∑ r ∈ S, P (r : ZMod m) := by
    rw [unitRange P hPzero]
    conv_lhs => arg 1; rw [hm]
    rw [Finset.sum_range_add, ← Finset.sum_add_distrib, Finset.mul_sum,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases ho : Odd r
    · have hs : r ∈ S := Finset.mem_filter.mpr ⟨hr,ho⟩
      rw [if_pos ho,Nat.add_comm q r]
      dsimp only [P]
      rw [hFshift _ ho,hrefShift _ hs,star_neg]
      ring
    · have ho' : ¬ Odd (q+r) := by
        intro h
        have h1 := Nat.odd_iff.mp h
        have h2 := Nat.even_iff.mp evenq
        have h3 := Nat.mod_lt r (by decide : 0 < 2)
        exact ho (Nat.odd_iff.mpr (by omega))
      rw [if_neg ho,hPzero _ ((unitOdd r).not.mpr ho),
        hPzero _ ((unitOdd (q+r)).not.mpr ho'),add_zero]
  have hPpoint (r : ℕ) (hr : r ∈ S) :
      P (r : ZMod m) = (((L/2)^2 * (σ r * D r * D (R r)) : ℝ) : ℂ) := by
    dsimp only [P]
    rw [hsignF _ hr,hF _ hr,hF _ (hRo _ hr)]
    have hstar : star (((L/2*D r : ℝ) : ℂ)) = ((L/2*D r : ℝ):ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    rw [hstar]
    push_cast
    ring
  have hPsum' : (∑ x : (ZMod m)ˣ, P (x : ZMod m)) =
      (((m.totient : ℝ)/2 * ∑ r ∈ S, σ r * D r * D (R r) : ℝ) : ℂ) := by
    rw [hPsum,Finset.sum_congr rfl hPpoint]
    rw [← Complex.ofReal_sum,← Finset.mul_sum]
    have he : (L/2)^2 = (m.totient:ℝ)/4 := by nlinarith only [hLs]
    rw [he]
    push_cast
    ring
  change (∑ r ∈ S, σ r * D r * D (R r)) = _
  rw [hform]
  change _ = 2 * ((∑ x : (ZMod m)ˣ, P (x : ZMod m)) / (m.totient : ℂ)).re
  rw [hPsum']
  have hφc : (m.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
  have he : (((m.totient : ℝ)/2 * ∑ r ∈ S, σ r * D r * D (R r) : ℝ) : ℂ) / (m.totient : ℂ) =
      (((∑ r ∈ S, σ r * D r * D (R r))/2 : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [he, Complex.ofReal_re]
  ring
