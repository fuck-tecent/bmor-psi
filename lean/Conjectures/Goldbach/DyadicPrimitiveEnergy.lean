import Mathlib

/- gggreatboy, upstream PR 2870, commit 9096c74880d047ed65ddb48a7ade29b797f16d6f,
   Apache-2.0. The following primitive character criterion is reused as a private lemma.
   The projection and Parseval argument below are new. -/
private theorem kernelCriterion :
∀ (k : ℕ) (χ : DirichletCharacter ℂ (2^(k+1))), 1 ≤ k →
  (χ.IsPrimitive ↔ χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) = -1) := by
  intro k χ hk
  haveI : NeZero (2^(k+1)) := ⟨by positivity⟩
  have hd : 2^k ∣ 2^(k+1) := pow_dvd_pow 2 (Nat.le_succ k)
  have hlt : 1 < 2^k := by
    calc (1:ℕ) < 2^1 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  -- `1 + 2^k` is odd, hence a unit modulo `2^(k+1)`.
  have hodd : Odd (1 + 2^k) := by
    rw [add_comm, Nat.odd_add_one, Nat.not_odd_iff_even]
    exact ⟨2^(k-1), by rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hk]⟩
  have hcop : Nat.Coprime (1 + 2^k) (2^(k+1)) :=
    Nat.Coprime.pow_right (k+1) hodd.coprime_two_right
  -- The kernel of reduction modulo `2^k` consists of `1` and `1 + 2^k`.
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
  -- The value at `1 + 2^k` detects factoring through level `2^k`.
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
  · -- primitive ⇒ value `-1`
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
  · -- value `-1` ⇒ primitive
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


private theorem energy {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (s : Finset κ) (A : ι → κ → ℂ) (v : κ → ℂ) (c : ℝ)
    (h : ∀ j ∈ s, ∀ k ∈ s, (∑ i, A i j * star (A i k)) = if j=k then (c:ℂ) else 0) :
    (∑ i, ‖∑ j ∈ s, A i j * v j‖^2) = c * ∑ j ∈ s, ‖v j‖^2 := by
  classical
  have expand i : ((‖∑ j ∈ s, A i j * v j‖^2 : ℝ):ℂ) =
      ∑ j ∈ s, ∑ k ∈ s, (A i j * star (A i k)) * (v j * star (v k)) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    change _ * star _ = _
    simp only [star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    ring
  have eq : (∑ i, ((‖∑ j ∈ s, A i j * v j‖^2 : ℝ):ℂ)) =
       ∑ j ∈ s, (c:ℂ) * ((‖v j‖^2 : ℝ):ℂ) := by
    simp_rw [expand]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j hj
    rw [Finset.sum_comm]
    apply Eq.trans (Finset.sum_congr rfl (fun k hk => by rw [← Finset.sum_mul,h j hj k hk,ite_mul,zero_mul]))

    simp [hj,Complex.ofReal_pow,← Complex.mul_conj']
  have re := congrArg Complex.re eq
  simpa only [Complex.re_sum,Complex.ofReal_re,← Complex.ofReal_mul,← Finset.mul_sum] using re

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

set_option maxHeartbeats 1000000 in
theorem Conjectures.Goldbach.DyadicPrimitiveEnergy : ∀ (k : ℕ), 1 ≤ k →
  let q : ℕ := 2^k
  let m : ℕ := 2^(k+1)
  ∀ f : ZMod m → ℝ,
    (∑ r ∈ (Finset.range q).filter (fun r => Odd r), (f (r : ZMod m) - f ((r+q : ℕ) : ZMod m))^2) =
      2 / (m.totient : ℝ) * ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ m)).filter (fun χ => χ.conductor = m),
        ‖∑ x : (ZMod m)ˣ, (f (x : ZMod m) : ℂ) * star (χ (x : ZMod m))‖^2 := by
  classical
  intro k hk q m f
  have hm : m = q+q := by dsimp [m,q]; rw [pow_succ]; omega
  haveI : NeZero m := ⟨by dsimp [m]; positivity⟩
  let T : ZMod m := ((1+q : ℕ):ZMod m)
  let S := (Finset.range q).filter Odd
  let C := (Finset.univ : Finset (DirichletCharacter ℂ m)).filter (fun χ => χ.conductor=m)
  let D := fun r : ℕ => f (r:ZMod m) - f ((r+q:ℕ):ZMod m)
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
  have all := energy S A (fun r => (D r:ℂ)) c orth
  have rhs : (∑ χ ∈ C, ‖∑ x : (ZMod m)ˣ, (f (x:ZMod m):ℂ)*star (χ (x:ZMod m))‖^2) =
      c * ∑ r ∈ S, (D r)^2 := by
    calc _ = ∑ χ ∈ C, ‖∑ r ∈ S, A χ r*(D r:ℂ)‖^2 := Finset.sum_congr rfl (fun χ hh => by rw [freq χ hh])
         _ = ∑ χ, ‖∑ r ∈ S, A χ r*(D r:ℂ)‖^2 := Finset.sum_subset (Finset.subset_univ _) (fun χ _ hh => by simp [A,hh])
         _ = _ := by simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using all
  change (∑ r ∈ S, (D r)^2) = 2 / _ * _
  rw [rhs]
  have hφ : (m.totient:ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos m)).ne'
  dsimp [c]; field_simp
