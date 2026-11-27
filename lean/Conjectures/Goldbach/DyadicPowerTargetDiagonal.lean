import Mathlib

/- gggreatboy, upstream PR 2870, commit 9096c74880d047ed65ddb48a7ade29b797f16d6f,
   Apache-2.0. The following primitive character criterion is reused as a private lemma.
   The unit reflection and orthogonality argument after it are new. -/
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


theorem Conjectures.Goldbach.DyadicPowerTargetDiagonal :
    ∀ (N k : ℕ), Even N → 1 ≤ k →
  let m : ℕ := 2^(k+1)
  m ∣ 2*N →
    ∀ (χ ψ : DirichletCharacter ℂ m), ψ.IsPrimitive →
      (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m))) /
        (m.totient : ℂ) =
      if χ=ψ then if m ∣ N then ψ (-1) else -ψ (-1) else 0 := by
  classical
  intro N k hNe hk m hd χ ψ hψ
  haveI : NeZero m := ⟨by dsimp [m]; positivity⟩
  have twoN : (2:ZMod m)*N = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff (2*N) m).mpr hd
  have hodd (x : (ZMod m)ˣ) : Odd (x : ZMod m).val :=
    Nat.coprime_two_right.mp ((ZMod.val_coe_unit_coprime x).of_dvd_right
      (by dsimp [m]; exact dvd_pow_self _ (by omega)))
  have hmult (x : (ZMod m)ˣ) : (N:ZMod m)*(x:ZMod m) = N := by
    obtain ⟨j,hj⟩ := hodd x
    have he : (x:ZMod m) = 2*(j:ZMod m)+1 := by
      rw [← ZMod.natCast_zmod_val (x:ZMod m)]
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using congrArg (fun t : ℕ => (t : ZMod m)) hj
    rw [he]; linear_combination (j:ZMod m) * twoN
  have href (x : (ZMod m)ˣ) : (N:ZMod m) - x = ((N:ZMod m)-1)*x := by
    rw [sub_mul,one_mul,hmult]
  let θ := χ⁻¹ * ψ
  have hf (x : (ZMod m)ˣ) : star (χ (x:ZMod m))*ψ ((N:ZMod m)-x) =
      ψ ((N:ZMod m)-1)*θ (x:ZMod m) := by
    rw [href,map_mul,MulChar.star_apply']; simp [θ,MulChar.mul_apply]; ring
  simp_rw [hf]
  rw [← Finset.mul_sum]
  by_cases heq : χ=ψ
  · subst χ
    have hθ : θ=1 := by simp [θ]
    simp only [if_true,hθ,MulChar.one_apply_coe,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,mul_one,ZMod.card_units_eq_totient]
    have hφ : (m.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos m)).ne'
    rw [mul_div_cancel_right₀ _ hφ]
    by_cases hm : m ∣ N
    · rw [if_pos hm,(ZMod.natCast_eq_zero_iff _ _).mpr hm,zero_sub]
    · rw [if_neg hm]
      have half : 2^k ∣ N := by
        have htmp : 2 * 2^k ∣ 2*N := by simpa [m,pow_succ'] using hd
        exact (Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) htmp)
      obtain ⟨t,ht⟩ := half
      have oddt : Odd t := by
        by_contra h
        obtain ⟨j,hj⟩ := Nat.not_odd_iff_even.mp h
        apply hm
        refine ⟨j,?_⟩
        rw [ht,hj]; dsimp [m]; ring
      obtain ⟨j,hj⟩ := oddt
      have hN : (N:ZMod m) = (2^k:ℕ) := by
        have he : N = 2^k + m*j := by rw [ht,hj]; dsimp [m]; ring
        rw [he]; simp
      have hzero : ((2^k:ℕ):ZMod m) + ((2^k:ℕ):ZMod m) = 0 := by
        have h : 2^k + 2^k = m := by dsimp [m]; rw [pow_succ]; omega
        simpa using (congrArg (fun n : ℕ => (n:ZMod m)) h)
      have hneg : (N:ZMod m)-1 = -1 * ((1+2^k:ℕ):ZMod m) := by
        rw [hN]; push_cast at *; linear_combination hzero
      rw [hneg,map_mul,(kernelCriterion k ψ hk).mp hψ]; ring
  · rw [if_neg heq]
    have hθ : θ≠1 := by
      intro h
      apply heq
      change χ⁻¹*ψ=1 at h
      simpa [mul_assoc] using (congrArg (fun t => χ*t) h).symm
    obtain ⟨b,hb⟩ := MulChar.ne_one_iff.mp hθ
    have hs : ∑ x : (ZMod m)ˣ, θ (x:ZMod m) = 0 := by
      apply eq_zero_of_mul_eq_self_left hb
      simpa only [Finset.mul_sum, ← map_mul, ← Units.val_mul] using
        (Group.mulLeft_bijective b).sum_comp (fun x : (ZMod m)ˣ => θ (x:ZMod m))
    rw [hs,mul_zero,zero_div]
