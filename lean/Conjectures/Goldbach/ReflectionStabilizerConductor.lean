import Mathlib

/-!
# PREPUB goldbach gap: `L-goldbach-reflection-stabilizer-conductor`

Let `m ≥ 1`, `N ∈ ℕ`, `χ` a Dirichlet character mod `m`, and set `g = gcd(m,N)`,
`d = m/g`.  For `ψ` a character mod `m` define the reflection sum

`R ψ = ∑_{x ∈ (Z/m)^*} conj (χ x) · ψ (N - x)`.

**Reflection–stabilizer invariance.**  If `u ∈ (Z/m)^*` with `u ≡ 1 (mod d)`, then
`N - u z = u (N - z)` in `Z/m` because `(1-u)·N ≡ 0 (mod m)` (as `d | u-1` and
`m | d·N`).  Hence, substituting `x = u z` and using multiplicativity,
`R ψ = conj(χ u) ψ(u) · R ψ`.

Consequences:

1. if `R ψ ≠ 0`, then `conj(χ u) ψ(u) = 1` for every such `u`; since character
   values are roots of unity this says `(χ⁻¹ψ)(u) = 1`, i.e. `χ⁻¹ψ` factors through
   level `d`, so `conductor (χ⁻¹ψ) ∣ d`;
2. the `ψ` with `R ψ ≠ 0` therefore inject into the characters factoring through
   level `d` (via `ψ ↦ χ⁻¹ψ` and the conductor), giving
   `#{ψ : R ψ ≠ 0} ≤ φ(d)`.

All arguments are elementary; no zeros of L-functions or distribution input is used.
-/

open scoped BigOperators

noncomputable section

namespace PEqualNP.Outside

variable {m : ℕ} [NeZero m]

/-- Character values at units are roots of unity, so conjugation is inversion. -/
theorem star_apply_units (χ : DirichletCharacter ℂ m) (u : (ZMod m)ˣ) :
    star (χ (u : ZMod m)) = (χ (u : ZMod m))⁻¹ := by
  have hcoe : χ (u : ZMod m) = ↑(MulChar.equivToUnitHom χ u) :=
    (MulChar.coe_equivToUnitHom χ u).symm
  rw [hcoe]
  have hpow : ((MulChar.equivToUnitHom χ u) : ℂ) ^ (Fintype.card (ZMod m)ˣ) = 1 := by
    have hz : (MulChar.equivToUnitHom χ u) ^ (Fintype.card (ZMod m)ˣ) = 1 := by
      have h1 : u ^ (Fintype.card (ZMod m)ˣ) = 1 := pow_card_eq_one
      calc (MulChar.equivToUnitHom χ u) ^ (Fintype.card (ZMod m)ˣ)
          = MulChar.equivToUnitHom χ (u ^ (Fintype.card (ZMod m)ˣ)) := (map_pow _ _ _).symm
        _ = 1 := by rw [h1, map_one]
    calc ((MulChar.equivToUnitHom χ u) : ℂ) ^ (Fintype.card (ZMod m)ˣ)
        = (((MulChar.equivToUnitHom χ u) ^ (Fintype.card (ZMod m)ˣ) : ℂˣ) : ℂ) :=
          (Units.val_pow_eq_pow_val _ _).symm
      _ = 1 := by rw [hz, Units.val_one]
  have hcard : Fintype.card (ZMod m)ˣ ≠ 0 := by
    have hpos : 0 < Fintype.card (ZMod m)ˣ := Fintype.card_pos_iff.mpr ⟨(1 : (ZMod m)ˣ)⟩
    omega
  have hnorm : ‖((MulChar.equivToUnitHom χ u) : ℂ)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hpow hcard
  rw [Complex.inv_eq_conj hnorm, Complex.star_def]

end PEqualNP.Outside

/- PREPUB frozen statement `L-goldbach-reflection-stabilizer-conductor`, under its
platform module name. -/
theorem Conjectures.Goldbach.ReflectionStabilizerConductor :
    ∀ (m : ℕ) [NeZero m] (N : ℕ) (χ : DirichletCharacter ℂ m),
      let d := m / Nat.gcd m N
      let R := fun ψ : DirichletCharacter ℂ m =>
        ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m))
      (∀ ψ, R ψ ≠ 0 → (χ⁻¹ * ψ).conductor ∣ d) ∧
        ((Finset.univ : Finset (DirichletCharacter ℂ m)).filter (fun ψ => R ψ ≠ 0)).card ≤ d.totient := by
  intro m _ N χ
  classical
  dsimp only
  set g : ℕ := Nat.gcd m N with hg
  set d : ℕ := m / g with hd
  set Rfun : DirichletCharacter ℂ m → ℂ :=
    fun ψ => ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m)) with hR
  have hgpos : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_left N (NeZero.pos m)
  have hgdm : g ∣ m := by rw [hg]; exact Nat.gcd_dvd_left m N
  have hgdn : g ∣ N := by rw [hg]; exact Nat.gcd_dvd_right m N
  have hdvd : d ∣ m := by rw [hd]; exact Nat.div_dvd_of_dvd hgdm
  have hgd : g * d = m := by
    rw [hd, hg]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left m N)
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, mul_zero] at hgd
      exact absurd hgd.symm (NeZero.ne m)
    · exact h
  haveI : NeZero d := ⟨Nat.pos_iff_ne_zero.mp hdpos⟩
  have hNd : N = g * (N / g) := by
    rw [hg]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right m N)).symm
  have hdN : d * N = m * (N / g) := by
    have h1 : d * N = (m / g) * (g * (N / g)) := by
      rw [hd]
      exact congrArg (fun t => (m / g) * t) hNd
    calc d * N = (m / g) * (g * (N / g)) := h1
      _ = ((m / g) * g) * (N / g) := by rw [mul_assoc]
      _ = m * (N / g) := by rw [Nat.div_mul_cancel hgdm]
  -- kernel of the reduction: `(1 - u) * N = 0`
  have hzero : ∀ u : (ZMod m)ˣ, ZMod.unitsMap hdvd u = 1 →
      ((1 : ZMod m) - (u : ZMod m)) * (N : ZMod m) = 0 := by
    intro u hu
    have hcast : ((u : ZMod m).cast : ZMod d) = 1 := by
      have h := congrArg (fun y : (ZMod d)ˣ => (y : ZMod d)) hu
      rw [ZMod.unitsMap_val] at h
      simpa using h
    have hval_mod : ((((u : ZMod m).val : ℕ)) : ZMod d) = 1 := by
      have h2 : (ZMod.cast (((((u : ZMod m).val : ℕ)) : ZMod m)) : ZMod d)
          = ((((u : ZMod m).val : ℕ)) : ZMod d) :=
        ZMod.cast_natCast (R := ZMod d) hdvd (((u : ZMod m).val : ℕ))
      rw [ZMod.natCast_zmod_val] at h2
      rw [← h2]
      exact hcast
    have hmod : (u : ZMod m).val ≡ 1 [MOD d] :=
      (ZMod.natCast_eq_natCast_iff (u : ZMod m).val 1 d).mp (by simpa using hval_mod)
    obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp hmod
    have hk1 : (1 : ℤ) - (((u : ZMod m).val : ℕ) : ℤ) = (d : ℤ) * k := by simpa using hk
    have hk' : ((u : ZMod m).val : ℤ) = 1 - (d : ℤ) * k := by linarith
    have hx : (u : ZMod m) = 1 - (d : ZMod m) * (k : ZMod m) := by
      calc (u : ZMod m) = ((((u : ZMod m).val : ℕ)) : ZMod m) := (ZMod.natCast_zmod_val _).symm
        _ = ((((u : ZMod m).val : ℤ)) : ZMod m) := by push_cast; ring_nf
        _ = ((1 - (d : ℤ) * k : ℤ) : ZMod m) := by rw [hk']
        _ = 1 - (d : ZMod m) * (k : ZMod m) := by push_cast; ring
    have hdN0 : (d : ZMod m) * (N : ZMod m) = 0 := by
      have hcast2 : (((d * N : ℕ)) : ZMod m) = 0 := by
        rw [hdN, Nat.cast_mul, ZMod.natCast_self, zero_mul]
      rwa [Nat.cast_mul] at hcast2
    calc ((1 : ZMod m) - (u : ZMod m)) * (N : ZMod m)
        = ((d : ZMod m) * (k : ZMod m)) * (N : ZMod m) := by rw [hx]; ring
      _ = (k : ZMod m) * ((d : ZMod m) * (N : ZMod m)) := by ring
      _ = 0 := by rw [hdN0, mul_zero]
  -- reflection-stabilizer invariance
  have hinv : ∀ (u : (ZMod m)ˣ), ZMod.unitsMap hdvd u = 1 → ∀ ψ : DirichletCharacter ℂ m,
      Rfun ψ = (star (χ (u : ZMod m)) * ψ (u : ZMod m)) * Rfun ψ := by
    intro u hu ψ
    have hNu : (N : ZMod m) = (u : ZMod m) * (N : ZMod m) := by
      have h := hzero u hu
      rw [sub_mul, one_mul] at h
      exact sub_eq_zero.mp h
    let eu : (ZMod m)ˣ ≃ (ZMod m)ˣ :=
      { toFun := fun x => u * x, invFun := fun x => u⁻¹ * x,
        left_inv := fun x => by simp [mul_assoc],
        right_inv := fun x => by simp [mul_assoc] }
    have hsum : (∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m)))
        = ∑ x : (ZMod m)ˣ, star (χ (((u * x : (ZMod m)ˣ)) : ZMod m))
            * ψ ((N : ZMod m) - ((u * x : (ZMod m)ˣ) : ZMod m)) := by
      have h := (Equiv.sum_comp eu (fun x : (ZMod m)ˣ =>
        star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m)))).symm
      simpa [eu] using h
    have hpoint : ∀ x : (ZMod m)ˣ,
        star (χ (((u * x : (ZMod m)ˣ)) : ZMod m)) * ψ ((N : ZMod m) - ((u * x : (ZMod m)ˣ) : ZMod m))
          = (star (χ (u : ZMod m)) * ψ (u : ZMod m))
              * (star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m))) := by
      intro x
      have hux : (((u * x : (ZMod m)ˣ)) : ZMod m) = (u : ZMod m) * (x : ZMod m) := Units.val_mul _ _
      have hchi : χ (((u * x : (ZMod m)ˣ)) : ZMod m) = χ (u : ZMod m) * χ (x : ZMod m) := by
        rw [hux, map_mul]
      have harg : (N : ZMod m) - (((u * x : (ZMod m)ˣ)) : ZMod m)
          = (u : ZMod m) * ((N : ZMod m) - (x : ZMod m)) := by
        rw [hux, mul_sub, ← hNu]
      have hpsi : ψ ((N : ZMod m) - (((u * x : (ZMod m)ˣ)) : ZMod m))
          = ψ (u : ZMod m) * ψ ((N : ZMod m) - (x : ZMod m)) := by
        rw [harg, map_mul]
      rw [hchi, hpsi, star_mul]
      ring
    have hR1 : Rfun ψ = ∑ x : (ZMod m)ˣ,
        star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m)) := by rw [hR]
    calc Rfun ψ
        = ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m)) := hR1
      _ = ∑ x : (ZMod m)ˣ, (star (χ (u : ZMod m)) * ψ (u : ZMod m))
              * (star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m))) := by
          rw [hsum]
          exact Finset.sum_congr rfl (fun x _ => hpoint x)
      _ = (star (χ (u : ZMod m)) * ψ (u : ZMod m))
              * ∑ x : (ZMod m)ˣ, star (χ (x : ZMod m)) * ψ ((N : ZMod m) - (x : ZMod m)) := by
          rw [Finset.mul_sum]
      _ = (star (χ (u : ZMod m)) * ψ (u : ZMod m)) * Rfun ψ := by rw [hR1]
  -- part 1: conductor divides `d`
  have hpart1 : ∀ ψ, Rfun ψ ≠ 0 → (χ⁻¹ * ψ).conductor ∣ d := by
    intro ψ hψ
    rw [← DirichletCharacter.mem_conductorSet_iff_conductor_dvd (χ⁻¹ * ψ) hdvd]
    rw [DirichletCharacter.mem_conductorSet_iff (χ := χ⁻¹ * ψ) (x := d)]
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap hdvd).mpr ?_
    intro u hu
    have hu' : ZMod.unitsMap hdvd u = 1 := (MonoidHom.mem_ker).mp hu
    have hinvu := hinv u hu' ψ
    have hK : star (χ (u : ZMod m)) * ψ (u : ZMod m) = 1 := by
      have hz : (star (χ (u : ZMod m)) * ψ (u : ZMod m) - 1) * Rfun ψ = 0 := by
        rw [sub_mul, one_mul, hinvu.symm, sub_self]
      rcases mul_eq_zero.mp hz with h1 | h2
      · exact sub_eq_zero.mp h1
      · exact absurd h2 hψ
    have hχinv : (χ⁻¹ * ψ) (u : ZMod m) = 1 := by
      rw [MulChar.mul_apply, MulChar.inv_apply_eq_inv, Ring.inverse_eq_inv,
        ← PEqualNP.Outside.star_apply_units χ u]
      exact hK
    rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [Units.val_one, MulChar.coe_toUnitHom]
    exact hχinv
  constructor
  · exact hpart1
  · set S : Finset (DirichletCharacter ℂ m) :=
      (Finset.univ : Finset (DirichletCharacter ℂ m)).filter (fun ψ => Rfun ψ ≠ 0) with hS
    set T : Finset (DirichletCharacter ℂ m) :=
      (Finset.univ : Finset (DirichletCharacter ℂ m)).filter
        (fun ξ => ξ.FactorsThrough d) with hT
    set Φ : DirichletCharacter ℂ m → DirichletCharacter ℂ m := fun ψ => χ⁻¹ * ψ with hΦ
    have hmaps : Set.MapsTo Φ ↑S ↑T := by
      intro ψ hψ
      simp only [hS, hT, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hψ ⊢
      have hcond := hpart1 ψ hψ
      have hmem : d ∈ (χ⁻¹ * ψ).conductorSet :=
        (DirichletCharacter.mem_conductorSet_iff_conductor_dvd (χ⁻¹ * ψ) hdvd).mpr hcond
      have hft := (DirichletCharacter.mem_conductorSet_iff (χ := χ⁻¹ * ψ) (x := d)).mp hmem
      simpa [hΦ] using hft
    have hinjS : Set.InjOn Φ ↑S := by
      intro a _ b _ hab
      have h := congrArg (fun t => χ * t) hab
      simpa [hΦ, mul_assoc] using h
    have hcard1 : S.card ≤ T.card :=
      Finset.card_le_card_of_injOn Φ hmaps hinjS
    -- characters factoring through `d` inject into characters of level `d`
    have hcard2 : T.card ≤ d.totient := by
      set Ψ : DirichletCharacter ℂ m → DirichletCharacter ℂ d :=
        fun ξ => if h : ξ.FactorsThrough d then h.χ₀ else 1 with hΨ
      have hmaps2 : Set.MapsTo Ψ ↑T ↑(Finset.univ : Finset (DirichletCharacter ℂ d)) := by
        intro ξ hξ
        simp only [hT, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hξ
        simp [hΨ, hξ]
      have hinj2 : Set.InjOn Ψ ↑T := by
        intro a ha b hb hab
        simp only [hT, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
        simp only [hΨ, dif_pos ha, dif_pos hb] at hab
        rw [DirichletCharacter.FactorsThrough.eq_changeLevel ha,
          DirichletCharacter.FactorsThrough.eq_changeLevel hb, hab]
      calc T.card ≤ (Finset.univ : Finset (DirichletCharacter ℂ d)).card :=
            Finset.card_le_card_of_injOn Ψ hmaps2 hinj2
        _ = Fintype.card (DirichletCharacter ℂ d) := by rw [Finset.card_univ]
        _ = Nat.card (DirichletCharacter ℂ d) := (Nat.card_eq_fintype_card).symm
        _ = d.totient := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
    calc S.card ≤ T.card := hcard1
      _ ≤ d.totient := hcard2
