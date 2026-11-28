import Mathlib
import Conjectures.Goldbach.PrimitivePartnerCubicMass

/-! Exact quadratic mass of the twisted singular series over all primitive partners
inside one common level `D`. The row orthogonality of `PrimitivePartnerCubicMass`
is combined with the CRT factorization of `SharpSingularSeriesRatios` and with the
bijection between characters of level `D` and primitive characters of levels dividing `D`.
Adapted from `Conjectures.Goldbach.PrimitivePartnerCubicMass` (PR 4245) and
`Conjectures.Goldbach.SharpSingularSeriesRatios`. -/

namespace Conjectures.Goldbach.PartnerLevelParseval_aux

open Finset DirichletCharacter MulChar
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open scoped BigOperators Classical

/-! ### Row orthogonality at one level -/

private theorem local_parseval {q : ℕ} [NeZero q] (A : DirichletCharacter ℂ q) (m : ℕ) (he : Even m) :
    (∑ C : DirichletCharacter ℂ q,
      ‖J A C (m : ZMod q) / J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q)‖ ^ 2) =
      (q.totient : ℝ) / ‖J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q)‖ := by
  have h := CubicPartnerResearch.row_plancherel A (m : ZMod q)
  have hne : ‖J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (principal_ne_zero q m he)
  simp_rw [norm_div, div_pow, ← sum_div]
  rw [h]
  field_simp [hne]

private theorem local_value {p q : ℕ} [Fact p.Prime] [NeZero q] (j m : ℕ) (hq : q = p * p ^ j)
    (he : Even m) (A : DirichletCharacter ℂ q) :
    (∑ C : DirichletCharacter ℂ q,
      ‖J A C (m : ZMod q) / J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q)‖ ^ 2) =
      if p ∣ m then 1 else ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  subst hq
  rw [local_parseval A m he]
  have hp : p.Prime := Fact.out
  have hJ := ordinary_prime_power (p := p) j m
  have hφ : ((p * p ^ j).totient : ℝ) = ((p ^ j : ℕ) : ℝ) * ((p : ℝ) - 1) := by
    rw [← pow_succ', Nat.totient_prime_pow_succ hp]
    push_cast [Nat.cast_sub hp.one_le]
    ring
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hpow : (p : ℝ) ^ j ≠ 0 := pow_ne_zero j hp0
  rw [hφ, hJ]
  push_cast
  split_ifs with hpm
  · have h1 : (p : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith
    field_simp [hpow, h1]
  · have hp3 : 3 ≤ p := by
      have := hp.two_le
      have : p ≠ 2 := fun h => hpm (h ▸ even_iff_two_dvd.mp he)
      omega
    have h2 : (p : ℝ) - 2 ≠ 0 := by
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    field_simp [hpow, h2]

/-! ### The CRT bijection on characters -/

private noncomputable def glue {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℕ}
    {L : ℕ} (e : ZMod L ≃+* ∀ i, ZMod (q i))
    (f : ∀ i, DirichletCharacter ℂ (q i)) : DirichletCharacter ℂ L where
  toFun x := ∏ i, f i (e x i)
  map_one' := by simp
  map_mul' x y := by
    have h : ∀ i, f i (e (x * y) i) = f i (e x i) * f i (e y i) := by
      intro i
      rw [e.map_mul, Pi.mul_apply, map_mul]
    simp only [h, ← Finset.prod_mul_distrib]
  map_nonunit' x hx := by
    by_contra h
    apply hx
    have hall : ∀ i, IsUnit (e x i) := by
      intro i
      by_contra hi
      exact h (Finset.prod_eq_zero (Finset.mem_univ i) (MulChar.map_nonunit (f i) hi))
    simpa using (Pi.isUnit_iff.mpr hall).map e.symm

private noncomputable def phiEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℕ}
    {L : ℕ} (e : ZMod L ≃+* ∀ i, ZMod (q i)) :
    DirichletCharacter ℂ L ≃ ∀ i, DirichletCharacter ℂ (q i) where
  toFun := component e
  invFun := glue e
  left_inv χ := by
    apply MulChar.ext'
    intro x
    exact (reassemble e χ x).symm
  right_inv f := by
    funext i
    apply MulChar.ext'
    intro x
    show ∏ j, f j (e (e.symm (Pi.mulSingle i x)) j) = f i x
    rw [e.apply_symm_apply]
    rw [Finset.prod_eq_single i]
    · rw [Pi.mulSingle_eq_same]
    · intro j _ hji
      rw [Pi.mulSingle_eq_of_ne hji, map_one]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

/-! ### Primitive origins of a character of level `D` -/

private theorem core {s t L : ℕ} [NeZero L] (a : DirichletCharacter ℂ s) (b : DirichletCharacter ℂ t)
    (hs : s ∣ L) (ht : t ∣ L) (ha : a.IsPrimitive) (hb : b.IsPrimitive)
    (h : changeLevel hs a = changeLevel ht b) :
    (⟨s, a⟩ : Σ n : ℕ, DirichletCharacter ℂ n) = ⟨t, b⟩ := by
  have eqst := congrArg DirichletCharacter.conductor h
  rw [conductor_changeLevel, conductor_changeLevel, ha, hb] at eqst
  subst t
  exact congrArg (Sigma.mk s) (changeLevel_injective hs h)

private theorem lift_congr {s t L : ℕ} (hs : s ∣ L) (ht : t ∣ L)
    (a : DirichletCharacter ℂ s) (b : DirichletCharacter ℂ t)
    (h : (⟨s, a⟩ : Σ n : ℕ, DirichletCharacter ℂ n) = ⟨t, b⟩) :
    changeLevel hs a = changeLevel ht b := by
  cases h
  rfl

private theorem main {D r : ℕ} [NeZero D] [NeZero r] (hr : r ∣ D)
    (α : DirichletCharacter ℂ r) (hα : α.IsPrimitive) (m : ℕ) (hm : 0 < m) (he : Even m) :
    ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
      (∀ b, b ∈ F ↔ b.1 ≠ 0 ∧ b.1 ∣ D ∧ b.2.IsPrimitive) ∧
      (∑ b ∈ F, ‖series α b.2 m‖ ^ 2) =
        ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ 2 *
          ∏ p ∈ D.primeFactors.filter (fun p => ¬ p ∣ m), (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  let I := ↥D.primeFactors
  let Q (i : I) := (i : ℕ) ^ D.factorization (i : ℕ)
  haveI (i : I) : NeZero (Q i) :=
    ⟨pow_ne_zero _ (Nat.Prime.ne_zero (Nat.mem_primeFactors.mp i.property).1)⟩
  let e := ZMod.equivPi D (NeZero.ne D)
  let w (i : I) (C : DirichletCharacter ℂ (Q i)) : ℝ :=
    ‖J (component e (changeLevel hr α) i) C (m : ZMod (Q i)) /
      J (1 : DirichletCharacter ℂ (Q i)) 1 (m : ZMod (Q i))‖ ^ 2
  let g : DirichletCharacter ℂ D → Σ s : ℕ, DirichletCharacter ℂ s :=
    fun B => ⟨B.conductor, B.primitiveCharacter⟩
  let F := univ.image g
  refine ⟨F, ?_, ?_⟩
  · intro b
    simp only [F, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨B, rfl⟩
      exact ⟨B.conductor_ne_zero, B.conductor_dvd_level, B.primitiveCharacter_isPrimitive⟩
    · rintro ⟨hb0, hbd, hbprim⟩
      obtain ⟨s, β⟩ := b
      haveI : NeZero s := ⟨hb0⟩
      refine ⟨changeLevel hbd β, ?_⟩
      dsimp only [g]
      exact core _ _ _ _ (primitiveCharacter_isPrimitive _) hbprim (changeLevel_primitiveCharacter _)
  · have hsum : (∑ b ∈ F, ‖series α b.2 m‖ ^ 2) =
        ∑ B : DirichletCharacter ℂ D, ‖series α B.primitiveCharacter m‖ ^ 2 := by
      have ginj : ∀ B C : DirichletCharacter ℂ D, g B = g C → B = C := by
        intro B C hBC
        have h1 := lift_congr B.conductor_dvd_level C.conductor_dvd_level
          B.primitiveCharacter C.primitiveCharacter hBC
        rw [changeLevel_primitiveCharacter, changeLevel_primitiveCharacter] at h1
        exact h1
      dsimp only [F]
      rw [sum_image (fun x _ y _ h => ginj x y h)]
    have hfac : ∀ B : DirichletCharacter ℂ D, ‖series α B.primitiveCharacter m‖ ^ 2 =
        ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ 2 *
        ∏ i : I, w i (component e B i) := by
      intro B
      haveI : NeZero B.conductor := ⟨B.conductor_ne_zero⟩
      have hB := full_product e hα B.primitiveCharacter_isPrimitive hr B.conductor_dvd_level m hm he
      have hch : changeLevel B.conductor_dvd_level B.primitiveCharacter = B :=
        changeLevel_primitiveCharacter B
      rw [hch] at hB
      rw [hB, norm_mul, norm_prod, mul_pow, prod_pow]
    have hprod : (∑ B : DirichletCharacter ℂ D, ∏ i : I, w i (component e B i)) =
        ∏ i : I, ∑ C : DirichletCharacter ℂ (Q i), w i C := by
      calc (∑ B : DirichletCharacter ℂ D, ∏ i : I, w i (component e B i))
          = ∑ f : ∀ i, DirichletCharacter ℂ (Q i), ∏ i : I, w i (f i) :=
            Equiv.sum_comp (phiEquiv e)
              (fun f : ∀ i, DirichletCharacter ℂ (Q i) => ∏ i : I, w i (f i))
        _ = ∏ i : I, ∑ C : DirichletCharacter ℂ (Q i), w i C :=
            (Fintype.prod_sum (fun i C => w i C)).symm
    have hloc : ∀ i : I, (∑ C : DirichletCharacter ℂ (Q i), w i C) =
        if (i : ℕ) ∣ m then 1 else ((i : ℝ) - 1) / ((i : ℝ) - 2) := by
      intro i
      have hi := Nat.mem_primeFactors.mp i.property
      letI : Fact (i : ℕ).Prime := ⟨hi.1⟩
      obtain ⟨a, ha⟩ : ∃ a, D.factorization (i : ℕ) = a + 1 := by
        have := (hi.1.dvd_iff_one_le_factorization (NeZero.ne D)).mp hi.2.1
        exact ⟨D.factorization (i : ℕ) - 1, by omega⟩
      have hQ : Q i = (i : ℕ) * (i : ℕ) ^ a := by
        dsimp only [Q]
        rw [ha, pow_succ']
      exact local_value a m hQ he (component e (changeLevel hr α) i)
    rw [hsum]
    simp_rw [hfac]
    rw [← Finset.mul_sum, hprod]
    congr 1
    simp_rw [hloc]
    rw [Finset.prod_filter]
    trans (∏ p ∈ D.primeFactors, if p ∣ m then (1 : ℝ) else ((p : ℝ) - 1) / ((p : ℝ) - 2))
    · dsimp only [I]
      exact Finset.prod_coe_sort D.primeFactors
        (fun p => if p ∣ m then (1 : ℝ) else ((p : ℝ) - 1) / ((p : ℝ) - 2))
    · apply Finset.prod_congr rfl
      intro p hp
      by_cases hpm : p ∣ m <;> simp [hpm]

end Conjectures.Goldbach.PartnerLevelParseval_aux

theorem Conjectures.Goldbach.PartnerLevelParseval :
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  exact ∀ (D r : ℕ) [NeZero D] [NeZero r], r ∣ D → ∀ α : DirichletCharacter ℂ r, α.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s), (∀ b, b ∈ F ↔ b.1 ≠ 0 ∧ b.1 ∣ D ∧ b.2.IsPrimitive) ∧ (∑ b ∈ F, ‖S α b.2 m‖ ^ 2) = ‖O m‖ ^ 2 * ∏ p ∈ D.primeFactors.filter (fun p => ¬ p ∣ m), (((p:ℝ)-1)/((p:ℝ)-2))
:= by
  classical
  dsimp only
  intro D r instD instr hr α hα m hm he
  exact Conjectures.Goldbach.PartnerLevelParseval_aux.main hr α hα m hm he
