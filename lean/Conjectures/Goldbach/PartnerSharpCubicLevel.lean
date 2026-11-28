import Mathlib
import Conjectures.Goldbach.PrimitivePartnerCubicMass

/-! The optimal cubic row constant at an odd squarefree level.
The local prime-power row bounds and the Euler product for the twisted
singular series are those of `Conjectures.Goldbach.PrimitivePartnerCubicMass`
(itself adapted from zxg0623, Goldbach PR 4023, Apache-2.0); here they are
combined with an exact CRT bijection between characters of the squarefree
level and the primitive partners of the divisors, which turns the uniform
bound into an exact optimum attained by the principal row at target two. -/

namespace Conjectures.Goldbach.PartnerSharpCubicLevel_aux

open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open SquarefreeTwistedGoldbachDensity
open Finset DirichletCharacter
open scoped BigOperators Classical

private theorem card_chars {p : ℕ} [Fact p.Prime] :
    Fintype.card (DirichletCharacter ℂ p) = p - 1 := by
  rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p,
    Nat.totient_prime (Fact.out : p.Prime)]

/-- At an odd prime the principal row at target two has the exact cubic mass
`1 + 1/(p-2)^2`. -/
private theorem local_exact_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (∑ c : DirichletCharacter ℂ p, ‖J (1 : DirichletCharacter ℂ p) c (2 : ZMod p) /
        J (1 : DirichletCharacter ℂ p) 1 (2 : ZMod p)‖ ^ 3) = 1 + 1 / ((p : ℝ) - 2) ^ 2 := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hm0 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have ht (c : DirichletCharacter ℂ p) :
      ‖J (1 : DirichletCharacter ℂ p) c (2 : ZMod p)‖ = if c = 1 then (p : ℝ) - 2 else 1 := by
    have h := local_norm (1 : DirichletCharacter ℂ p) c (2 : ZMod p)
    change ‖localSum (1 : DirichletCharacter ℂ p) c (2 : ZMod p)‖ = _ at h
    rw [ite_eq_right hm0] at h
    by_cases hc : c = 1
    · rw [ite_eq_left hc]
      have h' : ‖localSum (1 : DirichletCharacter ℂ p) c (2 : ZMod p)‖ = (p : ℝ) - 2 := by
        simpa [hc] using h
      exact h'
    · rw [ite_eq_right hc]
      have h' : ‖localSum (1 : DirichletCharacter ℂ p) c (2 : ZMod p)‖ = 1 := by
        simpa [hc] using h
      exact h'
  have hW : ‖J (1 : DirichletCharacter ℂ p) 1 (2 : ZMod p)‖ = (p : ℝ) - 2 := by
    have h := ht 1
    rwa [ite_eq_left rfl] at h
  have dpos : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    linarith
  have step : (∑ c : DirichletCharacter ℂ p, ‖J (1 : DirichletCharacter ℂ p) c (2 : ZMod p) /
        J (1 : DirichletCharacter ℂ p) 1 (2 : ZMod p)‖ ^ 3) =
      ∑ c : DirichletCharacter ℂ p, (if c = 1 then (1 : ℝ) else (1 / ((p : ℝ) - 2)) ^ 3) := by
    apply Finset.sum_congr rfl
    intro c _
    rw [norm_div, ht c, hW]
    split_ifs with hc
    · rw [div_self dpos.ne', one_pow]
    · rw [one_div]
  rw [step, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ p))]
  simp only [ite_true]
  have h2 : (∑ c ∈ (univ : Finset (DirichletCharacter ℂ p)).erase 1,
      (if c = 1 then (1 : ℝ) else (1 / ((p : ℝ) - 2)) ^ 3)) =
      ∑ _c ∈ (univ : Finset (DirichletCharacter ℂ p)).erase 1, (1 / ((p : ℝ) - 2)) ^ 3 := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [ite_eq_right (Finset.ne_of_mem_erase hc)]
  rw [h2, Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ 1),
    Finset.card_univ, card_chars]
  have hsub : p - 1 - 1 = p - 2 := by omega
  rw [hsub]
  have hcast : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ p)]; norm_num
  rw [hcast]
  field_simp [dpos.ne']

/-- The local cubic row bound at an odd prime, in the form needed for the
product over the prime factors of the level. -/
private theorem local_bound {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) (k m q : ℕ)
    (hq : q = p * p ^ k) [NeZero q] (he : Even m) (A : DirichletCharacter ℂ q) :
    (∑ c : DirichletCharacter ℂ q, ‖J A c (m : ZMod q) /
        J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q)‖ ^ 3) ≤ 1 + 1 / ((p : ℝ) - 2) ^ 2 := by
  subst q
  have hW : 0 < ‖J (1 : DirichletCharacter ℂ (p * p ^ k)) 1 (m : ZMod (p * p ^ k))‖ :=
    norm_pos_iff.mpr (principal_ne_zero _ m he)
  by_cases hpm : p ∣ m
  · have h := CubicPartnerResearch.divisible_row (p := p) k m hpm A
    dsimp only at h
    calc
      _ = ∑ c : DirichletCharacter ℂ (p * p ^ k),
            ‖J A c (m : ZMod (p * p ^ k))‖ ^ 3 /
              ‖J (1 : DirichletCharacter ℂ (p * p ^ k)) 1 (m : ZMod (p * p ^ k))‖ ^ 3 := by
        apply Finset.sum_congr rfl
        intro c _
        rw [norm_div, div_pow]
      _ = (∑ c : DirichletCharacter ℂ (p * p ^ k),
            ‖J A c (m : ZMod (p * p ^ k))‖ ^ 3) /
            ‖J (1 : DirichletCharacter ℂ (p * p ^ k)) 1 (m : ZMod (p * p ^ k))‖ ^ 3 :=
        by rw [Finset.sum_div]
      _ ≤ 1 := by
        rw [div_le_one (pow_pos hW 3)]
        exact h
      _ ≤ _ := by
        have : (0 : ℝ) ≤ 1 / ((p : ℝ) - 2) ^ 2 := by positivity
        linarith
  · have h := CubicPartnerResearch.unit_row (p := p) hp3 k m hpm A
    dsimp only at h
    simpa only [norm_div] using h

section CRT

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℕ} [∀ i, NeZero (q i)]
  {L : ℕ} (e : ZMod L ≃+* ∀ i, ZMod (q i))

/-- The character of level `L` with prescribed CRT components. -/
private noncomputable def ofComponents (g : ∀ i, DirichletCharacter ℂ (q i)) :
    DirichletCharacter ℂ L where
  toFun x := ∏ i, g i (e x i)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, Pi.mul_apply, Finset.prod_mul_distrib]
  map_nonunit' x hx := by
    by_contra h0
    apply hx
    have hu : ∀ i, IsUnit (e x i) := by
      intro i
      by_contra hi
      exact h0 (Finset.prod_eq_zero (Finset.mem_univ i) (MulChar.map_nonunit (g i) hi))
    have hux : IsUnit (e x) := Pi.isUnit_iff.mpr hu
    simpa using hux.map e.symm

private theorem component_ofComponents (g : ∀ i, DirichletCharacter ℂ (q i)) (i : ι) :
    component e (ofComponents e g) i = g i := by
  apply MulChar.ext
  intro u
  change (∏ j, g j (e (e.symm (Pi.mulSingle i (u : ZMod (q i)))) j)) = g i u
  simp only [e.apply_symm_apply]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    rw [Pi.mulSingle_eq_of_ne hji]
    exact map_one (g j)
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem components_bijective :
    Function.Bijective (fun χ : DirichletCharacter ℂ L => fun i => component e χ i) := by
  constructor
  · intro χ ψ h
    apply MulChar.ext
    intro u
    rw [reassemble e χ u, reassemble e ψ u]
    exact Finset.prod_congr rfl (fun i _ =>
      congrArg (fun c : DirichletCharacter ℂ (q i) => c (e u i)) (congrFun h i))
  · intro g
    exact ⟨ofComponents e g, funext (fun i => component_ofComponents e g i)⟩

end CRT

/-- The primitive partner attached to a character of the fixed level. -/
private noncomputable def partner {D : ℕ} (χ : DirichletCharacter ℂ D) :
    Σ s : ℕ, DirichletCharacter ℂ s :=
  ⟨χ.conductor, χ.primitiveCharacter⟩

private noncomputable def liftTo {D : ℕ} (b : Σ t : ℕ, DirichletCharacter ℂ t) :
    DirichletCharacter ℂ D :=
  if h : b.1 ∣ D then changeLevel h b.2 else 1

private theorem liftTo_partner {D : ℕ} (χ : DirichletCharacter ℂ D) : liftTo (partner χ) = χ := by
  unfold liftTo partner
  rw [dite_eq_left χ.conductor_dvd_level]
  exact χ.changeLevel_primitiveCharacter

private theorem partner_inj {D : ℕ} : Function.Injective (partner (D := D)) := by
  intro χ ψ h
  have := congrArg (liftTo (D := D)) h
  rwa [liftTo_partner, liftTo_partner] at this

private theorem partner_eq_of_lift {D : ℕ} [NeZero D] {s t : ℕ}
    (a : DirichletCharacter ℂ s) (b : DirichletCharacter ℂ t)
    (hs : s ∣ D) (ht : t ∣ D) (ha : a.IsPrimitive) (hb : b.IsPrimitive)
    (h : changeLevel hs a = changeLevel ht b) :
    (⟨s, a⟩ : Σ n : ℕ, DirichletCharacter ℂ n) = ⟨t, b⟩ := by
  have eqst := congrArg DirichletCharacter.conductor h
  rw [conductor_changeLevel, conductor_changeLevel, ha, hb] at eqst
  subst t
  exact congrArg (Sigma.mk s) (changeLevel_injective hs h)

private theorem mem_partner_image {D : ℕ} [NeZero D] (s : ℕ) (β : DirichletCharacter ℂ s) :
    (⟨s, β⟩ : Σ t : ℕ, DirichletCharacter ℂ t) ∈
        (univ : Finset (DirichletCharacter ℂ D)).image (partner (D := D)) ↔
      s ≠ 0 ∧ s ∣ D ∧ β.IsPrimitive := by
  constructor
  · intro hb
    obtain ⟨χ, _, hχ⟩ := Finset.mem_image.mp hb
    have h1 : χ.conductor = s := congrArg Sigma.fst hχ
    have hd : s ∣ D := h1 ▸ χ.conductor_dvd_level
    have hlift : liftTo (⟨s, β⟩ : Σ t : ℕ, DirichletCharacter ℂ t) = χ := by
      have h := congrArg (liftTo (D := D)) hχ
      rw [liftTo_partner] at h
      exact h.symm
    have h2 : changeLevel hd β = χ := by
      unfold liftTo at hlift
      rwa [dite_eq_left hd] at hlift
    refine ⟨?_, hd, ?_⟩
    · intro hs
      exact χ.conductor_ne_zero (h1.trans hs)
    · show β.conductor = s
      rw [← conductor_changeLevel β hd, h2, h1]
  · rintro ⟨_, hd, hp⟩
    refine Finset.mem_image.mpr ⟨changeLevel hd β, Finset.mem_univ _, ?_⟩
    exact partner_eq_of_lift _ _ _ hd (DirichletCharacter.primitiveCharacter_isPrimitive _) hp
      (changeLevel hd β).changeLevel_primitiveCharacter

theorem main (D : ℕ) (hD : 0 < D) (hodd : Odd D) (hsf : Squarefree D) :
    ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
      (∀ b, b ∈ F ↔ b.1 ≠ 0 ∧ b.1 ∣ D ∧ b.2.IsPrimitive) ∧
      (∑ b ∈ F, ‖series (1 : DirichletCharacter ℂ 1) b.2 2‖ ^ 3) =
        ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖ ^ 3 *
          (∏ p ∈ D.primeFactors, (1 + 1 / ((p : ℝ) - 2) ^ 2)) ∧
      ∀ (r : ℕ) [NeZero r], r ∣ D → ∀ α : DirichletCharacter ℂ r, α.IsPrimitive →
        ∀ m : ℕ, 0 < m → Even m →
          (∑ b ∈ F, ‖series α b.2 m‖ ^ 3) ≤
            ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ 3 *
              (∏ p ∈ D.primeFactors, (1 + 1 / ((p : ℝ) - 2) ^ 2)) := by
  classical
  letI : NeZero D := ⟨hD.ne'⟩
  let ι := ↥D.primeFactors
  let q : ι → ℕ := fun i => (i : ℕ)
  have hq (i : ι) : (i : ℕ).Prime := Nat.prime_of_mem_primeFactors i.property
  letI (i : ι) : NeZero (i : ℕ) := ⟨(hq i).ne_zero⟩
  letI (i : ι) : Fact (i : ℕ).Prime := ⟨hq i⟩
  have hq2 (i : ι) : q i ≠ 2 := by
    intro h
    dsimp only [q] at h
    have hd : (i : ℕ) ∣ D := Nat.dvd_of_mem_primeFactors i.property
    have hd2 : 2 ∣ D := h ▸ hd
    have hmod : D % 2 = 0 := Nat.mod_eq_zero_of_dvd hd2
    have hodd' : D % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  have hq3 (i : ι) : 3 ≤ q i := by
    have h1 : 2 ≤ q i := (hq i).two_le
    have h2 := hq2 i
    omega
  have hDprod : (∏ i : ι, (i : ℕ)) = D := by
    have h1 : (∏ i : ι, (i : ℕ)) = ∏ p : ↥D.primeFactors, (p : ℕ) ^ D.factorization p :=
      Finset.prod_congr rfl (fun p _ => by
        rw [Nat.factorization_eq_one_of_squarefree hsf (hq p)
          (Nat.dvd_of_mem_primeFactors p.property), pow_one])
    exact h1.trans (Nat.prod_primeFactors_coe_pow_factorization hD.ne').symm
  have hcop : Pairwise (fun i j : ι => Nat.Coprime (i : ℕ) (j : ℕ)) := by
    intro i j hij
    refine (hq i).coprime_iff_not_dvd.mpr (fun hd => hij (Subtype.ext ?_))
    rcases (Nat.dvd_prime (hq j)).mp hd with h1 | h
    · exact absurd h1 (hq i).ne_one
    · exact h
  let e : ZMod D ≃+* ∀ i, ZMod (q i) :=
    (ZMod.ringEquivCongr hDprod.symm).trans (ZMod.prodEquivPi (fun i : ι => (i : ℕ)) hcop)
  let F := (univ : Finset (DirichletCharacter ℂ D)).image (partner (D := D))
  have hprod : (∏ i : ι, (1 + 1 / ((q i : ℝ) - 2) ^ 2)) =
      ∏ p ∈ D.primeFactors, (1 + 1 / ((p : ℝ) - 2) ^ 2) :=
    Finset.prod_coe_sort D.primeFactors (fun p : ℕ => 1 + 1 / ((p : ℝ) - 2) ^ 2)
  have hmem : ∀ b, b ∈ F ↔ b.1 ≠ 0 ∧ b.1 ∣ D ∧ b.2.IsPrimitive := by
    rintro ⟨s, β⟩
    exact mem_partner_image s β
  have key : ∀ (r : ℕ) [NeZero r] (hr : r ∣ D) (α : DirichletCharacter ℂ r)
      (hα : α.IsPrimitive) (m : ℕ) (hm : 0 < m) (he : Even m),
      (∑ b ∈ F, ‖series α b.2 m‖ ^ 3) =
        ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ 3 *
          ∏ i : ι, ∑ c : DirichletCharacter ℂ (q i),
            ‖J (component e (changeLevel hr α) i) c (m : ZMod (q i)) /
              J (1 : DirichletCharacter ℂ (q i)) 1 (m : ZMod (q i))‖ ^ 3 := by
    intro r inst hr α hα m hm he
    let W (i : ι) (c : DirichletCharacter ℂ (q i)) : ℝ :=
      ‖J (component e (changeLevel hr α) i) c (m : ZMod (q i)) /
        J (1 : DirichletCharacter ℂ (q i)) 1 (m : ZMod (q i))‖ ^ 3
    have hsum : (∑ b ∈ F, ‖series α b.2 m‖ ^ 3) =
        ∑ χ : DirichletCharacter ℂ D, ‖series α (partner χ).2 m‖ ^ 3 := by
      dsimp only [F]
      rw [Finset.sum_image (partner_inj (D := D)).injOn]
    have on (χ : DirichletCharacter ℂ D) : ‖series α (partner χ).2 m‖ ^ 3 =
        ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ 3 *
          ∏ i : ι, W i (component e χ i) := by
      haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      have h := full_product e hα χ.primitiveCharacter_isPrimitive hr χ.conductor_dvd_level m hm he
      rw [χ.changeLevel_primitiveCharacter] at h
      dsimp only [partner]
      rw [h, norm_mul, norm_prod, mul_pow]
      dsimp only [W]
      rw [prod_pow]
    calc
      (∑ b ∈ F, ‖series α b.2 m‖ ^ 3) = ∑ χ : DirichletCharacter ℂ D, ‖series α (partner χ).2 m‖ ^ 3 := hsum
      _ = ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ 3 *
            ∑ χ : DirichletCharacter ℂ D, ∏ i : ι, W i (component e χ i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun χ _ => on χ)
      _ = ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ 3 *
            ∑ g : ∀ i, DirichletCharacter ℂ (q i), ∏ i : ι, W i (g i) := by
        congr 1
        exact Equiv.sum_comp
          (Equiv.ofBijective (fun χ : DirichletCharacter ℂ D => fun i => component e χ i)
            (components_bijective e)) (fun g => ∏ i : ι, W i (g i))
      _ = _ := by rw [← Fintype.prod_sum W]
  refine ⟨F, hmem, ?_, ?_⟩
  · rw [key 1 (one_dvd D) (1 : DirichletCharacter ℂ 1) isPrimitive_one_level_one 2
      (by norm_num) (by decide)]
    have hA : ∀ i : ι, component e (changeLevel (one_dvd D) (1 : DirichletCharacter ℂ 1)) i = 1 := by
      intro i
      rw [map_one]
      exact component_one e i
    have hloc : ∀ i : ι, (∑ c : DirichletCharacter ℂ (q i),
        ‖J (component e (changeLevel (one_dvd D) (1 : DirichletCharacter ℂ 1)) i) c
            ((2 : ℕ) : ZMod (q i)) /
          J (1 : DirichletCharacter ℂ (q i)) 1 ((2 : ℕ) : ZMod (q i))‖ ^ 3) =
        1 + 1 / ((q i : ℝ) - 2) ^ 2 := by
      intro i
      rw [hA i]
      exact local_exact_two (p := (i : ℕ)) (hq2 i)
    rw [Finset.prod_congr rfl (fun i _ => hloc i), hprod]
  · intro r inst hr α hα m hm he
    rw [key r hr α hα m hm he]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg _) _)
    rw [← hprod]
    apply Finset.prod_le_prod₀
      (fun i _ => Finset.sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _))
    intro i _
    exact local_bound (p := (i : ℕ)) (hq3 i) 0 m (q i) (by dsimp only [q]; simp) he
      (component e (changeLevel hr α) i)

end Conjectures.Goldbach.PartnerSharpCubicLevel_aux

theorem Conjectures.Goldbach.PartnerSharpCubicLevel :
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
  exact ∀ D : ℕ, 0 < D → Odd D → Squarefree D → ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s), (∀ b, b ∈ F ↔ b.1 ≠ 0 ∧ b.1 ∣ D ∧ b.2.IsPrimitive) ∧ (∑ b ∈ F, ‖S (1 : DirichletCharacter ℂ 1) b.2 2‖ ^ 3) = ‖O 2‖ ^ 3 * (∏ p ∈ D.primeFactors, (1+1/((p:ℝ)-2)^2)) ∧ ∀ (r : ℕ) [NeZero r], r ∣ D → ∀ α : DirichletCharacter ℂ r, α.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → (∑ b ∈ F, ‖S α b.2 m‖ ^ 3) ≤ ‖O m‖ ^ 3 * (∏ p ∈ D.primeFactors, (1+1/((p:ℝ)-2)^2)) := by
  classical
  dsimp only
  intro D hD hodd hsf
  exact Conjectures.Goldbach.PartnerSharpCubicLevel_aux.main D hD hodd hsf
