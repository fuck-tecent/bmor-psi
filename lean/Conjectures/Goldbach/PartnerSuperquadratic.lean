import Mathlib
import Conjectures.Goldbach.PrimitivePartnerCubicMass

open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open scoped BigOperators Classical

namespace Conjectures.Goldbach.PartnerSuperquadraticProof

private noncomputable def errorTerm (t : ℝ) (p : ℕ) : ℝ :=
  (2 : ℝ) ^ (t - 1) * (p : ℝ) ^ (-(t / 2))

private def exceptionalFactor (p : ℕ) : ℝ := if p = 3 then 2 else 1

private theorem power_tail (t P : ℝ) (hP : 0 < P) :
    ((2 : ℝ) / Real.sqrt P) ^ (t - 2) * (2 / P) =
      (2 : ℝ) ^ (t - 1) * P ^ (-(t / 2)) := by
  rw [Real.div_rpow (by norm_num) (Real.sqrt_nonneg _) _, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hP.le]
  simp only [div_eq_mul_inv]
  rw [← Real.rpow_neg hP.le, ← Real.rpow_neg_one P]
  have h₂ : (2 : ℝ) ^ (t - 2) * 2 = (2 : ℝ) ^ (t - 1) := by
    calc
      _ = (2 : ℝ) ^ (t - 2) * (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
  have hP' : P ^ (-((1 / 2 : ℝ) * (t - 2))) * P ^ (-1 : ℝ) =
      P ^ (-(t / 2)) := by
    rw [← Real.rpow_add hP]
    congr 1
    ring
  calc
    _ = ((2 : ℝ) ^ (t - 2) * 2) *
        (P ^ (-((1 / 2 : ℝ) * (t - 2))) * P ^ (-1 : ℝ)) := by ring
    _ = _ := by rw [h₂, hP', div_eq_mul_inv t (2 : ℝ)]

private theorem local_moment {p q : ℕ} [Fact p.Prime] [NeZero q] (k m : ℕ)
    (hQ : q = p * p ^ k) (he : Even m) (A : DirichletCharacter ℂ q)
    (t : ℝ) (ht : 2 < t) :
    (∑ B : DirichletCharacter ℂ q,
      ‖J A B (m : ZMod q) / J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q)‖ ^ t) ≤
      exceptionalFactor p * Real.exp (errorTerm t p) := by
  subst q
  let q := p * p ^ k
  let W := ‖J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q)‖
  let X (B : DirichletCharacter ℂ q) := ‖J A B (m : ZMod q)‖ / W
  simp only [norm_div]
  change (∑ B : DirichletCharacter ℂ q, X B ^ t) ≤ _
  have hw : 0 < W := norm_pos_iff.mpr (principal_ne_zero q m he)
  have hp : p.Prime := Fact.out
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hn (B : DirichletCharacter ℂ q) : 0 ≤ X B := div_nonneg (norm_nonneg _) hw.le
  have hle (B : DirichletCharacter ℂ q) : X B ≤ 1 := by
    apply (div_le_one hw).2
    exact TwistedGoldbachSingularSeries.chars_le_units A B _
  have power_le_square (B : DirichletCharacter ℂ q) : X B ^ t ≤ X B ^ (2 : ℕ) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_ge' (hn B) (hle B) (by norm_num) ht.le
  have hW : W = (p : ℝ) ^ k * (if p ∣ m then (p : ℝ) - 1 else (p : ℝ) - 2) := by
    rw [← Nat.cast_pow]
    exact ordinary_prime_power k m
  have hφ : (q.totient : ℝ) = (p : ℝ) ^ k * ((p : ℝ) - 1) := by
    dsimp only [q]
    rw [← pow_succ', Nat.totient_prime_pow_succ hp]
    push_cast [Nat.cast_sub hp.one_le]
    ring
  have mass : (∑ B : DirichletCharacter ℂ q, X B ^ (2 : ℕ)) = (q.totient : ℝ) / W := by
    simp only [X, div_pow, ← sum_div, CubicPartnerResearch.row_plancherel]
    change (q.totient : ℝ) * W / W ^ 2 = (q.totient : ℝ) / W
    field_simp [hw.ne']
  have hpowers :
      (∑ B : DirichletCharacter ℂ q, X B ^ t) ≤
      (∑ B : DirichletCharacter ℂ q, X B ^ (2 : ℕ)) :=
    sum_le_sum (fun B _ => power_le_square B)
  have herror : 0 ≤ errorTerm t p := by unfold errorTerm; positivity
  have hexp : 1 ≤ Real.exp (errorTerm t p) := Real.one_le_exp herror
  by_cases hd : p ∣ m
  · have hden : W = (q.totient : ℝ) := by rw [hW, hφ, ite_eq_left hd]
    have hmass : (∑ B : DirichletCharacter ℂ q, X B ^ (2 : ℕ)) = 1 := by
      rw [mass, ← hden, div_self hw.ne']
    apply hpowers.trans (hmass.le.trans ?_)
    unfold exceptionalFactor
    split_ifs
    · linarith
    · simpa only [one_mul] using hexp
  have hmass : (∑ B : DirichletCharacter ℂ q, X B ^ (2 : ℕ)) =
      ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    rw [mass, hW, hφ, ite_eq_right hd]
    exact mul_div_mul_left _ _ (pow_ne_zero _ hp'.ne')
  by_cases h3 : p = 3
  · have hmass₂ : (∑ B : DirichletCharacter ℂ q, X B ^ (2 : ℕ)) = 2 := by
      rw [hmass, h3]
      norm_num
    apply hpowers.trans (hmass₂.le.trans ?_)
    simpa only [exceptionalFactor, h3, ite_true, mul_one] using
      mul_le_mul_of_nonneg_left hexp (show (0 : ℝ) ≤ 2 by norm_num)
  have h5 : 5 ≤ p := by
    have h₂ : p ≠ 2 := fun eq => hd (eq ▸ (even_iff_two_dvd.mp he))
    have h₄ : p ≠ 4 := by
      intro eq
      subst p
      norm_num at hp
    have hp₂ := hp.two_le
    omega
  have h5R : (5 : ℝ) ≤ p := by exact_mod_cast h5
  have hden : 0 < (p : ℝ) - 2 := by linarith
  have hroot_ge : (2 : ℝ) ≤ Real.sqrt p := by
    have hs : Real.sqrt (4 : ℝ) = 2 := by norm_num
    rw [← hs]
    exact Real.sqrt_le_sqrt (by linarith)
  have hroot_pos : 0 < Real.sqrt p := by linarith
  let cap := (2 : ℝ) / Real.sqrt p
  let u := cap ^ (t - 2)
  have cap_nonneg : 0 ≤ cap := by dsimp [cap]; positivity
  have cap_le : cap ≤ 1 := (div_le_one hroot_pos).2 hroot_ge
  have hu : 0 ≤ u := Real.rpow_nonneg cap_nonneg _
  have hu_le : u ≤ 1 := Real.rpow_le_one cap_nonneg cap_le (by linarith)
  have other (B : DirichletCharacter ℂ q) (hB : B ≠ 1) : X B ≤ cap := by
    have bound := CubicPartnerResearch.unit_pointwise k m hd A B (fun h => hB h.2)
    have hmax : (if A = 1 ∨ B = 1 then (1 : ℝ) else Real.sqrt p) ≤ Real.sqrt p := by
      split_ifs
      · linarith
      · exact le_rfl
    calc
      X B ≤ Real.sqrt p / ((p : ℝ) - 2) := by
        dsimp only [X]
        rw [hW, ite_eq_right hd]
        exact (div_le_div_of_nonneg_right
          (bound.trans (mul_le_mul_of_nonneg_left hmax (pow_nonneg hp'.le _)))
          (mul_nonneg (pow_nonneg hp'.le _) hden.le)).trans_eq
          (mul_div_mul_left _ _ (pow_ne_zero _ hp'.ne'))
      _ ≤ Real.sqrt p / ((p : ℝ) / 2) :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) (by linarith)
      _ = cap := by
        dsimp [cap]
        field_simp [hp'.ne', hroot_pos.ne']
        nlinarith [Real.sq_sqrt hp'.le]
  let rest := (univ : Finset (DirichletCharacter ℂ q)).erase 1
  have split_sum (f : DirichletCharacter ℂ q → ℝ) :
      (∑ B : DirichletCharacter ℂ q, f B) = f 1 + ∑ B ∈ rest, f B := by
    rw [add_comm]
    exact (sum_erase_add _ _ (mem_univ _)).symm
  have term (B : DirichletCharacter ℂ q) (hB : B ∈ rest) :
      X B ^ t ≤ X B ^ (2 : ℕ) * u := by
    have hpow : X B ^ t = X B ^ (2 : ℕ) * X B ^ (t - 2) := by
      rw [← Real.rpow_two, ← Real.rpow_add_of_nonneg (hn B) (by norm_num : (0 : ℝ) ≤ 2)
        (by linarith : 0 ≤ t - 2)]
      congr 1
      ring
    rw [hpow]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hn B)
      (other B (mem_erase.mp hB).1) (by linarith)) (sq_nonneg _)
  have primary : X 1 ^ (2 : ℕ) ≤ 1 := pow_le_one₀ (hn _) (hle _)
  have error_bound : u / ((p : ℝ) - 2) ≤ errorTerm t p := by
    calc
      _ ≤ u / ((p : ℝ) / 2) := div_le_div_of_nonneg_left hu (by positivity) (by linarith)
      _ = u * (2 / (p : ℝ)) := by ring
      _ = _ := power_tail t (p : ℝ) hp'
  rw [exceptionalFactor, ite_eq_right h3, one_mul]
  calc
    (∑ B : DirichletCharacter ℂ q, X B ^ t)
        ≤ X 1 ^ (2 : ℕ) + ∑ B ∈ rest, X B ^ (2 : ℕ) * u := by
      rw [split_sum]
      exact add_le_add (power_le_square _) (sum_le_sum term)
    _ = u * ((∑ B : DirichletCharacter ℂ q, X B ^ (2 : ℕ))) +
        (1 - u) * X 1 ^ (2 : ℕ) := by
      rw [split_sum, ← sum_mul]
      ring
    _ ≤ u * (((p : ℝ) - 1) / ((p : ℝ) - 2)) + (1 - u) * 1 := by
      rw [hmass]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left primary (sub_nonneg.mpr hu_le))
    _ = 1 + u / ((p : ℝ) - 2) := by field_simp [hden.ne']; ring
    _ ≤ 1 + errorTerm t p := add_le_add (le_refl 1) error_bound
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (errorTerm t p)

private theorem envelope_product (t : ℝ) (ht : 2 < t) (S : Finset ℕ) :
    (∏ p ∈ S, exceptionalFactor p * Real.exp (errorTerm t p)) ≤
      2 * Real.exp (∑' n : ℕ, errorTerm t n) := by
  have hSum : Summable (errorTerm t) :=
    (Real.summable_nat_rpow.mpr (by linarith : -(t / 2) < -1)).mul_left _
  have hsmall : (∏ p ∈ S, exceptionalFactor p) ≤ 2 := by
    unfold exceptionalFactor
    rw [Finset.prod_ite_eq' S 3 (fun _ => (2 : ℝ))]
    split_ifs <;> norm_num
  rw [prod_mul_distrib, ← Real.exp_sum]
  apply mul_le_mul hsmall (Real.exp_le_exp.mpr (hSum.sum_le_tsum S (fun n _ => by
    unfold errorTerm
    positivity))) (Real.exp_pos _).le
  norm_num

private theorem rpow_product {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (h : ∀ i, 0 ≤ f i) (t : ℝ) :
    (∏ i ∈ S, f i) ^ t = ∏ i ∈ S, (f i) ^ t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, Real.mul_rpow (h a) (prod_nonneg (fun i _ => h i)), ih]

private theorem global_moment (t : ℝ) (ht : 2 < t) {r : ℕ} [NeZero r]
    (α : DirichletCharacter ℂ r) (hα : α.IsPrimitive) (m : ℕ) (hm : 0 < m) (he : Even m)
    (F : Finset (Σ s : ℕ, DirichletCharacter ℂ s)) (hf : ∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive) :
    (∑ b ∈ F, ‖series α b.2 m‖ ^ t) ≤
      (2 * Real.exp (∑' n : ℕ, errorTerm t n)) *
        ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ t := by
  classical
  let D := r * ∏ b ∈ F, b.1
  have hD : 0 < D := Nat.mul_pos (NeZero.pos r) (prod_pos fun b hb => Nat.pos_of_ne_zero (hf b hb).1)
  letI : NeZero D := ⟨hD.ne'⟩
  let I := ↥D.primeFactors
  let Q (i : I) := (i : ℕ) ^ D.factorization i
  letI (i : I) : NeZero (Q i) := ⟨(Nat.ordProj_pos D i).ne'⟩
  let e := ZMod.equivPi D hD.ne'
  let hr : r ∣ D := dvd_mul_right r _
  have divides (b : F) : b.val.1 ∣ D :=
    (dvd_prod_of_mem (fun z : Σ s : ℕ, DirichletCharacter ℂ s => z.1) b.property).trans
      (dvd_mul_left _ r)
  let B (b : F) := changeLevel (divides b) b.val.2
  let coords (b : F) (i : I) := component e (B b) i
  have hInjective : Function.Injective coords := by
    intro b c h
    have same : B b = B c := by
      apply MulChar.ext
      intro u
      rw [reassemble e (B b) (u : ZMod D), reassemble e (B c) (u : ZMod D)]
      exact prod_congr rfl (fun i _ => congrArg
        (fun χ : DirichletCharacter ℂ (Q i) => χ (e u i)) (congrFun h i))
    have source_eq {s v : ℕ} (a : DirichletCharacter ℂ s) (c : DirichletCharacter ℂ v)
        (hs : s ∣ D) (hv : v ∣ D) (ha : a.IsPrimitive) (hc : c.IsPrimitive)
        (h : changeLevel hs a = changeLevel hv c) :
        (⟨s, a⟩ : Σ n : ℕ, DirichletCharacter ℂ n) = ⟨v, c⟩ := by
      have eq := congrArg DirichletCharacter.conductor h
      rw [conductor_changeLevel, conductor_changeLevel, ha, hc] at eq
      subst v
      exact congrArg (Sigma.mk s) (changeLevel_injective hs h)
    exact Subtype.ext (source_eq _ _ _ _ (hf _ b.property).2 (hf _ c.property).2 same)
  let A (i : I) := component e (changeLevel hr α) i
  let ratio (i : I) (b : DirichletCharacter ℂ (Q i)) :=
    ‖J (A i) b (m : ZMod (Q i)) / J (1 : DirichletCharacter ℂ (Q i)) 1 (m : ZMod (Q i))‖
  let ordinary := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ t
  have term (b : F) : ‖series α b.val.2 m‖ ^ t =
      ordinary * ∏ i, (ratio i (coords b i)) ^ t := by
    letI : NeZero b.val.1 := ⟨(hf _ b.property).1⟩
    rw [full_product e hα (hf _ b.property).2 hr (divides b) m hm he, norm_mul, norm_prod]
    change (_ * ∏ i, ratio i (coords b i)) ^ t = _
    rw [Real.mul_rpow (norm_nonneg _) (prod_nonneg (fun _ _ => norm_nonneg _))]
    rw [rpow_product _ _ (fun _ => norm_nonneg _)]
  have totals :
      (∑ b : F, ∏ i, (ratio i (coords b i)) ^ t) ≤ ∏ i, ∑ c, (ratio i c) ^ t := by
    rw [Fintype.prod_sum]
    let f (c : ∀ i, DirichletCharacter ℂ (Q i)) : ℝ := ∏ i, (ratio i (c i)) ^ t
    change (∑ b : F, f (coords b)) ≤ ∑ c, f c
    rw [← sum_image (f := f) hInjective.injOn]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun c _ _ => prod_nonneg
      (fun i _ => Real.rpow_nonneg (norm_nonneg _) _))
  have bounds (i : I) :
      (∑ b, (ratio i b) ^ t) ≤ exceptionalFactor i * Real.exp (errorTerm t i) := by
    have h := Nat.mem_primeFactors.mp i.property
    letI : Fact (i : ℕ).Prime := ⟨h.1⟩
    have hpos := (h.1.dvd_iff_one_le_factorization hD.ne').mp h.2.1
    have hexp : D.factorization i = D.factorization i - 1 + 1 := by omega
    have hQ : Q i = (i : ℕ) * (i : ℕ) ^ (D.factorization i - 1) := by
      dsimp only [Q]
      rw [← pow_succ', ← hexp]
    exact local_moment _ m hQ he (A i) t ht
  have hbound : (∏ i, ∑ c, (ratio i c) ^ t) ≤ 2 * Real.exp (∑' n : ℕ, errorTerm t n) := calc
    _ ≤ ∏ i : I, exceptionalFactor i * Real.exp (errorTerm t i) :=
      prod_le_prod₀ (fun i _ => sum_nonneg (fun c _ => Real.rpow_nonneg (norm_nonneg _) _))
        (fun i _ => bounds i)
    _ = ∏ p ∈ D.primeFactors, exceptionalFactor p * Real.exp (errorTerm t p) :=
      prod_coe_sort D.primeFactors (fun p => exceptionalFactor p * Real.exp (errorTerm t p))
    _ ≤ _ := envelope_product t ht _
  rw [← sum_coe_sort F]
  calc
    _ = ordinary * ∑ b : F, ∏ i, (ratio i (coords b i)) ^ t := by
      rw [mul_sum]
      exact sum_congr rfl (fun b _ => term b)
    _ ≤ ordinary * (2 * Real.exp (∑' n : ℕ, errorTerm t n)) :=
      mul_le_mul_of_nonneg_left (totals.trans hbound) (Real.rpow_nonneg (norm_nonneg _) _)
    _ = _ := mul_comm _ _

private theorem superquadratic (t : ℝ) (ht : 2 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) [NeZero r] (α : DirichletCharacter ℂ r), α.IsPrimitive →
    ∀ m : ℕ, 0 < m → Even m → ∀ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
    (∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive) →
      (∑ b ∈ F, ‖series α b.2 m‖ ^ t) ≤ C *
        ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ t := by
  refine ⟨2 * Real.exp (∑' n : ℕ, errorTerm t n), by positivity, ?_⟩
  intro r _ α hα m hm he F hf
  exact global_moment t ht α hα m hm he F hf

end Conjectures.Goldbach.PartnerSuperquadraticProof

theorem Conjectures.Goldbach.PartnerSuperquadratic :
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
  exact ∀ t : ℝ, 2 < t → ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) [NeZero r] (α : DirichletCharacter ℂ r), α.IsPrimitive →
    ∀ m : ℕ, 0 < m → Even m →
    ∀ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
    (∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive) →
    (∑ b ∈ F, ‖S α b.2 m‖ ^ t) ≤ C * ‖O m‖ ^ t := by
  exact Conjectures.Goldbach.PartnerSuperquadraticProof.superquadratic
