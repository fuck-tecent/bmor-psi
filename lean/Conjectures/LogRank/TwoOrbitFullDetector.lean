import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic

/-!
# Two-Orbit Full Detector at One-Third Density (`L-log-rank-two-orbit-full-detector`)

Self-contained formal proof that for all sufficiently large `k` (`n = 3k + 1`), there exists a
size-`k` seed `S ⊆ Fin n` such that `orbit I ∪ orbit S` detects every interior row `A`
(`2 ≤ |A| ≤ n - 2`), where `I = {0, 1, ..., k - 1}`.

Architecture:
1. `TwoOrbitDiscrepancy`: Self-contained finite-combinatorics proof of Spencer's (1985)
   three-valued coloring lemma (via Shannon entropy / Gibbs inequality + Rademacher Hoeffding +
   Hamming ball counting) extended to arbitrary `x₀ ∈ [-1, 1]^n` and iterated to full `±1` coloring.
2. `TwoOrbitCosine`: Rudin-Shapiro cosine polynomial `cosPoly` with exact parallelogram-law
   derivative bounds, Rolle + MVT `intervals_nice`, Chebyshev root counting of well-separated bad
   runs (`cosine_bad_runs`).
3. `TwoOrbitFejer`: Nonnegative Fejér-kernel smoothing (`fejerK`, `quadInt`) + two-stage
   discrepancy coloring yielding an odd sine polynomial `s_o` large on every bad run at all
   `n = 3k + 1` roots of unity.
4. `TwoOrbitPerturb`: Finite product-weight probabilistic perturbation (`probWU`), binomial mode
   lower bound, sub-Gaussian MGF tail bound, and exact disjoint-block cover/miss factorization.
5. `TwoOrbitFlatSeed`, `TwoOrbit`, `TwoOrbitCertificate`, `TwoOrbitMiddle`: Polynomial-to-seed
   identities, greedy disjoint translate packing, and Parseval spectral middle-row reduction.
6. `TwoOrbitBridge` & `Conjectures.LogRank.TwoOrbitFullDetector`: Assembly of the discrete flat
   Littlewood initial seed `S₀`, exact-size probabilistic perturbation to `S`, and conclusion.
-/


/-!
# Elementary Spencer Partial Coloring & Full Discrepancy Coloring

Completely self-contained finite-combinatorics proof of the three-valued coloring lemma
(Spencer 1985 via Shannon entropy / Gibbs inequality and Hamming ball counting)
extended to arbitrary starting points `x₀ ∈ [-1, 1]^n` and iterated to full `±1` coloring.
Zero measure theory or Brownian motion dependencies.
-/

namespace TwoOrbitDiscrepancy

open scoped BigOperators
open Finset

/-! ### Section 1: Elementary analytic inequalities -/

private lemma le_of_hasDerivAt_nonpos {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hnp : ∀ x, a < x → x < b → f' x ≤ 0) : f b ≤ f a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · have hpos : 0 < b - a := sub_pos.mpr hlt
    let s : ℝ := (f b - f a) / (b - a)
    let g : ℝ → ℝ := fun x => f x - s * (x - a)
    have hg_deriv : ∀ x, HasDerivAt g (f' x - s) x := fun x => by
      have hlin : HasDerivAt (fun y : ℝ => s * (y - a)) s x :=
        (((hasDerivAt_id' x).sub_const a).const_mul s).congr_deriv (by ring)
      exact (hd x).sub hlin
    have hg_eq : g a = g b := by
      dsimp only [g, s]; field_simp [hpos.ne']; ring
    obtain ⟨c, ⟨hca, hcb⟩, hc⟩ := exists_deriv_eq_zero hlt
      (fun x _ => (hg_deriv x).continuousAt.continuousWithinAt) hg_eq
    rw [(hg_deriv c).deriv] at hc
    have hnp_c : f' c ≤ 0 := hnp c hca hcb
    have hs_le : s ≤ 0 := by linarith
    dsimp only [s] at hs_le
    rw [div_le_iff₀ hpos] at hs_le
    linarith

private lemma prod_le_prod_nonneg {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : 0 ≤ f a := hf a (Finset.mem_insert_self _ _)
    have h2 : f a ≤ g a := hfg a (Finset.mem_insert_self _ _)
    have h3 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h4 : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    exact mul_le_mul h2 h4 h3 (h1.trans h2)

/-- `(exp t + exp (-t)) / 2 ≤ exp (t^2 / 2)` for all real `t`. -/
lemma cosh_half_le_exp_sq_half (t : ℝ) :
    (Real.exp t + Real.exp (-t)) / 2 ≤ Real.exp (t ^ 2 / 2) := by
  suffices hnonneg : ∀ s : ℝ, 0 ≤ s →
      (Real.exp s + Real.exp (-s)) / 2 ≤ Real.exp (s ^ 2 / 2) by
    rcases le_total 0 t with ht | ht
    · exact hnonneg t ht
    · have := hnonneg (-t) (by linarith)
      simpa [add_comm, neg_sq] using this
  intro s hs
  have hexp_neg : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := fun x =>
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).congr_deriv (by ring)
  -- Let `u(x) = (exp x - exp (-x)) - x * (exp x + exp (-x))`; `u(0) = 0`, `u'(x) = -x * (exp x - exp (-x)) ≤ 0`.
  let u : ℝ → ℝ := fun x => (Real.exp x - Real.exp (-x)) - x * (Real.exp x + Real.exp (-x))
  have hu_deriv : ∀ x : ℝ, HasDerivAt u (-x * (Real.exp x - Real.exp (-x))) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => Real.exp y) (Real.exp x) x := Real.hasDerivAt_exp x
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := hexp_neg x
    have hsub : HasDerivAt (fun y : ℝ => Real.exp y - Real.exp (-y)) (Real.exp x + Real.exp (-x)) x :=
      (h1.sub h2).congr_deriv (by ring)
    have hadd : HasDerivAt (fun y : ℝ => Real.exp y + Real.exp (-y)) (Real.exp x - Real.exp (-x)) x :=
      (h1.add h2).congr_deriv (by ring)
    have hmul : HasDerivAt (fun y : ℝ => y * (Real.exp y + Real.exp (-y)))
        (1 * (Real.exp x + Real.exp (-x)) + x * (Real.exp x - Real.exp (-x))) x :=
      (hasDerivAt_id' x).mul hadd
    exact (hsub.sub hmul).congr_deriv (by ring)
  have hu_nonpos : ∀ x : ℝ, 0 ≤ x → u x ≤ 0 := by
    intro x hx
    have hle := le_of_hasDerivAt_nonpos hx hu_deriv fun y hy0 _ => by
      have hexp : Real.exp (-y) ≤ Real.exp y := Real.exp_le_exp.mpr (by linarith)
      nlinarith
    have h0 : u 0 = 0 := by simp [u]
    linarith
  -- Let `g(x) = exp (-x^2 / 2) * ((exp x + exp (-x)) / 2)`; `g(0) = 1`, `g'(x) = exp (-x^2/2) * u(x) / 2 ≤ 0`.
  let g : ℝ → ℝ := fun x => Real.exp (-(x ^ 2 / 2)) * ((Real.exp x + Real.exp (-x)) / 2)
  have hg_deriv : ∀ x : ℝ, HasDerivAt g (Real.exp (-(x ^ 2 / 2)) * (u x / 2)) x := by
    intro x
    have hsq : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x := by
      have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        have hmul : HasDerivAt (fun y : ℝ => y * y) (2 * x) x :=
          ((hasDerivAt_id' x).mul (hasDerivAt_id' x)).congr_deriv (by ring)
        simpa [pow_two] using hmul
      exact ((h1.div_const 2).neg).congr_deriv (by ring)
    have he : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) (Real.exp (-(x ^ 2 / 2)) * (-x)) x := by
      simpa [Function.comp_def] using (Real.hasDerivAt_exp (-(x ^ 2 / 2))).comp x hsq
    have hc : HasDerivAt (fun y : ℝ => (Real.exp y + Real.exp (-y)) / 2) ((Real.exp x - Real.exp (-x)) / 2) x := by
      have h1 : HasDerivAt (fun y : ℝ => Real.exp y) (Real.exp x) x := Real.hasDerivAt_exp x
      have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := hexp_neg x
      exact ((h1.add h2).div_const 2).congr_deriv (by ring)
    exact (he.mul hc).congr_deriv (by dsimp only [u]; ring)
  have hg_le : g s ≤ 1 := by
    have hle := le_of_hasDerivAt_nonpos hs hg_deriv fun y hy0 _ => by
      have hpos : 0 ≤ Real.exp (-(y ^ 2 / 2)) := le_of_lt (Real.exp_pos _)
      have huy : u y ≤ 0 := hu_nonpos y (le_of_lt hy0)
      nlinarith
    have h0 : g 0 = 1 := by norm_num [g]
    linarith
  have hpos : 0 < Real.exp (s ^ 2 / 2) := Real.exp_pos _
  have hmul : g s * Real.exp (s ^ 2 / 2) ≤ 1 * Real.exp (s ^ 2 / 2) :=
    mul_le_mul_of_nonneg_right hg_le hpos.le
  dsimp only [g] at hmul
  rw [mul_right_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul, one_mul] at hmul
  exact hmul

/-- Sub-Gaussian tail bound for a Rademacher linear form over `Fin n → Bool`. -/
def signVal (b : Bool) : ℝ := if b then 1 else -1

lemma signVal_sq (b : Bool) : signVal b ^ 2 = 1 := by
  cases b <;> norm_num [signVal]

lemma sum_exp_rademacher (n : ℕ) (w : Fin n → ℝ) :
    ∑ σ : Fin n → Bool, Real.exp (∑ i : Fin n, signVal (σ i) * w i) ≤
      (2 : ℝ) ^ n * Real.exp ((∑ i : Fin n, w i ^ 2) / 2) := by
  have hfactor : ∑ σ : Fin n → Bool, Real.exp (∑ i : Fin n, signVal (σ i) * w i) =
      ∏ i : Fin n, (Real.exp (w i) + Real.exp (-w i)) := by
    have h1 : ∀ σ : Fin n → Bool, Real.exp (∑ i : Fin n, signVal (σ i) * w i) =
        ∏ i : Fin n, Real.exp (signVal (σ i) * w i) := fun σ => Real.exp_sum _ _
    simp_rw [h1]
    let f : Fin n → Bool → ℝ := fun i b => Real.exp (signVal b * w i)
    change ∑ σ : Fin n → Bool, ∏ i : Fin n, f i (σ i) = _
    rw [← Fintype.prod_sum f]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [f, signVal]
  rw [hfactor]
  have hbound : ∏ i : Fin n, (Real.exp (w i) + Real.exp (-w i)) ≤
      ∏ i : Fin n, (2 * Real.exp (w i ^ 2 / 2)) := by
    apply prod_le_prod_nonneg Finset.univ _ _ (fun i _ => by positivity)
    intro i _
    have := cosh_half_le_exp_sq_half (w i)
    linarith
  calc ∏ i : Fin n, (Real.exp (w i) + Real.exp (-w i))
      ≤ ∏ i : Fin n, (2 * Real.exp (w i ^ 2 / 2)) := hbound
    _ = (∏ _i : Fin n, (2 : ℝ)) * ∏ i : Fin n, Real.exp (w i ^ 2 / 2) := Finset.prod_mul_distrib
    _ = (2 : ℝ) ^ n * Real.exp (∑ i : Fin n, w i ^ 2 / 2) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_sum]
    _ = (2 : ℝ) ^ n * Real.exp ((∑ i : Fin n, w i ^ 2) / 2) := by
        rw [Finset.sum_div]

/-- Two-sided Hoeffding tail count for Rademacher vectors. -/
lemma rademacher_tail_count (n : ℕ) (v : Fin n → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hv : 0 < ∑ i : Fin n, v i ^ 2) :
    (((Finset.univ : Finset (Fin n → Bool)).filter
        (fun σ => t * Real.sqrt (∑ i : Fin n, v i ^ 2) ≤ |∑ i : Fin n, signVal (σ i) * v i|)).card : ℝ)
      ≤ 2 * (2 : ℝ) ^ n * Real.exp (-(t ^ 2 / 2)) := by
  set S := Real.sqrt (∑ i : Fin n, v i ^ 2)
  have hS_pos : 0 < S := Real.sqrt_pos.mpr hv
  have hS_sq : S ^ 2 = ∑ i : Fin n, v i ^ 2 := Real.sq_sqrt hv.le
  have hone_side : ∀ u : Fin n → ℝ, (∑ i : Fin n, u i ^ 2) = S ^ 2 →
      (((Finset.univ : Finset (Fin n → Bool)).filter
          (fun σ => t * S ≤ ∑ i : Fin n, signVal (σ i) * u i)).card : ℝ)
        ≤ (2 : ℝ) ^ n * Real.exp (-(t ^ 2 / 2)) := by
    intro u hu
    let lam : ℝ := t / S
    have hlam : 0 ≤ lam := div_nonneg ht hS_pos.le
    let w : Fin n → ℝ := fun i => lam * u i
    have hsum_w : ∑ i : Fin n, w i ^ 2 = t ^ 2 := by
      have : ∑ i : Fin n, w i ^ 2 = lam ^ 2 * ∑ i : Fin n, u i ^ 2 := by
        simp_rw [w, mul_pow, ← Finset.mul_sum]
      rw [this, hu]
      dsimp only [lam]
      field_simp [ne_of_gt hS_pos]
    have hmgf := sum_exp_rademacher n w
    rw [hsum_w] at hmgf
    let A := (Finset.univ : Finset (Fin n → Bool)).filter
      (fun σ => t * S ≤ ∑ i : Fin n, signVal (σ i) * u i)
    have hmarkov : (A.card : ℝ) * Real.exp (t ^ 2) ≤
        ∑ σ : Fin n → Bool, Real.exp (∑ i : Fin n, signVal (σ i) * w i) := by
      calc (A.card : ℝ) * Real.exp (t ^ 2)
          = ∑ _σ ∈ A, Real.exp (t ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ σ ∈ A, Real.exp (∑ i : Fin n, signVal (σ i) * w i) := by
            refine Finset.sum_le_sum fun σ hσ => ?_
            have hge : t * S ≤ ∑ i : Fin n, signVal (σ i) * u i := (Finset.mem_filter.mp hσ).2
            have heq : ∑ i : Fin n, signVal (σ i) * w i = lam * ∑ i : Fin n, signVal (σ i) * u i := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => by dsimp only [w]; ring
            rw [heq]
            apply Real.exp_le_exp.mpr
            have hmul := mul_le_mul_of_nonneg_left hge hlam
            have ht2 : lam * (t * S) = t ^ 2 := by
              dsimp only [lam]; field_simp [ne_of_gt hS_pos]
            linarith
        _ ≤ ∑ σ : Fin n → Bool, Real.exp (∑ i : Fin n, signVal (σ i) * w i) :=
            Finset.sum_le_univ_sum_of_nonneg (fun _ => (Real.exp_pos _).le)
    have hcomb : (A.card : ℝ) * Real.exp (t ^ 2) ≤ (2 : ℝ) ^ n * Real.exp (t ^ 2 / 2) :=
      hmarkov.trans hmgf
    have hexp_pos : 0 < Real.exp (t ^ 2) := Real.exp_pos _
    have hdiv := (le_div_iff₀ hexp_pos).mpr hcomb
    calc (A.card : ℝ) ≤ (2 : ℝ) ^ n * Real.exp (t ^ 2 / 2) / Real.exp (t ^ 2) := hdiv
      _ = (2 : ℝ) ^ n * Real.exp (-(t ^ 2 / 2)) := by
          rw [mul_div_assoc, ← Real.exp_sub]
          congr 2; ring
  have hpos := hone_side v hS_sq.symm
  have hneg := hone_side (fun i => -v i) (by simp [hS_sq])
  let Aall := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun σ => t * S ≤ |∑ i : Fin n, signVal (σ i) * v i|)
  let Apos := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun σ => t * S ≤ ∑ i : Fin n, signVal (σ i) * v i)
  let Aneg := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun σ => t * S ≤ ∑ i : Fin n, signVal (σ i) * (-v i))
  have hsub : Aall ⊆ Apos ∪ Aneg := by
    intro σ hσ
    have hge := (Finset.mem_filter.mp hσ).2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases le_abs.mp hge with h | h
    · exact Or.inl ⟨Finset.mem_univ _, h⟩
    · refine Or.inr ⟨Finset.mem_univ _, ?_⟩
      have : ∑ i : Fin n, signVal (σ i) * (-v i) = -(∑ i : Fin n, signVal (σ i) * v i) := by
        simp [Finset.sum_neg_distrib]
      linarith
  have hcard : (Aall.card : ℝ) ≤ (Apos.card : ℝ) + (Aneg.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  linarith

/-! ### Section 2: Finite Shannon entropy and Gibbs inequality -/

noncomputable def entTerm (p : ℝ) : ℝ :=
  if p ≤ 0 then 0 else p * (-Real.log p)

lemma entTerm_zero : entTerm 0 = 0 := by simp [entTerm]

lemma entTerm_le_gibbs {p w : ℝ} (hp : 0 ≤ p) (hw : 0 < w) :
    entTerm p ≤ p * (-Real.log w) + (w - p) := by
  by_cases hp0 : p ≤ 0
  · have hpeq : p = 0 := le_antisymm hp0 hp
    subst hpeq
    simp [entTerm, hw.le]
  · push Not at hp0
    simp only [entTerm, not_le.mpr hp0, ↓reduceIte]
    have hlog := Real.log_le_sub_one_of_pos (div_pos hw hp0)
    rw [Real.log_div hw.ne' hp0.ne'] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hp
    have hcancel : p * (w / p - 1) = w - p := by field_simp [hp0.ne']
    linarith

lemma entropy_le_cross {α : Type*} (s : Finset α) (p w : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hsum_p : ∑ a ∈ s, p a = 1)
    (hw : ∀ a ∈ s, 0 < w a) (hsum_w : ∑ a ∈ s, w a ≤ 1) :
    ∑ a ∈ s, entTerm (p a) ≤ ∑ a ∈ s, p a * (-Real.log (w a)) := by
  have h1 : ∑ a ∈ s, entTerm (p a) ≤ ∑ a ∈ s, (p a * (-Real.log (w a)) + (w a - p a)) :=
    Finset.sum_le_sum fun a ha => entTerm_le_gibbs (hp a ha) (hw a ha)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum_p] at h1
  linarith

/-- Subadditivity of finite Shannon entropy for a family of bucket maps `b : Fin m → Ω → ℤ`. -/
lemma entropy_tuple_le_sum {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (hΩ : 0 < Fintype.card Ω)
    (m : ℕ) (b : Fin m → Ω → ℤ) :
    let N : ℝ := Fintype.card Ω
    let img := (Finset.univ : Finset Ω).image (fun ω => fun j : Fin m => b j ω)
    let pTuple (y : Fin m → ℤ) : ℝ :=
      (((Finset.univ : Finset Ω).filter (fun ω => (fun j => b j ω) = y)).card : ℝ) / N
    let imgJ (j : Fin m) := (Finset.univ : Finset Ω).image (b j)
    let pJ (j : Fin m) (z : ℤ) : ℝ :=
      (((Finset.univ : Finset Ω).filter (fun ω => b j ω = z)).card : ℝ) / N
    ∑ y ∈ img, entTerm (pTuple y) ≤ ∑ j : Fin m, ∑ z ∈ imgJ j, entTerm (pJ j z) := by
  intro N img pTuple imgJ pJ
  have hN_pos : 0 < N := by dsimp only [N]; exact_mod_cast hΩ
  have hpTuple_nonneg : ∀ y ∈ img, 0 ≤ pTuple y := fun y _ => by dsimp [pTuple]; positivity
  have hpTuple_sum : ∑ y ∈ img, pTuple y = 1 := by
    dsimp only [pTuple]
    rw [← Finset.sum_div]
    have hcard : ∑ y ∈ img, ((Finset.univ : Finset Ω).filter (fun ω => (fun j => b j ω) = y)).card =
        Fintype.card Ω := by
      have := Finset.card_eq_sum_card_fiberwise (f := fun ω : Ω => fun j : Fin m => b j ω)
        (s := Finset.univ) (t := img) (fun ω _ => Finset.mem_image_of_mem _ (Finset.mem_univ _))
      simpa using this.symm
    have hcast : (∑ y ∈ img, (((Finset.univ : Finset Ω).filter (fun ω => (fun j => b j ω) = y)).card : ℝ)) = N := by
      dsimp only [N]; exact_mod_cast hcard
    rw [hcast, div_self hN_pos.ne']
  -- Product distribution `q y = ∏ j, pJ j (y j)` is positive on `img` and sums to ≤ 1.
  let q : (Fin m → ℤ) → ℝ := fun y => ∏ j : Fin m, pJ j (y j)
  have hq_pos : ∀ y ∈ img, 0 < q y := by
    intro y hy
    obtain ⟨ω, _, rfl⟩ := Finset.mem_image.mp hy
    dsimp only [q]
    refine Finset.prod_pos fun j _ => ?_
    dsimp only [pJ]
    apply div_pos _ hN_pos
    have hmem : ω ∈ (Finset.univ : Finset Ω).filter (fun ω' => b j ω' = b j ω) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hcpos : 0 < ((Finset.univ : Finset Ω).filter (fun ω' => b j ω' = b j ω)).card :=
      Finset.card_pos.mpr ⟨ω, hmem⟩
    exact_mod_cast hcpos
  have hpJ_sum : ∀ j : Fin m, ∑ z ∈ imgJ j, pJ j z = 1 := by
    intro j
    dsimp only [pJ]
    rw [← Finset.sum_div]
    have hcard : ∑ z ∈ imgJ j, ((Finset.univ : Finset Ω).filter (fun ω => b j ω = z)).card =
        Fintype.card Ω := by
      have := Finset.card_eq_sum_card_fiberwise (f := b j) (s := Finset.univ) (t := imgJ j)
        (fun ω _ => Finset.mem_image_of_mem _ (Finset.mem_univ _))
      simpa using this.symm
    have hcast : (∑ z ∈ imgJ j, (((Finset.univ : Finset Ω).filter (fun ω => b j ω = z)).card : ℝ)) = N := by
      dsimp only [N]; exact_mod_cast hcard
    rw [hcast, div_self hN_pos.ne']
  have hq_sum : ∑ y ∈ img, q y ≤ 1 := by
    let box : Finset (Fin m → ℤ) := Fintype.piFinset imgJ
    have hsub : img ⊆ box := by
      intro y hy
      obtain ⟨ω, _, rfl⟩ := Finset.mem_image.mp hy
      exact Fintype.mem_piFinset.mpr fun j => Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hbox : ∑ y ∈ box, q y = 1 := by
      dsimp only [box, q]
      have hbij : ∑ y ∈ Fintype.piFinset imgJ, ∏ j : Fin m, pJ j (y j) =
          ∑ y : (j : Fin m) → {z // z ∈ imgJ j}, ∏ j : Fin m, pJ j (y j).1 := by
        refine Finset.sum_bij (fun y hy j => ⟨y j, (Fintype.mem_piFinset.mp hy) j⟩)
          (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
        · intro y₁ _ y₂ _ hEq
          funext j
          exact congrArg Subtype.val (congrFun hEq j)
        · intro y _
          refine ⟨fun j => (y j).1, Fintype.mem_piFinset.mpr fun j => (y j).2, ?_⟩
          funext j; rfl
      rw [hbij]
      let f : (j : Fin m) → {z // z ∈ imgJ j} → ℝ := fun j z => pJ j z.1
      change ∑ y : (j : Fin m) → {z // z ∈ imgJ j}, ∏ j : Fin m, f j (y j) = 1
      rw [← Fintype.prod_sum f]
      refine Finset.prod_eq_one fun j _ => ?_
      dsimp only [f]
      rw [Finset.univ_eq_attach]
      simpa [Finset.sum_attach] using hpJ_sum j
    calc ∑ y ∈ img, q y ≤ ∑ y ∈ box, q y :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun y _ _ =>
            Finset.prod_nonneg fun j _ => by dsimp [pJ]; positivity
      _ = 1 := hbox
  have hgibbs := entropy_le_cross img pTuple q hpTuple_nonneg hpTuple_sum hq_pos hq_sum
  -- Expand `-log (q y) = ∑ j, -log (pJ j (y j))` and collect fibers per `j`.
  have hexpand : ∑ y ∈ img, pTuple y * (-Real.log (q y)) =
      ∑ j : Fin m, ∑ z ∈ imgJ j, entTerm (pJ j z) := by
    have hlog : ∀ y ∈ img, -Real.log (q y) = ∑ j : Fin m, (-Real.log (pJ j (y j))) := by
      intro y hy
      obtain ⟨ω, _, rfl⟩ := Finset.mem_image.mp hy
      dsimp only [q]
      rw [Real.log_prod (fun j _ => by
        dsimp only [pJ]
        apply ne_of_gt
        apply div_pos _ hN_pos
        have hcpos : 0 < ((Finset.univ : Finset Ω).filter (fun ω' => b j ω' = b j ω)).card :=
          Finset.card_pos.mpr ⟨ω, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
        exact_mod_cast hcpos)]
      rw [← Finset.sum_neg_distrib]
    calc ∑ y ∈ img, pTuple y * (-Real.log (q y))
        = ∑ y ∈ img, ∑ j : Fin m, pTuple y * (-Real.log (pJ j (y j))) := by
          refine Finset.sum_congr rfl fun y hy => ?_
          rw [hlog y hy, Finset.mul_sum]
      _ = ∑ j : Fin m, ∑ y ∈ img, pTuple y * (-Real.log (pJ j (y j))) := Finset.sum_comm
      _ = ∑ j : Fin m, ∑ z ∈ imgJ j, entTerm (pJ j z) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          -- Group `y ∈ img` by `y j = z`.
          have hfiber : ∑ y ∈ img, pTuple y * (-Real.log (pJ j (y j))) =
              ∑ z ∈ imgJ j, (∑ y ∈ img.filter (fun y => y j = z), pTuple y) * (-Real.log (pJ j z)) := by
            rw [← Finset.sum_fiberwise_of_maps_to (g := fun y : Fin m → ℤ => y j) (t := imgJ j)
              (fun y hy => by
                obtain ⟨ω, _, rfl⟩ := Finset.mem_image.mp hy
                exact Finset.mem_image_of_mem _ (Finset.mem_univ _))]
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun y hy => by rw [(Finset.mem_filter.mp hy).2]
          rw [hfiber]
          refine Finset.sum_congr rfl fun z hz => ?_
          have hmarg : ∑ y ∈ img.filter (fun y => y j = z), pTuple y = pJ j z := by
            dsimp only [pTuple, pJ]
            rw [← Finset.sum_div]
            congr 1
            have hcard : ∑ y ∈ img.filter (fun y => y j = z),
                ((Finset.univ : Finset Ω).filter (fun ω => (fun k => b k ω) = y)).card =
                ((Finset.univ : Finset Ω).filter (fun ω => b j ω = z)).card := by
              have h1 := Finset.card_eq_sum_card_fiberwise
                (f := fun ω : Ω => fun k : Fin m => b k ω)
                (s := (Finset.univ : Finset Ω).filter (fun ω => b j ω = z))
                (t := img.filter (fun y => y j = z))
                (fun ω hω => Finset.mem_filter.mpr
                  ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (Finset.mem_filter.mp hω).2⟩)
              rw [h1]
              refine Finset.sum_congr rfl fun y hy => ?_
              congr 1
              ext ω
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨fun hEq =>
                ⟨by have := congrFun hEq j; rw [this, (Finset.mem_filter.mp hy).2], hEq⟩,
                fun h => h.2⟩
            exact_mod_cast hcard
          rw [hmarg]
          obtain ⟨ω, _, rfl⟩ := Finset.mem_image.mp hz
          have hppos : 0 < pJ j (b j ω) := by
            dsimp only [pJ]
            apply div_pos _ hN_pos
            have hcpos : 0 < ((Finset.univ : Finset Ω).filter (fun ω' => b j ω' = b j ω)).card :=
              Finset.card_pos.mpr ⟨ω, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
            exact_mod_cast hcpos
          simp [entTerm, not_le.mpr hppos]
  linarith

/-! ### Section 3: Entropy bound for a single quantized Rademacher linear form -/

lemma sum_inv_two_pow_le (R : ℕ) : ∑ r ∈ Finset.range R, ((1 : ℝ) / 2) ^ r ≤ 2 := by
  induction R with
  | zero => simp
  | succ R ih =>
    have hgeom : ∑ r ∈ Finset.range (R + 1), ((1 : ℝ) / 2) ^ r =
        2 - 2 * ((1 : ℝ) / 2) ^ (R + 1) := by
      clear ih
      induction R with
      | zero => norm_num
      | succ k ihk =>
        rw [Finset.sum_range_succ, ihk, pow_succ]
        ring
    rw [hgeom]
    have : 0 ≤ ((1 : ℝ) / 2) ^ (R + 1) := by positivity
    linarith

lemma sum_nat_mul_inv_two_pow_le (R : ℕ) :
    ∑ r ∈ Finset.range R, (r : ℝ) * ((1 : ℝ) / 2) ^ r ≤ 2 := by
  cases R with
  | zero => norm_num
  | succ k =>
    have hexact : ∀ m : ℕ, ∑ r ∈ Finset.range (m + 1), (r : ℝ) * ((1 : ℝ) / 2) ^ r =
        2 - ((m : ℝ) + 2) * ((1 : ℝ) / 2) ^ m := by
      intro m
      induction m with
      | zero => norm_num
      | succ m ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        push_cast; ring
    rw [hexact k]
    have : 0 ≤ ((k : ℝ) + 2) * ((1 : ℝ) / 2) ^ k := by positivity
    linarith

lemma bucket_entropy_le (n : ℕ) (v : Fin n → ℝ) (c : ℝ) (hc : 2 ≤ c) :
    let normv := Real.sqrt (∑ i : Fin n, v i ^ 2)
    let b : (Fin n → Bool) → ℤ := fun σ =>
      if normv = 0 then 0
      else ⌊(∑ i : Fin n, signVal (σ i) * v i) / (2 * c * normv) + 1 / 2⌋
    let img := (Finset.univ : Finset (Fin n → Bool)).image b
    let p (z : ℤ) : ℝ :=
      (((Finset.univ : Finset (Fin n → Bool)).filter (fun σ => b σ = z)).card : ℝ) / (2 : ℝ) ^ n
    ∑ z ∈ img, entTerm (p z) ≤ 28 * Real.exp (-(c ^ 2 / 4)) := by
  intro normv b img p
  by_cases hnorm : normv = 0
  · have hb0 : ∀ σ : Fin n → Bool, b σ = 0 := fun σ => by simp [b, hnorm]
    have himg : img ⊆ {0} := by
      intro z hz
      obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hz
      simp [hb0]
    have hsum0 : ∑ z ∈ img, entTerm (p z) ≤ entTerm (p 0) := by
      calc ∑ z ∈ img, entTerm (p z)
          ≤ ∑ z ∈ ({0} : Finset ℤ), entTerm (p z) :=
            Finset.sum_le_sum_of_subset_of_nonneg himg fun z _ _ => by
              dsimp only [entTerm]
              split_ifs with h
              · exact le_rfl
              · push Not at h
                have hp1 : p z ≤ 1 := by
                  dsimp only [p]
                  rw [div_le_one (by positivity)]
                  have hle := Finset.card_le_univ
                    ((Finset.univ : Finset (Fin n → Bool)).filter (fun σ => b σ = z))
                  simpa [Fintype.card_pi, Fintype.card_bool] using
                    (Nat.cast_le (α := ℝ)).mpr hle
                have hlog : Real.log (p z) ≤ 0 := Real.log_nonpos h.le hp1
                nlinarith
        _ = entTerm (p 0) := by simp
    have hp0 : p 0 = 1 := by
      dsimp only [p]
      have hfilt : (Finset.univ : Finset (Fin n → Bool)).filter (fun σ => b σ = 0) = Finset.univ := by
        ext σ; simp [hb0]
      rw [hfilt, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      simp
    rw [hp0] at hsum0
    have hent1 : entTerm 1 = 0 := by simp [entTerm]
    rw [hent1] at hsum0
    have : 0 ≤ 28 * Real.exp (-(c ^ 2 / 4)) := by positivity
    linarith
  · have hv_nonneg : 0 ≤ ∑ i : Fin n, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hv_pos : 0 < ∑ i : Fin n, v i ^ 2 := by
      rcases eq_or_lt_of_le hv_nonneg with h | h
      · exfalso; apply hnorm; simp [normv, ← h]
      · exact h
    have hnorm_pos : 0 < normv := Real.sqrt_pos.mpr hv_pos
    have hc_pos : 0 < c := by linarith
    -- Comparison distribution `w`: `w 0 = 1 - θ`, `w k = (θ / 4) * (1/2)^(|k|-1)` for `k ≠ 0`.
    let θ : ℝ := Real.exp (-(c ^ 2 / 4))
    have hθ_pos : 0 < θ := Real.exp_pos _
    have hθ_le : θ ≤ 1 / 2 := by
      have h1 : -(c ^ 2 / 4) ≤ -1 := by nlinarith
      have h2 : Real.exp (-(c ^ 2 / 4)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr h1
      have h3 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
      have h4 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, one_div]
        exact inv_anti₀ (by norm_num) h3
      exact h2.trans h4
    let w : ℤ → ℝ := fun k =>
      if k = 0 then 1 - θ else (θ / 4) * ((1 : ℝ) / 2) ^ (k.natAbs - 1)
    have hw_pos : ∀ k ∈ img, 0 < w k := by
      intro k _
      dsimp only [w]
      split_ifs
      · linarith
      · positivity
    have hsum_w : ∑ k ∈ img, w k ≤ 1 := by
      -- Bound by finite symmetric range `Icc (-R) R`.
      obtain ⟨R, hR⟩ : ∃ R : ℕ, ∀ k ∈ img, k.natAbs ≤ R := by
        refine ⟨img.sup Int.natAbs, fun k hk => Finset.le_sup (f := Int.natAbs) hk⟩
      let S_box : Finset ℤ := Finset.Icc (-(R : ℤ)) (R : ℤ)
      have hsub : img ⊆ S_box := by
        intro k hk
        rw [Finset.mem_Icc]
        have hle := hR k hk
        omega
      have hbox_le : ∑ k ∈ S_box, w k ≤ 1 := by
        have h0mem : (0 : ℤ) ∈ S_box := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        rw [← Finset.add_sum_erase _ _ h0mem]
        have hw0 : w 0 = 1 - θ := by simp [w]
        rw [hw0]
        -- Partition `S_box.erase 0` into positive `{1..R}` and negative `{-R..-1}`.
        let posSet : Finset ℤ := (Finset.range R).image (fun r : ℕ => (r : ℤ) + 1)
        let negSet : Finset ℤ := (Finset.range R).image (fun r : ℕ => -((r : ℤ) + 1))
        have hpart : S_box.erase 0 = posSet ∪ negSet := by
          ext k
          simp only [Finset.mem_erase, S_box, Finset.mem_Icc, Finset.mem_union,
            posSet, negSet, Finset.mem_image, Finset.mem_range]
          constructor
          · rintro ⟨hk0, hlo, hhi⟩
            by_cases hpos : 0 < k
            · exact Or.inl ⟨(k - 1).toNat, by omega, by omega⟩
            · exact Or.inr ⟨(-k - 1).toNat, by omega, by omega⟩
          · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) <;> omega
        have hdisj : Disjoint posSet negSet := by
          rw [Finset.disjoint_left]
          intro k h1 h2
          obtain ⟨r1, _, rfl⟩ := Finset.mem_image.mp h1
          obtain ⟨r2, _, hEq⟩ := Finset.mem_image.mp h2
          omega
        rw [hpart, Finset.sum_union hdisj]
        have hpos_sum : ∑ k ∈ posSet, w k = (θ / 4) * ∑ r ∈ Finset.range R, ((1 : ℝ) / 2) ^ r := by
          rw [Finset.sum_image (fun a _ b _ h => by omega), Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          have hne : (r : ℤ) + 1 ≠ 0 := by omega
          have habs : ((r : ℤ) + 1).natAbs - 1 = r := by omega
          dsimp only [w]; rw [ite_eq_right hne, habs]
        have hneg_sum : ∑ k ∈ negSet, w k = (θ / 4) * ∑ r ∈ Finset.range R, ((1 : ℝ) / 2) ^ r := by
          rw [Finset.sum_image (fun a _ b _ h => by omega), Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          have hne : -((r : ℤ) + 1) ≠ 0 := by omega
          have habs : (-((r : ℤ) + 1)).natAbs - 1 = r := by omega
          dsimp only [w]; rw [ite_eq_right hne, habs]
        rw [hpos_sum, hneg_sum]
        have hgeom := sum_inv_two_pow_le R
        nlinarith
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by
        dsimp only [w]; split_ifs
        · linarith
        · positivity).trans hbox_le
    have hp_nonneg : ∀ k ∈ img, 0 ≤ p k := fun k _ =>
      div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
    have hp_sum : ∑ k ∈ img, p k = 1 := by
      dsimp only [p]
      rw [← Finset.sum_div]
      have hcard : ∑ k ∈ img, ((Finset.univ : Finset (Fin n → Bool)).filter (fun σ => b σ = k)).card =
          2 ^ n := by
        have h1 := Finset.card_eq_sum_card_fiberwise (f := b) (s := Finset.univ) (t := img)
          (fun σ _ => Finset.mem_image_of_mem _ (Finset.mem_univ _))
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h1
        exact h1.symm
      have hcast : (∑ k ∈ img, (((Finset.univ : Finset (Fin n → Bool)).filter (fun σ => b σ = k)).card : ℝ)) =
          (2 : ℝ) ^ n := by exact_mod_cast hcard
      rw [hcast, div_self (by positivity)]
    have hgibbs := entropy_le_cross img p w hp_nonneg hp_sum hw_pos hsum_w
    -- Pointwise tail bound on `p k` for `k ≠ 0`.
    have hp_tail : ∀ k : ℤ, k ≠ 0 →
        p k ≤ 2 * Real.exp (-(c ^ 2 / 2)) * ((1 : ℝ) / 2) ^ (k.natAbs - 1) := by
      intro k hk0
      set r : ℕ := k.natAbs - 1
      have hkabs : k.natAbs = r + 1 := by omega
      let t : ℝ := (2 * (r : ℝ) + 1) * c
      have ht_nonneg : 0 ≤ t := by positivity
      have hsub : (Finset.univ : Finset (Fin n → Bool)).filter (fun σ => b σ = k) ⊆
          (Finset.univ : Finset (Fin n → Bool)).filter
            (fun σ => t * normv ≤ |∑ i : Fin n, signVal (σ i) * v i|) := by
        intro σ hσ
        have hbEq : b σ = k := (Finset.mem_filter.mp hσ).2
        simp only [b, hnorm, ↓reduceIte] at hbEq
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        set X := ∑ i : Fin n, signVal (σ i) * v i
        have hfl_lo : (k : ℝ) ≤ X / (2 * c * normv) + 1 / 2 := by
          rw [← hbEq]; exact Int.floor_le _
        have hfl_hi : X / (2 * c * normv) + 1 / 2 < (k : ℝ) + 1 := by
          rw [← hbEq]; exact Int.lt_floor_add_one _
        have hden : 0 < 2 * c * normv := by positivity
        by_cases hkpos : 0 < k
        · have hkcast : (k : ℝ) = (r : ℝ) + 1 := by exact_mod_cast (show k = (r : ℤ) + 1 by omega)
          have h1 : (r : ℝ) + 1 / 2 ≤ X / (2 * c * normv) := by linarith
          have h2 : ((r : ℝ) + 1 / 2) * (2 * c * normv) ≤ X := (le_div_iff₀ hden).mp h1
          have h3 : t * normv ≤ X := by dsimp only [t]; linarith
          exact h3.trans (le_abs_self X)
        · have hkcast : (k : ℝ) = -((r : ℝ) + 1) := by exact_mod_cast (show k = -((r : ℤ) + 1) by omega)
          have h1 : X / (2 * c * normv) ≤ -((r : ℝ) + 1 / 2) := by linarith
          have h2 : X ≤ -((r : ℝ) + 1 / 2) * (2 * c * normv) := (div_le_iff₀ hden).mp h1
          have h3 : t * normv ≤ -X := by dsimp only [t]; linarith
          exact h3.trans (neg_le_abs X)
      have hcnt := rademacher_tail_count n v t ht_nonneg hv_pos
      have hple : p k ≤ 2 * Real.exp (-(t ^ 2 / 2)) := by
        dsimp only [p]
        have hcle : (((Finset.univ : Finset (Fin n → Bool)).filter (fun σ => b σ = k)).card : ℝ) ≤
            2 * (2 : ℝ) ^ n * Real.exp (-(t ^ 2 / 2)) :=
          ((Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)).trans hcnt
        rw [div_le_iff₀ (by positivity)]
        linarith
      -- Bound `exp (-(t^2/2)) ≤ exp (-(c^2/2)) * (1/2)^r`.
      have htsq : c ^ 2 / 2 + 2 * (r : ℝ) ≤ t ^ 2 / 2 := by
        have h1 : (1 : ℝ) + 4 * (r : ℝ) ≤ (2 * (r : ℝ) + 1) ^ 2 := by nlinarith
        have h2 : 4 ≤ c ^ 2 := by nlinarith
        dsimp only [t]
        nlinarith [sq_nonneg (r : ℝ)]
      have h2r : Real.exp (-(2 * (r : ℝ))) ≤ ((1 : ℝ) / 2) ^ r := by
        have hbase : Real.exp (-2) ≤ (1 : ℝ) / 2 := by
          have h3 : (2 : ℝ) ≤ Real.exp 2 := by
            have := Real.add_one_le_exp (2 : ℝ); linarith
          rw [Real.exp_neg, one_div]
          exact inv_anti₀ (by norm_num) h3
        calc Real.exp (-(2 * (r : ℝ))) = Real.exp ((r : ℝ) * (-2)) := by congr 1; ring
          _ = (Real.exp (-2)) ^ r := by rw [Real.exp_nat_mul]
          _ ≤ ((1 : ℝ) / 2) ^ r := pow_le_pow_left₀ (Real.exp_pos _).le hbase r
      calc p k ≤ 2 * Real.exp (-(t ^ 2 / 2)) := hple
        _ ≤ 2 * Real.exp (-(c ^ 2 / 2 + 2 * (r : ℝ))) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
        _ = 2 * Real.exp (-(c ^ 2 / 2)) * Real.exp (-(2 * (r : ℝ))) := by
            rw [neg_add, Real.exp_add, mul_assoc]
        _ ≤ 2 * Real.exp (-(c ^ 2 / 2)) * ((1 : ℝ) / 2) ^ r :=
            mul_le_mul_of_nonneg_left h2r (by positivity)
    -- Bound the Gibbs RHS `∑ k ∈ img, p k * (-log (w k))`.
    have hlog_w0 : -Real.log (1 - θ) ≤ 2 * θ := by
      have h1 : 0 < 1 - θ := by linarith
      have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
      rw [Real.log_inv] at h2
      have h3 : (1 - θ)⁻¹ - 1 ≤ 2 * θ := by
        have : (1 - θ) * ((1 - θ)⁻¹ - 1) ≤ (1 - θ) * (2 * θ) := by
          rw [mul_sub, mul_inv_cancel₀ h1.ne', mul_one]
          nlinarith
        exact le_of_mul_le_mul_left this h1
      linarith
    have hlog_wk : ∀ k : ℤ, k ≠ 0 →
        -Real.log (w k) = (Real.log 4 + c ^ 2 / 4) + ((k.natAbs - 1 : ℕ) : ℝ) * Real.log 2 := by
      intro k hk0
      dsimp only [w]
      rw [ite_eq_right hk0, Real.log_mul (by positivity) (by positivity),
        Real.log_div hθ_pos.ne' (by norm_num), Real.log_pow,
        one_div, Real.log_inv]
      dsimp only [θ]
      rw [Real.log_exp]
      ring
    -- Split `img` into `0` and `img.erase 0`.
    have hsplit : ∑ k ∈ img, p k * (-Real.log (w k)) ≤
        2 * θ + ∑ k ∈ img.erase 0, p k * (-Real.log (w k)) := by
      by_cases h0 : (0 : ℤ) ∈ img
      · rw [← Finset.add_sum_erase _ _ h0]
        have hp0le1 : p 0 ≤ 1 := by
          calc p 0 ≤ ∑ k ∈ img, p k := Finset.single_le_sum hp_nonneg h0
            _ = 1 := hp_sum
        have hw0eq : w 0 = 1 - θ := by simp [w]
        rw [hw0eq]
        have hterm0 : p 0 * (-Real.log (1 - θ)) ≤ 2 * θ := by
          calc p 0 * (-Real.log (1 - θ)) ≤ 1 * (2 * θ) :=
                mul_le_mul hp0le1 hlog_w0 (by
                  have : Real.log (1 - θ) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
                  linarith) (by norm_num)
            _ = 2 * θ := one_mul _
        linarith
      · rw [Finset.erase_eq_of_notMem h0]
        linarith [hθ_pos]
    -- Bound sums over `img.erase 0` using `R`.
    obtain ⟨R, hR⟩ : ∃ R : ℕ, ∀ k ∈ img, k.natAbs ≤ R :=
      ⟨img.sup Int.natAbs, fun k hk => Finset.le_sup (f := Int.natAbs) hk⟩
    have hsum_tail_1 : ∑ k ∈ img.erase 0, p k ≤ 8 * Real.exp (-(c ^ 2 / 2)) := by
      let posSet : Finset ℤ := (Finset.range R).image (fun r : ℕ => (r : ℤ) + 1)
      let negSet : Finset ℤ := (Finset.range R).image (fun r : ℕ => -((r : ℤ) + 1))
      have hsub : img.erase 0 ⊆ posSet ∪ negSet := by
        intro k hk
        have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
        have hkle := hR k (Finset.mem_erase.mp hk).2
        simp only [Finset.mem_union, posSet, negSet, Finset.mem_image, Finset.mem_range]
        by_cases hpos : 0 < k
        · exact Or.inl ⟨(k - 1).toNat, by omega, by omega⟩
        · exact Or.inr ⟨(-k - 1).toNat, by omega, by omega⟩
      have hdisj : Disjoint posSet negSet := by
        rw [Finset.disjoint_left]
        intro k h1 h2
        obtain ⟨r1, _, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨r2, _, hEq⟩ := Finset.mem_image.mp h2
        omega
      calc ∑ k ∈ img.erase 0, p k
          ≤ ∑ k ∈ img.erase 0, (2 * Real.exp (-(c ^ 2 / 2)) * ((1 : ℝ) / 2) ^ (k.natAbs - 1)) :=
            Finset.sum_le_sum fun k hk => hp_tail k (Finset.mem_erase.mp hk).1
        _ ≤ ∑ k ∈ posSet ∪ negSet, (2 * Real.exp (-(c ^ 2 / 2)) * ((1 : ℝ) / 2) ^ (k.natAbs - 1)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ = 2 * (2 * Real.exp (-(c ^ 2 / 2)) * ∑ r ∈ Finset.range R, ((1 : ℝ) / 2) ^ r) := by
            rw [Finset.sum_union hdisj,
              Finset.sum_image (fun a _ b _ h => by omega),
              Finset.sum_image (fun a _ b _ h => by omega)]
            have h1 : ∀ r : ℕ, ((r : ℤ) + 1).natAbs - 1 = r := fun r => by omega
            have h2 : ∀ r : ℕ, (-((r : ℤ) + 1)).natAbs - 1 = r := fun r => by omega
            simp_rw [h1, h2, ← Finset.mul_sum]; ring
        _ ≤ 8 * Real.exp (-(c ^ 2 / 2)) := by
            have := sum_inv_two_pow_le R
            nlinarith [Real.exp_pos (-(c ^ 2 / 2))]
    have hsum_tail_2 : ∑ k ∈ img.erase 0, p k * ((k.natAbs - 1 : ℕ) : ℝ) ≤
        8 * Real.exp (-(c ^ 2 / 2)) := by
      let posSet : Finset ℤ := (Finset.range R).image (fun r : ℕ => (r : ℤ) + 1)
      let negSet : Finset ℤ := (Finset.range R).image (fun r : ℕ => -((r : ℤ) + 1))
      have hsub : img.erase 0 ⊆ posSet ∪ negSet := by
        intro k hk
        have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
        have hkle := hR k (Finset.mem_erase.mp hk).2
        simp only [Finset.mem_union, posSet, negSet, Finset.mem_image, Finset.mem_range]
        by_cases hpos : 0 < k
        · exact Or.inl ⟨(k - 1).toNat, by omega, by omega⟩
        · exact Or.inr ⟨(-k - 1).toNat, by omega, by omega⟩
      have hdisj : Disjoint posSet negSet := by
        rw [Finset.disjoint_left]
        intro k h1 h2
        obtain ⟨r1, _, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨r2, _, hEq⟩ := Finset.mem_image.mp h2
        omega
      calc ∑ k ∈ img.erase 0, p k * ((k.natAbs - 1 : ℕ) : ℝ)
          ≤ ∑ k ∈ img.erase 0, (2 * Real.exp (-(c ^ 2 / 2)) *
              (((k.natAbs - 1 : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (k.natAbs - 1))) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have := hp_tail k (Finset.mem_erase.mp hk).1
            have hnn : (0 : ℝ) ≤ ((k.natAbs - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
            nlinarith
        _ ≤ ∑ k ∈ posSet ∪ negSet, (2 * Real.exp (-(c ^ 2 / 2)) *
              (((k.natAbs - 1 : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (k.natAbs - 1))) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ = 2 * (2 * Real.exp (-(c ^ 2 / 2)) * ∑ r ∈ Finset.range R, (r : ℝ) * ((1 : ℝ) / 2) ^ r) := by
            rw [Finset.sum_union hdisj,
              Finset.sum_image (fun a _ b _ h => by omega),
              Finset.sum_image (fun a _ b _ h => by omega)]
            have h1 : ∀ r : ℕ, ((r : ℤ) + 1).natAbs - 1 = r := fun r => by omega
            have h2 : ∀ r : ℕ, (-((r : ℤ) + 1)).natAbs - 1 = r := fun r => by omega
            simp_rw [h1, h2, ← Finset.mul_sum]; ring
        _ ≤ 8 * Real.exp (-(c ^ 2 / 2)) := by
            have := sum_nat_mul_inv_two_pow_le R
            nlinarith [Real.exp_pos (-(c ^ 2 / 2))]
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hlog4 : Real.log 4 ≤ 2 := by
      have : Real.log 4 = Real.log (2 * 2) := by norm_num
      rw [this, Real.log_mul (by norm_num) (by norm_num)]; linarith
    have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog4_nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hxex : (c ^ 2 / 4) * Real.exp (-(c ^ 2 / 4)) ≤ 1 := by
      have h1 : c ^ 2 / 4 + 1 ≤ Real.exp (c ^ 2 / 4) := Real.add_one_le_exp _
      have h2 : c ^ 2 / 4 ≤ Real.exp (c ^ 2 / 4) := by linarith
      have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-(c ^ 2 / 4))).le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h3
      exact h3
    have hθsq : Real.exp (-(c ^ 2 / 2)) = θ * θ := by
      dsimp only [θ]; rw [← Real.exp_add]; congr 1; ring
    have htail_sum : ∑ k ∈ img.erase 0, p k * (-Real.log (w k)) ≤ 26 * θ := by
      have hrw : ∑ k ∈ img.erase 0, p k * (-Real.log (w k)) =
          (Real.log 4 + c ^ 2 / 4) * (∑ k ∈ img.erase 0, p k) +
          Real.log 2 * (∑ k ∈ img.erase 0, p k * ((k.natAbs - 1 : ℕ) : ℝ)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hlog_wk k (Finset.mem_erase.mp hk).1]; ring
      rw [hrw]
      have h1 : (Real.log 4 + c ^ 2 / 4) * (∑ k ∈ img.erase 0, p k) ≤
          (Real.log 4 + c ^ 2 / 4) * (8 * Real.exp (-(c ^ 2 / 2))) :=
        mul_le_mul_of_nonneg_left hsum_tail_1 (by positivity)
      have h2 : Real.log 2 * (∑ k ∈ img.erase 0, p k * ((k.natAbs - 1 : ℕ) : ℝ)) ≤
          Real.log 2 * (8 * Real.exp (-(c ^ 2 / 2))) :=
        mul_le_mul_of_nonneg_left hsum_tail_2 hlog2_nn
      rw [hθsq] at h1 h2
      have h3 : (Real.log 4 + c ^ 2 / 4) * (8 * (θ * θ)) ≤ 16 * θ := by
        have ha : Real.log 4 * (8 * (θ * θ)) ≤ 8 * θ := by nlinarith
        have hb : (c ^ 2 / 4) * (8 * (θ * θ)) = 8 * ((c ^ 2 / 4) * θ) * θ := by ring
        have hc' : 8 * ((c ^ 2 / 4) * θ) * θ ≤ 8 * θ := by nlinarith [hxex]
        linarith
      have h4 : Real.log 2 * (8 * (θ * θ)) ≤ 4 * θ := by nlinarith
      linarith
    linarith

/-! ### Section 4: Hamming ball count and Spencer's three-valued coloring lemma -/

lemma hamming_ball_card_lt (n : ℕ) (hn : 1 ≤ n) (σ₀ : Fin n → Bool) :
    (((Finset.univ : Finset (Fin n → Bool)).filter
        (fun τ => 10 * ((Finset.univ : Finset (Fin n)).filter (fun i => τ i ≠ σ₀ i)).card < n)).card : ℝ)
      < (2 : ℝ) ^ n * Real.exp (-(n : ℝ) / 10) := by
  let d : (Fin n → Bool) → ℕ := fun τ =>
    ((Finset.univ : Finset (Fin n)).filter (fun i => τ i ≠ σ₀ i)).card
  let B := (Finset.univ : Finset (Fin n → Bool)).filter (fun τ => 10 * d τ < n)
  -- Compare each `τ ∈ B` against `3^(n/10 - d τ)`.
  have h1 : (B.card : ℝ) < ∑ τ : Fin n → Bool, (3 : ℝ) ^ ((n : ℝ) / 10) * ((1 : ℝ) / 3) ^ (d τ) := by
    have hlt_each : ∀ τ ∈ B, (1 : ℝ) < (3 : ℝ) ^ ((n : ℝ) / 10) * ((1 : ℝ) / 3) ^ (d τ) := by
      intro τ hτ
      have hdlt : 10 * d τ < n := (Finset.mem_filter.mp hτ).2
      have hexp_pos : (0 : ℝ) < (n : ℝ) / 10 - (d τ : ℝ) := by
        have : (10 : ℝ) * (d τ : ℝ) < (n : ℝ) := by exact_mod_cast hdlt
        linarith
      have hrw : (3 : ℝ) ^ ((n : ℝ) / 10) * ((1 : ℝ) / 3) ^ (d τ) =
          (3 : ℝ) ^ ((n : ℝ) / 10 - (d τ : ℝ)) := by
        rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3), Real.rpow_natCast,
          one_div, inv_pow, ← div_eq_mul_inv]
      rw [hrw]
      exact Real.one_lt_rpow (by norm_num) hexp_pos
    have hBne : B.Nonempty := ⟨σ₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [d]; omega⟩⟩
    calc (B.card : ℝ) = ∑ _τ ∈ B, (1 : ℝ) := by simp
      _ < ∑ τ ∈ B, (3 : ℝ) ^ ((n : ℝ) / 10) * ((1 : ℝ) / 3) ^ (d τ) :=
          Finset.sum_lt_sum_of_nonempty hBne hlt_each
      _ ≤ ∑ τ : Fin n → Bool, (3 : ℝ) ^ ((n : ℝ) / 10) * ((1 : ℝ) / 3) ^ (d τ) :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => by positivity
  -- Evaluate the full sum as `3^(n/10) * (4/3)^n`.
  have h2 : ∑ τ : Fin n → Bool, (3 : ℝ) ^ ((n : ℝ) / 10) * ((1 : ℝ) / 3) ^ (d τ) =
      (3 : ℝ) ^ ((n : ℝ) / 10) * ((4 : ℝ) / 3) ^ n := by
    rw [← Finset.mul_sum]
    congr 1
    have hprod : ∀ τ : Fin n → Bool, ((1 : ℝ) / 3) ^ (d τ) =
        ∏ i : Fin n, (if τ i ≠ σ₀ i then (1 : ℝ) / 3 else 1) := by
      intro τ
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    simp_rw [hprod]
    let f : Fin n → Bool → ℝ := fun i b => if b ≠ σ₀ i then (1 : ℝ) / 3 else 1
    change ∑ τ : Fin n → Bool, ∏ i : Fin n, f i (τ i) = _
    rw [← Fintype.prod_sum f]
    have hterm : ∀ i : Fin n, ∑ b : Bool, f i b = 4 / 3 := by
      intro i
      dsimp only [f]
      cases h : σ₀ i <;> norm_num [Fintype.sum_bool]
    simp_rw [hterm]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- Compare `3^(n/10) * (4/3)^n ≤ 2^n * exp (-n/10)` by raising to the 10th power.
  have h3 : (3 : ℝ) ^ ((n : ℝ) / 10) * ((4 : ℝ) / 3) ^ n ≤ (2 : ℝ) ^ n * Real.exp (-(n : ℝ) / 10) := by
    have hbase : (3 : ℝ) ^ ((1 : ℝ) / 10) * ((4 : ℝ) / 3) ≤ 2 * Real.exp (-(1 : ℝ) / 10) := by
      have hlhs_nn : 0 ≤ (3 : ℝ) ^ ((1 : ℝ) / 10) * ((4 : ℝ) / 3) := by positivity
      have hrhs_nn : 0 ≤ 2 * Real.exp (-(1 : ℝ) / 10) := by positivity
      suffices h10 : ((3 : ℝ) ^ ((1 : ℝ) / 10) * ((4 : ℝ) / 3)) ^ 10 ≤
          (2 * Real.exp (-(1 : ℝ) / 10)) ^ 10 by
        exact le_of_pow_le_pow_left₀ (by norm_num : 10 ≠ 0) hrhs_nn h10
      rw [mul_pow, mul_pow, ← Real.rpow_natCast ((3 : ℝ) ^ _), ← Real.rpow_mul (by norm_num),
        ← Real.exp_nat_mul]
      norm_num
      have hexp1 : Real.exp 1 ≤ 4 := by
        have hhalf : (1 : ℝ) / 2 ≤ Real.exp (-(1 : ℝ) / 2) := by
          have := Real.add_one_le_exp (-(1 : ℝ) / 2); linarith
        have hpos : Real.exp ((1 : ℝ) / 2) ≤ 2 := by
          have h1 : Real.exp ((1 : ℝ) / 2) * Real.exp (-(1 : ℝ) / 2) = 1 := by
            rw [← Real.exp_add]; norm_num
          nlinarith [Real.exp_pos ((1 : ℝ) / 2)]
        have hsq : Real.exp 1 = Real.exp ((1 : ℝ) / 2) * Real.exp ((1 : ℝ) / 2) := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos ((1 : ℝ) / 2)]
      have hinv : (1 : ℝ) / 4 ≤ Real.exp (-1) := by
        rw [Real.exp_neg, one_div]
        exact inv_anti₀ (Real.exp_pos 1) hexp1
      linarith
    have hpow := pow_le_pow_left₀ (by positivity) hbase n
    rw [mul_pow, mul_pow, ← Real.rpow_natCast ((3 : ℝ) ^ _), ← Real.rpow_mul (by norm_num),
      ← Real.exp_nat_mul] at hpow
    convert hpow using 2 <;> ring
  linarith

/-- Spencer's three-valued coloring lemma at `x₀ = 0`: finds `z ∈ {-1, 0, 1}^n` with at least `n/10`
nonzero entries and `|⟨z, v_j⟩| ≤ c_j * ‖v_j‖₂`. -/
lemma spencer_partial_zero (n m : ℕ) (hn : 1 ≤ n) (v : Fin m → Fin n → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 2 ≤ c j)
    (hbudget : ∑ j : Fin m, Real.exp (-(c j ^ 2 / 4)) ≤ (n : ℝ) / 280) :
    ∃ z : Fin n → ℝ,
      (∀ i, z i = -1 ∨ z i = 0 ∨ z i = 1) ∧
      n ≤ 10 * ((Finset.univ : Finset (Fin n)).filter (fun i => z i ≠ 0)).card ∧
      ∀ j : Fin m, |∑ i : Fin n, z i * v j i| ≤ c j * Real.sqrt (∑ i : Fin n, v j i ^ 2) := by
  let Ω := Fin n → Bool
  have hΩ : 0 < Fintype.card Ω := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; positivity
  let normv (j : Fin m) : ℝ := Real.sqrt (∑ i : Fin n, v j i ^ 2)
  let b : Fin m → Ω → ℤ := fun j σ =>
    if normv j = 0 then 0
    else ⌊(∑ i : Fin n, signVal (σ i) * v j i) / (2 * c j * normv j) + 1 / 2⌋
  let img := (Finset.univ : Finset Ω).image (fun σ => fun j : Fin m => b j σ)
  let pTuple (y : Fin m → ℤ) : ℝ :=
    (((Finset.univ : Finset Ω).filter (fun σ => (fun j => b j σ) = y)).card : ℝ) / (2 : ℝ) ^ n
  have hcardΩ : (Fintype.card Ω : ℝ) = (2 : ℝ) ^ n := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; simp
  have hent_sub := entropy_tuple_le_sum hΩ m b
  simp only [hcardΩ] at hent_sub
  have hent_le : ∑ y ∈ img, entTerm (pTuple y) ≤ (n : ℝ) / 10 := by
    calc ∑ y ∈ img, entTerm (pTuple y)
        ≤ ∑ j : Fin m, ∑ z ∈ (Finset.univ : Finset Ω).image (b j),
            entTerm ((((Finset.univ : Finset Ω).filter (fun σ => b j σ = z)).card : ℝ) / (2 : ℝ) ^ n) :=
          hent_sub
      _ ≤ ∑ j : Fin m, 28 * Real.exp (-(c j ^ 2 / 4)) :=
          Finset.sum_le_sum fun j _ => bucket_entropy_le n (v j) (c j) (hc j)
      _ = 28 * ∑ j : Fin m, Real.exp (-(c j ^ 2 / 4)) := by rw [← Finset.mul_sum]
      _ ≤ (n : ℝ) / 10 := by linarith
  -- Average over `img` to find a fiber of weight `≥ exp (-n / 10)`.
  have hp_sum : ∑ y ∈ img, pTuple y = 1 := by
    dsimp only [pTuple]
    rw [← Finset.sum_div]
    have hcard : ∑ y ∈ img, ((Finset.univ : Finset Ω).filter (fun σ => (fun j => b j σ) = y)).card =
        Fintype.card Ω := by
      have := Finset.card_eq_sum_card_fiberwise (f := fun σ : Ω => fun j : Fin m => b j σ)
        (s := Finset.univ) (t := img) (fun σ _ => Finset.mem_image_of_mem _ (Finset.mem_univ _))
      simpa using this.symm
    have hcast : (∑ y ∈ img, (((Finset.univ : Finset Ω).filter (fun σ => (fun j => b j σ) = y)).card : ℝ)) =
        (2 : ℝ) ^ n := by rw [← hcardΩ]; exact_mod_cast hcard
    rw [hcast, div_self (by positivity)]
  have hex_big : ∃ y₀ ∈ img, Real.exp (-(n : ℝ) / 10) ≤ pTuple y₀ := by
    by_contra! hall
    have hlt : ∑ y ∈ img, pTuple y * ((n : ℝ) / 10) < ∑ y ∈ img, entTerm (pTuple y) := by
      have himg_ne : img.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
      refine Finset.sum_lt_sum_of_nonempty himg_ne fun y hy => ?_
      obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hy
      have hppos : 0 < pTuple (fun j => b j σ) := by
        dsimp only [pTuple]
        apply div_pos _ (by positivity)
        have hcpos : 0 < ((Finset.univ : Finset Ω).filter (fun σ' => (fun j => b j σ') = fun j => b j σ)).card :=
          Finset.card_pos.mpr ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
        exact_mod_cast hcpos
      have hlt_y := hall (fun j => b j σ) hy
      have hlog : Real.log (pTuple (fun j => b j σ)) < -(n : ℝ) / 10 := by
        have := Real.log_lt_log hppos hlt_y
        rwa [Real.log_exp] at this
      simp only [entTerm, not_le.mpr hppos, ↓reduceIte]
      nlinarith
    rw [← Finset.sum_mul, hp_sum, one_mul] at hlt
    linarith
  obtain ⟨y₀, hy₀, hpy₀⟩ := hex_big
  let F := (Finset.univ : Finset Ω).filter (fun σ => (fun j => b j σ) = y₀)
  have hF_card : (2 : ℝ) ^ n * Real.exp (-(n : ℝ) / 10) ≤ (F.card : ℝ) := by
    dsimp only [pTuple] at hpy₀
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)).mp hpy₀
    linarith
  have hF_ne : F.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < (F.card : ℝ) := lt_of_lt_of_le (by positivity) hF_card
    exact_mod_cast hpos
  obtain ⟨σ₀, hσ₀⟩ := hF_ne
  -- Compare `F` with the small Hamming ball around `σ₀`.
  let Ball := (Finset.univ : Finset Ω).filter
    (fun τ => 10 * ((Finset.univ : Finset (Fin n)).filter (fun i => τ i ≠ σ₀ i)).card < n)
  have hBall_lt : (Ball.card : ℝ) < (F.card : ℝ) :=
    lt_of_lt_of_le (hamming_ball_card_lt n hn σ₀) hF_card
  have hnot_sub : ¬ (F ⊆ Ball) := fun hsub => by
    have : (F.card : ℝ) ≤ (Ball.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    linarith
  obtain ⟨τ, hτF, hτnotB⟩ := Finset.not_subset.mp hnot_sub
  have hdist : n ≤ 10 * ((Finset.univ : Finset (Fin n)).filter (fun i => τ i ≠ σ₀ i)).card := by
    have : ¬ (10 * ((Finset.univ : Finset (Fin n)).filter (fun i => τ i ≠ σ₀ i)).card < n) :=
      fun h => hτnotB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  -- Set `z i = (signVal (τ i) - signVal (σ₀ i)) / 2`.
  refine ⟨fun i => (signVal (τ i) - signVal (σ₀ i)) / 2, ?_, ?_, ?_⟩
  · intro i
    cases h1 : τ i <;> cases h2 : σ₀ i <;> norm_num [signVal, h1, h2]
  · have hfilt_eq : (Finset.univ : Finset (Fin n)).filter
        (fun i => (signVal (τ i) - signVal (σ₀ i)) / 2 ≠ 0) =
        (Finset.univ : Finset (Fin n)).filter (fun i => τ i ≠ σ₀ i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases h1 : τ i <;> cases h2 : σ₀ i <;> norm_num [signVal, h1, h2]
    rw [hfilt_eq]
    exact hdist
  · intro j
    by_cases hnj : normv j = 0
    · have hsum0 : ∑ i : Fin n, v j i ^ 2 = 0 := by
        have hnn : 0 ≤ ∑ i : Fin n, v j i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
        have hsq : normv j ^ 2 = ∑ i : Fin n, v j i ^ 2 := Real.sq_sqrt hnn
        rw [hnj, zero_pow (by norm_num)] at hsq; exact hsq.symm
      have hv0 : ∀ i : Fin n, v j i = 0 := fun i => by
        have hle : v j i ^ 2 ≤ ∑ k : Fin n, v j k ^ 2 :=
          Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
        rw [hsum0] at hle
        nlinarith [sq_nonneg (v j i)]
      simp [hv0]
    · have hnj_pos : 0 < normv j := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hnj)
      have hcj_pos : 0 < c j := by linarith [hc j]
      have hb_eq : b j τ = b j σ₀ := by
        have h1 : (fun k => b k τ) = y₀ := (Finset.mem_filter.mp hτF).2
        have h2 : (fun k => b k σ₀) = y₀ := (Finset.mem_filter.mp hσ₀).2
        exact congrFun (h1.trans h2.symm) j
      simp only [b, hnj, ↓reduceIte] at hb_eq
      set A := (∑ i : Fin n, signVal (τ i) * v j i) / (2 * c j * normv j) + 1 / 2
      set B' := (∑ i : Fin n, signVal (σ₀ i) * v j i) / (2 * c j * normv j) + 1 / 2
      have hA_lo : ((⌊A⌋ : ℤ) : ℝ) ≤ A := Int.floor_le A
      have hA_hi : A < ((⌊A⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one A
      have hB_lo : ((⌊B'⌋ : ℤ) : ℝ) ≤ B' := Int.floor_le B'
      have hB_hi : B' < ((⌊B'⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one B'
      rw [hb_eq] at hA_lo hA_hi
      have hdiff_lt : |A - B'| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have hdiff_eq : A - B' = (∑ i : Fin n, (signVal (τ i) - signVal (σ₀ i)) / 2 * v j i) /
          (c j * normv j) := by
        dsimp only [A, B']
        have hsum_sub : ∑ i : Fin n, signVal (τ i) * v j i - ∑ i : Fin n, signVal (σ₀ i) * v j i =
            2 * ∑ i : Fin n, (signVal (τ i) - signVal (σ₀ i)) / 2 * v j i := by
          rw [← Finset.sum_sub_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring
        have hden : c j * normv j ≠ 0 := by positivity
        calc (∑ i : Fin n, signVal (τ i) * v j i) / (2 * c j * normv j) + 1 / 2 -
              ((∑ i : Fin n, signVal (σ₀ i) * v j i) / (2 * c j * normv j) + 1 / 2)
            = (∑ i : Fin n, signVal (τ i) * v j i - ∑ i : Fin n, signVal (σ₀ i) * v j i) /
                (2 * (c j * normv j)) := by ring
          _ = (2 * ∑ i : Fin n, (signVal (τ i) - signVal (σ₀ i)) / 2 * v j i) /
                (2 * (c j * normv j)) := by rw [hsum_sub]
          _ = (∑ i : Fin n, (signVal (τ i) - signVal (σ₀ i)) / 2 * v j i) / (c j * normv j) := by
                field_simp [hden]
      rw [hdiff_eq, abs_div, abs_of_pos (mul_pos hcj_pos hnj_pos),
        div_le_one (mul_pos hcj_pos hnj_pos)] at hdiff_lt
      exact hdiff_lt

/-- Partial coloring from an arbitrary starting point `x₀ ∈ [-1, 1]^n`: fixes at least `n / 20`
coordinates to `±1`. -/
lemma spencer_partial_general (n m : ℕ) (hn : 1 ≤ n) (v : Fin m → Fin n → ℝ)
    (x₀ : Fin n → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1) (c : Fin m → ℝ)
    (hc : ∀ j, 2 ≤ c j)
    (hbudget : ∑ j : Fin m, Real.exp (-(c j ^ 2 / 4)) ≤ (n : ℝ) / 280) :
    ∃ x : Fin n → ℝ,
      (∀ i, |x i| ≤ 1) ∧
      n ≤ 20 * ((Finset.univ : Finset (Fin n)).filter (fun i => x i = -1 ∨ x i = 1)).card ∧
      ∀ j : Fin m, |∑ i : Fin n, (x i - x₀ i) * v j i| ≤
        c j * Real.sqrt (∑ i : Fin n, v j i ^ 2) := by
  let r : Fin n → ℝ := fun i => 1 - |x₀ i|
  have hr_nn : ∀ i, 0 ≤ r i := fun i => by dsimp [r]; linarith [hx₀ i]
  have hr_le : ∀ i, r i ≤ 1 := fun i => by dsimp [r]; linarith [abs_nonneg (x₀ i)]
  let w : Fin m → Fin n → ℝ := fun j i => r i * v j i
  obtain ⟨z, hz_val, hz_card, hz_bound⟩ := spencer_partial_zero n m hn w c hc hbudget
  let xPlus : Fin n → ℝ := fun i => x₀ i + r i * z i
  let xMinus : Fin n → ℝ := fun i => x₀ i - r i * z i
  have hvalid : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ i, |x₀ i + s * (r i * z i)| ≤ 1 := by
    intro s hs i
    have hrz : |s * (r i * z i)| ≤ r i := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hr_nn i)]
      have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
      have hz1 : |z i| ≤ 1 := by rcases hz_val i with h | h | h <;> rw [h] <;> norm_num
      rw [hs1, one_mul]
      nlinarith [hr_nn i]
    calc |x₀ i + s * (r i * z i)| ≤ |x₀ i| + |s * (r i * z i)| := abs_add_le _ _
      _ ≤ |x₀ i| + r i := by linarith
      _ = 1 := by dsimp [r]; ring
  have hbound : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ j : Fin m,
      |∑ i : Fin n, (s * (r i * z i)) * v j i| ≤ c j * Real.sqrt (∑ i : Fin n, v j i ^ 2) := by
    intro s hs j
    have heq : ∑ i : Fin n, (s * (r i * z i)) * v j i = s * ∑ i : Fin n, z i * w j i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by dsimp [w]; ring
    rw [heq, abs_mul]
    have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    rw [hs1, one_mul]
    have hw_le : ∑ i : Fin n, w j i ^ 2 ≤ ∑ i : Fin n, v j i ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      dsimp only [w]
      rw [mul_pow]
      have hr2 : r i ^ 2 ≤ 1 := by nlinarith [hr_nn i, hr_le i]
      nlinarith [sq_nonneg (v j i)]
    calc |∑ i : Fin n, z i * w j i|
        ≤ c j * Real.sqrt (∑ i : Fin n, w j i ^ 2) := hz_bound j
      _ ≤ c j * Real.sqrt (∑ i : Fin n, v j i ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hw_le) (by linarith [hc j])
  -- Every nonzero coordinate of `z` lands in `{-1, 1}` for at least one of `xPlus`, `xMinus`.
  let S_nz := (Finset.univ : Finset (Fin n)).filter (fun i => z i ≠ 0)
  let S_plus := (Finset.univ : Finset (Fin n)).filter (fun i => xPlus i = -1 ∨ xPlus i = 1)
  let S_minus := (Finset.univ : Finset (Fin n)).filter (fun i => xMinus i = -1 ∨ xMinus i = 1)
  have hcover : S_nz ⊆ S_plus ∪ S_minus := by
    intro i hi
    have hzne : z i ≠ 0 := (Finset.mem_filter.mp hi).2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases le_total 0 (x₀ i) with hxpos | hxneg
    · have hreq : r i = 1 - x₀ i := by dsimp [r]; rw [abs_of_nonneg hxpos]
      rcases hz_val i with hzm | hz0 | hzp
      · exact Or.inr ⟨Finset.mem_univ _, Or.inr (by dsimp [xMinus]; rw [hreq, hzm]; ring)⟩
      · exact absurd hz0 hzne
      · exact Or.inl ⟨Finset.mem_univ _, Or.inr (by dsimp [xPlus]; rw [hreq, hzp]; ring)⟩
    · have hreq : r i = 1 + x₀ i := by dsimp [r]; rw [abs_of_nonpos hxneg]; ring
      rcases hz_val i with hzm | hz0 | hzp
      · exact Or.inl ⟨Finset.mem_univ _, Or.inl (by dsimp [xPlus]; rw [hreq, hzm]; ring)⟩
      · exact absurd hz0 hzne
      · exact Or.inr ⟨Finset.mem_univ _, Or.inl (by dsimp [xMinus]; rw [hreq, hzp]; ring)⟩
  have hsum_card : S_nz.card ≤ S_plus.card + S_minus.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  by_cases hge : S_minus.card ≤ S_plus.card
  · refine ⟨xPlus, fun i => by simpa [xPlus] using hvalid 1 (Or.inl rfl) i, ?_, fun j => ?_⟩
    · dsimp only [S_nz, S_plus, S_minus] at hsum_card hge; omega
    · have := hbound 1 (Or.inl rfl) j
      simpa [xPlus] using this
  · refine ⟨xMinus, fun i => ?_, ?_, fun j => ?_⟩
    · have := hvalid (-1) (Or.inr rfl) i
      simpa [xMinus, sub_eq_add_neg] using this
    · dsimp only [S_nz, S_plus, S_minus] at hsum_card hge; omega
    · have := hbound (-1) (Or.inr rfl) j
      simpa [xMinus, sub_eq_add_neg] using this

/-! ### Section 5: Iterated full `±1` discrepancy coloring -/

/-- Full `±1` discrepancy coloring (analogue of BBMST Corollary 4.2):
for any `x₀ ∈ [-1, 1]^n` and `v_1, …, v_m ∈ ℝ^n`, if `c_j ≥ 100` and
`∑_j exp (-c_j^2 / 10000) ≤ n / 280`, then there exists `x ∈ {-1, 1}^n` with
`|⟨x - x₀, v_j⟩| ≤ (c_j + 200) * √n * ‖v_j‖_∞`. -/
theorem full_coloring (n : ℕ) :
    ∀ (m : ℕ) (v : Fin m → Fin n → ℝ) (x₀ : Fin n → ℝ) (_ : ∀ i, |x₀ i| ≤ 1)
      (c : Fin m → ℝ) (_ : ∀ j, 100 ≤ c j)
      (_ : ∑ j : Fin m, Real.exp (-(c j ^ 2 / 10000)) ≤ (n : ℝ) / 280)
      (B : Fin m → ℝ) (_ : ∀ j i, |v j i| ≤ B j),
    ∃ x : Fin n → ℝ,
      (∀ i, x i = -1 ∨ x i = 1) ∧
      ∀ j : Fin m, |∑ i : Fin n, (x i - x₀ i) * v j i| ≤ (c j + 200) * Real.sqrt n * B j := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro m v x₀ hx₀ c hc hbudget B hB
    by_cases hn_small : n ≤ 40000
    · -- Base case: round every coordinate to `±1` with `|x i - x₀ i| ≤ 1`.
      let x : Fin n → ℝ := fun i => if 0 ≤ x₀ i then 1 else -1
      refine ⟨x, fun i => by dsimp [x]; split_ifs <;> simp, fun j => ?_⟩
      by_cases hn0 : n = 0
      · subst hn0; simp
      · have hBnn : 0 ≤ B j :=
          (abs_nonneg (v j ⟨0, Nat.pos_of_ne_zero hn0⟩)).trans (hB j ⟨0, Nat.pos_of_ne_zero hn0⟩)
        have hdiff : ∀ i : Fin n, |x i - x₀ i| ≤ 1 := by
          intro i
          dsimp only [x]
          have h1 := abs_le.mp (hx₀ i)
          split_ifs with h
          · rw [abs_le]; constructor <;> linarith
          · rw [abs_le]; constructor <;> linarith
        have hsum_le : |∑ i : Fin n, (x i - x₀ i) * v j i| ≤ (n : ℝ) * B j := by
          calc |∑ i : Fin n, (x i - x₀ i) * v j i|
              ≤ ∑ i : Fin n, |(x i - x₀ i) * v j i| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _i : Fin n, B j := by
                refine Finset.sum_le_sum fun i _ => ?_
                rw [abs_mul]
                calc |x i - x₀ i| * |v j i| ≤ 1 * B j :=
                      mul_le_mul (hdiff i) (hB j i) (abs_nonneg _) (by norm_num)
                  _ = B j := one_mul _
            _ = (n : ℝ) * B j := by simp
        have hn_le_200 : (n : ℝ) ≤ 200 * Real.sqrt n := by
          have hnr : (n : ℝ) ≤ 40000 := by exact_mod_cast hn_small
          have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have hsq : Real.sqrt n ≤ 200 := by
            rw [Real.sqrt_le_left (by norm_num)]; linarith
          have hmul : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hnn).symm
          nlinarith [Real.sqrt_nonneg n]
        have hc200 : 200 ≤ c j + 200 := by linarith [hc j]
        calc |∑ i : Fin n, (x i - x₀ i) * v j i|
            ≤ (n : ℝ) * B j := hsum_le
          _ ≤ (200 * Real.sqrt n) * B j := mul_le_mul_of_nonneg_right hn_le_200 hBnn
          _ ≤ ((c j + 200) * Real.sqrt n) * B j := by
              have : 200 * Real.sqrt n ≤ (c j + 200) * Real.sqrt n :=
                mul_le_mul_of_nonneg_right hc200 (Real.sqrt_nonneg n)
              exact mul_le_mul_of_nonneg_right this hBnn
    · push Not at hn_small
      have hn1 : 1 ≤ n := by omega
      have hBnn : ∀ j, 0 ≤ B j := fun j =>
        (abs_nonneg (v j ⟨0, by omega⟩)).trans (hB j ⟨0, by omega⟩)
      -- Step 1: apply three-valued coloring with `b j = c j / 50`.
      let b : Fin m → ℝ := fun j => c j / 50
      have hb_ge2 : ∀ j, 2 ≤ b j := fun j => by dsimp [b]; linarith [hc j]
      have hb_budget : ∑ j : Fin m, Real.exp (-(b j ^ 2 / 4)) ≤ (n : ℝ) / 280 := by
        have heq : ∀ j, -(b j ^ 2 / 4) = -(c j ^ 2 / 10000) := fun j => by dsimp [b]; ring
        simp_rw [heq]; exact hbudget
      obtain ⟨y, hy_abs, hy_card, hy_bound⟩ :=
        spencer_partial_general n m hn1 v x₀ hx₀ b hb_ge2 hb_budget
      -- Choose a subset `U` of fixed coordinates of size exactly `n / 20`.
      let S_fix := (Finset.univ : Finset (Fin n)).filter (fun i => y i = -1 ∨ y i = 1)
      have hU_le : n / 20 ≤ S_fix.card := by dsimp only [S_fix]; omega
      obtain ⟨U, hU_sub, hU_card⟩ := Finset.exists_subset_card_eq hU_le
      let W : Finset (Fin n) := Finset.univ \ U
      have hW_card : W.card = n - n / 20 := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hU_card]
      set n' : ℕ := W.card
      have hn'_lt : n' < n := by omega
      have hn'_pos : 0 < n' := by omega
      -- Reindex `W` via an equivalence `e : Fin n' ≃ W`.
      let e : Fin n' ≃ W := (Fintype.equivFinOfCardEq (by simp [n'])).symm
      -- Define updated parameters `a j = √(c j ^ 2 + 10000 * log (n / n'))`.
      have hratio_ge : (1 : ℝ) ≤ (n : ℝ) / (n' : ℝ) := by
        rw [one_le_div (by exact_mod_cast hn'_pos)]
        exact_mod_cast (show n' ≤ n by omega)
      have hlog_nn : 0 ≤ Real.log ((n : ℝ) / (n' : ℝ)) := Real.log_nonneg hratio_ge
      let a : Fin m → ℝ := fun j => Real.sqrt (c j ^ 2 + 10000 * Real.log ((n : ℝ) / (n' : ℝ)))
      have ha_sq : ∀ j, a j ^ 2 = c j ^ 2 + 10000 * Real.log ((n : ℝ) / (n' : ℝ)) := fun j =>
        Real.sq_sqrt (by positivity)
      have ha_ge100 : ∀ j, 100 ≤ a j := by
        intro j
        have h1 : c j ^ 2 ≤ a j ^ 2 := by rw [ha_sq]; linarith
        have h2 : c j ≤ a j := by nlinarith [hc j, Real.sqrt_nonneg (c j ^ 2 + 10000 * Real.log ((n : ℝ) / (n' : ℝ)))]
        linarith [hc j]
      have ha_budget : ∑ j : Fin m, Real.exp (-(a j ^ 2 / 10000)) ≤ (n' : ℝ) / 280 := by
        have hterm : ∀ j, Real.exp (-(a j ^ 2 / 10000)) =
            ((n' : ℝ) / (n : ℝ)) * Real.exp (-(c j ^ 2 / 10000)) := by
          intro j
          rw [ha_sq]
          have harg : -((c j ^ 2 + 10000 * Real.log ((n : ℝ) / (n' : ℝ))) / 10000) =
              -Real.log ((n : ℝ) / (n' : ℝ)) + -(c j ^ 2 / 10000) := by ring
          rw [harg, Real.exp_add, Real.exp_neg,
            Real.exp_log (div_pos (by exact_mod_cast hn1) (by exact_mod_cast hn'_pos)),
            inv_div]
        simp_rw [hterm, ← Finset.mul_sum]
        have hnr_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have h1 := mul_le_mul_of_nonneg_left hbudget (div_nonneg (Nat.cast_nonneg n') hnr_pos.le)
        calc ((n' : ℝ) / (n : ℝ)) * ∑ j : Fin m, Real.exp (-(c j ^ 2 / 10000))
            ≤ ((n' : ℝ) / (n : ℝ)) * ((n : ℝ) / 280) := h1
          _ = (n' : ℝ) / 280 := by field_simp [hnr_pos.ne']
      -- Apply induction hypothesis on `W` (size `n'`).
      obtain ⟨z, hz_pm, hz_bound⟩ := ih n' hn'_lt m
        (fun j k => v j (e k).1)
        (fun k => y (e k).1)
        (fun k => hy_abs (e k).1)
        a ha_ge100 ha_budget B (fun j k => hB j (e k).1)
      -- Assemble `x` on `Fin n`: `y i` for `i ∈ U`, `z (e.symm ⟨i, _⟩)` for `i ∈ W`.
      let x : Fin n → ℝ := fun i =>
        if hi : i ∈ W then z (e.symm ⟨i, hi⟩) else y i
      refine ⟨x, ?_, ?_⟩
      · intro i
        dsimp only [x]
        split_ifs with hi
        · exact hz_pm _
        · have hiU : i ∈ U := by
            by_contra hnot
            exact hi (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
          exact (Finset.mem_filter.mp (hU_sub hiU)).2
      · intro j
        -- Split `∑ i, (x i - x₀ i) * v j i = ∑ i, (y i - x₀ i) * v j i + ∑ i, (x i - y i) * v j i`.
        have hdecomp : ∑ i : Fin n, (x i - x₀ i) * v j i =
            (∑ i : Fin n, (y i - x₀ i) * v j i) + (∑ k : Fin n', (z k - y (e k).1) * v j (e k).1) := by
          have h1 : ∑ i : Fin n, (x i - x₀ i) * v j i =
              (∑ i : Fin n, (y i - x₀ i) * v j i) + (∑ i : Fin n, (x i - y i) * v j i) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => by ring
          rw [h1]
          congr 1
          have hWsum : ∑ i : Fin n, (x i - y i) * v j i = ∑ i ∈ W, (x i - y i) * v j i := by
            rw [← Finset.sum_subset (Finset.subset_univ W)]
            intro i _ hiW
            simp [x, hiW]
          rw [hWsum]
          refine Finset.sum_bij (fun i hi => e.symm ⟨i, hi⟩) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
          · intro i₁ hi₁ i₂ hi₂ hEq
            have := e.symm.injective hEq
            exact congrArg Subtype.val this
          · intro k _
            refine ⟨(e k).1, (e k).2, ?_⟩
            simp
          · intro i hi
            simp [x, hi]
        rw [hdecomp]
        -- Bound the first term by `0.02 * c j * √n * B j`.
        have hnorm_le : Real.sqrt (∑ i : Fin n, v j i ^ 2) ≤ Real.sqrt n * B j := by
          have hsq : ∑ i : Fin n, v j i ^ 2 ≤ (n : ℝ) * B j ^ 2 := by
            calc ∑ i : Fin n, v j i ^ 2 ≤ ∑ _i : Fin n, B j ^ 2 := by
                  refine Finset.sum_le_sum fun i _ => ?_
                  have := hB j i
                  have h1 : |v j i| ^ 2 ≤ B j ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
                  simpa [sq_abs] using h1
              _ = (n : ℝ) * B j ^ 2 := by simp
          calc Real.sqrt (∑ i : Fin n, v j i ^ 2)
              ≤ Real.sqrt ((n : ℝ) * B j ^ 2) := Real.sqrt_le_sqrt hsq
            _ = Real.sqrt n * Real.sqrt (B j ^ 2) := Real.sqrt_mul (Nat.cast_nonneg n) _
            _ = Real.sqrt n * B j := by rw [Real.sqrt_sq (hBnn j)]
        have hterm1 : |∑ i : Fin n, (y i - x₀ i) * v j i| ≤ (c j / 50) * Real.sqrt n * B j := by
          calc |∑ i : Fin n, (y i - x₀ i) * v j i|
              ≤ (c j / 50) * Real.sqrt (∑ i : Fin n, v j i ^ 2) := hy_bound j
            _ ≤ (c j / 50) * (Real.sqrt n * B j) :=
                mul_le_mul_of_nonneg_left hnorm_le (by linarith [hc j])
            _ = (c j / 50) * Real.sqrt n * B j := by ring
        -- Bound `a j ≤ c j + 4` and `√n' ≤ 0.975 * √n`.
        have ha_le : a j ≤ c j + 4 := by
          have hlog_le : Real.log ((n : ℝ) / (n' : ℝ)) ≤ 2 / 37 := by
            have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
            have hnr' : (0 : ℝ) < (n' : ℝ) := by exact_mod_cast hn'_pos
            have h1 := Real.log_le_sub_one_of_pos (div_pos hnr hnr')
            have hfrac : (n : ℝ) / (n' : ℝ) - 1 ≤ 2 / 37 := by
              have hn'ge : (19 : ℝ) * (n : ℝ) ≤ 20 * (n' : ℝ) := by
                have : 19 * n ≤ 20 * n' := by omega
                exact_mod_cast this
              rw [sub_le_iff_le_add, div_le_iff₀ hnr']
              linarith
            linarith
          have hsq_le : a j ^ 2 ≤ (c j + 4) ^ 2 := by
            rw [ha_sq]
            nlinarith [hc j]
          nlinarith [hc j, Real.sqrt_nonneg (c j ^ 2 + 10000 * Real.log ((n : ℝ) / (n' : ℝ)))]
        have hsqrt_le : Real.sqrt n' ≤ (39 / 40 : ℝ) * Real.sqrt n := by
          have hsq : (n' : ℝ) ≤ (39 / 40 : ℝ) ^ 2 * (n : ℝ) := by
            have hn'le : 20 * n' ≤ 19 * n + 20 := by omega
            have hcast : (20 : ℝ) * (n' : ℝ) ≤ 19 * (n : ℝ) + 20 := by exact_mod_cast hn'le
            have hnbig : (40000 : ℝ) < (n : ℝ) := by exact_mod_cast hn_small
            nlinarith
          calc Real.sqrt n' ≤ Real.sqrt ((39 / 40 : ℝ) ^ 2 * (n : ℝ)) := Real.sqrt_le_sqrt hsq
            _ = Real.sqrt ((39 / 40 : ℝ) ^ 2) * Real.sqrt n := Real.sqrt_mul (by positivity) _
            _ = (39 / 40 : ℝ) * Real.sqrt n := by rw [Real.sqrt_sq (by norm_num)]
        have hterm2 : |∑ k : Fin n', (z k - y (e k).1) * v j (e k).1| ≤
            (c j + 204) * ((39 / 40 : ℝ) * Real.sqrt n) * B j := by
          calc |∑ k : Fin n', (z k - y (e k).1) * v j (e k).1|
              ≤ (a j + 200) * Real.sqrt n' * B j := hz_bound j
            _ ≤ (c j + 204) * ((39 / 40 : ℝ) * Real.sqrt n) * B j := by
                have h1 : (a j + 200) * Real.sqrt n' ≤ (c j + 204) * ((39 / 40 : ℝ) * Real.sqrt n) :=
                  mul_le_mul (by linarith) hsqrt_le (Real.sqrt_nonneg _) (by linarith [hc j])
                exact mul_le_mul_of_nonneg_right h1 (hBnn j)
        calc |∑ i : Fin n, (y i - x₀ i) * v j i + ∑ k : Fin n', (z k - y (e k).1) * v j (e k).1|
            ≤ |∑ i : Fin n, (y i - x₀ i) * v j i| +
              |∑ k : Fin n', (z k - y (e k).1) * v j (e k).1| := abs_add_le _ _
          _ ≤ (c j / 50) * Real.sqrt n * B j +
              (c j + 204) * ((39 / 40 : ℝ) * Real.sqrt n) * B j := add_le_add hterm1 hterm2
          _ = (c j / 50 + (c j + 204) * (39 / 40 : ℝ)) * (Real.sqrt n * B j) := by ring
          _ ≤ (c j + 200) * (Real.sqrt n * B j) := by
              have hcoeff : c j / 50 + (c j + 204) * (39 / 40 : ℝ) ≤ c j + 200 := by
                linarith [hc j]
              exact mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (Real.sqrt_nonneg _) (hBnn j))
          _ = (c j + 200) * Real.sqrt n * B j := by ring

end TwoOrbitDiscrepancy

/-!
# Rudin-Shapiro Cosine Polynomial & Well-Separated Bad Intervals

Self-contained formalization of BBMST (2020) Section 3 with three simplifications:
1. Exact derivative bounds `‖P_t^{(k)}‖² + ‖Q_t^{(k)}‖² ≤ 2^(2kt + t + 1)` proved directly by
   parallelogram-law induction on `(k, t)` — no Bernstein inequality needed.
2. `intervals_nice` proved via Rolle's theorem + MVT for `k ∈ {1, 2, 3}` — no Howell theorem needed.
3. Bad-interval count `N ≤ 2 γ m` proved via IVT + Chebyshev polynomial roots — no root multiplicities.
4. Grid width `16 π / m` (for `32 ∣ m`) so fattened intervals `I⁺` are pairwise disjoint inside `(0, π/2)`.
-/

namespace TwoOrbitCosine

open scoped BigOperators ComplexConjugate
open Finset

/-! ### Section 1: Rudin-Shapiro coefficients, polynomials, and initial sums -/

def rsPcoeff : ℕ → ℕ → ℝ
  | 0, j => if j = 0 then 1 else 0
  | t + 1, j => if j < 2 ^ t then rsPcoeff t j else rsQcoeff t (j - 2 ^ t)
where
  rsQcoeff : ℕ → ℕ → ℝ
  | 0, j => if j = 0 then 1 else 0
  | t + 1, j => if j < 2 ^ t then rsPcoeff t j else -rsQcoeff t (j - 2 ^ t)

def rsQcoeff : ℕ → ℕ → ℝ := rsPcoeff.rsQcoeff

lemma rsPcoeff_zero (j : ℕ) : rsPcoeff 0 j = if j = 0 then 1 else 0 := rfl
lemma rsQcoeff_zero (j : ℕ) : rsQcoeff 0 j = if j = 0 then 1 else 0 := rfl
lemma rsPcoeff_succ (t j : ℕ) :
    rsPcoeff (t + 1) j = if j < 2 ^ t then rsPcoeff t j else rsQcoeff t (j - 2 ^ t) := rfl
lemma rsQcoeff_succ (t j : ℕ) :
    rsQcoeff (t + 1) j = if j < 2 ^ t then rsPcoeff t j else -rsQcoeff t (j - 2 ^ t) := rfl

lemma rsPcoeff_pm_and_rsQcoeff_pm (t : ℕ) :
    (∀ j < 2 ^ t, rsPcoeff t j = -1 ∨ rsPcoeff t j = 1) ∧
    (∀ j < 2 ^ t, rsQcoeff t j = -1 ∨ rsQcoeff t j = 1) := by
  induction t with
  | zero =>
    constructor <;> (intro j hj; have hj0 : j = 0 := (by omega); subst hj0; right; rfl)
  | succ t ih =>
    constructor <;> intro j hj
    · rw [rsPcoeff_succ]
      split_ifs with h
      · exact ih.1 j h
      · exact ih.2 (j - 2 ^ t) (by omega)
    · rw [rsQcoeff_succ]
      split_ifs with h
      · exact ih.1 j h
      · rcases ih.2 (j - 2 ^ t) (by omega) with hq | hq <;> [right; left] <;> linarith

lemma rsPcoeff_eq_of_lt {t s j : ℕ} (hts : t ≤ s) (hj : j < 2 ^ t) :
    rsPcoeff s j = rsPcoeff t j := by
  induction hts with
  | refl => rfl
  | step hle ih =>
    rename_i s'
    rw [rsPcoeff_succ, if_pos (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) hle))]
    exact ih

lemma rsQcoeff_eq_rsPcoeff_of_lt {t s j : ℕ} (hts : t < s) (hj : j < 2 ^ t) :
    rsQcoeff s j = rsPcoeff t j := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_lt hts
  rw [rsQcoeff_succ,
    if_pos (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  exact rsPcoeff_eq_of_lt (by omega) hj

/-- Infinite Rudin-Shapiro sequence agreeing with `rsPcoeff t` on `j < 2^t`. -/
def rsSeq (j : ℕ) : ℝ := rsPcoeff (j + 1) j

lemma rsSeq_eq_rsPcoeff {t j : ℕ} (hj : j < 2 ^ t) : rsSeq j = rsPcoeff t j := by
  unfold rsSeq
  have h1 : j < 2 ^ (j + 1) := lt_trans Nat.lt_two_pow_self (Nat.pow_lt_pow_right (by norm_num) (by omega))
  rcases le_total t (j + 1) with h | h
  · exact rsPcoeff_eq_of_lt h hj
  · exact (rsPcoeff_eq_of_lt h h1).symm

lemma rsSeq_pm (j : ℕ) : rsSeq j = -1 ∨ rsSeq j = 1 := by
  have h1 : j < 2 ^ (j + 1) := lt_trans Nat.lt_two_pow_self (Nat.pow_lt_pow_right (by norm_num) (by omega))
  exact (rsPcoeff_pm_and_rsQcoeff_pm (j + 1)).1 j h1

noncomputable def rsP (t : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ range (2 ^ t), (rsPcoeff t j : ℂ) * z ^ j

noncomputable def rsQ (t : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ range (2 ^ t), (rsQcoeff t j : ℂ) * z ^ j

lemma rsP_zero (z : ℂ) : rsP 0 z = 1 := by simp [rsP, rsPcoeff_zero]
lemma rsQ_zero (z : ℂ) : rsQ 0 z = 1 := by simp [rsQ, rsQcoeff_zero]

lemma rsP_succ (t : ℕ) (z : ℂ) : rsP (t + 1) z = rsP t z + z ^ (2 ^ t) * rsQ t z := by
  unfold rsP rsQ
  rw [pow_succ', two_mul, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [rsPcoeff_succ, if_pos (Finset.mem_range.mp hj)]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hnot : ¬ (2 ^ t + j < 2 ^ t) := by omega
    rw [rsPcoeff_succ, if_neg hnot, Nat.add_sub_cancel_left, pow_add]
    ring

lemma rsQ_succ (t : ℕ) (z : ℂ) : rsQ (t + 1) z = rsP t z - z ^ (2 ^ t) * rsQ t z := by
  unfold rsP rsQ
  rw [pow_succ', two_mul, Finset.sum_range_add, Finset.mul_sum, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [rsQcoeff_succ, if_pos (Finset.mem_range.mp hj)]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hnot : ¬ (2 ^ t + j < 2 ^ t) := by omega
    rw [rsQcoeff_succ, if_neg hnot, Nat.add_sub_cancel_left, pow_add]
    push_cast; ring

lemma complex_parallelogram (u v : ℂ) :
    ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im]
  ring

lemma rs_norm_sq_sum (t : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖rsP t z‖ ^ 2 + ‖rsQ t z‖ ^ 2 = (2 : ℝ) ^ (t + 1) := by
  induction t with
  | zero => simp [rsP_zero, rsQ_zero]; norm_num
  | succ t ih =>
    rw [rsP_succ, rsQ_succ, complex_parallelogram, norm_mul, norm_pow, hz, one_pow, one_mul, ih,
      ← pow_succ']

lemma rsP_norm_le (t : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖rsP t z‖ ≤ Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
  have h := rs_norm_sq_sum t hz
  have hsq : ‖rsP t z‖ ^ 2 ≤ (2 : ℝ) ^ (t + 1) := by nlinarith [sq_nonneg ‖rsQ t z‖]
  calc ‖rsP t z‖ = Real.sqrt (‖rsP t z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((2 : ℝ) ^ (t + 1)) := Real.sqrt_le_sqrt hsq

lemma rsQ_norm_le (t : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖rsQ t z‖ ≤ Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
  have h := rs_norm_sq_sum t hz
  have hsq : ‖rsQ t z‖ ^ 2 ≤ (2 : ℝ) ^ (t + 1) := by nlinarith [sq_nonneg ‖rsP t z‖]
  calc ‖rsQ t z‖ = Real.sqrt (‖rsQ t z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((2 : ℝ) ^ (t + 1)) := Real.sqrt_le_sqrt hsq

/-- Partial sum bound: `‖∑ j < M, rsPcoeff t j * z^j‖ ≤ 4 √M` (and same for `rsQcoeff`). -/
lemma rs_partial_bound (t : ℕ) :
    ∀ M ≤ 2 ^ t, ∀ z : ℂ, ‖z‖ = 1 →
      ‖∑ j ∈ range M, (rsPcoeff t j : ℂ) * z ^ j‖ ≤ 4 * Real.sqrt M ∧
      ‖∑ j ∈ range M, (rsQcoeff t j : ℂ) * z ^ j‖ ≤ 4 * Real.sqrt M := by
  induction t with
  | zero =>
    intro M hM z hz
    have hM01 : M = 0 ∨ M = 1 := by omega
    rcases hM01 with rfl | rfl
    · simp
    · simp [rsPcoeff_zero, rsQcoeff_zero]
  | succ t ih =>
    intro M hM z hz
    by_cases hle : M ≤ 2 ^ t
    · have hEqP : ∑ j ∈ range M, (rsPcoeff (t + 1) j : ℂ) * z ^ j =
          ∑ j ∈ range M, (rsPcoeff t j : ℂ) * z ^ j :=
        Finset.sum_congr rfl fun j hj => by
          rw [rsPcoeff_succ, if_pos (lt_of_lt_of_le (Finset.mem_range.mp hj) hle)]
      have hEqQ : ∑ j ∈ range M, (rsQcoeff (t + 1) j : ℂ) * z ^ j =
          ∑ j ∈ range M, (rsPcoeff t j : ℂ) * z ^ j :=
        Finset.sum_congr rfl fun j hj => by
          rw [rsQcoeff_succ, if_pos (lt_of_lt_of_le (Finset.mem_range.mp hj) hle)]
      rw [hEqP, hEqQ]
      exact ⟨(ih M hle z hz).1, (ih M hle z hz).1⟩
    · push Not at hle
      set r := M - 2 ^ t
      have hr : r ≤ 2 ^ t := by rw [pow_succ'] at hM; omega
      have hM_eq : M = 2 ^ t + r := by omega
      have hsplitP : ∑ j ∈ range M, (rsPcoeff (t + 1) j : ℂ) * z ^ j =
          rsP t z + z ^ (2 ^ t) * ∑ j ∈ range r, (rsQcoeff t j : ℂ) * z ^ j := by
        rw [hM_eq, Finset.sum_range_add, Finset.mul_sum]
        congr 1
        · unfold rsP
          refine Finset.sum_congr rfl fun j hj => by
            rw [rsPcoeff_succ, if_pos (Finset.mem_range.mp hj)]
        · refine Finset.sum_congr rfl fun j _ => by
            rw [rsPcoeff_succ, if_neg (by omega), Nat.add_sub_cancel_left, pow_add]; ring
      have hsplitQ : ∑ j ∈ range M, (rsQcoeff (t + 1) j : ℂ) * z ^ j =
          rsP t z - z ^ (2 ^ t) * ∑ j ∈ range r, (rsQcoeff t j : ℂ) * z ^ j := by
        rw [hM_eq, Finset.sum_range_add, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
        congr 1
        · unfold rsP
          refine Finset.sum_congr rfl fun j hj => by
            rw [rsQcoeff_succ, if_pos (Finset.mem_range.mp hj)]
        · refine Finset.sum_congr rfl fun j _ => by
            rw [rsQcoeff_succ, if_neg (by omega), Nat.add_sub_cancel_left, pow_add]; push_cast; ring
      have h1 : ‖rsP t z‖ ≤ Real.sqrt (2 * ((2 ^ t : ℕ) : ℝ)) := by
        have := rsP_norm_le t hz
        simpa [pow_succ'] using this
      have h2 : ‖z ^ (2 ^ t) * ∑ j ∈ range r, (rsQcoeff t j : ℂ) * z ^ j‖ ≤ 4 * Real.sqrt r := by
        rw [norm_mul, norm_pow, hz, one_pow, one_mul]
        exact (ih r hr z hz).2
      have hcomb : Real.sqrt (2 * ((2 ^ t : ℕ) : ℝ)) + 4 * Real.sqrt (r : ℝ) ≤ 4 * Real.sqrt (M : ℝ) := by
        set a : ℝ := ((2 ^ t : ℕ) : ℝ)
        set b : ℝ := (r : ℝ)
        have ha : 0 ≤ a := Nat.cast_nonneg _
        have hb : 0 ≤ b := Nat.cast_nonneg _
        have hba : b ≤ a := by dsimp only [a, b]; exact_mod_cast hr
        have hMab : (M : ℝ) = a + b := by dsimp only [a, b]; exact_mod_cast hM_eq
        rw [hMab]
        have hsq : (Real.sqrt (2 * a) + 4 * Real.sqrt b) ^ 2 ≤ (4 * Real.sqrt (a + b)) ^ 2 := by
          have h1s : Real.sqrt (2 * a) ^ 2 = 2 * a := Real.sq_sqrt (by positivity)
          have h2s : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
          have h3s : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt (by positivity)
          have hcross : (Real.sqrt (2 * a) * Real.sqrt b) ^ 2 ≤ (7 / 4 * a) ^ 2 := by
            rw [mul_pow, h1s, h2s]; nlinarith
          have hcross' : Real.sqrt (2 * a) * Real.sqrt b ≤ 7 / 4 * a := by
            nlinarith [Real.sqrt_nonneg (2 * a), Real.sqrt_nonneg b]
          nlinarith
        nlinarith [Real.sqrt_nonneg (2 * a), Real.sqrt_nonneg b, Real.sqrt_nonneg (a + b)]
      constructor
      · rw [hsplitP]; exact (norm_add_le _ _).trans (by linarith)
      · rw [hsplitQ]; exact (norm_sub_le _ _).trans (by linarith)

lemma rsSeq_partial_bound (M : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖∑ j ∈ range M, (rsSeq j : ℂ) * z ^ j‖ ≤ 4 * Real.sqrt M := by
  have hle : M ≤ 2 ^ M := Nat.le_of_lt Nat.lt_two_pow_self
  have heq : ∑ j ∈ range M, (rsSeq j : ℂ) * z ^ j =
      ∑ j ∈ range M, (rsPcoeff M j : ℂ) * z ^ j :=
    Finset.sum_congr rfl fun j hj => by
      rw [rsSeq_eq_rsPcoeff (lt_of_lt_of_le (Finset.mem_range.mp hj) hle)]
  rw [heq]
  exact (rs_partial_bound M M hle z hz).1

/-- Values of `rsP` and `rsQ` at `1` and `-1` for odd indices `2*r + 1`. -/
lemma rs_eval_pm_one (r : ℕ) :
    rsP (2 * r + 1) 1 = (2 : ℂ) ^ (r + 1) ∧ rsQ (2 * r + 1) 1 = 0 ∧
    rsP (2 * r + 1) (-1) = 0 ∧ rsQ (2 * r + 1) (-1) = (2 : ℂ) ^ (r + 1) := by
  induction r with
  | zero =>
    refine ⟨by simp [rsP_succ, rsQ_succ, rsP_zero, rsQ_zero]; norm_num, by simp [rsP_succ, rsQ_succ, rsP_zero, rsQ_zero], by simp [rsP_succ, rsQ_succ, rsP_zero, rsQ_zero], by simp [rsP_succ, rsQ_succ, rsP_zero, rsQ_zero]; norm_num⟩
  | succ r ih =>
    obtain ⟨hP1, hQ1, hPm1, hQm1⟩ := ih
    have heven : (-1 : ℂ) ^ (2 ^ (2 * r + 1)) = 1 := by
      have : Even (2 ^ (2 * r + 1)) := by
        rw [pow_succ']; exact even_two_mul _
      exact this.neg_one_pow
    have hP2 : rsP (2 * (r + 1)) 1 = (2 : ℂ) ^ (r + 1) := by
      rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega, rsP_succ, one_pow, one_mul, hP1, hQ1, add_zero]
    have hQ2 : rsQ (2 * (r + 1)) 1 = (2 : ℂ) ^ (r + 1) := by
      rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega, rsQ_succ, one_pow, one_mul, hP1, hQ1, sub_zero]
    have hPm2 : rsP (2 * (r + 1)) (-1) = (2 : ℂ) ^ (r + 1) := by
      rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega, rsP_succ, heven, one_mul, hPm1, hQm1, zero_add]
    have hQm2 : rsQ (2 * (r + 1)) (-1) = -((2 : ℂ) ^ (r + 1)) := by
      rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega, rsQ_succ, heven, one_mul, hPm1, hQm1, zero_sub]
    have heven2 : (-1 : ℂ) ^ (2 ^ (2 * (r + 1))) = 1 := by
      have : Even (2 ^ (2 * (r + 1))) := by
        rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega, pow_succ']; exact even_two_mul _
      exact this.neg_one_pow
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [rsP_succ, one_pow, one_mul, hP2, hQ2, pow_succ']; ring
    · rw [rsQ_succ, one_pow, one_mul, hP2, hQ2, sub_self]
    · rw [rsP_succ, heven2, one_mul, hPm2, hQm2, add_neg_cancel]
    · rw [rsQ_succ, heven2, one_mul, hPm2, hQm2, sub_neg_eq_add, pow_succ']; ring

/-! ### Section 2: Exact derivative bounds for Rudin-Shapiro via parallelogram induction -/

noncomputable def rsPd (k t : ℕ) (θ : ℝ) : ℂ :=
  ∑ j ∈ range (2 ^ t),
    (rsPcoeff t j : ℂ) * ((j : ℂ) * Complex.I) ^ k * Complex.exp ((j : ℂ) * (θ : ℂ) * Complex.I)

noncomputable def rsQd (k t : ℕ) (θ : ℝ) : ℂ :=
  ∑ j ∈ range (2 ^ t),
    (rsQcoeff t j : ℂ) * ((j : ℂ) * Complex.I) ^ k * Complex.exp ((j : ℂ) * (θ : ℂ) * Complex.I)

lemma rsPd_zero (t : ℕ) (θ : ℝ) : rsPd 0 t θ = rsP t (Complex.exp ((θ : ℂ) * Complex.I)) := by
  unfold rsPd rsP
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_zero, mul_one, ← Complex.exp_nat_mul]
  congr 2; ring

lemma rsQd_zero (t : ℕ) (θ : ℝ) : rsQd 0 t θ = rsQ t (Complex.exp ((θ : ℂ) * Complex.I)) := by
  unfold rsQd rsQ
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_zero, mul_one, ← Complex.exp_nat_mul]
  congr 2; ring

lemma hasDerivAt_rsPd (k t : ℕ) (θ : ℝ) : HasDerivAt (rsPd k t) (rsPd (k + 1) t θ) θ := by
  unfold rsPd
  have hterm : ∀ j ∈ range (2 ^ t),
      HasDerivAt (fun x : ℝ => (rsPcoeff t j : ℂ) * ((j : ℂ) * Complex.I) ^ k *
          Complex.exp ((j : ℂ) * (x : ℂ) * Complex.I))
        ((rsPcoeff t j : ℂ) * ((j : ℂ) * Complex.I) ^ (k + 1) *
          Complex.exp ((j : ℂ) * (θ : ℂ) * Complex.I)) θ := by
    intro j _
    have hlin : HasDerivAt (fun x : ℝ => (j : ℂ) * (x : ℂ) * Complex.I) ((j : ℂ) * Complex.I) θ := by
      have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) θ := Complex.ofRealCLM.hasDerivAt
      convert (hid.const_mul (j : ℂ)).mul_const Complex.I using 1; ring
    have hexp := (Complex.hasDerivAt_exp _).comp θ hlin
    exact (hexp.const_mul ((rsPcoeff t j : ℂ) * ((j : ℂ) * Complex.I) ^ k)).congr_deriv (by
      rw [pow_succ]; ring)
  exact HasDerivAt.fun_sum hterm

lemma hasDerivAt_rsQd (k t : ℕ) (θ : ℝ) : HasDerivAt (rsQd k t) (rsQd (k + 1) t θ) θ := by
  unfold rsQd
  have hterm : ∀ j ∈ range (2 ^ t),
      HasDerivAt (fun x : ℝ => (rsQcoeff t j : ℂ) * ((j : ℂ) * Complex.I) ^ k *
          Complex.exp ((j : ℂ) * (x : ℂ) * Complex.I))
        ((rsQcoeff t j : ℂ) * ((j : ℂ) * Complex.I) ^ (k + 1) *
          Complex.exp ((j : ℂ) * (θ : ℂ) * Complex.I)) θ := by
    intro j _
    have hlin : HasDerivAt (fun x : ℝ => (j : ℂ) * (x : ℂ) * Complex.I) ((j : ℂ) * Complex.I) θ := by
      have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) θ := Complex.ofRealCLM.hasDerivAt
      convert (hid.const_mul (j : ℂ)).mul_const Complex.I using 1; ring
    have hexp := (Complex.hasDerivAt_exp _).comp θ hlin
    exact (hexp.const_mul ((rsQcoeff t j : ℂ) * ((j : ℂ) * Complex.I) ^ k)).congr_deriv (by
      rw [pow_succ]; ring)
  exact HasDerivAt.fun_sum hterm

lemma rsPd_succ (k t : ℕ) (θ : ℝ) :
    rsPd k (t + 1) θ = rsPd k t θ +
      Complex.exp (((2 ^ t : ℕ) : ℂ) * (θ : ℂ) * Complex.I) *
        ∑ l ∈ range (k + 1), ((k.choose l : ℕ) : ℂ) *
          (((2 ^ t : ℕ) : ℂ) * Complex.I) ^ (k - l) * rsQd l t θ := by
  unfold rsPd rsQd
  rw [pow_succ', two_mul, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => by
      rw [rsPcoeff_succ, if_pos (Finset.mem_range.mp hj)]
  · have hswap :
        Complex.exp (((2 ^ t : ℕ) : ℂ) * (θ : ℂ) * Complex.I) *
          ∑ l ∈ range (k + 1), ((k.choose l : ℕ) : ℂ) *
            (((2 ^ t : ℕ) : ℂ) * Complex.I) ^ (k - l) *
            ∑ j ∈ range (2 ^ t),
              (rsQcoeff t j : ℂ) * ((j : ℂ) * Complex.I) ^ l *
                Complex.exp ((j : ℂ) * (θ : ℂ) * Complex.I) =
        ∑ j ∈ range (2 ^ t),
          (rsQcoeff t j : ℂ) *
            (∑ l ∈ range (k + 1), ((j : ℂ) * Complex.I) ^ l *
              (((2 ^ t : ℕ) : ℂ) * Complex.I) ^ (k - l) * (k.choose l : ℂ)) *
            (Complex.exp (((2 ^ t : ℕ) : ℂ) * (θ : ℂ) * Complex.I) *
              Complex.exp ((j : ℂ) * (θ : ℂ) * Complex.I)) := by
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => by ring
    rw [hswap]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rsPcoeff_succ, if_neg (by omega), Nat.add_sub_cancel_left, ← add_pow, ← Complex.exp_add]
    congr 1
    · congr 1; push_cast; ring
    · congr 1; push_cast; ring

lemma rsQd_succ (k t : ℕ) (θ : ℝ) :
    rsQd k (t + 1) θ = rsPd k t θ -
      Complex.exp (((2 ^ t : ℕ) : ℂ) * (θ : ℂ) * Complex.I) *
        ∑ l ∈ range (k + 1), ((k.choose l : ℕ) : ℂ) *
          (((2 ^ t : ℕ) : ℂ) * Complex.I) ^ (k - l) * rsQd l t θ := by
  unfold rsPd rsQd
  rw [pow_succ', two_mul, Finset.sum_range_add, sub_eq_add_neg]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => by
      rw [rsQcoeff_succ, if_pos (Finset.mem_range.mp hj)]
  · have hswap :
        -(Complex.exp (((2 ^ t : ℕ) : ℂ) * (θ : ℂ) * Complex.I) *
          ∑ l ∈ range (k + 1), ((k.choose l : ℕ) : ℂ) *
            (((2 ^ t : ℕ) : ℂ) * Complex.I) ^ (k - l) *
            ∑ j ∈ range (2 ^ t),
              (rsQcoeff t j : ℂ) * ((j : ℂ) * Complex.I) ^ l *
                Complex.exp ((j : ℂ) * (θ : ℂ) * Complex.I)) =
        ∑ j ∈ range (2 ^ t),
          (-(rsQcoeff t j : ℂ)) *
            (∑ l ∈ range (k + 1), ((j : ℂ) * Complex.I) ^ l *
              (((2 ^ t : ℕ) : ℂ) * Complex.I) ^ (k - l) * (k.choose l : ℂ)) *
            (Complex.exp (((2 ^ t : ℕ) : ℂ) * (θ : ℂ) * Complex.I) *
              Complex.exp ((j : ℂ) * (θ : ℂ) * Complex.I)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      simp_rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => by ring
    rw [hswap]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rsQcoeff_succ, if_neg (by omega), Nat.add_sub_cancel_left, ← add_pow, ← Complex.exp_add]
    congr 1
    · congr 1; push_cast; ring
    · congr 1; push_cast; ring

/-- Exact Bernstein-strength bound for all derivatives of Rudin-Shapiro polynomials,
proved directly by parallelogram-law induction. -/
theorem rs_deriv_norm_sq_le (k : ℕ) :
    ∀ t : ℕ, ∀ θ : ℝ, ‖rsPd k t θ‖ ^ 2 + ‖rsQd k t θ‖ ^ 2 ≤ (2 : ℝ) ^ (2 * k * t + t + 1) := by
  induction k using Nat.strong_induction_on with
  | ind k ihk =>
    intro t
    induction t with
    | zero =>
      intro θ
      cases k with
      | zero => simp [rsPd_zero, rsQd_zero, rsP_zero, rsQ_zero]; norm_num
      | succ k' => simp [rsPd, rsQd, rsPcoeff_zero, rsQcoeff_zero]
    | succ t iht =>
      intro θ
      rw [rsPd_succ, rsQd_succ, complex_parallelogram]
      have hexp_norm : ‖Complex.exp (((2 ^ t : ℕ) : ℂ) * (θ : ℂ) * Complex.I)‖ = 1 := by
        have : ((2 ^ t : ℕ) : ℂ) * (θ : ℂ) * Complex.I = ((((2 ^ t : ℕ) : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, hexp_norm, one_mul]
      -- Split `l = k` from `l < k` in the binomial sum.
      rw [Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, one_mul, one_mul]
      set R := ∑ l ∈ range k, ((k.choose l : ℕ) : ℂ) *
        (((2 ^ t : ℕ) : ℂ) * Complex.I) ^ (k - l) * rsQd l t θ
      have hR_le : ‖R‖ ≤ ((2 : ℝ) ^ k - 1) * (2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
        have hterm : ∀ l ∈ range k,
            ‖((k.choose l : ℕ) : ℂ) * (((2 ^ t : ℕ) : ℂ) * Complex.I) ^ (k - l) * rsQd l t θ‖ ≤
              (k.choose l : ℝ) * (2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
          intro l hl
          have hlk : l < k := Finset.mem_range.mp hl
          have hql_sq : ‖rsQd l t θ‖ ^ 2 ≤ (2 : ℝ) ^ (2 * l * t + t + 1) := by
            have := ihk l hlk t θ; nlinarith [sq_nonneg ‖rsPd l t θ‖]
          have hql : ‖rsQd l t θ‖ ≤ (2 : ℝ) ^ (l * t) * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
            have hsq : ((2 : ℝ) ^ (l * t) * Real.sqrt ((2 : ℝ) ^ (t + 1))) ^ 2 =
                (2 : ℝ) ^ (2 * l * t + t + 1) := by
              rw [mul_pow, ← pow_mul, Real.sq_sqrt (by positivity), ← pow_add]
              congr 1; ring
            nlinarith [norm_nonneg (rsQd l t θ),
              show (0 : ℝ) ≤ (2 : ℝ) ^ (l * t) * Real.sqrt ((2 : ℝ) ^ (t + 1)) by positivity]
          rw [norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_natCast, Complex.norm_natCast, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
          calc (k.choose l : ℝ) * (2 : ℝ) ^ (t * (k - l)) * ‖rsQd l t θ‖
              ≤ (k.choose l : ℝ) * (2 : ℝ) ^ (t * (k - l)) * ((2 : ℝ) ^ (l * t) * Real.sqrt ((2 : ℝ) ^ (t + 1))) :=
                mul_le_mul_of_nonneg_left hql (by positivity)
            _ = (k.choose l : ℝ) * ((2 : ℝ) ^ (t * (k - l)) * (2 : ℝ) ^ (l * t)) * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by ring
            _ = (k.choose l : ℝ) * (2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
                rw [← pow_add, show t * (k - l) + l * t = k * t by
                  have : l ≤ k := le_of_lt hlk
                  calc t * (k - l) + l * t = t * (k - l) + t * l := by ring
                    _ = t * (k - l + l) := by rw [← mul_add]
                    _ = t * k := by rw [Nat.sub_add_cancel this]
                    _ = k * t := by ring]
        calc ‖R‖ ≤ ∑ l ∈ range k, ‖((k.choose l : ℕ) : ℂ) *
              (((2 ^ t : ℕ) : ℂ) * Complex.I) ^ (k - l) * rsQd l t θ‖ := norm_sum_le _ _
          _ ≤ ∑ l ∈ range k, (k.choose l : ℝ) * (2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1)) :=
              Finset.sum_le_sum hterm
          _ = (∑ l ∈ range k, (k.choose l : ℝ)) * ((2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1))) := by
              rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun _ _ => by ring
          _ = ((2 : ℝ) ^ k - 1) * (2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
              have hch : ∑ l ∈ range k, (k.choose l : ℝ) = (2 : ℝ) ^ k - 1 := by
                have hfull : ∑ l ∈ range (k + 1), k.choose l = 2 ^ k := Nat.sum_range_choose k
                rw [Finset.sum_range_succ, Nat.choose_self] at hfull
                have hcast : (∑ l ∈ range k, (k.choose l : ℝ)) + 1 = (2 : ℝ) ^ k := by exact_mod_cast hfull
                linarith
              rw [hch]; ring
      have hqt_sq : ‖rsQd k t θ‖ ^ 2 ≤ (2 : ℝ) ^ (2 * k * t + t + 1) := by
        have := iht θ; nlinarith [sq_nonneg ‖rsPd k t θ‖]
      have hqt : ‖rsQd k t θ‖ ≤ (2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
        have hsq : ((2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1))) ^ 2 =
            (2 : ℝ) ^ (2 * k * t + t + 1) := by
          rw [mul_pow, ← pow_mul, Real.sq_sqrt (by positivity), ← pow_add]; congr 1; ring
        nlinarith [norm_nonneg (rsQd k t θ),
          show (0 : ℝ) ≤ (2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1)) by positivity]
      have htri : ‖R + rsQd k t θ‖ ^ 2 ≤ (‖rsQd k t θ‖ + ‖R‖) ^ 2 := by
        have h1 : ‖R + rsQd k t θ‖ ≤ ‖rsQd k t θ‖ + ‖R‖ := by
          rw [add_comm]; exact norm_add_le _ _
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      set M : ℝ := (2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1))
      have hM_sq : M ^ 2 = (2 : ℝ) ^ (2 * k * t + t + 1) := by
        dsimp only [M]; rw [mul_pow, ← pow_mul, Real.sq_sqrt (by positivity), ← pow_add]; congr 1; ring
      have hM_nn : 0 ≤ M := by positivity
      have h2k_ge : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      have hR_le' : ‖R‖ ≤ ((2 : ℝ) ^ k - 1) * M := by simpa [M, mul_assoc] using hR_le
      have hqt' : ‖rsQd k t θ‖ ≤ M := hqt
      have hcross : ‖rsQd k t θ‖ * ‖R‖ ≤ ((2 : ℝ) ^ k - 1) * M ^ 2 := by
        calc ‖rsQd k t θ‖ * ‖R‖ ≤ M * (((2 : ℝ) ^ k - 1) * M) :=
              mul_le_mul hqt' hR_le' (norm_nonneg _) hM_nn
          _ = ((2 : ℝ) ^ k - 1) * M ^ 2 := by ring
      have hRsq : ‖R‖ ^ 2 ≤ ((2 : ℝ) ^ k - 1) ^ 2 * M ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) hR_le' 2
        simpa [mul_pow] using this
      have hfinal : 2 * (‖rsPd k t θ‖ ^ 2 + ‖R + rsQd k t θ‖ ^ 2) ≤
          2 * ((2 : ℝ) ^ k) ^ 2 * M ^ 2 := by
        have hpq := iht θ
        rw [← hM_sq] at hpq
        nlinarith [htri, hcross, hRsq]
      calc 2 * (‖rsPd k t θ‖ ^ 2 + ‖R + rsQd k t θ‖ ^ 2)
          ≤ 2 * ((2 : ℝ) ^ k) ^ 2 * M ^ 2 := hfinal
        _ = (2 : ℝ) ^ (2 * k * (t + 1) + (t + 1) + 1) := by
            rw [hM_sq, ← pow_mul, mul_assoc, ← pow_add, ← pow_succ']
            congr 1; ring

/-! ### Section 3: Rescaled function `H(x)` and its derivatives -/

noncomputable def Halpha (t k : ℕ) (x : ℝ) : ℂ :=
  ((Real.sqrt ((2 : ℝ) ^ (t + 1)))⁻¹ * (((2 ^ (t + 10) : ℕ) : ℝ) ^ k)⁻¹ : ℝ) *
    rsPd k t (x / ((2 ^ (t + 10) : ℕ) : ℝ))

noncomputable def Hbeta (t k : ℕ) (x : ℝ) : ℂ :=
  ((Real.sqrt ((2 : ℝ) ^ (t + 1)))⁻¹ * (((2 ^ (t + 10) : ℕ) : ℝ) ^ k)⁻¹ : ℝ) *
    rsQd k t (x / ((2 ^ (t + 10) : ℕ) : ℝ))

lemma Halpha_norm_le (t k : ℕ) (x : ℝ) : ‖Halpha t k x‖ ≤ ((1 : ℝ) / 2) ^ (10 * k) := by
  unfold Halpha
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hpd_sq : ‖rsPd k t (x / ((2 ^ (t + 10) : ℕ) : ℝ))‖ ^ 2 ≤ (2 : ℝ) ^ (2 * k * t + t + 1) := by
    have := rs_deriv_norm_sq_le k t (x / ((2 ^ (t + 10) : ℕ) : ℝ))
    nlinarith [sq_nonneg ‖rsQd k t (x / ((2 ^ (t + 10) : ℕ) : ℝ))‖]
  have hpd : ‖rsPd k t (x / ((2 ^ (t + 10) : ℕ) : ℝ))‖ ≤
      (2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
    have hsq : ((2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1))) ^ 2 = (2 : ℝ) ^ (2 * k * t + t + 1) := by
      rw [mul_pow, ← pow_mul, Real.sq_sqrt (by positivity), ← pow_add]; congr 1; ring
    nlinarith [norm_nonneg (rsPd k t (x / ((2 ^ (t + 10) : ℕ) : ℝ))),
      show (0 : ℝ) ≤ (2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1)) by positivity]
  calc (Real.sqrt ((2 : ℝ) ^ (t + 1)))⁻¹ * (((2 ^ (t + 10) : ℕ) : ℝ) ^ k)⁻¹ *
        ‖rsPd k t (x / ((2 ^ (t + 10) : ℕ) : ℝ))‖
      ≤ (Real.sqrt ((2 : ℝ) ^ (t + 1)))⁻¹ * (((2 ^ (t + 10) : ℕ) : ℝ) ^ k)⁻¹ *
          ((2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1))) :=
        mul_le_mul_of_nonneg_left hpd (by positivity)
    _ = ((1 : ℝ) / 2) ^ (10 * k) := by
        have hsqrt_ne : Real.sqrt ((2 : ℝ) ^ (t + 1)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
        have hT : (((2 ^ (t + 10) : ℕ) : ℝ) ^ k) = (2 : ℝ) ^ (k * t) * (2 : ℝ) ^ (10 * k) := by
          push_cast; rw [← pow_mul, ← pow_add]; congr 1; ring
        rw [hT, one_div, inv_pow]
        field_simp [hsqrt_ne]

lemma Hbeta_norm_le (t k : ℕ) (x : ℝ) : ‖Hbeta t k x‖ ≤ ((1 : ℝ) / 2) ^ (10 * k) := by
  unfold Hbeta
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hqd_sq : ‖rsQd k t (x / ((2 ^ (t + 10) : ℕ) : ℝ))‖ ^ 2 ≤ (2 : ℝ) ^ (2 * k * t + t + 1) := by
    have := rs_deriv_norm_sq_le k t (x / ((2 ^ (t + 10) : ℕ) : ℝ))
    nlinarith [sq_nonneg ‖rsPd k t (x / ((2 ^ (t + 10) : ℕ) : ℝ))‖]
  have hqd : ‖rsQd k t (x / ((2 ^ (t + 10) : ℕ) : ℝ))‖ ≤
      (2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
    have hsq : ((2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1))) ^ 2 = (2 : ℝ) ^ (2 * k * t + t + 1) := by
      rw [mul_pow, ← pow_mul, Real.sq_sqrt (by positivity), ← pow_add]; congr 1; ring
    nlinarith [norm_nonneg (rsQd k t (x / ((2 ^ (t + 10) : ℕ) : ℝ))),
      show (0 : ℝ) ≤ (2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1)) by positivity]
  calc (Real.sqrt ((2 : ℝ) ^ (t + 1)))⁻¹ * (((2 ^ (t + 10) : ℕ) : ℝ) ^ k)⁻¹ *
        ‖rsQd k t (x / ((2 ^ (t + 10) : ℕ) : ℝ))‖
      ≤ (Real.sqrt ((2 : ℝ) ^ (t + 1)))⁻¹ * (((2 ^ (t + 10) : ℕ) : ℝ) ^ k)⁻¹ *
          ((2 : ℝ) ^ (k * t) * Real.sqrt ((2 : ℝ) ^ (t + 1))) :=
        mul_le_mul_of_nonneg_left hqd (by positivity)
    _ = ((1 : ℝ) / 2) ^ (10 * k) := by
        have hsqrt_ne : Real.sqrt ((2 : ℝ) ^ (t + 1)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
        have hT : (((2 ^ (t + 10) : ℕ) : ℝ) ^ k) = (2 : ℝ) ^ (k * t) * (2 : ℝ) ^ (10 * k) := by
          push_cast; rw [← pow_mul, ← pow_add]; congr 1; ring
        rw [hT, one_div, inv_pow]
        field_simp [hsqrt_ne]

lemma Halpha_sq_add_Hbeta_sq (t : ℕ) (x : ℝ) :
    ‖Halpha t 0 x‖ ^ 2 + ‖Hbeta t 0 x‖ ^ 2 = 1 := by
  unfold Halpha Hbeta
  rw [pow_zero, inv_one, mul_one, rsPd_zero, rsQd_zero, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow, mul_pow, ← mul_add,
    rs_norm_sq_sum t (Complex.norm_exp_ofReal_mul_I _), inv_pow, Real.sq_sqrt (by positivity)]
  field_simp

lemma hasDerivAt_Halpha (t k : ℕ) (x : ℝ) : HasDerivAt (Halpha t k) (Halpha t (k + 1) x) x := by
  unfold Halpha
  set T : ℝ := ((2 ^ (t + 10) : ℕ) : ℝ)
  have hdiv : HasDerivAt (fun y : ℝ => y / T) (1 / T) x := (hasDerivAt_id x).div_const T
  have hcomp := (hasDerivAt_rsPd k t (x / T)).scomp x hdiv
  exact (hcomp.const_mul (((Real.sqrt ((2 : ℝ) ^ (t + 1)))⁻¹ * (T ^ k)⁻¹ : ℝ) : ℂ)).congr_deriv (by
    rw [Complex.real_smul]; push_cast; rw [pow_succ (T : ℂ) k, mul_inv]; ring)

lemma hasDerivAt_Hbeta (t k : ℕ) (x : ℝ) : HasDerivAt (Hbeta t k) (Hbeta t (k + 1) x) x := by
  unfold Hbeta
  set T : ℝ := ((2 ^ (t + 10) : ℕ) : ℝ)
  have hdiv : HasDerivAt (fun y : ℝ => y / T) (1 / T) x := (hasDerivAt_id x).div_const T
  have hcomp := (hasDerivAt_rsQd k t (x / T)).scomp x hdiv
  exact (hcomp.const_mul (((Real.sqrt ((2 : ℝ) ^ (t + 1)))⁻¹ * (T ^ k)⁻¹ : ℝ) : ℂ)).congr_deriv (by
    rw [Complex.real_smul]; push_cast; rw [pow_succ (T : ℂ) k, mul_inv]; ring)

noncomputable def Hd (t k : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ range (k + 1), ((k.choose j : ℕ) : ℂ) *
    (Complex.I ^ (k - j) * Complex.exp ((x : ℂ) * Complex.I) * Halpha t j x +
     (2 * Complex.I) ^ (k - j) * Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t j x)

lemma Hd_zero (t : ℕ) (x : ℝ) :
    Hd t 0 x = Complex.exp ((x : ℂ) * Complex.I) * Halpha t 0 x +
      Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t 0 x := by
  simp [Hd]

lemma hasDerivAt_Hd (t k : ℕ) (x : ℝ) : HasDerivAt (Hd t k) (Hd t (k + 1) x) x := by
  -- Differentiate each summand and apply Pascal's identity `choose (k+1) j`.
  have he1 : HasDerivAt (fun y : ℝ => Complex.exp ((y : ℂ) * Complex.I))
      (Complex.I * Complex.exp ((x : ℂ) * Complex.I)) x := by
    have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) * Complex.I) Complex.I x := by
      have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := Complex.ofRealCLM.hasDerivAt
      exact (hid.mul_const Complex.I).congr_deriv (one_mul _)
    exact ((Complex.hasDerivAt_exp _).comp x hlin).congr_deriv (by ring)
  have he2 : HasDerivAt (fun y : ℝ => Complex.exp ((2 : ℂ) * (y : ℂ) * Complex.I))
      ((2 * Complex.I) * Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I)) x := by
    have hlin : HasDerivAt (fun y : ℝ => (2 : ℂ) * (y : ℂ) * Complex.I) (2 * Complex.I) x := by
      have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := Complex.ofRealCLM.hasDerivAt
      exact ((hid.const_mul (2 : ℂ)).mul_const Complex.I).congr_deriv (by ring)
    exact ((Complex.hasDerivAt_exp _).comp x hlin).congr_deriv (by ring)
  have hsum : HasDerivAt (Hd t k)
      (∑ j ∈ range (k + 1), ((k.choose j : ℕ) : ℂ) *
        ((Complex.I ^ (k - j + 1) * Complex.exp ((x : ℂ) * Complex.I) * Halpha t j x +
          Complex.I ^ (k - j) * Complex.exp ((x : ℂ) * Complex.I) * Halpha t (j + 1) x) +
         ((2 * Complex.I) ^ (k - j + 1) * Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t j x +
          (2 * Complex.I) ^ (k - j) * Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t (j + 1) x))) x := by
    unfold Hd
    apply HasDerivAt.fun_sum
    intro j _
    have ha := (he1.const_mul (Complex.I ^ (k - j))).mul (hasDerivAt_Halpha t j x)
    have hb := (he2.const_mul ((2 * Complex.I) ^ (k - j))).mul (hasDerivAt_Hbeta t j x)
    convert (ha.add hb).const_mul ((k.choose j : ℕ) : ℂ) using 1
    rw [pow_succ, pow_succ]; ring
  convert hsum using 1
  -- Match the Pascal sum `∑_{j=0}^{k+1} C(k+1, j) T(j)` with `∑_{j=0}^k C(k, j) (T_left(j) + T_right(j+1))`.
  let f : ℕ → ℂ := fun j =>
    Complex.I ^ (k + 1 - j) * Complex.exp ((x : ℂ) * Complex.I) * Halpha t j x +
    (2 * Complex.I) ^ (k + 1 - j) * Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t j x
  change ∑ j ∈ range (k + 2), ((Nat.choose (k + 1) j : ℕ) : ℂ) * f j = _
  rw [Finset.sum_range_succ', Nat.choose_zero_right, Nat.cast_one, one_mul]
  have hrhs : ∑ j ∈ range (k + 1), ((k.choose j : ℕ) : ℂ) *
      ((Complex.I ^ (k - j + 1) * Complex.exp ((x : ℂ) * Complex.I) * Halpha t j x +
        Complex.I ^ (k - j) * Complex.exp ((x : ℂ) * Complex.I) * Halpha t (j + 1) x) +
       ((2 * Complex.I) ^ (k - j + 1) * Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t j x +
        (2 * Complex.I) ^ (k - j) * Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t (j + 1) x)) =
      (∑ j ∈ range (k + 1), ((k.choose j : ℕ) : ℂ) * f j) +
      (∑ j ∈ range (k + 1), ((k.choose j : ℕ) : ℂ) * f (j + 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsub1 : k + 1 - j = k - j + 1 := by omega
    have hsub2 : k + 1 - (j + 1) = k - j := by omega
    dsimp only [f]
    rw [hsub1, hsub2]; ring
  rw [hrhs]
  have h1 : ∑ j ∈ range (k + 1), ((Nat.choose (k + 1) (j + 1) : ℕ) : ℂ) * f (j + 1) =
      (∑ j ∈ range (k + 1), ((k.choose j : ℕ) : ℂ) * f (j + 1)) +
      (∑ j ∈ range (k + 1), ((k.choose (j + 1) : ℕ) : ℂ) * f (j + 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.choose_succ_succ]; push_cast; ring
  rw [h1]
  have hshift : ∑ j ∈ range (k + 1), ((k.choose j : ℕ) : ℂ) * f j =
      f 0 + ∑ j ∈ range (k + 1), ((k.choose (j + 1) : ℕ) : ℂ) * f (j + 1) := by
    rw [Finset.sum_range_succ' (fun j => ((k.choose j : ℕ) : ℂ) * f j) k,
      Nat.choose_zero_right, Nat.cast_one, one_mul,
      Finset.sum_range_succ (fun j => ((k.choose (j + 1) : ℕ) : ℂ) * f (j + 1)) k,
      Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, add_zero, add_comm]
  rw [hshift]; ring

lemma Hd_approx_and_bound (t k : ℕ) (hk : k ≤ 4) (x : ℝ) :
    ‖Hd t k x - (Complex.I ^ k * Complex.exp ((x : ℂ) * Complex.I) * Halpha t 0 x +
      (2 * Complex.I) ^ k * Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t 0 x)‖ ≤ 1 / 8 ∧
    ‖Hd t k x‖ ≤ (2 : ℝ) ^ k + 2 := by
  have hmain_norm : ‖Complex.I ^ k * Complex.exp ((x : ℂ) * Complex.I) * Halpha t 0 x +
      (2 * Complex.I) ^ k * Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t 0 x‖ ≤ 1 + (2 : ℝ) ^ k := by
    have he1 : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I x
    have he2 : ‖Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I)‖ = 1 := by
      have : (2 : ℂ) * (x : ℂ) * Complex.I = (((2 * x : ℝ) : ℂ) * Complex.I) := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have ha0 : ‖Halpha t 0 x‖ ≤ 1 := by simpa using Halpha_norm_le t 0 x
    have hb0 : ‖Hbeta t 0 x‖ ≤ 1 := by simpa using Hbeta_norm_le t 0 x
    calc ‖Complex.I ^ k * Complex.exp ((x : ℂ) * Complex.I) * Halpha t 0 x +
          (2 * Complex.I) ^ k * Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t 0 x‖
        ≤ ‖Complex.I ^ k * Complex.exp ((x : ℂ) * Complex.I) * Halpha t 0 x‖ +
          ‖(2 * Complex.I) ^ k * Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t 0 x‖ := norm_add_le _ _
      _ ≤ 1 + (2 : ℝ) ^ k := by
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, he1, one_mul, one_mul,
            norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one,
            he2, mul_one]
          have : (2 : ℝ) ^ k * ‖Hbeta t 0 x‖ ≤ (2 : ℝ) ^ k * 1 :=
            mul_le_mul_of_nonneg_left hb0 (by positivity)
          linarith
  have hdiff : ‖Hd t k x - (Complex.I ^ k * Complex.exp ((x : ℂ) * Complex.I) * Halpha t 0 x +
      (2 * Complex.I) ^ k * Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t 0 x)‖ ≤ 1 / 8 := by
    unfold Hd
    rw [Finset.sum_range_succ', Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul, add_sub_cancel_right]
    have he1 : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I x
    have he2 : ‖Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I)‖ = 1 := by
      have : (2 : ℂ) * (x : ℂ) * Complex.I = (((2 * x : ℝ) : ℂ) * Complex.I) := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hterm : ∀ j ∈ range k,
        ‖((k.choose (j + 1) : ℕ) : ℂ) *
          (Complex.I ^ (k - (j + 1)) * Complex.exp ((x : ℂ) * Complex.I) * Halpha t (j + 1) x +
           (2 * Complex.I) ^ (k - (j + 1)) * Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t (j + 1) x)‖
          ≤ (k.choose (j + 1) : ℝ) * ((1 + (2 : ℝ) ^ (k - (j + 1))) * (1 / 1024 : ℝ)) := by
      intro j _
      rw [norm_mul, Complex.norm_natCast]
      have hdec : ((1 : ℝ) / 2) ^ (10 * (j + 1)) ≤ (1 / 1024 : ℝ) := by
        have h10 : 10 ≤ 10 * (j + 1) := by omega
        calc ((1 : ℝ) / 2) ^ (10 * (j + 1)) ≤ ((1 : ℝ) / 2) ^ 10 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) h10
          _ = 1 / 1024 := by norm_num
      have ha := (Halpha_norm_le t (j + 1) x).trans hdec
      have hb := (Hbeta_norm_le t (j + 1) x).trans hdec
      have hsum_norm :
          ‖Complex.I ^ (k - (j + 1)) * Complex.exp ((x : ℂ) * Complex.I) * Halpha t (j + 1) x +
           (2 * Complex.I) ^ (k - (j + 1)) * Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t (j + 1) x‖
            ≤ (1 + (2 : ℝ) ^ (k - (j + 1))) * (1 / 1024 : ℝ) := by
        calc _ ≤ ‖Complex.I ^ (k - (j + 1)) * Complex.exp ((x : ℂ) * Complex.I) * Halpha t (j + 1) x‖ +
              ‖(2 * Complex.I) ^ (k - (j + 1)) * Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t (j + 1) x‖ :=
              norm_add_le _ _
          _ ≤ 1 * (1 / 1024 : ℝ) + (2 : ℝ) ^ (k - (j + 1)) * (1 / 1024 : ℝ) := by
              rw [norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, he1, one_mul, one_mul,
                norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_I,
                mul_one, he2, mul_one]
              have : (2 : ℝ) ^ (k - (j + 1)) * ‖Hbeta t (j + 1) x‖ ≤
                  (2 : ℝ) ^ (k - (j + 1)) * (1 / 1024 : ℝ) :=
                mul_le_mul_of_nonneg_left hb (by positivity)
              linarith
          _ = (1 + (2 : ℝ) ^ (k - (j + 1))) * (1 / 1024 : ℝ) := by ring
      exact mul_le_mul_of_nonneg_left hsum_norm (Nat.cast_nonneg _)
    calc ‖∑ j ∈ range k, ((k.choose (j + 1) : ℕ) : ℂ) * _‖
        ≤ ∑ j ∈ range k, ‖((k.choose (j + 1) : ℕ) : ℂ) * _‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range k, (k.choose (j + 1) : ℝ) * ((1 + (2 : ℝ) ^ (k - (j + 1))) * (1 / 1024 : ℝ)) :=
          Finset.sum_le_sum hterm
      _ ≤ 1 / 8 := by
          interval_cases k <;> simp [Finset.sum_range_succ, Nat.choose] <;> norm_num
  refine ⟨hdiff, ?_⟩
  have htri := norm_le_norm_sub_add (Hd t k x)
    (Complex.I ^ k * Complex.exp ((x : ℂ) * Complex.I) * Halpha t 0 x +
     (2 * Complex.I) ^ k * Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t 0 x)
  linarith

/-- BBMST Lemma 3.4: `Re(H)` and its first three derivatives cannot all be `< 1/4`. -/
lemma H_deriv_lbounds (t : ℕ) (x : ℝ) :
    1 / 4 ≤ |(Hd t 0 x).re| ∨ 1 / 4 ≤ |(Hd t 1 x).re| ∨
    1 / 4 ≤ |(Hd t 2 x).re| ∨ 1 / 4 ≤ |(Hd t 3 x).re| := by
  by_contra! h
  obtain ⟨h0, h1, h2, h3⟩ := h
  set u := Complex.exp ((x : ℂ) * Complex.I) * Halpha t 0 x
  set v := Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I) * Hbeta t 0 x
  let E (k : ℕ) : ℝ := (Complex.I ^ k * u + (2 * Complex.I) ^ k * v).re
  have hE : ∀ k ≤ 3, |E k| ≤ 3 / 8 := by
    intro k hk
    have hdiff := (Hd_approx_and_bound t k (by omega) x).1
    have hre : |(Hd t k x).re - E k| ≤ 1 / 8 := by
      have : (Hd t k x - (Complex.I ^ k * u + (2 * Complex.I) ^ k * v)).re = (Hd t k x).re - E k := rfl
      rw [← this]
      have hdiff' : ‖Hd t k x - (Complex.I ^ k * u + (2 * Complex.I) ^ k * v)‖ ≤ 1 / 8 := by
        dsimp only [u, v]; rw [← mul_assoc, ← mul_assoc]; exact hdiff
      exact (Complex.abs_re_le_norm _).trans hdiff'
    have hlt : |(Hd t k x).re| < 1 / 4 := by
      match k with
      | 0 => exact h0
      | 1 => exact h1
      | 2 => exact h2
      | 3 => exact h3
      | _ + 4 => omega
    have htri : |E k| ≤ |(Hd t k x).re| + |(Hd t k x).re - E k| := by
      have h1 := abs_sub_abs_le_abs_sub (E k) (Hd t k x).re
      rw [abs_sub_comm] at h1
      linarith only [h1]
    linarith only [htri, hlt, hre]
  have hE0 : E 0 = u.re + v.re := by simp [E]
  have hE1 : E 1 = -u.im - 2 * v.im := by simp [E]; ring
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  have hE2 : E 2 = -u.re - 4 * v.re := by
    dsimp only [E]
    rw [mul_pow, hI2]
    have h22 : (2 : ℂ) ^ 2 = 4 := by norm_num
    rw [h22, Complex.add_re]; simp; ring
  have hE3 : E 3 = u.im + 8 * v.im := by
    dsimp only [E]
    rw [mul_pow, hI3]
    have h23 : (2 : ℂ) ^ 3 = 8 := by norm_num
    rw [h23, Complex.add_re]; simp
  have hu_re : u.re = (4 * E 0 + E 2) / 3 := by linarith only [hE0, hE2]
  have hv_re : v.re = -(E 0 + E 2) / 3 := by linarith only [hE0, hE2]
  have hu_im : u.im = -(4 * E 1 + E 3) / 3 := by linarith only [hE1, hE3]
  have hv_im : v.im = (E 1 + E 3) / 6 := by linarith only [hE1, hE3]
  have hnorm1 : u.re ^ 2 + u.im ^ 2 + v.re ^ 2 + v.im ^ 2 = 1 := by
    have he1 : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I x
    have he2 : ‖Complex.exp ((2 : ℂ) * (x : ℂ) * Complex.I)‖ = 1 := by
      have : (2 : ℂ) * (x : ℂ) * Complex.I = (((2 * x : ℝ) : ℂ) * Complex.I) := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hu_sq : u.re ^ 2 + u.im ^ 2 = ‖Halpha t 0 x‖ ^ 2 := by
      have : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by simp [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [← this, norm_mul, he1, one_mul]
    have hv_sq : v.re ^ 2 + v.im ^ 2 = ‖Hbeta t 0 x‖ ^ 2 := by
      have : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by simp [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [← this, norm_mul, he2, one_mul]
    linarith [Halpha_sq_add_Hbeta_sq t x]
  have hb0 := abs_le.mp (hE 0 (by omega))
  have hb1 := abs_le.mp (hE 1 (by omega))
  have hb2 := abs_le.mp (hE 2 (by omega))
  have hb3 := abs_le.mp (hE 3 (by omega))
  have h1s : u.re ^ 2 ≤ (5 * (3 / 8) / 3) ^ 2 := by
    have : |u.re| ≤ 5 * (3 / 8) / 3 := by rw [hu_re, abs_le]; constructor <;> linarith only [hb0.1, hb0.2, hb2.1, hb2.2]
    nlinarith only [this, sq_abs u.re, abs_nonneg u.re]
  have h2s : u.im ^ 2 ≤ (5 * (3 / 8) / 3) ^ 2 := by
    have : |u.im| ≤ 5 * (3 / 8) / 3 := by rw [hu_im, abs_le]; constructor <;> linarith only [hb1.1, hb1.2, hb3.1, hb3.2]
    nlinarith only [this, sq_abs u.im, abs_nonneg u.im]
  have h3s : v.re ^ 2 ≤ (2 * (3 / 8) / 3) ^ 2 := by
    have : |v.re| ≤ 2 * (3 / 8) / 3 := by rw [hv_re, abs_le]; constructor <;> linarith only [hb0.1, hb0.2, hb2.1, hb2.2]
    nlinarith only [this, sq_abs v.re, abs_nonneg v.re]
  have h4s : v.im ^ 2 ≤ (2 * (3 / 8) / 6) ^ 2 := by
    have : |v.im| ≤ 2 * (3 / 8) / 6 := by rw [hv_im, abs_le]; constructor <;> linarith only [hb1.1, hb1.2, hb3.1, hb3.2]
    nlinarith only [this, sq_abs v.im, abs_nonneg v.im]
  linarith only [hnorm1, h1s, h2s, h3s, h4s]

/-! ### Section 4: Rolle's theorem divided-difference bound & `intervals_nice` -/

private lemma prod_le_prod_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul (hfg a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hfg i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (le_trans (hf a (Finset.mem_insert_self _ _)) (hfg a (Finset.mem_insert_self _ _)))

private lemma poly_eval_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ) (x : ℝ) :
    (∑ i ∈ s, f i).eval x = ∑ i ∈ s, (f i).eval x :=
  map_sum (Polynomial.evalRingHom x) f s

private lemma poly_coeff_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ) (k : ℕ) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k :=
  map_sum (Polynomial.lcoeff ℝ k) f s

lemma rolle_iter (k : ℕ) :
    ∀ (g : ℕ → ℝ → ℝ),
      (∀ r < k, ∀ x, HasDerivAt (g r) (g (r + 1) x) x) →
      ∀ (y : Fin (k + 1) → ℝ), StrictMono y → (∀ i, g 0 (y i) = 0) →
      ∃ ξ, y 0 ≤ ξ ∧ ξ ≤ y (Fin.last k) ∧ g k ξ = 0 := by
  induction k with
  | zero =>
    intro g _ y _ hy0
    exact ⟨y 0, le_rfl, le_rfl, hy0 0⟩
  | succ k ih =>
    intro g hg y hy_mono hy0
    have hex : ∀ i : Fin (k + 1), ∃ z, y i.castSucc < z ∧ z < y i.succ ∧ g 1 z = 0 := by
      intro i
      have hlt : y i.castSucc < y i.succ := hy_mono Fin.castSucc_lt_succ
      have hcont : ContinuousOn (g 0) (Set.Icc (y i.castSucc) (y i.succ)) :=
        fun x _ => (hg 0 (by omega) x).continuousAt.continuousWithinAt
      have heq : g 0 (y i.castSucc) = g 0 (y i.succ) := by rw [hy0, hy0]
      obtain ⟨z, ⟨hz1, hz2⟩, hz_deriv⟩ := exists_deriv_eq_zero hlt hcont heq
      rw [(hg 0 (by omega) z).deriv] at hz_deriv
      exact ⟨z, hz1, hz2, hz_deriv⟩
    choose z hz_lo hz_hi hz0 using hex
    have hz_mono : StrictMono z := by
      intro i j hij
      have h1 : z i < y i.succ := hz_hi i
      have h2 : y i.succ ≤ y j.castSucc := hy_mono.monotone (by
        rw [Fin.le_def]; simp; exact hij)
      have h3 : y j.castSucc < z j := hz_lo j
      linarith
    obtain ⟨ξ, hξ1, hξ2, hξ0⟩ := ih (fun r => g (r + 1)) (fun r hr => hg (r + 1) (by omega)) z hz_mono hz0
    refine ⟨ξ, ?_, ?_, hξ0⟩
    · exact le_trans (le_of_lt (hz_lo 0)) hξ1
    · exact le_trans hξ2 (le_of_lt (hz_hi (Fin.last k)))

/-- Lagrange interpolation `k`-th derivative bound for `k ∈ {1, 2, 3}` via Rolle + MVT. -/
lemma deriv_bound_from_samples (f : ℕ → ℝ → ℝ) (hf : ∀ r ≤ 3, ∀ x, HasDerivAt (f r) (f (r + 1) x) x)
    {a η : ℝ} (hη : 0 < η) (x : Fin 7 → ℝ)
    (hx_lo : ∀ j : Fin 7, a + (j.val : ℝ) * η ≤ x j)
    (hx_hi : ∀ j : Fin 7, x j ≤ a + ((j.val : ℝ) + 1) * η)
    (B : ℝ) (hB : ∀ j : Fin 7, |f 0 (x j)| ≤ B)
    (M : ℕ → ℝ) (hM : ∀ r ≤ 4, ∀ u, |f r u| ≤ M r)
    (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
    |f k (x 0)| ≤ ((k + 1).factorial : ℝ) * B / η ^ k + 7 * η * M (k + 1) := by
  -- Use `y i = x (2*i)` for `i : Fin (k + 1)`; pairwise separation is `≥ η`.
  let y : Fin (k + 1) → ℝ := fun i => x ⟨2 * i.val, by omega⟩
  have hy_sep : ∀ i j : Fin (k + 1), i < j → η ≤ y j - y i := by
    intro i j hij
    have h1 := hx_hi ⟨2 * i.val, by omega⟩
    have h2 := hx_lo ⟨2 * j.val, by omega⟩
    simp only at h1 h2
    have hlt : ((2 * i.val : ℕ) : ℝ) + 2 ≤ ((2 * j.val : ℕ) : ℝ) := by
      have : 2 * i.val + 2 ≤ 2 * j.val := by omega
      exact_mod_cast this
    have hmul := mul_le_mul_of_nonneg_right hlt hη.le
    dsimp only [y]; linarith only [h1, h2, hmul]
  have hy_mono : StrictMono y := fun i j hij => by linarith [hy_sep i j hij]
  have hy_abs_sep : ∀ i j : Fin (k + 1), i ≠ j → η ≤ |y i - y j| := by
    intro i j hne
    rcases lt_or_gt_of_ne hne with h | h
    · rw [abs_sub_comm, abs_of_pos (by linarith [hy_sep i j h])]; exact hy_sep i j h
    · rw [abs_of_pos (by linarith [hy_sep j i h])]; exact hy_sep j i h
  -- Define the degree-`k` Lagrange interpolant `L` as a polynomial in `Polynomial ℝ`.
  let basis (i : Fin (k + 1)) : Polynomial ℝ :=
    ∏ j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i,
      Polynomial.C ((y i - y j)⁻¹) * (Polynomial.X - Polynomial.C (y j))
  let L : Polynomial ℝ := ∑ i : Fin (k + 1), Polynomial.C (f 0 (y i)) * basis i
  have hL_eval : ∀ i : Fin (k + 1), L.eval (y i) = f 0 (y i) := by
    intro i
    simp only [L, poly_eval_sum, Polynomial.eval_mul, Polynomial.eval_C]
    rw [Finset.sum_eq_single i]
    · have hb : (basis i).eval (y i) = 1 := by
        simp only [basis, Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X]
        refine Finset.prod_eq_one fun j hj => ?_
        have hne : y i - y j ≠ 0 := by
          have := hy_abs_sep i j (Finset.mem_erase.mp hj).1.symm
          intro h0; rw [h0, abs_zero] at this; linarith
        exact inv_mul_cancel₀ hne
      rw [hb, mul_one]
    · intro j _ hji
      have hb0 : (basis j).eval (y i) = 0 := by
        simp only [basis, Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X]
        exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ _⟩) (by simp)
      rw [hb0, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- Apply `rolle_iter` to `g r u = f r u - (derivative^[r] L).eval u`.
  let g : ℕ → ℝ → ℝ := fun r u => f r u - (Polynomial.derivative^[r] L).eval u
  have hg_deriv : ∀ r < k, ∀ u, HasDerivAt (g r) (g (r + 1) u) u := by
    intro r hr u
    have hf' := hf r (by omega) u
    have hL' : HasDerivAt (fun t => (Polynomial.derivative^[r] L).eval t)
        ((Polynomial.derivative^[r + 1] L).eval u) u := by
      rw [Function.iterate_succ_apply']
      exact Polynomial.hasDerivAt _ u
    exact hf'.sub hL'
  obtain ⟨ξ, hξ_lo, hξ_hi, hξ_zero⟩ := rolle_iter k g hg_deriv y hy_mono
    (fun i => by dsimp [g]; rw [hL_eval]; ring)
  have hfξ : f k ξ = (Polynomial.derivative^[k] L).eval ξ := by
    dsimp only [g] at hξ_zero; linarith
  -- Compute `(derivative^[k] L).eval ξ` using `coeff k`: for degree ≤ k, `derivative^[k] P = C (k! * P.coeff k)`.
  have hdeg_basis : ∀ i : Fin (k + 1), (basis i).natDegree ≤ k := by
    intro i
    dsimp only [basis]
    calc (∏ j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i,
            (Polynomial.C ((y i - y j)⁻¹) * (Polynomial.X - Polynomial.C (y j)))).natDegree
        ≤ ∑ j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i,
            (Polynomial.C ((y i - y j)⁻¹) * (Polynomial.X - Polynomial.C (y j))).natDegree :=
          Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i, 1 := by
          refine Finset.sum_le_sum fun j _ => ?_
          calc (Polynomial.C ((y i - y j)⁻¹) * (Polynomial.X - Polynomial.C (y j))).natDegree
              ≤ (Polynomial.C ((y i - y j)⁻¹)).natDegree + (Polynomial.X - Polynomial.C (y j)).natDegree :=
                Polynomial.natDegree_mul_le
            _ ≤ 0 + 1 := by simp
            _ = 1 := zero_add 1
      _ = k := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
            Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, Nat.add_sub_cancel]
  have hdeg_L : L.natDegree ≤ k := by
    dsimp only [L]
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le k, fun i _ => ?_⟩
    exact Polynomial.natDegree_C_mul_le _ _ |>.trans (hdeg_basis i)
  have hderiv_k_eq : (Polynomial.derivative^[k] L).eval ξ = (k.factorial : ℝ) * L.coeff k := by
    have hcoeff : ∀ P : Polynomial ℝ, P.natDegree ≤ k →
        (Polynomial.derivative^[k] P).eval ξ = (k.factorial : ℝ) * P.coeff k := by
      intro P hP
      have hdeg0 : (Polynomial.derivative^[k] P).natDegree = 0 := by
        have := Polynomial.natDegree_iterate_derivative P k
        omega
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0, Polynomial.eval_C,
        Polynomial.coeff_iterate_derivative, zero_add, Nat.descFactorial_self, nsmul_eq_mul]
    exact hcoeff L hdeg_L
  -- Compute `L.coeff k = ∑ i, f 0 (y i) * ∏_{j ≠ i} (y i - y j)⁻¹`.
  have hcoeff_basis : ∀ i : Fin (k + 1),
      (basis i).coeff k = ∏ j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i, (y i - y j)⁻¹ := by
    intro i
    dsimp only [basis]
    have hfactor : ∏ j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i,
        (Polynomial.C ((y i - y j)⁻¹) * (Polynomial.X - Polynomial.C (y j))) =
        Polynomial.C (∏ j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i, (y i - y j)⁻¹) *
        ∏ j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i, (Polynomial.X - Polynomial.C (y j)) := by
      rw [Finset.prod_mul_distrib, map_prod]
    rw [hfactor, Polynomial.coeff_C_mul]
    have hmonic : (∏ j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i,
        (Polynomial.X - Polynomial.C (y j))).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _
    have hdeg_monic : (∏ j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i,
        (Polynomial.X - Polynomial.C (y j))).natDegree = k := by
      rw [Polynomial.natDegree_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _]
      simp
    have hlead : (∏ j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i,
        (Polynomial.X - Polynomial.C (y j))).coeff k = 1 := by
      have h1 := hmonic.leadingCoeff
      rw [Polynomial.leadingCoeff, hdeg_monic] at h1
      exact h1
    rw [hlead, mul_one]
  have hL_bound : |(Polynomial.derivative^[k] L).eval ξ| ≤ ((k + 1).factorial : ℝ) * B / η ^ k := by
    rw [hderiv_k_eq]
    have hLcoeff : L.coeff k = ∑ i : Fin (k + 1),
        f 0 (y i) * ∏ j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i, (y i - y j)⁻¹ := by
      simp only [L, poly_coeff_sum, Polynomial.coeff_C_mul, hcoeff_basis]
    rw [hLcoeff, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have hsum_le : |∑ i : Fin (k + 1),
        f 0 (y i) * ∏ j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i, (y i - y j)⁻¹| ≤
        ((k + 1 : ℕ) : ℝ) * (B / η ^ k) := by
      calc |∑ i : Fin (k + 1), _|
          ≤ ∑ i : Fin (k + 1), |f 0 (y i) * ∏ j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i, (y i - y j)⁻¹| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin (k + 1), (B / η ^ k) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [abs_mul, Finset.abs_prod]
            have hprod_le : ∏ j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i, |(y i - y j)⁻¹| ≤ (η ^ k)⁻¹ := by
              calc ∏ j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i, |(y i - y j)⁻¹|
                  ≤ ∏ _j ∈ (Finset.univ : Finset (Fin (k + 1))).erase i, η⁻¹ := by
                    refine prod_le_prod_nonneg _ _ _ (fun _ _ => abs_nonneg _) fun j hj => ?_
                    rw [abs_inv]
                    exact inv_anti₀ hη (hy_abs_sep i j (Finset.mem_erase.mp hj).1.symm)
                _ = (η ^ k)⁻¹ := by simp
            have hfi : |f 0 (y i)| ≤ B := hB ⟨2 * i.val, by omega⟩
            rw [div_eq_mul_inv]
            exact mul_le_mul hfi hprod_le (Finset.prod_nonneg fun _ _ => abs_nonneg _) (le_trans (abs_nonneg _) hfi)
        _ = ((k + 1 : ℕ) : ℝ) * (B / η ^ k) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (k.factorial : ℝ) * |∑ i : Fin (k + 1), _|
        ≤ (k.factorial : ℝ) * (((k + 1 : ℕ) : ℝ) * (B / η ^ k)) :=
          mul_le_mul_of_nonneg_left hsum_le (Nat.cast_nonneg _)
      _ = ((k + 1).factorial : ℝ) * B / η ^ k := by
          rw [Nat.factorial_succ]; push_cast; ring
  -- Mean Value Theorem between `x 0` and `ξ` (both lie in `[a, a + 7η]`, so `|x 0 - ξ| ≤ 7η`).
  have hdist : |x 0 - ξ| ≤ 7 * η := by
    have hx0_lo : a ≤ x 0 := by simpa using hx_lo 0
    have hx0_hi : x 0 ≤ a + 7 * η := by
      have := hx_hi 0; simp at this; linarith
    have hξ_a : a ≤ ξ := le_trans hx0_lo hξ_lo
    have hξ_b : ξ ≤ a + 7 * η := by
      have hlast := hx_hi ⟨2 * k, by omega⟩
      simp only at hlast
      have h2k : ((2 * k : ℕ) : ℝ) + 1 ≤ 7 := by
        have : 2 * k + 1 ≤ 7 := by omega
        exact_mod_cast this
      have : y (Fin.last k) ≤ a + 7 * η := by
        dsimp only [y]; simp only [Fin.val_last]; nlinarith
      exact le_trans hξ_hi this
    rw [abs_le]; constructor <;> linarith
  have hmvt : |f k (x 0) - f k ξ| ≤ M (k + 1) * |x 0 - ξ| := by
    have hlip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f k) (f' := f (k + 1)) (s := Set.univ) (C := M (k + 1))
      (fun u _ => (hf k hk3 u).hasDerivWithinAt)
      (fun u _ => by simpa [Real.norm_eq_abs] using hM (k + 1) (by omega) u)
      convex_univ (Set.mem_univ ξ) (Set.mem_univ (x 0))
    simpa [Real.norm_eq_abs] using hlip
  have hMnn : 0 ≤ M (k + 1) := le_trans (abs_nonneg _) (hM (k + 1) (by omega) 0)
  have hmvt' : |f k (x 0) - f k ξ| ≤ 7 * η * M (k + 1) := by
    calc |f k (x 0) - f k ξ| ≤ M (k + 1) * |x 0 - ξ| := hmvt
      _ ≤ M (k + 1) * (7 * η) := mul_le_mul_of_nonneg_left hdist hMnn
      _ = 7 * η * M (k + 1) := by ring
  have htri : |f k (x 0)| ≤ |f k (x 0) - f k ξ| + |f k ξ| := by
    have := abs_add_le (f k (x 0) - f k ξ) (f k ξ)
    simpa using this
  rw [← hfξ] at hL_bound
  linarith

/-- BBMST Lemma 3.3: Among any 7 consecutive intervals of length `η < 2^(-11)`,
at least one has `|Re(H(x))| ≥ η^3 / 128` throughout. -/
lemma intervals_nice (t : ℕ) {a η : ℝ} (hη0 : 0 < η) (hη1 : η < (1 : ℝ) / 2048) :
    ∃ j : Fin 7, ∀ x ∈ Set.Icc (a + (j.val : ℝ) * η) (a + ((j.val : ℝ) + 1) * η),
      η ^ 3 / 128 ≤ |(Hd t 0 x).re| := by
  by_contra! hall
  choose x hx_mem hx_lt using hall
  let f : ℕ → ℝ → ℝ := fun r u => (Hd t r u).re
  have hf : ∀ r ≤ 3, ∀ u, HasDerivAt (f r) (f (r + 1) u) u := fun r _ u =>
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (hasDerivAt_Hd t r u)
  have hM : ∀ r ≤ 4, ∀ u, |f r u| ≤ (2 : ℝ) ^ r + 2 := fun r hr u =>
    (Complex.abs_re_le_norm _).trans (Hd_approx_and_bound t r hr u).2
  have hlt0 : |f 0 (x 0)| < 1 / 4 := by
    have h1 := hx_lt 0
    have h2 : η ^ 3 ≤ 1 := by
      have : η ≤ 1 := by linarith
      exact pow_le_one₀ hη0.le this
    dsimp only [f]; linarith
  have hlt_k : ∀ k : ℕ, 1 ≤ k → k ≤ 3 → |f k (x 0)| < 1 / 4 := by
    intro k hk1 hk3
    have hb := deriv_bound_from_samples f hf hη0 x
      (fun j => (hx_mem j).1) (fun j => (hx_mem j).2)
      (η ^ 3 / 128) (fun j => le_of_lt (hx_lt j))
      (fun r => (2 : ℝ) ^ r + 2) hM k hk1 hk3
    have hη3_div : η ^ 3 / 128 / η ^ k ≤ 1 / 128 := by
      have hpow : η ^ 3 ≤ η ^ k := pow_le_pow_of_le_one hη0.le (by linarith) hk3
      rw [div_div, div_le_iff₀ (by positivity)]
      linarith
    have hfact : ((k + 1).factorial : ℝ) ≤ 24 := by
      interval_cases k <;> norm_num
    have hterm1 : ((k + 1).factorial : ℝ) * (η ^ 3 / 128) / η ^ k ≤ 24 / 128 := by
      rw [mul_div_assoc]
      calc ((k + 1).factorial : ℝ) * (η ^ 3 / 128 / η ^ k)
          ≤ 24 * (1 / 128 : ℝ) := mul_le_mul hfact hη3_div (by positivity) (by norm_num)
        _ = 24 / 128 := by ring
    have hMval : (2 : ℝ) ^ (k + 1) + 2 ≤ 18 := by
      interval_cases k <;> norm_num
    have hterm2 : 7 * η * ((2 : ℝ) ^ (k + 1) + 2) < 126 / 2048 := by nlinarith
    linarith
  rcases H_deriv_lbounds t (x 0) with h | h | h | h
  · exact not_lt_of_ge h hlt0
  · exact not_lt_of_ge h (hlt_k 1 (by omega) (by omega))
  · exact not_lt_of_ge h (hlt_k 2 (by omega) (by omega))
  · exact not_lt_of_ge h (hlt_k 3 (by omega) (by omega))

/-- BBMST Lemma 3.8: For odd `t`, `Re(H(x)) ≥ 1/2` near `0` and near `T * π`. -/
lemma H_near_endpoints (r : ℕ) (x : ℝ)
    (hx : |x| ≤ 1 / 8 ∨ |x - ((2 ^ (2 * r + 1 + 10) : ℕ) : ℝ) * Real.pi| ≤ 1 / 8) :
    1 / 2 ≤ (Hd (2 * r + 1) 0 x).re := by
  set t := 2 * r + 1
  set T : ℝ := ((2 ^ (t + 10) : ℕ) : ℝ)
  have hT_pos : 0 < T := by positivity
  have hsqrt : Real.sqrt ((2 : ℝ) ^ (t + 1)) = (2 : ℝ) ^ (r + 1) := by
    have : (2 : ℝ) ^ (t + 1) = ((2 : ℝ) ^ (r + 1)) ^ 2 := by
      rw [← pow_mul]; congr 1; omega
    rw [this, Real.sqrt_sq (by positivity)]
  have hvals := rs_eval_pm_one r
  have ht_eq : t = 2 * r + 1 := rfl
  have hlip : ∀ x₀ : ℝ, |(Hd t 0 x).re - (Hd t 0 x₀).re| ≤ 4 * |x - x₀| := by
    intro x₀
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u => (Hd t 0 u).re) (f' := fun u => (Hd t 1 u).re) (s := Set.univ) (C := 4)
      (fun u _ => (Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (hasDerivAt_Hd t 0 u)).hasDerivWithinAt)
      (fun u _ => by
        have h1 := (Complex.abs_re_le_norm _).trans (Hd_approx_and_bound t 1 (by omega) u).2
        rw [Real.norm_eq_abs]; norm_num at h1; exact h1)
      convex_univ (Set.mem_univ x₀) (Set.mem_univ x)
    simpa [Real.norm_eq_abs] using h
  rcases hx with hx0 | hxT
  · have hH0 : (Hd t 0 0).re = 1 := by
      rw [Hd_zero]
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, Halpha, Hbeta,
        zero_div, pow_zero, inv_one, mul_one, rsPd_zero, rsQd_zero, hsqrt]
      rw [ht_eq, hvals.1, hvals.2.1]
      simp
    have := abs_le.mp (hlip 0)
    rw [hH0, sub_zero] at this
    linarith
  · have hHT : (Hd t 0 (T * Real.pi)).re = 1 := by
      rw [Hd_zero]
      have hdiv : T * Real.pi / ((2 ^ (t + 10) : ℕ) : ℝ) = Real.pi :=
        mul_div_cancel_left₀ _ hT_pos.ne'
      have hexp1 : Complex.exp (((T * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
        have hT_even : Even (2 ^ (t + 10)) := by
          rw [show t + 10 = (t + 9) + 1 by omega, pow_succ']; exact even_two_mul _
        obtain ⟨q, hq⟩ := hT_even
        have harg : ((T * Real.pi : ℝ) : ℂ) * Complex.I = (q : ℂ) * (2 * Real.pi * Complex.I) := by
          dsimp only [T]; rw [hq]; push_cast; ring
        rw [harg, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
      have hexp2 : Complex.exp ((2 : ℂ) * ((T * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
        have harg : (2 : ℂ) * ((T * Real.pi : ℝ) : ℂ) * Complex.I =
            ((2 ^ (t + 10) : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
          dsimp only [T]; push_cast; ring
        rw [harg, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
      rw [hexp1, hexp2, one_mul, one_mul]
      simp only [Halpha, Hbeta, hdiv, pow_zero, inv_one, mul_one, rsPd_zero, rsQd_zero,
        Complex.exp_pi_mul_I, hsqrt]
      rw [ht_eq, hvals.2.2.1, hvals.2.2.2]
      simp
    have := abs_le.mp (hlip (T * Real.pi))
    rw [hHT] at this
    linarith

/-! ### Section 5: The cosine polynomial `cosPoly`, even sine `sinEven`, and bad runs -/

/-- The cosine polynomial `c(θ) = Re(z^T P_t(z) + z^{2T} Q_t(z))` with `z = e^{2iθ}`. -/
noncomputable def cosPoly (t : ℕ) (θ : ℝ) : ℝ :=
  (Complex.exp ((2 * (2 ^ (t + 10) : ℕ) : ℝ) * θ * Complex.I) *
      rsP t (Complex.exp ((2 * θ : ℝ) * Complex.I)) +
   Complex.exp ((4 * (2 ^ (t + 10) : ℕ) : ℝ) * θ * Complex.I) *
      rsQ t (Complex.exp ((2 * θ : ℝ) * Complex.I))).re

lemma cosPoly_eq_Hd (t : ℕ) (θ : ℝ) :
    cosPoly t θ = Real.sqrt ((2 : ℝ) ^ (t + 1)) * (Hd t 0 (2 * ((2 ^ (t + 10) : ℕ) : ℝ) * θ)).re := by
  unfold cosPoly
  rw [Hd_zero]
  set T : ℝ := ((2 ^ (t + 10) : ℕ) : ℝ)
  have hT_ne : T ≠ 0 := by positivity
  have hsqrt_ne : Real.sqrt ((2 : ℝ) ^ (t + 1)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hdiv : 2 * T * θ / ((2 ^ (t + 10) : ℕ) : ℝ) = 2 * θ := by
    dsimp only [T]; field_simp [hT_ne]
  simp only [Halpha, Hbeta, hdiv, pow_zero, inv_one, mul_one, rsPd_zero, rsQd_zero]
  have h1 : (((2 * T * θ : ℝ) : ℂ) * Complex.I) = ((2 * (2 ^ (t + 10) : ℕ) : ℝ) * θ * Complex.I) := by
    dsimp only [T]; push_cast; ring
  have h2 : ((2 : ℂ) * ((2 * T * θ : ℝ) : ℂ) * Complex.I) = ((4 * (2 ^ (t + 10) : ℕ) : ℝ) * θ * Complex.I) := by
    dsimp only [T]; push_cast; ring
  rw [h1, h2]
  have hscale : ∀ z : ℂ, (Real.sqrt ((2 : ℝ) ^ (t + 1)) : ℝ) * (((Real.sqrt ((2 : ℝ) ^ (t + 1)))⁻¹ : ℝ) * z).re = z.re := by
    intro z
    rw [Complex.re_ofReal_mul, ← mul_assoc, mul_inv_cancel₀ hsqrt_ne, one_mul]
  rw [Complex.add_re, Complex.add_re, mul_add]
  have ha : (Complex.exp ((2 * (2 ^ (t + 10) : ℕ) : ℝ) * θ * Complex.I) *
      (((Real.sqrt ((2 : ℝ) ^ (t + 1)))⁻¹ : ℝ) * rsP t (Complex.exp ((2 * θ : ℝ) * Complex.I)))) =
      (((Real.sqrt ((2 : ℝ) ^ (t + 1)))⁻¹ : ℝ) : ℂ) *
      (Complex.exp ((2 * (2 ^ (t + 10) : ℕ) : ℝ) * θ * Complex.I) * rsP t (Complex.exp ((2 * θ : ℝ) * Complex.I))) := by ring
  have hb : (Complex.exp ((4 * (2 ^ (t + 10) : ℕ) : ℝ) * θ * Complex.I) *
      (((Real.sqrt ((2 : ℝ) ^ (t + 1)))⁻¹ : ℝ) * rsQ t (Complex.exp ((2 * θ : ℝ) * Complex.I)))) =
      (((Real.sqrt ((2 : ℝ) ^ (t + 1)))⁻¹ : ℝ) : ℂ) *
      (Complex.exp ((4 * (2 ^ (t + 10) : ℕ) : ℝ) * θ * Complex.I) * rsQ t (Complex.exp ((2 * θ : ℝ) * Complex.I))) := by ring
  rw [ha, hb, hscale, hscale]

lemma cosPoly_eq_cos_sum (t : ℕ) (θ : ℝ) :
    cosPoly t θ =
      ∑ j ∈ range (2 ^ t),
        (rsPcoeff t j * Real.cos (2 * (((2 ^ (t + 10) + j : ℕ) : ℝ)) * θ) +
         rsQcoeff t j * Real.cos (2 * (((2 * 2 ^ (t + 10) + j : ℕ) : ℝ)) * θ)) := by
  unfold cosPoly rsP rsQ
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.add_re]
  have hterm : ∀ (a : ℝ) (N : ℕ),
      (Complex.exp (((2 * N : ℕ) : ℝ) * θ * Complex.I) *
        ((a : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I) ^ j)).re =
      a * Real.cos (2 * ((N + j : ℕ) : ℝ) * θ) := by
    intro a N
    rw [← Complex.exp_nat_mul]
    have hmul : Complex.exp (((2 * N : ℕ) : ℝ) * θ * Complex.I) *
        ((a : ℂ) * Complex.exp ((j : ℂ) * ((2 * θ : ℝ) * Complex.I))) =
        (a : ℂ) * Complex.exp (((2 * ((N + j : ℕ) : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [hmul, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have h1 := hterm (rsPcoeff t j) (2 ^ (t + 10))
  have h2 := hterm (rsQcoeff t j) (2 * 2 ^ (t + 10))
  have hc1 : (((2 * 2 ^ (t + 10) : ℕ) : ℝ) : ℂ) = (2 * (2 ^ (t + 10) : ℕ) : ℝ) := by push_cast; ring
  have hc2 : (((2 * (2 * 2 ^ (t + 10)) : ℕ) : ℝ) : ℂ) = (4 * (2 ^ (t + 10) : ℕ) : ℝ) := by push_cast; ring
  rw [hc1] at h1; rw [hc2] at h2
  rw [h1, h2]

lemma cosPoly_symm_pi_sub (t : ℕ) (θ : ℝ) : cosPoly t (Real.pi - θ) = cosPoly t θ := by
  rw [cosPoly_eq_cos_sum, cosPoly_eq_cos_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcos : ∀ N : ℕ, Real.cos (2 * (N : ℝ) * (Real.pi - θ)) = Real.cos (2 * (N : ℝ) * θ) := by
    intro N
    have harg : 2 * (N : ℝ) * (Real.pi - θ) = -(2 * (N : ℝ) * θ) + (N : ℤ) * (2 * Real.pi) := by
      push_cast; ring
    rw [harg, Real.cos_add_int_mul_two_pi, Real.cos_neg]
  rw [hcos, hcos]

lemma cosPoly_symm_pi_add (t : ℕ) (θ : ℝ) : cosPoly t (Real.pi + θ) = cosPoly t θ := by
  rw [cosPoly_eq_cos_sum, cosPoly_eq_cos_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcos : ∀ N : ℕ, Real.cos (2 * (N : ℝ) * (Real.pi + θ)) = Real.cos (2 * (N : ℝ) * θ) := by
    intro N
    have harg : 2 * (N : ℝ) * (Real.pi + θ) = (2 * (N : ℝ) * θ) + (N : ℤ) * (2 * Real.pi) := by
      push_cast; ring
    rw [harg, Real.cos_add_int_mul_two_pi]
  rw [hcos, hcos]

lemma cosPoly_continuous (t : ℕ) : Continuous (cosPoly t) := by
  have heq : cosPoly t = fun θ => ∑ j ∈ range (2 ^ t),
      (rsPcoeff t j * Real.cos (2 * (((2 ^ (t + 10) + j : ℕ) : ℝ)) * θ) +
       rsQcoeff t j * Real.cos (2 * (((2 * 2 ^ (t + 10) + j : ℕ) : ℝ)) * θ)) :=
    funext (cosPoly_eq_cos_sum t)
  rw [heq]
  continuity

lemma cosPoly_norm_le (t : ℕ) (θ : ℝ) : |cosPoly t θ| ≤ 2 * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
  unfold cosPoly
  have hz : ‖Complex.exp ((2 * θ : ℝ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have he1 : ‖Complex.exp ((2 * (2 ^ (t + 10) : ℕ) : ℝ) * θ * Complex.I)‖ = 1 := by
    have : ((2 * (2 ^ (t + 10) : ℕ) : ℝ) * θ : ℂ) * Complex.I =
        (((2 * (2 ^ (t + 10) : ℕ) : ℝ) * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have he2 : ‖Complex.exp ((4 * (2 ^ (t + 10) : ℕ) : ℝ) * θ * Complex.I)‖ = 1 := by
    have : ((4 * (2 ^ (t + 10) : ℕ) : ℝ) * θ : ℂ) * Complex.I =
        (((4 * (2 ^ (t + 10) : ℕ) : ℝ) * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  calc |(_ : ℂ).re| ≤ ‖_‖ := Complex.abs_re_le_norm _
    _ ≤ ‖Complex.exp _ * rsP t _‖ + ‖Complex.exp _ * rsQ t _‖ := norm_add_le _ _
    _ = ‖rsP t (Complex.exp ((2 * θ : ℝ) * Complex.I))‖ +
        ‖rsQ t (Complex.exp ((2 * θ : ℝ) * Complex.I))‖ := by
        rw [norm_mul, norm_mul, he1, he2, one_mul, one_mul]
    _ ≤ Real.sqrt ((2 : ℝ) ^ (t + 1)) + Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
        exact add_le_add (rsP_norm_le t hz) (rsQ_norm_le t hz)
    _ = 2 * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by ring

lemma chebyshev_T_cos (n : ℕ) (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (Real.cos x) = Real.cos ((n : ℝ) * x) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => simp [Polynomial.Chebyshev.T_zero]
    | 1 => simp [Polynomial.Chebyshev.T_one]
    | k + 2 =>
      rw [show ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 by push_cast; ring, Polynomial.Chebyshev.T_add_two]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
      rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring]
      rw [ih (k + 1) (by omega), ih k (by omega)]
      have h1 : ((k + 2 : ℕ) : ℝ) * x = ((k + 1 : ℕ) : ℝ) * x + x := by push_cast; ring
      have h2 : ((k : ℕ) : ℝ) * x = ((k + 1 : ℕ) : ℝ) * x - x := by push_cast; ring
      rw [h1, h2, Real.cos_add, Real.cos_sub]; ring

/-- Chebyshev representation of `cosPoly t θ` as a polynomial in `cos (2θ)` of degree `≤ 2T + 2^t - 1`. -/
noncomputable def cosPolyCheb (t : ℕ) : Polynomial ℝ :=
  ∑ j ∈ range (2 ^ t),
    (Polynomial.C (rsPcoeff t j) * Polynomial.Chebyshev.T ℝ ((2 ^ (t + 10) + j : ℕ) : ℤ) +
     Polynomial.C (rsQcoeff t j) * Polynomial.Chebyshev.T ℝ ((2 * 2 ^ (t + 10) + j : ℕ) : ℤ))

lemma cosPolyCheb_eval (t : ℕ) (θ : ℝ) :
    (cosPolyCheb t).eval (Real.cos (2 * θ)) = cosPoly t θ := by
  rw [cosPoly_eq_cos_sum]
  unfold cosPolyCheb
  rw [poly_eval_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_C, chebyshev_T_cos, chebyshev_T_cos]
  have h1 : ((2 ^ (t + 10) + j : ℕ) : ℝ) * (2 * θ) = 2 * ((2 ^ (t + 10) + j : ℕ) : ℝ) * θ := by ring
  have h2 : ((2 * 2 ^ (t + 10) + j : ℕ) : ℝ) * (2 * θ) = 2 * ((2 * 2 ^ (t + 10) + j : ℕ) : ℝ) * θ := by ring
  rw [h1, h2]

lemma cosPolyCheb_natDegree_le (t : ℕ) :
    (cosPolyCheb t).natDegree ≤ 2 * 2 ^ (t + 10) + 2 ^ t - 1 := by
  unfold cosPolyCheb
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun j hj => ?_⟩
  have hjlt : j < 2 ^ t := Finset.mem_range.mp hj
  have h1 : (Polynomial.C (rsPcoeff t j) * Polynomial.Chebyshev.T ℝ ((2 ^ (t + 10) + j : ℕ) : ℤ)).natDegree ≤
      2 * 2 ^ (t + 10) + 2 ^ t - 1 := by
    calc _ ≤ (Polynomial.Chebyshev.T ℝ ((2 ^ (t + 10) + j : ℕ) : ℤ)).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ = ((2 ^ (t + 10) + j : ℕ) : ℤ).natAbs := Polynomial.Chebyshev.natDegree_T ℝ _
      _ = 2 ^ (t + 10) + j := Int.natAbs_natCast _
      _ ≤ 2 * 2 ^ (t + 10) + 2 ^ t - 1 := by omega
  have h2 : (Polynomial.C (rsQcoeff t j) * Polynomial.Chebyshev.T ℝ ((2 * 2 ^ (t + 10) + j : ℕ) : ℤ)).natDegree ≤
      2 * 2 ^ (t + 10) + 2 ^ t - 1 := by
    calc _ ≤ (Polynomial.Chebyshev.T ℝ ((2 * 2 ^ (t + 10) + j : ℕ) : ℤ)).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ = ((2 * 2 ^ (t + 10) + j : ℕ) : ℤ).natAbs := Polynomial.Chebyshev.natDegree_T ℝ _
      _ = 2 * 2 ^ (t + 10) + j := Int.natAbs_natCast _
      _ ≤ 2 * 2 ^ (t + 10) + 2 ^ t - 1 := by omega
  exact (Polynomial.natDegree_add_le _ _).trans (max_le h1 h2)

/-- Base-16 factored definition of `2 ^ 474` (all exponents ≤ 32) so reduction never recurses deeply. -/
noncomputable def c474 : ℝ := (2 * (16 : ℝ) ^ 18) * (8 * (16 : ℝ) ^ 32) ^ 3 * 256

lemma c474_pos : 0 < c474 := by
  unfold c474
  have h16 : (0 : ℝ) < 16 := by norm_num
  exact mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos h16 18))
    (pow_pos (mul_pos (by norm_num) (pow_pos h16 32)) 3)) (by norm_num)

private lemma cosine_params_thresh (m r : ℕ) (hm32 : 32 ∣ m) (hm_pos : 0 < m)
    (hγ_hi : 2 * 2 ^ (2 * r + 1 + 10) + 2 ^ (2 * r + 1) - 1 ≤ m / 16 ^ 33)
    (hγ_lo : m ≤ (8 * 16 ^ 33) * (2 * 2 ^ (2 * r + 1 + 10) + 2 ^ (2 * r + 1) - 1)) :
    let t := 2 * r + 1
    let T : ℕ := 2 ^ (t + 10)
    let M := m / 32
    let step : ℝ := 16 * Real.pi / (m : ℝ)
    let η : ℝ := 2 * (T : ℝ) * step
    let τ : ℝ := (1 / c474) * Real.sqrt m
    10 ≤ M ∧ (M : ℝ) * step = Real.pi / 2 ∧
    0 < η ∧ η < 1 / 2048 ∧
    τ ≤ Real.sqrt ((2 : ℝ) ^ (t + 1)) * (η ^ 3 / 128) := by
  intro t T M step η τ
  have h16pos : (0 : ℝ) < 16 := by norm_num
  have h16nn : (0 : ℝ) ≤ 16 := by norm_num
  have hm_eq : m = 32 * M := by
    obtain ⟨q, hq⟩ := hm32; simp [M, hq]
  have hM_ge : 10 ≤ M := by
    have hpos : 1 ≤ 2 * T + 2 ^ t - 1 := by
      have h1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
      have h2 : 1 ≤ T := Nat.one_le_two_pow
      omega
    have hm_ge : 16 ^ 33 ≤ m := by
      have hmul : 1 * 16 ^ 33 ≤ m :=
        (Nat.le_div_iff_mul_le (Nat.pow_pos (by norm_num : 0 < 16))).mp (hpos.trans hγ_hi)
      simpa using hmul
    have h320 : 32 * 10 ≤ 16 ^ 33 :=
      le_trans (by norm_num : 32 * 10 ≤ 16 ^ 3)
        (Nat.pow_le_pow_right (by norm_num) (by norm_num : 3 ≤ 33))
    have hmul : 32 * 10 ≤ 32 * M := (h320.trans hm_ge).trans hm_eq.le
    exact Nat.le_of_mul_le_mul_left hmul (by norm_num)
  have hγ_le_real : (2 * (T : ℝ) + (2 : ℝ) ^ t - 1) ≤ (m : ℝ) / (16 : ℝ) ^ 33 := by
    have h1 : (2 * T + 2 ^ t - 1) * 16 ^ 33 ≤ m :=
      (Nat.le_div_iff_mul_le (Nat.pow_pos (by norm_num : 0 < 16))).mp hγ_hi
    have h2 : ((2 * T + 2 ^ t - 1 : ℕ) : ℝ) * (16 : ℝ) ^ 33 ≤ (m : ℝ) := by exact_mod_cast h1
    have hsub : 1 ≤ 2 * T + 2 ^ t := by have := Nat.one_le_two_pow (n := t); omega
    rw [Nat.cast_sub hsub] at h2; push_cast at h2
    rw [le_div_iff₀ (pow_pos h16pos 33)]; exact h2
  have h2T_ge : (m : ℝ) / (16 : ℝ) ^ 34 ≤ 2 * (T : ℝ) := by
    have h1 : 2 * T + 2 ^ t - 1 ≤ 3 * T := by
      have hle : 2 ^ t ≤ T := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpos : 1 ≤ 2 ^ t := Nat.one_le_two_pow
      omega
    have h2 : m ≤ (8 * 16 ^ 33) * (3 * T) := hγ_lo.trans (Nat.mul_le_mul_left _ h1)
    have h3 : (m : ℝ) ≤ (8 * (16 : ℝ) ^ 33) * (3 * (T : ℝ)) := by exact_mod_cast h2
    rw [div_le_iff₀ (pow_pos h16pos 34)]
    have hpow : (16 : ℝ) ^ 34 = 16 * (16 : ℝ) ^ 33 := by rw [pow_succ']
    have hTnn : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
    have h34 : (8 * (16 : ℝ) ^ 33) * (3 * (T : ℝ)) ≤ (8 * (16 : ℝ) ^ 33) * (4 * (T : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hTnn]) (mul_nonneg (by norm_num) (pow_nonneg h16nn 33))
    have h4 : (8 * (16 : ℝ) ^ 33) * (4 * (T : ℝ)) = 2 * (T : ℝ) * (16 * (16 : ℝ) ^ 33) := by ring
    rw [hpow]; exact h3.trans (h34.trans_eq h4)
  clear hγ_hi hγ_lo
  have hM_step : (M : ℝ) * step = Real.pi / 2 := by
    dsimp only [step]
    have hm_cast : (m : ℝ) = 32 * (M : ℝ) := by exact_mod_cast hm_eq
    have hM_ne : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    rw [hm_cast]; field_simp [hM_ne]; ring
  have hm_pos_r : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have hstep_pos : 0 < step := div_pos (mul_pos (by norm_num) Real.pi_pos) hm_pos_r
  have hT_pos_r : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (Nat.pow_pos (by norm_num : 0 < 2) (n := t + 10))
  have hη_pos : 0 < η := mul_pos (mul_pos (by norm_num) hT_pos_r) hstep_pos
  have h2T_le : (2 * (T : ℝ)) ≤ (m : ℝ) / (16 : ℝ) ^ 33 := by
    have h1 : 2 * T ≤ 2 * T + 2 ^ t - 1 := by have := Nat.one_le_two_pow (n := t); omega
    have h2 : (2 * (T : ℝ)) ≤ (2 * (T : ℝ) + (2 : ℝ) ^ t - 1) := by
      have : ((2 * T : ℕ) : ℝ) ≤ ((2 * T + 2 ^ t - 1 : ℕ) : ℝ) := by exact_mod_cast h1
      have hsub : 1 ≤ 2 * T + 2 ^ t := by have := Nat.one_le_two_pow (n := t); omega
      rw [Nat.cast_sub hsub] at this; push_cast at this; exact this
    exact h2.trans hγ_le_real
  have hη_lt : η < 1 / 2048 := by
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have h16pi : 16 * Real.pi < 4 * (16 : ℝ) := by linarith only [hpi]
    calc η = 2 * (T : ℝ) * (16 * Real.pi / (m : ℝ)) := rfl
      _ ≤ ((m : ℝ) / (16 : ℝ) ^ 33) * (16 * Real.pi / (m : ℝ)) :=
          mul_le_mul_of_nonneg_right h2T_le hstep_pos.le
      _ = 16 * Real.pi / (16 : ℝ) ^ 33 := by field_simp [hm_pos_r.ne']
      _ < (4 * (16 : ℝ)) / (16 : ℝ) ^ 33 :=
          div_lt_div_of_pos_right h16pi (pow_pos h16pos 33)
      _ = 4 / (16 : ℝ) ^ 32 := by
          rw [show (33 : ℕ) = 1 + 32 by norm_num, pow_add, pow_one]
          have hne : (16 : ℝ) ^ 32 ≠ 0 := pow_ne_zero 32 h16pos.ne'
          field_simp [h16pos.ne', hne]
      _ ≤ 4 / (16 : ℝ) ^ 4 := by
          apply div_le_div_of_nonneg_left (by norm_num) (pow_pos h16pos 4)
          exact pow_le_pow_right₀ (by norm_num) (by norm_num : 4 ≤ 32)
      _ ≤ 1 / 2048 := by norm_num
  have hthresh : τ ≤ Real.sqrt ((2 : ℝ) ^ (t + 1)) * (η ^ 3 / 128) := by
    have hη_ge : (1 : ℝ) / (8 * (16 : ℝ) ^ 32) ≤ η := by
      have hpi : 3 < Real.pi := Real.pi_gt_three
      have h32 : 2 * (16 : ℝ) ≤ 16 * Real.pi := by linarith only [hpi]
      calc (1 : ℝ) / (8 * (16 : ℝ) ^ 32) = (2 * (16 : ℝ)) / (16 : ℝ) ^ 34 := by
            rw [show (34 : ℕ) = 2 + 32 by norm_num, pow_add]
            have hne : (16 : ℝ) ^ 32 ≠ 0 := pow_ne_zero 32 h16pos.ne'
            field_simp [hne]; ring
        _ ≤ 16 * Real.pi / (16 : ℝ) ^ 34 :=
            div_le_div_of_nonneg_right h32 (pow_nonneg h16nn 34)
        _ = ((m : ℝ) / (16 : ℝ) ^ 34) * (16 * Real.pi / (m : ℝ)) := by field_simp [hm_pos_r.ne']
        _ ≤ 2 * (T : ℝ) * (16 * Real.pi / (m : ℝ)) :=
            mul_le_mul_of_nonneg_right h2T_ge hstep_pos.le
        _ = η := rfl
    have h2t1_ge : (m : ℝ) / (4 * (16 : ℝ) ^ 36) ≤ (2 : ℝ) ^ (t + 1) := by
      have hTeq : (2 : ℝ) * (T : ℝ) = (4 * (16 : ℝ) ^ 2) * (2 : ℝ) ^ (t + 1) := by
        dsimp only [T]; push_cast
        rw [show (4 * (16 : ℝ) ^ 2 : ℝ) = (2 : ℝ) ^ 10 by norm_num, ← pow_succ', ← pow_add]
        congr 1; omega
      rw [div_le_iff₀ (mul_pos (by norm_num) (pow_pos h16pos 36))]
      have hmul : (m : ℝ) ≤ (16 : ℝ) ^ 34 * (2 * (T : ℝ)) := by
        have h' := (div_le_iff₀ (pow_pos h16pos 34)).mp h2T_ge
        linarith only [h']
      have hcomb : (16 : ℝ) ^ 34 * (4 * (16 : ℝ) ^ 2) = 4 * (16 : ℝ) ^ 36 := by
        rw [show (36 : ℕ) = 34 + 2 by norm_num, pow_add]; ring
      rw [hTeq, ← mul_assoc, hcomb] at hmul
      linarith only [hmul]
    have hsqrt_ge : Real.sqrt m / (2 * (16 : ℝ) ^ 18) ≤ Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
      have h1 := Real.sqrt_le_sqrt h2t1_ge
      rw [Real.sqrt_div (Nat.cast_nonneg m)] at h1
      have h2 : Real.sqrt (4 * (16 : ℝ) ^ 36) = 2 * (16 : ℝ) ^ 18 := by
        have hsq : 4 * (16 : ℝ) ^ 36 = (2 * (16 : ℝ) ^ 18) ^ 2 := by
          rw [mul_pow, ← pow_mul]; norm_num
        rw [hsq, Real.sqrt_sq (mul_nonneg (by norm_num) (pow_nonneg h16nn 18))]
      rw [h2] at h1; exact h1
    have hη3_ge : ((1 : ℝ) / (8 * (16 : ℝ) ^ 32)) ^ 3 ≤ η ^ 3 :=
      pow_le_pow_left₀ (div_nonneg (by norm_num) (mul_nonneg (by norm_num) (pow_nonneg h16nn 32))) hη_ge 3
    have hdiv_ge : ((1 : ℝ) / (8 * (16 : ℝ) ^ 32)) ^ 3 / 256 ≤ η ^ 3 / 128 := by
      have hnn : 0 ≤ ((1 : ℝ) / (8 * (16 : ℝ) ^ 32)) ^ 3 :=
        pow_nonneg (div_nonneg (by norm_num) (mul_nonneg (by norm_num) (pow_nonneg h16nn 32))) 3
      have h1 : ((1 : ℝ) / (8 * (16 : ℝ) ^ 32)) ^ 3 / 256 ≤ ((1 : ℝ) / (8 * (16 : ℝ) ^ 32)) ^ 3 / 128 := by
        linarith only [hnn]
      have h2 : ((1 : ℝ) / (8 * (16 : ℝ) ^ 32)) ^ 3 / 128 ≤ η ^ 3 / 128 :=
        div_le_div_of_nonneg_right hη3_ge (by norm_num)
      exact h1.trans h2
    have hpow_eq : (1 / c474) * Real.sqrt m =
        (Real.sqrt m / (2 * (16 : ℝ) ^ 18)) * (((1 : ℝ) / (8 * (16 : ℝ) ^ 32)) ^ 3 / 256) := by
      unfold c474
      have h18 : (16 : ℝ) ^ 18 ≠ 0 := pow_ne_zero 18 h16pos.ne'
      have h32 : (16 : ℝ) ^ 32 ≠ 0 := pow_ne_zero 32 h16pos.ne'
      rw [div_pow, one_pow]
      field_simp [h18, h32]
    calc τ = (1 / c474) * Real.sqrt m := rfl
      _ = (Real.sqrt m / (2 * (16 : ℝ) ^ 18)) * (((1 : ℝ) / (8 * (16 : ℝ) ^ 32)) ^ 3 / 256) := hpow_eq
      _ ≤ Real.sqrt ((2 : ℝ) ^ (t + 1)) * (η ^ 3 / 128) := by
          apply mul_le_mul hsqrt_ge hdiv_ge
            (div_nonneg (pow_nonneg (div_nonneg (by norm_num) (mul_nonneg (by norm_num) (pow_nonneg h16nn 32))) 3) (by norm_num))
            (Real.sqrt_nonneg _)
  exact ⟨hM_ge, hM_step, hη_pos, hη_lt, hthresh⟩

private lemma cosine_bad_starts_card_le (r M : ℕ) (step τ : ℝ)
    (hstep_pos : 0 < step) (hM_step : (M : ℝ) * step = Real.pi / 2)
    (hτ_nn : 0 ≤ τ) (hτ_lt_c0 : τ < cosPoly (2 * r + 1) 0)
    (badStarts : Finset ℕ)
    (hstarts : ∀ a ∈ badStarts,
      1 ≤ a ∧ a < M ∧
      (∀ θ ∈ Set.Icc (((a - 1 : ℕ) : ℝ) * step) ((((a - 1 : ℕ) : ℝ) + 1) * step),
        τ ≤ |cosPoly (2 * r + 1) θ|) ∧
      ∃ w ∈ Set.Icc ((a : ℝ) * step) (((a : ℝ) + 1) * step), |cosPoly (2 * r + 1) w| < τ) :
    badStarts.card ≤ 2 * (2 * 2 ^ (2 * r + 1 + 10) + 2 ^ (2 * r + 1) - 1) := by
  classical
  set t := 2 * r + 1
  let Q : Polynomial ℝ := cosPolyCheb t ^ 2 - Polynomial.C (τ ^ 2)
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    have hev := congrArg (fun P : Polynomial ℝ => P.eval 1) hQ0
    simp only [Q, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_zero] at hev
    have h1 : (cosPolyCheb t).eval 1 = cosPoly t 0 := by simpa using cosPolyCheb_eval t 0
    rw [h1] at hev
    have hpos : τ ^ 2 < cosPoly t 0 ^ 2 := by nlinarith only [hτ_nn, hτ_lt_c0]
    linarith only [hev, hpos]
  have hQ_deg : Q.natDegree ≤ 2 * (2 * 2 ^ (t + 10) + 2 ^ t - 1) := by
    have hsq : (cosPolyCheb t ^ 2).natDegree ≤ 2 * (2 * 2 ^ (t + 10) + 2 ^ t - 1) :=
      (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left 2 (cosPolyCheb_natDegree_le t))
    have hcdeg : (Polynomial.C (τ ^ 2)).natDegree = 0 := Polynomial.natDegree_C _
    exact (Polynomial.natDegree_sub_le_iff_left (by omega)).mpr hsq
  have hex_root : ∀ a ∈ badStarts, ∃ z ∈ Set.Icc ((a : ℝ) * step) (((a : ℝ) + 1) * step),
      Q.eval (Real.cos (2 * z)) = 0 := by
    intro a ha
    obtain ⟨h1, _, hprev, w, hw_mem, hw_lt⟩ := hstarts a ha
    have ha_end : τ ≤ |cosPoly t ((a : ℝ) * step)| := by
      apply hprev ((a : ℝ) * step)
      have hcast : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by rw [Nat.cast_sub h1, Nat.cast_one]
      rw [hcast]
      constructor
      · have hle : (a : ℝ) - 1 ≤ (a : ℝ) := by linarith
        exact mul_le_mul_of_nonneg_right hle hstep_pos.le
      · have heq : ((a : ℝ) - 1 + 1) * step = (a : ℝ) * step := by ring
        rw [heq]
    have hcont : ContinuousOn (fun θ => |cosPoly t θ|) (Set.Icc ((a : ℝ) * step) w) :=
      (cosPoly_continuous t).abs.continuousOn
    have hmem_ivt : τ ∈ Set.Icc |cosPoly t w| |cosPoly t ((a : ℝ) * step)| := ⟨hw_lt.le, ha_end⟩
    obtain ⟨z, hz_mem, hz_eq⟩ := intermediate_value_Icc' hw_mem.1 hcont hmem_ivt
    refine ⟨z, ⟨hz_mem.1, hz_mem.2.trans hw_mem.2⟩, ?_⟩
    simp only [Q, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C, cosPolyCheb_eval]
    dsimp only at hz_eq
    have hsq : cosPoly t z ^ 2 = τ ^ 2 := by rw [← sq_abs, hz_eq]
    linarith only [hsq]
  choose zOf hz_mem hz_root using fun a (ha : a ∈ badStarts) => hex_root a ha
  let rootSet : Finset ℝ := badStarts.attach.image (fun x => Real.cos (2 * zOf x.1 x.2))
  have hinj_root : Function.Injective (fun x : {a // a ∈ badStarts} => Real.cos (2 * zOf x.1 x.2)) := by
    intro x₁ x₂ hEq
    by_contra hne
    have hane : x₁.1 ≠ x₂.1 := fun h => hne (Subtype.ext h)
    have hz_range : ∀ x : {a // a ∈ badStarts}, 2 * zOf x.1 x.2 ∈ Set.Icc (0 : ℝ) Real.pi := by
      intro x
      obtain ⟨_, hx_ltM, _, _⟩ := hstarts x.1 x.2
      have hzm := hz_mem x.1 x.2
      have hleM : ((x.1 : ℝ) + 1) ≤ (M : ℝ) := by exact_mod_cast (show x.1 + 1 ≤ M by omega)
      have hlo : 0 ≤ (x.1 : ℝ) * step := mul_nonneg (Nat.cast_nonneg _) hstep_pos.le
      have hhi : ((x.1 : ℝ) + 1) * step ≤ Real.pi / 2 :=
        (mul_le_mul_of_nonneg_right hleM hstep_pos.le).trans_eq hM_step
      constructor <;> linarith only [hlo, hhi, hzm.1, hzm.2]
    have h2z_eq : 2 * zOf x₁.1 x₁.2 = 2 * zOf x₂.1 x₂.2 :=
      Real.injOn_cos (hz_range x₁) (hz_range x₂) hEq
    have hz_eq : zOf x₁.1 x₁.2 = zOf x₂.1 x₂.2 := by linarith only [h2z_eq]
    have hsep : x₁.1 + 1 < x₂.1 ∨ x₂.1 + 1 < x₁.1 := by
      rcases lt_or_gt_of_ne hane with hlt | hgt
      · left
        by_contra! hle
        have hsucc : x₂.1 = x₁.1 + 1 := by omega
        have hprev2 := (hstarts x₂.1 x₂.2).2.2.1
        obtain ⟨w, hw_mem, hw_lt⟩ := (hstarts x₁.1 x₁.2).2.2.2
        rw [hsucc, Nat.add_sub_cancel] at hprev2
        exact not_lt_of_ge (hprev2 w hw_mem) hw_lt
      · right
        by_contra! hle
        have hsucc : x₁.1 = x₂.1 + 1 := by omega
        have hprev1 := (hstarts x₁.1 x₁.2).2.2.1
        obtain ⟨w, hw_mem, hw_lt⟩ := (hstarts x₂.1 x₂.2).2.2.2
        rw [hsucc, Nat.add_sub_cancel] at hprev1
        exact not_lt_of_ge (hprev1 w hw_mem) hw_lt
    have hzm1 := hz_mem x₁.1 x₁.2
    have hzm2 := hz_mem x₂.1 x₂.2
    rcases hsep with h | h
    · have hcast : (x₁.1 : ℝ) + 1 < (x₂.1 : ℝ) := by exact_mod_cast h
      have hlt_s := mul_lt_mul_of_pos_right hcast hstep_pos
      linarith only [hzm1.2, hzm2.1, hz_eq, hlt_s]
    · have hcast : (x₂.1 : ℝ) + 1 < (x₁.1 : ℝ) := by exact_mod_cast h
      have hlt_s := mul_lt_mul_of_pos_right hcast hstep_pos
      linarith only [hzm2.2, hzm1.1, hz_eq, hlt_s]
  have hcard_roots : rootSet.card = badStarts.card := by
    dsimp only [rootSet]
    rw [Finset.card_image_of_injective _ hinj_root, Finset.card_attach]
  have hroot_sub : rootSet.val ⊆ Q.roots := by
    intro u hu
    rw [Finset.mem_val] at hu
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
    rw [Polynomial.mem_roots hQ_ne]
    exact hz_root x.1 x.2
  have hroot_card_le : rootSet.card ≤ Q.natDegree := by
    have h1 := Multiset.card_le_card (Multiset.le_iff_subset rootSet.nodup |>.mpr hroot_sub)
    exact h1.trans (Polynomial.card_roots' Q)
  omega

/-- Extraction of maximal bad grid runs in `[0, π/2]` with grid step `16π / m` (`32 ∣ m`). -/
theorem cosine_bad_runs (m r : ℕ) (hm32 : 32 ∣ m) (hm_pos : 0 < m)
    (hγ_hi : 2 * 2 ^ (2 * r + 1 + 10) + 2 ^ (2 * r + 1) - 1 ≤ m / 16 ^ 33)
    (hγ_lo : m ≤ (8 * 16 ^ 33) * (2 * 2 ^ (2 * r + 1 + 10) + 2 ^ (2 * r + 1) - 1)) :
    let t := 2 * r + 1
    let M := m / 32
    let step : ℝ := 16 * Real.pi / (m : ℝ)
    let τ : ℝ := (1 / c474) * Real.sqrt m
    ∃ runs : Finset (ℕ × ℕ),
      (∀ ab ∈ runs, 1 ≤ ab.1 ∧ ab.1 < ab.2 ∧ ab.2 ≤ M - 1 ∧ ab.2 - ab.1 ≤ 6) ∧
      (∀ ab₁ ∈ runs, ∀ ab₂ ∈ runs, ab₁ ≠ ab₂ → ab₁.2 + 1 ≤ ab₂.1 ∨ ab₂.2 + 1 ≤ ab₁.1) ∧
      (runs.card ≤ 2 * (2 * 2 ^ (t + 10) + 2 ^ t - 1)) ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        (∀ ab ∈ runs, θ ∉ Set.Icc ((ab.1 : ℝ) * step) ((ab.2 : ℝ) * step)) →
        τ ≤ |cosPoly t θ|) := by
  classical
  intro t M step τ
  set T : ℕ := 2 ^ (t + 10)
  set η : ℝ := 2 * (T : ℝ) * step
  obtain ⟨hM_ge, hM_step, hη_pos, hη_lt, hthresh⟩ :=
    cosine_params_thresh m r hm32 hm_pos hγ_hi hγ_lo
  clear hγ_hi hγ_lo
  have hstep_pos : 0 < step := div_pos (mul_pos (by norm_num) Real.pi_pos) (by exact_mod_cast hm_pos)
  -- Define grid goodness on `j < M`.
  let isGood (j : ℕ) : Prop :=
    ∀ θ ∈ Set.Icc ((j : ℝ) * step) (((j : ℝ) + 1) * step), τ ≤ |cosPoly t θ|
  have hisGood_of_H : ∀ j : ℕ,
      (∀ x ∈ Set.Icc ((j : ℝ) * η) (((j : ℝ) + 1) * η), η ^ 3 / 128 ≤ |(Hd t 0 x).re|) →
      isGood j := by
    intro j hH θ hθ
    rw [cosPoly_eq_Hd, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hx_mem : 2 * (T : ℝ) * θ ∈ Set.Icc ((j : ℝ) * η) (((j : ℝ) + 1) * η) := by
      have h2T : 0 ≤ 2 * (T : ℝ) := mul_nonneg (by norm_num) (Nat.cast_nonneg T)
      constructor
      · have h1 := mul_le_mul_of_nonneg_left hθ.1 h2T
        calc (j : ℝ) * η = 2 * (T : ℝ) * ((j : ℝ) * step) := by dsimp only [η]; ring
          _ ≤ 2 * (T : ℝ) * θ := h1
      · have h2 := mul_le_mul_of_nonneg_left hθ.2 h2T
        calc 2 * (T : ℝ) * θ ≤ 2 * (T : ℝ) * (((j : ℝ) + 1) * step) := h2
          _ = ((j : ℝ) + 1) * η := by dsimp only [η]; ring
    exact hthresh.trans (mul_le_mul_of_nonneg_left (hH _ hx_mem) (Real.sqrt_nonneg _))
  -- Grid intervals `0` and `M - 1` are good by `H_near_endpoints`.
  have hgood0 : isGood 0 := by
    apply hisGood_of_H
    intro x hx
    have hx_abs : |x| ≤ 1 / 8 := by
      simp only [Nat.cast_zero, zero_mul, zero_add, one_mul] at hx
      rw [abs_le]; constructor <;> linarith only [hx.1, hx.2, hη_lt]
    have hge := H_near_endpoints r x (Or.inl hx_abs)
    have hη3 : η ^ 3 / 128 ≤ 1 / 2 := by
      have : η ^ 3 ≤ 1 := pow_le_one₀ hη_pos.le (by linarith only [hη_lt])
      linarith only [this]
    exact hη3.trans (hge.trans (le_abs_self _))
  have hgood_last : isGood (M - 1) := by
    apply hisGood_of_H
    intro x hx
    have hM_eta : (M : ℝ) * η = (T : ℝ) * Real.pi := by
      calc (M : ℝ) * η = 2 * (T : ℝ) * ((M : ℝ) * step) := by dsimp only [η]; ring
        _ = 2 * (T : ℝ) * (Real.pi / 2) := by rw [hM_step]
        _ = (T : ℝ) * Real.pi := by ring
    have hlo : (T : ℝ) * Real.pi - η ≤ x := by
      have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast] at hx
      linarith only [hx.1, hM_eta]
    have hhi : x ≤ (T : ℝ) * Real.pi := by
      have hcast : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]; ring
      rw [hcast] at hx
      linarith only [hx.2, hM_eta]
    have hx_abs : |x - (T : ℝ) * Real.pi| ≤ 1 / 8 := by
      rw [abs_le]; constructor <;> linarith only [hlo, hhi, hη_lt]
    have hge := H_near_endpoints r x (Or.inr hx_abs)
    have hη3 : η ^ 3 / 128 ≤ 1 / 2 := by
      have : η ^ 3 ≤ 1 := pow_le_one₀ hη_pos.le (by linarith only [hη_lt])
      linarith only [this]
    exact hη3.trans (hge.trans (le_abs_self _))
  -- Every 7 consecutive grid indices contain a good index.
  have h7_good : ∀ a : ℕ, ∃ j : Fin 7, isGood (a + j.val) := by
    intro a
    obtain ⟨j, hj⟩ := intervals_nice t (a := (a : ℝ) * η) hη_pos hη_lt
    refine ⟨j, hisGood_of_H (a + j.val) fun x hx => hj x ?_⟩
    constructor <;> (push_cast at hx; linarith only [hx.1, hx.2])
  have hex_good_after : ∀ a : ℕ, a < M - 1 → ¬ isGood a → ∃ b, a < b ∧ b ≤ M - 1 ∧ b ≤ a + 6 ∧ isGood b := by
    intro a ha hbad_a
    obtain ⟨j, hj⟩ := h7_good a
    have hj_ne0 : j.val ≠ 0 := by
      intro h0
      rw [h0, add_zero] at hj
      exact hbad_a hj
    by_cases hle : a + j.val ≤ M - 1
    · exact ⟨a + j.val, by omega, hle, by omega, hj⟩
    · exact ⟨M - 1, by omega, le_rfl, by omega, hgood_last⟩
  let badStarts : Finset ℕ := (Finset.range M).filter (fun a => ¬ isGood a ∧ (a = 0 ∨ isGood (a - 1)))
  let endOf (a : ℕ) : ℕ :=
    if h : ∃ b, a < b ∧ isGood b then Nat.find h else M - 1
  have hend_spec : ∀ a ∈ badStarts,
      1 ≤ a ∧ a < endOf a ∧ endOf a ≤ M - 1 ∧ endOf a - a ≤ 6 ∧
      isGood (endOf a) ∧ ∀ j, a ≤ j → j < endOf a → ¬ isGood j := by
    intro a ha
    have ha_lt : a < M := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hbad_a : ¬ isGood a := (Finset.mem_filter.mp ha).2.1
    have ha_ne0 : a ≠ 0 := fun h0 => by subst h0; exact hbad_a hgood0
    have ha_ne_last : a ≠ M - 1 := fun h1 => by rw [h1] at hbad_a; exact hbad_a hgood_last
    have ha_lt2 : a < M - 1 := by omega
    obtain ⟨b0, hb0_gt, hb0_leM, hb0_le6, hb0_good⟩ := hex_good_after a ha_lt2 hbad_a
    have hex_b : ∃ b, a < b ∧ isGood b := ⟨b0, hb0_gt, hb0_good⟩
    have hend_eq : endOf a = Nat.find hex_b := by simp only [endOf, hex_b, ↓reduceDIte]
    have hspec := Nat.find_spec hex_b
    have hle_b0 : Nat.find hex_b ≤ b0 := Nat.find_min' hex_b ⟨hb0_gt, hb0_good⟩
    refine ⟨by omega, by omega, by omega, by omega, by rw [hend_eq]; exact hspec.2, ?_⟩
    intro j hja hjlt
    rcases eq_or_lt_of_le hja with rfl | hgt
    · exact hbad_a
    · intro hgoodj
      have hmin := Nat.find_min' hex_b ⟨hgt, hgoodj⟩
      omega
  let runs : Finset (ℕ × ℕ) := badStarts.image (fun a => (a, endOf a))
  refine ⟨runs, ?_, ?_, ?_, ?_⟩
  · intro ab hab
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hab
    obtain ⟨h1, h2, h3, h4, _, _⟩ := hend_spec a ha
    exact ⟨h1, h2, h3, h4⟩
  · intro ab₁ h1 ab₂ h2 hne
    obtain ⟨a₁, ha₁, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨a₂, ha₂, rfl⟩ := Finset.mem_image.mp h2
    have ha_ne : a₁ ≠ a₂ := fun heq => hne (by subst heq; rfl)
    obtain ⟨h1_1, h1_2, _, _, h1_good, h1_bad⟩ := hend_spec a₁ ha₁
    obtain ⟨h2_1, h2_2, _, _, h2_good, h2_bad⟩ := hend_spec a₂ ha₂
    have hprev1 : isGood (a₁ - 1) := by
      rcases (Finset.mem_filter.mp ha₁).2.2 with h0 | hp
      · omega
      · exact hp
    have hprev2 : isGood (a₂ - 1) := by
      rcases (Finset.mem_filter.mp ha₂).2.2 with h0 | hp
      · omega
      · exact hp
    rcases lt_or_gt_of_ne ha_ne with hlt | hgt
    · left
      by_contra! hbad
      rcases lt_or_eq_of_le (show a₂ ≤ endOf a₁ by omega) with hlt2 | heq2
      · exact h1_bad (a₂ - 1) (by omega) (by omega) hprev2
      · rw [← heq2] at h1_good
        exact (Finset.mem_filter.mp ha₂).2.1 h1_good
    · right
      by_contra! hbad
      rcases lt_or_eq_of_le (show a₁ ≤ endOf a₂ by omega) with hlt1 | heq1
      · exact h2_bad (a₁ - 1) (by omega) (by omega) hprev1
      · rw [← heq1] at h2_good
        exact (Finset.mem_filter.mp ha₁).2.1 h2_good
  · -- Bound `runs.card ≤ badStarts.card ≤ 2 * (2T + 2^t - 1)`.
    have hτ_nn : 0 ≤ τ := mul_nonneg (div_nonneg (by norm_num) c474_pos.le) (Real.sqrt_nonneg m)
    have hτ_lt_c0 : τ < cosPoly t 0 := by
      have hsq_pos : 0 < Real.sqrt ((2 : ℝ) ^ (t + 1)) :=
        Real.sqrt_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) (t + 1))
      have hc0 : Real.sqrt ((2 : ℝ) ^ (t + 1)) * (1 / 2) ≤ cosPoly t 0 := by
        rw [cosPoly_eq_Hd, mul_zero]
        exact mul_le_mul_of_nonneg_left (H_near_endpoints r 0 (Or.inl (by norm_num))) hsq_pos.le
      have hη3 : η ^ 3 / 128 < 1 / 2 := by
        have : η ^ 3 ≤ 1 := pow_le_one₀ hη_pos.le (by linarith only [hη_lt])
        linarith only [this]
      have hlt1 : Real.sqrt ((2 : ℝ) ^ (t + 1)) * (η ^ 3 / 128) < Real.sqrt ((2 : ℝ) ^ (t + 1)) * (1 / 2) :=
        mul_lt_mul_of_pos_left hη3 hsq_pos
      exact lt_of_le_of_lt hthresh (lt_of_lt_of_le hlt1 hc0)
    have hstarts : ∀ a ∈ badStarts,
        1 ≤ a ∧ a < M ∧
        (∀ θ ∈ Set.Icc (((a - 1 : ℕ) : ℝ) * step) ((((a - 1 : ℕ) : ℝ) + 1) * step), τ ≤ |cosPoly t θ|) ∧
        ∃ w ∈ Set.Icc ((a : ℝ) * step) (((a : ℝ) + 1) * step), |cosPoly t w| < τ := by
      intro a ha
      obtain ⟨h1, _, _, _, _, _⟩ := hend_spec a ha
      have ha_lt : a < M := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
      have hprev : isGood (a - 1) := by
        rcases (Finset.mem_filter.mp ha).2.2 with h0 | hp
        · omega
        · exact hp
      have hbad_a : ¬ isGood a := (Finset.mem_filter.mp ha).2.1
      dsimp only [isGood] at hbad_a
      push Not at hbad_a
      exact ⟨h1, ha_lt, hprev, hbad_a⟩
    have hcard := cosine_bad_starts_card_le r M step τ hstep_pos hM_step hτ_nn hτ_lt_c0 badStarts hstarts
    exact (Finset.card_image_le).trans hcard
  · -- Any `θ ∈ [0, π/2]` outside all bad runs lies in a good grid interval.
    intro θ hθ hout
    by_cases hright : θ = Real.pi / 2
    · rw [hright]
      apply hgood_last (Real.pi / 2)
      have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast]
      have hlo : ((M : ℝ) - 1) * step ≤ Real.pi / 2 := by
        have h1 := mul_le_mul_of_nonneg_right (show (M : ℝ) - 1 ≤ (M : ℝ) by linarith) hstep_pos.le
        exact h1.trans_eq hM_step
      have hhi : Real.pi / 2 ≤ ((M : ℝ) - 1 + 1) * step := by
        have heq : ((M : ℝ) - 1 + 1) * step = (M : ℝ) * step := by ring
        rw [heq, hM_step]
      exact ⟨hlo, hhi⟩
    · have hlt : θ < Real.pi / 2 := lt_of_le_of_ne hθ.2 hright
      set j : ℕ := Nat.floor (θ / step)
      have hj_lo : (j : ℝ) * step ≤ θ := by
        have := Nat.floor_le (div_nonneg hθ.1 hstep_pos.le)
        exact (le_div_iff₀ hstep_pos).mp this
      have hj_hi : θ ≤ ((j : ℝ) + 1) * step := by
        have := Nat.lt_floor_add_one (θ / step)
        exact le_of_lt ((div_lt_iff₀ hstep_pos).mp this)
      have hj_ltM : j < M := by
        have h1 : θ / step < (M : ℝ) := by
          rw [div_lt_iff₀ hstep_pos, hM_step]; exact hlt
        exact_mod_cast (Nat.floor_lt (div_nonneg hθ.1 hstep_pos.le)).mpr h1
      by_cases hgj : isGood j
      · exact hgj θ ⟨hj_lo, hj_hi⟩
      · exfalso
        have hex_start : ∀ j' : ℕ, j' < M → ¬ isGood j' →
            ∃ a ≤ j', ¬ isGood a ∧ (a = 0 ∨ isGood (a - 1)) ∧ ∀ u, a ≤ u → u ≤ j' → ¬ isGood u := by
          intro j'
          induction j' with
          | zero => intro _ hbad0; exact absurd hgood0 hbad0
          | succ k ih =>
            intro hkM hbadk
            by_cases hgk : isGood k
            · exact ⟨k + 1, le_rfl, hbadk, Or.inr hgk, fun u h1 h2 => by
                have : u = k + 1 := by omega
                subst this; exact hbadk⟩
            · obtain ⟨a, ha_le, hbad_a, hprev_a, hall_bad⟩ := ih (by omega) hgk
              refine ⟨a, by omega, hbad_a, hprev_a, fun u hu1 hu2 => ?_⟩
              rcases eq_or_lt_of_le hu2 with rfl | hlt'
              · exact hbadk
              · exact hall_bad u hu1 (by omega)
        obtain ⟨a, ha_le, hbad_a, hprev_a, hall_bad⟩ := hex_start j hj_ltM hgj
        have ha_mem : a ∈ badStarts := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), hbad_a, hprev_a⟩
        have hrun_mem : (a, endOf a) ∈ runs := Finset.mem_image_of_mem _ ha_mem
        obtain ⟨_, _, _, _, hgood_end, _⟩ := hend_spec a ha_mem
        have hj_lt_end : j < endOf a := by
          by_contra! hge
          exact hall_bad (endOf a) (by omega) hge hgood_end
        have hθ_in : θ ∈ Set.Icc ((a : ℝ) * step) ((endOf a : ℝ) * step) := by
          have ha_r : (a : ℝ) ≤ (j : ℝ) := by exact_mod_cast ha_le
          have hj1_r : (j : ℝ) + 1 ≤ (endOf a : ℝ) := by exact_mod_cast (show j + 1 ≤ endOf a by omega)
          exact ⟨(mul_le_mul_of_nonneg_right ha_r hstep_pos.le).trans hj_lo,
            hj_hi.trans (mul_le_mul_of_nonneg_right hj1_r hstep_pos.le)⟩
        exact hout (a, endOf a) hrun_mem hθ_in

end TwoOrbitCosine

/-!
# Fejér-Smoothed Odd Sine Polynomial & Discrete Flat Littlewood Polynomial

Uses the nonnegative Fejér kernel `fejerK (2*m)` together with `quadInt` (four-quadrant
continuous interval integrals, avoiding discontinuous indicator integrability completely)
to construct an odd sine polynomial `s_o(θ) = ∑_{j < m} ε_j sin ((2j+1) θ)` that is
large on every bad run of the Rudin-Shapiro cosine polynomial at all `n = 3k + 1` roots of unity.
-/

namespace TwoOrbitFejer

open scoped BigOperators ComplexConjugate
open Finset

/-! ### Section 1: Nonnegative Fejér kernel and tail integral bounds -/

private lemma integral_finset_sum_cont {ι : Type*} (s : Finset ι) (a b : ℝ) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    ∫ t in a..b, ∑ i ∈ s, f i t = ∑ i ∈ s, ∫ t in a..b, f i t := by
  classical
  suffices h : Continuous (fun t => ∑ i ∈ s, f i t) ∧
      ∫ t in a..b, ∑ i ∈ s, f i t = ∑ i ∈ s, ∫ t in a..b, f i t from h.2
  induction s using Finset.induction_on with
  | empty => exact ⟨continuous_const, by simp⟩
  | @insert x s hx ih =>
    have hfx : Continuous (f x) := hf x (Finset.mem_insert_self _ _)
    obtain ⟨hfs, hint_s⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨?_, ?_⟩
    · simp_rw [Finset.sum_insert hx]
      exact hfx.add hfs
    · simp_rw [Finset.sum_insert hx]
      rw [intervalIntegral.integral_add (hfx.intervalIntegrable a b) (hfs.intervalIntegrable a b),
        hint_s]

noncomputable def fejerK (N : ℕ) (u : ℝ) : ℝ :=
  1 + 2 * ∑ r ∈ Finset.Ico 1 N, (1 - (r : ℝ) / (N : ℝ)) * Real.cos ((r : ℝ) * u)

lemma fejerK_continuous (N : ℕ) : Continuous (fejerK N) := by
  unfold fejerK
  continuity

lemma fejerK_eq_norm_sq (N : ℕ) (hN : 1 ≤ N) (u : ℝ) :
    (N : ℝ) * fejerK N u = ‖∑ j ∈ range N, Complex.exp (((j : ℝ) * u : ℝ) * Complex.I)‖ ^ 2 := by
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Expand `‖∑_{j < N} e^{i j u}‖^2 = ∑_j ∑_k cos ((j - k) u)`.
  have hnorm_sq : ‖∑ j ∈ range N, Complex.exp (((j : ℝ) * u : ℝ) * Complex.I)‖ ^ 2 =
      ∑ j ∈ range N, ∑ k ∈ range N, Real.cos (((j : ℝ) - (k : ℝ)) * u) := by
    have h1 : ((‖∑ j ∈ range N, Complex.exp (((j : ℝ) * u : ℝ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) =
        (∑ j ∈ range N, Complex.exp (((j : ℝ) * u : ℝ) * Complex.I)) *
          conj (∑ k ∈ range N, Complex.exp (((k : ℝ) * u : ℝ) * Complex.I)) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    have hre := congrArg Complex.re h1
    simp only [Complex.ofReal_re] at hre
    rw [hre, map_sum, Finset.sum_mul, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hconj : conj (Complex.exp (((k : ℝ) * u : ℝ) * Complex.I)) =
        Complex.exp (-(((k : ℝ) * u : ℝ) * Complex.I)) := by
      rw [← Complex.exp_conj]
      simp [Complex.conj_ofReal, Complex.conj_I]
    rw [hconj, ← Complex.exp_add]
    have harg : (((j : ℝ) * u : ℝ) * Complex.I) + -(((k : ℝ) * u : ℝ) * Complex.I) =
        ((((j : ℝ) - (k : ℝ)) * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg, Complex.exp_ofReal_mul_I_re]
  rw [hnorm_sq]
  -- Group pairs `(j, k)` by `j = k`, `j > k` (`r = j - k`), and `j < k` (`r = k - j`).
  have hpair_all : ∀ K : ℕ, 1 ≤ K →
      ∑ j ∈ range K, ∑ k ∈ range K, Real.cos (((j : ℝ) - (k : ℝ)) * u) =
      (K : ℝ) + 2 * ∑ r ∈ Finset.Ico 1 K, ((K - r : ℕ) : ℝ) * Real.cos ((r : ℝ) * u) := by
    intro K
    induction K with
    | zero => intro h0; omega
    | succ M ih =>
      intro _
      by_cases hM : M = 0
      · subst hM; simp
      · have hM1 : 1 ≤ M := Nat.pos_of_ne_zero hM
        rw [Finset.sum_range_succ]
        have hinner : ∀ j ∈ range M,
            ∑ k ∈ range (M + 1), Real.cos (((j : ℝ) - (k : ℝ)) * u) =
            (∑ k ∈ range M, Real.cos (((j : ℝ) - (k : ℝ)) * u)) +
              Real.cos (((M : ℝ) - (j : ℝ)) * u) := by
          intro j _
          rw [Finset.sum_range_succ]
          have hcos_sym : Real.cos (((j : ℝ) - (M : ℝ)) * u) = Real.cos (((M : ℝ) - (j : ℝ)) * u) := by
            rw [← Real.cos_neg]; congr 1; ring
          rw [hcos_sym]
        rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, Finset.sum_range_succ]
        have hdiag : Real.cos (((M : ℝ) - (M : ℝ)) * u) = 1 := by simp
        rw [hdiag, ih hM1]
        have hcross : ∑ j ∈ range M, Real.cos (((M : ℝ) - (j : ℝ)) * u) =
            ∑ r ∈ Finset.Ico 1 (M + 1), Real.cos ((r : ℝ) * u) := by
          refine Finset.sum_bij (fun j _ => M - j) ?_ ?_ ?_ ?_
          · intro j hj; rw [Finset.mem_Ico]; have := Finset.mem_range.mp hj; omega
          · intro j₁ h1 j₂ h2 hEq; have := Finset.mem_range.mp h1; have := Finset.mem_range.mp h2; omega
          · intro r hr; rw [Finset.mem_Ico] at hr
            exact ⟨M - r, Finset.mem_range.mpr (by omega), by omega⟩
          · intro j hj
            have hjlt : j < M := Finset.mem_range.mp hj
            rw [Nat.cast_sub (le_of_lt hjlt)]
        rw [hcross]
        -- Combine `∑_{1..M-1} (M - r) cos(ru) + ∑_{1..M} cos(ru) = ∑_{1..M} (M + 1 - r) cos(ru)`.
        have hIco : Finset.Ico 1 (M + 1) = insert M (Finset.Ico 1 M) := by
          ext r; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
        have hM_not : M ∉ Finset.Ico 1 M := by simp
        rw [hIco, Finset.sum_insert hM_not, Finset.sum_insert hM_not]
        have hMsub : ((M + 1 - M : ℕ) : ℝ) = 1 := by norm_num
        rw [hMsub, one_mul]
        have hcomb : ∑ r ∈ Finset.Ico 1 M, ((M - r : ℕ) : ℝ) * Real.cos ((r : ℝ) * u) +
            ∑ r ∈ Finset.Ico 1 M, Real.cos ((r : ℝ) * u) =
            ∑ r ∈ Finset.Ico 1 M, ((M + 1 - r : ℕ) : ℝ) * Real.cos ((r : ℝ) * u) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r hr => ?_
          have hrlt : r < M := (Finset.mem_Ico.mp hr).2
          have hsub : M + 1 - r = (M - r) + 1 := by omega
          rw [hsub, Nat.cast_add, Nat.cast_one]; ring
        set S1 := ∑ r ∈ Finset.Ico 1 M, ((M - r : ℕ) : ℝ) * Real.cos ((r : ℝ) * u)
        set S2 := ∑ r ∈ Finset.Ico 1 M, Real.cos ((r : ℝ) * u)
        set S3 := ∑ r ∈ Finset.Ico 1 M, ((M + 1 - r : ℕ) : ℝ) * Real.cos ((r : ℝ) * u)
        push_cast
        linarith [hcomb]
  rw [hpair_all N hN]
  unfold fejerK
  rw [mul_add, mul_one, mul_left_comm, Finset.mul_sum]
  congr 1; congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrlt : r < N := (Finset.mem_Ico.mp hr).2
  rw [Nat.cast_sub (le_of_lt hrlt)]
  field_simp [hN_ne]

lemma fejerK_nonneg (N : ℕ) (hN : 1 ≤ N) (u : ℝ) : 0 ≤ fejerK N u := by
  have h := fejerK_eq_norm_sq N hN u
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  nlinarith [sq_nonneg ‖∑ j ∈ range N, Complex.exp (((j : ℝ) * u : ℝ) * Complex.I)‖]

lemma fejerK_le_inv_sin_sq (N : ℕ) (hN : 1 ≤ N) (u : ℝ) (hsin : Real.sin (u / 2) ≠ 0) :
    fejerK N u ≤ 1 / ((N : ℝ) * Real.sin (u / 2) ^ 2) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set z : ℂ := Complex.exp ((u : ℂ) * Complex.I)
  have hz_norm : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I u
  have hz_sub_sq : ‖z - 1‖ ^ 2 = 4 * Real.sin (u / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [z, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    have h1 := Real.sin_sq_add_cos_sq u
    have h2 : Real.cos u = 1 - 2 * Real.sin (u / 2) ^ 2 := by
      have hu : u = 2 * (u / 2) := by ring
      conv_lhs => rw [hu]
      rw [Real.cos_two_mul]
      have := Real.sin_sq_add_cos_sq (u / 2)
      nlinarith
    nlinarith
  have hz_ne1 : z ≠ 1 := by
    intro h1
    rw [h1, sub_self, norm_zero, zero_pow (by norm_num)] at hz_sub_sq
    have : Real.sin (u / 2) ^ 2 = 0 := by linarith
    exact hsin (sq_eq_zero_iff.mp this)
  have hsum_eq : ∑ j ∈ range N, Complex.exp (((j : ℝ) * u : ℝ) * Complex.I) = ∑ j ∈ range N, z ^ j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only [z]
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hgeom_bound : ‖∑ j ∈ range N, z ^ j‖ ^ 2 ≤ 1 / Real.sin (u / 2) ^ 2 := by
    rw [geom_sum_eq hz_ne1, norm_div, div_pow, hz_sub_sq]
    have hnum : ‖z ^ N - 1‖ ≤ 2 := by
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hz_norm, one_pow, norm_one]; norm_num
    have hnum_sq : ‖z ^ N - 1‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (z ^ N - 1)]
    have hsin_sq_pos : 0 < Real.sin (u / 2) ^ 2 := sq_pos_of_ne_zero hsin
    rw [div_le_div_iff₀ (by positivity) hsin_sq_pos]
    nlinarith
  have hEq := fejerK_eq_norm_sq N hN u
  rw [hsum_eq] at hEq
  rw [le_div_iff₀ (by positivity)]
  have hmul : (N : ℝ) * fejerK N u * Real.sin (u / 2) ^ 2 ≤ 1 := by
    rw [hEq]
    have := (le_div_iff₀ (sq_pos_of_ne_zero hsin)).mp hgeom_bound
    linarith
  linarith

lemma integral_cos_full_period (r : ℕ) (hr : 1 ≤ r) (θ₀ : ℝ) :
    ∫ t in (-Real.pi)..Real.pi, Real.cos ((r : ℝ) * (θ₀ - t)) = 0 := by
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let F : ℝ → ℝ := fun t => -Real.sin ((r : ℝ) * (θ₀ - t)) / (r : ℝ)
  have hderiv : ∀ t ∈ Set.uIcc (-Real.pi) Real.pi, HasDerivAt F (Real.cos ((r : ℝ) * (θ₀ - t))) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => (r : ℝ) * (θ₀ - x)) (-(r : ℝ)) t :=
      (((hasDerivAt_const t θ₀).sub (hasDerivAt_id' t)).const_mul (r : ℝ)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun x : ℝ => Real.sin ((r : ℝ) * (θ₀ - x)))
        (Real.cos ((r : ℝ) * (θ₀ - t)) * -(r : ℝ)) t := by
      simpa [Function.comp_def] using (Real.hasDerivAt_sin ((r : ℝ) * (θ₀ - t))).comp t h1
    exact ((h2.neg).div_const (r : ℝ)).congr_deriv (by field_simp [hr_ne])
  have hint : IntervalIntegrable (fun t => Real.cos ((r : ℝ) * (θ₀ - t))) MeasureTheory.volume (-Real.pi) Real.pi :=
    (by continuity : Continuous (fun t => Real.cos ((r : ℝ) * (θ₀ - t)))).intervalIntegrable (-Real.pi) Real.pi
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp only [F]
  have hper : Real.sin ((r : ℝ) * (θ₀ - (-Real.pi))) = Real.sin ((r : ℝ) * (θ₀ - Real.pi)) := by
    have harg : (r : ℝ) * (θ₀ - (-Real.pi)) = (r : ℝ) * (θ₀ - Real.pi) + (r : ℤ) * (2 * Real.pi) := by
      push_cast; ring
    rw [harg, Real.sin_add_int_mul_two_pi]
  rw [hper, sub_self]

lemma integral_fejerK_sub (N : ℕ) (θ₀ : ℝ) :
    ∫ t in (-Real.pi)..Real.pi, fejerK N (θ₀ - t) = 2 * Real.pi := by
  unfold fejerK
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (Continuous.intervalIntegrable (by continuity) _ _),
    intervalIntegral.integral_const, smul_eq_mul, mul_one,
    intervalIntegral.integral_const_mul,
    integral_finset_sum_cont _ (-Real.pi) Real.pi _ (fun r _ => by continuity)]
  have hzero : ∑ r ∈ Finset.Ico 1 N,
      ∫ t in (-Real.pi)..Real.pi, (1 - (r : ℝ) / (N : ℝ)) * Real.cos ((r : ℝ) * (θ₀ - t)) = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [intervalIntegral.integral_const_mul, integral_cos_full_period r (Finset.mem_Ico.mp hr).1 θ₀,
      mul_zero]
  rw [hzero, mul_zero, add_zero]; ring

lemma integral_inv_sq_sub (c a b : ℝ) (hca : c < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / (t - c) ^ 2 = 1 / (a - c) - 1 / (b - c) := by
  let F : ℝ → ℝ := fun t => -(1 / (t - c))
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt F (1 / (t - c) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have hne : t - c ≠ 0 := by linarith [ht.1]
    have h1 : HasDerivAt (fun x => x - c) 1 t := (hasDerivAt_id t).sub_const c
    have h2 : HasDerivAt (fun x => (x - c)⁻¹) (-(1 / (t - c) ^ 2)) t := by
      convert h1.inv hne using 1; ring
    convert h2.neg using 1
    · ext x; simp [F, one_div]
    · ring
  have hint : IntervalIntegrable (fun t => 1 / (t - c) ^ 2) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro t ht
    have hne : (t - c) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [ht.1])
    exact (continuousAt_const.div ((continuousAt_id.sub continuousAt_const).pow 2) hne).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp only [F]; ring

lemma integral_inv_sq_sub_rev (c a b : ℝ) (hab : a ≤ b) (hbc : b < c) :
    ∫ t in a..b, 1 / (c - t) ^ 2 = 1 / (c - b) - 1 / (c - a) := by
  let F : ℝ → ℝ := fun t => 1 / (c - t)
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt F (1 / (c - t) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have hne : c - t ≠ 0 := by linarith [ht.2]
    have h1 : HasDerivAt (fun x : ℝ => c - x) (-1) t :=
      ((hasDerivAt_const t c).sub (hasDerivAt_id' t)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun x => (c - x)⁻¹) (1 / (c - t) ^ 2) t :=
      (h1.inv hne).congr_deriv (by ring)
    simpa [F, one_div] using h2
  have hint : IntervalIntegrable (fun t => 1 / (c - t) ^ 2) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro t ht
    have hne : (c - t) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [ht.2])
    exact (continuousAt_const.div ((continuousAt_const.sub continuousAt_id).pow 2) hne).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]

/-- Tail integral bound for the Fejér kernel `fejerK (2 * m)` outside `[θ₀ - δ, θ₀ + δ]`
with `θ₀ ∈ (0, π/2)` and `δ = 4π / m`. -/
lemma integral_fejerK_outside_le (m : ℕ) (hm : 32 ≤ m) {θ₀ : ℝ}
    (hθ₀_lo : 4 * Real.pi / (m : ℝ) < θ₀) (hθ₀_hi : θ₀ < Real.pi / 2 - 4 * Real.pi / (m : ℝ)) :
    let δ : ℝ := 4 * Real.pi / (m : ℝ)
    (∫ t in (-Real.pi)..(θ₀ - δ), fejerK (2 * m) (θ₀ - t)) +
    (∫ t in (θ₀ + δ)..Real.pi, fejerK (2 * m) (θ₀ - t)) ≤ 3 * Real.pi / 8 := by
  intro δ
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h2m1 : 1 ≤ 2 * m := by omega
  -- Helper: on `[θ₀ + δ, π]`, `fejerK (2m) (θ₀ - t) ≤ π^2 / (2m * (t - θ₀)^2)`.
  have hright : ∫ t in (θ₀ + δ)..Real.pi, fejerK (2 * m) (θ₀ - t) ≤ Real.pi / 8 := by
    have hab : θ₀ + δ ≤ Real.pi := by linarith
    have hpt : ∀ t ∈ Set.Icc (θ₀ + δ) Real.pi,
        fejerK (2 * m) (θ₀ - t) ≤ (Real.pi ^ 2 / (2 * (m : ℝ))) * (1 / (t - θ₀) ^ 2) := by
      intro t ht
      have hu0 : 0 ≤ (t - θ₀) / 2 := by linarith [ht.1]
      have hu1 : (t - θ₀) / 2 ≤ Real.pi / 2 := by linarith [ht.2, hθ₀_lo]
      have hsin_ge : (t - θ₀) / Real.pi ≤ Real.sin ((t - θ₀) / 2) := by
        have h := Real.mul_le_sin hu0 hu1
        have heq : 2 / Real.pi * ((t - θ₀) / 2) = (t - θ₀) / Real.pi := by field_simp [hpi_pos.ne']
        linarith
      have hsin_pos : 0 < Real.sin ((t - θ₀) / 2) := lt_of_lt_of_le (by
        have : 0 < t - θ₀ := by linarith [ht.1]
        positivity) hsin_ge
      have hsin_eq : Real.sin ((θ₀ - t) / 2) ^ 2 = Real.sin ((t - θ₀) / 2) ^ 2 := by
        have : (θ₀ - t) / 2 = -((t - θ₀) / 2) := by ring
        rw [this, Real.sin_neg, neg_sq]
      have hsin_ne : Real.sin ((θ₀ - t) / 2) ≠ 0 := by
        intro h0; rw [h0, zero_pow (by norm_num)] at hsin_eq
        exact hsin_pos.ne' (sq_eq_zero_iff.mp hsin_eq.symm)
      have hfe := fejerK_le_inv_sin_sq (2 * m) h2m1 (θ₀ - t) hsin_ne
      rw [hsin_eq] at hfe
      have ht_pos : 0 < t - θ₀ := by linarith [ht.1]
      have hsq_ge : ((t - θ₀) / Real.pi) ^ 2 ≤ Real.sin ((t - θ₀) / 2) ^ 2 :=
        pow_le_pow_left₀ (div_nonneg ht_pos.le hpi_pos.le) hsin_ge 2
      have hden_pos : 0 < (2 * (m : ℝ)) * ((t - θ₀) / Real.pi) ^ 2 := by positivity
      have hcast2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
      rw [hcast2m] at hfe
      calc fejerK (2 * m) (θ₀ - t) ≤ 1 / ((2 * (m : ℝ)) * Real.sin ((t - θ₀) / 2) ^ 2) := hfe
        _ ≤ 1 / ((2 * (m : ℝ)) * ((t - θ₀) / Real.pi) ^ 2) :=
            one_div_le_one_div_of_le hden_pos (mul_le_mul_of_nonneg_left hsq_ge (by positivity))
        _ = (Real.pi ^ 2 / (2 * (m : ℝ))) * (1 / (t - θ₀) ^ 2) := by
            field_simp [hpi_pos.ne', hm_pos.ne', (show t - θ₀ ≠ 0 by linarith [ht.1])]
    have hint1 : IntervalIntegrable (fun t => fejerK (2 * m) (θ₀ - t)) MeasureTheory.volume (θ₀ + δ) Real.pi :=
      ((fejerK_continuous (2 * m)).comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
    have hint2 : IntervalIntegrable (fun t => (Real.pi ^ 2 / (2 * (m : ℝ))) * (1 / (t - θ₀) ^ 2))
        MeasureTheory.volume (θ₀ + δ) Real.pi := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hab]
      intro t ht
      have hne : (t - θ₀) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [ht.1])
      exact (continuousAt_const.mul (continuousAt_const.div ((continuousAt_id.sub continuousAt_const).pow 2) hne)).continuousWithinAt
    have hmono := intervalIntegral.integral_mono_on hab hint1 hint2 hpt
    rw [intervalIntegral.integral_const_mul, integral_inv_sq_sub θ₀ (θ₀ + δ) Real.pi (by linarith) hab] at hmono
    have hsub_le : 1 / (θ₀ + δ - θ₀) - 1 / (Real.pi - θ₀) ≤ 1 / δ := by
      rw [add_sub_cancel_left]
      have : 0 ≤ 1 / (Real.pi - θ₀) := by
        have : 0 < Real.pi - θ₀ := by linarith
        positivity
      linarith
    calc ∫ t in (θ₀ + δ)..Real.pi, fejerK (2 * m) (θ₀ - t)
        ≤ (Real.pi ^ 2 / (2 * (m : ℝ))) * (1 / δ) :=
          hmono.trans (mul_le_mul_of_nonneg_left hsub_le (by positivity))
      _ = Real.pi / 8 := by dsimp only [δ]; field_simp [hm_pos.ne', hpi_pos.ne']; ring
  -- Split `[-π, θ₀ - δ]` into `[-π, θ₀ - π]` and `[θ₀ - π, θ₀ - δ]`.
  have hsplit_left :
      ∫ t in (-Real.pi)..(θ₀ - δ), fejerK (2 * m) (θ₀ - t) =
      (∫ t in (-Real.pi)..(θ₀ - Real.pi), fejerK (2 * m) (θ₀ - t)) +
      (∫ t in (θ₀ - Real.pi)..(θ₀ - δ), fejerK (2 * m) (θ₀ - t)) := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals
      (((fejerK_continuous (2 * m)).comp (continuous_const.sub continuous_id)).intervalIntegrable _ _)
      (((fejerK_continuous (2 * m)).comp (continuous_const.sub continuous_id)).intervalIntegrable _ _)
  -- Middle-left piece `[θ₀ - π, θ₀ - δ]`: same bound `≤ π / 8`.
  have hmid_left : ∫ t in (θ₀ - Real.pi)..(θ₀ - δ), fejerK (2 * m) (θ₀ - t) ≤ Real.pi / 8 := by
    have hab : θ₀ - Real.pi ≤ θ₀ - δ := by
      have : δ ≤ Real.pi := by
        dsimp only [δ]
        rw [div_le_iff₀ hm_pos]
        have hm32 : (32 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        nlinarith
      linarith
    have hpt : ∀ t ∈ Set.Icc (θ₀ - Real.pi) (θ₀ - δ),
        fejerK (2 * m) (θ₀ - t) ≤ (Real.pi ^ 2 / (2 * (m : ℝ))) * (1 / (θ₀ - t) ^ 2) := by
      intro t ht
      have hu0 : 0 ≤ (θ₀ - t) / 2 := by linarith [ht.2]
      have hu1 : (θ₀ - t) / 2 ≤ Real.pi / 2 := by linarith [ht.1]
      have hsin_ge : (θ₀ - t) / Real.pi ≤ Real.sin ((θ₀ - t) / 2) := by
        have h := Real.mul_le_sin hu0 hu1
        have heq : 2 / Real.pi * ((θ₀ - t) / 2) = (θ₀ - t) / Real.pi := by field_simp [hpi_pos.ne']
        linarith
      have hsin_pos : 0 < Real.sin ((θ₀ - t) / 2) := lt_of_lt_of_le (by
        have : 0 < θ₀ - t := by linarith [ht.2]
        positivity) hsin_ge
      have hfe := fejerK_le_inv_sin_sq (2 * m) h2m1 (θ₀ - t) hsin_pos.ne'
      have ht_pos : 0 < θ₀ - t := by linarith [ht.2]
      have hsq_ge : ((θ₀ - t) / Real.pi) ^ 2 ≤ Real.sin ((θ₀ - t) / 2) ^ 2 :=
        pow_le_pow_left₀ (div_nonneg ht_pos.le hpi_pos.le) hsin_ge 2
      have hden_pos : 0 < (2 * (m : ℝ)) * ((θ₀ - t) / Real.pi) ^ 2 := by positivity
      have hcast2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
      rw [hcast2m] at hfe
      calc fejerK (2 * m) (θ₀ - t) ≤ 1 / ((2 * (m : ℝ)) * Real.sin ((θ₀ - t) / 2) ^ 2) := hfe
        _ ≤ 1 / ((2 * (m : ℝ)) * ((θ₀ - t) / Real.pi) ^ 2) :=
            one_div_le_one_div_of_le hden_pos (mul_le_mul_of_nonneg_left hsq_ge (by positivity))
        _ = (Real.pi ^ 2 / (2 * (m : ℝ))) * (1 / (θ₀ - t) ^ 2) := by
            field_simp [hpi_pos.ne', hm_pos.ne', (show θ₀ - t ≠ 0 by linarith [ht.2])]
    have hint1 : IntervalIntegrable (fun t => fejerK (2 * m) (θ₀ - t)) MeasureTheory.volume (θ₀ - Real.pi) (θ₀ - δ) :=
      ((fejerK_continuous (2 * m)).comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
    have hint2 : IntervalIntegrable (fun t => (Real.pi ^ 2 / (2 * (m : ℝ))) * (1 / (θ₀ - t) ^ 2))
        MeasureTheory.volume (θ₀ - Real.pi) (θ₀ - δ) := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hab]
      intro t ht
      have hne : (θ₀ - t) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [ht.2])
      exact (continuousAt_const.mul (continuousAt_const.div ((continuousAt_const.sub continuousAt_id).pow 2) hne)).continuousWithinAt
    have hmono := intervalIntegral.integral_mono_on hab hint1 hint2 hpt
    rw [intervalIntegral.integral_const_mul, integral_inv_sq_sub_rev θ₀ (θ₀ - Real.pi) (θ₀ - δ) hab (by linarith)] at hmono
    have hsub_le : 1 / (θ₀ - (θ₀ - δ)) - 1 / (θ₀ - (θ₀ - Real.pi)) ≤ 1 / δ := by
      have : θ₀ - (θ₀ - δ) = δ := by ring
      have : θ₀ - (θ₀ - Real.pi) = Real.pi := by ring
      rw [‹θ₀ - (θ₀ - δ) = δ›, ‹θ₀ - (θ₀ - Real.pi) = Real.pi›]
      have : 0 ≤ 1 / Real.pi := by positivity
      linarith
    calc ∫ t in (θ₀ - Real.pi)..(θ₀ - δ), fejerK (2 * m) (θ₀ - t)
        ≤ (Real.pi ^ 2 / (2 * (m : ℝ))) * (1 / δ) :=
          hmono.trans (mul_le_mul_of_nonneg_left hsub_le (by positivity))
      _ = Real.pi / 8 := by dsimp only [δ]; field_simp [hm_pos.ne', hpi_pos.ne']; ring
  -- Far-left piece `[-π, θ₀ - π]`: `(θ₀ - t)/2 ∈ [π/2, 3π/4]`, so `sin ≥ 1/2`, `fejerK ≤ 2/m`.
  have hfar_left : ∫ t in (-Real.pi)..(θ₀ - Real.pi), fejerK (2 * m) (θ₀ - t) ≤ Real.pi / 8 := by
    have hab : -Real.pi ≤ θ₀ - Real.pi := by linarith
    have hpt : ∀ t ∈ Set.Icc (-Real.pi) (θ₀ - Real.pi),
        fejerK (2 * m) (θ₀ - t) ≤ 2 / (m : ℝ) := by
      intro t ht
      have hu_lo : Real.pi / 2 ≤ (θ₀ - t) / 2 := by linarith [ht.2]
      have hu_hi : (θ₀ - t) / 2 ≤ 3 * Real.pi / 4 := by linarith [ht.1, hθ₀_hi]
      -- `sin ((θ₀ - t)/2) = sin (π - (θ₀ - t)/2) ≥ (2/π) * (π - (θ₀ - t)/2) ≥ (2/π) * (π/4) = 1/2`.
      have hw0 : 0 ≤ Real.pi - (θ₀ - t) / 2 := by linarith
      have hw1 : Real.pi - (θ₀ - t) / 2 ≤ Real.pi / 2 := by linarith
      have hsin_ge : 1 / 2 ≤ Real.sin ((θ₀ - t) / 2) := by
        rw [← Real.sin_pi_sub]
        have h := Real.mul_le_sin hw0 hw1
        have hlow : Real.pi / 4 ≤ Real.pi - (θ₀ - t) / 2 := by linarith
        have hmul : 2 / Real.pi * (Real.pi / 4) ≤ 2 / Real.pi * (Real.pi - (θ₀ - t) / 2) :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
        have hval : 2 / Real.pi * (Real.pi / 4) = 1 / 2 := by field_simp [hpi_pos.ne']; ring
        linarith
      have hsin_pos : 0 < Real.sin ((θ₀ - t) / 2) := by linarith
      have hfe := fejerK_le_inv_sin_sq (2 * m) h2m1 (θ₀ - t) hsin_pos.ne'
      have hsq : (1 / 4 : ℝ) ≤ Real.sin ((θ₀ - t) / 2) ^ 2 := by nlinarith
      have hcast2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
      rw [hcast2m] at hfe
      calc fejerK (2 * m) (θ₀ - t) ≤ 1 / ((2 * (m : ℝ)) * Real.sin ((θ₀ - t) / 2) ^ 2) := hfe
        _ ≤ 1 / ((2 * (m : ℝ)) * (1 / 4)) :=
            one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hsq (by positivity))
        _ = 2 / (m : ℝ) := by field_simp [hm_pos.ne']; ring
    have hint1 : IntervalIntegrable (fun t => fejerK (2 * m) (θ₀ - t)) MeasureTheory.volume (-Real.pi) (θ₀ - Real.pi) :=
      ((fejerK_continuous (2 * m)).comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on hab hint1 intervalIntegrable_const hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hlen : θ₀ - Real.pi - (-Real.pi) ≤ Real.pi / 2 := by linarith
    have hm32 : (32 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hprod : (θ₀ - Real.pi - (-Real.pi)) * (2 / (m : ℝ)) ≤ (Real.pi / 2) * (2 / 32) := by
      apply mul_le_mul hlen (by exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm32)
        (by positivity) (by positivity)
    linarith
  linarith

/-! ### Section 2: Four-quadrant continuous integral functional `quadInt` -/

noncomputable def quadInt (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ t in a..b, f t) + (∫ t in (Real.pi - b)..(Real.pi - a), f t) -
  (∫ t in (-b)..(-a), f t) - (∫ t in (a - Real.pi)..(b - Real.pi), f t)

lemma quadInt_add (a b : ℝ) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    quadInt a b (fun t => f t + g t) = quadInt a b f + quadInt a b g := by
  unfold quadInt
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
    intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
    intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
    intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

lemma quadInt_const_mul (a b c : ℝ) (f : ℝ → ℝ) :
    quadInt a b (fun t => c * f t) = c * quadInt a b f := by
  unfold quadInt
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

lemma quadInt_finset_sum {ι : Type*} (s : Finset ι) (a b : ℝ) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    quadInt a b (fun t => ∑ i ∈ s, f i t) = ∑ i ∈ s, quadInt a b (f i) := by
  unfold quadInt
  rw [integral_finset_sum_cont s a b f hf,
    integral_finset_sum_cont s (Real.pi - b) (Real.pi - a) f hf,
    integral_finset_sum_cont s (-b) (-a) f hf,
    integral_finset_sum_cont s (a - Real.pi) (b - Real.pi) f hf]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

lemma quadInt_const (a b c : ℝ) : quadInt a b (fun _ => c) = 0 := by
  unfold quadInt
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma quadInt_cos (a b : ℝ) (r : ℕ) : quadInt a b (fun t => Real.cos ((r : ℝ) * t)) = 0 := by
  unfold quadInt
  -- `∫_{-b}^{-a} cos(rt) = ∫_a^b cos(rt)` and `∫_{a-π}^{b-π} cos(rt) = ∫_{π-b}^{π-a} cos(rt)`.
  have h1 : ∫ t in (-b)..(-a), Real.cos ((r : ℝ) * t) = ∫ t in a..b, Real.cos ((r : ℝ) * t) := by
    have h := intervalIntegral.integral_comp_neg (f := fun t => Real.cos ((r : ℝ) * t)) (a := a) (b := b)
    simpa [mul_neg, Real.cos_neg] using h.symm
  have h2 : ∫ t in (a - Real.pi)..(b - Real.pi), Real.cos ((r : ℝ) * t) =
      ∫ t in (Real.pi - b)..(Real.pi - a), Real.cos ((r : ℝ) * t) := by
    have h := intervalIntegral.integral_comp_neg (f := fun t => Real.cos ((r : ℝ) * t))
      (a := Real.pi - b) (b := Real.pi - a)
    have hlo : -(Real.pi - a) = a - Real.pi := by ring
    have hhi : -(Real.pi - b) = b - Real.pi := by ring
    rw [hlo, hhi] at h
    simpa [mul_neg, Real.cos_neg] using h.symm
  rw [h1, h2]; ring

lemma quadInt_sin_even (a b : ℝ) (k : ℕ) :
    quadInt a b (fun t => Real.sin (((2 * k : ℕ) : ℝ) * t)) = 0 := by
  unfold quadInt
  have h1 : ∫ t in (Real.pi - b)..(Real.pi - a), Real.sin (((2 * k : ℕ) : ℝ) * t) =
      -(∫ t in a..b, Real.sin (((2 * k : ℕ) : ℝ) * t)) := by
    have h := intervalIntegral.integral_comp_sub_left
      (f := fun t => Real.sin (((2 * k : ℕ) : ℝ) * t)) Real.pi (a := a) (b := b)
    have hfn : ∀ t : ℝ, Real.sin (((2 * k : ℕ) : ℝ) * (Real.pi - t)) =
        -Real.sin (((2 * k : ℕ) : ℝ) * t) := by
      intro t
      have harg : ((2 * k : ℕ) : ℝ) * (Real.pi - t) = -(((2 * k : ℕ) : ℝ) * t) + (k : ℤ) * (2 * Real.pi) := by
        push_cast; ring
      rw [harg, Real.sin_add_int_mul_two_pi, Real.sin_neg]
    simp_rw [hfn, intervalIntegral.integral_neg] at h
    exact h.symm
  have h2 : ∫ t in (-b)..(-a), Real.sin (((2 * k : ℕ) : ℝ) * t) =
      -(∫ t in a..b, Real.sin (((2 * k : ℕ) : ℝ) * t)) := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun t => Real.sin (((2 * k : ℕ) : ℝ) * t)) (a := a) (b := b)
    simp_rw [mul_neg, Real.sin_neg, intervalIntegral.integral_neg] at h
    exact h.symm
  have h3 : ∫ t in (a - Real.pi)..(b - Real.pi), Real.sin (((2 * k : ℕ) : ℝ) * t) =
      ∫ t in a..b, Real.sin (((2 * k : ℕ) : ℝ) * t) := by
    have h := intervalIntegral.integral_comp_sub_right
      (f := fun t => Real.sin (((2 * k : ℕ) : ℝ) * t)) Real.pi (a := a) (b := b)
    have hfn : ∀ t : ℝ, Real.sin (((2 * k : ℕ) : ℝ) * (t - Real.pi)) =
        Real.sin (((2 * k : ℕ) : ℝ) * t) := by
      intro t
      have harg : ((2 * k : ℕ) : ℝ) * (t - Real.pi) = ((2 * k : ℕ) : ℝ) * t + (-k : ℤ) * (2 * Real.pi) := by
        push_cast; ring
      rw [harg, Real.sin_add_int_mul_two_pi]
    simp_rw [hfn] at h
    exact h.symm
  rw [h1, h2, h3]; ring

lemma quadInt_sin_odd (a b : ℝ) (j : ℕ) :
    quadInt a b (fun t => Real.sin (((2 * j + 1 : ℕ) : ℝ) * t)) =
      4 * ∫ t in a..b, Real.sin (((2 * j + 1 : ℕ) : ℝ) * t) := by
  unfold quadInt
  have h1 : ∫ t in (Real.pi - b)..(Real.pi - a), Real.sin (((2 * j + 1 : ℕ) : ℝ) * t) =
      ∫ t in a..b, Real.sin (((2 * j + 1 : ℕ) : ℝ) * t) := by
    have h := intervalIntegral.integral_comp_sub_left
      (f := fun t => Real.sin (((2 * j + 1 : ℕ) : ℝ) * t)) Real.pi (a := a) (b := b)
    have hfn : ∀ t : ℝ, Real.sin (((2 * j + 1 : ℕ) : ℝ) * (Real.pi - t)) =
        Real.sin (((2 * j + 1 : ℕ) : ℝ) * t) := by
      intro t
      have harg : ((2 * j + 1 : ℕ) : ℝ) * (Real.pi - t) =
          (Real.pi - ((2 * j + 1 : ℕ) : ℝ) * t) + (j : ℤ) * (2 * Real.pi) := by
        push_cast; ring
      rw [harg, Real.sin_add_int_mul_two_pi, Real.sin_pi_sub]
    simp_rw [hfn] at h
    exact h.symm
  have h2 : ∫ t in (-b)..(-a), Real.sin (((2 * j + 1 : ℕ) : ℝ) * t) =
      -(∫ t in a..b, Real.sin (((2 * j + 1 : ℕ) : ℝ) * t)) := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun t => Real.sin (((2 * j + 1 : ℕ) : ℝ) * t)) (a := a) (b := b)
    simp_rw [mul_neg, Real.sin_neg, intervalIntegral.integral_neg] at h
    exact h.symm
  have h3 : ∫ t in (a - Real.pi)..(b - Real.pi), Real.sin (((2 * j + 1 : ℕ) : ℝ) * t) =
      -(∫ t in a..b, Real.sin (((2 * j + 1 : ℕ) : ℝ) * t)) := by
    have h := intervalIntegral.integral_comp_sub_right
      (f := fun t => Real.sin (((2 * j + 1 : ℕ) : ℝ) * t)) Real.pi (a := a) (b := b)
    have hfn : ∀ t : ℝ, Real.sin (((2 * j + 1 : ℕ) : ℝ) * (t - Real.pi)) =
        -Real.sin (((2 * j + 1 : ℕ) : ℝ) * t) := by
      intro t
      have harg : ((2 * j + 1 : ℕ) : ℝ) * (t - Real.pi) =
          (((2 * j + 1 : ℕ) : ℝ) * t - Real.pi) + (-j : ℤ) * (2 * Real.pi) := by
        push_cast; ring
      rw [harg, Real.sin_add_int_mul_two_pi, Real.sin_sub_pi]
    simp_rw [hfn, intervalIntegral.integral_neg] at h
    exact h.symm
  rw [h1, h2, h3]; ring

/-- Key identity: the Fejér convolution of `quadInt a b` is an exact odd sine polynomial! -/
lemma quadInt_fejerK_eq (m : ℕ) (a b θ : ℝ) :
    (1 / (2 * Real.pi)) * quadInt a b (fun t => fejerK (2 * m) (θ - t)) =
      ∑ j ∈ range m,
        ((1 - ((2 * j + 1 : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ)) *
          (4 / Real.pi * ∫ t in a..b, Real.sin (((2 * j + 1 : ℕ) : ℝ) * t))) *
        Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ) := by
  unfold fejerK
  rw [quadInt_add a b (fun _ => (1 : ℝ)) _ continuous_const (by continuity),
    quadInt_const, zero_add, quadInt_const_mul,
    quadInt_finset_sum _ a b _ (fun r _ => by continuity)]
  have hterm : ∀ r ∈ Finset.Ico 1 (2 * m),
      quadInt a b (fun t => (1 - (r : ℝ) / ((2 * m : ℕ) : ℝ)) * Real.cos ((r : ℝ) * (θ - t))) =
      (1 - (r : ℝ) / ((2 * m : ℕ) : ℝ)) * Real.sin ((r : ℝ) * θ) *
        quadInt a b (fun t => Real.sin ((r : ℝ) * t)) := by
    intro r _
    rw [quadInt_const_mul]
    have hcos_sub : (fun t => Real.cos ((r : ℝ) * (θ - t))) =
        (fun t => Real.cos ((r : ℝ) * θ) * Real.cos ((r : ℝ) * t) +
                  Real.sin ((r : ℝ) * θ) * Real.sin ((r : ℝ) * t)) := by
      ext t
      have : (r : ℝ) * (θ - t) = (r : ℝ) * θ - (r : ℝ) * t := by ring
      rw [this, Real.cos_sub]
    rw [hcos_sub, quadInt_add a b _ _ (by continuity) (by continuity),
      quadInt_const_mul, quadInt_cos, mul_zero, zero_add, quadInt_const_mul]
    ring
  rw [Finset.sum_congr rfl hterm]
  -- Drop even `r` (where `quadInt_sin_even` gives 0) and reindex odd `r = 2*j + 1`.
  have hfilter : ∑ r ∈ Finset.Ico 1 (2 * m),
      (1 - (r : ℝ) / ((2 * m : ℕ) : ℝ)) * Real.sin ((r : ℝ) * θ) *
        quadInt a b (fun t => Real.sin ((r : ℝ) * t)) =
      ∑ r ∈ (Finset.Ico 1 (2 * m)).filter (fun r => r % 2 = 1),
        (1 - (r : ℝ) / ((2 * m : ℕ) : ℝ)) * Real.sin ((r : ℝ) * θ) *
          quadInt a b (fun t => Real.sin ((r : ℝ) * t)) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun r hr hnot => ?_
    have hev : r % 2 = 0 := by
      have : ¬ (r % 2 = 1) := fun h => hnot (Finset.mem_filter.mpr ⟨hr, h⟩)
      omega
    have hr2 : r = 2 * (r / 2) := by omega
    rw [hr2, quadInt_sin_even, mul_zero]
  rw [hfilter]
  have hbij : ∑ r ∈ (Finset.Ico 1 (2 * m)).filter (fun r => r % 2 = 1),
      (1 - (r : ℝ) / ((2 * m : ℕ) : ℝ)) * Real.sin ((r : ℝ) * θ) *
        quadInt a b (fun t => Real.sin ((r : ℝ) * t)) =
      ∑ j ∈ range m,
        (1 - ((2 * j + 1 : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ)) * Real.sin (((2 * j + 1 : ℕ) : ℝ) * θ) *
          (4 * ∫ t in a..b, Real.sin (((2 * j + 1 : ℕ) : ℝ) * t)) := by
    refine Finset.sum_bij (fun r _ => r / 2) ?_ ?_ ?_ ?_
    · intro r hr
      have h1 := Finset.mem_Ico.mp (Finset.mem_filter.mp hr).1
      exact Finset.mem_range.mpr (by omega)
    · intro r₁ h1 r₂ h2 hEq
      have ho1 := (Finset.mem_filter.mp h1).2
      have ho2 := (Finset.mem_filter.mp h2).2
      omega
    · intro j hj
      have hjlt := Finset.mem_range.mp hj
      refine ⟨2 * j + 1, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩, by omega⟩
    · intro r hr
      have ho := (Finset.mem_filter.mp hr).2
      have hreq : r = 2 * (r / 2) + 1 := by omega
      conv_lhs => rw [hreq]
      rw [quadInt_sin_odd]
  rw [hbij, ← mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [hpi_ne]

/-! ### Section 3: Sum of integrals over pairwise-disjoint subintervals of `[L, R]` -/

/-- If a finite family of non-degenerate intervals `[a_i, b_i] ⊆ [L, R]` (`a_i < b_i`) has
pairwise disjoint interiors (`b_i ≤ a_j ∨ b_j ≤ a_i`), then the sum of integrals of any
nonnegative continuous function over them is at most the integral over `[L, R]`. -/
lemma sum_disjoint_interval_integrals_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (L R : ℝ) (hLR : L ≤ R) (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_nn : ∀ t, 0 ≤ f t)
    (hsub : ∀ i ∈ s, L ≤ a i ∧ a i < b i ∧ b i ≤ R)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → b i ≤ a j ∨ b j ≤ a i) :
    ∑ i ∈ s, ∫ t in (a i)..(b i), f t ≤ ∫ t in L..R, f t := by
  classical
  induction s using Finset.strongInduction generalizing L with
  | H s ih =>
    by_cases hne : s.Nonempty
    · obtain ⟨i₀, hi₀, hmin⟩ := s.exists_min_image a hne
      have hi₀_sub := hsub i₀ hi₀
      rw [← Finset.add_sum_erase _ _ hi₀]
      have hrest_sub : ∀ j ∈ s.erase i₀, b i₀ ≤ a j ∧ a j < b j ∧ b j ≤ R := by
        intro j hj
        have hjs : j ∈ s := Finset.mem_of_mem_erase hj
        have hjne : j ≠ i₀ := (Finset.mem_erase.mp hj).1
        have hjsub := hsub j hjs
        have hminj : a i₀ ≤ a j := hmin j hjs
        have hbi_le : b i₀ ≤ a j := by
          rcases hdisj i₀ hi₀ j hjs hjne.symm with h | h
          · exact h
          · linarith [hjsub.2.1]
        exact ⟨hbi_le, hjsub.2.1, hjsub.2.2⟩
      have hrest_disj : ∀ i ∈ s.erase i₀, ∀ j ∈ s.erase i₀, i ≠ j → b i ≤ a j ∨ b j ≤ a i :=
        fun i hi j hj hne => hdisj i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj) hne
      have hih := ih (s.erase i₀) (Finset.erase_ssubset hi₀) (b i₀) hi₀_sub.2.2 hrest_sub hrest_disj
      have hhead : 0 ≤ ∫ t in L..(a i₀), f t :=
        intervalIntegral.integral_nonneg hi₀_sub.1 (fun t _ => hf_nn t)
      have hadj1 : (∫ t in L..(a i₀), f t) + (∫ t in (a i₀)..(b i₀), f t) = ∫ t in L..(b i₀), f t :=
        intervalIntegral.integral_add_adjacent_intervals
          (hf_cont.intervalIntegrable (μ := MeasureTheory.volume) L (a i₀))
          (hf_cont.intervalIntegrable (μ := MeasureTheory.volume) (a i₀) (b i₀))
      have hadj2 : (∫ t in L..(b i₀), f t) + (∫ t in (b i₀)..R, f t) = ∫ t in L..R, f t :=
        intervalIntegral.integral_add_adjacent_intervals
          (hf_cont.intervalIntegrable (μ := MeasureTheory.volume) L (b i₀))
          (hf_cont.intervalIntegrable (μ := MeasureTheory.volume) (b i₀) R)
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
      exact intervalIntegral.integral_nonneg hLR (fun t _ => hf_nn t)

/-- Bound a sum of signed four-quadrant integrals of a nonnegative continuous `F` on `[-π, π]`
around a target point `θ₀` covered by `[θ₀ - δ, θ₀ + δ] ⊆ [a i₀, b i₀] ⊂ (0, π/2)`. -/
lemma abs_sum_quadInt_ge {N : ℕ} (a b : Fin N → ℝ) (α : Fin N → ℝ)
    (hα : ∀ i, α i = -1 ∨ α i = 1)
    (hab : ∀ i, 0 < a i ∧ a i < b i ∧ b i < Real.pi / 2)
    (hsep : ∀ i j : Fin N, i ≠ j → b i < a j ∨ b j < a i)
    (F : ℝ → ℝ) (hF_cont : Continuous F) (hF_nn : ∀ t, 0 ≤ F t)
    (i₀ : Fin N) {θ₀ δ : ℝ} (hδ : 0 < δ)
    (hcov_lo : a i₀ ≤ θ₀ - δ) (hcov_hi : θ₀ + δ ≤ b i₀) :
    (∫ t in (-Real.pi)..Real.pi, F t) -
      2 * ((∫ t in (-Real.pi)..(θ₀ - δ), F t) + (∫ t in (θ₀ + δ)..Real.pi, F t))
      ≤ |∑ i : Fin N, α i * quadInt (a i) (b i) F| := by
  have hθ_lo : 0 < θ₀ - δ := lt_of_lt_of_le (hab i₀).1 hcov_lo
  have hθ_hi : θ₀ + δ < Real.pi / 2 := lt_of_le_of_lt hcov_hi (hab i₀).2.2
  -- Split `∫_{-π}^π F = ∫_{-π}^{θ₀-δ} F + ∫_{θ₀-δ}^{θ₀+δ} F + ∫_{θ₀+δ}^π F`.
  have hfull : ∫ t in (-Real.pi)..Real.pi, F t =
      (∫ t in (-Real.pi)..(θ₀ - δ), F t) + (∫ t in (θ₀ - δ)..(θ₀ + δ), F t) +
      (∫ t in (θ₀ + δ)..Real.pi, F t) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume) (f := F) (a := -Real.pi) (b := θ₀ - δ) (c := θ₀ + δ)
      (hF_cont.intervalIntegrable _ _) (hF_cont.intervalIntegrable _ _)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume) (f := F) (a := -Real.pi) (b := θ₀ + δ) (c := Real.pi)
      (hF_cont.intervalIntegrable _ _) (hF_cont.intervalIntegrable _ _)
    linarith
  -- Split `∫_{a i₀}^{b i₀} F` into `[a i₀, θ₀ - δ]`, `[θ₀ - δ, θ₀ + δ]`, `[θ₀ + δ, b i₀]`.
  have hi₀_split : ∫ t in (a i₀)..(b i₀), F t =
      (∫ t in (a i₀)..(θ₀ - δ), F t) + (∫ t in (θ₀ - δ)..(θ₀ + δ), F t) +
      (∫ t in (θ₀ + δ)..(b i₀), F t) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume) (f := F) (a := a i₀) (b := θ₀ - δ) (c := θ₀ + δ)
      (hF_cont.intervalIntegrable _ _) (hF_cont.intervalIntegrable _ _)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume) (f := F) (a := a i₀) (b := θ₀ + δ) (c := b i₀)
      (hF_cont.intervalIntegrable _ _) (hF_cont.intervalIntegrable _ _)
    linarith
  -- Helper: bound all 4 quadrants of all `i` (minus `[θ₀ - δ, θ₀ + δ]`) by the tail integral.
  -- Quadrant 1 (`(0, π/2)`): split `Fin N` into left of `i₀`, `i₀` itself, right of `i₀`.
  let Q1L := (Finset.univ : Finset (Fin N)).filter (fun i => b i < a i₀)
  let Q1R := (Finset.univ : Finset (Fin N)).filter (fun i => b i₀ < a i)
  have hQ1_part : (Finset.univ : Finset (Fin N)).erase i₀ = Q1L ∪ Q1R := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Q1L, Q1R,
      Finset.mem_filter, true_and]
    constructor
    · intro hne; exact hsep i i₀ hne
    · rintro (h | h) <;> (intro heq; subst heq; linarith [(hab i).2.1])
  have hQ1_disj : Disjoint Q1L Q1R := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    have h1' := (Finset.mem_filter.mp h1).2
    have h2' := (Finset.mem_filter.mp h2).2
    linarith [(hab i).2.1, (hab i₀).2.1]
  have hQ1L_le : ∑ i ∈ Q1L, ∫ t in (a i)..(b i), F t ≤ ∫ t in (0 : ℝ)..(a i₀), F t := by
    apply sum_disjoint_interval_integrals_le Q1L a b 0 (a i₀) (hab i₀).1.le F hF_cont hF_nn
    · intro i hi; exact ⟨(hab i).1.le, (hab i).2.1, (Finset.mem_filter.mp hi).2.le⟩
    · intro i _ j _ hne; rcases hsep i j hne with h | h <;> [left; right] <;> exact h.le
  have hQ1R_le : ∑ i ∈ Q1R, ∫ t in (a i)..(b i), F t ≤ ∫ t in (b i₀)..(Real.pi / 2), F t := by
    apply sum_disjoint_interval_integrals_le Q1R a b (b i₀) (Real.pi / 2) (hab i₀).2.2.le F hF_cont hF_nn
    · intro i hi; exact ⟨(Finset.mem_filter.mp hi).2.le, (hab i).2.1, (hab i).2.2.le⟩
    · intro i _ j _ hne; rcases hsep i j hne with h | h <;> [left; right] <;> exact h.le
  -- Quadrant 2 (`(π/2, π)`): `∑ ∫_{π - b i}^{π - a i} ≤ ∫_{π/2}^π F`.
  have hQ2_le : ∑ i : Fin N, ∫ t in (Real.pi - b i)..(Real.pi - a i), F t ≤
      ∫ t in (Real.pi / 2)..Real.pi, F t := by
    apply sum_disjoint_interval_integrals_le Finset.univ (fun i => Real.pi - b i) (fun i => Real.pi - a i)
      (Real.pi / 2) Real.pi (by linarith [Real.pi_pos]) F hF_cont hF_nn
    · intro i _; exact ⟨by linarith [(hab i).2.2], by linarith [(hab i).2.1], by linarith [(hab i).1]⟩
    · intro i _ j _ hne; rcases hsep i j hne with h | h <;> [right; left] <;> linarith
  -- Quadrant 3 (`(-π/2, 0)`): `∑ ∫_{-b i}^{-a i} ≤ ∫_{-π/2}^0 F`.
  have hQ3_le : ∑ i : Fin N, ∫ t in (-b i)..(-a i), F t ≤ ∫ t in (-(Real.pi / 2))..(0 : ℝ), F t := by
    apply sum_disjoint_interval_integrals_le Finset.univ (fun i => -b i) (fun i => -a i)
      (-(Real.pi / 2)) 0 (by linarith [Real.pi_pos]) F hF_cont hF_nn
    · intro i _; exact ⟨by linarith [(hab i).2.2], by linarith [(hab i).2.1], by linarith [(hab i).1]⟩
    · intro i _ j _ hne; rcases hsep i j hne with h | h <;> [right; left] <;> linarith
  -- Quadrant 4 (`(-π, -π/2)`): `∑ ∫_{a i - π}^{b i - π} ≤ ∫_{-π}^{-π/2} F`.
  have hQ4_le : ∑ i : Fin N, ∫ t in (a i - Real.pi)..(b i - Real.pi), F t ≤
      ∫ t in (-Real.pi)..(-(Real.pi / 2)), F t := by
    apply sum_disjoint_interval_integrals_le Finset.univ (fun i => a i - Real.pi) (fun i => b i - Real.pi)
      (-Real.pi) (-(Real.pi / 2)) (by linarith [Real.pi_pos]) F hF_cont hF_nn
    · intro i _; exact ⟨by linarith [(hab i).1], by linarith [(hab i).2.1], by linarith [(hab i).2.2]⟩
    · intro i _ j _ hne; rcases hsep i j hne with h | h <;> [left; right] <;> linarith
  -- Sum of all non-core pieces bounded by `∫_{-π}^{θ₀-δ} F + ∫_{θ₀+δ}^π F`.
  have hleft_stitch : (∫ t in (-Real.pi)..(-(Real.pi / 2)), F t) +
      (∫ t in (-(Real.pi / 2))..(0 : ℝ), F t) + (∫ t in (0 : ℝ)..(a i₀), F t) +
      (∫ t in (a i₀)..(θ₀ - δ), F t) = ∫ t in (-Real.pi)..(θ₀ - δ), F t := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume) (f := F)
      (a := -Real.pi) (b := -(Real.pi / 2)) (c := 0)
      (hF_cont.intervalIntegrable _ _) (hF_cont.intervalIntegrable _ _)
    have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume) (f := F)
      (a := -Real.pi) (b := 0) (c := a i₀)
      (hF_cont.intervalIntegrable _ _) (hF_cont.intervalIntegrable _ _)
    have h3 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume) (f := F)
      (a := -Real.pi) (b := a i₀) (c := θ₀ - δ)
      (hF_cont.intervalIntegrable _ _) (hF_cont.intervalIntegrable _ _)
    linarith
  have hright_stitch : (∫ t in (θ₀ + δ)..(b i₀), F t) +
      (∫ t in (b i₀)..(Real.pi / 2), F t) + (∫ t in (Real.pi / 2)..Real.pi, F t) =
      ∫ t in (θ₀ + δ)..Real.pi, F t := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume) (f := F)
      (a := θ₀ + δ) (b := b i₀) (c := Real.pi / 2)
      (hF_cont.intervalIntegrable _ _) (hF_cont.intervalIntegrable _ _)
    have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume) (f := F)
      (a := θ₀ + δ) (b := Real.pi / 2) (c := Real.pi)
      (hF_cont.intervalIntegrable _ _) (hF_cont.intervalIntegrable _ _)
    linarith
  -- Isolate `α i₀ * ∫_{θ₀-δ}^{θ₀+δ} F` from `∑ i, α i * quadInt (a i) (b i) F`.
  set core := ∫ t in (θ₀ - δ)..(θ₀ + δ), F t
  set rem := (∑ i : Fin N, α i * quadInt (a i) (b i) F) - α i₀ * core
  have hrem_abs : |rem| ≤ (∫ t in (-Real.pi)..(θ₀ - δ), F t) + (∫ t in (θ₀ + δ)..Real.pi, F t) := by
    -- Express `rem` as signed sum of all non-core integrals, each `≥ 0` and with `|α i| = 1`.
    have hα_abs : ∀ i, |α i| = 1 := fun i => by rcases hα i with h | h <;> rw [h] <;> norm_num
    have hnn_int : ∀ u v, u ≤ v → 0 ≤ ∫ t in u..v, F t :=
      fun u v huv => intervalIntegral.integral_nonneg huv (fun t _ => hF_nn t)
    have hquad_split : ∀ i : Fin N,
        |α i * quadInt (a i) (b i) F| ≤
          (∫ t in (a i)..(b i), F t) + (∫ t in (Real.pi - b i)..(Real.pi - a i), F t) +
          (∫ t in (-b i)..(-a i), F t) + (∫ t in (a i - Real.pi)..(b i - Real.pi), F t) := by
      intro i
      rw [abs_mul, hα_abs i, one_mul]
      unfold quadInt
      have h1 := hnn_int (a i) (b i) (hab i).2.1.le
      have h2 := hnn_int (Real.pi - b i) (Real.pi - a i) (by linarith [(hab i).2.1])
      have h3 := hnn_int (-b i) (-a i) (by linarith [(hab i).2.1])
      have h4 := hnn_int (a i - Real.pi) (b i - Real.pi) (by linarith [(hab i).2.1])
      rw [abs_le]; constructor <;> linarith
    have hi₀_rem : |α i₀ * quadInt (a i₀) (b i₀) F - α i₀ * core| ≤
        (∫ t in (a i₀)..(θ₀ - δ), F t) + (∫ t in (θ₀ + δ)..(b i₀), F t) +
        (∫ t in (Real.pi - b i₀)..(Real.pi - a i₀), F t) +
        (∫ t in (-b i₀)..(-a i₀), F t) + (∫ t in (a i₀ - Real.pi)..(b i₀ - Real.pi), F t) := by
      rw [← mul_sub, abs_mul, hα_abs i₀, one_mul]
      unfold quadInt
      rw [hi₀_split]
      have h1 := hnn_int (a i₀) (θ₀ - δ) hcov_lo
      have h2 := hnn_int (θ₀ + δ) (b i₀) hcov_hi
      have h3 := hnn_int (Real.pi - b i₀) (Real.pi - a i₀) (by linarith [(hab i₀).2.1])
      have h4 := hnn_int (-b i₀) (-a i₀) (by linarith [(hab i₀).2.1])
      have h5 := hnn_int (a i₀ - Real.pi) (b i₀ - Real.pi) (by linarith [(hab i₀).2.1])
      rw [abs_le]; constructor <;> linarith
    have hrem_eq : rem = (α i₀ * quadInt (a i₀) (b i₀) F - α i₀ * core) +
        ∑ i ∈ Finset.univ.erase i₀, α i * quadInt (a i) (b i) F := by
      dsimp only [rem]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      ring
    rw [hrem_eq]
    have hsum_er : |∑ i ∈ Finset.univ.erase i₀, α i * quadInt (a i) (b i) F| ≤
        (∑ i ∈ Finset.univ.erase i₀, ∫ t in (a i)..(b i), F t) +
        (∑ i ∈ Finset.univ.erase i₀, ∫ t in (Real.pi - b i)..(Real.pi - a i), F t) +
        (∑ i ∈ Finset.univ.erase i₀, ∫ t in (-b i)..(-a i), F t) +
        (∑ i ∈ Finset.univ.erase i₀, ∫ t in (a i - Real.pi)..(b i - Real.pi), F t) := by
      calc |∑ i ∈ Finset.univ.erase i₀, α i * quadInt (a i) (b i) F|
          ≤ ∑ i ∈ Finset.univ.erase i₀, |α i * quadInt (a i) (b i) F| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.univ.erase i₀,
              ((∫ t in (a i)..(b i), F t) + (∫ t in (Real.pi - b i)..(Real.pi - a i), F t) +
               (∫ t in (-b i)..(-a i), F t) + (∫ t in (a i - Real.pi)..(b i - Real.pi), F t)) :=
            Finset.sum_le_sum fun i _ => hquad_split i
        _ = _ := by simp only [Finset.sum_add_distrib]
    have hQ1_er : ∑ i ∈ Finset.univ.erase i₀, ∫ t in (a i)..(b i), F t ≤
        (∫ t in (0 : ℝ)..(a i₀), F t) + (∫ t in (b i₀)..(Real.pi / 2), F t) := by
      rw [hQ1_part, Finset.sum_union hQ1_disj]
      linarith [hQ1L_le, hQ1R_le]
    have hQ2_add := Finset.add_sum_erase Finset.univ (fun i => ∫ t in (Real.pi - b i)..(Real.pi - a i), F t)
      (Finset.mem_univ i₀)
    have hQ3_add := Finset.add_sum_erase Finset.univ (fun i => ∫ t in (-b i)..(-a i), F t)
      (Finset.mem_univ i₀)
    have hQ4_add := Finset.add_sum_erase Finset.univ (fun i => ∫ t in (a i - Real.pi)..(b i - Real.pi), F t)
      (Finset.mem_univ i₀)
    have htri := abs_add_le (α i₀ * quadInt (a i₀) (b i₀) F - α i₀ * core)
      (∑ i ∈ Finset.univ.erase i₀, α i * quadInt (a i) (b i) F)
    linarith
  have hcore_nn : 0 ≤ core := intervalIntegral.integral_nonneg (by linarith) (fun t _ => hF_nn t)
  have hα0_abs : |α i₀ * core| = core := by
    rw [abs_mul, abs_of_nonneg hcore_nn]
    rcases hα i₀ with h | h <;> rw [h] <;> norm_num
  have hrev_tri : core - |rem| ≤ |∑ i : Fin N, α i * quadInt (a i) (b i) F| := by
    have h := abs_sub_abs_le_abs_sub (α i₀ * core) (-rem)
    have heq : α i₀ * core - -rem = ∑ i : Fin N, α i * quadInt (a i) (b i) F := by
      dsimp only [rem]; ring
    rw [heq, abs_neg, hα0_abs] at h
    linarith
  linarith

/-! ### Section 4: Odd sine polynomial theorem from bad runs and discrepancy coloring -/

/-- Symmetry-folding of an angle `θ ∈ [0, 2π)` into `[0, π/2]`. -/
noncomputable def foldAngle (θ : ℝ) : ℝ :=
  if θ ≤ Real.pi / 2 then θ
  else if θ ≤ Real.pi then Real.pi - θ
  else if θ ≤ 3 * Real.pi / 2 then θ - Real.pi
  else 2 * Real.pi - θ

lemma foldAngle_mem (θ : ℝ) (h0 : 0 ≤ θ) (h2pi : θ ≤ 2 * Real.pi) :
    foldAngle θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
  unfold foldAngle
  split_ifs <;> constructor <;> linarith

lemma abs_oddSin_foldAngle (m : ℕ) (c : Fin m → ℝ) (θ : ℝ) :
    |∑ j : Fin m, c j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * foldAngle θ)| =
    |∑ j : Fin m, c j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θ)| := by
  by_cases h1 : θ ≤ Real.pi / 2
  · have hf : foldAngle θ = θ := by simp only [foldAngle, h1, ↓reduceIte]
    rw [hf]
  · by_cases h2 : θ ≤ Real.pi
    · have hf : foldAngle θ = Real.pi - θ := by simp only [foldAngle, h1, h2, ↓reduceIte]
      rw [hf]
      have hsum : ∑ j : Fin m, c j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * (Real.pi - θ)) =
          ∑ j : Fin m, c j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have harg : ((2 * j.val + 1 : ℕ) : ℝ) * (Real.pi - θ) =
            (Real.pi - ((2 * j.val + 1 : ℕ) : ℝ) * θ) + (j.val : ℤ) * (2 * Real.pi) := by
          push_cast; ring
        rw [harg, Real.sin_add_int_mul_two_pi, Real.sin_pi_sub]
      rw [hsum]
    · by_cases h3 : θ ≤ 3 * Real.pi / 2
      · have hf : foldAngle θ = θ - Real.pi := by simp only [foldAngle, h1, h2, h3, ↓reduceIte]
        rw [hf, ← abs_neg, ← Finset.sum_neg_distrib]
        have hsum : ∑ j : Fin m, -(c j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * (θ - Real.pi))) =
            ∑ j : Fin m, c j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have harg : ((2 * j.val + 1 : ℕ) : ℝ) * (θ - Real.pi) =
              (((2 * j.val + 1 : ℕ) : ℝ) * θ - Real.pi) + (((-(j.val : ℤ) : ℤ) : ℝ)) * (2 * Real.pi) := by
            push_cast; ring
          rw [harg, Real.sin_add_int_mul_two_pi, Real.sin_sub_pi]; ring
        rw [hsum]
      · have hf : foldAngle θ = 2 * Real.pi - θ := by simp only [foldAngle, h1, h2, h3, ↓reduceIte]
        rw [hf, ← abs_neg, ← Finset.sum_neg_distrib]
        have hsum : ∑ j : Fin m, -(c j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * (2 * Real.pi - θ))) =
            ∑ j : Fin m, c j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have harg : ((2 * j.val + 1 : ℕ) : ℝ) * (2 * Real.pi - θ) =
              -(((2 * j.val + 1 : ℕ) : ℝ) * θ) + ((2 * j.val + 1 : ℕ) : ℤ) * (2 * Real.pi) := by
            push_cast; ring
          rw [harg, Real.sin_add_int_mul_two_pi, Real.sin_neg]; ring
        rw [hsum]

/-- Main odd-sine construction theorem: given a well-separated collection of bad runs in `[0, π/2]`
with `runs.card ≤ m / 2^131`, and a finite list of evaluation angles `θs : Fin E → ℝ` (`E ≤ 7*m`),
there exists `ε : Fin m → ℝ` in `{-1, 1}` such that the odd sine polynomial
`s_o(θ) = ∑_{j < m} ε_j sin ((2j+1) θ)` has `|s_o(θs ξ)| ≥ 200 √m` whenever `foldAngle (θs ξ)`
falls inside any bad run. -/
theorem fejer_odd_sine_exists
    (hColor : ∀ (n m : ℕ) (v : Fin m → Fin n → ℝ) (x₀ : Fin n → ℝ),
      (∀ i, |x₀ i| ≤ 1) →
      ∀ (c : Fin m → ℝ), (∀ j, 100 ≤ c j) →
      (∑ j : Fin m, Real.exp (-(c j ^ 2 / 10000)) ≤ (n : ℝ) / 280) →
      ∀ (B : Fin m → ℝ), (∀ j i, |v j i| ≤ B j) →
      ∃ x : Fin n → ℝ,
        (∀ i, x i = -1 ∨ x i = 1) ∧
        ∀ j : Fin m, |∑ i : Fin n, (x i - x₀ i) * v j i| ≤ (c j + 200) * Real.sqrt n * B j)
    (m : ℕ) (hm32 : 32 ∣ m) (hm_big : 16 ^ 33 ≤ m)
    (runs : Finset (ℕ × ℕ))
    (hruns_in : ∀ ab ∈ runs, 1 ≤ ab.1 ∧ ab.1 < ab.2 ∧ ab.2 ≤ m / 32 - 1 ∧ ab.2 - ab.1 ≤ 6)
    (hruns_sep : ∀ ab₁ ∈ runs, ∀ ab₂ ∈ runs, ab₁ ≠ ab₂ → ab₁.2 + 1 ≤ ab₂.1 ∨ ab₂.2 + 1 ≤ ab₁.1)
    (hruns_card : runs.card * (8 * 16 ^ 32) ≤ m)
    (E : ℕ) (hE : E ≤ 7 * m) (θs : Fin E → ℝ) :
    let step : ℝ := 16 * Real.pi / (m : ℝ)
    ∃ ε : Fin m → ℝ, (∀ j, ε j = -1 ∨ ε j = 1) ∧
      ∀ ξ : Fin E,
        (∃ ab ∈ runs, foldAngle (θs ξ) ∈ Set.Icc ((ab.1 : ℝ) * step) ((ab.2 : ℝ) * step)) →
        200 * Real.sqrt m ≤ |∑ j : Fin m, ε j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θs ξ)| := by
  classical
  intro step
  set M := m / 32
  have hm_eq : m = 32 * M := by obtain ⟨q, hq⟩ := hm32; simp [M, hq]
  have hm_pos : 0 < m := by omega
  have hmr_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have hstep_pos : 0 < step := by dsimp [step]; positivity
  have hM_step : (M : ℝ) * step = Real.pi / 2 := by
    dsimp only [step]
    have hm_cast : (m : ℝ) = 32 * (M : ℝ) := by exact_mod_cast hm_eq
    have hM_ne : (M : ℝ) ≠ 0 := by
      have : 0 < M := by omega
      exact_mod_cast this.ne'
    rw [hm_cast]; field_simp [hM_ne]; ring
  set δ : ℝ := 4 * Real.pi / (m : ℝ)
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  have hstep_eq : step = 4 * δ := by dsimp [step, δ]; ring
  by_cases hN0 : runs.card = 0
  · refine ⟨fun _ => 1, fun _ => Or.inr rfl, ?_⟩
    intro ξ ⟨ab, hab, _⟩
    have := Finset.card_pos.mpr ⟨ab, hab⟩
    omega
  · set N := runs.card
    have hN_pos : 0 < N := Nat.pos_of_ne_zero hN0
    have hNr_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
    let e : Fin N ≃ runs := (Fintype.equivFinOfCardEq (by simp [N])).symm
    let aI (i : Fin N) : ℝ := ((e i).1.1 : ℝ) * step - δ
    let bI (i : Fin N) : ℝ := ((e i).1.2 : ℝ) * step + δ
    have hab : ∀ i : Fin N, 0 < aI i ∧ aI i < bI i ∧ bI i < Real.pi / 2 := by
      intro i
      obtain ⟨h1, h2, h3, _⟩ := hruns_in (e i).1 (e i).2
      have h1r : (1 : ℝ) ≤ ((e i).1.1 : ℝ) := by exact_mod_cast h1
      have h2r : ((e i).1.1 : ℝ) < ((e i).1.2 : ℝ) := by exact_mod_cast h2
      have h3r : ((e i).1.2 : ℝ) + 1 ≤ (M : ℝ) := by
        have : (e i).1.2 + 1 ≤ M := by omega
        exact_mod_cast this
      dsimp only [aI, bI]
      refine ⟨by nlinarith [hstep_eq], by nlinarith [hstep_eq], ?_⟩
      nlinarith [hstep_eq, hM_step]
    have hsep : ∀ i j : Fin N, i ≠ j → bI i < aI j ∨ bI j < aI i := by
      intro i j hne
      have hne' : (e i).1 ≠ (e j).1 := fun h => hne (e.injective (Subtype.ext h))
      rcases hruns_sep (e i).1 (e i).2 (e j).1 (e j).2 hne' with h | h
      · left
        have hr : ((e i).1.2 : ℝ) + 1 ≤ ((e j).1.1 : ℝ) := by exact_mod_cast h
        dsimp only [aI, bI]; nlinarith [hstep_eq]
      · right
        have hr : ((e j).1.2 : ℝ) + 1 ≤ ((e i).1.1 : ℝ) := by exact_mod_cast h
        dsimp only [aI, bI]; nlinarith [hstep_eq]
    have hlen_le : ∀ i : Fin N, bI i - aI i ≤ 104 * Real.pi / (m : ℝ) := by
      intro i
      obtain ⟨_, h2, _, h6⟩ := hruns_in (e i).1 (e i).2
      have h6r : ((e i).1.2 : ℝ) - ((e i).1.1 : ℝ) ≤ 6 := by
        have : (e i).1.2 ≤ (e i).1.1 + 6 := by omega
        have : ((e i).1.2 : ℝ) ≤ ((e i).1.1 : ℝ) + 6 := by exact_mod_cast this
        linarith
      dsimp only [aI, bI, step, δ]
      have hmul : (((e i).1.2 : ℝ) - ((e i).1.1 : ℝ)) * (16 * Real.pi / (m : ℝ)) ≤
          6 * (16 * Real.pi / (m : ℝ)) :=
        mul_le_mul_of_nonneg_right h6r (by positivity)
      have heq : ((e i).1.2 : ℝ) * (16 * Real.pi / (m : ℝ)) + 4 * Real.pi / (m : ℝ) -
          (((e i).1.1 : ℝ) * (16 * Real.pi / (m : ℝ)) - 4 * Real.pi / (m : ℝ)) =
          (((e i).1.2 : ℝ) - ((e i).1.1 : ℝ)) * (16 * Real.pi / (m : ℝ)) + 8 * Real.pi / (m : ℝ) := by ring
      have h104 : 6 * (16 * Real.pi / (m : ℝ)) + 8 * Real.pi / (m : ℝ) = 104 * Real.pi / (m : ℝ) := by ring
      rw [heq]
      linarith only [hmul, h104]
    -- Step 1: Choose `α : Fin N → ℝ` in `{-1, 1}` so all Fejér-smoothed coefficients `ε̃_j ∈ [-1, 1]`.
    set K : ℝ := 2000
    let v1 : Fin m → Fin N → ℝ := fun j i =>
      K * Real.sqrt m * (1 - ((2 * j.val + 1 : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ)) *
        (4 / Real.pi * ∫ t in (aI i)..(bI i), Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * t))
    have hv1_bound : ∀ j i, |v1 j i| ≤ (2 : ℝ) ^ 20 / Real.sqrt m := by
      intro j i
      dsimp only [v1]
      have hwt_nn : 0 ≤ 1 - ((2 * j.val + 1 : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ) := by
        have hlt : 2 * j.val + 1 ≤ 2 * m := by omega
        have hcast : ((2 * j.val + 1 : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast hlt
        rw [sub_nonneg, div_le_one (by positivity)]; exact hcast
      have hwt_le : 1 - ((2 * j.val + 1 : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ) ≤ 1 := by
        have : 0 ≤ ((2 * j.val + 1 : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ) := by positivity
        linarith
      have hint_abs : |∫ t in (aI i)..(bI i), Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * t)| ≤ bI i - aI i := by
        have h1 := intervalIntegral.abs_integral_le_integral_abs (μ := MeasureTheory.volume) (hab i).2.1.le
          (f := fun t => Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * t))
        have h2 : ∫ t in (aI i)..(bI i), |Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * t)| ≤
            ∫ _t in (aI i)..(bI i), (1 : ℝ) := by
          apply intervalIntegral.integral_mono_on (hab i).2.1.le
            ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).abs.intervalIntegrable _ _)
            intervalIntegrable_const
          intro t _; exact Real.abs_sin_le_one _
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h2
        exact h1.trans h2
      have hsqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmr_pos
      have hsqrt_sq : Real.sqrt m * Real.sqrt m = (m : ℝ) := Real.mul_self_sqrt hmr_pos.le
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ K),
        abs_of_nonneg (Real.sqrt_nonneg m),
        abs_of_nonneg hwt_nn, abs_of_nonneg (by positivity : 0 ≤ 4 / Real.pi)]
      calc K * Real.sqrt m * (1 - ((2 * j.val + 1 : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ)) *
            (4 / Real.pi * |∫ t in (aI i)..(bI i), Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * t)|)
          ≤ K * Real.sqrt m * 1 * (4 / Real.pi * (104 * Real.pi / (m : ℝ))) := by
            have h3 : 4 / Real.pi * |∫ t in (aI i)..(bI i), Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * t)| ≤
                4 / Real.pi * (104 * Real.pi / (m : ℝ)) :=
              mul_le_mul_of_nonneg_left (hint_abs.trans (hlen_le i)) (by positivity)
            have h4 : K * Real.sqrt m * (1 - ((2 * j.val + 1 : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ)) ≤
                K * Real.sqrt m * 1 :=
              mul_le_mul_of_nonneg_left hwt_le (by positivity)
            exact mul_le_mul h4 h3 (by positivity) (by positivity)
        _ = 832000 / Real.sqrt m := by
            have h1 : K * Real.sqrt m * 1 * (4 / Real.pi * (104 * Real.pi / (m : ℝ))) =
                832000 * (Real.sqrt m / (m : ℝ)) := by
              dsimp only [K]; field_simp [Real.pi_pos.ne', hmr_pos.ne']; ring
            have h2 : Real.sqrt m / (m : ℝ) = 1 / Real.sqrt m := by
              rw [div_eq_div_iff hmr_pos.ne' hsqrt_pos.ne', one_mul, hsqrt_sq]
            rw [h1, h2]; ring
        _ ≤ (2 : ℝ) ^ 20 / Real.sqrt m := by
            apply div_le_div_of_nonneg_right (by norm_num) hsqrt_pos.le
    -- Apply `hColor` with `c1 = 100 * √(log (280 * m / N))`.
    have hratio_ge : 8 * (16 : ℝ) ^ 32 ≤ (m : ℝ) / (N : ℝ) := by
      rw [le_div_iff₀ hNr_pos]
      have : (N : ℝ) * (8 * (16 : ℝ) ^ 32) ≤ (m : ℝ) := by exact_mod_cast hruns_card
      linarith only [this]
    have hlog_ge1 : 1 ≤ Real.log (280 * (m : ℝ) / (N : ℝ)) := by
      have h1 : Real.exp 1 ≤ 280 * (m : ℝ) / (N : ℝ) := by
        have he : Real.exp 1 ≤ 4 := by
          have hhalf : (1 : ℝ) / 2 ≤ Real.exp (-(1 : ℝ) / 2) := by
            have := Real.add_one_le_exp (-(1 : ℝ) / 2); linarith
          have hpos : Real.exp ((1 : ℝ) / 2) ≤ 2 := by
            have hmul : Real.exp ((1 : ℝ) / 2) * Real.exp (-(1 : ℝ) / 2) = 1 := by
              rw [← Real.exp_add]; norm_num
            nlinarith [Real.exp_pos ((1 : ℝ) / 2)]
          have hsq : Real.exp 1 = Real.exp ((1 : ℝ) / 2) * Real.exp ((1 : ℝ) / 2) := by
            rw [← Real.exp_add]; norm_num
          nlinarith [Real.exp_pos ((1 : ℝ) / 2)]
        have h2 : (4 : ℝ) ≤ 280 * ((m : ℝ) / (N : ℝ)) := by
          have h131 : (1 : ℝ) ≤ 8 * (16 : ℝ) ^ 32 := by
            have h16 : (1 : ℝ) ≤ (16 : ℝ) ^ 32 := one_le_pow₀ (by norm_num)
            linarith only [h16]
          have hge1 : (1 : ℝ) ≤ (m : ℝ) / (N : ℝ) := h131.trans hratio_ge
          linarith only [hge1]
        have hrw : 280 * (m : ℝ) / (N : ℝ) = 280 * ((m : ℝ) / (N : ℝ)) := by ring
        linarith only [he, h2, hrw]
      have hlog := Real.log_le_log (Real.exp_pos 1) h1
      rwa [Real.log_exp] at hlog
    let c1 : Fin m → ℝ := fun _ => 100 * Real.sqrt (Real.log (280 * (m : ℝ) / (N : ℝ)))
    have hc1_ge : ∀ j, 100 ≤ c1 j := fun j => by
      dsimp only [c1]
      have : 1 ≤ Real.sqrt (Real.log (280 * (m : ℝ) / (N : ℝ))) := by
        rw [Real.one_le_sqrt]; exact hlog_ge1
      linarith only [this]
    have hc1_budget : ∑ j : Fin m, Real.exp (-(c1 j ^ 2 / 10000)) ≤ (N : ℝ) / 280 := by
      have hterm : ∀ j : Fin m, Real.exp (-(c1 j ^ 2 / 10000)) = (N : ℝ) / (280 * (m : ℝ)) := by
        intro j
        dsimp only [c1]
        rw [mul_pow, Real.sq_sqrt (by linarith only [hlog_ge1])]
        have harg : -((100 ^ 2 * Real.log (280 * (m : ℝ) / (N : ℝ))) / 10000) =
            -Real.log (280 * (m : ℝ) / (N : ℝ)) := by ring
        have hpos_arg : 0 < 280 * (m : ℝ) / (N : ℝ) :=
          div_pos (mul_pos (by norm_num) hmr_pos) hNr_pos
        rw [harg, Real.exp_neg, Real.exp_log hpos_arg, inv_div]
      simp_rw [hterm]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have : (m : ℝ) * ((N : ℝ) / (280 * (m : ℝ))) = (N : ℝ) / 280 := by field_simp [hmr_pos.ne']
      linarith only [this]
    obtain ⟨α, hα_pm, hα_bound⟩ := hColor N m v1 (fun _ => 0) (fun _ => by norm_num)
      c1 hc1_ge hc1_budget (fun _ => (2 : ℝ) ^ 20 / Real.sqrt m) hv1_bound
    let epsTilde : Fin m → ℝ := fun j => ∑ i : Fin N, α i * v1 j i
    have hepsTilde_le : ∀ j : Fin m, |epsTilde j| ≤ 1 := by
      intro j
      have hb := hα_bound j
      simp only [sub_zero] at hb
      set u : ℝ := (N : ℝ) / (m : ℝ)
      have hu_pos : 0 < u := div_pos hNr_pos hmr_pos
      have h16pos : (0 : ℝ) < 16 := by norm_num
      have hu_le : u ≤ 1 / (8 * (16 : ℝ) ^ 32) := by
        dsimp only [u]; rw [div_le_iff₀ hmr_pos]
        have : (N : ℝ) * (8 * (16 : ℝ) ^ 32) ≤ (m : ℝ) := by exact_mod_cast hruns_card
        rw [one_div]; field_simp; linarith only [this]
      have hsqrt_u : Real.sqrt u ≤ 1 / (2 * (16 : ℝ) ^ 16) := by
        have hsq : u ≤ (1 / (2 * (16 : ℝ) ^ 16)) ^ 2 := by
          have hpow : (1 / (8 * (16 : ℝ) ^ 32) : ℝ) ≤ (1 / (2 * (16 : ℝ) ^ 16)) ^ 2 := by
            have heq : (2 * (16 : ℝ) ^ 16) ^ 2 = 4 * (16 : ℝ) ^ 32 := by
              rw [mul_pow, ← pow_mul]; norm_num
            rw [div_pow, one_pow, heq]
            apply one_div_le_one_div_of_le (mul_pos (by norm_num) (pow_pos h16pos 32))
            have hp := pow_pos h16pos 32
            linarith only [hp]
          exact hu_le.trans hpow
        calc Real.sqrt u ≤ Real.sqrt ((1 / (2 * (16 : ℝ) ^ 16)) ^ 2) := Real.sqrt_le_sqrt hsq
          _ = 1 / (2 * (16 : ℝ) ^ 16) :=
              Real.sqrt_sq (div_nonneg (by norm_num) (mul_nonneg (by norm_num) (pow_nonneg h16pos.le 16)))
      have h280u_pos : 0 < 280 / u := div_pos (by norm_num) hu_pos
      have hlog_sq : Real.log (280 / u) ≤ 2 * Real.sqrt (280 / u) := by
        have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr h280u_pos)
        have h2 : Real.log (280 / u) = 2 * Real.log (Real.sqrt (280 / u)) := by
          have hsq : Real.sqrt (280 / u) ^ 2 = 280 / u := Real.sq_sqrt h280u_pos.le
          conv_lhs => rw [← hsq, Real.log_pow]
          norm_num
        linarith only [h1, h2]
      have hprod_le : Real.sqrt u * Real.sqrt (Real.log (280 / u)) ≤ 1 / (4 * (16 : ℝ) ^ 7) := by
        rw [← Real.sqrt_mul hu_pos.le]
        have h1 : u * Real.log (280 / u) ≤ 2 * Real.sqrt (280 * u) := by
          have hmul := mul_le_mul_of_nonneg_left hlog_sq hu_pos.le
          have hrw : u * (2 * Real.sqrt (280 / u)) = 2 * Real.sqrt (280 * u) := by
            rw [Real.sqrt_div (by norm_num), Real.sqrt_mul (by norm_num)]
            have hne : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu_pos)
            have hmul2 : u * (Real.sqrt 280 / Real.sqrt u) = Real.sqrt 280 * Real.sqrt u := by
              rw [mul_div_assoc', div_eq_iff hne]
              calc u * Real.sqrt 280 = (Real.sqrt u * Real.sqrt u) * Real.sqrt 280 := by
                    rw [Real.mul_self_sqrt hu_pos.le]
                _ = Real.sqrt 280 * Real.sqrt u * Real.sqrt u := by ring
            linarith only [hmul2]
          linarith only [hmul, hrw]
        have h2 : 2 * Real.sqrt (280 * u) ≤ (1 / (4 * (16 : ℝ) ^ 7)) ^ 2 := by
          have h280 : 280 * u ≤ (1 / (2 * (16 : ℝ) ^ 15)) ^ 2 := by
            calc 280 * u ≤ 280 * (1 / (8 * (16 : ℝ) ^ 32)) :=
                  mul_le_mul_of_nonneg_left hu_le (by norm_num)
              _ ≤ (2 * (16 : ℝ) ^ 2) * (1 / (8 * (16 : ℝ) ^ 32)) :=
                  mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg (by norm_num) (mul_nonneg (by norm_num) (pow_nonneg h16pos.le 32)))
              _ = 1 / (4 * (16 : ℝ) ^ 30) := by
                  rw [show (32 : ℕ) = 2 + 30 by norm_num, pow_add]
                  have hne1 : (16 : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 h16pos.ne'
                  have hne2 : (16 : ℝ) ^ 30 ≠ 0 := pow_ne_zero 30 h16pos.ne'
                  field_simp [hne1, hne2]; ring
              _ = (1 / (2 * (16 : ℝ) ^ 15)) ^ 2 := by
                  rw [div_pow, one_pow, mul_pow, ← pow_mul]; norm_num
          have hsq2 : Real.sqrt (280 * u) ≤ 1 / (2 * (16 : ℝ) ^ 15) := by
            calc Real.sqrt (280 * u) ≤ Real.sqrt ((1 / (2 * (16 : ℝ) ^ 15)) ^ 2) := Real.sqrt_le_sqrt h280
              _ = 1 / (2 * (16 : ℝ) ^ 15) :=
                  Real.sqrt_sq (div_nonneg (by norm_num) (mul_nonneg (by norm_num) (pow_nonneg h16pos.le 15)))
          calc 2 * Real.sqrt (280 * u) ≤ 2 * (1 / (2 * (16 : ℝ) ^ 15)) :=
                mul_le_mul_of_nonneg_left hsq2 (by norm_num)
            _ = 1 / (16 : ℝ) ^ 15 := by
                have hne : (16 : ℝ) ^ 15 ≠ 0 := pow_ne_zero 15 h16pos.ne'
                field_simp [hne]
            _ = (1 / (4 * (16 : ℝ) ^ 7)) ^ 2 := by
                rw [div_pow, one_pow, mul_pow, ← pow_mul, show (4 : ℝ) ^ 2 = 16 by norm_num,
                  ← pow_succ']
        calc Real.sqrt (u * Real.log (280 / u)) ≤ Real.sqrt ((1 / (4 * (16 : ℝ) ^ 7)) ^ 2) :=
              Real.sqrt_le_sqrt (h1.trans h2)
          _ = 1 / (4 * (16 : ℝ) ^ 7) :=
              Real.sqrt_sq (div_nonneg (by norm_num) (mul_nonneg (by norm_num) (pow_nonneg h16pos.le 7)))
      have hdiv_eq : Real.sqrt (N : ℝ) / Real.sqrt (m : ℝ) = Real.sqrt u :=
        (Real.sqrt_div hNr_pos.le (m : ℝ)).symm
      have harg_eq : 280 * (m : ℝ) / (N : ℝ) = 280 / u := by
        dsimp only [u]; field_simp [hNr_pos.ne', hmr_pos.ne']
      have hcomb : (c1 j + 200) * Real.sqrt (N : ℝ) * ((2 : ℝ) ^ 20 / Real.sqrt (m : ℝ)) ≤ 1 := by
        dsimp only [c1]
        rw [harg_eq]
        have hrw : (100 * Real.sqrt (Real.log (280 / u)) + 200) * Real.sqrt (N : ℝ) *
            ((2 : ℝ) ^ 20 / Real.sqrt (m : ℝ)) =
            100 * (Real.sqrt u * Real.sqrt (Real.log (280 / u)) * (2 : ℝ) ^ 20) +
            200 * (Real.sqrt u * (2 : ℝ) ^ 20) := by
          rw [← hdiv_eq]; ring
        rw [hrw]
        have h20eq : (2 : ℝ) ^ 20 = (16 : ℝ) ^ 5 := by norm_num
        have h1 : Real.sqrt u * Real.sqrt (Real.log (280 / u)) * (2 : ℝ) ^ 20 ≤ 1 / 1024 := by
          calc Real.sqrt u * Real.sqrt (Real.log (280 / u)) * (2 : ℝ) ^ 20
              ≤ (1 / (4 * (16 : ℝ) ^ 7)) * (2 : ℝ) ^ 20 :=
                mul_le_mul_of_nonneg_right hprod_le (by norm_num)
            _ = 1 / 1024 := by rw [h20eq]; norm_num
        have h2 : Real.sqrt u * (2 : ℝ) ^ 20 ≤ 1 / 1024 := by
          calc Real.sqrt u * (2 : ℝ) ^ 20
              ≤ (1 / (2 * (16 : ℝ) ^ 16)) * (2 : ℝ) ^ 20 :=
                mul_le_mul_of_nonneg_right hsqrt_u (by norm_num)
            _ = 1 / (2 * (16 : ℝ) ^ 11) := by
                rw [h20eq, show (16 : ℕ) = 5 + 11 by norm_num, pow_add]
                have hne1 : (16 : ℝ) ^ 5 ≠ 0 := pow_ne_zero 5 h16pos.ne'
                have hne2 : (16 : ℝ) ^ 11 ≠ 0 := pow_ne_zero 11 h16pos.ne'
                field_simp [hne1, hne2]
            _ ≤ 1 / 1024 := by
                apply one_div_le_one_div_of_le (by norm_num)
                have hge : (16 : ℝ) ^ 3 ≤ (16 : ℝ) ^ 11 :=
                  pow_le_pow_right₀ (by norm_num) (by norm_num : 3 ≤ 11)
                have h3 : (16 : ℝ) ^ 3 = 4096 := by norm_num
                linarith only [hge, h3]
        linarith only [h1, h2]
      exact hb.trans hcomb
    -- Step 2: Apply `hColor` on the `E ≤ 7*m` evaluation points to round `epsTilde` to `ε ∈ {-1, 1}^m`.
    let v2 : Fin E → Fin m → ℝ := fun ξ j => Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θs ξ)
    have hv2_bound : ∀ ξ j, |v2 ξ j| ≤ 1 := fun ξ j => Real.abs_sin_le_one _
    have hc2_budget : ∑ _ξ : Fin E, Real.exp (-((800 : ℝ) ^ 2 / 10000)) ≤ (m : ℝ) / 280 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hexp64 : Real.exp (-((800 : ℝ) ^ 2 / 10000)) ≤ 1 / 1960 := by
        have harg : -((800 : ℝ) ^ 2 / 10000) = -64 := by norm_num
        rw [harg, Real.exp_neg, one_div]
        apply inv_anti₀ (by norm_num)
        have h2le : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
        have hpow := pow_le_pow_left₀ (by norm_num) h2le 64
        rw [← Real.exp_nat_mul] at hpow
        have h64 : (1960 : ℝ) ≤ (2 : ℝ) ^ 64 :=
          le_trans (by norm_num : (1960 : ℝ) ≤ (2 : ℝ) ^ 11)
            (pow_le_pow_right₀ (by norm_num) (by norm_num : 11 ≤ 64))
        have hrw : (64 : ℕ) * (1 : ℝ) = (64 : ℝ) := by norm_num
        rw [hrw] at hpow
        linarith
      have hEr : (E : ℝ) ≤ 7 * (m : ℝ) := by exact_mod_cast hE
      calc (E : ℝ) * Real.exp (-((800 : ℝ) ^ 2 / 10000))
          ≤ (7 * (m : ℝ)) * (1 / 1960) :=
            mul_le_mul hEr hexp64 (Real.exp_pos _).le (by positivity)
        _ = (m : ℝ) / 280 := by ring
    obtain ⟨ε, hε_pm, hε_bound⟩ := hColor m E v2 epsTilde hepsTilde_le
      (fun _ => 800) (fun _ => by norm_num) hc2_budget (fun _ => 1) hv2_bound
    refine ⟨ε, hε_pm, ?_⟩
    intro ξ ⟨ab, hab_mem, hθ_in⟩
    set θ₀ := foldAngle (θs ξ)
    -- Relate `∑ j, epsTilde j * sin((2j+1) θ₀)` to the Fejér convolution via `quadInt_fejerK_eq`.
    have htilde_eq : ∑ j : Fin m, epsTilde j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θ₀) =
        K * Real.sqrt m * ((1 / (2 * Real.pi)) *
          ∑ i : Fin N, α i * quadInt (aI i) (bI i) (fun t => fejerK (2 * m) (θ₀ - t))) := by
      have hswap : ∑ j : Fin m, epsTilde j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θ₀) =
          ∑ i : Fin N, α i * ∑ j : Fin m, v1 j i * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θ₀) := by
        simp only [epsTilde, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hswap, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hfeq := quadInt_fejerK_eq m (aI i) (bI i) θ₀
      rw [← Fin.sum_univ_eq_sum_range] at hfeq
      have hinner : ∑ j : Fin m, v1 j i * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θ₀) =
          K * Real.sqrt m * ((1 / (2 * Real.pi)) * quadInt (aI i) (bI i) (fun t => fejerK (2 * m) (θ₀ - t))) := by
        rw [hfeq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by dsimp [v1]; ring
      rw [hinner]; ring
    -- Apply `abs_sum_quadInt_ge` + `integral_fejerK_outside_le` at `i₀ = e.symm ⟨ab, hab_mem⟩`.
    let i₀ : Fin N := e.symm ⟨ab, hab_mem⟩
    have hi₀_eq : (e i₀).1 = ab := by simp [i₀]
    have hcov_lo : aI i₀ ≤ θ₀ - δ := by
      dsimp only [aI]; rw [hi₀_eq]; linarith [hθ_in.1]
    have hcov_hi : θ₀ + δ ≤ bI i₀ := by
      dsimp only [bI]; rw [hi₀_eq]; linarith [hθ_in.2]
    have hquad_ge := abs_sum_quadInt_ge aI bI α hα_pm hab hsep
      (fun t => fejerK (2 * m) (θ₀ - t))
      ((fejerK_continuous (2 * m)).comp (continuous_const.sub continuous_id))
      (fun t => fejerK_nonneg (2 * m) (by omega) _) i₀ hδ_pos hcov_lo hcov_hi
    have hθ₀_lo : δ < θ₀ := by linarith [(hab i₀).1, hcov_lo]
    have hθ₀_hi : θ₀ < Real.pi / 2 - δ := by linarith [(hab i₀).2.2, hcov_hi]
    have htail := integral_fejerK_outside_le m (by omega) hθ₀_lo hθ₀_hi
    have hfull := integral_fejerK_sub (2 * m) θ₀
    have hquad_num : 5 * Real.pi / 4 ≤ |∑ i : Fin N, α i * quadInt (aI i) (bI i) (fun t => fejerK (2 * m) (θ₀ - t))| := by
      linarith
    have htilde_ge : 1250 * Real.sqrt m ≤ |∑ j : Fin m, epsTilde j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θs ξ)| := by
      rw [← abs_oddSin_foldAngle m epsTilde (θs ξ)]
      change 1250 * Real.sqrt m ≤ |∑ j : Fin m, epsTilde j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θ₀)|
      rw [htilde_eq, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ K),
        abs_of_nonneg (Real.sqrt_nonneg m),
        abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi))]
      have h1 : (1 / (2 * Real.pi)) * (5 * Real.pi / 4) = 5 / 8 := by
        field_simp [Real.pi_pos.ne']; ring
      have h2 : 5 / 8 ≤ (1 / (2 * Real.pi)) * |∑ i : Fin N, α i * quadInt (aI i) (bI i) (fun t => fejerK (2 * m) (θ₀ - t))| := by
        rw [← h1]
        exact mul_le_mul_of_nonneg_left hquad_num (by positivity)
      dsimp only [K]
      nlinarith [Real.sqrt_nonneg m]
    have hdiff_le : |∑ j : Fin m, ε j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θs ξ) -
        ∑ j : Fin m, epsTilde j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θs ξ)| ≤ 1000 * Real.sqrt m := by
      have hb := hε_bound ξ
      simp only [v2, mul_one] at hb
      have hrw : ∑ j : Fin m, ε j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θs ξ) -
          ∑ j : Fin m, epsTilde j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θs ξ) =
          ∑ j : Fin m, (ε j - epsTilde j) * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θs ξ) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hrw]
      linarith
    have hrev := abs_sub_abs_le_abs_sub
      (∑ j : Fin m, epsTilde j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θs ξ))
      (∑ j : Fin m, ε j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θs ξ))
    rw [abs_sub_comm] at hrev
    linarith [Real.sqrt_nonneg m]

end TwoOrbitFejer

/-!
# Finite Probabilistic Perturbation for the Two-Orbit Full Detector

Formalizes Section 2 of the two-orbit paper proof completely in finite combinatorics
(product weights over `Finset (Fin n)`, zero measure theory):
1. `binom_mode_ge`: integer-mean binomial mode lower bound `1 / (N + 1)`.
2. `probW_linear_tail`: sub-Gaussian MGF tail bound using `exp x ≤ 1 + x + x^2` on `x ≤ 1/2`.
3. `probW_disjoint_cover_fail` / `probW_disjoint_miss_fail`: exact factorization over
   pairwise-disjoint translates.
4. `seed_from_initial`: combines (1)-(3) to turn any initial seed `S₀` with
   `|S₀.card - k| ≤ C₀ √n` and `max (‖hatSet I ξ‖) (‖hatSet S₀ ξ‖) ≥ b √n` into an exact-size
   seed `S` (`S.card = k`) satisfying both the joint Fourier floor and all small-row witnesses.
-/

namespace TwoOrbitPerturb

open scoped BigOperators
open Finset

/-! ### Section 1: Elementary exponential bound and binomial mode -/

private lemma le_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hnn : ∀ x, a < x → x < b → 0 ≤ f' x) : f a ≤ f b := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · have hpos : 0 < b - a := sub_pos.mpr hlt
    let s : ℝ := (f b - f a) / (b - a)
    let g : ℝ → ℝ := fun x => f x - s * (x - a)
    have hg_deriv : ∀ x, HasDerivAt g (f' x - s) x := fun x => by
      have hlin : HasDerivAt (fun y : ℝ => s * (y - a)) s x :=
        (((hasDerivAt_id' x).sub_const a).const_mul s).congr_deriv (by ring)
      exact (hd x).sub hlin
    have hg_eq : g a = g b := by
      dsimp only [g, s]; field_simp [hpos.ne']; ring
    obtain ⟨c, ⟨hca, hcb⟩, hc⟩ := exists_deriv_eq_zero hlt
      (fun x _ => (hg_deriv x).continuousAt.continuousWithinAt) hg_eq
    rw [(hg_deriv c).deriv] at hc
    have hnn_c : 0 ≤ f' c := hnn c hca hcb
    have hs_ge : 0 ≤ s := by linarith
    dsimp only [s] at hs_ge
    rw [le_div_iff₀ hpos] at hs_ge
    linarith

private lemma le_of_hasDerivAt_nonpos {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hnp : ∀ x, a < x → x < b → f' x ≤ 0) : f b ≤ f a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · have hpos : 0 < b - a := sub_pos.mpr hlt
    let s : ℝ := (f b - f a) / (b - a)
    let g : ℝ → ℝ := fun x => f x - s * (x - a)
    have hg_deriv : ∀ x, HasDerivAt g (f' x - s) x := fun x => by
      have hlin : HasDerivAt (fun y : ℝ => s * (y - a)) s x :=
        (((hasDerivAt_id' x).sub_const a).const_mul s).congr_deriv (by ring)
      exact (hd x).sub hlin
    have hg_eq : g a = g b := by
      dsimp only [g, s]; field_simp [hpos.ne']; ring
    obtain ⟨c, ⟨hca, hcb⟩, hc⟩ := exists_deriv_eq_zero hlt
      (fun x _ => (hg_deriv x).continuousAt.continuousWithinAt) hg_eq
    rw [(hg_deriv c).deriv] at hc
    have hnp_c : f' c ≤ 0 := hnp c hca hcb
    have hs_le : s ≤ 0 := by linarith
    dsimp only [s] at hs_le
    rw [div_le_iff₀ hpos] at hs_le
    linarith

private lemma prod_le_prod_nonneg {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : 0 ≤ f a := hf a (Finset.mem_insert_self _ _)
    have h2 : f a ≤ g a := hfg a (Finset.mem_insert_self _ _)
    have h3 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h4 : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    exact mul_le_mul h2 h4 h3 (h1.trans h2)

/-- `exp x ≤ 1 + x + x^2` for all `x ≤ 1/2`. -/
lemma exp_le_one_add_add_sq {x : ℝ} (hx : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have hexp_half : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have h1 : (1 : ℝ) / 2 ≤ Real.exp (-(1 : ℝ) / 2) := by
      have := Real.add_one_le_exp (-(1 : ℝ) / 2); linarith
    have hmul : Real.exp (1 / 2 : ℝ) * Real.exp (-(1 : ℝ) / 2) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  let f : ℝ → ℝ := fun t => 1 + t + t ^ 2 - Real.exp t
  let f' : ℝ → ℝ := fun t => 1 + 2 * t - Real.exp t
  have hf_deriv : ∀ t : ℝ, HasDerivAt f (f' t) t := by
    intro t
    have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * t) t := by
      have hmul : HasDerivAt (fun y : ℝ => y * y) (2 * t) t :=
        ((hasDerivAt_id' t).mul (hasDerivAt_id' t)).congr_deriv (by ring)
      simpa [pow_two] using hmul
    have hpoly : HasDerivAt (fun y : ℝ => 1 + y + y ^ 2) (1 + 2 * t) t :=
      (((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id' t)).add hsq).congr_deriv (by ring)
    exact hpoly.sub (Real.hasDerivAt_exp t)
  have hf'_deriv : ∀ t : ℝ, HasDerivAt f' (2 - Real.exp t) t := by
    intro t
    have hlin : HasDerivAt (fun y : ℝ => 1 + 2 * y) 2 t :=
      ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id' t).const_mul 2)).congr_deriv (by ring)
    exact hlin.sub (Real.hasDerivAt_exp t)
  have hf'_mono : ∀ a b : ℝ, a ≤ b → b ≤ 1 / 2 → f' a ≤ f' b := by
    intro a b hab hb
    apply le_of_hasDerivAt_nonneg hab hf'_deriv
    intro t _ htb
    have : Real.exp t ≤ Real.exp (1 / 2 : ℝ) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hf'_0 : f' 0 = 0 := by simp [f']
  have hf_0 : f 0 = 0 := by simp [f]
  have hf_nn : 0 ≤ f x := by
    rcases le_total 0 x with hx0 | hx0
    · have hle := le_of_hasDerivAt_nonneg hx0 hf_deriv (fun t ht0 htx => by
        have := hf'_mono 0 t (le_of_lt ht0) (by linarith); linarith)
      linarith
    · have hle := le_of_hasDerivAt_nonpos hx0 hf_deriv (fun t _ ht0 => by
        have := hf'_mono t 0 (le_of_lt ht0) (by norm_num); linarith)
      linarith
  dsimp only [f] at hf_nn
  linarith

/-- Integer-mean binomial distribution attains its maximum at its mean `m = N * p`,
giving probability at least `1 / (N + 1)`. -/
lemma binom_mode_ge (N m : ℕ) (hm0 : 0 < m) (hmN : m < N) :
    let q : ℝ := (m : ℝ) / (N : ℝ)
    1 / ((N : ℝ) + 1) ≤ (N.choose m : ℝ) * q ^ m * (1 - q) ^ (N - m) := by
  intro q
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_trans hm0 hmN)
  have hq_pos : 0 < q := by dsimp [q]; positivity
  have h1q_pos : 0 < 1 - q := by
    dsimp only [q]
    rw [sub_pos, div_lt_one hN_pos]
    exact_mod_cast hmN
  let pmf (r : ℕ) : ℝ := (N.choose r : ℝ) * q ^ r * (1 - q) ^ (N - r)
  have hsum : ∑ r ∈ range (N + 1), pmf r = 1 := by
    have h := add_pow q (1 - q) N
    rw [add_sub_cancel, one_pow] at h
    rw [h]
    refine Finset.sum_congr rfl fun r _ => by dsimp [pmf]; ring
  have hstep : ∀ r < N,
      pmf (r + 1) * ((r + 1 : ℝ) * (1 - q)) = pmf r * (((N - r : ℕ) : ℝ) * q) := by
    intro r hr
    dsimp only [pmf]
    have hch : (N.choose (r + 1) : ℝ) * ((r + 1 : ℕ) : ℝ) = (N.choose r : ℝ) * ((N - r : ℕ) : ℝ) := by
      have hnat : (r + 1) * N.choose (r + 1) = (N - r) * N.choose r := by
        have := Nat.add_one_mul_choose_eq N r
        -- `N.choose r * (N - r) = N.choose (r + 1) * (r + 1)` via `Nat.choose_succ_right_eq`.
        have h1 := Nat.choose_succ_right_eq N r
        linarith
      have hcast : ((r + 1 : ℕ) : ℝ) * (N.choose (r + 1) : ℝ) =
          ((N - r : ℕ) : ℝ) * (N.choose r : ℝ) := by exact_mod_cast hnat
      linarith
    have hsub : N - r = (N - (r + 1)) + 1 := by omega
    have hpow : (1 - q) ^ (N - r) = (1 - q) ^ (N - (r + 1)) * (1 - q) := by
      rw [hsub, pow_succ]
    rw [pow_succ q, hpow]
    push_cast at hch ⊢
    calc (N.choose (r + 1) : ℝ) * (q ^ r * q) * (1 - q) ^ (N - (r + 1)) * (((r : ℝ) + 1) * (1 - q))
        = ((N.choose (r + 1) : ℝ) * ((r : ℝ) + 1)) * (q ^ r * q * ((1 - q) ^ (N - (r + 1)) * (1 - q))) := by ring
      _ = ((N.choose r : ℝ) * ((N - r : ℕ) : ℝ)) * (q ^ r * q * ((1 - q) ^ (N - (r + 1)) * (1 - q))) := by
          rw [hch]
      _ = (N.choose r : ℝ) * q ^ r * ((1 - q) ^ (N - (r + 1)) * (1 - q)) * (((N - r : ℕ) : ℝ) * q) := by ring
  have hup : ∀ r < m, pmf r ≤ pmf (r + 1) := by
    intro r hr
    have hEq := hstep r (lt_trans hr hmN)
    have hden_pos : 0 < ((r : ℝ) + 1) * (1 - q) := by positivity
    have hcmp : ((r : ℝ) + 1) * (1 - q) ≤ ((N - r : ℕ) : ℝ) * q := by
      dsimp only [q]
      rw [Nat.cast_sub (le_of_lt (lt_trans hr hmN))]
      have hle : (r : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hr
      have h1 : ((r : ℝ) + 1) * (1 - (m : ℝ) / (N : ℝ)) * (N : ℝ) ≤
          ((N : ℝ) - (r : ℝ)) * ((m : ℝ) / (N : ℝ)) * (N : ℝ) := by
        field_simp [hN_pos.ne']
        nlinarith
      exact le_of_mul_le_mul_right h1 hN_pos
    have hpmf_nn : 0 ≤ pmf r := by dsimp [pmf]; positivity
    have hmul : pmf r * (((r : ℝ) + 1) * (1 - q)) ≤ pmf (r + 1) * (((r : ℝ) + 1) * (1 - q)) := by
      rw [hEq]
      exact mul_le_mul_of_nonneg_left hcmp hpmf_nn
    exact le_of_mul_le_mul_right hmul hden_pos
  have hdown : ∀ r, m ≤ r → r < N → pmf (r + 1) ≤ pmf r := by
    intro r hmr hrN
    have hEq := hstep r hrN
    have hden_pos : 0 < ((r : ℝ) + 1) * (1 - q) := by positivity
    have hcmp : ((N - r : ℕ) : ℝ) * q ≤ ((r : ℝ) + 1) * (1 - q) := by
      dsimp only [q]
      rw [Nat.cast_sub (le_of_lt hrN)]
      have hge : (m : ℝ) ≤ (r : ℝ) := by exact_mod_cast hmr
      have hmN_r : (m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
      have h1 : ((N : ℝ) - (r : ℝ)) * ((m : ℝ) / (N : ℝ)) * (N : ℝ) ≤
          ((r : ℝ) + 1) * (1 - (m : ℝ) / (N : ℝ)) * (N : ℝ) := by
        field_simp [hN_pos.ne']
        nlinarith
      exact le_of_mul_le_mul_right h1 hN_pos
    have hpmf_nn : 0 ≤ pmf r := by dsimp [pmf]; positivity
    have hmul : pmf (r + 1) * (((r : ℝ) + 1) * (1 - q)) ≤ pmf r * (((r : ℝ) + 1) * (1 - q)) := by
      rw [hEq]
      exact mul_le_mul_of_nonneg_left hcmp hpmf_nn
    exact le_of_mul_le_mul_right hmul hden_pos
  have hmax : ∀ r ≤ N, pmf r ≤ pmf m := by
    intro r hrN
    rcases le_total r m with hle | hge
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      induction d generalizing r with
      | zero =>
        have hrm : r = m := by omega
        subst hrm; exact le_rfl
      | succ d ih =>
        exact (hup r (by omega)).trans (ih (r + 1) (by omega) (by omega) (by omega))
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hge
      induction d generalizing r with
      | zero =>
        have hrm : r = m := by omega
        subst hrm; exact le_rfl
      | succ d ih =>
        have hr_eq : r = (m + d) + 1 := by omega
        rw [hr_eq]
        exact (hdown (m + d) (by omega) (by omega)).trans (ih (m + d) (by omega) (by omega) (by omega))
  have h1 : (1 : ℝ) ≤ ((N : ℝ) + 1) * pmf m := by
    calc (1 : ℝ) = ∑ r ∈ range (N + 1), pmf r := hsum.symm
      _ ≤ ∑ _r ∈ range (N + 1), pmf m := Finset.sum_le_sum fun r hr => hmax r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
      _ = ((N : ℝ) + 1) * pmf m := by simp [Finset.sum_const]
  rw [div_le_iff₀ (by positivity)]
  linarith

/-! ### Section 2: Finite product distribution `probWU` on subsets of `U : Finset α` -/

def probWU {α : Type*} [DecidableEq α] (p : α → ℝ) (U S : Finset α) : ℝ :=
  (∏ i ∈ S, p i) * (∏ i ∈ U \ S, (1 - p i))

lemma probWU_nonneg {α : Type*} [DecidableEq α] (p : α → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (U S : Finset α) : 0 ≤ probWU p U S := by
  unfold probWU
  exact mul_nonneg (Finset.prod_nonneg fun i _ => hp0 i) (Finset.prod_nonneg fun i _ => by linarith [hp1 i])

/-- Master factorization identity: `∑_{S ⊆ U} probWU p U S * (∏_{i ∈ S} f₁ i) * (∏_{i ∈ U \ S} f₀ i) = ∏_{i ∈ U} (p i * f₁ i + (1 - p i) * f₀ i)`. -/
lemma sum_probWU_prod {α : Type*} [DecidableEq α] (p f₁ f₀ : α → ℝ) (U : Finset α) :
    ∑ S ∈ U.powerset, probWU p U S * (∏ i ∈ S, f₁ i) * (∏ i ∈ U \ S, f₀ i) =
      ∏ i ∈ U, (p i * f₁ i + (1 - p i) * f₀ i) := by
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  unfold probWU
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

lemma sum_probWU_eq_one {α : Type*} [DecidableEq α] (p : α → ℝ) (U : Finset α) :
    ∑ S ∈ U.powerset, probWU p U S = 1 := by
  have h := sum_probWU_prod p (fun _ => 1) (fun _ => 1) U
  simpa using h

/-- Splitting `U = A ⊔ B` factors `probWU p U (S₁ ∪ S₂) = probWU p A S₁ * probWU p B S₂`. -/
lemma probWU_union_disjoint {α : Type*} [DecidableEq α] (p : α → ℝ) {A B S₁ S₂ : Finset α}
    (hAB : Disjoint A B) (hS₁ : S₁ ⊆ A) (hS₂ : S₂ ⊆ B) :
    probWU p (A ∪ B) (S₁ ∪ S₂) = probWU p A S₁ * probWU p B S₂ := by
  have hSdisj : Disjoint S₁ S₂ := Disjoint.mono hS₁ hS₂ hAB
  have hdiff : (A ∪ B) \ (S₁ ∪ S₂) = (A \ S₁) ∪ (B \ S₂) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hxA | hxB, hnot⟩
      · exact Or.inl ⟨hxA, fun h => hnot (Or.inl h)⟩
      · exact Or.inr ⟨hxB, fun h => hnot (Or.inr h)⟩
    · rintro (⟨hxA, hnot1⟩ | ⟨hxB, hnot2⟩)
      · refine ⟨Or.inl hxA, ?_⟩
        rintro (h1 | h2)
        · exact hnot1 h1
        · exact Finset.disjoint_left.mp hAB hxA (hS₂ h2)
      · refine ⟨Or.inr hxB, ?_⟩
        rintro (h1 | h2)
        · exact Finset.disjoint_right.mp hAB hxB (hS₁ h1)
        · exact hnot2 h2
  have hDdisj : Disjoint (A \ S₁) (B \ S₂) := Disjoint.mono sdiff_subset sdiff_subset hAB
  unfold probWU
  rw [Finset.prod_union hSdisj, hdiff, Finset.prod_union hDdisj]
  ring

/-- Sub-Gaussian MGF tail bound for `∑ i ∈ U, ((1_{i ∈ S} - p i) * w i)`. -/
lemma sum_probWU_linear_tail {α : Type*} [DecidableEq α] (p w : α → ℝ) (U : Finset α)
    (hp0 : ∀ i ∈ U, 0 ≤ p i) (hp1 : ∀ i ∈ U, p i ≤ 1) (hw : ∀ i ∈ U, |w i| ≤ 1)
    {V t : ℝ} (hV : 0 < V) (hvar : ∑ i ∈ U, p i * (1 - p i) ≤ V)
    (ht0 : 0 ≤ t) (htV : t ≤ V) :
    ∑ S ∈ U.powerset.filter (fun S => t ≤ |∑ i ∈ U, ((if i ∈ S then (1 : ℝ) else 0) - p i) * w i|),
        probWU p U S
      ≤ 2 * Real.exp (-(t ^ 2 / (4 * V))) := by
  have hone : ∀ u : α → ℝ, (∀ i ∈ U, |u i| ≤ 1) →
      ∑ S ∈ U.powerset.filter (fun S => t ≤ ∑ i ∈ U, ((if i ∈ S then (1 : ℝ) else 0) - p i) * u i),
          probWU p U S
        ≤ Real.exp (-(t ^ 2 / (4 * V))) := by
    intro u hu
    let h : ℝ := t / (2 * V)
    have hh0 : 0 ≤ h := by dsimp [h]; positivity
    have hh_le : h ≤ 1 / 2 := by
      dsimp only [h]
      rw [div_le_iff₀ (by positivity)]
      linarith
    -- Compute MGF `∑_{S ⊆ U} probWU p U S * exp (h * ∑_{i ∈ U} (1_{i ∈ S} - p i) * u i)`.
    have hmgf : ∑ S ∈ U.powerset, probWU p U S *
          Real.exp (h * ∑ i ∈ U, ((if i ∈ S then (1 : ℝ) else 0) - p i) * u i)
        ≤ Real.exp (h ^ 2 * V) := by
      have hexp_split : ∀ S ∈ U.powerset,
          Real.exp (h * ∑ i ∈ U, ((if i ∈ S then (1 : ℝ) else 0) - p i) * u i) =
          (∏ i ∈ S, Real.exp (h * (1 - p i) * u i)) *
          (∏ i ∈ U \ S, Real.exp (h * (-p i) * u i)) := by
        intro S hS
        have hSsub : S ⊆ U := Finset.mem_powerset.mp hS
        rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_sdiff hSsub, mul_comm]
        have h1 : ∏ x ∈ S, Real.exp (h * (((if x ∈ S then (1 : ℝ) else 0) - p x) * u x)) =
            ∏ i ∈ S, Real.exp (h * (1 - p i) * u i) :=
          Finset.prod_congr rfl fun i hi => by simp only [hi, ↓reduceIte]; congr 1; ring
        have h2 : ∏ x ∈ U \ S, Real.exp (h * (((if x ∈ S then (1 : ℝ) else 0) - p x) * u x)) =
            ∏ i ∈ U \ S, Real.exp (h * (-p i) * u i) :=
          Finset.prod_congr rfl fun i hi => by
            have hnot : i ∉ S := (Finset.mem_sdiff.mp hi).2
            simp only [hnot, ↓reduceIte]; congr 1; ring
        rw [h1, h2]
      have hlhs : ∑ S ∈ U.powerset, probWU p U S *
            Real.exp (h * ∑ i ∈ U, ((if i ∈ S then (1 : ℝ) else 0) - p i) * u i) =
          ∏ i ∈ U, (p i * Real.exp (h * (1 - p i) * u i) + (1 - p i) * Real.exp (h * (-p i) * u i)) := by
        rw [← sum_probWU_prod p (fun i => Real.exp (h * (1 - p i) * u i))
          (fun i => Real.exp (h * (-p i) * u i)) U]
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [hexp_split S hS, mul_assoc]
      rw [hlhs]
      have hfactor : ∀ i ∈ U,
          p i * Real.exp (h * (1 - p i) * u i) + (1 - p i) * Real.exp (h * (-p i) * u i) ≤
            Real.exp (h ^ 2 * (p i * (1 - p i))) := by
        intro i hi
        have hp0i := hp0 i hi
        have hp1i := hp1 i hi
        have hui := hu i hi
        have hx1 : h * (1 - p i) * u i ≤ 1 / 2 := by
          have habs : |h * (1 - p i) * u i| ≤ h := by
            rw [abs_mul, abs_mul, abs_of_nonneg hh0, abs_of_nonneg (by linarith)]
            have h1 : (1 - p i) * |u i| ≤ 1 := by
              calc (1 - p i) * |u i| ≤ 1 * 1 := mul_le_mul (by linarith) hui (abs_nonneg _) (by norm_num)
                _ = 1 := one_mul 1
            calc h * (1 - p i) * |u i| = h * ((1 - p i) * |u i|) := by ring
              _ ≤ h * 1 := mul_le_mul_of_nonneg_left h1 hh0
              _ = h := mul_one h
          linarith [(abs_le.mp habs).2]
        have hx2 : h * (-p i) * u i ≤ 1 / 2 := by
          have habs : |h * (-p i) * u i| ≤ h := by
            rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hh0, abs_of_nonneg hp0i]
            have h1 : p i * |u i| ≤ 1 := by
              calc p i * |u i| ≤ 1 * 1 := mul_le_mul hp1i hui (abs_nonneg _) (by norm_num)
                _ = 1 := one_mul 1
            calc h * p i * |u i| = h * (p i * |u i|) := by ring
              _ ≤ h * 1 := mul_le_mul_of_nonneg_left h1 hh0
              _ = h := mul_one h
          linarith [(abs_le.mp habs).2]
        have he1 := exp_le_one_add_add_sq hx1
        have he2 := exp_le_one_add_add_sq hx2
        have hlin : p i * (1 + h * (1 - p i) * u i + (h * (1 - p i) * u i) ^ 2) +
            (1 - p i) * (1 + h * (-p i) * u i + (h * (-p i) * u i) ^ 2) =
            1 + h ^ 2 * (p i * (1 - p i)) * u i ^ 2 := by ring
        have hu2 : u i ^ 2 ≤ 1 := by nlinarith [sq_abs (u i), abs_nonneg (u i)]
        have hquad : p i * Real.exp (h * (1 - p i) * u i) + (1 - p i) * Real.exp (h * (-p i) * u i) ≤
            1 + h ^ 2 * (p i * (1 - p i)) := by
          have hstep1 : p i * Real.exp (h * (1 - p i) * u i) + (1 - p i) * Real.exp (h * (-p i) * u i) ≤
              p i * (1 + h * (1 - p i) * u i + (h * (1 - p i) * u i) ^ 2) +
              (1 - p i) * (1 + h * (-p i) * u i + (h * (-p i) * u i) ^ 2) :=
            by exact add_le_add (mul_le_mul_of_nonneg_left he1 hp0i) (mul_le_mul_of_nonneg_left he2 (by linarith))
          rw [hlin] at hstep1
          have hcoef_nn : 0 ≤ h ^ 2 * (p i * (1 - p i)) := by
            have : 0 ≤ p i * (1 - p i) := mul_nonneg hp0i (by linarith)
            positivity
          have hstep2 : h ^ 2 * (p i * (1 - p i)) * u i ^ 2 ≤ h ^ 2 * (p i * (1 - p i)) := by
            calc h ^ 2 * (p i * (1 - p i)) * u i ^ 2
                ≤ h ^ 2 * (p i * (1 - p i)) * 1 := mul_le_mul_of_nonneg_left hu2 hcoef_nn
              _ = h ^ 2 * (p i * (1 - p i)) := mul_one _
          linarith
        exact hquad.trans (by linarith [Real.add_one_le_exp (h ^ 2 * (p i * (1 - p i)))])
      calc ∏ i ∈ U, (p i * Real.exp (h * (1 - p i) * u i) + (1 - p i) * Real.exp (h * (-p i) * u i))
          ≤ ∏ i ∈ U, Real.exp (h ^ 2 * (p i * (1 - p i))) :=
            prod_le_prod_nonneg U _ _ (fun i hi => by
              have : 0 ≤ p i := hp0 i hi
              have : 0 ≤ 1 - p i := by linarith [hp1 i hi]
              positivity) hfactor
        _ = Real.exp (∑ i ∈ U, h ^ 2 * (p i * (1 - p i))) := (Real.exp_sum _ _).symm
        _ = Real.exp (h ^ 2 * ∑ i ∈ U, p i * (1 - p i)) := by rw [← Finset.mul_sum]
        _ ≤ Real.exp (h ^ 2 * V) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvar (sq_nonneg h))
    -- Markov inequality.
    let E := U.powerset.filter (fun S => t ≤ ∑ i ∈ U, ((if i ∈ S then (1 : ℝ) else 0) - p i) * u i)
    have hmarkov : (∑ S ∈ E, probWU p U S) * Real.exp (h * t) ≤ Real.exp (h ^ 2 * V) := by
      have h1 : (∑ S ∈ E, probWU p U S) * Real.exp (h * t) ≤
          ∑ S ∈ E, probWU p U S * Real.exp (h * ∑ i ∈ U, ((if i ∈ S then (1 : ℝ) else 0) - p i) * u i) := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun S hS => ?_
        have hSsub : S ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
        have hWnn : 0 ≤ probWU p U S := by
          unfold probWU
          exact mul_nonneg (Finset.prod_nonneg fun i hi => hp0 i (hSsub hi))
            (Finset.prod_nonneg fun i hi => by linarith [hp1 i (Finset.mem_sdiff.mp hi).1])
        apply mul_le_mul_of_nonneg_left _ hWnn
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hS).2 hh0)
      have h2 : ∑ S ∈ E, probWU p U S * Real.exp (h * ∑ i ∈ U, ((if i ∈ S then (1 : ℝ) else 0) - p i) * u i) ≤
          ∑ S ∈ U.powerset, probWU p U S * Real.exp (h * ∑ i ∈ U, ((if i ∈ S then (1 : ℝ) else 0) - p i) * u i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro S hS _
        have hSsub : S ⊆ U := Finset.mem_powerset.mp hS
        have hWnn : 0 ≤ probWU p U S := by
          unfold probWU
          exact mul_nonneg (Finset.prod_nonneg fun i hi => hp0 i (hSsub hi))
            (Finset.prod_nonneg fun i hi => by linarith [hp1 i (Finset.mem_sdiff.mp hi).1])
        exact mul_nonneg hWnn (Real.exp_pos _).le
      exact (h1.trans h2).trans hmgf
    have hdiv := (le_div_iff₀ (Real.exp_pos (h * t))).mpr hmarkov
    calc ∑ S ∈ E, probWU p U S ≤ Real.exp (h ^ 2 * V) / Real.exp (h * t) := hdiv
      _ = Real.exp (h ^ 2 * V - h * t) := (Real.exp_sub _ _).symm
      _ = Real.exp (-(t ^ 2 / (4 * V))) := by
          congr 1; dsimp only [h]; field_simp [hV.ne']; ring
  have hpos := hone w hw
  have hneg := hone (fun i => -w i) (fun i hi => by rw [abs_neg]; exact hw i hi)
  let Eall := U.powerset.filter (fun S => t ≤ |∑ i ∈ U, ((if i ∈ S then (1 : ℝ) else 0) - p i) * w i|)
  let Epos := U.powerset.filter (fun S => t ≤ ∑ i ∈ U, ((if i ∈ S then (1 : ℝ) else 0) - p i) * w i)
  let Eneg := U.powerset.filter (fun S => t ≤ ∑ i ∈ U, ((if i ∈ S then (1 : ℝ) else 0) - p i) * (-w i))
  have hsub : Eall ⊆ Epos ∪ Eneg := by
    intro S hS
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    have hSp := (Finset.mem_filter.mp hS).1
    rcases le_abs.mp (Finset.mem_filter.mp hS).2 with h | h
    · exact Or.inl ⟨hSp, h⟩
    · refine Or.inr ⟨hSp, ?_⟩
      have : ∑ i ∈ U, ((if i ∈ S then (1 : ℝ) else 0) - p i) * (-w i) =
          -(∑ i ∈ U, ((if i ∈ S then (1 : ℝ) else 0) - p i) * w i) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      linarith
  have hWnn : ∀ S ∈ U.powerset, 0 ≤ probWU p U S := fun S hS => by
    have hSsub := Finset.mem_powerset.mp hS
    unfold probWU
    exact mul_nonneg (Finset.prod_nonneg fun i hi => hp0 i (hSsub hi))
      (Finset.prod_nonneg fun i hi => by linarith [hp1 i (Finset.mem_sdiff.mp hi).1])
  have hsum_le : ∑ S ∈ Eall, probWU p U S ≤ (∑ S ∈ Epos, probWU p U S) + (∑ S ∈ Eneg, probWU p U S) := by
    calc ∑ S ∈ Eall, probWU p U S ≤ ∑ S ∈ Epos ∪ Eneg, probWU p U S :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun S hS _ => by
            rcases Finset.mem_union.mp hS with h | h
            · exact hWnn S (Finset.mem_filter.mp h).1
            · exact hWnn S (Finset.mem_filter.mp h).1
      _ ≤ (∑ S ∈ Epos, probWU p U S) + (∑ S ∈ Eneg, probWU p U S) := by
            have hui := Finset.sum_union_inter (s₁ := Epos) (s₂ := Eneg) (f := probWU p U)
            have hinter_nn : 0 ≤ ∑ S ∈ Epos ∩ Eneg, probWU p U S :=
              Finset.sum_nonneg fun S hS => hWnn S (Finset.mem_filter.mp (Finset.mem_inter.mp hS).1).1
            linarith
  linarith

/-! ### Section 3: Exact factorization over pairwise-disjoint target blocks -/

private lemma inter_union_sdiff_self {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∩ B) ∪ (A \ B) = A := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- For pairwise disjoint blocks `B` inside `U`, the probability that NO block `b ∈ B` is
contained in `S` factors exactly as `∏ b ∈ B, (1 - ∏ i ∈ b, p i)`. -/
lemma sum_probWU_no_cover_eq {α : Type*} [DecidableEq α] (p : α → ℝ)
    (B : Finset (Finset α)) :
    ∀ U : Finset α, (∀ b ∈ B, b ⊆ U) → (B : Set (Finset α)).Pairwise Disjoint →
    ∑ S ∈ U.powerset.filter (fun S => ∀ b ∈ B, ¬ (b ⊆ S)), probWU p U S =
      ∏ b ∈ B, (1 - ∏ i ∈ b, p i) := by
  classical
  induction B using Finset.induction_on with
  | empty =>
    intro U _ _
    simp [sum_probWU_eq_one]
  | @insert b₀ B' hb₀ ih =>
    intro U hsub hpair
    have hb₀U : b₀ ⊆ U := hsub b₀ (Finset.mem_insert_self _ _)
    have hB'pair : (B' : Set (Finset α)).Pairwise Disjoint :=
      hpair.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
    have hdisj_b₀ : ∀ b ∈ B', Disjoint b₀ b := fun b hb =>
      hpair (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hb)
        (fun hEq => hb₀ (hEq ▸ hb))
    have hB'sub : ∀ b ∈ B', b ⊆ U \ b₀ := by
      intro b hb
      exact Finset.subset_sdiff.mpr ⟨hsub b (Finset.mem_insert_of_mem hb), (hdisj_b₀ b hb).symm⟩
    set U' := U \ b₀
    have hUeq : b₀ ∪ U' = U := Finset.union_sdiff_of_subset hb₀U
    have hdisjU : Disjoint b₀ U' := Finset.disjoint_sdiff
    -- Bijection between `{S ⊆ U | no cover}` and `{S₁ ⊆ b₀ | S₁ ≠ b₀} × {S₂ ⊆ U' | no cover in B'}`.
    let F1 := b₀.powerset.filter (fun S₁ => ¬ (b₀ ⊆ S₁))
    let F2 := U'.powerset.filter (fun S₂ => ∀ b ∈ B', ¬ (b ⊆ S₂))
    let Fall := U.powerset.filter (fun S => ∀ b ∈ insert b₀ B', ¬ (b ⊆ S))
    have hbij : ∑ S ∈ Fall, probWU p U S =
        ∑ x ∈ F1 ×ˢ F2, probWU p b₀ x.1 * probWU p U' x.2 := by
      refine Finset.sum_bij (fun S _ => (S ∩ b₀, S \ b₀)) ?_ ?_ ?_ ?_
      · intro S hS
        have hSU : S ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
        have hnc := (Finset.mem_filter.mp hS).2
        refine Finset.mem_product.mpr ⟨?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
          intro h1
          exact hnc b₀ (Finset.mem_insert_self _ _) (h1.trans Finset.inter_subset_left)
        · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff hSU le_rfl), ?_⟩
          intro b hb h1
          exact hnc b (Finset.mem_insert_of_mem hb) (h1.trans Finset.sdiff_subset)
      · intro S₁ _ S₂ _ hEq
        have h1 : S₁ ∩ b₀ = S₂ ∩ b₀ := congrArg Prod.fst hEq
        have h2 : S₁ \ b₀ = S₂ \ b₀ := congrArg Prod.snd hEq
        rw [← inter_union_sdiff_self S₁ b₀, h1, h2, inter_union_sdiff_self]
      · intro x hx
        rcases Finset.mem_product.mp hx with ⟨hx1, hx2⟩
        have h1sub : x.1 ⊆ b₀ := Finset.mem_powerset.mp (Finset.mem_filter.mp hx1).1
        have h1nc : ¬ (b₀ ⊆ x.1) := (Finset.mem_filter.mp hx1).2
        have h2sub : x.2 ⊆ U' := Finset.mem_powerset.mp (Finset.mem_filter.mp hx2).1
        have h2nc := (Finset.mem_filter.mp hx2).2
        refine ⟨x.1 ∪ x.2, ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by
              rw [← hUeq]; exact Finset.union_subset_union h1sub h2sub), ?_⟩
          intro b hb hsub_b
          rcases Finset.mem_insert.mp hb with rfl | hb'
          · apply h1nc
            intro z hz
            rcases Finset.mem_union.mp (hsub_b hz) with hz1 | hz2
            · exact hz1
            · exact absurd hz (Finset.mem_sdiff.mp (h2sub hz2)).2
          · apply h2nc b hb'
            intro z hz
            rcases Finset.mem_union.mp (hsub_b hz) with hz1 | hz2
            · exact absurd (h1sub hz1) (Finset.disjoint_right.mp (hdisj_b₀ b hb') hz)
            · exact hz2
        · apply Prod.ext
          · ext z
            simp only [Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨h1 | h2, hzb⟩
              · exact h1
              · exact absurd hzb (Finset.mem_sdiff.mp (h2sub h2)).2
            · intro h1; exact ⟨Or.inl h1, h1sub h1⟩
          · ext z
            simp only [Finset.mem_sdiff, Finset.mem_union]
            constructor
            · rintro ⟨h1 | h2, hnot⟩
              · exact absurd (h1sub h1) hnot
              · exact h2
            · intro h2; exact ⟨Or.inr h2, (Finset.mem_sdiff.mp (h2sub h2)).2⟩
      · intro S hS
        have hSU : S ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
        have h1 := probWU_union_disjoint p hdisjU (S₁ := S ∩ b₀) (S₂ := S \ b₀)
          Finset.inter_subset_right (Finset.sdiff_subset_sdiff hSU le_rfl)
        rw [hUeq, inter_union_sdiff_self] at h1
        exact h1
    rw [hbij, Finset.sum_product, ← Finset.sum_mul_sum]
    have hF1 : ∑ S₁ ∈ F1, probWU p b₀ S₁ = 1 - ∏ i ∈ b₀, p i := by
      have hEq : F1 = b₀.powerset.erase b₀ := by
        ext S₁
        simp only [F1, Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase]
        constructor
        · rintro ⟨hsub1, hnot⟩; exact ⟨fun h => hnot (h ▸ le_rfl), hsub1⟩
        · rintro ⟨hne, hsub1⟩; exact ⟨hsub1, fun h => hne (Finset.Subset.antisymm hsub1 h)⟩
      rw [hEq]
      have hfull := sum_probWU_eq_one p b₀
      rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset_self b₀)] at hfull
      have htop : probWU p b₀ b₀ = ∏ i ∈ b₀, p i := by simp [probWU]
      linarith
    rw [hF1, ih U' hB'sub hB'pair, Finset.prod_insert hb₀]

/-- Dual version: probability that NO block `b ∈ B` is disjoint from `S` equals
`∏ b ∈ B, (1 - ∏ i ∈ b, (1 - p i))`. -/
lemma sum_probWU_no_miss_eq {α : Type*} [DecidableEq α] (p : α → ℝ)
    (B : Finset (Finset α)) (U : Finset α)
    (hsub : ∀ b ∈ B, b ⊆ U) (hpair : (B : Set (Finset α)).Pairwise Disjoint) :
    ∑ S ∈ U.powerset.filter (fun S => ∀ b ∈ B, ¬ Disjoint b S), probWU p U S =
      ∏ b ∈ B, (1 - ∏ i ∈ b, (1 - p i)) := by
  have h1 := sum_probWU_no_cover_eq (fun i => 1 - p i) B U hsub hpair
  rw [← h1]
  refine Finset.sum_bij (fun S _ => U \ S) ?_ ?_ ?_ ?_
  · intro S hS
    have hSU : S ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    have hnm := (Finset.mem_filter.mp hS).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    intro b hb hbc
    exact hnm b hb (Finset.disjoint_of_subset_left hbc Finset.sdiff_disjoint)
  · intro S₁ h1 S₂ h2 hEq
    have hS₁ : S₁ ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp h1).1
    have hS₂ : S₂ ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp h2).1
    rw [← Finset.sdiff_sdiff_eq_self hS₁, ← Finset.sdiff_sdiff_eq_self hS₂, hEq]
  · intro T hT
    have hTU : T ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    have hnc := (Finset.mem_filter.mp hT).2
    refine ⟨U \ T, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩,
      Finset.sdiff_sdiff_eq_self hTU⟩
    intro b hb hdisj
    apply hnc b hb
    intro x hx
    have hxU : x ∈ U := hsub b hb hx
    by_contra hnot
    exact Finset.disjoint_left.mp hdisj hx (Finset.mem_sdiff.mpr ⟨hxU, hnot⟩)
  · intro S hS
    have hSU : S ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    unfold probWU
    rw [Finset.sdiff_sdiff_eq_self hSU, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun i _ => by ring

/-- Exact-size cardinality lower bound for `S` obtained by deleting from `S₀` with prob `u = d / s`
and adding outside `S₀` with prob `v = e / (n - s)`. -/
lemma sum_probWU_exact_card_ge {α : Type*} [DecidableEq α] (U S₀ : Finset α) (hS₀ : S₀ ⊆ U)
    (d e : ℕ) (hd0 : 0 < d) (hd : d < S₀.card)
    (he0 : 0 < e) (he : e < (U \ S₀).card) :
    let u : ℝ := (d : ℝ) / (S₀.card : ℝ)
    let v : ℝ := (e : ℝ) / ((U \ S₀).card : ℝ)
    let p : α → ℝ := fun i => if i ∈ S₀ then 1 - u else v
    1 / (((U.card : ℝ) + 1) ^ 2) ≤
      ∑ S ∈ U.powerset.filter (fun S => S.card = S₀.card - d + e), probWU p U S := by
  intro u v p
  set R := U \ S₀
  have hUeq : S₀ ∪ R = U := Finset.union_sdiff_of_subset hS₀
  have hdisj : Disjoint S₀ R := Finset.disjoint_sdiff
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp only [u]; rw [div_le_one (by exact_mod_cast lt_trans hd0 hd)]; exact_mod_cast hd.le
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp only [v]; rw [div_le_one (by exact_mod_cast lt_trans he0 he)]; exact_mod_cast he.le
  have hp0 : ∀ i, 0 ≤ p i := fun i => by dsimp [p]; split_ifs <;> linarith
  have hp1 : ∀ i, p i ≤ 1 := fun i => by dsimp [p]; split_ifs <;> linarith
  -- Restrict to `S` with `(S₀ \ S).card = d` and `(S \ S₀).card = e`.
  let G := (S₀.powersetCard (S₀.card - d) ×ˢ R.powersetCard e).image (fun AB => AB.1 ∪ AB.2)
  have hGsub : G ⊆ U.powerset.filter (fun S => S.card = S₀.card - d + e) := by
    intro S hS
    obtain ⟨⟨A, B⟩, hAB, rfl⟩ := Finset.mem_image.mp hS
    rcases Finset.mem_product.mp hAB with ⟨hA, hB⟩
    rcases Finset.mem_powersetCard.mp hA with ⟨hAsub, hAcard⟩
    rcases Finset.mem_powersetCard.mp hB with ⟨hBsub, hBcard⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · rw [← hUeq]; exact Finset.union_subset_union hAsub hBsub
    · rw [Finset.card_union_of_disjoint (Disjoint.mono hAsub hBsub hdisj), hAcard, hBcard]
  have hGsum : ∑ S ∈ G, probWU p U S =
      ((S₀.card.choose d : ℝ) * u ^ d * (1 - u) ^ (S₀.card - d)) *
      ((R.card.choose e : ℝ) * v ^ e * (1 - v) ^ (R.card - e)) := by
    have hinj : ∀ AB₁ ∈ S₀.powersetCard (S₀.card - d) ×ˢ R.powersetCard e,
        ∀ AB₂ ∈ S₀.powersetCard (S₀.card - d) ×ˢ R.powersetCard e,
        AB₁.1 ∪ AB₁.2 = AB₂.1 ∪ AB₂.2 → AB₁ = AB₂ := by
      rintro ⟨A₁, B₁⟩ h1 ⟨A₂, B₂⟩ h2 hEq
      have hA₁ := (Finset.mem_powersetCard.mp (Finset.mem_product.mp h1).1).1
      have hB₁ := (Finset.mem_powersetCard.mp (Finset.mem_product.mp h1).2).1
      have hA₂ := (Finset.mem_powersetCard.mp (Finset.mem_product.mp h2).1).1
      have hB₂ := (Finset.mem_powersetCard.mp (Finset.mem_product.mp h2).2).1
      apply Prod.ext
      · ext x
        have hx := Finset.ext_iff.mp hEq x
        simp only [Finset.mem_union] at hx
        constructor
        · intro h; rcases hx.mp (Or.inl h) with h' | h'
          · exact h'
          · exact absurd (hA₁ h) (Finset.disjoint_right.mp hdisj (hB₂ h'))
        · intro h; rcases hx.mpr (Or.inl h) with h' | h'
          · exact h'
          · exact absurd (hA₂ h) (Finset.disjoint_right.mp hdisj (hB₁ h'))
      · ext x
        have hx := Finset.ext_iff.mp hEq x
        simp only [Finset.mem_union] at hx
        constructor
        · intro h; rcases hx.mp (Or.inr h) with h' | h'
          · exact absurd (hA₂ h') (Finset.disjoint_right.mp hdisj (hB₁ h))
          · exact h'
        · intro h; rcases hx.mpr (Or.inr h) with h' | h'
          · exact absurd (hA₁ h') (Finset.disjoint_right.mp hdisj (hB₂ h))
          · exact h'
    rw [Finset.sum_image hinj]
    have hconst : ∀ AB ∈ S₀.powersetCard (S₀.card - d) ×ˢ R.powersetCard e,
        probWU p U (AB.1 ∪ AB.2) =
          (u ^ d * (1 - u) ^ (S₀.card - d)) * (v ^ e * (1 - v) ^ (R.card - e)) := by
      rintro ⟨A, B⟩ hAB
      rcases Finset.mem_powersetCard.mp (Finset.mem_product.mp hAB).1 with ⟨hAsub, hAcard⟩
      rcases Finset.mem_powersetCard.mp (Finset.mem_product.mp hAB).2 with ⟨hBsub, hBcard⟩
      rw [← hUeq, probWU_union_disjoint p hdisj hAsub hBsub]
      have h1 : probWU p S₀ A = (1 - u) ^ (S₀.card - d) * u ^ d := by
        unfold probWU
        have hpA : ∏ i ∈ A, p i = (1 - u) ^ (S₀.card - d) := by
          have hc : ∏ i ∈ A, p i = ∏ _i ∈ A, (1 - u) :=
            Finset.prod_congr rfl fun i hi => by simp only [p, hAsub hi, ↓reduceIte]
          rw [hc, Finset.prod_const, hAcard]
        have hpS : ∏ i ∈ S₀ \ A, (1 - p i) = u ^ d := by
          have hc : ∏ i ∈ S₀ \ A, (1 - p i) = ∏ _i ∈ S₀ \ A, u :=
            Finset.prod_congr rfl fun i hi => by
              simp only [p, (Finset.mem_sdiff.mp hi).1, ↓reduceIte]; ring
          rw [hc, Finset.prod_const, Finset.card_sdiff, Finset.inter_eq_left.mpr hAsub, hAcard,
            Nat.sub_sub_self hd.le]
        rw [hpA, hpS]
      have h2 : probWU p R B = v ^ e * (1 - v) ^ (R.card - e) := by
        unfold probWU
        have hpB : ∏ i ∈ B, p i = v ^ e := by
          have hc : ∏ i ∈ B, p i = ∏ _i ∈ B, v :=
            Finset.prod_congr rfl fun i hi => by
              have hnot : i ∉ S₀ := (Finset.mem_sdiff.mp (hBsub hi)).2
              simp only [p, hnot, ↓reduceIte]
          rw [hc, Finset.prod_const, hBcard]
        have hpR : ∏ i ∈ R \ B, (1 - p i) = (1 - v) ^ (R.card - e) := by
          have hc : ∏ i ∈ R \ B, (1 - p i) = ∏ _i ∈ R \ B, (1 - v) :=
            Finset.prod_congr rfl fun i hi => by
              have hnot : i ∉ S₀ := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hi).1).2
              simp only [p, hnot, ↓reduceIte]
          rw [hc, Finset.prod_const, Finset.card_sdiff, Finset.inter_eq_left.mpr hBsub, hBcard]
        rw [hpB, hpR]
      rw [h1, h2]; ring
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_product,
      Finset.card_powersetCard, Finset.card_powersetCard, nsmul_eq_mul,
      Nat.choose_symm hd.le]
    push_cast; ring
  have hmode1 := binom_mode_ge S₀.card d hd0 hd
  have hmode2 := binom_mode_ge R.card e he0 he
  have hS0_le : (S₀.card : ℝ) + 1 ≤ (U.card : ℝ) + 1 := by
    have : S₀.card ≤ U.card := Finset.card_le_card hS₀
    exact_mod_cast Nat.add_le_add_right this 1
  have hR_le : (R.card : ℝ) + 1 ≤ (U.card : ℝ) + 1 := by
    have : R.card ≤ U.card := Finset.card_le_card Finset.sdiff_subset
    exact_mod_cast Nat.add_le_add_right this 1
  have hb1 : 1 / ((U.card : ℝ) + 1) ≤ (S₀.card.choose d : ℝ) * u ^ d * (1 - u) ^ (S₀.card - d) :=
    (one_div_le_one_div_of_le (by positivity) hS0_le).trans hmode1
  have hb2 : 1 / ((U.card : ℝ) + 1) ≤ (R.card.choose e : ℝ) * v ^ e * (1 - v) ^ (R.card - e) :=
    (one_div_le_one_div_of_le (by positivity) hR_le).trans hmode2
  have hprod_ge : 1 / (((U.card : ℝ) + 1) ^ 2) ≤ ∑ S ∈ G, probWU p U S := by
    rw [hGsum]
    have hsq : 1 / (((U.card : ℝ) + 1) ^ 2) = (1 / ((U.card : ℝ) + 1)) * (1 / ((U.card : ℝ) + 1)) := by
      rw [one_div_mul_one_div, sq]
    rw [hsq]
    exact mul_le_mul hb1 hb2 (by positivity) (by positivity)
  exact hprod_ge.trans (Finset.sum_le_sum_of_subset_of_nonneg hGsub fun S _ _ => probWU_nonneg p hp0 hp1 U S)

end TwoOrbitPerturb

/-!
The polynomial-to-seed step for the Log-rank two-orbit detector.
The analytic existence input on the paper side is Balister, Bollobás, Morris,
Sahasrabudhe and Tiba, https://doi.org/10.4007/annals.2020.192.3.6 .
The lemmas here hold for every supplied sign sequence.
-/

namespace TwoOrbitFlatSeed
open Finset

def positives (sign : ℕ → Bool) (k : ℕ) : Finset ℕ :=
  (range (k+k)).filter (fun j => sign j = true)

noncomputable def series (s : Finset ℕ) (z : ℂ) : ℂ := ∑ j ∈ s, z^j

noncomputable def signedSum (sign : ℕ → Bool) (k : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ range (k+k), if sign j then z^j else -(z^j)

theorem splitInterval (k : ℕ) (z : ℂ) :
    series (range (k+k)) z = (1+z^k)*series (range k) z := by
  unfold series
  rw [Finset.sum_range_add, add_mul, one_mul, Finset.mul_sum]
  simp_rw [pow_add]

theorem signedIdentity (sign : ℕ → Bool) (k : ℕ) (z : ℂ) :
    signedSum sign k z = 2*series (positives sign k) z -
      (1+z^k)*series (range k) z := by
  rw [← splitInterval]
  unfold signedSum series positives
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases sign j <;> simp
  ring

/-- Converting signs to a set only adds a multiple of the prescribed interval. -/
theorem lowerEnvelope (sign : ℕ → Bool) (k : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖signedSum sign k z‖ ≤
      4 * max ‖series (positives sign k) z‖ ‖series (range k) z‖ := by
  have hfac : ‖1+z^k‖ ≤ 2 := by
    calc
      ‖1+z^k‖ ≤ ‖(1 : ℂ)‖ + ‖z^k‖ := norm_add_le _ _
      _ = 2 := by rw [norm_one, norm_pow, hz, one_pow]; norm_num
  rw [signedIdentity]
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_ofNat]
  have h := mul_le_mul_of_nonneg_right hfac (norm_nonneg (series (range k) z))
  linarith only [h, le_max_left ‖series (positives sign k) z‖ ‖series (range k) z‖,
    le_max_right ‖series (positives sign k) z‖ ‖series (range k) z‖]

/-- Flatness at the trivial character controls the error in the target weight. -/
theorem cardinalError (sign : ℕ → Bool) (k : ℕ) :
    ‖signedSum sign k 1‖ = 2 * |((positives sign k).card : ℝ) - k| := by
  rw [signedIdentity]
  have h (s : Finset ℕ) : series s 1 = (s.card : ℂ) := by simp [series]
  simp only [h, card_range, one_pow]
  have he : 2 * ((positives sign k).card : ℂ) - (1+1) * (k : ℂ) =
      (((2 * (((positives sign k).card : ℝ) - k) : ℝ)) : ℂ) := by push_cast; ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  norm_num

end TwoOrbitFlatSeed

namespace TwoOrbit

open Finset

/-- A maximal disjoint collection of translates covers every candidate shift
by difference sets, each with cardinality at most `A.card ^ 2`. -/
theorem disjointTranslatePacking {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) (hA : A.Nonempty) :
    ∃ T : Finset G, (T : Set G).Pairwise
      (fun t u => Disjoint (A.image (fun x => x + t)) (A.image (fun x => x + u))) ∧
      Fintype.card G ≤ T.card * A.card ^ 2 := by
  classical
  let trans (t : G) := A.image fun x => x + t
  let P (T : Finset G) := (T : Set G).Pairwise (fun t u => Disjoint (trans t) (trans u))
  let F := (Finset.univ : Finset G).powerset.filter P
  have hF : F.Nonempty := ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), by simp [P]⟩⟩
  obtain ⟨T, hT, hmax⟩ := F.exists_max_image Finset.card hF
  have hPair : P T := (mem_filter.mp hT).2
  refine ⟨T, hPair, ?_⟩
  have hmeet (u : G) : ∃ t ∈ T, ¬ Disjoint (trans t) (trans u) := by
    by_contra! hf
    have hu : u ∉ T := by
      intro hut
      obtain ⟨a, ha⟩ := hA
      have hmem : a + u ∈ trans u := mem_image.mpr ⟨a, ha, rfl⟩
      exact (Finset.disjoint_left.mp (hf u hut)) hmem hmem
    have hnew : P (insert u T) := by
      change ((insert u T : Finset G) : Set G).Pairwise _
      rw [Finset.coe_insert, Set.pairwise_insert_of_notMem (by simpa using hu)]
      exact ⟨hPair, fun t ht => ⟨(hf t ht).symm, hf t ht⟩⟩
    have hnewF : insert u T ∈ F := mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hnew⟩
    have hle := hmax (insert u T) hnewF
    rw [card_insert_of_notMem hu] at hle
    omega
  let blocked (t : G) : Finset G := (A ×ˢ A).image fun ab => ab.1 + t - ab.2
  have hcover : (Finset.univ : Finset G) ⊆ T.biUnion blocked := by
    intro u _
    obtain ⟨t, ht, htd⟩ := hmeet u
    rw [Finset.disjoint_left] at htd
    push Not at htd
    obtain ⟨x, hx, hx'⟩ := htd
    obtain ⟨a, ha, hax⟩ := mem_image.mp hx
    obtain ⟨b, hb, hbx⟩ := mem_image.mp hx'
    refine mem_biUnion.mpr ⟨t, ht, mem_image.mpr ⟨(a,b), mem_product.mpr ⟨ha,hb⟩, ?_⟩⟩
    change a + t - b = u
    calc
      _ = (b + u) - b := by rw [hax, hbx]
      _ = _ := by abel
  calc
    Fintype.card G = (Finset.univ : Finset G).card := Finset.card_univ.symm
    _ ≤ (T.biUnion blocked).card := Finset.card_le_card hcover
    _ ≤ ∑ t ∈ T, (blocked t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ T, A.card ^ 2 := by
      apply sum_le_sum
      intro t _
      exact (Finset.card_image_le).trans_eq (by rw [card_product, pow_two])
    _ = T.card * A.card ^ 2 := by simp

/-- In the cyclic set `Fin n`, a nonempty row has at least `n / |A|²`
available disjoint translates. -/
theorem finDisjointTranslatePacking {n : ℕ} (A : Finset (Fin n)) (hA : A.Nonempty) :
    ∃ T : Finset (Fin n), (T : Set (Fin n)).Pairwise
      (fun t u => Disjoint (A.image (fun x => x + t)) (A.image (fun x => x + u))) ∧
      n ≤ T.card * A.card ^ 2 := by
  have hn : 0 < n := by
    obtain ⟨a, _⟩ := hA
    exact a.pos
  let _ : NeZero n := ⟨hn.ne'⟩
  simpa only [Fintype.card_fin] using disjointTranslatePacking A hA

end TwoOrbit

/-!
# Middle-row spectral reduction for the two-orbit log-rank detector

The finite Fourier transform, Parseval, and the variance bound for an adjacent-valued
intersection profile are adapted from the project's Apache-2.0 cyclic detector proof:
https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/1133bda2e6/lean/PEqualNP/Outside/L_log_rank_cyclic_detector_family.lean
The two-seed lower bound is used below without assuming the seeds have equal cardinality.
-/

namespace TwoOrbitMiddle
open scoped BigOperators ComplexConjugate
open Finset

noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private lemma phase_zero : phase 0 = 1 := by
  simp [phase]

private lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma phase_neg (x : ℝ) : phase (-x) = conj (phase x) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private lemma phase_nat (m : ℕ) : phase (m : ℝ) = 1 := by
  unfold phase
  have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
      (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

private lemma phase_pow (x : ℝ) (m : ℕ) : phase x ^ m = phase ((m : ℝ) * x) := by
  induction m with
  | zero => simp [phase_zero]
  | succ m ih =>
    rw [pow_succ, ih, ← phase_add]
    congr 1
    push_cast
    ring

lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  unfold phase
  exact Complex.norm_exp_ofReal_mul_I _

private lemma phase_re (x : ℝ) : (phase x).re = Real.cos (2 * Real.pi * x) := by
  unfold phase
  exact Complex.exp_ofReal_mul_I_re _

private lemma phase_im (x : ℝ) : (phase x).im = Real.sin (2 * Real.pi * x) := by
  unfold phase
  exact Complex.exp_ofReal_mul_I_im _

private lemma sq_norm_phase_sub_one (x : ℝ) :
    ‖phase x - 1‖ ^ 2 = 4 * Real.sin (Real.pi * x) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero,
    phase_re, phase_im]
  have hcs := Real.sin_sq_add_cos_sq (2 * Real.pi * x)
  have hcs1 := Real.sin_sq_add_cos_sq (Real.pi * x)
  have hcos : Real.cos (2 * Real.pi * x) = 1 - 2 * Real.sin (Real.pi * x) ^ 2 := by
    have h2 : 2 * Real.pi * x = 2 * (Real.pi * x) := by ring
    rw [h2, Real.cos_two_mul]
    nlinarith
  nlinarith

private lemma norm_phase_sub_one_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    4 * x ≤ ‖phase x - 1‖ := by
  have hpi_nonneg : 0 ≤ Real.pi * x := by positivity
  have hpi_le : Real.pi * x ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hsin_ge : 2 * x ≤ Real.sin (Real.pi * x) := by
    have h := Real.mul_le_sin hpi_nonneg hpi_le
    have hcancel : 2 / Real.pi * (Real.pi * x) = 2 * x := by
      field_simp [ne_of_gt Real.pi_pos]
    linarith
  have hsq : (4 * x) ^ 2 ≤ ‖phase x - 1‖ ^ 2 := by
    rw [sq_norm_phase_sub_one]
    nlinarith [hsin_ge, hx0]
  nlinarith [norm_nonneg (phase x - 1), hx0]

/-! ### Section 2: Finite Fourier transform and weighted spectral detection on `Fin n` -/

noncomputable def chi (n : ℕ) (ξ x : Fin n) : ℂ :=
  phase (((ξ.val * x.val : ℕ) : ℝ) / (n : ℝ))

private lemma chi_comm (n : ℕ) (ξ x : Fin n) : chi n ξ x = chi n x ξ := by
  simp [chi, Nat.mul_comm]

private lemma chi_zero_left (n : ℕ) [NeZero n] (x : Fin n) : chi n 0 x = 1 := by
  simp [chi, phase_zero]

lemma norm_chi (n : ℕ) (ξ x : Fin n) : ‖chi n ξ x‖ = 1 :=
  norm_phase _

private lemma chi_add_right {n : ℕ} [NeZero n] (ξ x y : Fin n) :
    chi n ξ (x + y) = chi n ξ x * chi n ξ y := by
  unfold chi
  rw [← phase_add]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  set q := (x.val + y.val) / n
  have hmod : (x + y).val = (x.val + y.val) % n := rfl
  have hdiv : x.val + y.val = n * q + (x + y).val := by
    rw [hmod]
    exact (Nat.div_add_mod (x.val + y.val) n).symm
  have hnat : ξ.val * x.val + ξ.val * y.val = ξ.val * (x + y).val + n * (ξ.val * q) := by
    calc
      ξ.val * x.val + ξ.val * y.val = ξ.val * (x.val + y.val) := by ring
      _ = ξ.val * (n * q + (x + y).val) := by rw [hdiv]
      _ = ξ.val * (x + y).val + n * (ξ.val * q) := by ring
  have harg :
      ((ξ.val * x.val : ℕ) : ℝ) / (n : ℝ) + ((ξ.val * y.val : ℕ) : ℝ) / (n : ℝ) =
      ((ξ.val * (x + y).val : ℕ) : ℝ) / (n : ℝ) + ((ξ.val * q : ℕ) : ℝ) := by
    have hcast : ((ξ.val * x.val : ℕ) : ℝ) + ((ξ.val * y.val : ℕ) : ℝ) =
        ((ξ.val * (x + y).val : ℕ) : ℝ) + (n : ℝ) * ((ξ.val * q : ℕ) : ℝ) := by
      exact_mod_cast hnat
    field_simp [hn]
    linarith
  rw [harg, phase_add, phase_nat, mul_one]

private lemma chi_sub_right {n : ℕ} [NeZero n] (ξ x y : Fin n) :
    chi n ξ (x - y) = chi n ξ x * conj (chi n ξ y) := by
  have h1 : chi n ξ ((x - y) + y) = chi n ξ (x - y) * chi n ξ y := chi_add_right ξ (x - y) y
  rw [sub_add_cancel] at h1
  have hmul : chi n ξ y * conj (chi n ξ y) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_chi]
    norm_num
  calc
    chi n ξ (x - y) = chi n ξ (x - y) * (chi n ξ y * conj (chi n ξ y)) := by rw [hmul, mul_one]
    _ = (chi n ξ (x - y) * chi n ξ y) * conj (chi n ξ y) := by ring
    _ = chi n ξ x * conj (chi n ξ y) := by rw [h1]

lemma chi_eq_pow {n : ℕ} (ξ x : Fin n) :
    chi n ξ x = phase ((ξ.val : ℝ) / (n : ℝ)) ^ x.val := by
  rw [chi, phase_pow]
  congr 1
  push_cast
  ring

private lemma phase_div_ne_one {n m : ℕ} (hm0 : 0 < m) (hmn : m < n) :
    phase ((m : ℝ) / (n : ℝ)) ≠ 1 := by
  intro heq
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_trans hm0 hmn
  by_cases hhalf : 2 * m ≤ n
  · have hge := norm_phase_sub_one_ge (x := (m : ℝ) / (n : ℝ)) (by positivity)
      (by
        rw [div_le_iff₀ hn]
        have : (2 : ℝ) * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hhalf
        linarith)
    rw [heq, sub_self, norm_zero] at hge
    have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
    have : 0 < 4 * ((m : ℝ) / (n : ℝ)) := by positivity
    linarith
  · have hcomp0 : 0 < n - m := by omega
    have hcomp2 : 2 * (n - m) ≤ n := by omega
    have hge := norm_phase_sub_one_ge (x := ((n - m : ℕ) : ℝ) / (n : ℝ)) (by positivity)
      (by
        rw [div_le_iff₀ hn]
        have : (2 : ℝ) * ((n - m : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcomp2
        linarith)
    have hphase_eq : phase (((n - m : ℕ) : ℝ) / (n : ℝ)) = conj (phase ((m : ℝ) / (n : ℝ))) := by
      have harg : (((n - m : ℕ) : ℝ) / (n : ℝ)) = (1 : ℝ) + (-((m : ℝ) / (n : ℝ))) := by
        rw [Nat.cast_sub (le_of_lt hmn)]
        field_simp [ne_of_gt hn]
        ring
      rw [harg, phase_add, show phase (1 : ℝ) = 1 from by simpa using phase_nat 1, one_mul,
        phase_neg]
    rw [hphase_eq, heq, map_one, sub_self, norm_zero] at hge
    have hc' : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by exact_mod_cast hcomp0
    have : 0 < 4 * (((n - m : ℕ) : ℝ) / (n : ℝ)) := by positivity
    linarith

lemma sum_chi_right {n : ℕ} [NeZero n] (ξ : Fin n) :
    ∑ x : Fin n, chi n ξ x = if ξ = 0 then (n : ℂ) else 0 := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp [chi_zero_left]
  · simp only [hξ, ↓reduceIte]
    have hpos : 0 < ξ.val := Nat.pos_of_ne_zero (fun h => hξ (Fin.ext h))
    have hz1 : phase ((ξ.val : ℝ) / (n : ℝ)) ≠ 1 := phase_div_ne_one hpos ξ.isLt
    have hsum : ∑ x : Fin n, chi n ξ x =
        ∑ j ∈ Finset.range n, phase ((ξ.val : ℝ) / (n : ℝ)) ^ j := by
      calc
        ∑ x : Fin n, chi n ξ x = ∑ x : Fin n, phase ((ξ.val : ℝ) / (n : ℝ)) ^ x.val :=
          Finset.sum_congr rfl fun x _ => chi_eq_pow ξ x
        _ = ∑ j ∈ Finset.range n, phase ((ξ.val : ℝ) / (n : ℝ)) ^ j :=
          Fin.sum_univ_eq_sum_range (fun j => phase ((ξ.val : ℝ) / (n : ℝ)) ^ j) n
    rw [hsum, geom_sum_eq hz1, phase_pow]
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    have hmul : (n : ℝ) * ((ξ.val : ℝ) / (n : ℝ)) = (ξ.val : ℝ) := mul_div_cancel₀ _ hn
    rw [hmul, phase_nat, sub_self, zero_div]

noncomputable def hat (n : ℕ) (f : Fin n → ℂ) (ξ : Fin n) : ℂ :=
  ∑ x : Fin n, f x * chi n ξ x

noncomputable def hatSet (n : ℕ) (S : Finset (Fin n)) (ξ : Fin n) : ℂ :=
  ∑ x ∈ S, chi n ξ x

private lemma hatSet_eq_hat (n : ℕ) (S : Finset (Fin n)) (ξ : Fin n) :
    hatSet n S ξ = hat n (fun x => if x ∈ S then 1 else 0) ξ := by
  unfold hatSet hat
  have hpt : ∀ x : Fin n, (if x ∈ S then (1 : ℂ) else 0) * chi n ξ x =
      if x ∈ S then chi n ξ x else 0 := by
    intro x
    split_ifs <;> simp
  simp_rw [hpt, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp

private lemma parseval (n : ℕ) [NeZero n] (f : Fin n → ℂ) :
    ∑ ξ : Fin n, ‖hat n f ξ‖ ^ 2 = (n : ℝ) * ∑ x : Fin n, ‖f x‖ ^ 2 := by
  have hterm (z : ℂ) : ((‖z‖ : ℂ) ^ 2) = z * conj z := by
    rw [← Complex.ofReal_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hc : ((∑ ξ : Fin n, ‖hat n f ξ‖ ^ 2 : ℝ) : ℂ) =
      (((n : ℝ) * ∑ x : Fin n, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    simp_rw [hterm]
    calc
      ∑ ξ : Fin n, hat n f ξ * conj (hat n f ξ)
        = ∑ ξ : Fin n, ∑ x : Fin n, ∑ y : Fin n,
            f x * chi n ξ x * (conj (f y) * conj (chi n ξ y)) := by
          refine Finset.sum_congr rfl fun ξ _ => ?_
          unfold hat
          rw [map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => by rw [map_mul]
      _ = ∑ x : Fin n, ∑ y : Fin n, f x * conj (f y) * ∑ ξ : Fin n, chi n (x - y) ξ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ξ _ => ?_
          rw [chi_comm n (x - y) ξ, chi_sub_right]
          ring
      _ = (n : ℂ) * ∑ x : Fin n, f x * conj (f x) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_eq_single x]
          · simp [sum_chi_right]; ring
          · intro y _ hyx
            have hne : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyx)
            simp [sum_chi_right, hne]
          · intro hx
            exact absurd (Finset.mem_univ x) hx
  exact Complex.ofReal_inj.mp hc

private lemma parseval_set (n : ℕ) [NeZero n] (A : Finset (Fin n)) :
    ∑ ξ ∈ Finset.univ.erase (0 : Fin n), ‖hatSet n A ξ‖ ^ 2 =
      (A.card : ℝ) * ((n : ℝ) - (A.card : ℝ)) := by
  have hp := parseval n (fun x => if x ∈ A then (1 : ℂ) else 0)
  have hlhs : ∑ ξ : Fin n, ‖hat n (fun x => if x ∈ A then (1 : ℂ) else 0) ξ‖ ^ 2 =
      ‖hatSet n A 0‖ ^ 2 + ∑ ξ ∈ Finset.univ.erase (0 : Fin n), ‖hatSet n A ξ‖ ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin n))]
    congr 1
    · rw [hatSet_eq_hat]
    · refine Finset.sum_congr rfl fun ξ _ => by rw [hatSet_eq_hat]
  have h0 : ‖hatSet n A 0‖ ^ 2 = (A.card : ℝ) ^ 2 := by
    unfold hatSet
    simp only [chi_zero_left, Finset.sum_const, nsmul_eq_mul, mul_one, Complex.norm_natCast]
  have hrhs : ∑ x : Fin n, ‖(if x ∈ A then (1 : ℂ) else 0)‖ ^ 2 = (A.card : ℝ) := by
    have : ∀ x : Fin n, ‖(if x ∈ A then (1 : ℂ) else 0)‖ ^ 2 = if x ∈ A then (1 : ℝ) else 0 := by
      intro x; split_ifs <;> simp
    simp_rw [this, Finset.sum_boole]
    simp
  rw [hlhs, h0, hrhs] at hp
  nlinarith

private lemma hat_inter_shift {n : ℕ} [NeZero n] (A S : Finset (Fin n)) (ξ : Fin n) :
    hat n (fun t => ((A ∩ S.image (fun i => i + t)).card : ℂ)) ξ =
      hatSet n A ξ * conj (hatSet n S ξ) := by
  have hcard (t : Fin n) :
      ((A ∩ S.image (fun i => i + t)).card : ℂ) =
        ∑ x ∈ A, ∑ y ∈ S, if y + t = x then (1 : ℂ) else 0 := by
    have hinj : ∀ x ∈ A, (∑ y ∈ S, if y + t = x then (1 : ℂ) else 0) =
        if x ∈ S.image (fun i => i + t) then 1 else 0 := by
      intro x _
      by_cases hx : x ∈ S.image (fun i => i + t)
      · rw [ite_eq_left hx]
        obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hx
        rw [Finset.sum_eq_single y₀]
        · simp
        · intro y _ hne
          have : y + t ≠ y₀ + t := fun h => hne (add_right_cancel h)
          simp [this]
        · intro h
          exact absurd hy₀ h
      · rw [ite_eq_right hx]
        refine Finset.sum_eq_zero fun y hy => ?_
        have : y + t ≠ x := fun h => hx (Finset.mem_image.mpr ⟨y, hy, h⟩)
        simp [this]
    rw [Finset.sum_congr rfl hinj]
    have hfilt : (∑ x ∈ A, if x ∈ S.image (fun i => i + t) then (1 : ℂ) else 0) =
        ((A.filter (fun x => x ∈ S.image (fun i => i + t))).card : ℂ) := by
      rw [Finset.sum_boole]
    rw [hfilt, Finset.filter_mem_eq_inter]
  unfold hat
  simp_rw [hcard, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h1 :
      ∑ x ∈ A, ∑ t : Fin n, ∑ y ∈ S, (if y + t = x then (1 : ℂ) else 0) * chi n ξ t =
      ∑ x ∈ A, ∑ y ∈ S, chi n ξ x * conj (chi n ξ y) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single (x - y)]
    · rw [add_sub_cancel, ite_eq_left rfl, one_mul, chi_sub_right]
    · intro t _ ht
      have hne : y + t ≠ x := fun h => ht (eq_sub_of_add_eq' h)
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h1]
  unfold hatSet
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]

private lemma orbit_variance_le_quarter {n : ℕ} [NeZero n] (A S : Finset (Fin n)) (a : ℤ)
    (hadj : ∀ t : Fin n,
      ((A ∩ S.image (fun i => i + t)).card : ℤ) = a ∨
      ((A ∩ S.image (fun i => i + t)).card : ℤ) = a + 1) :
    ∑ ξ ∈ Finset.univ.erase (0 : Fin n), ‖hatSet n A ξ‖ ^ 2 * ‖hatSet n S ξ‖ ^ 2 ≤
      (n : ℝ) ^ 2 / 4 := by
  let v : Fin n → ℝ := fun t => ((A ∩ S.image (fun i => i + t)).card : ℝ)
  let g : Fin n → ℂ := fun t => (v t : ℂ)
  have h0 : hat n g 0 = ((A.card * S.card : ℕ) : ℂ) := by
    have hg := hat_inter_shift A S 0
    simp only [hatSet, chi_zero_left, Finset.sum_const, nsmul_eq_mul, mul_one, map_natCast] at hg
    simpa [g, v] using hg
  have hsum_v : ∑ t : Fin n, v t = (A.card : ℝ) * (S.card : ℝ) := by
    have hre := congrArg Complex.re h0
    simp only [hat, g, chi_zero_left, mul_one, Complex.re_sum, Complex.ofReal_re,
      Nat.cast_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero,
      sub_zero] at hre
    exact hre
  have hp := parseval n g
  have hsplit : ∑ ξ : Fin n, ‖hat n g ξ‖ ^ 2 =
      ‖hat n g 0‖ ^ 2 +
        ∑ ξ ∈ Finset.univ.erase (0 : Fin n), ‖hatSet n A ξ‖ ^ 2 * ‖hatSet n S ξ‖ ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin n))]
    congr 1
    refine Finset.sum_congr rfl fun ξ _ => ?_
    have hg : hat n g ξ = hatSet n A ξ * conj (hatSet n S ξ) := by
      simpa [g, v] using hat_inter_shift A S ξ
    rw [hg, norm_mul, Complex.norm_conj, mul_pow]
  have hnorm0 : ‖hat n g 0‖ ^ 2 = ((A.card : ℝ) * (S.card : ℝ)) ^ 2 := by
    rw [h0, Complex.norm_natCast, Nat.cast_mul]
  have hnorm_g : ∑ t : Fin n, ‖g t‖ ^ 2 = ∑ t : Fin n, (v t) ^ 2 := by
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [g, Real.norm_eq_abs, sq_abs]
  rw [hsplit, hnorm0, hnorm_g] at hp
  have hquarter : ∑ t : Fin n, (v t - ((a : ℝ) + 1 / 2)) ^ 2 = (n : ℝ) / 4 := by
    have hpt : ∀ t : Fin n, (v t - ((a : ℝ) + 1 / 2)) ^ 2 = 1 / 4 := by
      intro t
      rcases hadj t with h | h
      · have hr : v t = (a : ℝ) := by
          dsimp only [v]
          exact_mod_cast h
        rw [hr]; ring
      · have hr : v t = (a : ℝ) + 1 := by
          dsimp only [v]
          have : ((A ∩ S.image (fun i => i + t)).card : ℝ) = ((a + 1 : ℤ) : ℝ) := by
            exact_mod_cast h
          simpa using this
        rw [hr]; ring
    simp_rw [hpt]
    simp [div_eq_mul_inv]
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  let μ : ℝ := ((A.card : ℝ) * (S.card : ℝ)) / (n : ℝ)
  have hvar_eq : ∑ t : Fin n, (v t - ((a : ℝ) + 1 / 2)) ^ 2 =
      (∑ t : Fin n, (v t) ^ 2) - 2 * ((a : ℝ) + 1 / 2) * (∑ t : Fin n, v t) +
        (n : ℝ) * ((a : ℝ) + 1 / 2) ^ 2 := by
    have hexp : ∀ t : Fin n, (v t - ((a : ℝ) + 1 / 2)) ^ 2 =
        (v t) ^ 2 - 2 * ((a : ℝ) + 1 / 2) * v t + ((a : ℝ) + 1 / 2) ^ 2 := fun t => by ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdiff_nonneg : 0 ≤ (n : ℝ) * ((n : ℝ) * (μ - ((a : ℝ) + 1 / 2)) ^ 2) := by positivity
  have hstep : (n : ℝ) * (∑ t : Fin n, (v t) ^ 2) - ((A.card : ℝ) * (S.card : ℝ)) ^ 2 ≤
      (n : ℝ) ^ 2 / 4 := by
    have hcalc : (n : ℝ) * (∑ t : Fin n, (v t) ^ 2) - ((A.card : ℝ) * (S.card : ℝ)) ^ 2 =
        (n : ℝ) * (∑ t : Fin n, (v t - ((a : ℝ) + 1 / 2)) ^ 2) -
          (n : ℝ) * ((n : ℝ) * (μ - ((a : ℝ) + 1 / 2)) ^ 2) := by
      rw [hvar_eq, hsum_v]
      dsimp only [μ]
      field_simp [ne_of_gt hn_pos]
      ring
    rw [hcalc, hquarter]
    linarith [hdiff_nonneg]
  linarith

/-- A joint Fourier floor detects an individual row when the row has sufficient energy.
    The conclusion identifies an actual cyclic shift of one seed. -/
theorem detects_mid_row {n : ℕ} [NeZero n] (A I S : Finset (Fin n)) (c : ℝ)
    (hspec : ∀ ξ : Fin n, ξ ≠ 0 →
      c * (n : ℝ) ≤ ‖hatSet n I ξ‖ ^ 2 + ‖hatSet n S ξ‖ ^ 2)
    (hsize : (n : ℝ) / 2 < c * (A.card : ℝ) * ((n : ℝ) - A.card))
    (a : ℤ) :
    ∃ t : Fin n,
      ¬ (((A ∩ I.image (fun i => i + t)).card : ℤ) = a ∨
        ((A ∩ I.image (fun i => i + t)).card : ℤ) = a + 1) ∨
      ¬ (((A ∩ S.image (fun i => i + t)).card : ℤ) = a ∨
        ((A ∩ S.image (fun i => i + t)).card : ℤ) = a + 1) := by
  by_contra hnone
  push Not at hnone
  have hI := orbit_variance_le_quarter A I a (fun t => (hnone t).1)
  have hS := orbit_variance_le_quarter A S a (fun t => (hnone t).2)
  have hUpper : ∑ ξ ∈ Finset.univ.erase (0 : Fin n),
      ‖hatSet n A ξ‖ ^ 2 * (‖hatSet n I ξ‖ ^ 2 + ‖hatSet n S ξ‖ ^ 2) ≤
        (n : ℝ) ^ 2 / 2 := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    linarith only [hI, hS]
  have hLower : (c * (n : ℝ)) * ((A.card : ℝ) * ((n : ℝ) - A.card)) ≤
      ∑ ξ ∈ Finset.univ.erase (0 : Fin n),
        ‖hatSet n A ξ‖ ^ 2 * (‖hatSet n I ξ‖ ^ 2 + ‖hatSet n S ξ‖ ^ 2) := by
    rw [← parseval_set, Finset.mul_sum]
    refine Finset.sum_le_sum fun ξ hξ => ?_
    rw [mul_comm (c * (n : ℝ))]
    exact mul_le_mul_of_nonneg_left (hspec ξ (Finset.mem_erase.mp hξ).1) (sq_nonneg _)
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  have hstrict : (n : ℝ) ^ 2 / 2 < (c * (n : ℝ)) * ((A.card : ℝ) * ((n : ℝ) - A.card)) := by
    calc
      _ = (n : ℝ) / 2 * (n : ℝ) := by ring
      _ < (c * (A.card : ℝ) * ((n : ℝ) - A.card)) * (n : ℝ) :=
        mul_lt_mul_of_pos_right hsize hn
      _ = _ := by ring
  exact (not_lt_of_ge (hLower.trans hUpper)) hstrict

/-- Version of the spectral reduction stated directly for the union of the two orbits. -/
theorem detects_mid_row_of_orbit_union {n : ℕ} [NeZero n] (A I S : Finset (Fin n)) (c : ℝ)
    (hspec : ∀ ξ : Fin n, ξ ≠ 0 →
      c * (n : ℝ) ≤ ‖hatSet n I ξ‖ ^ 2 + ‖hatSet n S ξ‖ ^ 2)
    (hsize : (n : ℝ) / 2 < c * (A.card : ℝ) * ((n : ℝ) - A.card))
    (a : ℤ) :
    let orbit := fun (T : Finset (Fin n)) =>
      (Finset.univ : Finset (Fin n)).image (fun t => T.image (fun i => i + t))
    ∃ B ∈ orbit I ∪ orbit S,
      ¬ (((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a + 1) := by
  intro orbit
  obtain ⟨t, h | h⟩ := detects_mid_row A I S c hspec hsize a
  · exact ⟨_, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩), h⟩
  · exact ⟨_, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩), h⟩

end TwoOrbitMiddle



namespace TwoOrbitCertificate

private def adjacent {α : Type*} [DecidableEq α] (A B : Finset α) (a : ℤ) : Prop :=
  ((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a + 1

/-- A wholly missed small row and a wholly covered small row have intersection
counts separated by at least two. Uniform column size transfers the gap to its complement. -/
theorem detects_of_miss_and_cover {α : Type*} [Fintype α] [DecidableEq α]
    (Y : Finset (Finset α)) (A : Finset α) (k : ℕ)
    (hk : ∀ B ∈ Y, B.card = k) (hA : 2 ≤ A.card)
    (hmiss : ∃ B ∈ Y, Disjoint A B) (hcover : ∃ B ∈ Y, A ⊆ B)
    (a : ℤ) :
    (∃ B ∈ Y, ¬ adjacent A B a) ∧ (∃ B ∈ Y, ¬ adjacent Aᶜ B a) := by
  obtain ⟨D, hD, hdisj⟩ := hmiss
  obtain ⟨C, hC, hsub⟩ := hcover
  have hd : (A ∩ D).card = 0 := by
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.card_empty]
  have hc : (A ∩ C).card = A.card := by
    congr 1
    ext z
    exact ⟨fun h => (Finset.mem_inter.mp h).1, fun h => Finset.mem_inter.mpr ⟨h,hsub h⟩⟩
  have hpart (B : Finset α) : (Aᶜ ∩ B).card + (A ∩ B).card = B.card := by
    have heq : Aᶜ ∩ B = B \ A := by
      ext z
      simp [and_comm]
    rw [heq, Finset.inter_comm A B]
    exact Finset.card_sdiff_add_card_inter B A
  have hd' : (Aᶜ ∩ D).card = k := by simpa [hd, hk D hD] using hpart D
  have hc' : (Aᶜ ∩ C).card + A.card = k := by simpa [hc, hk C hC] using hpart C
  constructor
  · by_contra! h
    have hD' := h D hD
    have hC' := h C hC
    unfold adjacent at hD' hC'
    rcases hD' with hD' | hD' <;> rcases hC' with hC' | hC' <;> omega
  · by_contra! h
    have hD' := h D hD
    have hC' := h C hC
    unfold adjacent at hD' hC'
    rcases hD' with hD' | hD' <;> rcases hC' with hC' | hC' <;> omega

/-- A uniform family with both a missing and a covering column for each small
row detects every row whose size or complement size is in the small range. -/
theorem detects_small_rows_or_complements {α : Type*} [Fintype α] [DecidableEq α]
    (Y : Finset (Finset α)) (k M : ℕ)
    (hk : ∀ B ∈ Y, B.card = k)
    (hw : ∀ A : Finset α, 2 ≤ A.card → A.card ≤ M →
      (∃ B ∈ Y, Disjoint A B) ∧ (∃ B ∈ Y, A ⊆ B)) :
    ∀ (A : Finset α), (2 ≤ A.card ∧ A.card ≤ M) ∨ (2 ≤ Aᶜ.card ∧ Aᶜ.card ≤ M) →
      ∀ a : ℤ, ∃ B ∈ Y,
        ¬ (((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a + 1) := by
  intro A hA a
  rcases hA with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · obtain ⟨hd, hc⟩ := hw A hlo hhi
    exact (detects_of_miss_and_cover Y A k hk hlo hd hc a).1
  · obtain ⟨hd, hc⟩ := hw Aᶜ hlo hhi
    simpa only [compl_compl, adjacent] using (detects_of_miss_and_cover Y Aᶜ k hk hlo hd hc a).2

end TwoOrbitCertificate


namespace TwoOrbitMiddle

/-- A seed that detects small rows by disjointness and containment, and has a joint
    Fourier floor with the interval, detects every interior row uniformly. -/
theorem detector_from_seed_family
    (hSeeds : ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∃ K : ℕ,
      ∀ k : ℕ, K ≤ k → 2 ≤ k →
      let n := 3*k+1
      let I := (Finset.univ : Finset (Fin n)).filter (fun i => i.val < k)
      ∃ S : Finset (Fin n), S.card = k ∧
        (∀ ξ : Fin n, ξ.val ≠ 0 →
          c * (n : ℝ) ≤ ‖hatSet n I ξ‖ ^ 2 + ‖hatSet n S ξ‖ ^ 2) ∧
        (∀ A : Finset (Fin n), 2 ≤ A.card → A.card ≤ M →
          (∃ t : Fin n, Disjoint A (S.image (fun i => i + t))) ∧
          (∃ t : Fin n, A ⊆ S.image (fun i => i + t)))) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 2 ≤ k →
      let n := 3*k+1
      let adj := fun (A B : Finset (Fin n)) (a : ℤ) =>
        ((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a+1
      let detects := fun (Y : Finset (Finset (Fin n))) =>
        ∀ A : Finset (Fin n), 2 ≤ A.card → A.card + 2 ≤ n →
          ∀ a : ℤ, ∃ B ∈ Y, ¬ adj A B a
      let shift := fun (S : Finset (Fin n)) (t : Fin n) => S.image (fun i => i+t)
      let orbit := fun (S : Finset (Fin n)) => (Finset.univ : Finset (Fin n)).image (shift S)
      let I := (Finset.univ : Finset (Fin n)).filter (fun i => i.val < k)
      ∃ S : Finset (Fin n), S.card = k ∧ detects (orbit I ∪ orbit S) := by
  classical
  rcases hSeeds with ⟨c, hc, hSeeds⟩
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / c)
  have hcM : 1 < c * (M : ℝ) := by
    rw [mul_comm]
    exact (div_lt_iff₀ hc).mp hM
  obtain ⟨K,hK⟩ := hSeeds M
  refine ⟨K, ?_⟩
  intro k hk hk2 n adj detects shift orbit I
  let _ : NeZero n := ⟨by dsimp [n]; omega⟩
  obtain ⟨S,hS,hSpec,hSparse⟩ := hK k hk hk2
  have hMap : I.map Fin.valEmbedding = Finset.range k := by
    ext j
    simp only [Finset.mem_map, Fin.valEmbedding_apply, I, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hj
      exact ⟨⟨j, by dsimp [n]; omega⟩, hj, rfl⟩
  have hI : I.card = k := by simpa using congrArg Finset.card hMap
  have hOrb (T : Finset (Fin n)) (t : Fin n) : shift T t ∈ orbit T :=
    Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  have hCardOrb (T : Finset (Fin n)) {B : Finset (Fin n)} (hB : B ∈ orbit T) :
      B.card = T.card := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hB
    exact Finset.card_image_of_injective _ (add_left_injective t)
  refine ⟨S,hS,?_⟩
  intro A hA hAn a
  have hSumNat : Aᶜ.card + A.card = n := by
    have hle : A.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ A
    rw [Finset.card_compl, Fintype.card_fin, Nat.sub_add_cancel hle]
  have hComplement : 2 ≤ Aᶜ.card := by omega
  by_cases hSmall : A.card ≤ M ∨ Aᶜ.card ≤ M
  · apply TwoOrbitCertificate.detects_small_rows_or_complements (orbit I ∪ orbit S) k M
    · intro B hB
      rcases Finset.mem_union.mp hB with hi | hs
      · exact (hCardOrb I hi).trans hI
      · exact (hCardOrb S hs).trans hS
    · intro T ht htm
      obtain ⟨⟨t0,ht0⟩,⟨t1,ht1⟩⟩ := hSparse T ht htm
      exact ⟨⟨_,Finset.mem_union_right _ (hOrb S t0),ht0⟩,
        ⟨_,Finset.mem_union_right _ (hOrb S t1),ht1⟩⟩
    · rcases hSmall with hm | hm
      · exact Or.inl ⟨hA,hm⟩
      · exact Or.inr ⟨hComplement,hm⟩
  · push Not at hSmall
    have hSumReal : (Aᶜ.card : ℝ) + (A.card : ℝ) = (n : ℝ) := by exact_mod_cast hSumNat
    have hSpec' (ξ : Fin n) (hξ : ξ ≠ 0) :
        c * (n : ℝ) ≤ ‖hatSet n I ξ‖ ^ 2 + ‖hatSet n S ξ‖ ^ 2 :=
      hSpec ξ (fun hzero => hξ (Fin.ext (by simpa using hzero)))
    exact detects_mid_row_of_orbit_union A I S c hSpec' (by
      have hapos : 0 < (A.card : ℝ) := by exact_mod_cast (show 0 < A.card by omega)
      have hcpos : 0 < (Aᶜ.card : ℝ) := by exact_mod_cast (show 0 < Aᶜ.card by omega)
      have hEq : (n : ℝ) - A.card = (Aᶜ.card : ℝ) := by linarith
      rw [hEq]
      by_cases hHalf : (A.card : ℝ) ≤ (n : ℝ) / 2
      · have hMcast : (M : ℝ) ≤ A.card := by exact_mod_cast hSmall.1.le
        have hh := hcM.trans_le (mul_le_mul_of_nonneg_left hMcast hc.le)
        have hm := mul_lt_mul_of_pos_right hh hcpos
        linarith only [hm, hHalf, hSumReal]
      · have hMcast : (M : ℝ) ≤ Aᶜ.card := by exact_mod_cast hSmall.2.le
        have hh := hcM.trans_le (mul_le_mul_of_nonneg_left hMcast hc.le)
        have hm := mul_lt_mul_of_pos_right hh hapos
        have hm' : (A.card : ℝ) < c * (A.card : ℝ) * (Aᶜ.card : ℝ) := by
          simpa only [one_mul, mul_right_comm] using hm
        linarith only [hm', hHalf]) a

end TwoOrbitMiddle

namespace TwoOrbitBridge

open scoped BigOperators ComplexConjugate
open Finset

/-! ### Bridge A: Discrete flat Littlewood initial seed -/

private lemma cosPoly_foldAngle (t : ℕ) (θ : ℝ) :
    TwoOrbitCosine.cosPoly t (TwoOrbitFejer.foldAngle θ) = TwoOrbitCosine.cosPoly t θ := by
  by_cases h1 : θ ≤ Real.pi / 2
  · simp only [TwoOrbitFejer.foldAngle, h1, ↓reduceIte]
  · by_cases h2 : θ ≤ Real.pi
    · simp only [TwoOrbitFejer.foldAngle, h1, h2, ↓reduceIte]
      exact TwoOrbitCosine.cosPoly_symm_pi_sub t θ
    · by_cases h3 : θ ≤ 3 * Real.pi / 2
      · simp only [TwoOrbitFejer.foldAngle, h1, h2, h3, ↓reduceIte]
        have h : θ = Real.pi + (θ - Real.pi) := by ring
        conv_rhs => rw [h]
        exact (TwoOrbitCosine.cosPoly_symm_pi_add t (θ - Real.pi)).symm
      · simp only [TwoOrbitFejer.foldAngle, h1, h2, h3, ↓reduceIte]
        have h : 2 * Real.pi - θ = Real.pi + (Real.pi - θ) := by ring
        rw [h, TwoOrbitCosine.cosPoly_symm_pi_add, TwoOrbitCosine.cosPoly_symm_pi_sub]

private lemma symm_exp_pair (a : ℝ) (d : ℕ) (θ : ℝ) :
    (a : ℂ) * Complex.exp (((d : ℕ) : ℝ) * θ * Complex.I) +
    (a : ℂ) * Complex.exp (-(((d : ℕ) : ℝ) * θ * Complex.I)) =
    ((2 * a * Real.cos ((d : ℝ) * θ) : ℝ) : ℂ) := by
  have h1 : (((d : ℕ) : ℝ) : ℂ) * (θ : ℂ) * Complex.I = ((((d : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  have h2 : -((((d : ℝ) * θ : ℝ) : ℂ) * Complex.I) = (((-((d : ℝ) * θ) : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h1, h2]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    ring
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul,
      Complex.exp_ofReal_mul_I_im, Real.sin_neg]
    ring

private lemma antisymm_exp_pair (a : ℝ) (d : ℕ) (θ : ℝ) :
    (a : ℂ) * Complex.exp (((d : ℕ) : ℝ) * θ * Complex.I) +
    ((-a : ℝ) : ℂ) * Complex.exp (-(((d : ℕ) : ℝ) * θ * Complex.I)) =
    ((2 * a * Real.sin ((d : ℝ) * θ) : ℝ) : ℂ) * Complex.I := by
  have h1 : (((d : ℕ) : ℝ) : ℂ) * (θ : ℂ) * Complex.I = ((((d : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  have h2 : -((((d : ℝ) * θ : ℝ) : ℂ) * Complex.I) = (((-((d : ℝ) * θ) : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h1, h2]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
    ring

/-- Sum decomposition of `range (4*m + 1)` into center `2*m` plus symmetric pairs `2*m ± d`. -/
private lemma sum_centered_pairs (m : ℕ) (f : ℕ → ℂ) :
    ∑ j ∈ range (4 * m + 1), f j =
      f (2 * m) + ∑ d ∈ Finset.Icc 1 (2 * m), (f (2 * m + d) + f (2 * m - d)) := by
  have hsplit : ∑ j ∈ range (4 * m + 1), f j =
      (∑ j ∈ range (2 * m), f j) + f (2 * m) + ∑ d ∈ range (2 * m), f (2 * m + 1 + d) := by
    rw [show 4 * m + 1 = (2 * m + 1) + 2 * m by omega, Finset.sum_range_add,
      Finset.sum_range_succ]
  have hlo : ∑ j ∈ range (2 * m), f j = ∑ d ∈ Finset.Icc 1 (2 * m), f (2 * m - d) := by
    refine Finset.sum_bij (fun j _ => 2 * m - j) ?_ ?_ ?_ ?_
    · intro j hj; rw [Finset.mem_Icc]; have := Finset.mem_range.mp hj; omega
    · intro j₁ h1 j₂ h2 hEq
      have := Finset.mem_range.mp h1; have := Finset.mem_range.mp h2; omega
    · intro d hd; rw [Finset.mem_Icc] at hd
      exact ⟨2 * m - d, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j hj; have := Finset.mem_range.mp hj; congr 1; omega
  have hhi : ∑ d ∈ range (2 * m), f (2 * m + 1 + d) = ∑ d ∈ Finset.Icc 1 (2 * m), f (2 * m + d) := by
    refine Finset.sum_bij (fun d _ => d + 1) ?_ ?_ ?_ ?_
    · intro d hd; rw [Finset.mem_Icc]; have := Finset.mem_range.mp hd; omega
    · intro d₁ _ d₂ _ hEq; omega
    · intro d hd; rw [Finset.mem_Icc] at hd
      exact ⟨d - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro d _; congr 1; omega
  rw [hsplit, hlo, hhi, Finset.sum_add_distrib]
  ring

/-- Splitting a sum over `Icc 1 (2*m)` into even indices `2*l` (`l ∈ Icc 1 m`) and odd indices `2*j+1` (`j < m`). -/
private lemma sum_Icc_even_odd (m : ℕ) (g : ℕ → ℂ) :
    ∑ d ∈ Finset.Icc 1 (2 * m), g d =
      (∑ l ∈ Finset.Icc 1 m, g (2 * l)) + ∑ j ∈ range m, g (2 * j + 1) := by
  have hev_inj : Set.InjOn (fun l => 2 * l) (Finset.Icc 1 m : Set ℕ) := by
    intro a _ b _ h; dsimp only at h; omega
  have hodd_inj : Set.InjOn (fun j => 2 * j + 1) (range m : Set ℕ) := by
    intro a _ b _ h; dsimp only at h; omega
  have hdisj : Disjoint ((Finset.Icc 1 m).image (fun l => 2 * l))
      ((range m).image (fun j => 2 * j + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx2
    omega
  have hunion : Finset.Icc 1 (2 * m) =
      (Finset.Icc 1 m).image (fun l => 2 * l) ∪ (range m).image (fun j => 2 * j + 1) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    constructor
    · intro ⟨h1, h2⟩
      by_cases he : d % 2 = 0
      · left; exact ⟨d / 2, ⟨by omega, by omega⟩, by omega⟩
      · right; exact ⟨d / 2, by omega, by omega⟩
    · rintro (⟨l, ⟨h1, h2⟩, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
  rw [hunion, Finset.sum_union hdisj, Finset.sum_image (fun a ha b hb h => hev_inj ha hb h),
    Finset.sum_image (fun a ha b hb h => hodd_inj ha hb h)]

/-- Bound on the even-sine remainder `∑_{l ∈ Icc 1 m \ (B₁ ∪ B₂)} rsSeq l * sin (2l θ)` via 5 initial-segment bounds. -/
private lemma even_sine_rem_bound (m t : ℕ) (hm100 : 100 ≤ m)
    (hT_hi : 2 * 2 ^ (t + 10) + 2 ^ t ≤ m) (θ : ℝ) :
    let T := 2 ^ (t + 10)
    let B₁ := Finset.Ico T (T + 2 ^ t)
    let B₂ := Finset.Ico (2 * T) (2 * T + 2 ^ t)
    |∑ l ∈ (Finset.Icc 1 m) \ (B₁ ∪ B₂), TwoOrbitCosine.rsSeq l * Real.sin (2 * (l : ℝ) * θ)|
      ≤ 25 * Real.sqrt m := by
  intro T B₁ B₂
  set w : ℂ := Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)
  have hw : ‖w‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hT_pos : 1 ≤ T := Nat.one_le_two_pow
  have h2t_pos : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have h2t_lt_T : 2 ^ t < T := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hB1_sub : B₁ ⊆ Finset.Icc 1 m := by
    intro l hl; simp only [B₁, Finset.mem_Ico] at hl; simp only [Finset.mem_Icc]; omega
  have hB2_sub : B₂ ⊆ Finset.Icc 1 m := by
    intro l hl; simp only [B₂, Finset.mem_Ico] at hl; simp only [Finset.mem_Icc]; omega
  have hB_disj : Disjoint B₁ B₂ := by
    rw [Finset.disjoint_left]; intro l h1 h2
    simp only [B₁, B₂, Finset.mem_Ico] at h1 h2; omega
  let F (l : ℕ) : ℂ := (TwoOrbitCosine.rsSeq l : ℂ) * w ^ l
  have hF_im : ∀ l : ℕ, (F l).im = TwoOrbitCosine.rsSeq l * Real.sin (2 * (l : ℝ) * θ) := by
    intro l
    dsimp only [F, w]
    rw [← Complex.exp_nat_mul]
    have harg : (l : ℂ) * (((2 * θ : ℝ) : ℂ) * Complex.I) = (((2 * (l : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [harg, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hsum_im : ∑ l ∈ (Finset.Icc 1 m) \ (B₁ ∪ B₂), TwoOrbitCosine.rsSeq l * Real.sin (2 * (l : ℝ) * θ) =
      (∑ l ∈ (Finset.Icc 1 m) \ (B₁ ∪ B₂), F l).im := by
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun l _ => (hF_im l).symm
  have hsplit : ∑ l ∈ (Finset.Icc 1 m) \ (B₁ ∪ B₂), F l =
      (∑ l ∈ range (m + 1), F l) - F 0 -
      ((∑ l ∈ range (T + 2 ^ t), F l) - (∑ l ∈ range T, F l)) -
      ((∑ l ∈ range (2 * T + 2 ^ t), F l) - (∑ l ∈ range (2 * T), F l)) := by
    have hIcc : ∑ l ∈ Finset.Icc 1 m, F l = (∑ l ∈ range (m + 1), F l) - F 0 := by
      have hU : range (m + 1) = insert 0 (Finset.Icc 1 m) := by
        ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      have h0 : 0 ∉ Finset.Icc 1 m := by simp
      rw [hU, Finset.sum_insert h0]; ring
    have hIco : ∀ a b : ℕ, a ≤ b → ∑ l ∈ Finset.Ico a b, F l =
        (∑ l ∈ range b, F l) - ∑ l ∈ range a, F l := by
      intro a b hab
      have hU : range b = range a ∪ Finset.Ico a b := by
        ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      have hD : Disjoint (range a) (Finset.Ico a b) := by
        rw [Finset.disjoint_left]; intro x h1 h2
        simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
      rw [hU, Finset.sum_union hD]; ring
    have hsub : B₁ ∪ B₂ ⊆ Finset.Icc 1 m := Finset.union_subset hB1_sub hB2_sub
    have hadd := Finset.sum_sdiff hsub (f := F)
    rw [Finset.sum_union hB_disj, hIcc, hIco T (T + 2 ^ t) (Nat.le_add_right _ _),
      hIco (2 * T) (2 * T + 2 ^ t) (Nat.le_add_right _ _)] at hadd
    linear_combination hadd
  have hpref : ∀ M ≤ m + 1, ‖∑ l ∈ range M, F l‖ ≤ 4 * Real.sqrt ((m + 1 : ℕ) : ℝ) := by
    intro M hM
    have h1 := TwoOrbitCosine.rsSeq_partial_bound M hw
    have h2 : Real.sqrt (M : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hM)
    exact h1.trans (by linarith only [h2])
  have hF0 : ‖F 0‖ = 1 := by
    dsimp only [F]; rw [pow_zero, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rcases TwoOrbitCosine.rsSeq_pm 0 with h | h <;> simp [h]
  have hnorm_sum : ‖∑ l ∈ (Finset.Icc 1 m) \ (B₁ ∪ B₂), F l‖ ≤
      20 * Real.sqrt ((m + 1 : ℕ) : ℝ) + 1 := by
    rw [hsplit]
    have h1 := hpref (m + 1) le_rfl
    have h2 := hpref (T + 2 ^ t) (by omega)
    have h3 := hpref T (by omega)
    have h4 := hpref (2 * T + 2 ^ t) (by omega)
    have h5 := hpref (2 * T) (by omega)
    have ht1 := norm_sub_le ((∑ l ∈ range (m + 1), F l) - F 0 -
      ((∑ l ∈ range (T + 2 ^ t), F l) - ∑ l ∈ range T, F l))
      ((∑ l ∈ range (2 * T + 2 ^ t), F l) - ∑ l ∈ range (2 * T), F l)
    have ht2 := norm_sub_le ((∑ l ∈ range (m + 1), F l) - F 0)
      ((∑ l ∈ range (T + 2 ^ t), F l) - ∑ l ∈ range T, F l)
    have ht3 := norm_sub_le (∑ l ∈ range (m + 1), F l) (F 0)
    have ht4 := norm_sub_le (∑ l ∈ range (T + 2 ^ t), F l) (∑ l ∈ range T, F l)
    have ht5 := norm_sub_le (∑ l ∈ range (2 * T + 2 ^ t), F l) (∑ l ∈ range (2 * T), F l)
    linarith only [ht1, ht2, ht3, ht4, ht5, h1, h2, h3, h4, h5, hF0]
  have hsqrt_cmp : Real.sqrt ((m + 1 : ℕ) : ℝ) ≤ (11 / 10 : ℝ) * Real.sqrt m := by
    have hsq : ((m + 1 : ℕ) : ℝ) ≤ ((11 / 10 : ℝ) * Real.sqrt m) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
      have hm_r : (100 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm100
      push_cast; nlinarith only [hm_r]
    calc Real.sqrt ((m + 1 : ℕ) : ℝ) ≤ Real.sqrt (((11 / 10 : ℝ) * Real.sqrt m) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = (11 / 10 : ℝ) * Real.sqrt m := Real.sqrt_sq (by positivity)
  have h1_le_sqrt : (1 : ℝ) ≤ Real.sqrt m := by
    rw [Real.one_le_sqrt]; exact_mod_cast (show 1 ≤ m by omega)
  rw [hsum_im]
  exact (Complex.abs_im_le_norm _).trans (by linarith only [hnorm_sum, hsqrt_cmp, h1_le_sqrt])

private noncomputable def coeffPos (m t : ℕ) (ε : Fin m → ℝ) (d : ℕ) : ℝ :=
  if d % 2 = 0 then
    let l := d / 2
    let T := 2 ^ (t + 10)
    if T ≤ l ∧ l < T + 2 ^ t then TwoOrbitCosine.rsPcoeff t (l - T)
    else if 2 * T ≤ l ∧ l < 2 * T + 2 ^ t then TwoOrbitCosine.rsQcoeff t (l - 2 * T)
    else TwoOrbitCosine.rsSeq l
  else
    if h : d / 2 < m then ε ⟨d / 2, h⟩ else 1

private noncomputable def coeffNeg (m t : ℕ) (ε : Fin m → ℝ) (d : ℕ) : ℝ :=
  if d % 2 = 0 then
    let l := d / 2
    let T := 2 ^ (t + 10)
    if T ≤ l ∧ l < T + 2 ^ t then TwoOrbitCosine.rsPcoeff t (l - T)
    else if 2 * T ≤ l ∧ l < 2 * T + 2 ^ t then TwoOrbitCosine.rsQcoeff t (l - 2 * T)
    else -TwoOrbitCosine.rsSeq l
  else
    if h : d / 2 < m then -ε ⟨d / 2, h⟩ else -1

private noncomputable def bVal (m t : ℕ) (ε : Fin m → ℝ) (j : ℕ) : ℝ :=
  if j < 2 * m then coeffNeg m t ε (2 * m - j)
  else if j = 2 * m then 1
  else if j ≤ 4 * m then coeffPos m t ε (j - 2 * m)
  else 1

private lemma bVal_pm (m t : ℕ) (ε : Fin m → ℝ) (hε : ∀ j, ε j = -1 ∨ ε j = 1) (j : ℕ) :
    bVal m t ε j = -1 ∨ bVal m t ε j = 1 := by
  have hpmP := (TwoOrbitCosine.rsPcoeff_pm_and_rsQcoeff_pm t).1
  have hpmQ := (TwoOrbitCosine.rsPcoeff_pm_and_rsQcoeff_pm t).2
  have hpos_pm : ∀ d : ℕ, coeffPos m t ε d = -1 ∨ coeffPos m t ε d = 1 := by
    intro d; dsimp only [coeffPos]
    split_ifs with he h1 h2 hlt
    · exact hpmP _ (by omega)
    · exact hpmQ _ (by omega)
    · exact TwoOrbitCosine.rsSeq_pm _
    · exact hε _
    · exact Or.inr rfl
  have hneg_pm : ∀ d : ℕ, coeffNeg m t ε d = -1 ∨ coeffNeg m t ε d = 1 := by
    intro d; dsimp only [coeffNeg]
    split_ifs with he h1 h2 hlt
    · exact hpmP _ (by omega)
    · exact hpmQ _ (by omega)
    · rcases TwoOrbitCosine.rsSeq_pm (d / 2) with h | h <;> [right; left] <;> linarith
    · rcases hε ⟨d / 2, hlt⟩ with h | h <;> [right; left] <;> linarith
    · exact Or.inl rfl
  dsimp only [bVal]
  split_ifs
  · exact hneg_pm _
  · exact Or.inr rfl
  · exact hpos_pm _
  · exact Or.inr rfl

private noncomputable def Pcenter (m t : ℕ) (ε : Fin m → ℝ) (θ : ℝ) : ℂ :=
  1 + ∑ d ∈ Finset.Icc 1 (2 * m),
    ((coeffPos m t ε d : ℂ) * Complex.exp (((d : ℕ) : ℝ) * θ * Complex.I) +
     (coeffNeg m t ε d : ℂ) * Complex.exp (-(((d : ℕ) : ℝ) * θ * Complex.I)))

private lemma signedSum_decomp (m t k : ℕ) (ε : Fin m → ℝ) (sign : ℕ → Bool)
    (hsign_val : ∀ j : ℕ, ∀ z : ℂ, (if sign j then z ^ j else -(z ^ j)) = (bVal m t ε j : ℂ) * z ^ j)
    (h4m_le : 4 * m + 1 ≤ 2 * k) (θ : ℝ) :
    let z : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
    TwoOrbitFlatSeed.signedSum sign k z =
      Complex.exp (((2 * m : ℕ) : ℝ) * θ * Complex.I) * Pcenter m t ε θ +
      ∑ j ∈ Finset.Ico (4 * m + 1) (2 * k), z ^ j := by
  intro z
  unfold TwoOrbitFlatSeed.signedSum
  rw [show k + k = 2 * k by omega]
  have hsplit_r : range (2 * k) = range (4 * m + 1) ∪ Finset.Ico (4 * m + 1) (2 * k) := by
    ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj_r : Disjoint (range (4 * m + 1)) (Finset.Ico (4 * m + 1) (2 * k)) := by
    rw [Finset.disjoint_left]; intro j h1 h2
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
  rw [hsplit_r, Finset.sum_union hdisj_r]
  congr 1
  · have hsum1 : ∑ j ∈ range (4 * m + 1), (if sign j then z ^ j else -(z ^ j)) =
        ∑ j ∈ range (4 * m + 1), (bVal m t ε j : ℂ) * z ^ j :=
      Finset.sum_congr rfl fun j _ => hsign_val j z
    rw [hsum1, sum_centered_pairs m]
    have hzpow : ∀ j : ℕ, z ^ j = Complex.exp (((j : ℕ) : ℝ) * θ * Complex.I) := by
      intro j; dsimp only [z]; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have hb_mid : bVal m t ε (2 * m) = 1 := by simp [bVal]
    rw [hb_mid, Complex.ofReal_one, one_mul, hzpow (2 * m)]
    dsimp only [Pcenter]
    rw [mul_add, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd2 : d ≤ 2 * m := (Finset.mem_Icc.mp hd).2
    have hb_pos : bVal m t ε (2 * m + d) = coeffPos m t ε d := by
      dsimp only [bVal]
      have h1 : ¬ (2 * m + d < 2 * m) := by omega
      have h2 : ¬ (2 * m + d = 2 * m) := by omega
      have h3 : 2 * m + d ≤ 4 * m := by omega
      simp only [h1, h2, h3, ↓reduceIte, Nat.add_sub_cancel_left]
    have hb_neg : bVal m t ε (2 * m - d) = coeffNeg m t ε d := by
      dsimp only [bVal]
      have h1 : 2 * m - d < 2 * m := by omega
      have hsub : 2 * m - (2 * m - d) = d := by omega
      simp only [h1, ↓reduceIte, hsub]
    rw [hb_pos, hb_neg, hzpow (2 * m + d), hzpow (2 * m - d), mul_add]
    congr 1
    · rw [mul_left_comm (Complex.exp _) (coeffPos m t ε d : ℂ), ← Complex.exp_add]
      congr 2; push_cast; ring
    · rw [mul_left_comm (Complex.exp _) (coeffNeg m t ε d : ℂ), ← Complex.exp_add]
      congr 2; rw [Nat.cast_sub hd2]; push_cast; ring
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hgt : 4 * m < j := (Finset.mem_Ico.mp hj).1
    have hb1 : bVal m t ε j = 1 := by
      dsimp only [bVal]
      have h1 : ¬ (j < 2 * m) := by omega
      have h2 : ¬ (j = 2 * m) := by omega
      have h3 : ¬ (j ≤ 4 * m) := by omega
      simp only [h1, h2, h3, ↓reduceIte]
    rw [hsign_val j z, hb1, Complex.ofReal_one, one_mul]

private lemma Pcenter_eval (m t : ℕ) (ε : Fin m → ℝ)
    (hT_hi : 2 * 2 ^ (t + 10) + 2 ^ t ≤ m) (θ : ℝ) :
    let T := 2 ^ (t + 10)
    let B₁ := Finset.Ico T (T + 2 ^ t)
    let B₂ := Finset.Ico (2 * T) (2 * T + 2 ^ t)
    (Pcenter m t ε θ).re = 1 + 2 * TwoOrbitCosine.cosPoly t θ ∧
    (Pcenter m t ε θ).im =
      2 * (∑ l ∈ (Finset.Icc 1 m) \ (B₁ ∪ B₂), TwoOrbitCosine.rsSeq l * Real.sin (2 * (l : ℝ) * θ)) +
      2 * (∑ j : Fin m, ε j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θ)) := by
  intro T B₁ B₂
  have hT_pos : 1 ≤ T := Nat.one_le_two_pow
  have h2t_pos : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have h2t_lt_T : 2 ^ t < T := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hsplit := sum_Icc_even_odd m (fun d =>
    (coeffPos m t ε d : ℂ) * Complex.exp (((d : ℕ) : ℝ) * θ * Complex.I) +
    (coeffNeg m t ε d : ℂ) * Complex.exp (-(((d : ℕ) : ℝ) * θ * Complex.I)))
  have hodd_part : ∑ j ∈ range m,
      ((coeffPos m t ε (2 * j + 1) : ℂ) * Complex.exp (((2 * j + 1 : ℕ) : ℝ) * θ * Complex.I) +
       (coeffNeg m t ε (2 * j + 1) : ℂ) * Complex.exp (-(((2 * j + 1 : ℕ) : ℝ) * θ * Complex.I))) =
      ((2 * ∑ j : Fin m, ε j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θ) : ℝ) : ℂ) * Complex.I := by
    rw [← Fin.sum_univ_eq_sum_range]
    have hterm : ∀ j : Fin m,
        (coeffPos m t ε (2 * j.val + 1) : ℂ) * Complex.exp (((2 * j.val + 1 : ℕ) : ℝ) * θ * Complex.I) +
        (coeffNeg m t ε (2 * j.val + 1) : ℂ) * Complex.exp (-(((2 * j.val + 1 : ℕ) : ℝ) * θ * Complex.I)) =
        ((2 * (ε j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θ)) : ℝ) : ℂ) * Complex.I := by
      intro j
      have hodd : ¬ ((2 * j.val + 1) % 2 = 0) := by omega
      have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
      have hp : coeffPos m t ε (2 * j.val + 1) = ε j := by
        dsimp only [coeffPos]; simp only [hodd, ↓reduceIte, hdiv, j.isLt, ↓reduceDIte, Fin.eta]
      have hn : coeffNeg m t ε (2 * j.val + 1) = -ε j := by
        dsimp only [coeffNeg]; simp only [hodd, ↓reduceIte, hdiv, j.isLt, ↓reduceDIte, Fin.eta]
      rw [hp, hn, antisymm_exp_pair]; congr 2; ring
    rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_mul, ← Complex.ofReal_sum,
      Finset.mul_sum]
  have heven_part : ∑ l ∈ Finset.Icc 1 m,
      ((coeffPos m t ε (2 * l) : ℂ) * Complex.exp (((2 * l : ℕ) : ℝ) * θ * Complex.I) +
       (coeffNeg m t ε (2 * l) : ℂ) * Complex.exp (-(((2 * l : ℕ) : ℝ) * θ * Complex.I))) =
      ((2 * TwoOrbitCosine.cosPoly t θ : ℝ) : ℂ) +
      ((2 * ∑ l ∈ (Finset.Icc 1 m) \ (B₁ ∪ B₂), TwoOrbitCosine.rsSeq l * Real.sin (2 * (l : ℝ) * θ) : ℝ) : ℂ) * Complex.I := by
    have hB1_sub : B₁ ⊆ Finset.Icc 1 m := by
      intro l hl; simp only [B₁, Finset.mem_Ico] at hl; simp only [Finset.mem_Icc]; omega
    have hB2_sub : B₂ ⊆ Finset.Icc 1 m := by
      intro l hl; simp only [B₂, Finset.mem_Ico] at hl; simp only [Finset.mem_Icc]; omega
    have hB_disj : Disjoint B₁ B₂ := by
      rw [Finset.disjoint_left]; intro l h1 h2
      simp only [B₁, B₂, Finset.mem_Ico] at h1 h2; omega
    have hsub := Finset.union_subset hB1_sub hB2_sub
    rw [← Finset.sum_sdiff hsub, Finset.sum_union hB_disj]
    have hrem : ∑ l ∈ (Finset.Icc 1 m) \ (B₁ ∪ B₂),
        ((coeffPos m t ε (2 * l) : ℂ) * Complex.exp (((2 * l : ℕ) : ℝ) * θ * Complex.I) +
         (coeffNeg m t ε (2 * l) : ℂ) * Complex.exp (-(((2 * l : ℕ) : ℝ) * θ * Complex.I))) =
        ((2 * ∑ l ∈ (Finset.Icc 1 m) \ (B₁ ∪ B₂), TwoOrbitCosine.rsSeq l * Real.sin (2 * (l : ℝ) * θ) : ℝ) : ℂ) * Complex.I := by
      have hterm : ∀ l ∈ (Finset.Icc 1 m) \ (B₁ ∪ B₂),
          (coeffPos m t ε (2 * l) : ℂ) * Complex.exp (((2 * l : ℕ) : ℝ) * θ * Complex.I) +
          (coeffNeg m t ε (2 * l) : ℂ) * Complex.exp (-(((2 * l : ℕ) : ℝ) * θ * Complex.I)) =
          ((2 * (TwoOrbitCosine.rsSeq l * Real.sin (2 * (l : ℝ) * θ)) : ℝ) : ℂ) * Complex.I := by
        intro l hl
        have hnot := (Finset.mem_sdiff.mp hl).2
        have hnot1 : ¬ (2 ^ (t + 10) ≤ l ∧ l < 2 ^ (t + 10) + 2 ^ t) := fun h =>
          hnot (Finset.mem_union_left _ (Finset.mem_Ico.mpr h))
        have hnot2 : ¬ (2 * 2 ^ (t + 10) ≤ l ∧ l < 2 * 2 ^ (t + 10) + 2 ^ t) := fun h =>
          hnot (Finset.mem_union_right _ (Finset.mem_Ico.mpr h))
        have hev : (2 * l) % 2 = 0 := by omega
        have hdiv : (2 * l) / 2 = l := by omega
        have hp : coeffPos m t ε (2 * l) = TwoOrbitCosine.rsSeq l := by
          dsimp only [coeffPos]; simp only [hev, ↓reduceIte, hdiv, hnot1, hnot2]
        have hn : coeffNeg m t ε (2 * l) = -TwoOrbitCosine.rsSeq l := by
          dsimp only [coeffNeg]; simp only [hev, ↓reduceIte, hdiv, hnot1, hnot2]
        rw [hp, hn, antisymm_exp_pair]
        apply congrArg (· * Complex.I)
        apply congrArg Complex.ofReal
        have harg : (((2 * l : ℕ) : ℝ) * θ) = 2 * (l : ℝ) * θ := by push_cast; ring
        rw [harg]; ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Complex.ofReal_sum, Finset.mul_sum]
    have hB1 : ∑ l ∈ B₁,
        ((coeffPos m t ε (2 * l) : ℂ) * Complex.exp (((2 * l : ℕ) : ℝ) * θ * Complex.I) +
         (coeffNeg m t ε (2 * l) : ℂ) * Complex.exp (-(((2 * l : ℕ) : ℝ) * θ * Complex.I))) =
        ((2 * ∑ j ∈ range (2 ^ t), TwoOrbitCosine.rsPcoeff t j * Real.cos (2 * ((T + j : ℕ) : ℝ) * θ) : ℝ) : ℂ) := by
      have hbij : ∑ l ∈ B₁,
          ((coeffPos m t ε (2 * l) : ℂ) * Complex.exp (((2 * l : ℕ) : ℝ) * θ * Complex.I) +
           (coeffNeg m t ε (2 * l) : ℂ) * Complex.exp (-(((2 * l : ℕ) : ℝ) * θ * Complex.I))) =
          ∑ j ∈ range (2 ^ t),
            ((2 * (TwoOrbitCosine.rsPcoeff t j * Real.cos (2 * ((T + j : ℕ) : ℝ) * θ)) : ℝ) : ℂ) := by
        refine Finset.sum_bij (fun l _ => l - T) ?_ ?_ ?_ ?_
        · intro l hl; simp only [B₁, Finset.mem_Ico] at hl; simp only [Finset.mem_range]; omega
        · intro l₁ h1 l₂ h2 hEq
          simp only [B₁, Finset.mem_Ico] at h1 h2; omega
        · intro j hj; simp only [Finset.mem_range] at hj
          exact ⟨T + j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro l hl
          have h1 : 2 ^ (t + 10) ≤ l ∧ l < 2 ^ (t + 10) + 2 ^ t := Finset.mem_Ico.mp hl
          have hev : (2 * l) % 2 = 0 := by omega
          have hdiv : (2 * l) / 2 = l := by omega
          have hp : coeffPos m t ε (2 * l) = TwoOrbitCosine.rsPcoeff t (l - T) := by
            dsimp only [coeffPos, T]; simp only [hev, ↓reduceIte, hdiv, h1.1, h1.2, and_self]
          have hn : coeffNeg m t ε (2 * l) = TwoOrbitCosine.rsPcoeff t (l - T) := by
            dsimp only [coeffNeg, T]; simp only [hev, ↓reduceIte, hdiv, h1.1, h1.2, and_self]
          rw [hp, hn, symm_exp_pair]
          have hl_eq : T + (l - T) = l := by dsimp only [T]; omega
          rw [hl_eq]
          apply congrArg Complex.ofReal
          have harg : (((2 * l : ℕ) : ℝ) * θ) = 2 * ((l : ℕ) : ℝ) * θ := by push_cast; ring
          rw [harg]; ring
      rw [hbij, ← Complex.ofReal_sum, Finset.mul_sum]
    have hB2 : ∑ l ∈ B₂,
        ((coeffPos m t ε (2 * l) : ℂ) * Complex.exp (((2 * l : ℕ) : ℝ) * θ * Complex.I) +
         (coeffNeg m t ε (2 * l) : ℂ) * Complex.exp (-(((2 * l : ℕ) : ℝ) * θ * Complex.I))) =
        ((2 * ∑ j ∈ range (2 ^ t), TwoOrbitCosine.rsQcoeff t j * Real.cos (2 * ((2 * T + j : ℕ) : ℝ) * θ) : ℝ) : ℂ) := by
      have hbij : ∑ l ∈ B₂,
          ((coeffPos m t ε (2 * l) : ℂ) * Complex.exp (((2 * l : ℕ) : ℝ) * θ * Complex.I) +
           (coeffNeg m t ε (2 * l) : ℂ) * Complex.exp (-(((2 * l : ℕ) : ℝ) * θ * Complex.I))) =
          ∑ j ∈ range (2 ^ t),
            ((2 * (TwoOrbitCosine.rsQcoeff t j * Real.cos (2 * ((2 * T + j : ℕ) : ℝ) * θ)) : ℝ) : ℂ) := by
        refine Finset.sum_bij (fun l _ => l - 2 * T) ?_ ?_ ?_ ?_
        · intro l hl; simp only [B₂, Finset.mem_Ico] at hl; simp only [Finset.mem_range]; omega
        · intro l₁ h1 l₂ h2 hEq
          simp only [B₂, Finset.mem_Ico] at h1 h2; omega
        · intro j hj; simp only [Finset.mem_range] at hj
          exact ⟨2 * T + j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro l hl
          have h2 : 2 * 2 ^ (t + 10) ≤ l ∧ l < 2 * 2 ^ (t + 10) + 2 ^ t := Finset.mem_Ico.mp hl
          have hnot1 : ¬ (2 ^ (t + 10) ≤ l ∧ l < 2 ^ (t + 10) + 2 ^ t) := by dsimp only [T] at h2t_lt_T; omega
          have hev : (2 * l) % 2 = 0 := by omega
          have hdiv : (2 * l) / 2 = l := by omega
          have hp : coeffPos m t ε (2 * l) = TwoOrbitCosine.rsQcoeff t (l - 2 * T) := by
            dsimp only [coeffPos, T]; simp only [hev, ↓reduceIte, hdiv, hnot1, h2.1, h2.2, and_self]
          have hn : coeffNeg m t ε (2 * l) = TwoOrbitCosine.rsQcoeff t (l - 2 * T) := by
            dsimp only [coeffNeg, T]; simp only [hev, ↓reduceIte, hdiv, hnot1, h2.1, h2.2, and_self]
          rw [hp, hn, symm_exp_pair]
          have hl_eq : 2 * T + (l - 2 * T) = l := by dsimp only [T]; omega
          rw [hl_eq]
          apply congrArg Complex.ofReal
          have harg : (((2 * l : ℕ) : ℝ) * θ) = 2 * ((l : ℕ) : ℝ) * θ := by push_cast; ring
          rw [harg]; ring
      rw [hbij, ← Complex.ofReal_sum, Finset.mul_sum]
    rw [hrem, hB1, hB2, TwoOrbitCosine.cosPoly_eq_cos_sum, Finset.sum_add_distrib, mul_add, Complex.ofReal_add]
    dsimp only [T]
    ring
  have hfull : Pcenter m t ε θ =
      ((1 + 2 * TwoOrbitCosine.cosPoly t θ : ℝ) : ℂ) +
      ((2 * (∑ l ∈ (Finset.Icc 1 m) \ (B₁ ∪ B₂), TwoOrbitCosine.rsSeq l * Real.sin (2 * (l : ℝ) * θ)) +
        2 * (∑ j : Fin m, ε j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θ)) : ℝ) : ℂ) * Complex.I := by
    dsimp only [Pcenter]
    rw [hsplit, heven_part, hodd_part, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_add]
    ring
  rw [hfull]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  constructor <;> ring

/-- Bridge A: For all sufficiently large `k`, there exists an initial seed `S₀ ⊆ Fin (3k+1)`
with `|S₀.card - k| ≤ 3 √n` and joint Fourier floor `(1 / (12 * c474)) √n` with the interval `I`. -/
theorem discrete_flat_littlewood_seed :
    ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k → 2 ≤ k →
      let n := 3 * k + 1
      let I := (Finset.univ : Finset (Fin n)).filter (fun i => i.val < k)
      ∃ S₀ : Finset (Fin n),
        |(S₀.card : ℝ) - (k : ℝ)| ≤ 3 * Real.sqrt n ∧
        ∀ ξ : Fin n, ξ.val ≠ 0 →
          (1 / (12 * TwoOrbitCosine.c474)) * Real.sqrt n ≤
            max ‖TwoOrbitMiddle.hatSet n I ξ‖ ‖TwoOrbitMiddle.hatSet n S₀ ξ‖ := by
  classical
  obtain ⟨K1, hK1⟩ := exists_nat_gt ((256 * TwoOrbitCosine.c474) ^ 2)
  refine ⟨max (16 ^ 38) (4 * K1 + 100000), ?_⟩
  intro k hk hk2 n I
  have hk_16 : 16 ^ 38 ≤ k := le_trans (le_max_left _ _) hk
  have hk_K1 : 4 * K1 + 100000 ≤ k := le_trans (le_max_right _ _) hk
  set m : ℕ := 32 * ((2 * k - 1) / 128)
  have hm32 : 32 ∣ m := ⟨(2 * k - 1) / 128, rfl⟩
  have h4m_le : 4 * m + 1 ≤ 2 * k := by
    have h1 : 128 * ((2 * k - 1) / 128) ≤ 2 * k - 1 := Nat.mul_div_le _ _
    dsimp only [m]; omega
  have h4m_ge : 2 * k - 128 ≤ 4 * m := by
    have h1 : 2 * k - 1 < 128 * ((2 * k - 1) / 128 + 1) := by
      have := Nat.lt_mul_div_succ (2 * k - 1) (by norm_num : 0 < 128); linarith
    dsimp only [m]; omega
  have hm_ge_K1 : K1 + 20000 ≤ m := by omega
  have hm_16_37 : 16 ^ 37 ≤ m := by
    have h1 : 4 * 16 ^ 37 ≤ 2 * 16 ^ 38 - 128 := by
      have hpow : 16 ^ 38 = 16 * 16 ^ 37 := by rw [pow_succ']
      have hpos : 16 ^ 3 ≤ 16 ^ 37 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      have h3 : 16 ^ 3 = 4096 := by norm_num
      omega
    have h2 : 4 * 16 ^ 37 ≤ 4 * m := le_trans h1 (le_trans (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hk_16) 128) h4m_ge)
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  have hm_big : 16 ^ 33 ≤ m :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num : 33 ≤ 37)) hm_16_37
  have hm_pos : 0 < m := by omega
  have hn_le_7m : n ≤ 7 * m := by dsimp only [n]; omega
  have hm_le_n : m ≤ n := by dsimp only [n]; omega
  let f (r : ℕ) : ℕ := 2 * 2 ^ (2 * r + 1 + 10) + 2 ^ (2 * r + 1) - 1
  have hf0 : f 0 ≤ m / 16 ^ 33 := by
    have h1 : f 0 ≤ 16 ^ 4 := by dsimp [f]; norm_num
    have h2 : 16 ^ 4 * 16 ^ 33 ≤ m := by rw [← pow_add]; exact hm_16_37
    exact h1.trans ((Nat.le_div_iff_mul_le (Nat.pow_pos (by norm_num : 0 < 16))).mpr h2)
  let Sr : Finset ℕ := (range (m + 1)).filter (fun r => f r ≤ m / 16 ^ 33)
  have hSr_ne : Sr.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hf0⟩⟩
  set r : ℕ := Sr.max' hSr_ne
  have hr_mem : r ∈ Sr := Finset.max'_mem Sr hSr_ne
  have hγ_hi : f r ≤ m / 16 ^ 33 := (Finset.mem_filter.mp hr_mem).2
  have hγ_lo : m ≤ (8 * 16 ^ 33) * f r := by
    have hr_lt_m : r < m := by
      have h1 : r < 2 ^ (2 * r + 1) :=
        lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h2 : 2 ^ (2 * r + 1) ≤ f r := by
        dsimp only [f]; have : 1 ≤ 2 ^ (2 * r + 1 + 10) := Nat.one_le_two_pow; omega
      have h3 : m / 16 ^ 33 < m := Nat.div_lt_self hm_pos (by
        have : 16 ^ 1 ≤ 16 ^ 33 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
        omega)
      omega
    have hnot : r + 1 ∉ Sr := fun hmem => by
      have := Finset.le_max' Sr (r + 1) hmem; omega
    have hgt : m / 16 ^ 33 < f (r + 1) := by
      by_contra! hle
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hle⟩)
    have hstep : f (r + 1) ≤ 7 * f r := by
      dsimp only [f]
      have ha : 2 ^ (2 * (r + 1) + 1 + 10) = 4 * 2 ^ (2 * r + 1 + 10) := by
        rw [show 2 * (r + 1) + 1 + 10 = (2 * r + 1 + 10) + 2 by omega, pow_add]; ring
      have hb : 2 ^ (2 * (r + 1) + 1) = 4 * 2 ^ (2 * r + 1) := by
        rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega, pow_add]; ring
      have hpos : 1 ≤ 2 ^ (2 * r + 1) := Nat.one_le_two_pow
      rw [ha, hb]; omega
    have hq1 : m / 16 ^ 33 + 1 ≤ 7 * f r := by omega
    have hdiv : m ≤ 16 ^ 33 * (m / 16 ^ 33 + 1) := by
      have := Nat.lt_mul_div_succ m (Nat.pow_pos (by norm_num : 0 < 16) (n := 33))
      omega
    calc m ≤ 16 ^ 33 * (m / 16 ^ 33 + 1) := hdiv
      _ ≤ 16 ^ 33 * (7 * f r) := Nat.mul_le_mul_left _ hq1
      _ ≤ 16 ^ 33 * (8 * f r) := Nat.mul_le_mul_left _ (by omega)
      _ = (8 * 16 ^ 33) * f r := by ring
  set t : ℕ := 2 * r + 1
  obtain ⟨runs, hruns_in, hruns_sep, hruns_card0, hcos_good⟩ :=
    TwoOrbitCosine.cosine_bad_runs m r hm32 hm_pos hγ_hi hγ_lo
  have hruns_card : runs.card * (8 * 16 ^ 32) ≤ m := by
    have h1 : f r * 16 ^ 33 ≤ m :=
      (Nat.le_div_iff_mul_le (Nat.pow_pos (by norm_num : 0 < 16))).mp hγ_hi
    calc runs.card * (8 * 16 ^ 32)
        ≤ (2 * f r) * (8 * 16 ^ 32) := Nat.mul_le_mul_right _ hruns_card0
      _ = f r * (16 * 16 ^ 32) := by ring
      _ = f r * 16 ^ 33 := by rw [← pow_succ']
      _ ≤ m := h1
  let θs : Fin n → ℝ := fun ξ => 2 * Real.pi * (ξ.val : ℝ) / (n : ℝ)
  obtain ⟨ε, hε_pm, hodd_good⟩ :=
    TwoOrbitFejer.fejer_odd_sine_exists TwoOrbitDiscrepancy.full_coloring
      m hm32 hm_big runs hruns_in hruns_sep hruns_card n hn_le_7m θs
  have hT_hi : 2 * 2 ^ (t + 10) + 2 ^ t ≤ m := by
    have h1 : f r * 16 ^ 33 ≤ m :=
      (Nat.le_div_iff_mul_le (Nat.pow_pos (by norm_num : 0 < 16))).mp hγ_hi
    have h2 : 2 ≤ 16 ^ 33 := le_trans (by norm_num : 2 ≤ 16 ^ 1) (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    have h3 : 2 * f r ≤ m := by
      have hmul : f r * 2 ≤ f r * 16 ^ 33 := Nat.mul_le_mul_left (f r) h2
      linarith only [h1, hmul]
    dsimp only [f] at h3
    dsimp only [t]
    have hpos : 1 ≤ 2 ^ (2 * r + 1) := Nat.one_le_two_pow
    omega
  let sign (j : ℕ) : Bool := decide (bVal m t ε j = 1)
  have hsign_val : ∀ j : ℕ, ∀ z : ℂ, (if sign j then z ^ j else -(z ^ j)) = (bVal m t ε j : ℂ) * z ^ j := by
    intro j z
    rcases bVal_pm m t ε hε_pm j with h | h
    · have hf : sign j = false := by
        simp only [sign, h, decide_eq_false_iff_not]; norm_num
      rw [hf, h]; simp
    · have ht : sign j = true := by
        simp only [sign, h, decide_eq_true_eq]
      rw [ht, h]; simp
  have hpad_le : ∀ z : ℂ, ‖z‖ = 1 → ‖∑ j ∈ Finset.Ico (4 * m + 1) (2 * k), z ^ j‖ ≤ 127 := by
    intro z hz
    calc ‖∑ j ∈ Finset.Ico (4 * m + 1) (2 * k), z ^ j‖
        ≤ ∑ j ∈ Finset.Ico (4 * m + 1) (2 * k), ‖z ^ j‖ := norm_sum_le _ _
      _ = ∑ _j ∈ Finset.Ico (4 * m + 1) (2 * k), (1 : ℝ) :=
          Finset.sum_congr rfl fun j _ => by rw [norm_pow, hz, one_pow]
      _ = ((2 * k - (4 * m + 1) : ℕ) : ℝ) := by simp
      _ ≤ 127 := by exact_mod_cast (show 2 * k - (4 * m + 1) ≤ 127 by omega)
  let pos := TwoOrbitFlatSeed.positives sign k
  have hpos_lt : ∀ j ∈ pos, j < n := by
    intro j hj
    have : j < k + k := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    dsimp only [n]; omega
  let S₀ : Finset (Fin n) := pos.attach.image (fun j => ⟨j.1, hpos_lt j.1 j.2⟩)
  have hS0_card : S₀.card = pos.card := by
    dsimp only [S₀]
    rw [Finset.card_image_of_injective _ (fun a b h => Subtype.ext (congrArg Fin.val h)),
      Finset.card_attach]
  refine ⟨S₀, ?_, ?_⟩
  · -- Cardinality error `|S₀.card - k| ≤ 3 √n`.
    have hce := TwoOrbitFlatSeed.cardinalError sign k
    have h1 := signedSum_decomp m t k ε sign hsign_val h4m_le 0
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, Complex.exp_zero, one_mul] at h1
    have hP0_eval := Pcenter_eval m t ε hT_hi 0
    simp only [mul_zero, Real.sin_zero, Finset.sum_const_zero, add_zero] at hP0_eval
    have hP0_norm : ‖Pcenter m t ε 0‖ ≤ 1 + 4 * Real.sqrt m := by
      have hre : ‖Pcenter m t ε 0‖ = |(Pcenter m t ε 0).re| := by
        have hsq : ‖Pcenter m t ε 0‖ ^ 2 = (Pcenter m t ε 0).re ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply, hP0_eval.2]; ring
        have : |(Pcenter m t ε 0).re| ^ 2 = (Pcenter m t ε 0).re ^ 2 := sq_abs _
        nlinarith only [hsq, this, norm_nonneg (Pcenter m t ε 0), abs_nonneg (Pcenter m t ε 0).re]
      rw [hre, hP0_eval.1]
      have hcos0 := TwoOrbitCosine.cosPoly_norm_le t 0
      have h2t1_le : (2 : ℝ) ^ (t + 1) ≤ (m : ℝ) := by
        have hnat : 2 ^ (t + 1) ≤ m := by
          have : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ']
          have : 2 ^ t ≤ 2 ^ (t + 10) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        exact_mod_cast hnat
      have hsq_le : Real.sqrt ((2 : ℝ) ^ (t + 1)) ≤ Real.sqrt m := Real.sqrt_le_sqrt h2t1_le
      have habs : |1 + 2 * TwoOrbitCosine.cosPoly t 0| ≤ 1 + 2 * |TwoOrbitCosine.cosPoly t 0| := by
        calc |1 + 2 * TwoOrbitCosine.cosPoly t 0| ≤ |1| + |2 * TwoOrbitCosine.cosPoly t 0| := abs_add_le _ _
          _ = 1 + 2 * |TwoOrbitCosine.cosPoly t 0| := by rw [abs_one, abs_mul]; norm_num
      linarith only [habs, hcos0, hsq_le]
    have hnorm1 : ‖TwoOrbitFlatSeed.signedSum sign k 1‖ ≤ 6 * Real.sqrt n := by
      have hpad1 := hpad_le 1 (by simp)
      have htri : ‖TwoOrbitFlatSeed.signedSum sign k 1‖ ≤ ‖Pcenter m t ε 0‖ + 127 := by
        rw [h1]; exact (norm_add_le _ _).trans (by linarith only [hpad1])
      have hsqrt_mn : Real.sqrt m ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hm_le_n)
      have h128 : (128 : ℝ) ≤ 2 * Real.sqrt m := by
        have hsq : (64 : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast (show 64 ^ 2 ≤ m by omega)
        have h64 : (64 : ℝ) ≤ Real.sqrt m := by
          calc (64 : ℝ) = Real.sqrt ((64 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
            _ ≤ Real.sqrt m := Real.sqrt_le_sqrt hsq
        linarith only [h64]
      linarith only [htri, hP0_norm, hsqrt_mn, h128]
    rw [hS0_card]; linarith only [hce, hnorm1]
  · -- Joint Fourier lower bound at every nonzero frequency `ξ`.
    intro ξ hξ0
    set z : ℂ := TwoOrbitMiddle.phase ((ξ.val : ℝ) / (n : ℝ))
    have hz_eq : z = Complex.exp ((θs ξ : ℂ) * Complex.I) := by
      dsimp only [z, TwoOrbitMiddle.phase, θs]; congr 1; push_cast; ring
    have hz_norm : ‖z‖ = 1 := TwoOrbitMiddle.norm_phase _
    have hhat_I : TwoOrbitMiddle.hatSet n I ξ = TwoOrbitFlatSeed.series (range k) z := by
      unfold TwoOrbitMiddle.hatSet TwoOrbitFlatSeed.series
      refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
      · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      · intro i₁ _ i₂ _ hEq; exact Fin.ext hEq
      · intro j hj; refine ⟨⟨j, by dsimp [n]; have := Finset.mem_range.mp hj; omega⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hj⟩
      · intro i _; exact TwoOrbitMiddle.chi_eq_pow ξ i
    have hhat_S0 : TwoOrbitMiddle.hatSet n S₀ ξ = TwoOrbitFlatSeed.series pos z := by
      unfold TwoOrbitMiddle.hatSet TwoOrbitFlatSeed.series
      dsimp only [S₀]
      rw [Finset.sum_image (fun a _ b _ h => Subtype.ext (congrArg Fin.val h))]
      refine Finset.sum_bij (fun j _ => j.1) ?_ ?_ ?_ ?_
      · intro j _; exact j.2
      · intro j₁ _ j₂ _ hEq; exact Subtype.ext hEq
      · intro j hj; exact ⟨⟨j, hj⟩, Finset.mem_attach _ _, rfl⟩
      · intro j _; exact TwoOrbitMiddle.chi_eq_pow ξ ⟨j.1, hpos_lt j.1 j.2⟩
    have hPcenter_ge : (1 / TwoOrbitCosine.c474) * Real.sqrt m ≤ ‖TwoOrbitFlatSeed.signedSum sign k z‖ := by
      have hdecomp := signedSum_decomp m t k ε sign hsign_val h4m_le (θs ξ)
      rw [← hz_eq] at hdecomp
      have hshift_norm : ‖Complex.exp (((2 * m : ℕ) : ℝ) * θs ξ * Complex.I) * Pcenter m t ε (θs ξ)‖ =
          ‖Pcenter m t ε (θs ξ)‖ := by
        have he : ‖Complex.exp (((2 * m : ℕ) : ℝ) * θs ξ * Complex.I)‖ = 1 := by
          have : (((2 * m : ℕ) : ℝ) : ℂ) * (θs ξ : ℂ) * Complex.I =
              ((((2 * m : ℕ) : ℝ) * θs ξ : ℝ) : ℂ) * Complex.I := by push_cast; ring
          rw [this, Complex.norm_exp_ofReal_mul_I]
        rw [norm_mul, he, one_mul]
      have htri : ‖Pcenter m t ε (θs ξ)‖ - 127 ≤ ‖TwoOrbitFlatSeed.signedSum sign k z‖ := by
        have hpad := hpad_le z hz_norm
        have hsub := norm_sub_norm_le (Complex.exp (((2 * m : ℕ) : ℝ) * θs ξ * Complex.I) * Pcenter m t ε (θs ξ))
          (-(∑ j ∈ Finset.Ico (4 * m + 1) (2 * k), z ^ j))
        rw [sub_neg_eq_add, ← hdecomp, hshift_norm, norm_neg] at hsub
        linarith only [hsub, hpad]
      have hsqrt_big : 256 * TwoOrbitCosine.c474 ≤ Real.sqrt m := by
        have hK1_le : (K1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show K1 ≤ m by omega)
        have hsq : (256 * TwoOrbitCosine.c474) ^ 2 ≤ (m : ℝ) := le_trans hK1.le hK1_le
        calc 256 * TwoOrbitCosine.c474 = Real.sqrt ((256 * TwoOrbitCosine.c474) ^ 2) :=
              (Real.sqrt_sq (mul_nonneg (by norm_num) TwoOrbitCosine.c474_pos.le)).symm
          _ ≤ Real.sqrt m := Real.sqrt_le_sqrt hsq
      have h128_le : (128 : ℝ) ≤ (1 / TwoOrbitCosine.c474) * Real.sqrt m := by
        have h1 : (256 : ℝ) ≤ (1 / TwoOrbitCosine.c474) * Real.sqrt m := by
          rw [one_div, inv_mul_eq_div, le_div_iff₀ TwoOrbitCosine.c474_pos]; exact hsqrt_big
        linarith only [h1]
      have hθ_in : TwoOrbitFejer.foldAngle (θs ξ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
        apply TwoOrbitFejer.foldAngle_mem
        · dsimp only [θs]; positivity
        · dsimp only [θs]
          have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by dsimp [n]; omega)
          rw [div_le_iff₀ hn_pos]
          have hle : (ξ.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast ξ.isLt.le
          nlinarith only [hle, Real.pi_pos]
      by_cases hbad : ∃ ab ∈ runs,
          TwoOrbitFejer.foldAngle (θs ξ) ∈
            Set.Icc ((ab.1 : ℝ) * (16 * Real.pi / (m : ℝ))) ((ab.2 : ℝ) * (16 * Real.pi / (m : ℝ)))
      · have hso := hodd_good ξ hbad
        have hse := even_sine_rem_bound m t (by omega) hT_hi (θs ξ)
        have him := (Pcenter_eval m t ε hT_hi (θs ξ)).2
        dsimp only at hse him
        have him_ge : 350 * Real.sqrt m ≤ |(Pcenter m t ε (θs ξ)).im| := by
          rw [him]
          set Se : ℝ := ∑ l ∈ (Finset.Icc 1 m) \ (Finset.Ico (2 ^ (t + 10)) (2 ^ (t + 10) + 2 ^ t) ∪
            Finset.Ico (2 * 2 ^ (t + 10)) (2 * 2 ^ (t + 10) + 2 ^ t)),
            TwoOrbitCosine.rsSeq l * Real.sin (2 * (l : ℝ) * θs ξ)
          set So : ℝ := ∑ j : Fin m, ε j * Real.sin (((2 * j.val + 1 : ℕ) : ℝ) * θs ξ)
          have hrev := abs_sub_abs_le_abs_sub (2 * So) (-(2 * Se))
          rw [sub_neg_eq_add, add_comm (2 * So) (2 * Se), abs_neg, abs_mul, abs_mul,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hrev
          linarith only [hrev, hso, hse]
        have hge1 : (1 : ℝ) ≤ TwoOrbitCosine.c474 := by
          unfold TwoOrbitCosine.c474
          have h16 : (1 : ℝ) ≤ (16 : ℝ) ^ 18 := one_le_pow₀ (by norm_num)
          have h32 : (1 : ℝ) ≤ (16 : ℝ) ^ 32 := one_le_pow₀ (by norm_num)
          have h3 : (1 : ℝ) ≤ (8 * (16 : ℝ) ^ 32) ^ 3 := one_le_pow₀ (by linarith only [h32])
          nlinarith only [h16, h3]
        have hinv_le : 1 / TwoOrbitCosine.c474 ≤ 1 := by
          rw [div_le_one TwoOrbitCosine.c474_pos]; exact hge1
        have hsqrt_le : (1 / TwoOrbitCosine.c474) * Real.sqrt m ≤ Real.sqrt m := by
          calc (1 / TwoOrbitCosine.c474) * Real.sqrt m ≤ 1 * Real.sqrt m :=
                mul_le_mul_of_nonneg_right hinv_le (Real.sqrt_nonneg m)
            _ = Real.sqrt m := one_mul _
        have hnorm_ge := him_ge.trans (Complex.abs_im_le_norm _)
        linarith only [htri, hnorm_ge, h128_le, hsqrt_le]
      · push Not at hbad
        have hcos := hcos_good (TwoOrbitFejer.foldAngle (θs ξ)) hθ_in hbad
        rw [cosPoly_foldAngle] at hcos
        have hre := (Pcenter_eval m t ε hT_hi (θs ξ)).1
        have hre_ge : 2 * ((1 / TwoOrbitCosine.c474) * Real.sqrt m) - 1 ≤ |(Pcenter m t ε (θs ξ)).re| := by
          rw [hre]
          have hrev := abs_sub_abs_le_abs_sub (2 * TwoOrbitCosine.cosPoly t (θs ξ)) (-1)
          rw [sub_neg_eq_add, add_comm, abs_neg, abs_one, abs_mul,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hrev
          linarith only [hrev, hcos]
        have hnorm_ge := hre_ge.trans (Complex.abs_re_le_norm _)
        linarith only [htri, hnorm_ge, h128_le]
    have hsqrt_nm : Real.sqrt n ≤ 3 * Real.sqrt m := by
      have hsq : (n : ℝ) ≤ (3 * Real.sqrt m) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
        have : (n : ℝ) ≤ 7 * (m : ℝ) := by exact_mod_cast hn_le_7m
        linarith only [this, show (0 : ℝ) ≤ (m : ℝ) by positivity]
      calc Real.sqrt n ≤ Real.sqrt ((3 * Real.sqrt m) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = 3 * Real.sqrt m := Real.sqrt_sq (by positivity)
    have henv := TwoOrbitFlatSeed.lowerEnvelope sign k z hz_norm
    rw [← hhat_S0, ← hhat_I, max_comm] at henv
    have h1 : (1 / (3 * TwoOrbitCosine.c474)) * Real.sqrt n ≤
        (1 / TwoOrbitCosine.c474) * Real.sqrt m := by
      have hc := TwoOrbitCosine.c474_pos
      have h2 := mul_le_mul_of_nonneg_left hsqrt_nm (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hc.le))
      have h3 : 1 / (3 * TwoOrbitCosine.c474) * (3 * Real.sqrt m) = 1 / TwoOrbitCosine.c474 * Real.sqrt m := by
        field_simp [hc.ne']
      linarith only [h2, h3]
    have h4 : (1 / (12 * TwoOrbitCosine.c474)) * Real.sqrt n * 4 = (1 / (3 * TwoOrbitCosine.c474)) * Real.sqrt n := by
      field_simp [TwoOrbitCosine.c474_pos.ne']; ring
    linarith only [h1, hPcenter_ge, henv, h4]

/-! ### Bridge B: Probabilistic perturbation from initial seed `S₀` to exact-size seed `S` -/

private lemma exp_half_le_two : Real.exp ((1 : ℝ) / 2) ≤ 2 := by
  have h1 : (1 : ℝ) / 2 ≤ Real.exp (-(1 : ℝ) / 2) := by
    have := Real.add_one_le_exp (-(1 : ℝ) / 2); linarith
  have hmul : Real.exp ((1 : ℝ) / 2) * Real.exp (-(1 : ℝ) / 2) = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos ((1 : ℝ) / 2)]

private lemma two_pow_ge_mul_pow (C r : ℕ) :
    ∃ L₁ : ℕ, ∀ L : ℕ, L₁ ≤ L → (C : ℝ) * (L : ℝ) ^ r ≤ (2 : ℝ) ^ L := by
  refine ⟨C * 2 ^ (r + 1) * (r + 1).factorial, ?_⟩
  intro L hL
  have hexp_le : Real.exp ((L : ℝ) / 2) ≤ (2 : ℝ) ^ L := by
    have h1 : Real.exp ((L : ℝ) / 2) = Real.exp ((1 : ℝ) / 2) ^ L := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [h1]
    exact pow_le_pow_left₀ (Real.exp_pos _).le exp_half_le_two L
  have hser := Real.pow_div_factorial_le_exp ((L : ℝ) / 2) (by positivity) (r + 1)
  have hfact_pos : (0 : ℝ) < ((r + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (r + 1)
  have hL_ge : (C : ℝ) * (2 : ℝ) ^ (r + 1) * ((r + 1).factorial : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast hL
  have hpow_le : (C : ℝ) * (L : ℝ) ^ r ≤ ((L : ℝ) / 2) ^ (r + 1) / ((r + 1).factorial : ℝ) := by
    rw [le_div_iff₀ hfact_pos, div_pow, pow_succ]
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (r + 1) := by positivity
    rw [le_div_iff₀ h2pos]
    have hmul := mul_le_mul_of_nonneg_left hL_ge (pow_nonneg (Nat.cast_nonneg L) r)
    linarith only [hmul, show (C : ℝ) * (L : ℝ) ^ r * ((r + 1).factorial : ℝ) * (2 : ℝ) ^ (r + 1) =
      (L : ℝ) ^ r * ((C : ℝ) * (2 : ℝ) ^ (r + 1) * ((r + 1).factorial : ℝ)) by ring]
  exact hpow_le.trans (hser.trans hexp_le)

private lemma nat_choose_le_pow (n r : ℕ) : n.choose r ≤ n ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 : n.choose (r + 1) * (r + 1) = n.choose r * (n - r) := Nat.choose_succ_right_eq n r
    have h2 : n.choose (r + 1) ≤ n.choose (r + 1) * (r + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos r)
    calc n.choose (r + 1) ≤ n.choose r * (n - r) := h1 ▸ h2
      _ ≤ n ^ r * n := Nat.mul_le_mul ih (Nat.sub_le n r)
      _ = n ^ (r + 1) := by rw [pow_succ]

private lemma sum_biUnion_le_nonneg {α ι : Type*} [DecidableEq α] (s : Finset ι)
    (f : ι → Finset α) (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    ∑ x ∈ s.biUnion f, w x ≤ ∑ i ∈ s, ∑ x ∈ f i, w x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hui := Finset.sum_union_inter (s₁ := f a) (s₂ := s.biUnion f) (f := w)
    have hinter_nn : 0 ≤ ∑ x ∈ f a ∩ s.biUnion f, w x := Finset.sum_nonneg fun x _ => hw x
    linarith only [hui, hinter_nn, ih]

private lemma prod_le_prod_nonneg {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.prod_insert hx]
    exact mul_le_mul (hfg x (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hfg i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (le_trans (hf x (Finset.mem_insert_self _ _)) (hfg x (Finset.mem_insert_self _ _)))

private lemma nat_le_two_exp_log (n L : ℕ) (hn_lt : n < 2 ^ (L + 1)) :
    (n : ℝ) ≤ 2 * Real.exp (L : ℝ) := by
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hpow : (2 : ℝ) ^ L ≤ Real.exp (L : ℝ) := by
    have := pow_le_pow_left₀ (by norm_num) h2e L
    rwa [← Real.exp_nat_mul, mul_one] at this
  have hn2 : (n : ℝ) ≤ 2 * (2 : ℝ) ^ L := by
    have : n ≤ 2 * 2 ^ L := by rw [← pow_succ']; exact hn_lt.le
    exact_mod_cast this
  linarith only [hn2, hpow]

/-- Helper for Bridge B: union bound on Fourier concentration failure across all `ξ : Fin n`. -/
private lemma perturb_fourier_tail_lt (n L : ℕ) [NeZero n] (p : Fin n → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (b : ℝ) (hb_pos : 0 < b) (hL_100 : 100 ≤ L) (hL_four' : 40000 / b ^ 2 < (L : ℝ))
    (hn_lt_pow : n < 2 ^ (L + 1))
    (hvar : ∑ i : Fin n, p i * (1 - p i) ≤ 4 * (n : ℝ) / (L : ℝ) ^ 2)
    (ht_le_V : (b / 8) * Real.sqrt n ≤ 4 * (n : ℝ) / (L : ℝ) ^ 2) :
    let t : ℝ := (b / 8) * Real.sqrt n
    let BadRe (ξ : Fin n) := (Finset.univ : Finset (Fin n)).powerset.filter (fun S =>
      t ≤ |∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0) - p i) * (TwoOrbitMiddle.chi n ξ i).re|)
    let BadIm (ξ : Fin n) := (Finset.univ : Finset (Fin n)).powerset.filter (fun S =>
      t ≤ |∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0) - p i) * (TwoOrbitMiddle.chi n ξ i).im|)
    let BadFour := (Finset.univ : Finset (Fin n)).biUnion (fun ξ => BadRe ξ ∪ BadIm ξ)
    ∑ S ∈ BadFour, TwoOrbitPerturb.probWU p Finset.univ S < 1 / (3 * ((n : ℝ) + 1) ^ 2) := by
  classical
  intro t BadRe BadIm BadFour
  set V : ℝ := 4 * (n : ℝ) / (L : ℝ) ^ 2
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (NeZero.pos n)
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hV_pos : 0 < V := by dsimp [V]; positivity
  have hWnn : ∀ S : Finset (Fin n), 0 ≤ TwoOrbitPerturb.probWU p Finset.univ S :=
    fun S => TwoOrbitPerturb.probWU_nonneg p hp0 hp1 Finset.univ S
  have hfour_exp : Real.exp (-(t ^ 2 / (4 * V))) ≤ Real.exp (-(30 * (L : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have heq : t ^ 2 / (4 * V) = (b ^ 2 / 1024) * (L : ℝ) ^ 2 := by
      dsimp only [t, V]
      rw [mul_pow, Real.sq_sqrt hn_pos.le]
      field_simp [hn_pos.ne', hL_pos.ne']; ring
    rw [heq]
    have h1 : (40000 : ℝ) < (L : ℝ) * b ^ 2 := (div_lt_iff₀ (sq_pos_of_pos hb_pos)).mp hL_four'
    have h2 : 30 * (L : ℝ) ≤ (b ^ 2 / 1024) * (L : ℝ) ^ 2 := by nlinarith only [h1, hL_pos]
    linarith only [h2]
  have hsum1 : ∑ S ∈ BadFour, TwoOrbitPerturb.probWU p Finset.univ S ≤
      ∑ ξ : Fin n, (∑ S ∈ BadRe ξ, TwoOrbitPerturb.probWU p Finset.univ S +
        ∑ S ∈ BadIm ξ, TwoOrbitPerturb.probWU p Finset.univ S) := by
    refine (sum_biUnion_le_nonneg _ _ _ hWnn).trans (Finset.sum_le_sum fun ξ _ => ?_)
    have hui := Finset.sum_union_inter (s₁ := BadRe ξ) (s₂ := BadIm ξ)
      (f := TwoOrbitPerturb.probWU p Finset.univ)
    have hinter_nn : 0 ≤ ∑ S ∈ BadRe ξ ∩ BadIm ξ, TwoOrbitPerturb.probWU p Finset.univ S :=
      Finset.sum_nonneg fun S _ => hWnn S
    linarith only [hui, hinter_nn]
  have hsum2 : ∑ ξ : Fin n, (∑ S ∈ BadRe ξ, TwoOrbitPerturb.probWU p Finset.univ S +
        ∑ S ∈ BadIm ξ, TwoOrbitPerturb.probWU p Finset.univ S) ≤
      4 * (n : ℝ) * Real.exp (-(30 * (L : ℝ))) := by
    have hterm : ∀ ξ : Fin n,
        ∑ S ∈ BadRe ξ, TwoOrbitPerturb.probWU p Finset.univ S +
        ∑ S ∈ BadIm ξ, TwoOrbitPerturb.probWU p Finset.univ S ≤
          4 * Real.exp (-(30 * (L : ℝ))) := by
      intro ξ
      have hre := TwoOrbitPerturb.sum_probWU_linear_tail p (fun i => (TwoOrbitMiddle.chi n ξ i).re)
        Finset.univ (fun i _ => hp0 i) (fun i _ => hp1 i)
        (fun i _ => (Complex.abs_re_le_norm _).trans_eq (TwoOrbitMiddle.norm_chi n ξ i))
        hV_pos hvar (by positivity) ht_le_V
      have him := TwoOrbitPerturb.sum_probWU_linear_tail p (fun i => (TwoOrbitMiddle.chi n ξ i).im)
        Finset.univ (fun i _ => hp0 i) (fun i _ => hp1 i)
        (fun i _ => (Complex.abs_im_le_norm _).trans_eq (TwoOrbitMiddle.norm_chi n ξ i))
        hV_pos hvar (by positivity) ht_le_V
      linarith only [hre, him, hfour_exp]
    calc _ ≤ ∑ _ξ : Fin n, (4 * Real.exp (-(30 * (L : ℝ)))) := Finset.sum_le_sum fun ξ _ => hterm ξ
      _ = 4 * (n : ℝ) * Real.exp (-(30 * (L : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hn_exp : (n : ℝ) ≤ 2 * Real.exp (L : ℝ) := nat_le_two_exp_log n L hn_lt_pow
  have hlt_num : 4 * (n : ℝ) * Real.exp (-(30 * (L : ℝ))) < 1 / (3 * ((n : ℝ) + 1) ^ 2) := by
    rw [lt_div_iff₀ (by positivity), Real.exp_neg]
    have h1 : 4 * (n : ℝ) * (3 * ((n : ℝ) + 1) ^ 2) ≤ 384 * Real.exp (3 * (L : ℝ)) := by
      have hn1 : (n : ℝ) + 1 ≤ 4 * Real.exp (L : ℝ) := by
        have : (1 : ℝ) ≤ Real.exp (L : ℝ) := Real.one_le_exp hL_pos.le
        linarith only [hn_exp, this]
      have h3eq : Real.exp (3 * (L : ℝ)) = Real.exp (L : ℝ) ^ 3 := by
        simpa using Real.exp_nat_mul (L : ℝ) 3
      rw [h3eq]
      have hsq : ((n : ℝ) + 1) ^ 2 ≤ (4 * Real.exp (L : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hn1 2
      have hmul := mul_le_mul hn_exp hsq (by positivity) (by positivity)
      nlinarith only [hmul]
    have h384 : (384 : ℝ) * Real.exp (3 * (L : ℝ)) < Real.exp (30 * (L : ℝ)) := by
      have h384_le : (384 : ℝ) < Real.exp (27 * (L : ℝ)) := by
        have h27 : (2700 : ℝ) ≤ 27 * (L : ℝ) := by
          have : (100 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_100
          linarith only [this]
        have := Real.add_one_le_exp (27 * (L : ℝ))
        linarith only [this, h27]
      have hmul := mul_lt_mul_of_pos_right h384_le (Real.exp_pos (3 * (L : ℝ)))
      rw [← Real.exp_add] at hmul
      have harg : 27 * (L : ℝ) + 3 * (L : ℝ) = 30 * (L : ℝ) := by ring
      rw [harg] at hmul; linarith only [hmul]
    have hpos := Real.exp_pos (30 * (L : ℝ))
    have hrw : 4 * (n : ℝ) * (Real.exp (30 * (L : ℝ)))⁻¹ * (3 * ((n : ℝ) + 1) ^ 2) =
        (4 * (n : ℝ) * (3 * ((n : ℝ) + 1) ^ 2)) / Real.exp (30 * (L : ℝ)) := by ring
    rw [hrw, div_lt_one hpos]
    linarith only [h1, h384]
  exact lt_of_le_of_lt (hsum1.trans hsum2) hlt_num

/-- Helper for Bridge B: union bound on small-row cover/miss failure across all `2 ≤ |A| ≤ M'`. -/
private lemma perturb_small_rows_tail_lt (n L M' : ℕ) [NeZero n] (p : Fin n → ℝ)
    (hp_lo : ∀ i : Fin n, 1 / (4 * (L : ℝ) ^ 2) ≤ p i)
    (hp_hi : ∀ i : Fin n, p i ≤ 1 - 1 / (4 * (L : ℝ) ^ 2))
    (hL_100 : 100 ≤ L) (hL_96 : 96 * M' * 2 ^ M' + 100 ≤ L)
    (hn_lt_pow : n < 2 ^ (L + 1)) (hM'2 : 2 ≤ M')
    (hpoly2 : ((M' ^ 2 * 4 ^ M' * (2 * M' + 10) : ℕ) : ℝ) * (L : ℝ) ^ (2 * M' + 1) ≤ (n : ℝ))
    (SmallRows : Finset (Finset (Fin n)))
    (hSmall_def : SmallRows = (Finset.univ : Finset (Fin n)).powerset.filter (fun A => 2 ≤ A.card ∧ A.card ≤ M'))
    (BOf : ∀ A : Finset (Fin n), A ∈ SmallRows → Finset (Finset (Fin n)))
    (hB_trans : ∀ A hA, ∀ b ∈ BOf A hA, ∃ t : Fin n, b = A.image (fun x => x + t))
    (hB_pair : ∀ A hA, (BOf A hA : Set (Finset (Fin n))).Pairwise Disjoint)
    (hB_card : ∀ A hA, n ≤ (BOf A hA).card * M' ^ 2) :
    let BadCov (A : {A // A ∈ SmallRows}) :=
      (Finset.univ : Finset (Fin n)).powerset.filter (fun S => ∀ b ∈ BOf A.1 A.2, ¬ (b ⊆ S))
    let BadMiss (A : {A // A ∈ SmallRows}) :=
      (Finset.univ : Finset (Fin n)).powerset.filter (fun S => ∀ b ∈ BOf A.1 A.2, ¬ Disjoint b S)
    let BadSmall := SmallRows.attach.biUnion (fun A => BadCov A ∪ BadMiss A)
    ∑ S ∈ BadSmall, TwoOrbitPerturb.probWU p Finset.univ S < 1 / (3 * ((n : ℝ) + 1) ^ 2) := by
  classical
  intro BadCov BadMiss BadSmall
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (NeZero.pos n)
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hL2_ge : (10000 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (100 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_100
    nlinarith only [this]
  have hp0 : ∀ i : Fin n, 0 ≤ p i := fun i => le_trans (by positivity) (hp_lo i)
  have hp1 : ∀ i : Fin n, p i ≤ 1 := fun i => le_trans (hp_hi i) (by linarith [show (0 : ℝ) ≤ 1 / (4 * (L : ℝ) ^ 2) by positivity])
  have hWnn : ∀ S : Finset (Fin n), 0 ≤ TwoOrbitPerturb.probWU p Finset.univ S :=
    fun S => TwoOrbitPerturb.probWU_nonneg p hp0 hp1 Finset.univ S
  set q : ℝ := 1 / (4 * (L : ℝ) ^ 2)
  have hq_pos : 0 < q := by dsimp [q]; positivity
  have hq_le1 : q ≤ 1 := by
    dsimp only [q]; rw [div_le_one (by positivity)]; linarith only [hL2_ge]
  have hqM'_eq : q ^ M' = 1 / ((4 : ℝ) ^ M' * (L : ℝ) ^ (2 * M')) := by
    dsimp only [q]; rw [div_pow, one_pow, mul_pow, ← pow_mul]
  have hsmall_each : ∀ A : {A // A ∈ SmallRows},
      (∑ S ∈ BadCov A, TwoOrbitPerturb.probWU p Finset.univ S) +
      (∑ S ∈ BadMiss A, TwoOrbitPerturb.probWU p Finset.univ S) ≤
        2 * Real.exp (-((2 * (M' : ℝ) + 10) * (L : ℝ))) := by
    intro A
    have hAM' : A.1.card ≤ M' := by
      have hA : A.1 ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun A => 2 ≤ A.card ∧ A.card ≤ M') :=
        hSmall_def ▸ A.2
      exact (Finset.mem_filter.mp hA).2.2
    have hcard_b : ∀ b ∈ BOf A.1 A.2, b.card ≤ M' := by
      intro b hb
      obtain ⟨t, rfl⟩ := hB_trans A.1 A.2 b hb
      exact Finset.card_image_le.trans hAM'
    have hrate : (2 * (M' : ℝ) + 10) * (L : ℝ) ≤ ((BOf A.1 A.2).card : ℝ) * q ^ M' := by
      have hBc : (n : ℝ) / (M' : ℝ) ^ 2 ≤ ((BOf A.1 A.2).card : ℝ) := by
        rw [div_le_iff₀ (by exact_mod_cast (show 0 < M' ^ 2 by positivity))]
        exact_mod_cast hB_card A.1 A.2
      have hstep1 : ((n : ℝ) / (M' : ℝ) ^ 2) * q ^ M' ≤ ((BOf A.1 A.2).card : ℝ) * q ^ M' :=
        mul_le_mul_of_nonneg_right hBc (pow_nonneg hq_pos.le M')
      have hstep2 : (2 * (M' : ℝ) + 10) * (L : ℝ) ≤ ((n : ℝ) / (M' : ℝ) ^ 2) * q ^ M' := by
        rw [hqM'_eq]
        have hM'pos : (0 : ℝ) < (M' : ℝ) := by exact_mod_cast (show 0 < M' by omega)
        have hden_pos : (0 : ℝ) < (M' : ℝ) ^ 2 * ((4 : ℝ) ^ M' * (L : ℝ) ^ (2 * M')) := by positivity
        have hrw : ((n : ℝ) / (M' : ℝ) ^ 2) * (1 / ((4 : ℝ) ^ M' * (L : ℝ) ^ (2 * M'))) =
            (n : ℝ) / ((M' : ℝ) ^ 2 * ((4 : ℝ) ^ M' * (L : ℝ) ^ (2 * M'))) := by ring
        rw [hrw, le_div_iff₀ hden_pos]
        have hC_cast : ((M' ^ 2 * 4 ^ M' * (2 * M' + 10) : ℕ) : ℝ) =
            (M' : ℝ) ^ 2 * (4 : ℝ) ^ M' * (2 * (M' : ℝ) + 10) := by push_cast; ring
        have hL_pow : (L : ℝ) ^ (2 * M' + 1) = (L : ℝ) * (L : ℝ) ^ (2 * M') := by rw [pow_succ']
        rw [hC_cast, hL_pow] at hpoly2
        linarith only [hpoly2, show (2 * (M' : ℝ) + 10) * (L : ℝ) * ((M' : ℝ) ^ 2 * ((4 : ℝ) ^ M' * (L : ℝ) ^ (2 * M'))) =
          (M' : ℝ) ^ 2 * (4 : ℝ) ^ M' * (2 * (M' : ℝ) + 10) * ((L : ℝ) * (L : ℝ) ^ (2 * M')) by ring]
      exact hstep2.trans hstep1
    have hcov : ∑ S ∈ BadCov A, TwoOrbitPerturb.probWU p Finset.univ S ≤
        Real.exp (-((2 * (M' : ℝ) + 10) * (L : ℝ))) := by
      have hcov_eq : ∑ S ∈ BadCov A, TwoOrbitPerturb.probWU p Finset.univ S =
          ∏ b ∈ BOf A.1 A.2, (1 - ∏ i ∈ b, p i) := by
        dsimp only [BadCov]
        convert TwoOrbitPerturb.sum_probWU_no_cover_eq p (BOf A.1 A.2) Finset.univ
          (fun _ _ => Finset.subset_univ _) (hB_pair A.1 A.2)
      rw [hcov_eq]
      have hterm : ∀ b ∈ BOf A.1 A.2, 1 - ∏ i ∈ b, p i ≤ Real.exp (-(q ^ M')) := by
        intro b hb
        have hprod_ge : q ^ M' ≤ ∏ i ∈ b, p i := by
          have h1 : q ^ M' ≤ q ^ b.card := pow_le_pow_of_le_one hq_pos.le hq_le1 (hcard_b b hb)
          have h2 : q ^ b.card ≤ ∏ i ∈ b, p i := by
            rw [← Finset.prod_const]
            exact prod_le_prod_nonneg b _ _ (fun _ _ => hq_pos.le) (fun i _ => hp_lo i)
          exact h1.trans h2
        calc 1 - ∏ i ∈ b, p i ≤ 1 - q ^ M' := by linarith only [hprod_ge]
          _ ≤ Real.exp (-(q ^ M')) := by linarith [Real.add_one_le_exp (-(q ^ M'))]
      have hprod_le : ∏ b ∈ BOf A.1 A.2, (1 - ∏ i ∈ b, p i) ≤
          ∏ _b ∈ BOf A.1 A.2, Real.exp (-(q ^ M')) :=
        prod_le_prod_nonneg (BOf A.1 A.2) _ _ (fun b _ => by
          have h1 : ∏ i ∈ b, p i ≤ 1 := by
            simpa only [Finset.prod_const_one] using
              prod_le_prod_nonneg b p (fun _ => (1 : ℝ)) (fun i _ => hp0 i) (fun i _ => hp1 i)
          linarith only [h1]) hterm
      calc _ ≤ ∏ _b ∈ BOf A.1 A.2, Real.exp (-(q ^ M')) := hprod_le
        _ = Real.exp (-(((BOf A.1 A.2).card : ℝ) * q ^ M')) := by
            rw [Finset.prod_const, ← Real.exp_nat_mul]; congr 1; ring
        _ ≤ Real.exp (-((2 * (M' : ℝ) + 10) * (L : ℝ))) :=
            Real.exp_le_exp.mpr (by linarith only [hrate])
    have hmiss : ∑ S ∈ BadMiss A, TwoOrbitPerturb.probWU p Finset.univ S ≤
        Real.exp (-((2 * (M' : ℝ) + 10) * (L : ℝ))) := by
      have hmiss_eq : ∑ S ∈ BadMiss A, TwoOrbitPerturb.probWU p Finset.univ S =
          ∏ b ∈ BOf A.1 A.2, (1 - ∏ i ∈ b, (1 - p i)) := by
        dsimp only [BadMiss]
        convert TwoOrbitPerturb.sum_probWU_no_miss_eq p (BOf A.1 A.2) Finset.univ
          (fun _ _ => Finset.subset_univ _) (hB_pair A.1 A.2)
      rw [hmiss_eq]
      have hterm : ∀ b ∈ BOf A.1 A.2, 1 - ∏ i ∈ b, (1 - p i) ≤ Real.exp (-(q ^ M')) := by
        intro b hb
        have hprod_ge : q ^ M' ≤ ∏ i ∈ b, (1 - p i) := by
          have h1 : q ^ M' ≤ q ^ b.card := pow_le_pow_of_le_one hq_pos.le hq_le1 (hcard_b b hb)
          have h2 : q ^ b.card ≤ ∏ i ∈ b, (1 - p i) := by
            rw [← Finset.prod_const]
            exact prod_le_prod_nonneg b _ _ (fun _ _ => hq_pos.le) (fun i _ => by linarith only [hp_hi i])
          exact h1.trans h2
        calc 1 - ∏ i ∈ b, (1 - p i) ≤ 1 - q ^ M' := by linarith only [hprod_ge]
          _ ≤ Real.exp (-(q ^ M')) := by linarith [Real.add_one_le_exp (-(q ^ M'))]
      have hprod_le : ∏ b ∈ BOf A.1 A.2, (1 - ∏ i ∈ b, (1 - p i)) ≤
          ∏ _b ∈ BOf A.1 A.2, Real.exp (-(q ^ M')) :=
        prod_le_prod_nonneg (BOf A.1 A.2) _ _ (fun b _ => by
          have h1 : ∏ i ∈ b, (1 - p i) ≤ 1 := by
            simpa only [Finset.prod_const_one] using
              prod_le_prod_nonneg b (fun i => 1 - p i) (fun _ => (1 : ℝ))
                (fun i _ => by linarith only [hp1 i]) (fun i _ => by linarith only [hp0 i])
          linarith only [h1]) hterm
      calc _ ≤ ∏ _b ∈ BOf A.1 A.2, Real.exp (-(q ^ M')) := hprod_le
        _ = Real.exp (-(((BOf A.1 A.2).card : ℝ) * q ^ M')) := by
            rw [Finset.prod_const, ← Real.exp_nat_mul]; congr 1; ring
        _ ≤ Real.exp (-((2 * (M' : ℝ) + 10) * (L : ℝ))) :=
            Real.exp_le_exp.mpr (by linarith only [hrate])
    linarith only [hcov, hmiss]
  have hsmall_card : SmallRows.card ≤ M' * n ^ M' := by
    have hsub : SmallRows ⊆ (Finset.Icc 2 M').biUnion (fun r => (Finset.univ : Finset (Fin n)).powersetCard r) := by
      intro A hA
      rw [hSmall_def] at hA
      rcases Finset.mem_filter.mp hA with ⟨_, h2, hle⟩
      exact Finset.mem_biUnion.mpr ⟨A.card, Finset.mem_Icc.mpr ⟨h2, hle⟩,
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
    calc SmallRows.card
        ≤ ((Finset.Icc 2 M').biUnion (fun r => (Finset.univ : Finset (Fin n)).powersetCard r)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ r ∈ Finset.Icc 2 M', ((Finset.univ : Finset (Fin n)).powersetCard r).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ Finset.Icc 2 M', n ^ M' := by
          refine Finset.sum_le_sum fun r hr => ?_
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          exact (nat_choose_le_pow n r).trans (Nat.pow_le_pow_right (NeZero.pos n) (Finset.mem_Icc.mp hr).2)
      _ = (Finset.Icc 2 M').card * n ^ M' := by simp
      _ ≤ M' * n ^ M' := Nat.mul_le_mul_right _ (by rw [Nat.card_Icc]; omega)
  have hsum1 : ∑ S ∈ BadSmall, TwoOrbitPerturb.probWU p Finset.univ S ≤
      (SmallRows.card : ℝ) * (2 * Real.exp (-((2 * (M' : ℝ) + 10) * (L : ℝ)))) := by
    calc ∑ S ∈ BadSmall, TwoOrbitPerturb.probWU p Finset.univ S
        ≤ ∑ A ∈ SmallRows.attach, ∑ S ∈ BadCov A ∪ BadMiss A, TwoOrbitPerturb.probWU p Finset.univ S :=
          sum_biUnion_le_nonneg _ _ _ hWnn
      _ ≤ ∑ A ∈ SmallRows.attach, ((∑ S ∈ BadCov A, TwoOrbitPerturb.probWU p Finset.univ S) +
            (∑ S ∈ BadMiss A, TwoOrbitPerturb.probWU p Finset.univ S)) := by
          refine Finset.sum_le_sum fun A _ => ?_
          have hui := Finset.sum_union_inter (s₁ := BadCov A) (s₂ := BadMiss A)
            (f := TwoOrbitPerturb.probWU p Finset.univ)
          have hinter_nn : 0 ≤ ∑ S ∈ BadCov A ∩ BadMiss A, TwoOrbitPerturb.probWU p Finset.univ S :=
            Finset.sum_nonneg fun S _ => hWnn S
          linarith only [hui, hinter_nn]
      _ ≤ ∑ _A ∈ SmallRows.attach, (2 * Real.exp (-((2 * (M' : ℝ) + 10) * (L : ℝ)))) :=
          Finset.sum_le_sum fun A _ => hsmall_each A
      _ = (SmallRows.card : ℝ) * (2 * Real.exp (-((2 * (M' : ℝ) + 10) * (L : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
  have hsc_r : (SmallRows.card : ℝ) ≤ (M' : ℝ) * (n : ℝ) ^ M' := by exact_mod_cast hsmall_card
  have hsum2 : (SmallRows.card : ℝ) * (2 * Real.exp (-((2 * (M' : ℝ) + 10) * (L : ℝ)))) ≤
      2 * (M' : ℝ) * (n : ℝ) ^ M' * Real.exp (-((2 * (M' : ℝ) + 10) * (L : ℝ))) := by
    have := mul_le_mul_of_nonneg_right hsc_r (by positivity : 0 ≤ 2 * Real.exp (-((2 * (M' : ℝ) + 10) * (L : ℝ))))
    linarith only [this, show (M' : ℝ) * (n : ℝ) ^ M' * (2 * Real.exp (-((2 * (M' : ℝ) + 10) * (L : ℝ)))) =
      2 * (M' : ℝ) * (n : ℝ) ^ M' * Real.exp (-((2 * (M' : ℝ) + 10) * (L : ℝ))) by ring]
  have hn_exp : (n : ℝ) ≤ 2 * Real.exp (L : ℝ) := nat_le_two_exp_log n L hn_lt_pow
  have hlt_num : 2 * (M' : ℝ) * (n : ℝ) ^ M' * Real.exp (-((2 * (M' : ℝ) + 10) * (L : ℝ))) <
      1 / (3 * ((n : ℝ) + 1) ^ 2) := by
    rw [lt_div_iff₀ (by positivity), Real.exp_neg]
    have hn1 : (n : ℝ) + 1 ≤ 4 * Real.exp (L : ℝ) := by
      have : (1 : ℝ) ≤ Real.exp (L : ℝ) := Real.one_le_exp hL_pos.le
      linarith only [hn_exp, this]
    have hnM : (n : ℝ) ^ M' ≤ (2 : ℝ) ^ M' * Real.exp ((M' : ℝ) * (L : ℝ)) := by
      calc (n : ℝ) ^ M' ≤ (2 * Real.exp (L : ℝ)) ^ M' := pow_le_pow_left₀ hn_pos.le hn_exp M'
        _ = (2 : ℝ) ^ M' * Real.exp (L : ℝ) ^ M' := mul_pow _ _ _
        _ = (2 : ℝ) ^ M' * Real.exp ((M' : ℝ) * (L : ℝ)) := by rw [← Real.exp_nat_mul]
    have hn1sq : ((n : ℝ) + 1) ^ 2 ≤ 16 * Real.exp (2 * (L : ℝ)) := by
      calc ((n : ℝ) + 1) ^ 2 ≤ (4 * Real.exp (L : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hn1 2
        _ = 16 * Real.exp (L : ℝ) ^ 2 := by ring
        _ = 16 * Real.exp (2 * (L : ℝ)) := by rw [← Real.exp_nat_mul]; norm_num
    have hprod_le : 2 * (M' : ℝ) * (n : ℝ) ^ M' * (3 * ((n : ℝ) + 1) ^ 2) ≤
        (96 * (M' : ℝ) * (2 : ℝ) ^ M') * Real.exp (((M' : ℝ) + 2) * (L : ℝ)) := by
      have hmul := mul_le_mul hnM hn1sq (by positivity) (by positivity)
      have hmul' := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ 6 * (M' : ℝ))
      have hexp_add : Real.exp ((M' : ℝ) * (L : ℝ)) * Real.exp (2 * (L : ℝ)) =
          Real.exp (((M' : ℝ) + 2) * (L : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      have hlhs : 2 * (M' : ℝ) * (n : ℝ) ^ M' * (3 * ((n : ℝ) + 1) ^ 2) =
          6 * (M' : ℝ) * ((n : ℝ) ^ M' * ((n : ℝ) + 1) ^ 2) := by ring
      have hrhs : 6 * (M' : ℝ) * ((2 : ℝ) ^ M' * Real.exp ((M' : ℝ) * (L : ℝ)) * (16 * Real.exp (2 * (L : ℝ)))) =
          (96 * (M' : ℝ) * (2 : ℝ) ^ M') * (Real.exp ((M' : ℝ) * (L : ℝ)) * Real.exp (2 * (L : ℝ))) := by ring
      rw [hlhs, ← hexp_add, ← hrhs]
      exact hmul'
    have hcoeff_lt : 96 * (M' : ℝ) * (2 : ℝ) ^ M' < Real.exp (L : ℝ) := by
      have h1 : 96 * (M' : ℝ) * (2 : ℝ) ^ M' + 100 ≤ (L : ℝ) := by exact_mod_cast hL_96
      have h2 := Real.add_one_le_exp (L : ℝ)
      linarith only [h1, h2]
    have hfin : (96 * (M' : ℝ) * (2 : ℝ) ^ M') * Real.exp (((M' : ℝ) + 2) * (L : ℝ)) <
        Real.exp ((2 * (M' : ℝ) + 10) * (L : ℝ)) := by
      have h1 := mul_lt_mul_of_pos_right hcoeff_lt (Real.exp_pos (((M' : ℝ) + 2) * (L : ℝ)))
      rw [← Real.exp_add] at h1
      have h2 : Real.exp ((L : ℝ) + ((M' : ℝ) + 2) * (L : ℝ)) ≤
          Real.exp ((2 * (M' : ℝ) + 10) * (L : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hM'nn : (0 : ℝ) ≤ (M' : ℝ) := Nat.cast_nonneg M'
        nlinarith only [hL_pos, hM'nn]
      exact lt_of_lt_of_le h1 h2
    have hpos := Real.exp_pos ((2 * (M' : ℝ) + 10) * (L : ℝ))
    have hrw : 2 * (M' : ℝ) * (n : ℝ) ^ M' * (Real.exp ((2 * (M' : ℝ) + 10) * (L : ℝ)))⁻¹ *
        (3 * ((n : ℝ) + 1) ^ 2) =
        (2 * (M' : ℝ) * (n : ℝ) ^ M' * (3 * ((n : ℝ) + 1) ^ 2)) /
        Real.exp ((2 * (M' : ℝ) + 10) * (L : ℝ)) := by ring
    rw [hrw, div_lt_one hpos]
    exact lt_of_le_of_lt hprod_le hfin
  exact lt_of_le_of_lt (hsum1.trans hsum2) hlt_num

/-- Helper for Bridge B: transferring the joint Fourier floor from `S₀` to `S`. -/
private lemma perturb_fourier_preserve (n : ℕ) [NeZero n] (I S₀ S : Finset (Fin n))
    (u v b : ℝ) (hb_pos : 0 < b) (h1uv : (3 : ℝ) / 4 ≤ 1 - u - v)
    (ξ : Fin n) (hξ_ne : ξ ≠ 0)
    (hmax : b * Real.sqrt n ≤ max ‖TwoOrbitMiddle.hatSet n I ξ‖ ‖TwoOrbitMiddle.hatSet n S₀ ξ‖)
    (hre_lt : |∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0) - (if i ∈ S₀ then 1 - u else v)) *
        (TwoOrbitMiddle.chi n ξ i).re| < (b / 8) * Real.sqrt n)
    (him_lt : |∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0) - (if i ∈ S₀ then 1 - u else v)) *
        (TwoOrbitMiddle.chi n ξ i).im| < (b / 8) * Real.sqrt n) :
    b ^ 2 / 4 * (n : ℝ) ≤
      ‖TwoOrbitMiddle.hatSet n I ξ‖ ^ 2 + ‖TwoOrbitMiddle.hatSet n S ξ‖ ^ 2 := by
  classical
  let p : Fin n → ℝ := fun i => if i ∈ S₀ then 1 - u else v
  set t : ℝ := (b / 8) * Real.sqrt n
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (NeZero.pos n)
  have hdiff_eq : TwoOrbitMiddle.hatSet n S ξ - ((1 - u - v : ℝ) : ℂ) * TwoOrbitMiddle.hatSet n S₀ ξ =
      ∑ i : Fin n, (((if i ∈ S then (1 : ℝ) else 0) - p i : ℝ) : ℂ) * TwoOrbitMiddle.chi n ξ i := by
    have h1 : TwoOrbitMiddle.hatSet n S ξ =
        ∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0 : ℝ) : ℂ) * TwoOrbitMiddle.chi n ξ i := by
      unfold TwoOrbitMiddle.hatSet
      have hfilt : (Finset.univ : Finset (Fin n)).filter (fun i => i ∈ S) = S := by ext x; simp
      symm
      calc ∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0 : ℝ) : ℂ) * TwoOrbitMiddle.chi n ξ i
          = ∑ i : Fin n, if i ∈ S then TwoOrbitMiddle.chi n ξ i else 0 :=
            Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
        _ = ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => i ∈ S), TwoOrbitMiddle.chi n ξ i := by
            rw [Finset.sum_filter]
        _ = ∑ i ∈ S, TwoOrbitMiddle.chi n ξ i := by rw [hfilt]
    have h2 : ∑ i : Fin n, (p i : ℂ) * TwoOrbitMiddle.chi n ξ i =
        ((1 - u - v : ℝ) : ℂ) * TwoOrbitMiddle.hatSet n S₀ ξ := by
      have hp_eq : ∀ i : Fin n, (p i : ℂ) = ((1 - u - v : ℝ) : ℂ) * (if i ∈ S₀ then 1 else 0) + (v : ℂ) := by
        intro i; dsimp only [p]; split_ifs <;> (push_cast; ring)
      have hsum_chi0 : ∑ i : Fin n, TwoOrbitMiddle.chi n ξ i = 0 := by
        rw [TwoOrbitMiddle.sum_chi_right]; simp [hξ_ne]
      calc ∑ i : Fin n, (p i : ℂ) * TwoOrbitMiddle.chi n ξ i
          = ∑ i : Fin n, (((1 - u - v : ℝ) : ℂ) * ((if i ∈ S₀ then 1 else 0) * TwoOrbitMiddle.chi n ξ i) +
              (v : ℂ) * TwoOrbitMiddle.chi n ξ i) :=
            Finset.sum_congr rfl fun i _ => by rw [hp_eq i]; ring
        _ = ((1 - u - v : ℝ) : ℂ) * (∑ i : Fin n, if i ∈ S₀ then TwoOrbitMiddle.chi n ξ i else 0) +
            (v : ℂ) * ∑ i : Fin n, TwoOrbitMiddle.chi n ξ i := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
            congr 2; refine Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
        _ = ((1 - u - v : ℝ) : ℂ) * TwoOrbitMiddle.hatSet n S₀ ξ := by
            rw [hsum_chi0, mul_zero, add_zero, ← Finset.sum_filter]
            unfold TwoOrbitMiddle.hatSet
            have hfilt : (Finset.univ : Finset (Fin n)).filter (fun i => i ∈ S₀) = S₀ := by ext x; simp
            rw [hfilt]
    rw [h1, ← h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by push_cast; ring
  have hdiff_norm : ‖TwoOrbitMiddle.hatSet n S ξ - ((1 - u - v : ℝ) : ℂ) * TwoOrbitMiddle.hatSet n S₀ ξ‖ ≤ 2 * t := by
    have hre_eq : (TwoOrbitMiddle.hatSet n S ξ - ((1 - u - v : ℝ) : ℂ) * TwoOrbitMiddle.hatSet n S₀ ξ).re =
        ∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0) - p i) * (TwoOrbitMiddle.chi n ξ i).re := by
      rw [hdiff_eq, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => Complex.re_ofReal_mul _ _
    have him_eq : (TwoOrbitMiddle.hatSet n S ξ - ((1 - u - v : ℝ) : ℂ) * TwoOrbitMiddle.hatSet n S₀ ξ).im =
        ∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0) - p i) * (TwoOrbitMiddle.chi n ξ i).im := by
      rw [hdiff_eq, Complex.im_sum]
      refine Finset.sum_congr rfl fun i _ => Complex.im_ofReal_mul _ _
    have hsq : ‖TwoOrbitMiddle.hatSet n S ξ - ((1 - u - v : ℝ) : ℂ) * TwoOrbitMiddle.hatSet n S₀ ξ‖ ^ 2 ≤ (2 * t) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre_eq, him_eq]
      have hr2 : (∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0) - p i) * (TwoOrbitMiddle.chi n ξ i).re) ^ 2 ≤ t ^ 2 := by
        nlinarith [sq_abs (∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0) - p i) * (TwoOrbitMiddle.chi n ξ i).re),
          abs_nonneg (∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0) - p i) * (TwoOrbitMiddle.chi n ξ i).re), hre_lt]
      have hi2 : (∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0) - p i) * (TwoOrbitMiddle.chi n ξ i).im) ^ 2 ≤ t ^ 2 := by
        nlinarith [sq_abs (∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0) - p i) * (TwoOrbitMiddle.chi n ξ i).im),
          abs_nonneg (∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0) - p i) * (TwoOrbitMiddle.chi n ξ i).im), him_lt]
      nlinarith only [hr2, hi2, show (0 : ℝ) ≤ t ^ 2 by positivity]
    nlinarith [norm_nonneg (TwoOrbitMiddle.hatSet n S ξ - ((1 - u - v : ℝ) : ℂ) * TwoOrbitMiddle.hatSet n S₀ ξ),
      show (0 : ℝ) ≤ t by dsimp [t]; positivity]
  rcases le_max_iff.mp hmax with hI_ge | hS0_ge
  · have hI_sq : b ^ 2 * (n : ℝ) ≤ ‖TwoOrbitMiddle.hatSet n I ξ‖ ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hI_ge 2
      rw [mul_pow, Real.sq_sqrt hn_pos.le] at this; exact this
    nlinarith only [hI_sq, sq_nonneg ‖TwoOrbitMiddle.hatSet n S ξ‖, show (0 : ℝ) ≤ b ^ 2 * (n : ℝ) by positivity]
  · have hS_ge : (b / 2) * Real.sqrt n ≤ ‖TwoOrbitMiddle.hatSet n S ξ‖ := by
      have hrev := norm_sub_norm_le (((1 - u - v : ℝ) : ℂ) * TwoOrbitMiddle.hatSet n S₀ ξ)
        (TwoOrbitMiddle.hatSet n S ξ)
      rw [norm_sub_rev, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith only [h1uv])] at hrev
      have hscaled : (3 / 4 : ℝ) * (b * Real.sqrt n) ≤ (1 - u - v) * ‖TwoOrbitMiddle.hatSet n S₀ ξ‖ :=
        mul_le_mul h1uv hS0_ge (by positivity) (by linarith only [h1uv])
      dsimp only [t] at hdiff_norm
      linarith only [hrev, hscaled, hdiff_norm]
    have hS_sq : b ^ 2 / 4 * (n : ℝ) ≤ ‖TwoOrbitMiddle.hatSet n S ξ‖ ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hS_ge 2
      rw [mul_pow, Real.sq_sqrt hn_pos.le] at this
      linarith only [this, show (b / 2) ^ 2 * (n : ℝ) = b ^ 2 / 4 * (n : ℝ) by ring]
    nlinarith only [hS_sq, sq_nonneg ‖TwoOrbitMiddle.hatSet n I ξ‖]

/-- Bridge B: Perturb the initial flat seed `S₀` to obtain an exact-size seed `S` (`S.card = k`)
preserving the joint Fourier floor and witnessing every small row `2 ≤ |A| ≤ M`. -/
theorem seed_family_exists :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∃ K : ℕ,
      ∀ k : ℕ, K ≤ k → 2 ≤ k →
      let n := 3 * k + 1
      let I := (Finset.univ : Finset (Fin n)).filter (fun i => i.val < k)
      ∃ S : Finset (Fin n), S.card = k ∧
        (∀ ξ : Fin n, ξ.val ≠ 0 →
          c * (n : ℝ) ≤ ‖TwoOrbitMiddle.hatSet n I ξ‖ ^ 2 + ‖TwoOrbitMiddle.hatSet n S ξ‖ ^ 2) ∧
        (∀ A : Finset (Fin n), 2 ≤ A.card → A.card ≤ M →
          (∃ t : Fin n, Disjoint A (S.image (fun i => i + t))) ∧
          (∃ t : Fin n, A ⊆ S.image (fun i => i + t))) := by
  classical
  obtain ⟨K₀, hK₀⟩ := discrete_flat_littlewood_seed
  set b : ℝ := 1 / (12 * TwoOrbitCosine.c474)
  have hb_pos : 0 < b := div_pos (by norm_num) (mul_pos (by norm_num) TwoOrbitCosine.c474_pos)
  have hb_le1 : b ≤ 1 := by
    dsimp only [b]
    rw [div_le_one (mul_pos (by norm_num) TwoOrbitCosine.c474_pos)]
    unfold TwoOrbitCosine.c474
    have h1 : (1 : ℝ) ≤ (16 : ℝ) ^ 18 := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ (16 : ℝ) ^ 32 := one_le_pow₀ (by norm_num)
    have h3 : (1 : ℝ) ≤ (8 * (16 : ℝ) ^ 32) ^ 3 := one_le_pow₀ (by linarith only [h2])
    nlinarith only [h1, h3]
  refine ⟨b ^ 2 / 4, by positivity, ?_⟩
  intro M
  set M' : ℕ := max M 2
  have hM'2 : 2 ≤ M' := le_max_right M 2
  have hMM' : M ≤ M' := le_max_left M 2
  obtain ⟨L_four, hL_four⟩ := exists_nat_gt (40000 / b ^ 2)
  obtain ⟨L_poly1, hL_poly1⟩ := two_pow_ge_mul_pow 4000 4
  set C_small : ℕ := M' ^ 2 * 4 ^ M' * (2 * M' + 10)
  obtain ⟨L_poly2, hL_poly2⟩ := two_pow_ge_mul_pow C_small (2 * M' + 1)
  set L₀ : ℕ := max (max (max L_four L_poly1) L_poly2) (96 * M' * 2 ^ M' + 100)
  refine ⟨max K₀ (2 ^ L₀), ?_⟩
  intro k hk hk2 n I
  have hk_K0 : K₀ ≤ k := le_trans (le_max_left _ _) hk
  have hk_pow : 2 ^ L₀ ≤ k := le_trans (le_max_right _ _) hk
  let _ : NeZero n := ⟨by dsimp [n]; omega⟩
  obtain ⟨S₀, hS0_card_err, hS0_spec⟩ := hK₀ k hk_K0 hk2
  set L : ℕ := Nat.log 2 n
  have hn_ge_pow : 2 ^ L ≤ n := Nat.pow_log_le_self 2 (by dsimp [n]; omega)
  have hn_lt_pow : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hL_ge : L₀ ≤ L := by
    have : 2 ^ L₀ ≤ n := le_trans hk_pow (by dsimp [n]; omega)
    exact (Nat.le_log_iff_pow_le (by norm_num) (by dsimp [n]; omega)).mpr this
  have hL_four_le : L_four ≤ L := by dsimp [L₀] at hL_ge; omega
  have hL_poly1_le : L_poly1 ≤ L := by dsimp [L₀] at hL_ge; omega
  have hL_poly2_le : L_poly2 ≤ L := by dsimp [L₀] at hL_ge; omega
  have hL_96 : 96 * M' * 2 ^ M' + 100 ≤ L := by dsimp [L₀] at hL_ge; omega
  have hL_100 : 100 ≤ L := by omega
  have hL_four' : 40000 / b ^ 2 < (L : ℝ) := lt_of_lt_of_le hL_four (by exact_mod_cast hL_four_le)
  have hpoly1 : (4000 : ℝ) * (L : ℝ) ^ 4 ≤ (n : ℝ) :=
    (hL_poly1 L hL_poly1_le).trans (by exact_mod_cast hn_ge_pow)
  have hpoly2 : (C_small : ℝ) * (L : ℝ) ^ (2 * M' + 1) ≤ (n : ℝ) :=
    (hL_poly2 L hL_poly2_le).trans (by exact_mod_cast hn_ge_pow)
  set d : ℕ := n / (L ^ 2)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by dsimp [n]; omega)
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hn_ge_4000 : (4000 : ℝ) ≤ (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (L : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ L by omega))
    linarith only [h1, hpoly1]
  have h20sqrt_le_d : 20 * Real.sqrt n ≤ (d : ℝ) := by
    have h1 : 40 * Real.sqrt n ≤ (n : ℝ) / (L : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have hsq : (40 * Real.sqrt n * (L : ℝ) ^ 2) ^ 2 ≤ (n : ℝ) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hn_pos.le, ← pow_mul, show 2 * 2 = 4 by norm_num]
        have : (1600 : ℝ) * (L : ℝ) ^ 4 ≤ (n : ℝ) := by
          have : (0 : ℝ) ≤ (L : ℝ) ^ 4 := by positivity
          linarith only [hpoly1, this]
        nlinarith only [this, hn_pos]
      nlinarith [Real.sqrt_nonneg n, hn_pos]
    have hdiv_ge : (n : ℝ) / (L : ℝ) ^ 2 - 1 ≤ (d : ℝ) := by
      have hlt : n < (L ^ 2) * (d + 1) := Nat.lt_mul_div_succ n (by positivity)
      have hcast : (n : ℝ) < (L : ℝ) ^ 2 * ((d : ℝ) + 1) := by exact_mod_cast hlt
      rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
      linarith only [hcast]
    have hsqrt_ge1 : (1 : ℝ) ≤ Real.sqrt n := by
      rw [Real.one_le_sqrt]; exact_mod_cast (show 1 ≤ n by dsimp [n]; omega)
    linarith only [h1, hdiv_ge, hsqrt_ge1]
  have hd_le : (d : ℝ) ≤ (n : ℝ) / (L : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    exact_mod_cast (Nat.div_mul_le_self n (L ^ 2))
  have hsqrt_le_n : Real.sqrt n ≤ (n : ℝ) / 60 := by
    have h60 : (60 : ℝ) ≤ Real.sqrt n := by
      calc (60 : ℝ) = Real.sqrt ((60 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt n := Real.sqrt_le_sqrt (by linarith only [hn_ge_4000])
    have := mul_le_mul_of_nonneg_right h60 (Real.sqrt_nonneg n)
    rw [Real.mul_self_sqrt hn_pos.le] at this
    linarith only [this]
  have hd_pos : 0 < d := by
    have : (0 : ℝ) < (d : ℝ) := by linarith [Real.sqrt_pos.mpr hn_pos, h20sqrt_le_d]
    exact_mod_cast this
  have hS0_bounds : (k : ℝ) - 3 * Real.sqrt n ≤ (S₀.card : ℝ) ∧
      (S₀.card : ℝ) ≤ (k : ℝ) + 3 * Real.sqrt n := by
    have := abs_le.mp hS0_card_err; constructor <;> linarith only [this.1, this.2]
  have hS0_ge_n4 : (n : ℝ) / 4 ≤ (S₀.card : ℝ) := by
    have hn_eq : (n : ℝ) = 3 * (k : ℝ) + 1 := by exact_mod_cast rfl
    linarith only [hn_eq, hS0_bounds.1, hsqrt_le_n, hn_ge_4000]
  have hS0_le_n2 : (S₀.card : ℝ) ≤ (n : ℝ) / 2 := by
    have hn_eq : (n : ℝ) = 3 * (k : ℝ) + 1 := by exact_mod_cast rfl
    linarith only [hn_eq, hS0_bounds.2, hsqrt_le_n, hn_ge_4000]
  have hR_card : ((Finset.univ \ S₀).card : ℝ) = (n : ℝ) - (S₀.card : ℝ) := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    have hle : S₀.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ S₀
    rw [Nat.cast_sub hle]
  set e : ℕ := d + k - S₀.card
  have he_real : (e : ℝ) = (d : ℝ) + (k : ℝ) - (S₀.card : ℝ) := by
    have hle : S₀.card ≤ d + k := by
      have : (S₀.card : ℝ) ≤ (d : ℝ) + (k : ℝ) := by linarith only [hS0_bounds.2, h20sqrt_le_d, Real.sqrt_nonneg n]
      exact_mod_cast this
    dsimp only [e]; rw [Nat.cast_sub hle, Nat.cast_add]
  have he_ge_half : (d : ℝ) / 2 ≤ (e : ℝ) := by linarith only [he_real, hS0_bounds.2, h20sqrt_le_d]
  have he_le_two : (e : ℝ) ≤ 2 * (d : ℝ) := by linarith only [he_real, hS0_bounds.1, h20sqrt_le_d]
  have he_pos : 0 < e := by
    have : (0 : ℝ) < (e : ℝ) := by linarith [show (0 : ℝ) < (d : ℝ) by exact_mod_cast hd_pos, he_ge_half]
    exact_mod_cast this
  have hL2_ge : (10000 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (100 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_100
    nlinarith only [this]
  have hd_lt_S0 : d < S₀.card := by
    have : (d : ℝ) < (S₀.card : ℝ) := by
      have h1 : (n : ℝ) / (L : ℝ) ^ 2 ≤ (n : ℝ) / 10000 :=
        div_le_div_of_nonneg_left hn_pos.le (by norm_num) hL2_ge
      linarith only [hd_le, h1, hS0_ge_n4, hn_pos]
    exact_mod_cast this
  have he_lt_R : e < (Finset.univ \ S₀).card := by
    have : (e : ℝ) < ((Finset.univ \ S₀).card : ℝ) := by
      have h1 : (n : ℝ) / (L : ℝ) ^ 2 ≤ (n : ℝ) / 10000 :=
        div_le_div_of_nonneg_left hn_pos.le (by norm_num) hL2_ge
      linarith only [he_le_two, hd_le, h1, hR_card, hS0_le_n2, hn_pos]
    exact_mod_cast this
  have hcard_target : S₀.card - d + e = k := by
    have hle : S₀.card ≤ d + k := by
      have : (S₀.card : ℝ) ≤ (d : ℝ) + (k : ℝ) := by linarith only [hS0_bounds.2, h20sqrt_le_d, Real.sqrt_nonneg n]
      exact_mod_cast this
    dsimp only [e]; omega
  set u : ℝ := (d : ℝ) / (S₀.card : ℝ)
  set v : ℝ := (e : ℝ) / ((Finset.univ \ S₀).card : ℝ)
  let p : Fin n → ℝ := fun i => if i ∈ S₀ then 1 - u else v
  have hS0_pos : (0 : ℝ) < (S₀.card : ℝ) := by linarith only [hS0_ge_n4, hn_pos]
  have hR_pos : (0 : ℝ) < ((Finset.univ \ S₀).card : ℝ) := by linarith only [hR_card, hS0_le_n2, hn_pos]
  have hd_ge_half : (n : ℝ) / (2 * (L : ℝ) ^ 2) ≤ (d : ℝ) := by
    have hlt : n < (L ^ 2) * (d + 1) := Nat.lt_mul_div_succ n (by positivity)
    have hcast : (n : ℝ) < (L : ℝ) ^ 2 * ((d : ℝ) + 1) := by exact_mod_cast hlt
    have h2L2 : 2 * (L : ℝ) ^ 2 ≤ (n : ℝ) := by
      have h1 : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 4 := by
        have : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (show 1 ≤ L by omega)
        nlinarith [sq_nonneg ((L : ℝ) - 1)]
      linarith only [h1, hpoly1]
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hcast, h2L2, hL2_ge]
  have hu_le : u ≤ 4 / (L : ℝ) ^ 2 := by
    dsimp only [u]; rw [div_le_iff₀ hS0_pos]
    calc (d : ℝ) ≤ (n : ℝ) / (L : ℝ) ^ 2 := hd_le
      _ = 4 / (L : ℝ) ^ 2 * ((n : ℝ) / 4) := by ring
      _ ≤ 4 / (L : ℝ) ^ 2 * (S₀.card : ℝ) := mul_le_mul_of_nonneg_left hS0_ge_n4 (by positivity)
  have hu_ge : 1 / (2 * (L : ℝ) ^ 2) ≤ u := by
    dsimp only [u]; rw [le_div_iff₀ hS0_pos]
    calc 1 / (2 * (L : ℝ) ^ 2) * (S₀.card : ℝ) ≤ 1 / (2 * (L : ℝ) ^ 2) * (n : ℝ) :=
          mul_le_mul_of_nonneg_left (by linarith only [hS0_le_n2, hn_pos]) (by positivity)
      _ = (n : ℝ) / (2 * (L : ℝ) ^ 2) := by ring
      _ ≤ (d : ℝ) := hd_ge_half
  have hv_le : v ≤ 4 / (L : ℝ) ^ 2 := by
    dsimp only [v]; rw [div_le_iff₀ hR_pos]
    calc (e : ℝ) ≤ 2 * (d : ℝ) := he_le_two
      _ ≤ 2 * ((n : ℝ) / (L : ℝ) ^ 2) := by linarith only [hd_le]
      _ = 4 / (L : ℝ) ^ 2 * ((n : ℝ) / 2) := by ring
      _ ≤ 4 / (L : ℝ) ^ 2 * ((Finset.univ \ S₀).card : ℝ) :=
          mul_le_mul_of_nonneg_left (by linarith only [hR_card, hS0_le_n2]) (by positivity)
  have hv_ge : 1 / (4 * (L : ℝ) ^ 2) ≤ v := by
    dsimp only [v]; rw [le_div_iff₀ hR_pos]
    calc 1 / (4 * (L : ℝ) ^ 2) * ((Finset.univ \ S₀).card : ℝ)
        ≤ 1 / (4 * (L : ℝ) ^ 2) * (n : ℝ) :=
          mul_le_mul_of_nonneg_left (by linarith only [hR_card, hS0_pos]) (by positivity)
      _ = ((n : ℝ) / (2 * (L : ℝ) ^ 2)) / 2 := by ring
      _ ≤ (d : ℝ) / 2 := by linarith only [hd_ge_half]
      _ ≤ (e : ℝ) := he_ge_half
  have h4L2_le : 4 / (L : ℝ) ^ 2 ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [hL2_ge]
  have h14L2_le_8 : 1 / (4 * (L : ℝ) ^ 2) ≤ 1 / 8 := by
    rw [one_div_le_one_div (by positivity) (by norm_num)]; linarith only [hL2_ge]
  have h14L2_le_2 : 1 / (4 * (L : ℝ) ^ 2) ≤ 1 / (2 * (L : ℝ) ^ 2) := by
    rw [one_div_le_one_div (by positivity) (by positivity)]; linarith only [hL2_ge]
  have hp_lo : ∀ i : Fin n, 1 / (4 * (L : ℝ) ^ 2) ≤ p i := fun i => by
    dsimp only [p]; split_ifs
    · linarith only [hu_le, h4L2_le, h14L2_le_8]
    · exact hv_ge
  have hp_hi : ∀ i : Fin n, p i ≤ 1 - 1 / (4 * (L : ℝ) ^ 2) := fun i => by
    dsimp only [p]; split_ifs
    · linarith only [hu_ge, h14L2_le_2]
    · linarith only [hv_le, h4L2_le, h14L2_le_8]
  have hp0 : ∀ i : Fin n, 0 ≤ p i := fun i => le_trans (by positivity) (hp_lo i)
  have hp1 : ∀ i : Fin n, p i ≤ 1 := fun i => le_trans (hp_hi i) (by linarith [show (0 : ℝ) ≤ 1 / (4 * (L : ℝ) ^ 2) by positivity])
  have hWnn : ∀ S : Finset (Fin n), 0 ≤ TwoOrbitPerturb.probWU p Finset.univ S :=
    fun S => TwoOrbitPerturb.probWU_nonneg p hp0 hp1 Finset.univ S
  -- Step 1: Exact-size weight `≥ 1 / (n + 1)^2`.
  let GoodCard := (Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card = k)
  have hgood_ge : 1 / (((n : ℝ) + 1) ^ 2) ≤ ∑ S ∈ GoodCard, TwoOrbitPerturb.probWU p Finset.univ S := by
    have h1 := TwoOrbitPerturb.sum_probWU_exact_card_ge Finset.univ S₀ (Finset.subset_univ _)
      d e hd_pos hd_lt_S0 he_pos he_lt_R
    rw [Finset.card_univ, Fintype.card_fin, hcard_target] at h1
    exact h1
  -- Step 2: Fourier concentration tail `< 1 / (3 * (n + 1)^2)`.
  have hvar : ∑ i : Fin n, p i * (1 - p i) ≤ 4 * (n : ℝ) / (L : ℝ) ^ 2 := by
    have hsplit : ∑ i : Fin n, p i * (1 - p i) =
        (∑ i ∈ S₀, (1 - u) * u) + ∑ i ∈ Finset.univ \ S₀, v * (1 - v) := by
      rw [← Finset.sum_sdiff (Finset.subset_univ S₀), add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun i hi => by simp only [p, hi, ↓reduceIte]; ring
      · refine Finset.sum_congr rfl fun i hi => by
          have hnot : i ∉ S₀ := (Finset.mem_sdiff.mp hi).2
          simp only [p, hnot, ↓reduceIte]
    rw [hsplit, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have h1 : (S₀.card : ℝ) * ((1 - u) * u) ≤ (d : ℝ) := by
      have : (S₀.card : ℝ) * u = (d : ℝ) := mul_div_cancel₀ _ hS0_pos.ne'
      have hu0 : 0 ≤ u := by dsimp [u]; positivity
      nlinarith only [this, hu0, show (0 : ℝ) ≤ (d : ℝ) by positivity]
    have h2 : ((Finset.univ \ S₀).card : ℝ) * (v * (1 - v)) ≤ (e : ℝ) := by
      have : ((Finset.univ \ S₀).card : ℝ) * v = (e : ℝ) := mul_div_cancel₀ _ hR_pos.ne'
      have hv0 : 0 ≤ v := by dsimp [v]; positivity
      nlinarith only [this, hv0, show (0 : ℝ) ≤ (e : ℝ) by positivity]
    have h3 : 4 * (n : ℝ) / (L : ℝ) ^ 2 = 4 * ((n : ℝ) / (L : ℝ) ^ 2) := by ring
    linarith only [h1, h2, he_le_two, hd_le, h3]
  have ht_le_V : (b / 8) * Real.sqrt n ≤ 4 * (n : ℝ) / (L : ℝ) ^ 2 := by
    have h1 : Real.sqrt n ≤ (n : ℝ) / (L : ℝ) ^ 2 := by
      have h2 := h20sqrt_le_d.trans hd_le; linarith [Real.sqrt_nonneg n]
    have h3 : 4 * (n : ℝ) / (L : ℝ) ^ 2 = 4 * ((n : ℝ) / (L : ℝ) ^ 2) := by ring
    nlinarith only [h1, hb_le1, Real.sqrt_nonneg n, h3]
  let t : ℝ := (b / 8) * Real.sqrt n
  let BadRe (ξ : Fin n) := (Finset.univ : Finset (Fin n)).powerset.filter (fun S =>
    t ≤ |∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0) - p i) * (TwoOrbitMiddle.chi n ξ i).re|)
  let BadIm (ξ : Fin n) := (Finset.univ : Finset (Fin n)).powerset.filter (fun S =>
    t ≤ |∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0) - p i) * (TwoOrbitMiddle.chi n ξ i).im|)
  let BadFour := (Finset.univ : Finset (Fin n)).biUnion (fun ξ => BadRe ξ ∪ BadIm ξ)
  have hfour_le : ∑ S ∈ BadFour, TwoOrbitPerturb.probWU p Finset.univ S < 1 / (3 * ((n : ℝ) + 1) ^ 2) :=
    perturb_fourier_tail_lt n L p hp0 hp1 b hb_pos hL_100 hL_four' hn_lt_pow hvar ht_le_V
  -- Step 3: Small-row cover & miss failure tail `< 1 / (3 * (n + 1)^2)`.
  let SmallRows := (Finset.univ : Finset (Fin n)).powerset.filter (fun A => 2 ≤ A.card ∧ A.card ≤ M')
  have hpack_ex : ∀ A ∈ SmallRows,
      ∃ B : Finset (Finset (Fin n)),
        (∀ b ∈ B, ∃ t : Fin n, b = A.image (fun x => x + t)) ∧
        (B : Set (Finset (Fin n))).Pairwise Disjoint ∧
        n ≤ B.card * M' ^ 2 := by
    intro A hA
    have hA2 : 2 ≤ A.card := (Finset.mem_filter.mp hA).2.1
    have hAM' : A.card ≤ M' := (Finset.mem_filter.mp hA).2.2
    have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨T, hTpair, hTcard⟩ := TwoOrbit.finDisjointTranslatePacking A hAne
    let f : Fin n → Finset (Fin n) := fun t => A.image (fun x => x + t)
    have hfinj : Set.InjOn f (T : Set (Fin n)) := by
      intro t₁ ht₁ t₂ ht₂ hEq
      by_contra hne
      have hdisj : Disjoint (f t₁) (f t₂) := hTpair ht₁ ht₂ hne
      rw [hEq] at hdisj
      obtain ⟨a, ha⟩ := hAne
      have hmem : a + t₂ ∈ f t₂ := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      exact Finset.disjoint_left.mp hdisj hmem hmem
    refine ⟨T.image f, ?_, ?_, ?_⟩
    · intro b hb; obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hb; exact ⟨t, rfl⟩
    · intro b₁ hb₁ b₂ hb₂ hne
      obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb₁)
      obtain ⟨t₂, ht₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb₂)
      exact hTpair ht₁ ht₂ (fun h => hne (by rw [h]))
    · rw [Finset.card_image_of_injOn hfinj]
      exact hTcard.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hAM' 2))
  choose BOf hB_trans hB_pair hB_card using fun A (hA : A ∈ SmallRows) => hpack_ex A hA
  let BadCov (A : {A // A ∈ SmallRows}) :=
    (Finset.univ : Finset (Fin n)).powerset.filter (fun S => ∀ b ∈ BOf A.1 A.2, ¬ (b ⊆ S))
  let BadMiss (A : {A // A ∈ SmallRows}) :=
    (Finset.univ : Finset (Fin n)).powerset.filter (fun S => ∀ b ∈ BOf A.1 A.2, ¬ Disjoint b S)
  let BadSmall := SmallRows.attach.biUnion (fun A => BadCov A ∪ BadMiss A)
  have hsmall_le : ∑ S ∈ BadSmall, TwoOrbitPerturb.probWU p Finset.univ S < 1 / (3 * ((n : ℝ) + 1) ^ 2) :=
    perturb_small_rows_tail_lt n L M' p hp_lo hp_hi hL_100 hL_96 hn_lt_pow hM'2 hpoly2
      SmallRows rfl BOf hB_trans hB_pair hB_card
  -- Step 4: Extract a good exact-size seed `S ∈ GoodCard \ (BadFour ∪ BadSmall)`.
  have hex_good : ∃ S ∈ GoodCard, S ∉ BadFour ∪ BadSmall := by
    by_contra! hall
    have hsub : GoodCard ⊆ BadFour ∪ BadSmall := fun S hS => hall S hS
    have hle1 : ∑ S ∈ GoodCard, TwoOrbitPerturb.probWU p Finset.univ S ≤
        ∑ S ∈ BadFour ∪ BadSmall, TwoOrbitPerturb.probWU p Finset.univ S :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun S _ _ => hWnn S
    have hui := Finset.sum_union_inter (s₁ := BadFour) (s₂ := BadSmall)
      (f := TwoOrbitPerturb.probWU p Finset.univ)
    have hinter_nn : 0 ≤ ∑ S ∈ BadFour ∩ BadSmall, TwoOrbitPerturb.probWU p Finset.univ S :=
      Finset.sum_nonneg fun S _ => hWnn S
    have hpos : (0 : ℝ) < 1 / (((n : ℝ) + 1) ^ 2) := by positivity
    have hdiv3 : 1 / (3 * ((n : ℝ) + 1) ^ 2) = (1 / 3 : ℝ) * (1 / (((n : ℝ) + 1) ^ 2)) := by field_simp
    linarith only [hgood_ge, hle1, hui, hinter_nn, hfour_le, hsmall_le, hpos, hdiv3]
  obtain ⟨S, hS_good, hS_not_bad⟩ := hex_good
  have hS_card : S.card = k := (Finset.mem_filter.mp hS_good).2
  have hS_not_four : S ∉ BadFour := fun h => hS_not_bad (Finset.mem_union_left _ h)
  have hS_not_small : S ∉ BadSmall := fun h => hS_not_bad (Finset.mem_union_right _ h)
  refine ⟨S, hS_card, ?_, ?_⟩
  · intro ξ hξ0
    have hξ_ne : ξ ≠ 0 := fun h => hξ0 (by simp [h])
    have hnot_re : S ∉ BadRe ξ := fun h => hS_not_four
      (Finset.mem_biUnion.mpr ⟨ξ, Finset.mem_univ _, Finset.mem_union_left _ h⟩)
    have hnot_im : S ∉ BadIm ξ := fun h => hS_not_four
      (Finset.mem_biUnion.mpr ⟨ξ, Finset.mem_univ _, Finset.mem_union_right _ h⟩)
    have hre_lt : |∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0) - p i) * (TwoOrbitMiddle.chi n ξ i).re| < t := by
      by_contra! hge
      exact hnot_re (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hge⟩)
    have him_lt : |∑ i : Fin n, ((if i ∈ S then (1 : ℝ) else 0) - p i) * (TwoOrbitMiddle.chi n ξ i).im| < t := by
      by_contra! hge
      exact hnot_im (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hge⟩)
    have h1uv : (3 : ℝ) / 4 ≤ 1 - u - v := by linarith only [hu_le, hv_le, h4L2_le]
    exact perturb_fourier_preserve n I S₀ S u v b hb_pos h1uv ξ hξ_ne (hS0_spec ξ hξ0) hre_lt him_lt
  · intro A hA2 hAM
    have hA_mem : A ∈ SmallRows := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hA2, hAM.trans hMM'⟩
    have hnot_cov : S ∉ BadCov ⟨A, hA_mem⟩ := fun h => hS_not_small
      (Finset.mem_biUnion.mpr ⟨⟨A, hA_mem⟩, Finset.mem_attach _ _, Finset.mem_union_left _ h⟩)
    have hnot_miss : S ∉ BadMiss ⟨A, hA_mem⟩ := fun h => hS_not_small
      (Finset.mem_biUnion.mpr ⟨⟨A, hA_mem⟩, Finset.mem_attach _ _, Finset.mem_union_right _ h⟩)
    constructor
    · have hex : ∃ b ∈ BOf A hA_mem, Disjoint b S := by
        by_contra! hall
        exact hnot_miss (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hall⟩)
      obtain ⟨b, hb_mem, hb_disj⟩ := hex
      obtain ⟨t0, rfl⟩ := hB_trans A hA_mem b hb_mem
      refine ⟨-t0, ?_⟩
      rw [Finset.disjoint_left]
      intro a ha hSshift
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hSshift
      have hmem : s + (-t0) + t0 ∈ A.image (fun x => x + t0) := Finset.mem_image.mpr ⟨s + (-t0), ha, rfl⟩
      have hsimp : s + (-t0) + t0 = s := by abel
      rw [hsimp] at hmem
      exact Finset.disjoint_left.mp hb_disj hmem hs
    · have hex : ∃ b ∈ BOf A hA_mem, b ⊆ S := by
        by_contra! hall
        exact hnot_cov (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hall⟩)
      obtain ⟨b, hb_mem, hb_sub⟩ := hex
      obtain ⟨t0, rfl⟩ := hB_trans A hA_mem b hb_mem
      refine ⟨-t0, ?_⟩
      intro a ha
      have haS : a + t0 ∈ S := hb_sub (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      exact Finset.mem_image.mpr ⟨a + t0, haS, by abel⟩

end TwoOrbitBridge

theorem Conjectures.LogRank.TwoOrbitFullDetector :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 2 ≤ k →
      let n := 3*k+1;
      let adj := fun (A B : Finset (Fin n)) (a : ℤ) => ((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a+1;
      let detects := fun (Y : Finset (Finset (Fin n))) => ∀ A : Finset (Fin n), 2 ≤ A.card → A.card + 2 ≤ n → ∀ a : ℤ, ∃ B ∈ Y, ¬ adj A B a;
      let shift := fun (S : Finset (Fin n)) (t : Fin n) => S.image (fun i => i+t);
      let orbit := fun (S : Finset (Fin n)) => (Finset.univ : Finset (Fin n)).image (shift S);
      let I := (Finset.univ : Finset (Fin n)).filter (fun i => i.val < k);
      ∃ S : Finset (Fin n), S.card = k ∧ detects (orbit I ∪ orbit S) :=
  TwoOrbitMiddle.detector_from_seed_family TwoOrbitBridge.seed_family_exists
