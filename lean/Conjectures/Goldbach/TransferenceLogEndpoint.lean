import Mathlib
import Conjectures.Goldbach.PolynomialFourierTransference

/-! Endpoint binary transference with a logarithmically strengthened fourth moment.

The spectral truncation is chosen before the uniformity parameter: for a truncation
level `t = exp (-2 (L - 1))` the logarithmically weighted fourth moments bound the
truncated tail by `2 M / sqrt L`, which tends to zero with `L`.  The level is fixed
first (as a function of `M`, `δ`, `η` only), and the majorant uniformity `κ` is then
taken small enough for the truncated residual to be affordable.  The modulus is
qualitative.

Adapted from `Conjectures.Goldbach.PolynomialFourierTransference` (accepted proof of
`L-goldbach-polynomial-fourier-transference`), which supplies the Fourier inversion,
the truncated majorant estimate and the bad-set test function; the endpoint tail
estimate below replaces its `p < 4` moment interpolation. -/

namespace Conjectures.Goldbach.TransferenceLogEndpoint_aux
open Finset
open scoped ComplexConjugate BigOperators
open PolynomialTransfer
noncomputable section
variable {N : ℕ} [NeZero N]

private def bump (x : ℝ) : ℝ := x^4 * (1 + Real.log (1 + x⁻¹))

private theorem log_add_inv_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.log (1 + x⁻¹) :=
  Real.log_nonneg (by linarith [inv_nonneg.mpr hx])

private theorem bump_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ bump x := by
  unfold bump
  have h := log_add_inv_nonneg hx
  nlinarith [pow_nonneg hx 4]

private theorem bump_ge_fourth {x : ℝ} (hx : 0 ≤ x) : x^4 ≤ bump x := by
  unfold bump
  have h := log_add_inv_nonneg hx
  nlinarith [pow_nonneg hx 4]

private theorem bump_ge_mul {x : ℝ} {L : ℝ} (hx : 0 ≤ x) (hL : 1 ≤ L)
    (hxl : x ≤ Real.exp (-(L-1))) : x^4 * L ≤ bump x := by
  unfold bump
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp
  have h1 : x⁻¹ ≤ 1 + x⁻¹ := by linarith
  have hlog : Real.log (x⁻¹) ≤ Real.log (1 + x⁻¹) := Real.log_le_log (by positivity) h1
  rw [Real.log_inv] at hlog
  have hxlog : Real.log x ≤ -(L-1) := by
    have h2 := Real.log_le_log hxpos hxl
    rwa [Real.log_exp] at h2
  nlinarith [pow_nonneg hx 4]

private theorem sqrt_pow4 {x : ℝ} : Real.sqrt (x^4) = x^2 := by
  have h : x^4 = (x^2)^2 := by ring
  rw [h]; exact Real.sqrt_sq (sq_nonneg _)

/-- The logarithmically weighted fourth moments force the fourth moment of the
products at frequencies below the level `exp (-2 (L-1))` to be small. -/
private theorem small_part (f g : ZMod N → ℝ) {M L : ℝ} (hM : 0 ≤ M) (hL : 1 ≤ L)
    (hf : (∑ r, bump ‖F f r‖) ≤ M) (hg : (∑ r, bump ‖F g r‖) ≤ M) :
    ((∑ r, if ‖F f r‖ * ‖F g r‖ ≤ Real.exp (-2*(L-1)) then (‖F f r‖ * ‖F g r‖)^2 else 0) *
      Real.sqrt L) ≤ 2 * M := by
  let a : ZMod N → ℝ := fun r => ‖F f r‖
  let b : ZMod N → ℝ := fun r => ‖F g r‖
  have ha (r : ZMod N) : 0 ≤ a r := norm_nonneg _
  have hb (r : ZMod N) : 0 ≤ b r := norm_nonneg _
  have hf' : (∑ r, bump (a r)) ≤ M := hf
  have hg' : (∑ r, bump (b r)) ≤ M := hg
  let e := Real.exp (-(L-1))
  let t := Real.exp (-2*(L-1))
  have he : 0 < e := Real.exp_pos _
  have hee : e * e = t := by
    dsimp [e, t]; rw [← Real.exp_add]; congr 1; ring
  have pt (r : ZMod N) : (if a r * b r ≤ t then (a r * b r)^2 else 0) ≤
      (if a r ≤ e then (a r * b r)^2 else 0) + (if b r ≤ e then (a r * b r)^2 else 0) := by
    by_cases h1 : a r * b r ≤ t
    · by_cases h2 : a r ≤ e
      · by_cases h3 : b r ≤ e
        · simp only [h1, h2, h3, ↓reduceIte]; linarith [sq_nonneg (a r * b r)]
        · simp only [h1, h2, h3, ↓reduceIte]; linarith [sq_nonneg (a r * b r)]
      · by_cases h3 : b r ≤ e
        · simp only [h1, h2, h3, ↓reduceIte]; linarith [sq_nonneg (a r * b r)]
        · exfalso
          have ha2 : e < a r := not_le.mp h2
          have hb2 : e < b r := not_le.mp h3
          have hlt : t < a r * b r := by
            calc t = e * e := hee.symm
              _ < e * b r := mul_lt_mul_of_pos_left hb2 he
              _ ≤ a r * b r := mul_le_mul_of_nonneg_right ha2.le (hb r)
          linarith
    · have hz : 0 ≤ (if a r ≤ e then (a r * b r)^2 else 0) +
          (if b r ≤ e then (a r * b r)^2 else 0) := by split_ifs <;> positivity
      simp only [h1, ↓reduceIte]; linarith
  have sum1 : (∑ r, if a r * b r ≤ t then (a r * b r)^2 else 0) ≤
      (∑ r ∈ univ.filter (fun r => a r ≤ e), (a r * b r)^2) +
      (∑ r ∈ univ.filter (fun r => b r ≤ e), (a r * b r)^2) := by
    calc _ ≤ ∑ r, ((if a r ≤ e then (a r * b r)^2 else 0) +
          (if b r ≤ e then (a r * b r)^2 else 0)) := sum_le_sum (s := univ) fun r _ => pt r
      _ = _ := by rw [sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  have key (r : ZMod N) (hr : a r ≤ e) :
      (a r * b r)^2 * Real.sqrt L ≤ Real.sqrt (bump (a r)) * Real.sqrt (bump (b r)) := by
    have h1 : (a r)^4 * L ≤ bump (a r) := bump_ge_mul (ha r) hL hr
    have h2 : (b r)^4 ≤ bump (b r) := bump_ge_fourth (hb r)
    have s1 : Real.sqrt ((a r)^4 * L) = (a r)^2 * Real.sqrt L := by
      rw [Real.sqrt_mul (by positivity), sqrt_pow4]
    have s2 : Real.sqrt ((b r)^4) = (b r)^2 := sqrt_pow4
    calc (a r * b r)^2 * Real.sqrt L = Real.sqrt ((a r)^4 * L) * Real.sqrt ((b r)^4) := by
          rw [s1, s2]; ring
      _ ≤ Real.sqrt (bump (a r)) * Real.sqrt (bump (b r)) :=
          mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have partA : (∑ r ∈ univ.filter (fun r => a r ≤ e), (a r * b r)^2) * Real.sqrt L ≤ M := by
    have sub1 : (∑ r ∈ univ.filter (fun r => a r ≤ e), bump (a r)) ≤ M :=
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => bump_nonneg (ha i)).trans hf'
    have sub2 : (∑ r ∈ univ.filter (fun r => a r ≤ e), bump (b r)) ≤ M :=
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => bump_nonneg (hb i)).trans hg'
    calc (∑ r ∈ univ.filter (fun r => a r ≤ e), (a r * b r)^2) * Real.sqrt L
        = ∑ r ∈ univ.filter (fun r => a r ≤ e), (a r * b r)^2 * Real.sqrt L := by rw [Finset.sum_mul]
      _ ≤ ∑ r ∈ univ.filter (fun r => a r ≤ e),
            Real.sqrt (bump (a r)) * Real.sqrt (bump (b r)) :=
          sum_le_sum fun r hr => key r (mem_filter.mp hr).2
      _ ≤ Real.sqrt (∑ r ∈ univ.filter (fun r => a r ≤ e), bump (a r)) *
            Real.sqrt (∑ r ∈ univ.filter (fun r => a r ≤ e), bump (b r)) :=
          Real.sum_sqrt_mul_sqrt_le _ (fun r => bump_nonneg (ha r)) (fun r => bump_nonneg (hb r))
      _ ≤ Real.sqrt M * Real.sqrt M :=
          mul_le_mul (Real.sqrt_le_sqrt sub1) (Real.sqrt_le_sqrt sub2)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = M := Real.mul_self_sqrt hM
  have key' (r : ZMod N) (hr : b r ≤ e) :
      (a r * b r)^2 * Real.sqrt L ≤ Real.sqrt (bump (a r)) * Real.sqrt (bump (b r)) := by
    have h1 : (b r)^4 * L ≤ bump (b r) := bump_ge_mul (hb r) hL hr
    have h2 : (a r)^4 ≤ bump (a r) := bump_ge_fourth (ha r)
    have s1 : Real.sqrt ((b r)^4 * L) = (b r)^2 * Real.sqrt L := by
      rw [Real.sqrt_mul (by positivity), sqrt_pow4]
    have s2 : Real.sqrt ((a r)^4) = (a r)^2 := sqrt_pow4
    calc (a r * b r)^2 * Real.sqrt L = Real.sqrt ((a r)^4) * Real.sqrt ((b r)^4 * L) := by
          rw [s1, s2]; ring
      _ ≤ Real.sqrt (bump (a r)) * Real.sqrt (bump (b r)) :=
          mul_le_mul (Real.sqrt_le_sqrt h2) (Real.sqrt_le_sqrt h1)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have partB : (∑ r ∈ univ.filter (fun r => b r ≤ e), (a r * b r)^2) * Real.sqrt L ≤ M := by
    have sub1 : (∑ r ∈ univ.filter (fun r => b r ≤ e), bump (a r)) ≤ M :=
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => bump_nonneg (ha i)).trans hf'
    have sub2 : (∑ r ∈ univ.filter (fun r => b r ≤ e), bump (b r)) ≤ M :=
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => bump_nonneg (hb i)).trans hg'
    calc (∑ r ∈ univ.filter (fun r => b r ≤ e), (a r * b r)^2) * Real.sqrt L
        = ∑ r ∈ univ.filter (fun r => b r ≤ e), (a r * b r)^2 * Real.sqrt L := by rw [Finset.sum_mul]
      _ ≤ ∑ r ∈ univ.filter (fun r => b r ≤ e),
            Real.sqrt (bump (a r)) * Real.sqrt (bump (b r)) :=
          sum_le_sum fun r hr => key' r (mem_filter.mp hr).2
      _ ≤ Real.sqrt (∑ r ∈ univ.filter (fun r => b r ≤ e), bump (a r)) *
            Real.sqrt (∑ r ∈ univ.filter (fun r => b r ≤ e), bump (b r)) :=
          Real.sum_sqrt_mul_sqrt_le _ (fun r => bump_nonneg (ha r)) (fun r => bump_nonneg (hb r))
      _ ≤ Real.sqrt M * Real.sqrt M :=
          mul_le_mul (Real.sqrt_le_sqrt sub1) (Real.sqrt_le_sqrt sub2)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = M := Real.mul_self_sqrt hM
  calc (∑ r, if a r * b r ≤ t then (a r * b r)^2 else 0) * Real.sqrt L
      ≤ ((∑ r ∈ univ.filter (fun r => a r ≤ e), (a r * b r)^2) +
        (∑ r ∈ univ.filter (fun r => b r ≤ e), (a r * b r)^2)) * Real.sqrt L :=
        mul_le_mul_of_nonneg_right sum1 (Real.sqrt_nonneg _)
    _ = (∑ r ∈ univ.filter (fun r => a r ≤ e), (a r * b r)^2) * Real.sqrt L +
        (∑ r ∈ univ.filter (fun r => b r ≤ e), (a r * b r)^2) * Real.sqrt L := by ring
    _ ≤ M + M := add_le_add partA partB
    _ = 2 * M := by ring

private theorem budget (b f g : ZMod N → ℝ)
    (bn : ∀ x, 0 ≤ b x) (mass : E b = 1) (gn : ∀ x, 0 ≤ g x) (gm : E g ≤ 2)
    {M L s : ℝ} (hM : 1 ≤ M) (hL : 1 ≤ L) (hs : 0 < s)
    (hf : (∑ r, bump ‖F f r‖) ≤ M) (hg : (∑ r, bump ‖F g r‖) ≤ M)
    (b2 : (∑ r, ‖F b r‖^2) ≤ 1/s^2) :
    ∃ S : Finset (ZMod N), 0 ∈ S ∧
      (∑ r, ‖if r ∈ S then (if r = 0 then (1:ℂ) else 0) - coeff b g r else 0‖) ≤
        3 + 2*M/(Real.exp (-2*(L-1)))^2 ∧
      (∑ r, if r ∈ S then 0 else ‖F f r‖*‖F g r‖*‖F b r‖)^2 ≤ 2*M/(Real.sqrt L*s^2) := by
  classical
  let X := fun r => ‖F f r‖*‖F g r‖
  let t := Real.exp (-2*(L-1))
  have tp : 0 < t := Real.exp_pos _
  have t1 : t ≤ 1 := by
    dsimp [t]
    calc Real.exp (-2*(L-1)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith)
      _ = 1 := Real.exp_zero
  have nn (r : ZMod N) : 0 ≤ X r := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h4 : (∑ r, X r ^ 2) ≤ M := by
    have pt (r : ZMod N) : 2 * X r ^ 2 ≤ bump ‖F f r‖ + bump ‖F g r‖ := by
      have h1 := bump_ge_fourth (norm_nonneg (F f r))
      have h2 := bump_ge_fourth (norm_nonneg (F g r))
      dsimp [X]
      nlinarith [sq_nonneg (‖F f r‖^2 - ‖F g r‖^2)]
    calc (∑ r, X r ^ 2) ≤ ∑ r, (bump ‖F f r‖ + bump ‖F g r‖)/2 :=
          sum_le_sum (s := univ) fun r _ => by linarith [pt r]
      _ = ((∑ r, bump ‖F f r‖) + (∑ r, bump ‖F g r‖))/2 := by
          rw [← Finset.sum_div, sum_add_distrib]
      _ ≤ M := by linarith
  let U := univ.filter fun r => t < X r
  let S := insert 0 U
  have co : (U.card : ℝ) * t^2 ≤ M := by
    calc (U.card : ℝ) * t^2 = ∑ _r ∈ U, t^2 := by simp
      _ ≤ ∑ r ∈ U, X r ^ 2 := by
          apply sum_le_sum; intro r hr
          have hlt := (mem_filter.mp hr).2
          nlinarith [nn r]
      _ ≤ ∑ r, X r ^ 2 := sum_le_sum_of_subset_of_nonneg (subset_univ U) fun i _ _ => sq_nonneg _
      _ ≤ M := h4
  have cs : (U.card : ℝ) ≤ M/t^2 := (le_div_iff₀ (sq_pos_of_pos tp)).2 co
  have cb (r : ZMod N) : ‖coeff b g r‖ ≤ 2 := by
    simp only [coeff, norm_mul, Complex.norm_conj]
    have h := (boundF b bn r).trans_eq mass
    nlinarith [mul_le_mul_of_nonneg_left h (norm_nonneg (F g r)), (boundF g gn r).trans gm]
  have pt (r : ZMod N) :
      ‖if r ∈ S then (if r = 0 then (1:ℂ) else 0) - coeff b g r else 0‖ ≤
      (if r = 0 then (3:ℝ) else 0) + (if r ∈ U then 2 else 0) := by
    by_cases rz : r = 0
    · subst r; simp only [S, mem_insert, true_or, ite_true]
      have := norm_sub_le (1:ℂ) (coeff b g 0)
      simp only [norm_one] at this
      split_ifs <;> linarith [cb 0]
    · by_cases hr : r ∈ U <;> simp [S, rz, hr, cb]
  have lone : (∑ r, ‖if r ∈ S then (if r = 0 then (1:ℂ) else 0) - coeff b g r else 0‖) ≤
      3 + 2*M/t^2 := by
    have h := sum_le_sum (s := univ) fun r _ => pt r
    simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true] at h
    have su : (∑ r : ZMod N, if r ∈ U then (2:ℝ) else 0) = U.card*2 := by simp
    rw [su] at h
    rw [mul_div_assoc]
    linarith
  have small : (∑ r, if X r ≤ t then X r ^ 2 else 0) * Real.sqrt L ≤ 2*M :=
    small_part f g (by linarith) hL hf hg
  let Y := fun r => if r ∈ S then 0 else X r
  have yp (r : ZMod N) : Y r ^ 2 ≤ (if X r ≤ t then X r ^ 2 else 0) := by
    by_cases hr : r ∈ S
    · by_cases hh : X r ≤ t <;> simp [Y, hr, hh, sq_nonneg]
    · have sm : X r ≤ t := by
        by_contra! bad; apply hr; exact mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _, bad⟩)
      simp [Y, hr, sm]
  have ysum : (∑ r, Y r ^ 2) ≤ ∑ r, (if X r ≤ t then X r ^ 2 else 0) :=
    sum_le_sum (s := univ) fun r _ => yp r
  have w2 : 0 ≤ ∑ r, (if X r ≤ t then X r ^ 2 else 0) :=
    sum_nonneg fun r _ => by split_ifs <;> positivity
  have cauchy := sum_mul_sq_le_sq_mul_sq (R := ℝ) univ Y (fun r => ‖F b r‖)
  have prod := mul_le_mul ysum b2 (sum_nonneg fun _ _ => sq_nonneg _) w2
  have cancel : (1/s^2) * s^2 = 1 := by
    rw [one_div]; exact inv_mul_cancel₀ (pow_ne_zero 2 hs.ne')
  have key : (∑ r, Y r * ‖F b r‖)^2 ≤ 2*M/(Real.sqrt L*s^2) := by
    have hLpos : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
    calc (∑ r, Y r * ‖F b r‖)^2 ≤ (∑ r, Y r ^ 2) * (∑ r, ‖F b r‖^2) := cauchy
      _ ≤ (∑ r, (if X r ≤ t then X r ^ 2 else 0)) * (1/s^2) := prod
      _ ≤ 2*M/(Real.sqrt L*s^2) := by
          rw [le_div_iff₀ (by positivity)]
          calc (∑ r, (if X r ≤ t then X r ^ 2 else 0)) * (1/s^2) * (Real.sqrt L * s^2)
              = ((∑ r, (if X r ≤ t then X r ^ 2 else 0)) * Real.sqrt L) * ((1/s^2) * s^2) := by ring
            _ = (∑ r, (if X r ≤ t then X r ^ 2 else 0)) * Real.sqrt L := by rw [cancel, mul_one]
            _ ≤ 2*M := small
  refine ⟨S, mem_insert_self .., lone, ?_⟩
  simpa only [Y, X, ite_mul, zero_mul] using key

end

private theorem mainBound {M δ η : ℝ} (hM : 1 ≤ M) (hd : 0 < δ) (hd1 : δ ≤ 1)
    (he : 0 < η) (he1 : η ≤ 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) [NeZero N] (f g u v : ZMod N → ℝ),
    (∀ x, 0 ≤ f x ∧ f x ≤ u x ∧ 0 ≤ g x ∧ g x ≤ v x) → 1+δ ≤ E f + E g →
    (∑ r, bump ‖F f r‖) ≤ M → (∑ r, bump ‖F g r‖) ≤ M →
    (∀ r, ‖F (fun x => u x-1) r‖ ≤ κ ∧ ‖F (fun x => v x-1) r‖ ≤ κ) →
    ((univ.filter (fun n => conv f g n < δ^3/1000)).card : ℝ) ≤ η*(N : ℝ) := by
  classical
  let s := δ*η/100
  have hs : 0 < s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := by dsimp [s]; nlinarith
  have hsδ : s ≤ δ/100 := by dsimp [s]; nlinarith
  have hsη0 : s ≤ η := by dsimp [s]; nlinarith
  have hsη : s^2 ≤ η := by
    calc s^2 = s*s := sq s
      _ ≤ s*1 := mul_le_mul_of_nonneg_left hs1 hs.le
      _ = s := mul_one s
      _ ≤ η := hsη0
  have hδ2 : δ^2 ≤ 1 := by nlinarith
  have hs2 : s^2 ≤ 1 := by nlinarith
  let A := 128*M/(δ^2*s^2)
  have hA : 1 ≤ A := by
    have h1 : δ^2 * s^2 ≤ 1 := le_trans (mul_le_mul hδ2 hs2 (sq_nonneg s) (by linarith)) (by norm_num)
    dsimp [A]
    rw [le_div_iff₀ (by positivity)]
    linarith
  let L := A^2
  have hL : 1 ≤ L := by dsimp [L]; nlinarith
  have hsqL : Real.sqrt L = A := Real.sqrt_sq (by linarith)
  let t := Real.exp (-2*(L-1))
  have ht : 0 < t := Real.exp_pos _
  let W := 3 + 2*M/t^2
  have hW : 0 < W := by dsimp [W]; positivity
  let κ := min (s^2) (δ/(8*W^2))
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  have hκs : κ ≤ s^2 := min_le_left _ _
  have hκW : κ ≤ δ/(8*W^2) := min_le_right _ _
  have hκ1 : κ ≤ 1 := hκs.trans (by nlinarith)
  refine ⟨κ, hκ, ?_⟩
  intro N inst f g u v dom size hf hg dec
  have gm : E g ≤ 2 := by
    have h := (dec 0).2
    rw [Fzero, Complex.norm_real, Real.norm_eq_abs, Esub, Econst] at h
    have vv := (abs_le.mp h).2
    have gv := Emono (fun x => (dom x).2.2.2)
    linarith
  by_contra! too
  obtain ⟨b, bn, mass, b2, low⟩ := badWeights f g hs hsη too
  obtain ⟨S, h0, lone, tail⟩ :=
    budget b f g bn mass (fun x => (dom x).2.2.1) gm hM hL hs hf hg b2
  have cr := corrError b v mass hs (fun r => (dec r).2) hκ.le hκs b2
  have bar := corrBarrier b g v mass bn (fun x => (dom x).2.2) hs.le cr
  have htail : 2*M/(Real.sqrt L*s^2) = (δ/8)^2 := by
    rw [hsqL]
    dsimp [A]
    field_simp
    ring
  have hT : (∑ r, if r ∈ S then 0 else ‖F f r‖*‖F g r‖*‖F b r‖) ≤ δ/8 := by
    have hnn : 0 ≤ (∑ r, if r ∈ S then 0 else ‖F f r‖*‖F g r‖*‖F b r‖) :=
      sum_nonneg fun r _ => by split_ifs <;> positivity
    nlinarith [tail, htail]
  have cut := truncated b f g u S h0 (fun x => ⟨(dom x).1, (dom x).2.1⟩)
    (fun r => (dec r).1) lone hκ.le hT
  have hκW2 : κ*W^2 ≤ δ/8 := by
    calc κ*W^2 ≤ (δ/(8*W^2))*W^2 := mul_le_mul_of_nonneg_right hκW (by positivity)
      _ = δ/8 := by field_simp
  have hs2δ : s^2 ≤ δ/100 := by
    calc s^2 = s*s := sq s
      _ ≤ s*1 := mul_le_mul_of_nonneg_left hs1 hs.le
      _ = s := mul_one s
      _ ≤ δ/100 := hsδ
  have hδ3 : δ^3 ≤ δ := by
    calc δ^3 = δ*δ^2 := by ring
      _ ≤ δ*1 := mul_le_mul_of_nonneg_left hδ2 hd.le
      _ = δ := mul_one δ
  have key : E f ≤ (1 - E g + s + s^2) + κ*W^2 + 2*(δ^3/1000 + δ/8) := by
    linarith [cut, bar, low]
  linarith

end Conjectures.Goldbach.TransferenceLogEndpoint_aux

theorem Conjectures.Goldbach.TransferenceLogEndpoint :
by
  classical
  exact ∀ M δ η : ℝ, 1 ≤ M → 0 < δ → δ ≤ 1 → 0 < η → η ≤ 1 → ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) [NeZero N], ∀ f g u v : ZMod N → ℝ,
    let avg := fun h : ZMod N → ℝ => (∑ x, h x)/(N : ℝ)
    let ft := fun (h : ZMod N → ℝ) (r : ZMod N) => (∑ x : ZMod N, (h x : ℂ) * Complex.exp (-2*(Real.pi : ℂ)*Complex.I*((r*x).val : ℂ)/(N : ℂ)))/(N : ℂ)
    let bump := fun x : ℝ => x^4 * (1+Real.log (1+x⁻¹))
    (∀ x, 0 ≤ f x ∧ f x ≤ u x ∧ 0 ≤ g x ∧ g x ≤ v x) → 1+δ ≤ avg f + avg g →
    (∑ r : ZMod N, bump ‖ft f r‖) ≤ M → (∑ r : ZMod N, bump ‖ft g r‖) ≤ M →
    (∀ r, ‖ft (fun x => u x-1) r‖ ≤ κ ∧ ‖ft (fun x => v x-1) r‖ ≤ κ) →
    ((Finset.univ.filter (fun n : ZMod N => avg (fun x => f x*g (n-x)) < δ^3/1000)).card : ℝ) ≤ η*(N : ℝ) := by
  classical
  intro M δ η hM hd hd1 he he1
  obtain ⟨κ, hκ, h⟩ := Conjectures.Goldbach.TransferenceLogEndpoint_aux.mainBound hM hd hd1 he he1
  refine ⟨κ, hκ, ?_⟩
  intro N inst f g u v
  dsimp only
  simpa only [PolynomialTransfer.expForm, PolynomialTransfer.conv, PolynomialTransfer.E,
    Conjectures.Goldbach.TransferenceLogEndpoint_aux.bump] using h N f g u v
