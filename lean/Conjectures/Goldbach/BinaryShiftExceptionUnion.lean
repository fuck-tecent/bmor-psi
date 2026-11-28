import Conjectures.Goldbach.FixedModulusZeroClassSquare
import Conjectures.Goldbach.B13BilateralVaughanReduction
import Conjectures.Goldbach.BinaryShiftShortMixedEnergy
import Conjectures.Goldbach.DynThinWindowExceptions
import Conjectures.Goldbach.EstermannAlmostAllPolylog
import Conjectures.Goldbach.FareyHyperbolaRectangles
import Conjectures.Goldbach.MajorFixed144
import Conjectures.Goldbach.ThreeQuartersExceptionalDirichletWindows
import Mathlib

/- For a reference statement, see PrimeNumberTheoremAnd's ResidueCalcOnRectangles.lean at
   2c476fa6441c607096d93c8fc7ac0a227a655dae, licensed under Apache 2.0.
   The argument below uses the complex logarithm on each side of the rectangle. -/

/- The arithmetic foundation is adapted from muxkin's goldbach-proofs PR #2458,
   commit 25c1ef60495052eb22212b5560f90bbc6a4a0917 (Apache-2.0).
   Its source notes attributing earlier components are retained below. -/

/- The finite Ramanujan identities, kernel identities, CRT and prime-power computations
used below adapt DFQDZZ's goldbach-proofs PR #316, commit
e4ab24712555ae8c2c926adf19d368a9fb392c35 (Apache-2.0). Original credits are
retained with the corresponding sections. The multiplicative averaging, sieve estimates,
convolution bounds and the moving-modulus-window argument are derived below. -/

/-
# An explicit lower bound for the Ramanujan-weighted major-arc model

The arithmetic and kernel estimates below are extracted from DFQDZZ's
goldbach-proofs PR #316 (commit e4ab24712555ae8c2c926adf19d368a9fb392c35,
Apache-2.0). The CRT and prime-power computations are credited below.
The estimate applies to every positive even target.
-/

/- The finite CRT and prime-power calculations below adapt goldbach-proofs PRs #207 (XianWu18) and #203 (wzhxzkk), Apache-2.0. -/

/- Divisor-square mean adapted from OpenAI, openai/math, revision
3344da59991ed94f9ba711217b29c1d760badfa6, as checked in
PEqualNP.Outside.L_goldbach_frontier_uncond_deep_second_moment (Apache-2.0). -/

/-
Finite Möbius cancellation and the Wiener–Ikehara argument for coefficients
1 + μ, from goldbach-proofs, `PEqualNP/Outside/L_twin_primes_unconditional_short.lean`,
Git blob f04bea6b8c5c06b9fe28dc698cdaf5a55e2a6f85, Apache-2.0.
That source credits `L_twin_primes_hard_cutoff.lean`, Git blob
efec7cd55880f73ecf34c278b4ab18c646a9fb0c.
-/

/- Quadratic Gauss norm for any primitive additive character.
Adapted from the standard-character proof in FareyHyperbolaRectangles. -/

/-
The divisor estimates are adapted from Eric Naslund, `GradedNear/BurgessReduction.lean`
(https://github.com/enaslund/linniks-constant-3.99/blob/ecdbe3e3e08ad499d2c749ff417cc461f57334c5/GradedNear/BurgessReduction.lean).
-/

/-
The exact Möbius transfer is adapted from Eric Naslund, `GradedNear/BurgessReduction.lean`
(https://github.com/enaslund/linniks-constant-3.99/blob/ecdbe3e3e08ad499d2c749ff417cc461f57334c5/GradedNear/BurgessReduction.lean).
-/
section
/-!
Criterion for the frozen pointwise three-quarters bound on deep arcs.
No hypothesis on the real parts of the zeros is used. The formula keeps the
signed multiplicities of the enclosed zeros. An average over contour abscissae
bounds the left edge using local zero counts and an integrable product kernel.
At polynomial height the entire error is bounded at the oscillatory window scale.
Local Jensen bounds then fix the cutoff at the critical line, strictly excluding
zeros on the line itself. Finite character inversion recovers the prime sum.

The analytic growth, Jensen disk, logarithmic derivative and rectangle
residue estimates are adapted from DNZJSJ, goldbach-proofs PR #2486,
commit f3613cf846dfb3e7fe7d04fe6ce51c6ee25e7d4f (Apache-2.0).
The Mellin window and inversion use the same integer endpoints as the
conditional three-quarters proof. The right-half count, shared edge
selection and two-sided truncation estimate below do not use Dirichlet GRH.
The per-ordinate oscillatory bounds are from 34245621, PR #2511, at
cba708bd00210b8e17a7f7f9d5e48b74599f48c5. The rational-approximation and main-term estimates
are adapted from Esythium, PR #2512 at 9117b0e8465c7323ed09c4673b5ceac9a7ef8118.
-/

section
namespace GoldbachSmoothing

open Complex DirichletCharacter MeasureTheory
open scoped BigOperators

noncomputable section


theorem twistedCoefficient_zero {q : ℕ} (χ : DirichletCharacter ℂ q) :
    twistedCoefficient χ 0 = 0 := by
  simp [twistedCoefficient]


end
end GoldbachSmoothing
open scoped BigOperators Topology
open Asymptotics Complex Filter Finset MeasureTheory Set

noncomputable section


namespace Goldbach

open Metric Set MeromorphicOn

private theorem jensen_re_of_mem_outer {z : ℂ} {t : ℝ}
    (hz : z ∈ closedBall (⟨2, t⟩ : ℂ) (15 / 8)) : 1 / 8 ≤ z.re := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have hre := (Complex.abs_re_le_norm (z - (⟨2, t⟩ : ℂ))).trans hz
  simp only [Complex.sub_re] at hre
  linarith only [(abs_le.mp hre).1]

private theorem jensen_norm_of_mem_outer {z : ℂ} {t : ℝ}
    (hz : z ∈ closedBall (⟨2, t⟩ : ℂ) (15 / 8)) : 1 + ‖z‖ ≤ 3 * (2 + |t|) := by
  rw [mem_closedBall, dist_eq_norm] at hz
  let center : ℂ := ⟨2, t⟩
  have hcenter : ‖center‖ ≤ 2 + |t| := by
    simpa [center] using Complex.norm_le_abs_re_add_abs_im center
  have hnorm : ‖z‖ ≤ ‖z - center‖ + ‖center‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z - center) center
  linarith only [hz, hcenter, hnorm, abs_nonneg t]

private theorem jensen_analytic_outer {f : ℂ → ℂ} {t : ℝ}
    (hAnalytic : AnalyticOnNhd ℂ f {z | 0 < z.re}) :
    AnalyticOnNhd ℂ f (closedBall (⟨2, t⟩ : ℂ) (15 / 8)) := by
  intro z hz
  exact hAnalytic z (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 8)
    (jensen_re_of_mem_outer hz))

/-- For a holomorphic function with fixed growth and anchor bounds, the total divisor mass
in the closed disk of radius `29 / 16` about `2 + it` grows at most logarithmically. -/
theorem jensen_diskDivisor_bound {A b : ℝ} (hA : 0 < A) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) (f : ℂ → ℂ) (t : ℝ), 0 < q →
      AnalyticOnNhd ℂ f {z | 0 < z.re} →
      (∀ z : ℂ, 1 / 8 ≤ z.re → ‖f z‖ ≤ A * (q : ℝ) * (1 + ‖z‖) ^ 2) →
      b ≤ ‖f (⟨2, t⟩ : ℂ)‖ →
      ((∑ᶠ z : ℂ, divisor f (closedBall (⟨2, t⟩ : ℂ) (29 / 16)) z : ℤ) : ℝ) ≤
        K * Real.log (2 * (q : ℝ) * (2 + |t|)) := by
  classical
  let r : ℝ := 29 / 16
  let R : ℝ := 15 / 8
  have hr : 0 < r := by norm_num [r]
  have hR : 0 < R := by norm_num [R]
  have hrR : r < R := by norm_num [r, R]
  let B : ℝ := 1 + 9 * A
  let bMin : ℝ := min 1 b
  let D : ℝ := B / bMin
  let logRatio : ℝ := Real.log (R / r)
  let logFactor : ℝ := 2 + Real.log D / Real.log 2
  have hB : 1 ≤ B := by dsimp [B]; linarith only [hA]
  have hbMin : 0 < bMin := lt_min zero_lt_one hb
  have hD : 1 ≤ D := by
    apply (le_div_iff₀ hbMin).mpr
    simpa only [one_mul] using (min_le_left (1 : ℝ) b).trans hB
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogRatio : 0 < logRatio := Real.log_pos ((one_lt_div hr).mpr hrR)
  have hlogCoeff : 0 ≤ Real.log D / Real.log 2 := div_nonneg hlogD hlog2.le
  have hlogFactor : 0 < logFactor := by dsimp [logFactor]; linarith only [hlogCoeff]
  refine ⟨logFactor / logRatio, div_pos hlogFactor hlogRatio, ?_⟩
  intro q f t hq hAnalytic hGrowth hAnchor
  let c : ℂ := ⟨2, t⟩
  let v : ℝ := 2 + |t|
  let w : ℝ := 2 * (q : ℝ) * v
  let M : ℝ := B * w ^ 2
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast Nat.succ_le_of_lt hq
  have hq₀ : (0 : ℝ) ≤ q := by positivity
  have hv : 2 ≤ v := by dsimp [v]; linarith only [abs_nonneg t]
  have hw : 2 ≤ w := by
    have hq₂ : (1 : ℝ) ≤ 2 * (q : ℝ) := by linarith only [hq₁]
    exact hv.trans (le_mul_of_one_le_left (by linarith only [hv]) hq₂)
  have hw₀ : 0 < w := by linarith only [hw]
  have hM : 1 ≤ M := by
    have hWs : 1 ≤ w ^ 2 := by nlinarith only [hw, sq_nonneg (w - 2)]
    exact one_le_mul_of_one_le_of_one_le hB hWs
  have hAnchorMin : bMin ≤ ‖f c‖ := (min_le_right 1 b).trans hAnchor
  have hFpos : 0 < ‖f c‖ := hbMin.trans_le hAnchorMin
  have hFc : f c ≠ 0 := norm_pos_iff.mp hFpos
  have hOuter : AnalyticOnNhd ℂ f (closedBall c R) := by
    exact jensen_analytic_outer hAnalytic
  have hBound : ∀ z ∈ closedBall c R, ‖f z‖ ≤ M := by
    intro z hz
    have hnorm : 1 + ‖z‖ ≤ 3 * v := jensen_norm_of_mem_outer hz
    have hnormSq : (1 + ‖z‖) ^ 2 ≤ (3 * v) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by linarith only [hv])).mpr hnorm
    have hqSq : (q : ℝ) ≤ (2 * (q : ℝ)) ^ 2 := by
      have hqSelf : (q : ℝ) ≤ (q : ℝ) * (q : ℝ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hq₁ hq₀
      nlinarith only [hqSelf, sq_nonneg (q : ℝ)]
    have hqvSq : (q : ℝ) * v ^ 2 ≤ w ^ 2 := calc
      _ ≤ (2 * (q : ℝ)) ^ 2 * v ^ 2 := mul_le_mul_of_nonneg_right hqSq (sq_nonneg v)
      _ = _ := by dsimp [w]; ring
    calc
      ‖f z‖ ≤ A * (q : ℝ) * (1 + ‖z‖) ^ 2 := hGrowth z (jensen_re_of_mem_outer hz)
      _ ≤ A * (q : ℝ) * (3 * v) ^ 2 := mul_le_mul_of_nonneg_left hnormSq (mul_nonneg hA.le hq₀)
      _ = 9 * A * ((q : ℝ) * v ^ 2) := by ring
      _ ≤ 9 * A * w ^ 2 := mul_le_mul_of_nonneg_left hqvSq (by positivity)
      _ ≤ M := mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (sq_nonneg w)
  have hJensen : ((∑ᶠ z : ℂ, divisor f (closedBall c |r|) z : ℤ) : ℝ) ≤
      Real.log (M / ‖f c‖) / logRatio := by
    have hOuterAbs : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa [abs_of_pos hR] using hOuter
    have hCircle : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M := by
      intro z hz
      apply hBound z
      simpa only [abs_of_pos hR] using sphere_subset_closedBall hz
    exact AnalyticOnNhd.sum_divisor_le (r := r) (R := R) (M := M)
      (by simpa only [abs_of_pos hr] using hr)
      (by simpa only [abs_of_pos hr, abs_of_pos hR] using hrR)
      hM hOuterAbs hFc hCircle
  have hLogW : Real.log 2 ≤ Real.log w := Real.log_le_log (by norm_num) hw
  have hLogBound : Real.log (M / ‖f c‖) ≤ logFactor * Real.log w := by
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
    have hDivBound : M / ‖f c‖ ≤ D * w ^ 2 := calc
      _ ≤ M / bMin := div_le_div_of_nonneg_left hMpos.le hbMin hAnchorMin
      _ = _ := by dsimp [M, D]; ring
    calc
      _ ≤ Real.log (D * w ^ 2) := Real.log_le_log (div_pos hMpos hFpos) hDivBound
      _ = 2 * Real.log w + Real.log D := by
        rw [Real.log_mul (by linarith only [hD]) (pow_ne_zero _ hw₀.ne'), Real.log_pow]
        norm_num [add_comm]
      _ = 2 * Real.log w + (Real.log D / Real.log 2) * Real.log 2 := by
        rw [div_mul_cancel₀ _ hlog2.ne']
      _ ≤ 2 * Real.log w + (Real.log D / Real.log 2) * Real.log w :=
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hLogW hlogCoeff))
      _ = _ := by dsimp [logFactor]; ring
  change ((∑ᶠ z : ℂ, divisor f (closedBall c r) z : ℤ) : ℝ) ≤
    (logFactor / logRatio) * Real.log w
  calc
    _ = ((∑ᶠ z : ℂ, divisor f (closedBall c |r|) z : ℤ) : ℝ) :=
      congrArg (fun U : Set ℂ ↦ ((∑ᶠ z : ℂ, divisor f U z : ℤ) : ℝ))
        (congrArg (closedBall c) (abs_of_pos hr).symm)
    _ ≤ Real.log (M / ‖f c‖) / logRatio := hJensen
    _ ≤ (logFactor * Real.log w) / logRatio :=
      div_le_div_of_nonneg_right hLogBound hlogRatio.le
    _ = _ := by ring

end Goldbach


open scoped BigOperators Topology
open Complex Filter Metric Set

noncomputable section


namespace Goldbach

open Complex Metric Set
open scoped BigOperators

/-- Uniform logarithmic derivative bound on the right of Re s = 9/20, at a point with a
given positive separation from the zeros of the regularized L-function. -/
theorem norm_logDeriv_regularizedL_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t σ d : ℝ),
      9 / 20 ≤ σ → σ ≤ 2 → 0 < d →
      (∀ ρ : ℂ, 0 < ρ.re → regularizedL χ ρ = 0 → d ≤ ‖(⟨σ, t⟩ : ℂ) - ρ‖) →
      ‖logDeriv (regularizedL χ) (⟨σ, t⟩ : ℂ)‖ ≤
        C * Real.log (2 * (q : ℝ) * (2 + |t|)) * (1 + d⁻¹) := by
  let R : ℝ := 15 / 8
  let A : ℝ := 130200 / R
  let E : ℝ := (Real.log (12 / 11 : ℝ))⁻¹
  have hR : 0 < R := by norm_num [R]
  have hA : 0 < A := div_pos (by norm_num) hR
  have hE : 0 < E := inv_pos.mpr (Real.log_pos (by norm_num))
  refine ⟨13 * (A + E), mul_pos (by norm_num) (add_pos hA hE), ?_⟩
  intro q _ χ t σ d hσlo hσhi hd hSep
  let f := regularizedL χ
  let c : ℂ := ⟨2, t⟩
  let s : ℂ := ⟨σ, t⟩
  let K : ℝ := 2 + |t|
  let B : ℝ := 900 * (q : ℝ) * K ^ 2
  let L : ℝ := Real.log (2 * (q : ℝ) * K)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.succ_le_of_lt q.pos_of_neZero
  have hq0 : 0 < (q : ℝ) := zero_lt_one.trans_le hq1
  have hK2 : 2 ≤ K := le_add_of_nonneg_right (abs_nonneg t)
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 < K := zero_lt_one.trans_le hK1
  have hB0 : 0 < B := by
    dsimp only [B]
    positivity
  have hB2 : 2 ≤ B := by
    calc
      (2 : ℝ) ≤ 900 * 1 * 1 := by norm_num
      _ ≤ B := mul_le_mul (mul_le_mul_of_nonneg_left hq1 (by norm_num))
        (one_le_pow₀ hK1) zero_le_one (by positivity)
  have hReLower (w : ℂ) (hw : w ∈ closedBall c R) : (1 / 8 : ℝ) ≤ w.re := by
    have hDist := mem_closedBall_iff_norm.mp hw
    have hRe := abs_re_le_norm (w - c)
    rw [sub_re, show c.re = 2 from rfl] at hRe
    have hLower := neg_le_abs (w.re - 2)
    dsimp only [R] at hDist
    linarith
  have hcform : c = (2 : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;> simp [c, Complex.mul_re, Complex.mul_im]
  have hcnorm : ‖c‖ ≤ K := by
    rw [hcform]
    calc
      _ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = _ := by simp [K, norm_real, Real.norm_eq_abs]
  have hAnchor : (1 / 4 : ℝ) ≤ ‖f c‖ := norm_regularizedL_anchor χ t
  have hf0 : f c ≠ 0 := norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 4).trans_le hAnchor)
  have hf : AnalyticOnNhd ℂ f (closedBall c R) := (analytic_regularizedL χ).mono (subset_univ _)
  have hfB (w : ℂ) (hw : w ∈ closedBall c (24 / 25 * R)) : ‖f w‖ ≤ B * ‖f c‖ := by
    have hwBig := closedBall_subset_closedBall (show (24 / 25 : ℝ) * R ≤ R by norm_num [R]) hw
    have hDist := mem_closedBall_iff_norm.mp hwBig
    have hwNorm : 1 + ‖w‖ ≤ 3 * K := by
      dsimp only [R] at hDist
      linarith only [norm_le_norm_sub_add w c, hDist, hcnorm, hK2]
    have hGrowth : ‖f w‖ ≤ 25 * (q : ℝ) * (1 + ‖w‖) ^ 2 := by
      have hRaw := GoldbachGrhGrowth.norm_regularizedLFunction_le χ (hReLower w hwBig)
      by_cases hχ : χ = 1 <;> simpa [f, regularizedL, hχ] using hRaw
    calc
      _ ≤ 25 * (q : ℝ) * (1 + ‖w‖) ^ 2 := hGrowth
      _ ≤ 25 * (q : ℝ) * (3 * K) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hwNorm 2) (by positivity)
      _ = B * (1 / 4 : ℝ) := by
        dsimp only [B]
        ring
      _ ≤ B * ‖f c‖ := mul_le_mul_of_nonneg_left hAnchor hB0.le
  have hS : s ∈ closedBall c (83 / 100 * R) := by
    have hSub : s - c = ((σ - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s, c]
    rw [mem_closedBall_iff_norm, hSub, norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hσhi)]
    dsimp only [R]
    linarith
  have hS0 : f s ≠ 0 := by
    intro hsz
    have hs : 0 < s.re := (by norm_num : (0 : ℝ) < 9 / 20).trans_le hσlo
    have h := hSep s hs hsz
    rw [sub_self, norm_zero] at h
    exact hd.not_ge h
  obtain ⟨Z, hZ, hMass, hApprox⟩ :=
    GoldbachGrhLogDerivative.logDeriv_partial_fraction_disk hR hf hf0 hB2 hfB
  have hTerms : ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤
      (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) * d⁻¹ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    have hZmem : ρ ∈ (↑Z : Set ℂ) := hρ
    rw [hZ] at hZmem
    have hρLarge := closedBall_subset_closedBall (show (22 / 25 : ℝ) * R ≤ R by norm_num [R])
      hZmem.1
    have hρPos := (by norm_num : (0 : ℝ) < 1 / 8).trans_le (hReLower ρ hρLarge)
    have hρdist : d ≤ ‖s - ρ‖ := hSep ρ hρPos hZmem.2
    have hRecip : ‖s - ρ‖⁻¹ ≤ d⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hd hρdist
    rw [norm_div, Complex.norm_natCast, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hRecip (Nat.cast_nonneg _)
  have hLFormula : L = Real.log 2 + Real.log (q : ℝ) + Real.log K := by
    dsimp only [L]
    rw [Real.log_mul (by positivity) hK0.ne', Real.log_mul (by norm_num) hq0.ne']
  have hBLFormula : Real.log B = Real.log 900 + Real.log (q : ℝ) + 2 * Real.log K := by
    dsimp only [B]
    rw [Real.log_mul (by positivity) (pow_ne_zero _ hK0.ne'),
      Real.log_mul (by norm_num) hq0.ne', Real.log_pow]
    norm_num
  have hLog900 : Real.log 900 ≤ 10 * Real.log 2 := by
    calc
      _ ≤ Real.log ((2 : ℝ) ^ (10 : ℕ)) := Real.log_le_log (by norm_num) (by norm_num)
      _ = _ := by
        rw [Real.log_pow]
        norm_num
  have hLPos : 0 < L := by
    rw [hLFormula]
    linarith only [Real.log_nonneg hq1, Real.log_nonneg hK1, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hScaleLog : Real.log B ≤ 13 * L := by
    rw [hBLFormula, hLFormula]
    linarith only [hLog900, Real.log_nonneg hq1, Real.log_nonneg hK1,
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hRecip0 : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
  have hBudget : A + E * d⁻¹ ≤ (A + E) * (1 + d⁻¹) := by
    nlinarith only [hE.le, mul_nonneg hA.le hRecip0]
  have hMass' := mul_le_mul_of_nonneg_right hMass hRecip0
  change ‖logDeriv f s‖ ≤ 13 * (A + E) * L * (1 + d⁻¹)
  calc
    _ ≤ ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ +
        ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ := norm_le_norm_sub_add _ _
    _ ≤ A * Real.log B + (Real.log B / Real.log (12 / 11)) * d⁻¹ :=
      (add_le_add (hApprox s hS hS0) (hTerms.trans hMass'))
    _ = Real.log B * (A + E * d⁻¹) := by
      dsimp only [E]
      rw [div_eq_mul_inv]
      ring
    _ ≤ (13 * L) * (A + E * d⁻¹) := mul_le_mul_of_nonneg_right hScaleLog (by positivity)
    _ ≤ (13 * L) * ((A + E) * (1 + d⁻¹)) := mul_le_mul_of_nonneg_left hBudget (by positivity)
    _ = _ := by ring

end Goldbach

namespace Goldbach

/-- A unit interval contains a height separated by `1 / (2 * (1 + S.card))`
from all ordinates in a finite family. -/
theorem exists_goodHeight {α : Type*} (S : Finset α) (ordinate : α → ℝ) (T : ℝ) :
    ∃ u ∈ Set.Icc T (T + 1),
      ∀ a ∈ S, (1 : ℝ) / (2 * (1 + (S.card : ℝ))) ≤ |u - ordinate a| := by
  classical
  let den : ℝ := 1 + (S.card : ℝ)
  let gap : ℝ := 1 / (2 * den)
  let grid (j : Fin (S.card + 1)) : ℝ := T + (j.val : ℝ) / den
  have hDen : 0 < den := by dsimp [den]; positivity
  have hGrid (j : Fin (S.card + 1)) : grid j ∈ Set.Icc T (T + 1) := by
    have hj : (j.val : ℝ) ≤ S.card := by exact_mod_cast Nat.le_of_lt_succ j.isLt
    have hLower : 0 ≤ (j.val : ℝ) / den := div_nonneg (by positivity) hDen.le
    have hUpper : (j.val : ℝ) / den ≤ 1 := by
      apply (div_le_one hDen).mpr
      dsimp [den]
      linarith only [hj]
    exact ⟨by dsimp [grid]; linarith only [hLower], add_le_add le_rfl hUpper⟩
  have hGridGap {j k : Fin (S.card + 1)} (hjk : j ≠ k) :
      gap + gap ≤ |grid j - grid k| := by
    have hNat : j.val ≠ k.val := fun heq ↦ hjk (Fin.ext heq)
    have hInt : (j.val : ℤ) ≠ (k.val : ℤ) := by exact_mod_cast hNat
    have hAbsInt : (1 : ℤ) ≤ |(j.val : ℤ) - (k.val : ℤ)| :=
      Int.one_le_abs (sub_ne_zero.mpr hInt)
    have hAbs : (1 : ℝ) ≤ |(j.val : ℝ) - (k.val : ℝ)| := by exact_mod_cast hAbsInt
    have hGridSub : grid j - grid k = ((j.val : ℝ) - (k.val : ℝ)) / den := by
      dsimp [grid]
      ring
    calc
      gap + gap = 1 / den := by
        dsimp [gap]
        field_simp [hDen.ne']
        norm_num
      _ ≤ |(j.val : ℝ) - (k.val : ℝ)| / den := div_le_div_of_nonneg_right hAbs hDen.le
      _ = |grid j - grid k| := by rw [hGridSub, abs_div, abs_of_pos hDen]
  by_contra hNoGood
  have hBad (j : Fin (S.card + 1)) : ∃ a : S, |grid j - ordinate a| < gap := by
    by_contra hNoBad
    apply hNoGood
    refine ⟨grid j, hGrid j, ?_⟩
    intro a ha
    exact le_of_not_gt (fun h ↦ hNoBad ⟨⟨a, ha⟩, h⟩)
  let badAt (j : Fin (S.card + 1)) : S := (hBad j).choose
  have hBadAt (j : Fin (S.card + 1)) : |grid j - ordinate (badAt j)| < gap :=
    (hBad j).choose_spec
  have hInjective : Function.Injective badAt := by
    intro j k hEqual
    by_contra hDifferent
    have hPair : |grid j - ordinate (badAt j)| + |grid k - ordinate (badAt j)| < gap + gap :=
      (add_lt_add (hBadAt j) (by simpa only [hEqual] using hBadAt k))
    have hTri : |grid j - grid k| ≤
        |grid j - ordinate (badAt j)| + |grid k - ordinate (badAt j)| := by
      simpa only [abs_sub_comm (ordinate (badAt j)) (grid k)] using
        abs_sub_le (grid j) (ordinate (badAt j)) (grid k)
    exact not_lt_of_ge (hGridGap hDifferent) (hTri.trans_lt hPair)
  have hCard : S.card + 1 ≤ S.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective badAt hInjective
  omega
end Goldbach
namespace Goldbach

open Complex Set

noncomputable section


def contourLog {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  -logDeriv (regularizedL χ) z + principalFlag χ / (z - 1)

def UniformDirichletLogDerivative (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t d : ℝ),
    σ ∈ Icc (9 / 20 : ℝ) 2 → 0 < d →
    (∀ ρ : ℂ, 0 < ρ.re → regularizedL χ ρ = 0 → d ≤ ‖((σ : ℂ) + (t : ℂ) * I) - ρ‖) →
    ‖logDeriv (regularizedL χ) ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * logHeight q t * (1 + d⁻¹)


end
end Goldbach

open Complex Set MeasureTheory
open scoped BigOperators Interval


open Filter Set
open scoped BigOperators Topology


open Complex Filter Set MeasureTheory
open scoped BigOperators Interval Topology

namespace Goldbach

/-- Finite contour identity for the weighted logarithmic derivative with the
principal pole at one restored explicitly. -/
theorem rectBoundaryIntegral_neg_logDeriv_add_pole_mul
    {a b c d : ℝ} (F K : ℂ → ℂ) (S : Finset ℂ) (δ : ℂ)
    (ha : a < 1) (hb : 1 < b) (hc : c < 0) (hd : 0 < d)
    (hF : AnalyticOnNhd ℂ F (Icc a b ×ℂ Icc c d))
    (hK : AnalyticOnNhd ℂ K (Icc a b ×ℂ Icc c d))
    (hzeros : ∀ z ∈ Icc a b ×ℂ Icc c d, F z = 0 ↔ z ∈ S)
    (hinterior : ∀ p ∈ S, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d)
    (horder : ∀ p ∈ S, analyticOrderAt F p ≠ ⊤) (hF1 : F 1 ≠ 0) :
    rectBoundaryIntegral (fun z => (-logDeriv F z + δ / (z - 1)) * K z) a b c d =
      (2 * (Real.pi : ℂ) * I) * (δ * K 1 - ∑ p ∈ S, (analyticOrderNatAt F p : ℂ) * K p) := by
  classical
  let U := Icc a b ×ℂ Icc c d
  let T := insert (1 : ℂ) S
  let r : ℂ → ℂ := fun p => (analyticOrderNatAt F p : ℂ) * K p
  let coeff : ℂ → ℂ := fun p => if p = 1 then δ * K 1 else -r p
  have h1U : (1 : ℂ) ∈ U := by
    exact mem_reProdIm.mpr ⟨by simpa only [one_re] using Set.mem_Icc.mpr ⟨ha.le, hb.le⟩,
      by simpa only [one_im] using Set.mem_Icc.mpr ⟨hc.le, hd.le⟩⟩
  have h1S : (1 : ℂ) ∉ S := fun h => hF1 ((hzeros 1 h1U).mpr h)
  have hSU : (S : Set ℂ) ⊆ U := by
    intro p hp
    obtain ⟨hpa, hpb, hpc, hpd⟩ := hinterior p hp
    exact mem_reProdIm.mpr ⟨⟨hpa.le, hpb.le⟩, ⟨hpc.le, hpd.le⟩⟩
  have hT : ∀ p ∈ T, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simpa only [one_re, one_im] using And.intro ha (And.intro hb (And.intro hc hd))
    · exact hinterior p hp
  have hcoeff1 : coeff 1 = δ * K 1 := ite_eq_left rfl
  have hcoeff (p : ℂ) (hp : p ∈ S) : coeff p = -r p := by
    have hp1 : p ≠ (1 : ℂ) := fun heq => h1S (heq ▸ hp)
    exact ite_eq_right hp1
  have hsum (z : ℂ) :
      (∑ p ∈ T, coeff p / (z - p)) =
        δ * K 1 / (z - 1) - ∑ p ∈ S, r p / (z - p) := by
    have hsumS : (∑ p ∈ S, coeff p / (z - p)) = -(∑ p ∈ S, r p / (z - p)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p hp => by rw [hcoeff p hp, neg_div]
    change (∑ p ∈ insert (1 : ℂ) S, coeff p / (z - p)) = _
    rw [Finset.sum_insert h1S, hcoeff1, hsumS]
    exact (sub_eq_add_neg _ _).symm
  have hsum_coeff : (∑ p ∈ T, coeff p) = δ * K 1 - ∑ p ∈ S, r p := by
    have hsumS : (∑ p ∈ S, coeff p) = -(∑ p ∈ S, r p) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl hcoeff
    change (∑ p ∈ insert (1 : ℂ) S, coeff p) = _
    rw [Finset.sum_insert h1S, hcoeff1, hsumS, sub_eq_add_neg]
  obtain ⟨G, hG, hG_eq⟩ := logDeriv_mul_exists_analytic_remainder S hSU hF hK
    (fun z hz => (hzeros z hz).mp) horder
  let J : ℂ → ℂ := fun z => -G z + δ * dslope K 1 z
  have hJ : AnalyticOnNhd ℂ J U := by
    intro z hz
    exact (hG z hz).neg.add (analyticAt_const.mul ((hK z hz).dslope 1))
  have hJ_diff : ∀ z ∈ (Ioo a b ×ℂ Ioo c d) \ (T : Set ℂ), DifferentiableAt ℂ J z := by
    intro z hz
    obtain ⟨hr, hi⟩ := mem_reProdIm.mp hz.1
    exact (hJ z (mem_reProdIm.mpr ⟨Ioo_subset_Icc_self hr, Ioo_subset_Icc_self hi⟩)).differentiableAt
  have hEq : EqOn (fun z => (-logDeriv F z + δ / (z - 1)) * K z)
      (fun z => J z + ∑ p ∈ T, coeff p / (z - p)) (U \ (T : Set ℂ)) := by
    intro z hz
    have hzT : z ∉ T := hz.2
    have hzS : z ∉ S := fun h => hzT (Finset.mem_insert_of_mem h)
    have hz1 : z ≠ (1 : ℂ) := fun h => hzT (Finset.mem_insert.mpr (Or.inl h))
    have hGK := hG_eq ⟨hz.1, hzS⟩
    change logDeriv F z * K z = G z + ∑ p ∈ S, r p / (z - p) at hGK
    have hds : dslope K 1 z = (K z - K 1) / (z - 1) := by
      apply (eq_div_iff (sub_ne_zero.mpr hz1)).mpr
      simpa only [smul_eq_mul, mul_comm] using sub_smul_dslope K 1 z
    change (-logDeriv F z + δ / (z - 1)) * K z =
      (-G z + δ * dslope K 1 z) + ∑ p ∈ T, coeff p / (z - p)
    rw [hsum, hds]
    calc
      _ = -(logDeriv F z * K z) + δ / (z - 1) * K z := by ring
      _ = _ := by rw [hGK]; ring
  rw [rectBoundaryIntegral_eq_sum_residues (ha.le.trans hb.le) (hc.le.trans hd.le)
    _ J T coeff hT hJ.continuousOn hJ_diff hEq, hsum_coeff]

/-- Solve a rectangular contour identity for its right vertical integral. -/
theorem right_vertical_integral_of_rect {f : ℂ → ℂ} {a b c d : ℝ} {R : ℂ}
    (h : rectBoundaryIntegral f a b c d = 2 * (Real.pi : ℂ) * I * R) :
    (∫ y : ℝ in c..d, f (b + y * I)) =
      (∫ y : ℝ in c..d, f (a + y * I)) + 2 * (Real.pi : ℂ) * R +
        I * ((∫ x : ℝ in a..b, f (x + c * I)) - ∫ x : ℝ in a..b, f (x + d * I)) := by
  unfold rectBoundaryIntegral at h
  set bottom := (∫ x : ℝ in a..b, f (x + c * I))
  set top := (∫ x : ℝ in a..b, f (x + d * I))
  set left := (∫ y : ℝ in c..d, f (a + y * I))
  set right := (∫ y : ℝ in c..d, f (b + y * I))
  calc
    right = left - I * (bottom - top + I * right - I * left) + I * (bottom - top) := by
      ring_nf
      simp only [I_sq]
      ring
    _ = _ := by
      rw [h]
      ring_nf
      simp only [I_sq]
      ring

end Goldbach
namespace Goldbach

open Complex Filter MeasureTheory Set
open scoped BigOperators Interval Topology

theorem uniform_dirichlet_log_control : ∃ C : ℝ, 0 < C ∧ UniformDirichletLogDerivative C := by
  obtain ⟨C, hC, h⟩ := norm_logDeriv_regularizedL_le
  refine ⟨C, hC, ?_⟩
  intro q _ χ σ t d hσ hd hdist
  have hpoint : (⟨σ, t⟩ : ℂ) = (σ : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [← hpoint] at hdist ⊢
  exact h q χ t σ d hσ.1 hσ.2 hd hdist
end Goldbach
end
end
end

section
open Set MeasureTheory

namespace GoldbachOscillation


private noncomputable def R' (L y : ℝ) := (L^2-y^2) / (D L y)^2


private theorem D_pos {L : ℝ} (hL : 0 < L) (y : ℝ) : 0 < D L y := by unfold D; positivity

private theorem R_deriv {L : ℝ} (hL : 0 < L) (y : ℝ) : HasDerivAt (R L) (R' L y) y := by
  have h := (hasDerivAt_id y).div ((hasDerivAt_const y (L^2)).add ((hasDerivAt_id y).pow 2))
    (D_pos hL y).ne'
  convert h using 1
  · rfl
  unfold R' D
  simp
  ring

private theorem J_deriv {L : ℝ} (hL : 0 < L) (y : ℝ) : HasDerivAt (J L) (1 / D L y) y := by
  have h := ((Real.hasDerivAt_arctan (y/L)).comp y ((hasDerivAt_id y).div_const L)).div_const L
  convert h using 1
  · rfl
  unfold D
  field_simp [hL.ne']

private theorem wave_deriv (y : ℝ) :
    HasDerivAt wave (wave y * Complex.I) y := by
  simpa [wave] using! (((hasDerivAt_id (y:ℂ)).mul_const Complex.I).cexp).comp_ofReal

private theorem wave_norm (y : ℝ) : ‖wave y‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem R_bound {L : ℝ} (hL : 0 < L) (y : ℝ) : |R L y| ≤ 1/L := by
  rw [R, abs_div, abs_of_pos (D_pos hL y)]
  apply (div_le_div_iff₀ (D_pos hL y) hL).mpr
  unfold D
  nlinarith only [sq_nonneg (L-|y|), sq_abs y, mul_nonneg hL.le (abs_nonneg y)]

private theorem R'_bound {L : ℝ} (hL : 0 < L) (y : ℝ) : |R' L y| ≤ 1 / D L y := by
  have hp := D_pos hL y
  rw [R', abs_div, abs_of_pos (sq_pos_of_pos hp)]
  have hab : |L^2-y^2| ≤ D L y := abs_le.mpr ⟨by dsimp [D]; nlinarith [sq_nonneg L],
    by dsimp [D]; nlinarith [sq_nonneg y]⟩
  apply (div_le_div_iff₀ (sq_pos_of_pos hp) hp).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hab hp.le]

private theorem remainder {L : ℝ} (hL : 0 < L) (y : ℝ) :
    1-y*R L y = L^2 / D L y := by
  unfold R
  field_simp [(D_pos hL y).ne']
  unfold D
  ring

private noncomputable def mainTerm (w f : ℝ → ℝ) (x : ℝ) : ℂ := (w x:ℂ)*wave (f x)
private noncomputable def primitive (L : ℝ) (w f p : ℝ → ℝ) (x : ℝ) : ℂ :=
  -Complex.I*((w x * R L (p x) : ℝ):ℂ)*wave (f x)
private noncomputable def errorTerm (L : ℝ) (w dw f p dp : ℝ → ℝ) (x : ℝ) : ℂ :=
  wave (f x) * (((w x * (1-p x*R L (p x)) : ℝ):ℂ) +
    Complex.I * ((dw x*R L (p x)+w x*R' L (p x)*dp x : ℝ):ℂ))

private theorem primitive_deriv {L x : ℝ} (hL : 0 < L) {w dw f p dp : ℝ → ℝ}
    (hw : HasDerivAt w (dw x) x) (hf : HasDerivAt f (p x) x) (hp : HasDerivAt p (dp x) x) :
    HasDerivAt (primitive L w f p) (mainTerm w f x - errorTerm L w dw f p dp x) x := by
  have hr := (R_deriv hL (p x)).comp x hp
  have hd := (((hw.mul hr).ofReal_comp.const_mul (-Complex.I)).mul ((wave_deriv (f x)).scomp x hf))
  convert hd using 1
  · rfl
  dsimp [mainTerm, errorTerm]
  push_cast
  ring_nf
  simp [Complex.I_sq]

private theorem primitive_bound {L x : ℝ} (hL : 0 < L) (w f p : ℝ → ℝ)
    (hw : |w x| ≤ 1) : ‖primitive L w f p x‖ ≤ 1/L := by
  simp only [primitive, norm_mul, norm_neg, Complex.norm_I, one_mul, wave_norm,
    mul_one, Complex.norm_real, Real.norm_eq_abs]
  simpa using mul_le_mul hw (R_bound hL (p x)) (abs_nonneg _) zero_le_one

private theorem error_bound {L x : ℝ} (hL : 0 < L) (w dw f p dp : ℝ → ℝ)
    (hw : |w x| ≤ 1) (hdw : |dw x| ≤ 1) (hcurv : L^2 ≤ 4*dp x) :
    ‖errorTerm L w dw f p dp x‖ ≤ 1/L + 5 * (dp x / D L (p x)) := by
  have hd := D_pos hL (p x)
  have hp : 0 ≤ dp x := by nlinarith only [sq_nonneg L,hcurv]
  rw [errorTerm, norm_mul, wave_norm, one_mul]
  apply (norm_add_le ..).trans
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    remainder hL, abs_of_nonneg (div_nonneg (sq_nonneg L) hd.le)]
  have hfirst := mul_le_of_le_one_left (div_nonneg (sq_nonneg L) hd.le) hw
  have hsecond : |dw x*R L (p x)| ≤ 1/L := by
    rw [abs_mul]
    simpa using mul_le_mul hdw (R_bound hL _) (abs_nonneg _) zero_le_one
  have hthird : |w x*R' L (p x)*dp x| ≤ dp x/D L (p x) := by
    simp only [abs_mul, abs_of_nonneg hp]
    have hs : |w x| * |R' L (p x)| ≤ 1/D L (p x) := by
      simpa using mul_le_mul hw (R'_bound hL _) (abs_nonneg _) zero_le_one
    simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hs hp
  have hscale := div_le_div_of_nonneg_right hcurv hd.le
  rw [mul_div_assoc] at hscale
  have htriangle := abs_add_le (dw x*R L (p x)) (w x*R' L (p x)*dp x)
  linarith

/-- A regularized integration by parts works across a possible stationary point.
The arctangent controls the total variation of the multiplier. -/
private theorem regularized {a b L : ℝ} (hab : a ≤ b) (hlen : b-a ≤ 1) (hL : 0 < L)
    (w dw f p dp : ℝ → ℝ)
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (dw x) x)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (p x) x)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (dp x) x)
    (hcw : ContinuousOn dw (Icc a b)) (hcp : ContinuousOn dp (Icc a b))
    (hw1 : ∀ x ∈ Icc a b, |w x| ≤ 1) (hdw1 : ∀ x ∈ Icc a b, |dw x| ≤ 1)
    (hcurv : ∀ x ∈ Icc a b, L^2 ≤ 4*dp x) :
    ‖∫ x in a..b, mainTerm w f x‖ ≤ (3+5*Real.pi)/L := by
  have cw := HasDerivAt.continuousOn hw
  have cf := HasDerivAt.continuousOn hf
  have cp := HasDerivAt.continuousOn hp
  have cR : Continuous (R L) := continuous_iff_continuousAt.mpr fun y => (R_deriv hL y).continuousAt
  have cD : Continuous (D L) := by unfold D; fun_prop
  have cR' : Continuous (R' L) := by
    unfold R'
    exact (continuous_const.sub (continuous_id.pow 2)).div (cD.pow 2) (fun y => (sq_pos_of_pos (D_pos hL y)).ne')
  have cWave : Continuous wave := continuous_iff_continuousAt.mpr fun y => (wave_deriv y).continuousAt
  have cwav := cWave.comp_continuousOn cf
  have cr := cR.comp_continuousOn cp
  have cr' := cR'.comp_continuousOn cp
  have mainC : ContinuousOn (mainTerm w f) (Icc a b) := by unfold mainTerm; fun_prop
  have errC : ContinuousOn (errorTerm L w dw f p dp) (Icc a b) := by unfold errorTerm; fun_prop
  have mainI := mainC.intervalIntegrable_of_Icc (μ := volume) hab
  have errI := errC.intervalIntegrable_of_Icc (μ := volume) hab
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := primitive L w f p) (f' := fun x => mainTerm w f x - errorTerm L w dw f p dp x)
    (fun x hx => by rw [uIcc_of_le hab] at hx; exact primitive_deriv hL (hw x hx) (hf x hx) (hp x hx))
    (mainI.sub errI)
  rw [intervalIntegral.integral_sub mainI errI] at identity
  let density := fun x => dp x / D L (p x)
  have denC : ContinuousOn density (Icc a b) :=
    hcp.div (cD.comp_continuousOn cp) (fun x _ => (D_pos hL (p x)).ne')
  have di := denC.intervalIntegrable_of_Icc (μ := volume) hab
  have jd := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := J L ∘ p) (f' := density) (fun x hx => by
      rw [uIcc_of_le hab] at hx
      convert (J_deriv hL (p x)).comp x (hp x hx) using 1
      dsimp [density]; ring) di
  -- Integrating the positive density only costs the range of arctan, divided by L.
  have jbound : (∫ x in a..b, density x) ≤ Real.pi/L := by
    rw [jd]
    dsimp [J]
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ hL.le
    linarith only [Real.arctan_lt_pi_div_two (p b/L), Real.neg_pi_div_two_lt_arctan (p a/L)]
  have errBound := intervalIntegral.norm_integral_le_of_norm_le hab
    (g := fun x => 1/L + 5 * density x) (Filter.Eventually.of_forall fun x hx =>
      error_bound hL w dw f p dp (hw1 x ⟨hx.1.le,hx.2⟩) (hdw1 x ⟨hx.1.le,hx.2⟩) (hcurv x ⟨hx.1.le,hx.2⟩))
    (intervalIntegrable_const.add (di.const_mul 5))
  rw [intervalIntegral.integral_add intervalIntegrable_const (di.const_mul 5),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul] at errBound
  have lhs : (∫ x in a..b, mainTerm w f x) =
      (primitive L w f p b - primitive L w f p a) + ∫ x in a..b, errorTerm L w dw f p dp x :=
    sub_eq_iff_eq_add.mp identity
  rw [lhs]
  apply (norm_add_le ..).trans
  have nd := norm_sub_le (primitive L w f p b) (primitive L w f p a)
  have ba := primitive_bound hL w f p (hw1 a (left_mem_Icc.mpr hab))
  have bb := primitive_bound hL w f p (hw1 b (right_mem_Icc.mpr hab))
  have length := mul_le_mul_of_nonneg_right hlen (one_div_nonneg.mpr hL.le)
  rw [add_div, mul_div_assoc]
  rw [show 3/L = 3*(1/L) by ring]
  linarith only [ba,bb,nd,errBound,length,jbound]


private theorem dyadic_minus {a b γ σ : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hγ : 0 < γ) (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (β : ℝ) :
    ‖∫ x in a..b, kernel σ β (-γ) x‖ ≤ (3+5*Real.pi)/Real.sqrt γ := by
  let w := fun x : ℝ => x^(σ-1)
  let dw := fun x : ℝ => (σ-1)*x^(σ-1-1)
  let f := fun x : ℝ => β*x+(-γ)*Real.log x
  let p := fun x : ℝ => β-γ/x
  let dp := fun x : ℝ => γ/x^2
  have hx {x : ℝ} (h : x ∈ Icc a b) : 1 ≤ x := ha.trans h.1
  have hxp {x : ℝ} (h : x ∈ Icc a b) : 0 < x := zero_lt_one.trans_le (hx h)
  apply regularized hab (by linarith) (Real.sqrt_pos.mpr hγ) w dw f p dp
  · intro x h
    exact Real.hasDerivAt_rpow_const (Or.inl (hxp h).ne')
  · intro x h
    have h' := ((hasDerivAt_id x).const_mul β).add ((Real.hasDerivAt_log (hxp h).ne').const_mul (-γ))
    convert h' using 1
    · rfl
    dsimp [p]; ring
  · intro x h
    have h' := (hasDerivAt_const x β).sub ((hasDerivAt_const x γ).div (hasDerivAt_id x) (hxp h).ne')
    convert h' using 1
    · rfl
    dsimp [dp]; ring
  · unfold dw; fun_prop (disch := solve_by_elim [ne_of_gt, hxp])
  · change ContinuousOn (fun x : ℝ => γ/x^2) (Icc a b)
    fun_prop (disch := intro x hx; exact pow_ne_zero 2 (hxp hx).ne')
  · intro x h
    dsimp [w]
    rw [abs_of_nonneg (Real.rpow_nonneg (hxp h).le _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (hx h) (by linarith)
  · intro x h
    dsimp [dw]
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hσ'), abs_of_nonneg (Real.rpow_nonneg (hxp h).le _)]
    have h1 : -(σ-1) ≤ 1 := by linarith
    have h2 := Real.rpow_le_one_of_one_le_of_nonpos (hx h) (show σ-1-1 ≤ 0 by linarith)
    simpa using mul_le_mul h1 h2 (Real.rpow_nonneg (hxp h).le _) zero_le_one
  · intro x h
    rw [Real.sq_sqrt hγ.le]
    change γ ≤ 4*(γ/x^2)
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos (hxp h))).mpr
    have h2 := pow_le_pow_left₀ (hxp h).le (h.2.trans hb) 2
    nlinarith only [mul_le_mul_of_nonneg_left h2 hγ.le]

open scoped ComplexConjugate

private theorem wave_add (u v : ℝ) : wave (u+v) = wave u * wave v := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem conjugate_kernel (σ β γ x : ℝ) :
    conj (kernel σ (-β) (-γ) x) = kernel σ β γ x := by
  unfold kernel wave
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp
  ring

private theorem dyadic {a b γ σ : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hγ : γ ≠ 0) (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (β : ℝ) :
    ‖∫ x in a..b, kernel σ β γ x‖ ≤ min 1 ((3+5*Real.pi)/Real.sqrt |γ|) := by
  apply le_min
  · have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (f := kernel σ β γ) (C := 1) (fun x hx => by
        rw [uIoc_of_le hab] at hx
        have h1 := ha.trans hx.1.le
        rw [kernel, norm_mul, wave_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans h1) _)]
        exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith))
    rw [abs_of_nonneg (sub_nonneg.mpr hab), one_mul] at h
    exact h.trans (by linarith)
  · rcases lt_or_gt_of_ne hγ with hn | hpos
    · simpa [abs_of_neg hn] using dyadic_minus ha hab hb (neg_pos.mpr hn) hσ hσ' β
    · have id : (∫ x in a..b, kernel σ β γ x) = conj (∫ x in a..b, kernel σ (-β) (-γ) x) := by
        rw [← intervalIntegral.intervalIntegral_conj]
        exact intervalIntegral.integral_congr fun x _ => (conjugate_kernel σ β γ x).symm
      rw [id, Complex.norm_conj, abs_of_pos hpos]
      exact dyadic_minus ha hab hb hpos hσ hσ' (-β)

private theorem rescale {Y x : ℝ} (hY : 0 < Y) (hx : 0 < x) (σ β γ : ℝ) :
    kernel σ β γ (Y*x) = (((Y^(σ-1):ℝ):ℂ)*wave (γ*Real.log Y)) * kernel σ (β*Y) γ x := by
  unfold kernel
  rw [Real.mul_rpow hY.le hx.le, Real.log_mul hY.ne' hx.ne',
    show β*(Y*x)+γ*(Real.log Y+Real.log x) = γ*Real.log Y + ((β*Y)*x+γ*Real.log x) by ring, wave_add]
  push_cast
  ring

/- Away from a stationary point, integrate with the reciprocal of βx+γ.
Its fixed-sign derivative gives a total variation bound from the endpoints. -/
set_option maxHeartbeats 600000 in
private theorem separated {a b σ γ β H : ℝ} (ha : 0 < a) (hab : a ≤ b) (hσ : 0 ≤ σ)
    (hH : 0 < H) (hsep : ∀ x ∈ Icc a b, H ≤ |β*x+γ|) :
    ‖∫ x in a..b, kernel σ β γ x‖ ≤ 5*b^σ/H := by
  let F := fun x : ℝ => β*x + γ*Real.log x
  let p := fun x : ℝ => β+γ/x
  let W := fun x : ℝ => x^σ
  let dW := fun x : ℝ => σ*x^(σ-1)
  let z := fun x : ℝ => 1/(β*x+γ)
  let dz := fun x : ℝ => -β/(β*x+γ)^2
  let B := fun x : ℝ => -Complex.I*((W x*z x : ℝ):ℂ)*wave (F x)
  let er := fun x : ℝ => Complex.I*((dW x*z x+W x*dz x : ℝ):ℂ)*wave (F x)
  have pos {x : ℝ} (hx : x ∈ Icc a b) : 0 < x := ha.trans_le hx.1
  have nz {x : ℝ} (hx : x ∈ Icc a b) : β*x+γ ≠ 0 := abs_pos.mp (hH.trans_le (hsep x hx))
  have zd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt z (dz x) x := by
    have h := (hasDerivAt_const x (1:ℝ)).div (((hasDerivAt_id x).const_mul β).add_const γ) (nz hx)
    convert h using 1 <;> first | rfl | (dsimp [dz]; ring)
  have wd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt W (dW x) x :=
    Real.hasDerivAt_rpow_const (Or.inl (pos hx).ne')
  have fd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt F (p x) x := by
    have h := ((hasDerivAt_id x).const_mul β).add ((Real.hasDerivAt_log (pos hx).ne').const_mul γ)
    convert h using 1 <;> first | rfl | (dsimp [p]; ring)
  have hB (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt B (kernel σ β γ x - er x) x := by
    have hv := ((((wd x hx).mul (zd x hx)).ofReal_comp.const_mul (-Complex.I)).mul
      ((wave_deriv (F x)).scomp x (fd x hx)))
    have unit : W x*z x*p x = x^(σ-1) := by
      dsimp [W,z,p]
      rw [Real.rpow_sub_one (pos hx).ne']
      field_simp [(nz hx),(pos hx).ne']
    have hu : (W x:ℂ)*(z x:ℂ)*(p x:ℂ) = ((x^(σ-1):ℝ):ℂ) := by exact_mod_cast unit
    convert hv using 1
    · rfl
    change ((x^(σ-1):ℝ):ℂ)*wave (F x) - er x = _
    dsimp only [er, Pi.mul_apply, Function.comp_apply]
    push_cast
    rw [← hu]
    simp only [Complex.real_smul]
    linear_combination ((W x:ℂ)*(z x:ℂ)*(p x:ℂ)*wave (F x)) * Complex.I_sq
  have cw := HasDerivAt.continuousOn wd
  have cz := HasDerivAt.continuousOn zd
  have cf := HasDerivAt.continuousOn fd
  have cdw : ContinuousOn dW (Icc a b) := by unfold dW; fun_prop (disch := solve_by_elim [ne_of_gt,pos])
  have cdz : ContinuousOn dz (Icc a b) := by unfold dz; fun_prop (disch := intro x hx; exact pow_ne_zero _ (nz hx))
  have cwave : Continuous wave := continuous_iff_continuousAt.mpr fun y => (wave_deriv y).continuousAt
  have cwF := cwave.comp_continuousOn cf
  have ce : ContinuousOn er (Icc a b) := by unfold er; fun_prop
  have ck : ContinuousOn (kernel σ β γ) (Icc a b) := by
    change ContinuousOn (fun x : ℝ => ((x^(σ-1):ℝ):ℂ)*wave (F x)) _
    have hc : ContinuousOn (fun x : ℝ => x^(σ-1)) (Icc a b) :=
      continuousOn_id.rpow_const fun _ hx => Or.inl (pos hx).ne'
    exact (Complex.continuous_ofReal.comp_continuousOn hc).mul cwF
  have ei := ce.intervalIntegrable_of_Icc (μ := volume) hab
  have ki := ck.intervalIntegrable_of_Icc (μ := volume) hab
  have fi := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := B)
    (f' := fun x => kernel σ β γ x - er x)
    (fun x hx => hB x ((uIcc_of_le hab) ▸ hx)) (ki.sub ei)
  rw [intervalIntegral.integral_sub ki ei] at fi
  have zi := cdz.intervalIntegrable_of_Icc (μ := volume) hab
  have wi := cdw.intervalIntegrable_of_Icc (μ := volume) hab
  have wint := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := W) (f' := dW)
    (fun x hx => wd x ((uIcc_of_le hab) ▸ hx)) wi
  have zint := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := z) (f' := dz)
    (fun x hx => zd x ((uIcc_of_le hab) ▸ hx)) zi
  have zmax (x : ℝ) (hx : x ∈ Icc a b) : |z x| ≤ 1/H := by
    simp only [z, abs_div, abs_one]
    exact one_div_le_one_div_of_le hH (hsep x hx)
  have Wmax (x : ℝ) (hx : x ∈ Icc a b) : |W x| ≤ b^σ := by
    rw [abs_of_nonneg (Real.rpow_nonneg (pos hx).le _)]
    exact Real.rpow_le_rpow (pos hx).le hx.2 hσ
  have Bmax (x : ℝ) (hx : x ∈ Icc a b) : ‖B x‖ ≤ b^σ/H := by
    simp only [B, norm_mul, norm_neg, Complex.norm_I, wave_norm, one_mul, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    simpa [div_eq_mul_inv] using mul_le_mul (Wmax x hx) (zmax x hx) (abs_nonneg _) (Real.rpow_nonneg (ha.trans_le hab).le _)
  -- The sign of β determines the monotonicity of the reciprocal on this interval.
  have zvar : (∫ x in a..b, |dz x|) ≤ 2/H := by
    have sign {x : ℝ} : 0 ≤ (β*x+γ)^2 := sq_nonneg _
    have za := abs_le.mp (zmax a (left_mem_Icc.mpr hab))
    have zb := abs_le.mp (zmax b (right_mem_Icc.mpr hab))
    rcases le_total 0 β with hp | hn
    · have he : (∫ x in a..b, |dz x|) = -(z b-z a) := by
        rw [← zint, ← intervalIntegral.integral_neg]
        exact intervalIntegral.integral_congr fun x _ => abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp) sign)
      rw [he,show 2/H = 2*(1/H) by ring]; linarith
    · have he : (∫ x in a..b, |dz x|) = z b-z a := by
        rw [← zint]
        exact intervalIntegral.integral_congr fun x _ => abs_of_nonneg (div_nonneg (neg_nonneg.mpr hn) sign)
      rw [he,show 2/H = 2*(1/H) by ring]; linarith
  have eBound (x : ℝ) (hx : x ∈ Icc a b) : ‖er x‖ ≤ dW x*(1/H) + b^σ*|dz x| := by
    simp only [er, norm_mul, Complex.norm_I, one_mul, wave_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    apply (abs_add_le ..).trans
    rw [abs_mul (dW x) (z x), abs_mul (W x) (dz x), abs_of_nonneg (show 0 ≤ dW x from mul_nonneg hσ (Real.rpow_nonneg (pos hx).le _))]
    exact add_le_add (mul_le_mul_of_nonneg_left (zmax x hx) (mul_nonneg hσ (Real.rpow_nonneg (pos hx).le _)))
      (mul_le_mul_of_nonneg_right (Wmax x hx) (abs_nonneg _))
  have ai := cdz.abs.intervalIntegrable_of_Icc (μ := volume) hab
  have eint := intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall fun x hx => eBound x ⟨hx.1.le,hx.2⟩)
    ((wi.mul_const (1/H)).add (ai.const_mul (b^σ)))
  rw [intervalIntegral.integral_add (wi.mul_const (1/H)) (ai.const_mul (b^σ)),
    intervalIntegral.integral_mul_const (1/H) dW, intervalIntegral.integral_const_mul (b^σ) (fun x => |dz x|), wint] at eint
  rw [sub_eq_iff_eq_add.mp fi]
  apply (norm_add_le ..).trans
  have bd := norm_sub_le (B b) (B a)
  have bl := Bmax a (left_mem_Icc.mpr hab)
  have br := Bmax b (right_mem_Icc.mpr hab)
  have vb := mul_le_mul_of_nonneg_left zvar (Real.rpow_nonneg (ha.trans_le hab).le σ)
  have wa : 0 ≤ W a := Real.rpow_nonneg ha.le _
  have wb := mul_le_mul_of_nonneg_right (show W b-W a ≤ b^σ from sub_le_self _ wa) (one_div_nonneg.mpr hH.le)
  simp only [div_eq_mul_inv,one_mul] at bl br vb eint wb ⊢
  linarith only [bd,bl,br,vb,eint,wb]

/-- The bound holds through a stationary point and is uniform in the additive
frequency. The factor X^σ comes from scaling the dyadic interval. -/
private theorem uniform_bound :
    ∀ (X a b σ γ β : ℝ), 0 < X → X ≤ a → a ≤ b → b ≤ 2*X →
      0 ≤ σ → σ ≤ 1 → γ ≠ 0 →
      ‖∫ x in a..b, ((x^(σ-1):ℝ):ℂ) *
        Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)‖ ≤
        X^σ * min 1 ((3+5*Real.pi)/Real.sqrt |γ|) := by
  intro X a b σ γ β hX ha hab hb hσ hσ' hγ
  let l := a/X
  let r := b/X
  have h1 : 1 ≤ l := (one_le_div hX).mpr ha
  have hlr : l ≤ r := div_le_div_of_nonneg_right hab hX.le
  have h2 : r ≤ 2 := (div_le_iff₀ hX).mpr hb
  let z : ℂ := ((X^(σ-1):ℝ):ℂ)*wave (γ*Real.log X)
  have hz : ‖z‖ = X^(σ-1) := by
    simp only [z, norm_mul, wave_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hX.le _)]
  have eqn : (∫ x in l..r, kernel σ β γ (X*x)) = z * (∫ x in l..r, kernel σ (β*X) γ x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hlr] at hx
    exact rescale hX (zero_lt_one.trans_le (h1.trans hx.1)) σ β γ
  have sub := intervalIntegral.integral_comp_mul_left (kernel σ β γ) (a := l) (b := r) hX.ne'
  have hx1 : X*l = a := by dsimp [l]; field_simp
  have hx2 : X*r = b := by dsimp [r]; field_simp
  rw [sub,hx1,hx2] at eqn
  have eqnorm := congrArg norm eqn
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hX), norm_mul, hz] at eqnorm
  have hxpow : X * X^(σ-1) = X^σ := by
    calc
      _ = X^(1:ℝ) * X^(σ-1) := by rw [Real.rpow_one]
      _ = X^(1+(σ-1)) := (Real.rpow_add hX _ _).symm
      _ = _ := by rw [show (1:ℝ)+(σ-1)=σ by ring]
  change ‖∫ x in a..b, kernel σ β γ x‖ ≤ _
  calc
    _ = X*(X^(σ-1) * ‖∫ x in l..r, kernel σ (β*X) γ x‖) := by
      rw [← eqnorm, ← mul_assoc, mul_inv_cancel₀ hX.ne', one_mul]
    _ ≤ X^σ * min 1 ((3+5*Real.pi)/Real.sqrt |γ|) := by
      rw [← mul_assoc, hxpow]
      exact mul_le_mul_of_nonneg_left (dyadic h1 hlr h2 hγ hσ hσ' (β*X)) (Real.rpow_nonneg hX.le _)

/-- A dyadic piece of the additively twisted zero kernel. The curvature bound is
uniform in the frequency, and a lower bound on the absolute phase slope gives
stronger decay when the interval misses the stationary point. -/
theorem per_ordinate :
    ∀ (X a b σ γ β : ℝ), 0 < X → X ≤ a → a ≤ b → b ≤ 2*X → 0 ≤ σ → σ ≤ 1 →
      let K := ∫ x in a..b, ((x^(σ-1):ℝ):ℂ) *
        Complex.exp (((β*x+γ*Real.log x:ℝ):ℂ)*Complex.I)
      ‖K‖ ≤ X^σ ∧
      (γ ≠ 0 → ‖K‖ ≤ X^σ * ((3+5*Real.pi)/Real.sqrt |γ|)) ∧
      ∀ H : ℝ, 0 < H → (∀ x ∈ Set.Icc a b, H ≤ |β*x+γ|) → ‖K‖ ≤ 5*b^σ/H := by
  intro X a b σ γ β hX ha hab hb hσ hσ' K
  refine ⟨?_, ?_, fun H hH hsep => separated (hX.trans_le ha) hab hσ hH hsep⟩
  · have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := kernel σ β γ)
      (C := X^(σ-1)) (a := a) (b := b) (fun x hx => by
        rw [uIoc_of_le hab] at hx
        have hxx := ha.trans hx.1.le
        rw [kernel,norm_mul,wave_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (hX.le.trans hxx) _)]
        exact Real.rpow_le_rpow_of_nonpos hX hxx (sub_nonpos.mpr hσ'))
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h
    have hb' : b-a ≤ X := by linarith
    apply h.trans
    calc
      _ ≤ X^(σ-1)*X := mul_le_mul_of_nonneg_left hb' (Real.rpow_nonneg hX.le _)
      _ = _ := by rw [Real.rpow_sub_one hX.ne', div_mul_cancel₀ _ hX.ne']
  · intro hγ
    exact (uniform_bound X a b σ γ β hX ha hab hb hσ hσ' hγ).trans
      (mul_le_mul_of_nonneg_left (min_le_right ..) (Real.rpow_nonneg hX.le _))
end GoldbachOscillation
end

section
open Set Filter MeasureTheory Complex
open scoped Topology Interval

noncomputable section

namespace GoldbachTwistedMellin

/-- The trapezoid rises on [a,a+1] and falls on [b,b+1]. For integral
endpoints it agrees with the sharp interval (a,b] at every integer. -/
def taper (a b x : ℝ) : ℝ := max 0 (min (x-a) (min 1 (b+1-x)))


def test (a b β x : ℝ) : ℂ := (taper a b x:ℂ)*phase β x

def transform (a b β : ℝ) (s : ℂ) : ℂ := mellin (test a b β) s

theorem taper_left {a b x : ℝ} (h : x ≤ a) : taper a b x = 0 := by
  exact max_eq_left ((min_le_left ..).trans (sub_nonpos.mpr h))

theorem taper_right {a b x : ℝ} (h : b+1 ≤ x) : taper a b x = 0 := by
  exact max_eq_left ((min_le_right ..).trans ((min_le_right ..).trans (sub_nonpos.mpr h)))

theorem taper_rise {a b x : ℝ} (h : a+1 ≤ b) (hx : x ∈ Icc a (a+1)) :
    taper a b x = x-a := by
  rw [taper,min_eq_left (le_min (by linarith [hx.2]) (by linarith [hx.1,hx.2])),
    max_eq_right (sub_nonneg.mpr hx.1)]

theorem taper_flat {a b x : ℝ} (hx : x ∈ Icc (a+1) b) : taper a b x = 1 := by
  rw [taper,min_eq_left (show 1 ≤ b+1-x by linarith [hx.2]),
    min_eq_right (show 1 ≤ x-a by linarith [hx.1]),max_eq_right zero_le_one]

theorem taper_fall {a b x : ℝ} (h : a+1 ≤ b) (hx : x ∈ Icc b (b+1)) :
    taper a b x = b+1-x := by
  rw [taper,min_eq_right (show b+1-x ≤ 1 by linarith [hx.1]),
    min_eq_right (show b+1-x ≤ x-a by linarith [hx.1]),max_eq_right (sub_nonneg.mpr hx.2)]

theorem taper_nat (a b k : ℕ) :
    taper a b k = if k ∈ Finset.Ioc a b then 1 else 0 := by
  split_ifs with h
  · have hx := Finset.mem_Ioc.mp h
    apply taper_flat
    constructor
    · exact_mod_cast hx.1
    · exact_mod_cast hx.2
  · by_cases hk : k ≤ a
    · exact taper_left (by exact_mod_cast hk)
    · apply taper_right
      have hb : b+1 ≤ k := by simp only [Finset.mem_Ioc] at h; omega
      exact_mod_cast hb

theorem continuous_taper (a b : ℝ) : Continuous (taper a b) := by unfold taper; fun_prop

theorem phase_deriv (β x : ℝ) : HasDerivAt (phase β) (phase β x*((β:ℂ)*I)) x := by
  have d := ((((hasDerivAt_id (x:ℂ)).const_mul (β:ℂ)).mul_const I).cexp).comp_ofReal
  change HasDerivAt (fun y : ℝ => Complex.exp (((β*y:ℝ):ℂ)*I)) _ x
  simpa [phase,mul_assoc] using d

theorem continuous_phase (β : ℝ) : Continuous (phase β) :=
  continuous_iff_continuousAt.mpr fun x => (phase_deriv β x).continuousAt

@[simp] theorem norm_phase (β x : ℝ) : ‖phase β x‖ = 1 := by simp [phase,Complex.norm_exp]

theorem continuous_test (a b β : ℝ) : Continuous (test a b β) :=
  (continuous_ofReal.comp (continuous_taper a b)).mul (continuous_phase β)

private theorem test_top (a b β p : ℝ) : test a b β =O[atTop] (fun x : ℝ => x^p) := by
  apply Asymptotics.IsBigO.of_bound (c := 0)
  filter_upwards [eventually_ge_atTop (b+1)] with x hx
  simp [test,taper_right hx]

private theorem test_bot {a : ℝ} (ha : 0 < a) (b β p : ℝ) :
    test a b β =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x^p) := by
  apply Asymptotics.IsBigO.of_bound (c := 0)
  filter_upwards [(eventually_lt_nhds ha).filter_mono (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))] with x hx
  simp [test,taper_left hx.le]

theorem analytic_transform {a : ℝ} (ha : 0 < a) (b β : ℝ) :
    Differentiable ℂ (transform a b β) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow (a := s.re+1) (b := s.re-1)
    ((continuous_test a b β).locallyIntegrable.locallyIntegrableOn _)
    (test_top ..) (by linarith) (test_bot ha ..) (by linarith)

/-- The integral against the trapezoid is a difference of unit averages of
any primitive. This identity is used for both stationary and nonstationary phases. -/
theorem window_primitive {a b : ℝ} (hab : a+1 ≤ b) (f P : ℝ → ℂ)
    (hc : ContinuousOn f (Icc a (b+1))) (hd : ∀ x ∈ Icc a (b+1), HasDerivAt P (f x) x) :
    (∫ x in a..b+1, (taper a b x:ℂ)*f x) =
      (∫ x in b..b+1, P x) - ∫ x in a..a+1, P x := by
  have ab : a ≤ b := by linarith
  have a1 : a ≤ a+1 := by linarith
  have b1 : b ≤ b+1 := by linarith
  have hP : ContinuousOn P (Icc a (b+1)) := fun x hx =>
    (hd x hx).continuousAt.continuousWithinAt
  have iW {l r : ℝ} (hl : a ≤ l) (hr : r ≤ b+1) (hlr : l ≤ r) :
      IntervalIntegrable (fun x => (taper a b x:ℂ)*f x) volume l r :=
    ((continuous_ofReal.comp (continuous_taper a b)).continuousOn.mul
      (hc.mono (Icc_subset_Icc hl hr))).intervalIntegrable_of_Icc hlr
  have ip {l r : ℝ} (hl : a ≤ l) (hr : r ≤ b+1) (hlr : l ≤ r)
      (u : ℝ → ℂ) (v : ℂ) (hu : ∀ x, HasDerivAt u v x) :
      (∫ x in l..r, u x*f x) = u r*P r-u l*P l-(∫ x in l..r, v*P x) := by
    apply intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    · exact (continuous_iff_continuousAt.mpr fun x => (hu x).continuousAt).continuousOn
    · rw [uIcc_of_le hlr]
      exact hP.mono (Icc_subset_Icc hl hr)
    · exact fun x _ => hu x
    · intro x hx
      rw [min_eq_left hlr,max_eq_right hlr] at hx
      exact hd x ⟨hl.trans hx.1.le,hx.2.le.trans hr⟩
    · exact intervalIntegrable_const
    · exact (hc.mono (Icc_subset_Icc hl hr)).intervalIntegrable_of_Icc hlr
  have rise : (∫ x in a..a+1, (taper a b x:ℂ)*f x) = P (a+1) - ∫ x in a..a+1, P x := by
    let u := fun x : ℝ => (x:ℂ)-a
    have hu (x : ℝ) : HasDerivAt u 1 x := by
      simpa [u] using ((hasDerivAt_id (x:ℂ)).sub_const (a:ℂ)).comp_ofReal
    rw [intervalIntegral.integral_congr (g := fun x => u x*f x) (fun x hx => by
      rw [uIcc_of_le a1] at hx
      simp only [u,taper_rise hab hx,ofReal_sub]),ip le_rfl (by linarith) a1 u 1 hu]
    simp [u]
  have mid : (∫ x in a+1..b, (taper a b x:ℂ)*f x) = P b-P (a+1) := by
    rw [intervalIntegral.integral_congr (g := fun x => f x) (fun x hx => by
      rw [uIcc_of_le hab] at hx
      simp [taper_flat hx])]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hd x ((Icc_subset_Icc a1 b1) ((uIcc_of_le hab) ▸ hx)))
      ((hc.mono (Icc_subset_Icc a1 b1)).intervalIntegrable_of_Icc hab)
  have fall : (∫ x in b..b+1, (taper a b x:ℂ)*f x) = -P b + ∫ x in b..b+1, P x := by
    let u := fun x : ℝ => (b:ℂ)+1-x
    have hu (x : ℝ) : HasDerivAt u (-1) x := by
      simpa [u] using ((hasDerivAt_id (x:ℂ)).const_sub ((b:ℂ)+1)).comp_ofReal
    rw [intervalIntegral.integral_congr (g := fun x => u x*f x) (fun x hx => by
      rw [uIcc_of_le b1] at hx
      simp only [u,taper_fall hab hx,ofReal_sub,ofReal_add,ofReal_one]),ip ab le_rfl b1 u (-1) hu]
    simp [u,intervalIntegral.integral_neg]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (iW le_rfl b1 ab) (iW ab le_rfl b1),
    ← intervalIntegral.integral_add_adjacent_intervals (iW le_rfl (by linarith) a1) (iW a1 b1 hab),
    rise,mid,fall]
  abel

def density (β : ℝ) (s : ℂ) (x : ℝ) : ℂ := phase β x*(x:ℂ)^(s-1)

theorem continuousAt_density (β : ℝ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (density β s) x :=
  (continuous_phase β).continuousAt.mul
    (differentiableAt_id.ofReal_cpow_const (s-1) hx.ne').continuousAt

theorem integral_density {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (β : ℝ) (s : ℂ) :
    IntervalIntegrable (density β s) volume a b :=
  (show ContinuousOn (density β s) (Icc a b) from fun _ hx =>
    (continuousAt_density β s (ha.trans_le hx.1)).continuousWithinAt).intervalIntegrable_of_Icc hab

theorem transform_eq_taper_integral {a b : ℝ} (ha : 0 < a) (hab : a+1 ≤ b) (β : ℝ) (s : ℂ) :
    transform a b β s = ∫ x in a..b+1, (taper a b x:ℂ)*density β s x := by
  rw [transform,mellin,intervalIntegral.integral_of_le (show a ≤ b+1 by linarith)]
  simp only [smul_eq_mul]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioc a (b+1)) (t := Ioi (0:ℝ)) measurableSet_Ioi
    (fun x hx => ha.trans hx.1) (fun x hx => by
      rcases le_or_gt x a with hl | hl
      · simp [test,taper_left hl]
      · have hr : b+1 ≤ x := le_of_not_ge fun h => hx.2 ⟨hl,h⟩
        simp [test,taper_right hr])]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  unfold test density
  ring

/-- The integer-exact trapezoid is the average of translated sharp intervals.
The identity keeps the oscillatory phase, not just its absolute value. -/
theorem transform_eq_average {a b : ℝ} (ha : 0 < a) (hab : a+1 ≤ b) (β : ℝ) (s : ℂ) :
    transform a b β s = ∫ u in (0:ℝ)..1, ∫ x in (a+u)..(b+u), density β s x := by
  let f := density β s
  let P (v : ℝ) := ∫ x in a..v, f x
  have ab : a ≤ b := by linarith
  have hd (x : ℝ) (hx : x ∈ Icc a (b+1)) : HasDerivAt P (f x) x := by
    apply intervalIntegral.integral_hasDerivAt_right (integral_density ha hx.1 β s)
    · exact ContinuousAt.stronglyMeasurableAtFilter (s := Ioi (0:ℝ)) isOpen_Ioi
        (fun y hy => continuousAt_density β s hy) x (ha.trans_le hx.1)
    · exact continuousAt_density β s (ha.trans_le hx.1)
  have hc : ContinuousOn f (Icc a (b+1)) := fun x hx =>
    (continuousAt_density β s (ha.trans_le hx.1)).continuousWithinAt
  have pc : ContinuousOn P (Icc a (b+1)) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have shift (l : ℝ) (hl : a ≤ l) (hl' : l ≤ b) :
      IntervalIntegrable (fun u => P (l+u)) volume 0 1 := by
    have hmap : MapsTo (fun u : ℝ => l+u) (Icc 0 1) (Icc a (b+1)) :=
      fun u hu => ⟨by linarith [hu.1],by linarith [hu.2]⟩
    exact (pc.comp (continuous_const.add continuous_id).continuousOn hmap).intervalIntegrable_of_Icc zero_le_one
  rw [transform_eq_taper_integral ha hab,window_primitive hab f P hc hd]
  have he : (∫ u in (0:ℝ)..1, ∫ x in (a+u)..(b+u), f x) =
      ∫ u in (0:ℝ)..1, (P (b+u)-P (a+u)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    exact eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
      (integral_density ha (by linarith [hu.1]: a ≤ a+u) β s)
      (integral_density (by linarith [hu.1] : 0 < a+u) (by linarith : a+u ≤ b+u) β s))
  change _ = ∫ u in (0:ℝ)..1, ∫ x in (a+u)..(b+u), f x
  rw [he,intervalIntegral.integral_sub (shift b ab le_rfl) (shift a le_rfl ab),
    intervalIntegral.integral_comp_add_left,intervalIntegral.integral_comp_add_left]
  simp

theorem density_eq {x : ℝ} (hx : 0 < x) (β : ℝ) (s : ℂ) :
    density β s x = ((x^(s.re-1):ℝ):ℂ)*
      Complex.exp (((β*x+s.im*Real.log x:ℝ):ℂ)*I) := by
  rw [density,phase,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le,Real.rpow_def_of_pos hx,Complex.ofReal_exp,
    ← Complex.exp_add,← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp
  ring

/-- Any uniform bound for sharp subinterval integrals bounds the transform
of the exact integer window with the same constant. -/
theorem norm_transform_le {X a b D : ℝ} (hX : 0 < X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (β : ℝ) (s : ℂ)
    (hd : ∀ l r : ℝ, X ≤ l → l ≤ r → r ≤ 2*X → ‖∫ x in l..r, density β s x‖ ≤ D) :
    ‖transform a b β s‖ ≤ D := by
  rw [transform_eq_average (hX.trans_le ha) hab]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := D)
    (f := fun u : ℝ => ∫ x in (a+u)..(b+u), density β s x) (fun u hu => by
      rw [uIoc_of_le zero_le_one] at hu
      exact hd _ _ (by linarith [hu.1]) (by linarith) (by linarith [hu.2]))
  simpa using h

theorem norm_window_modes {X a b : ℝ} (hX : 0 < X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (β : ℝ) (s : ℂ) (hσ : 0 ≤ s.re) (hσ' : s.re ≤ 1) :
    ‖transform a b β s‖ ≤ X^s.re ∧
      (s.im ≠ 0 → ‖transform a b β s‖ ≤ X^s.re*((3+5*Real.pi)/Real.sqrt |s.im|)) ∧
      (0 < |s.im| → 4*|β| * X ≤ |s.im| →
        ‖transform a b β s‖ ≤ 20*X^s.re/|s.im|) := by
  have bounds (l r : ℝ) (hl : X ≤ l) (hlr : l ≤ r) (hr : r ≤ 2*X) :
      let K := ∫ x in l..r, density β s x
      ‖K‖ ≤ X^s.re ∧ (s.im ≠ 0 → ‖K‖ ≤ X^s.re*((3+5*Real.pi)/Real.sqrt |s.im|)) ∧
        ∀ H : ℝ, 0 < H → (∀ x ∈ Icc l r, H ≤ |β*x+s.im|) → ‖K‖ ≤ 5*r^s.re/H := by
    have he := intervalIntegral.integral_congr (μ := volume) (f := density β s)
      (a := l) (b := r) (fun x hx => density_eq ((hX.trans_le hl).trans_le (((uIcc_of_le hlr) ▸ hx).1)) β s)
    dsimp only
    rw [he]
    exact GoldbachOscillation.per_ordinate X l r s.re s.im β hX hl hlr hr hσ hσ'
  refine ⟨norm_transform_le hX ha hab hb β s (fun l r hl hm hr => (bounds l r hl hm hr).1),?_,?_⟩
  · intro ht
    exact norm_transform_le hX ha hab hb β s (fun l r hl hm hr => (bounds l r hl hm hr).2.1 ht)
  · intro ht hcut
    apply norm_transform_le hX ha hab hb β s
    intro l r hl hlr hr
    have hsep (x : ℝ) (hx : x ∈ Icc l r) : |s.im|/2 ≤ |β*x+s.im| := by
      have h := abs_add_le (β*x+s.im) (-(β*x))
      rw [show β*x+s.im+ -(β*x) = s.im by ring,abs_neg,abs_mul,abs_of_nonneg (hX.le.trans (hl.trans hx.1))] at h
      have hj := mul_le_mul_of_nonneg_left (hx.2.trans hr) (abs_nonneg β)
      linarith only [h,hcut,hj]
    have hpow : r^s.re ≤ 2*X^s.re := calc
      _ ≤ (2*X)^s.re := Real.rpow_le_rpow (hX.le.trans (hl.trans hlr)) hr hσ
      _ = (2:ℝ)^s.re * X^s.re := Real.mul_rpow (by norm_num) hX.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        simpa using Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) hσ')
        (Real.rpow_nonneg hX.le _)
    apply ((bounds l r hl hlr hr).2.2 _ (half_pos ht) hsep).trans
    rw [div_div_eq_mul_div]
    exact (div_le_div_iff_of_pos_right ht).mpr (by linarith only [hpow])

end GoldbachTwistedMellin
end
end

section
open Set MeasureTheory Complex
open scoped Interval

noncomputable section
namespace GoldbachTwistedMellin

private def freq (β : ℝ) : ℂ := (β:ℂ)*I
private theorem norm_freq (β : ℝ) : ‖freq β‖ = |β| := by simp [freq,Real.norm_eq_abs]

theorem density_succ (β : ℝ) (s : ℂ) (x : ℝ) :
    density β (s+1) x = phase β x*(x:ℂ)^s := by simp [density]

private theorem pow_deriv {s : ℂ} (hs : 0 < s.re) (β : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (density β (s+1)) (s*density β s x+freq β*density β (s+1) x) x := by
  have sn : s ≠ 0 := fun h => by simp [h] at hs
  have he := (phase_deriv β x).mul (hasDerivAt_ofReal_cpow_const hx.ne' sn)
  rw [show density β (s+1) = fun y : ℝ => phase β y*(y:ℂ)^s from funext (density_succ β s)]
  convert he using 1
  unfold density freq
  ring

private theorem pow_ibp {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    s*(∫ x in l..r, density β s x) = density β (s+1) r - density β (s+1) l -
      freq β*(∫ x in l..r, density β (s+1) x) := by
  have hder := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := density β (s+1)) (a := l) (b := r)
    (fun x hx => pow_deriv hs β (hl.trans_le (((uIcc_of_le hlr) ▸ hx).1)))
    (((integral_density hl hlr β s).const_mul s).add ((integral_density hl hlr β (s+1)).const_mul (freq β)))
  rw [intervalIntegral.integral_add ((integral_density hl hlr β s).const_mul s)
    ((integral_density hl hlr β (s+1)).const_mul (freq β)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hder
  exact eq_sub_of_add_eq hder

/-- Integration by parts for the whole piecewise linear window. The first
derivative contains two unit end intervals and the derivative of the twist. -/
theorem transform_recurrence {a b : ℝ} (ha : 0 < a) (hab : a+1 ≤ b) (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    s*transform a b β s = (∫ x in b..b+1, density β (s+1) x) -
      (∫ x in a..a+1, density β (s+1) x) - freq β*transform a b β (s+1) := by
  have hL : a ≤ b+1 := by linarith
  have cont (z : ℂ) : ContinuousOn (density β z) (Icc a (b+1)) :=
    fun x hx => (continuousAt_density β z (ha.trans_le hx.1)).continuousWithinAt
  have wcont (z : ℂ) : ContinuousOn (fun x => (taper a b x:ℂ)*density β z x) (Icc a (b+1)) :=
    (continuous_ofReal.comp (continuous_taper a b)).continuousOn.mul (cont z)
  have wp := window_primitive hab
    (fun x => s*density β s x+freq β*density β (s+1) x) (density β (s+1))
    (((cont s).const_mul _).add ((cont (s+1)).const_mul _))
    (fun x hx => pow_deriv hs β (ha.trans_le hx.1))
  have point (x : ℝ) : (taper a b x:ℂ)*(s*density β s x+freq β*density β (s+1) x) =
      s*((taper a b x:ℂ)*density β s x)+freq β*((taper a b x:ℂ)*density β (s+1) x) := by ring
  simp_rw [point] at wp
  rw [intervalIntegral.integral_add (((wcont s).intervalIntegrable_of_Icc hL).const_mul s)
    (((wcont (s+1)).intervalIntegrable_of_Icc hL).const_mul (freq β)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    ← transform_eq_taper_integral ha hab,← transform_eq_taper_integral ha hab] at wp
  exact eq_sub_of_add_eq wp

/-- The derivative of the smooth phase is bounded for |β|≤1. One integration
by parts gives a common first-order bound for the integrals in the recurrence. -/
private theorem endpoint_bound {X l r β : ℝ} (hX : 1 ≤ X) (hl : X ≤ l) (hlr : l ≤ r)
    (hr : r ≤ 2*X) (hβ : |β| ≤ 1) {s : ℂ} (hs : 0 < s.re) (hs' : s.re ≤ 2)
    (hn : 0 < ‖s+1‖) :
    ‖∫ x in l..r, density β (s+1) x‖ ≤ 32*X^4/‖s+1‖ := by
  have xl : 0 < l := zero_lt_one.trans_le (hX.trans hl)
  have bnd (x : ℝ) (hx : x ∈ Icc l r) : ‖density β ((s+1)+1) x‖ ≤ (2*X)^3 := by
    rw [density_succ,norm_mul,norm_phase,one_mul,norm_cpow_eq_rpow_re_of_pos (xl.trans_le hx.1)]
    rw [add_re,one_re]
    calc
      x^(s.re+1) ≤ (2*X)^(s.re+1) :=
        Real.rpow_le_rpow (xl.le.trans hx.1) (hx.2.trans hr) (by linarith)
      _ ≤ (2*X)^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = _ := by norm_num
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := l) (b := r)
    (fun x hx => bnd x (by rw [uIoc_of_le hlr] at hx; exact ⟨hx.1.le,hx.2⟩))
  rw [abs_of_nonneg (sub_nonneg.mpr hlr)] at hb
  have e := pow_ibp xl hlr β (s := s+1) (by simp only [add_re,one_re]; linarith)
  have he := (norm_sub_le .. : ‖(density β ((s+1)+1) r - density β ((s+1)+1) l) -
      freq β*(∫ x in l..r, density β ((s+1)+1) x)‖ ≤ _)
  rw [← e,norm_mul,norm_mul,norm_freq] at he
  apply (le_div_iff₀ hn).mpr
  rw [mul_comm]
  have coeff := mul_le_of_le_one_left (norm_nonneg (∫ x in l..r, density β ((s+1)+1) x)) hβ
  have len : r-l ≤ 2*X := by linarith
  have hlen := mul_le_mul_of_nonneg_left len (by positivity : 0 ≤ (2*X)^3)
  have x3 : X^3 ≤ X^4 := by
    simpa only [pow_succ] using (le_mul_of_one_le_right (by positivity : 0 ≤ X^3) hX)
  linarith only [he,norm_sub_le (density β ((s+1)+1) r) (density β ((s+1)+1) l),
    bnd r (right_mem_Icc.mpr hlr),bnd l (left_mem_Icc.mpr hlr),coeff,hb,hlen,x3]

/-- Uniform quadratic decay throughout the contour strip, including the
unit-width transition regions. This bound is only used beyond polynomial height. -/
theorem norm_transform_tail {X a b β : ℝ} (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (hβ : |β| ≤ 1) (s : ℂ) (hs : 0 < s.re) (hs' : s.re ≤ 2)
    (ht : 0 < |s.im|) : ‖transform a b β s‖ ≤ 96*X^4/|s.im|^2 := by
  have lt0 : 0 < X := zero_lt_one.trans_le hX
  have t1 : |s.im| ≤ ‖s+1‖ := by simpa using abs_im_le_norm (s+1)
  have t0 := abs_im_le_norm s
  have ext (l r : ℝ) (hl : X ≤ l) (hlr : l ≤ r) (hr : r ≤ 2*X) :=
    endpoint_bound hX hl hlr hr hβ hs hs' (ht.trans_le t1)
  have hB := ext b (b+1) (by linarith) (by linarith) hb
  have hA := ext a (a+1) ha (by linarith) (by linarith)
  have hG := norm_transform_le lt0 ha hab hb β (s+1) ext
  have he := transform_recurrence (lt0.trans_le ha) hab β hs
  have triangle := norm_sub_le ((∫ x in b..b+1, density β (s+1) x)-(∫ x in a..a+1, density β (s+1) x))
    (freq β*transform a b β (s+1))
  rw [← he,norm_mul,norm_mul,norm_freq] at triangle
  have part := norm_sub_le (∫ x in b..b+1, density β (s+1) x) (∫ x in a..a+1, density β (s+1) x)
  have coeff := mul_le_of_le_one_left (norm_nonneg (transform a b β (s+1))) hβ
  have total : ‖s‖ * ‖transform a b β s‖ ≤ 96*X^4/‖s+1‖ := by
    simp only [div_eq_mul_inv] at hA hB hG ⊢
    linarith only [triangle,part,coeff,hA,hB,hG]
  have htprod := (le_div_iff₀ (ht.trans_le t1)).mp total
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  calc
    _ = |s.im| * ‖transform a b β s‖*|s.im| := by ring
    _ ≤ _ := (mul_le_mul (mul_le_mul_of_nonneg_right t0 (norm_nonneg _)) t1 ht.le (by positivity)).trans htprod

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex
open scoped Topology Interval

noncomputable section
namespace GoldbachTwistedMellin

theorem integrable_transform {X a b β σ : ℝ} (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (hβ : |β| ≤ 1) (hs : 0 < σ) (hs' : σ ≤ 2) :
    Integrable (fun t : ℝ => transform a b β ((σ:ℂ)+(t:ℂ)*I)) := by
  let g := fun t : ℝ => transform a b β ((σ:ℂ)+(t:ℂ)*I)
  have hc : Continuous g := (analytic_transform (zero_lt_one.trans_le (hX.trans ha)) b β).continuous.comp
    (continuous_const.add (continuous_ofReal.mul continuous_const))
  obtain ⟨M,hM⟩ := (isCompact_Icc (α := ℝ) (a := -1) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  let C := 2*(max 0 M+96*X^4)
  refine (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable ?_
  filter_upwards with t
  change ‖g t‖ ≤ C*(1+t^2)⁻¹
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  by_cases ht : |t| ≤ 1
  · have h := hM t (abs_le.mp ht)
    have ht2 : t^2 ≤ 1 := by
      have hprod := mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ 1+|t| by positivity)
      nlinarith only [hprod,sq_abs t]
    have hm : ‖g t‖*(1+t^2) ≤ (max 0 M)*2 :=
      mul_le_mul (h.trans (le_max_right ..)) (by linarith) (by positivity) (le_max_left ..)
    dsimp [C]
    nlinarith only [hm,show 0 ≤ X^4 by positivity]
  · have ht' : 0 < |t| := by linarith only [lt_of_not_ge ht]
    have hbound := norm_transform_tail hX ha hab hb hβ ((σ:ℂ)+(t:ℂ)*I)
      (by simpa using hs) (by simpa using hs') (by simpa using ht')
    have hn : ‖g t‖*|t|^2 ≤ 96*X^4 := (le_div_iff₀ (by positivity)).mp (by simpa [g] using hbound)
    have hsq : 1 ≤ |t|^2 := by nlinarith only [lt_of_not_ge ht,sq_nonneg (|t|-1)]
    have hmul := mul_le_mul_of_nonneg_left (by nlinarith only [hsq,sq_abs t] : 1+t^2 ≤ 2*|t|^2) (norm_nonneg (g t))
    dsimp [C]
    nlinarith only [hmul,hn,le_max_left 0 M]

theorem mellinInv_transform {X a b β σ y : ℝ} (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (hβ : |β| ≤ 1) (hs : 0 < σ) (hs' : σ ≤ 2) (hy : 0 < y) :
    mellinInv σ (transform a b β) y = test a b β y := by
  have ha0 := zero_lt_one.trans_le (hX.trans ha)
  have hm : MellinConvergent (test a b β) (σ:ℂ) := by
    apply mellinConvergent_of_isBigO_rpow (a := σ+1) (b := σ-1)
      ((continuous_test a b β).locallyIntegrable.locallyIntegrableOn _)
    · apply Asymptotics.IsBigO.of_bound (c := 0)
      filter_upwards [eventually_ge_atTop (b+1)] with x hx
      simp [test,taper_right hx]
    · simp
    · apply Asymptotics.IsBigO.of_bound (c := 0)
      filter_upwards [(eventually_lt_nhds ha0).filter_mono (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))] with x hx
      simp [test,taper_left hx.le]
    · simp
  exact mellinInv_mellin_eq σ _ hy hm (integrable_transform hX ha hab hb hβ hs hs') (continuous_test a b β).continuousAt

-- The Dirichlet-series interchange follows the smoothing proof of PR #2486.


/-- Mellin inversion with an absolutely convergent Dirichlet series. -/
theorem series_transform_inversion (a : ℕ → ℂ) (ha0 : a 0 = 0) (f : ℝ → ℂ) (K : ℂ → ℂ) {σ : ℝ}
    (hK : Integrable (fun t : ℝ => K ((σ:ℂ)+(t:ℂ)*I)))
    (hInvK : ∀ y : ℝ, 0 < y → mellinInv σ K y = f y)
    (hAbs : Summable fun n => ‖LSeries.term a (σ : ℂ) n‖) :
    (∑' n, a n * f n) =
      (1 / (2 * Real.pi)) • (∫ t : ℝ,
        LSeries a ((σ : ℂ) + (t : ℂ) * I) * K ((σ : ℂ) + (t : ℂ) * I)) := by
  let z (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I
  let F (n : ℕ) (t : ℝ) : ℂ := LSeries.term a (z t) n * K (z t)
  have hN (n : ℕ) (t : ℝ) : ‖F n t‖ =
      ‖LSeries.term a (σ : ℂ) n‖ * ‖K (z t)‖ := by
    dsimp only [F]
    rw [norm_mul, term_norm_vertical]
  have hF (n : ℕ) : Integrable (F n) := by
    refine (hK.norm.const_mul ‖LSeries.term a (σ : ℂ) n‖).mono' ?_ ?_
    · exact (term_continuous_vertical a σ n).aestronglyMeasurable.mul hK.aestronglyMeasurable
    · filter_upwards with t
      exact le_of_eq (hN n t)
  have hFsum : Summable fun n => ∫ t : ℝ, ‖F n t‖ := by
    simp_rw [hN, integral_const_mul]
    exact hAbs.mul_right _
  have hInv (n : ℕ) : a n * f n =
      (1 / (2 * Real.pi)) • (∫ t : ℝ, F n t) := by
    by_cases hn : n = 0
    · subst n
      simp [F, ha0]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [← hInvK n hnR]
    unfold mellinInv
    simp only [F, z, LSeries.term_def₀ ha0, ofReal_natCast, smul_eq_mul, mul_assoc]
    rw [integral_const_mul]
    simp only [Algebra.smul_def]
    ring
  calc
    _ = ∑' n, (1 / (2 * Real.pi)) • (∫ t : ℝ, F n t) := tsum_congr hInv
    _ = (1 / (2 * Real.pi)) • (∑' n, ∫ t : ℝ, F n t) := tsum_const_smul'' _
    _ = (1 / (2 * Real.pi)) • (∫ t : ℝ, ∑' n, F n t) :=
      congrArg ((1 / (2 * Real.pi)) • ·) (integral_tsum_of_summable_integral_norm hF hFsum)
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      simp only [F, z, LSeries, tsum_mul_right]


open GoldbachSmoothing DirichletCharacter

theorem character_sum_eq_vertical {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a b : ℕ} {X β : ℝ} (hX : 1 ≤ X) (ha : X ≤ (a:ℝ)) (hab : (a:ℝ)+1 ≤ b)
    (hb : (b:ℝ)+1 ≤ 2*X) (hβ : |β| ≤ 1) :
    (∑ n ∈ Finset.Ioc a b, twistedCoefficient χ n * phase β n) =
      (1/(2*Real.pi)) • ∫ t : ℝ, (-logDeriv (LFunction χ) (2+(t:ℂ)*I)) *
        transform a b β (2+(t:ℂ)*I) := by
  have hAbs : Summable fun n => ‖LSeries.term (twistedCoefficient χ) (2:ℂ) n‖ :=
    summable_norm_iff.mpr (χ.LSeriesSummable_twist_vonMangoldt (by norm_num))
  have hEq (t : ℝ) : LSeries (twistedCoefficient χ) (2+(t:ℂ)*I) =
      -logDeriv (LFunction χ) (2+(t:ℂ)*I) := LSeries_twistedCoefficient_eq χ (by norm_num)
  have h := series_transform_inversion (twistedCoefficient χ) (twistedCoefficient_zero χ)
    (test a b β) (transform a b β) (σ := 2) (integrable_transform hX ha hab hb hβ (by norm_num) le_rfl)
    (fun _ hy => mellinInv_transform hX ha hab hb hβ (by norm_num) le_rfl hy) (by simpa using hAbs)
  simp only [ofReal_ofNat,hEq] at h
  rw [← h, tsum_eq_sum (s := Finset.Ioc a b)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp [test,taper_nat,hn]
  · intro n hn
    simp [test,taper_nat,hn]

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval

noncomputable section
namespace GoldbachTwistedMellin


@[simp] theorem re_line (σ t : ℝ) : (line σ t).re = σ := by simp [line]
@[simp] theorem im_line (σ t : ℝ) : (line σ t).im = t := by simp [line]

theorem continuous_line (σ : ℝ) : Continuous (line σ) :=
  continuous_const.add (continuous_ofReal.mul continuous_const)

theorem left_pole_dist {σ : ℝ} (hs : σ ≤ 3/4) (t : ℝ) : 1/4 ≤ ‖line σ t-1‖ := by
  have h := neg_le_abs (line σ t-1).re
  have h' := abs_re_le_norm (line σ t-1)
  simp only [sub_re,re_line,one_re] at h h'
  linarith

theorem horizontal_pole_dist {t : ℝ} (ht : 1 ≤ |t|) (σ : ℝ) : 1/4 ≤ ‖line σ t-1‖ := by
  have h := abs_im_le_norm (line σ t-1)
  simp only [sub_im,im_line,one_im,sub_zero] at h
  linarith

theorem contour_right (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    contourLog χ (line 2 t) = -logDeriv (LFunction χ) (line 2 t) := by
  have hn : line 2 t ≠ 1 := by intro h; have := congrArg Complex.re h; simp at this
  have hL := LFunction_ne_zero_of_one_le_re χ (Or.inr hn) (by simp)
  rw [contourLog,logDeriv_regularizedL_eq χ hn hL]
  ring

end GoldbachTwistedMellin
end
end


section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter GoldbachSmoothing
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

noncomputable def integrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b β : ℝ) (z : ℂ) : ℂ :=
  contourLog χ z * transform a b β z

/-- Signed, multiplicity-weighted residues of the additively twisted Mellin window. -/
noncomputable def zeroContribution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b β σ T : ℝ) : ℂ :=
  ∑ z ∈ boxZeros χ σ 2 (-T) T, (analyticOrderNatAt (regularizedL χ) z : ℂ) * transform a b β z

noncomputable def contourRemainder {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b β σ T : ℝ) : ℂ :=
  let F := integrand χ a b β
  (1/(2*Real.pi)) • ((∫ t : ℝ in (-T)..T, F (line σ t)) +
    I * ((∫ x : ℝ in σ..2, F (line x (-T))) - ∫ x : ℝ in σ..2, F (line x T)))

noncomputable def truncationRemainder {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b β T : ℝ) : ℂ :=
  let F := integrand χ a b β
  (1/(2*Real.pi)) • ((∫ t : ℝ, F (line 2 t)) - ∫ t : ℝ in (-T)..T, F (line 2 t))

theorem exact_twisted_box {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a b : ℕ} {X β σ T : ℝ} (hX : 1 ≤ X) (ha : X ≤ (a:ℝ)) (hab : (a:ℝ)+1 ≤ b)
    (hb : (b:ℝ)+1 ≤ 2*X) (hβ : |β| ≤ 1) (hs : σ < 1) (hT : 0 < T)
    (hinterior : ∀ z ∈ boxZeros χ σ 2 (-T) T, σ < z.re ∧ z.re < 2 ∧ -T < z.im ∧ z.im < T) :
    (∑ n ∈ Finset.Ioc a b, twistedCoefficient χ n * phase β n) =
      principalFlag χ * transform a b β 1 - zeroContribution χ a b β σ T +
        contourRemainder χ a b β σ T + truncationRemainder χ a b β T := by
  let K := transform a b β
  let S := boxZeros χ σ 2 (-T) T
  let F := integrand χ a b β
  let c : ℝ := 1/(2*Real.pi)
  have hK := analytic_transform (zero_lt_one.trans_le (hX.trans ha)) (b:ℝ) β
  have hr := rectBoundaryIntegral_neg_logDeriv_add_pole_mul (regularizedL χ) K S (principalFlag χ)
    hs (by norm_num : (1:ℝ) < 2) (neg_lt_zero.mpr hT) hT
    ((analytic_regularizedL χ).mono (subset_univ _)) (fun z _ => hK.analyticAt z)
    (fun z hz => by simp only [S,mem_boxZeros,and_iff_right hz]) hinterior
    (fun z _ => regularizedL_analyticOrder_ne_top χ z) (regularizedL_ne_zero_at_one χ)
  have vertical := right_vertical_integral_of_rect hr
  change (∫ y : ℝ in (-T)..T, F (line 2 y)) =
    (∫ y : ℝ in (-T)..T, F (line σ y)) +
      (2*(Real.pi:ℂ))*(principalFlag χ * K 1-zeroContribution χ a b β σ T) +
      I*((∫ x : ℝ in σ..2, F (line x (-T))) - ∫ x : ℝ in σ..2, F (line x T)) at vertical
  have inv := character_sum_eq_vertical χ hX ha hab hb hβ
  have rline (t : ℝ) : -logDeriv (LFunction χ) (2+(t:ℂ)*I) = contourLog χ (line 2 t) := by
    simpa [line] using (contour_right q χ t).symm
  simp_rw [rline] at inv
  change _ = c • ∫ t : ℝ, F (line 2 t) at inv
  have cancel (z : ℂ) : c • ((2*(Real.pi:ℂ))*z) = z := by
    rw [Complex.real_smul]
    simp [c,Complex.ofReal_mul,Real.pi_ne_zero,mul_assoc]
  have scaled := congrArg (fun z : ℂ => c • z) vertical
  simp only [smul_add,cancel] at scaled
  rw [inv]
  change _ = _ + c • (_ + _) + c • (_ - _)
  rw [smul_add,smul_sub,scaled]
  abel

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter GoldbachSmoothing
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- A single absolute convergent series bounds the logarithmic derivatives on
the right edge, for all characters and all imaginary heights. -/
theorem uniform_right_log_bound : ∃ A : ℝ, 0 < A ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ), ‖contourLog χ (line 2 t)‖ ≤ A := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hsum : Summable fun n => ‖LSeries.term f (2:ℂ) n‖ :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num))
  let M := ∑' n, ‖LSeries.term f (2:ℂ) n‖
  have hM : 0 ≤ M := tsum_nonneg fun n => norm_nonneg _
  refine ⟨M+1,by positivity,?_⟩
  intro q _ χ t
  rw [contour_right, ← LSeries_twistedCoefficient_eq χ (by simp)]
  have h (n : ℕ) : ‖LSeries.term (twistedCoefficient χ) (line 2 t) n‖ ≤ ‖LSeries.term f (2:ℂ) n‖ := by
    have hs : ‖LSeries.term f (line 2 t) n‖ = ‖LSeries.term f (2:ℂ) n‖ := by simp [LSeries.norm_term_eq]
    rw [← hs]
    apply LSeries.norm_term_le
    change ‖χ (n:ZMod q)*(ArithmeticFunction.vonMangoldt n:ℂ)‖ ≤ ‖(ArithmeticFunction.vonMangoldt n:ℂ)‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have ht := hsum.of_nonneg_of_le (fun _ => norm_nonneg _) h
  exact ((norm_tsum_le_tsum_norm ht).trans (ht.tsum_le_tsum h hsum)).trans (by dsimp [M]; linarith)

/-- Removing both infinite tails of a vertical integral loses at most 2M/T
when the pointwise norm beyond height T is at most M/t². -/
theorem tails_bound {f : ℝ → ℂ} (hi : Integrable f) {T M : ℝ} (hT : 0 < T) (_hM : 0 ≤ M)
    (hb : ∀ t : ℝ, T < |t| → ‖f t‖ ≤ M / t^2) :
    ‖(∫ t : ℝ, f t) - (∫ t : ℝ in (-T)..T, f t)‖ ≤ 2*M/T := by
  have ht : -T ≤ T := by linarith
  have hcut := intervalIntegral.integral_Iic_add_Ioi (b := T) (μ := volume) hi.integrableOn hi.integrableOn
  have hsplit : (∫ t in Iic T, f t) =
      (∫ t in Iic (-T), f t) + ∫ t in Ioc (-T) T, f t := by
    rw [← setIntegral_union (Iic_disjoint_Ioc (le_refl (-T))) measurableSet_Ioc hi.integrableOn hi.integrableOn,
      Iic_union_Ioc_eq_Iic ht]
  have htail (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi T)) (hg' : ∀ t ∈ Ioi T, ‖g t‖ ≤ M/t^2) :
      ‖∫ t in Ioi T, g t‖ ≤ M/T := by
    have hr (t : ℝ) (h : t ∈ Ioi T) : t^(-2:ℝ) = (t^2)⁻¹ := by
      rw [Real.rpow_neg (hT.trans h).le,Real.rpow_two]
    have hm := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hT).const_mul M
    calc
      ‖∫ t in Ioi T, g t‖ ≤ ∫ t in Ioi T, ‖g t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioi T, M*t^(-2:ℝ) := by
        apply setIntegral_mono_on hg.norm hm measurableSet_Ioi
        intro t ht'
        simpa only [hr t ht',div_eq_mul_inv] using hg' t ht'
      _ = M/T := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hT]
        norm_num [Real.rpow_neg hT.le,div_eq_mul_inv]
  have hpos := htail f hi.integrableOn (fun t ht' => hb t (by rwa [abs_of_pos (hT.trans ht')]))
  have hneg := htail (fun t => f (-t)) hi.comp_neg.integrableOn (fun t ht' => by
    simpa only [neg_sq] using hb (-t) (by rwa [abs_neg,abs_of_pos (hT.trans ht')]))
  rw [integral_comp_neg_Ioi] at hneg
  rw [← hcut, hsplit, intervalIntegral.integral_of_le ht]
  have cancel (l m r : ℂ) : l+m+r-m = l+r := by abel
  rw [cancel]
  exact (norm_add_le _ _).trans ((add_le_add hneg hpos).trans_eq (by ring))

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter GoldbachSmoothing
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem truncation_bound : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b : ℕ) (X β T : ℝ), 1 ≤ X → X ≤ (a:ℝ) → (a:ℝ)+1 ≤ b → (b:ℝ)+1 ≤ 2*X →
      |β| ≤ 1 → 0 < T → ‖truncationRemainder χ a b β T‖ ≤ C*X^4/T := by
  obtain ⟨A,hA,logbound⟩ := uniform_right_log_bound
  let c : ℝ := 1/(2*Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c*(2*A*96),by positivity,?_⟩
  intro q _ χ a b X β T hX ha hab hb hβ hT
  let F := integrand χ a b β
  have hr (t : ℝ) : LSeries (twistedCoefficient χ) (line 2 t) = contourLog χ (line 2 t) := by
    rw [contour_right]
    exact LSeries_twistedCoefficient_eq χ (by simp)
  have hAbs : Summable fun n => ‖LSeries.term (twistedCoefficient χ) (2:ℂ) n‖ :=
    summable_norm_iff.mpr (χ.LSeriesSummable_twist_vonMangoldt (by norm_num))
  have hi : Integrable fun t : ℝ => F (line 2 t) := by
    dsimp [F,integrand]
    simp_rw [← hr]
    exact integrable_series_transform (twistedCoefficient χ) (transform a b β) (σ := 2)
      (integrable_transform hX ha hab hb hβ (by norm_num) le_rfl) (by simpa using hAbs)
  have hbnd (t : ℝ) (ht : T < |t|) : ‖F (line 2 t)‖ ≤ (A*96*X^4)/t^2 := by
    have h := norm_transform_tail hX ha hab hb hβ (line 2 t) (by simp) (by simp) (by simpa using hT.trans ht)
    rw [im_line, sq_abs] at h
    change ‖contourLog χ (line 2 t) * _‖ ≤ _
    rw [norm_mul]
    exact (mul_le_mul (logbound q χ t) h (norm_nonneg _) hA.le).trans_eq (by ring)
  have ht := tails_bound hi hT (by positivity : 0 ≤ A*96*X^4) hbnd
  change ‖c • _‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  exact (mul_le_mul_of_nonneg_left ht hc.le).trans_eq (by ring)

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter MeromorphicOn Metric
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- Every zero to the right of the critical line whose ordinate differs from t
by at most one lies in the same Jensen disk. -/
theorem mem_right_jensen_disk {z : ℂ} {t : ℝ}
    (hl : 1/2 ≤ z.re) (hr : z.re ≤ 2) (hi : |z.im-t| ≤ 1) :
    z ∈ closedBall (⟨2,t⟩:ℂ) (29/16) := by
  rw [mem_closedBall,dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 29/16)).mp
  have hrabs : |z.re-2| ≤ 3/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have h1 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 3/2)).mpr hrabs
  have h2 := (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hi
  rw [sq_abs] at h1 h2
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re,Complex.sub_im]
  nlinarith only [h1,h2]

/-- The unit-height bound counts multiplicities throughout the right half of
the critical strip. It requires no hypothesis on the real part of other zeros. -/
theorem unconditional_right_slice_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) (Z : Finset ℂ),
      (∀ z ∈ Z, 1/2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im-t| ≤ 1) →
      (∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z:ℝ)) ≤ C*logHeight q t := by
  classical
  obtain ⟨C,hC,jensen⟩ := jensen_diskDivisor_bound (A:=25) (b:=1/4) (by norm_num) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro q _ χ t Z hZ
  let U := closedBall (⟨2,t⟩:ℂ) (29/16)
  let D := divisor (regularizedL χ) U
  have hfin := D.finiteSupport (isCompact_closedBall _ _)
  let W := Z ∪ hfin.toFinset
  have hsup : Function.support D ⊆ (W:Set ℂ) := fun _ hz => Finset.mem_union_right _ (hfin.mem_toFinset.mpr hz)
  have hbound := jensen q (regularizedL χ) t (NeZero.pos q)
    ((analytic_regularizedL χ).mono (subset_univ _))
    (fun s hs => by
      have hg := GoldbachGrhGrowth.norm_regularizedLFunction_le χ hs
      by_cases hχ : χ = 1
      · simpa only [regularizedL,hχ,ite_true] using hg
      · simpa only [regularizedL,hχ,ite_false] using hg) (norm_regularizedL_anchor χ t)
  have hmul (z : ℂ) (hz : z ∈ Z) : (analyticOrderNatAt (regularizedL χ) z : ℤ) = D z :=
    (regularizedL_divisor_apply χ (mem_right_jensen_disk (hZ z hz).1 (hZ z hz).2.1 (hZ z hz).2.2)).symm
  have hD : ∀ z, 0 ≤ D z := ((analytic_regularizedL χ).mono (subset_univ U)).divisor_nonneg
  have hsum : (∑ z ∈ Z,(analyticOrderNatAt (regularizedL χ) z:ℤ)) ≤ ∑ᶠ z, D z := by
    rw [finsum_eq_sum_of_support_subset _ hsup,Finset.sum_congr rfl hmul]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun z _ _ => hD z)
  exact (show (∑ z ∈ Z,(analyticOrderNatAt (regularizedL χ) z:ℝ)) ≤ ((∑ᶠ z, D z : ℤ):ℝ) by exact_mod_cast hsum).trans hbound

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- The number of distinct right-hand zeros in a horizontal band is at most
the Jensen bound for their total multiplicity. -/
theorem right_box_card :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      ((boxZeros χ (1/2) 2 (t-1) (t+1)).card:ℝ) ≤ C*logHeight q t := by
  obtain ⟨C,hC,count⟩ := unconditional_right_slice_count
  refine ⟨C,hC,?_⟩
  intro q _ χ t
  let Z := boxZeros χ (1/2) 2 (t-1) (t+1)
  have hz (z : ℂ) (h : z ∈ Z) := (mem_boxZeros χ _ _ _ _ z).mp h
  have bounds (z : ℂ) (h : z ∈ Z) : 1/2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im-t| ≤ 1 := by
    have b := mem_reProdIm.mp (hz z h).1
    exact ⟨b.1.1,b.1.2,abs_le.mpr ⟨by linarith [b.2.1],by linarith [b.2.2]⟩⟩
  have one (z : ℂ) (h : z ∈ Z) : (1:ℝ) ≤ analyticOrderNatAt (regularizedL χ) z := by
    exact_mod_cast (regularizedL_analyticOrderNatAt_pos_iff χ z).mpr (hz z h).2
  exact (show (Z.card:ℝ) ≤ ∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z:ℝ) by
    simpa using Finset.sum_le_sum one).trans (count q χ t Z bounds)

/-- A height in each unit interval avoids the ordinates of zeros near both the
upper and lower edge. The width of the forbidden neighborhoods is inverse
logarithmic in the modulus and height. -/
theorem good_symmetric_height :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ), 2 ≤ B →
      ∃ T ∈ Icc B (B+1), ∀ z : ℂ, 1/2 ≤ z.re → regularizedL χ z = 0 →
        (C*logHeight q (B+1/2))⁻¹ ≤ abs (T - |z.im|) := by
  obtain ⟨C,hC,count⟩ := right_box_card
  refine ⟨4*(1+2*C),by positivity,?_⟩
  intro q _ χ B hB
  let t := B+1/2
  let P := boxZeros χ (1/2) 2 (t-1) (t+1)
  let N := boxZeros χ (1/2) 2 (-t-1) (-t+1)
  let S := P ∪ N
  let L := logHeight q t
  have hL : 1 ≤ L := logHeight_ge_one q t
  have hLn : logHeight q (-t) = L := by simp [L,logHeight]
  have hs : (S.card:ℝ) ≤ 2*C*L := by
    have hp := count q χ t
    have hn := count q χ (-t)
    rw [hLn] at hn
    have hu : (S.card:ℝ) ≤ (P.card:ℝ)+(N.card:ℝ) := by exact_mod_cast Finset.card_union_le P N
    dsimp only [P,N] at hu
    linarith [hp,hn]
  obtain ⟨v,hv,sep⟩ := exists_goodHeight S (fun z => 2*|z.im|) (2*B+1/2)
  let T := v/2
  have hT : B+1/4 ≤ T ∧ T ≤ B+3/4 := by dsimp [T]; constructor <;> linarith [hv.1,hv.2]
  let g := (4*(1+2*C)*L)⁻¹
  have hden : 4*(1+(S.card:ℝ)) ≤ 4*(1+2*C)*L := by linarith only [hs,hL]
  have hg : g ≤ 1/(4*(1+(S.card:ℝ))) := by
    rw [one_div];exact inv_anti₀ (by positivity) hden
  have hg' : g ≤ 1/4 := hg.trans ((one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4) (by linarith [Nat.cast_nonneg (α:=ℝ) S.card] : (4:ℝ) ≤ 4*(1+(S.card:ℝ)))))
  refine ⟨T,⟨by linarith [hT.1],by linarith [hT.2]⟩,?_⟩
  intro z hz hzero
  change g ≤ _
  by_contra! hclose
  have hnear := abs_lt.mp (hclose.trans_le hg')
  have hr : z.re ≤ 2 := by by_contra! h; exact regularizedL_ne_zero_right χ (by linarith) hzero
  have hzS : z ∈ S := by
    by_cases hi : 0 ≤ z.im
    · rw [abs_of_nonneg hi] at hnear
      apply Finset.mem_union_left
      apply (mem_boxZeros χ _ _ _ _ z).mpr
      exact ⟨mem_reProdIm.mpr ⟨⟨hz,hr⟩,⟨by dsimp [t];linarith [hT.1,hnear.2],by dsimp [t];linarith [hT.2,hnear.1]⟩⟩,hzero⟩
    · rw [abs_of_neg (lt_of_not_ge hi)] at hnear
      apply Finset.mem_union_right
      apply (mem_boxZeros χ _ _ _ _ z).mpr
      exact ⟨mem_reProdIm.mpr ⟨⟨hz,hr⟩,⟨by dsimp [t];linarith [hT.2,hnear.1],by dsimp [t];linarith [hT.1,hnear.2]⟩⟩,hzero⟩
  have hsep := sep z hzS
  rw [show v-2*|z.im|=2*(T-|z.im|) by dsimp [T];ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hsep
  have heq : 1/(2*(1+(S.card:ℝ))) = 2*(1/(4*(1+(S.card:ℝ)))) := by field_simp; ring
  linarith only [heq,hsep,hg,hclose]

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem logHeight_mono_abs (q : ℕ) [NeZero q] {s t : ℝ} (h : |s| ≤ |t|) :
    logHeight q s ≤ logHeight q t := by
  have hq : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  apply Real.log_le_log (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- A uniform logarithmic-derivative bound holds on both horizontal edges. The
height can depend on the character; every point of each edge is covered. -/
theorem unconditional_horizontal_log {d : ℝ} (hd : 0 < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ), 2 ≤ B →
      ∃ T ∈ Icc B (B+1), (∀ z : ℂ, 1/2 ≤ z.re → regularizedL χ z = 0 → |z.im| ≠ T) ∧
        ∀ σ t : ℝ, 1/2+d ≤ σ → σ ≤ 2 → |t| = T →
        ‖contourLog χ (line σ t)‖ ≤ A*(logHeight q (B+1))^2 := by
  obtain ⟨C,hC,good⟩ := good_symmetric_height
  obtain ⟨K,hK,bound⟩ := uniform_dirichlet_log_control
  refine ⟨K*(1+d⁻¹+C)+4,by positivity,?_⟩
  intro q _ χ B hB
  obtain ⟨T,hT,avoid⟩ := good q χ B hB
  let L := logHeight q (B+1)
  have hL : 1 ≤ L := logHeight_ge_one q _
  have hc := logHeight_ge_one q (B+1/2)
  have hmid : logHeight q (B+1/2) ≤ L := by
    apply logHeight_mono_abs
    rw [abs_of_nonneg (by linarith : 0 ≤ B+1/2),abs_of_nonneg (by linarith : 0 ≤ B+1)]
    linarith
  let r := min d (C*logHeight q (B+1/2))⁻¹
  have hr : 0 < r := lt_min hd (by positivity)
  have hr' : r⁻¹ ≤ d⁻¹+C*L := by
    dsimp [r]
    rcases le_total d (C*logHeight q (B+1/2))⁻¹ with h|h
    · rw [min_eq_left h]; nlinarith only [hC,hL,mul_pos hC (by linarith : 0 < L)]
    · rw [min_eq_right h,inv_inv]; linarith only [mul_le_mul_of_nonneg_left hmid hC.le,inv_pos.mpr hd]
  refine ⟨T,hT,?_,?_⟩
  · intro z hz hz0 heq
    have gap := avoid z hz hz0
    rw [heq,sub_self,abs_zero] at gap
    exact (not_le_of_gt (by positivity)) gap
  intro σ t hσ hσ' ht
  have hdist (z : ℂ) (_hz : 0 < z.re) (hz0 : regularizedL χ z = 0) : r ≤ ‖line σ t - z‖ := by
    by_cases hz : 1/2 ≤ z.re
    · have h := avoid z hz hz0
      have h' := abs_norm_sub_norm_le t z.im
      simp only [Real.norm_eq_abs,ht] at h'
      exact ((min_le_right ..).trans (h.trans h')).trans (by simpa using abs_im_le_norm (line σ t-z))
    · exact (min_le_left ..).trans ((show d ≤ (line σ t-z).re by simp only [sub_re,re_line];linarith).trans (re_le_norm _))
  have raw := bound q χ σ t r ⟨by linarith,hσ'⟩ hr hdist
  have htlog : logHeight q t ≤ L := by apply logHeight_mono_abs;rw [ht,abs_of_nonneg (by linarith : 0≤B+1)];exact hT.2
  have hsep := horizontal_pole_dist (by rw [ht];linarith [hT.1] : 1 ≤ |t|) σ
  have hflag : ‖principalFlag χ‖ ≤ 1 := by by_cases h : χ = 1 <;> simp [principalFlag,h]
  have hpole : ‖principalFlag χ/(line σ t-1)‖ ≤ 4 := by
    rw [norm_div];apply (div_le_iff₀ (by linarith : 0 < ‖line σ t-1‖)).mpr;linarith
  rw [mul_right_comm K] at raw
  change ‖logDeriv (regularizedL χ) (line σ t)‖ ≤ K*(1+r⁻¹)*logHeight q t at raw
  have hfactor : 1+r⁻¹ ≤ (1+d⁻¹+C)*L := by
    nlinarith only [hr',hL,mul_le_mul_of_nonneg_left hL (inv_pos.mpr hd).le]
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hfactor hK.le) htlog
    (by linarith [logHeight_ge_one q t]) (by positivity)
  have hsq : 1 ≤ L^2 := one_le_pow₀ hL
  calc
    ‖contourLog χ (line σ t)‖ ≤ ‖logDeriv (regularizedL χ) (line σ t)‖ + ‖principalFlag χ/(line σ t-1)‖ := by
      simpa only [contourLog,norm_neg] using norm_add_le (-logDeriv (regularizedL χ) (line σ t)) (principalFlag χ/(line σ t-1))
    _ ≤ (K*(1+d⁻¹+C)+4)*L^2 := by nlinarith only [raw.trans hm,hpole,hsq]

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter GoldbachSmoothing
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- Along either horizontal side the window decays quadratically in height.
The loss from the logarithmic derivative is at most quadratic in log height. -/
theorem horizontal_edge_bound {d σ T B A X β : ℝ} {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a b : ℕ} (hX : 1 ≤ X) (ha : X ≤ (a:ℝ)) (hab : (a:ℝ)+1 ≤ b)
    (hb : (b:ℝ)+1 ≤ 2*X) (hβ : |β| ≤ 1) (hd : 0 < d)
    (hs : 1/2+d ≤ σ) (hs' : σ < 1) (hT : 0 < T) (hA : 0 ≤ A)
    (hlog : ∀ x t : ℝ, 1/2+d ≤ x → x ≤ 2 → |t| = T →
      ‖contourLog χ (line x t)‖ ≤ A*(logHeight q (B+1))^2) {t : ℝ} (ht : |t| = T) :
    ‖∫ x : ℝ in σ..2, integrand χ a b β (line x t)‖ ≤
      (2*A*96)*X^4*(logHeight q (B+1))^2/T^2 := by
  let L := logHeight q (B+1)
  have hpos : 0 < σ := by linarith
  have pt (x : ℝ) (hx : x ∈ Ι σ 2) : ‖integrand χ a b β (line x t)‖ ≤ (A*L^2)*(96*X^4/T^2) := by
    rw [uIoc_of_le (by linarith)] at hx
    have hw := norm_transform_tail hX ha hab hb hβ (line x t) (by simp;linarith [hx.1])
      (by simpa using hx.2) (by simpa [ht] using hT)
    rw [im_line,ht] at hw
    rw [integrand,norm_mul]
    exact mul_le_mul (hlog x t (hs.trans hx.1.le) hx.2 ht) hw (norm_nonneg _) (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const pt
  have hlen : |2-σ| ≤ 2 := by rw [abs_of_nonneg (by linarith)];linarith
  exact hi.trans ((mul_le_mul_of_nonneg_left hlen (by positivity)).trans_eq (by dsimp [L];ring))


end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex
open scoped Topology Interval

noncomputable section
namespace GoldbachTwistedMellin

def heightCut (X : ℝ) : ℝ := (2*X)^8
def logBudget (q : ℕ) (X : ℝ) : ℝ := 1+Goldbach.logHeight q (heightCut X)

theorem heightCut_ge {X : ℝ} (hX : 1 ≤ X) : 1+4*X ≤ heightCut X := by
  have hpow : X ≤ X^8 := by simpa using pow_le_pow_right₀ hX (show 1 ≤ 8 by decide)
  dsimp [heightCut]
  rw [mul_pow]
  norm_num
  linarith


end GoldbachTwistedMellin
end
end

section
open Set MeasureTheory
open scoped Interval Topology
noncomputable section
namespace GoldbachTwistedMellin

def rootKernel (x : ℝ) := |x|^(-(1/2):ℝ)

theorem rootKernel_nonneg (x : ℝ) : 0 ≤ rootKernel x := Real.rpow_nonneg (abs_nonneg _) _

theorem integrable_rootKernel (a b r : ℝ) : IntervalIntegrable (fun x => rootKernel (x-r)) volume a b := by
  have hpow (u v : ℝ) : IntervalIntegrable (fun x : ℝ => x^(-(1/2):ℝ)) volume u v :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hpos : IntervalIntegrable (fun x : ℝ => (x-r)^(-(1/2):ℝ)) volume a b :=
    by simpa using (hpow (a-r) (b-r)).comp_sub_right r
  have hneg : IntervalIntegrable (fun x : ℝ => (r-x)^(-(1/2):ℝ)) volume a b :=
    by simpa using (hpow (r-a) (r-b)).comp_sub_left r
  rw [intervalIntegrable_iff] at hpos hneg ⊢
  have h := Integrable.piecewise (μ:=volume.restrict (Ι a b)) (s:=Iio r) measurableSet_Iio.nullMeasurableSet
    (Integrable.integrableOn hneg) (Integrable.integrableOn hpos)
  apply h.congr
  filter_upwards with x
  by_cases hx : x < r
  · simp [Set.piecewise,hx,rootKernel,abs_of_neg (sub_neg.mpr hx),neg_sub]
  · simp [Set.piecewise,hx,rootKernel,abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hx))]

theorem integral_rootKernel_right {a b r : ℝ} (ha : r ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, rootKernel (x-r)) = 2*(Real.sqrt (b-r)-Real.sqrt (a-r)) := by
  have h : (∫ x in a..b, rootKernel (x-r)) = ∫ x in a..b, (x-r)^(-(1/2):ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    simp [rootKernel,abs_of_nonneg (sub_nonneg.mpr (ha.trans hx.1))]
  rw [h,intervalIntegral.integral_comp_sub_right (fun x : ℝ => x^(-(1/2):ℝ)) r,
    integral_rpow (Or.inl (by norm_num))]
  norm_num [← Real.sqrt_eq_rpow]
  ring

theorem integral_rootKernel_left {a b r : ℝ} (hb : b ≤ r) (hab : a ≤ b) :
    (∫ x in a..b, rootKernel (x-r)) = 2*(Real.sqrt (r-a)-Real.sqrt (r-b)) := by
  have h : (∫ x in a..b, rootKernel (x-r)) = ∫ x in a..b, (r-x)^(-(1/2):ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    simp [rootKernel,abs_of_nonpos (sub_nonpos.mpr (hx.2.trans hb)),neg_sub]
  rw [h,intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^(-(1/2):ℝ)) r,
    integral_rpow (Or.inl (by norm_num))]
  norm_num [← Real.sqrt_eq_rpow]
  ring

theorem integral_rootKernel_le {a b : ℝ} (hab : a ≤ b) (r : ℝ) :
    (∫ x in a..b, rootKernel (x-r)) ≤ 4*Real.sqrt (b-a) := by
  have diffBound (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      Real.sqrt (x+y)-Real.sqrt x ≤ Real.sqrt y := by
    apply sub_le_iff_le_add.mpr
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    nlinarith only [Real.sq_sqrt (add_nonneg hx hy),Real.sq_sqrt hx,Real.sq_sqrt hy,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  rcases le_total r a with h|h
  · rw [integral_rootKernel_right h hab]
    have he : b-r = a-r+(b-a) := by ring
    rw [he]
    linarith [diffBound (a-r) (b-a) (by linarith) (by linarith),Real.sqrt_nonneg (b-a)]
  rcases le_total b r with h'|h'
  · rw [integral_rootKernel_left h' hab]
    have he : r-a = r-b+(b-a) := by ring
    rw [he]
    linarith [diffBound (r-b) (b-a) (by linarith) (by linarith),Real.sqrt_nonneg (b-a)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (integrable_rootKernel a r r) (integrable_rootKernel r b r),
    integral_rootKernel_left (le_refl r) h,integral_rootKernel_right (le_refl r) h',sub_self,Real.sqrt_zero]
  linarith [Real.sqrt_le_sqrt (by linarith : r-a ≤ b-a),Real.sqrt_le_sqrt (by linarith : b-r ≤ b-a)]

end GoldbachTwistedMellin
end
end

section
open Set MeasureTheory
open scoped Interval Topology
noncomputable section
namespace GoldbachTwistedMellin

/-- A vertical side avoiding any prescribed finite set can be chosen with
controlled total square-root singularity at all real coordinates. -/
theorem exists_weighted_rootKernel_bound {ι : Type*} (S : Finset ι) (w y : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (bad : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Ioo a b, x ∉ bad ∧
      (∑ i ∈ S, w i*rootKernel (x-y i)) ≤ (4/Real.sqrt (b-a))*(∑ i ∈ S,w i) := by
  classical
  let I := Ioc a b
  let μ := volume.restrict I
  have len : 0 < b-a := sub_pos.mpr hab
  have hreal : μ.real univ = b-a := by
    simp [μ,I,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal len.le]
  have hn : μ ≠ 0 := by
    intro h
    have hp : 0 < μ.real univ := hreal.symm ▸ len
    simp [h] at hp
  let : IsFiniteMeasure μ := ⟨by simp [μ,I,Real.volume_Ioc]⟩
  let g := fun x : ℝ => ∑ i ∈ S, w i*rootKernel (x-y i)
  have int (i : ι) : Integrable (fun x => w i*rootKernel (x-y i)) μ :=
    ((integrable_rootKernel a b (y i)).1.const_mul (w i))
  have hi : Integrable g μ := integrable_finsetSum S (fun i _ => int i)
  have avg : (⨍ x, g x ∂μ) ≤ (4/Real.sqrt (b-a))*(∑ i ∈ S,w i) := by
    rw [average_eq,hreal,smul_eq_mul]
    have hi' : (∫ x, g x ∂μ) ≤ 4*Real.sqrt (b-a)*(∑ i ∈ S,w i) := by
      unfold g
      rw [integral_finsetSum S (fun i _ => int i),Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      rw [integral_const_mul]
      have hbound := integral_rootKernel_le hab.le (y i)
      rw [intervalIntegral.integral_of_le hab.le] at hbound
      exact (mul_le_mul_of_nonneg_left hbound (hw i hi)).trans_eq (by ring)
    apply (mul_le_mul_of_nonneg_left hi' (inv_nonneg.mpr len.le)).trans_eq
    have hs := Real.sq_sqrt len.le
    have hp := Real.sqrt_pos.mpr len
    field_simp
    rw [hs]
  let N : Set ℝ := Iᶜ ∪ (↑(insert b bad) : Set ℝ)
  have hN : μ N = 0 := by
    apply measure_union_null
    · simp [μ,I,Measure.restrict_apply,measurableSet_Ioc.compl]
    · exact (insert b bad).measure_zero μ
  obtain ⟨x,hx,hgx⟩ := exists_notMem_null_le_average hn hi hN
  have h' : x ∈ I := by by_contra hh;exact hx (Or.inl hh)
  have hbad : x ∉ insert b bad := fun h => hx (Or.inr h)
  exact ⟨x,⟨h'.1,lt_of_le_of_ne h'.2 (fun h => hbad (Finset.mem_insert.mpr (.inl h)))⟩,
    fun h => hbad (Finset.mem_insert.mpr (.inr h)),hgx.trans avg⟩

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem inv_distance_le_root_product (s z : ℂ) (hx : s.re ≠ z.re) (hy : s.im ≠ z.im) :
    ‖s-z‖⁻¹ ≤ rootKernel (s.re-z.re)*rootKernel (s.im-z.im) := by
  let x := |s.re-z.re|
  let y := |s.im-z.im|
  have hxp : 0 < x := abs_pos.mpr (sub_ne_zero.mpr hx)
  have hyp : 0 < y := abs_pos.mpr (sub_ne_zero.mpr hy)
  have h1 : x ≤ ‖s-z‖ := abs_re_le_norm _
  have h2 : y ≤ ‖s-z‖ := abs_im_le_norm _
  have hsq : Real.sqrt x*Real.sqrt y ≤ ‖s-z‖ := by
    rw [← Real.sqrt_mul hxp.le]
    exact (Real.sqrt_le_iff).mpr ⟨norm_nonneg _,by simpa only [pow_two] using mul_le_mul h1 h2 hyp.le (norm_nonneg _)⟩
  change _ ≤ x^(-(1/2):ℝ)*y^(-(1/2):ℝ)
  rw [Real.rpow_neg hxp.le,Real.rpow_neg hyp.le,←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow,← mul_inv]
  exact inv_anti₀ (mul_pos (Real.sqrt_pos.mpr hxp) (Real.sqrt_pos.mpr hyp)) hsq

/-- Only zeros within one vertical unit and to the right of one half may
contribute a singular term. A product of two locally integrable kernels
majorizes each such term at almost every height. -/
noncomputable def localZeroPotential (Z : Finset ℂ) (σ t : ℝ) : ℝ :=
  ∑ z ∈ Z, if |t-z.im| ≤ 1 then rootKernel (σ-z.re)*rootKernel (t-z.im) else 0

theorem localPotential_nonneg (Z : Finset ℂ) (σ t : ℝ) : 0 ≤ localZeroPotential Z σ t :=
  Finset.sum_nonneg fun z _ => by split <;> first | exact mul_nonneg (rootKernel_nonneg _) (rootKernel_nonneg _) | exact le_rfl

theorem localPotential_term {Z : Finset ℂ} {z : ℂ} (hz : z ∈ Z) (σ t : ℝ) (h : |t-z.im| ≤ 1) :
    rootKernel (σ-z.re)*rootKernel (t-z.im) ≤ localZeroPotential Z σ t := by
  classical
  let w := fun z : ℂ => if |t-z.im| ≤ 1 then rootKernel (σ-z.re)*rootKernel (t-z.im) else 0
  have hn (z : ℂ) (_ : z ∈ Z) : 0 ≤ w z := by dsimp [w];split <;> first | exact mul_nonneg (rootKernel_nonneg _) (rootKernel_nonneg _) | exact le_rfl
  simpa only [w,localZeroPotential,ite_eq_left h] using Finset.single_le_sum hn hz

theorem log_control_via_potential {d : ℝ} (hd : 0 < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t T : ℝ),
      1/2+d ≤ σ → σ ≤ 3/4 → |t| ≤ T →
      let Z := boxZeros χ (1/2) 2 (-T-1) (T+1)
      (∀ z ∈ Z, σ ≠ z.re) → (∀ z ∈ Z, t ≠ z.im) →
      ‖contourLog χ (line σ t)‖ ≤ A*logHeight q t*(1+localZeroPotential Z σ t) := by
  obtain ⟨C,hC,bound⟩ := uniform_dirichlet_log_control
  refine ⟨C*(2+d⁻¹)+4,by positivity,?_⟩
  intro q _ χ σ t T hs hs' ht Z xr yi
  let P := localZeroPotential Z σ t
  have hP : 0 ≤ P := localPotential_nonneg _ _ _
  let D := 1+d⁻¹+P
  have hD : 0 < D := by dsimp [D];positivity
  have sep (z : ℂ) (_ : 0 < z.re) (hz : regularizedL χ z = 0) : D⁻¹ ≤ ‖line σ t-z‖ := by
    by_cases hreal : z.re < 1/2
    · have hsep : d ≤ ‖line σ t-z‖ := (show d ≤ (line σ t-z).re by simp only [sub_re,re_line];linarith).trans (re_le_norm _)
      exact (show D⁻¹ ≤ d by simpa using inv_anti₀ (inv_pos.mpr hd) (by dsimp [D];linarith : d⁻¹ ≤ D)).trans hsep
    by_cases him : |t-z.im| ≤ 1
    · have hZ : z ∈ Z := by
        apply (mem_boxZeros χ _ _ _ _ z).mpr
        have hright : z.re ≤ 2 := by by_contra! h;exact regularizedL_ne_zero_right χ (by linarith) hz
        have htt := abs_le.mp ht
        have hii := abs_le.mp him
        exact ⟨mem_reProdIm.mpr ⟨⟨le_of_not_gt hreal,hright⟩,⟨by linarith [htt.1,hii.2],by linarith [htt.2,hii.1]⟩⟩,hz⟩
      have hdis := inv_distance_le_root_product (line σ t) z (by simpa using xr z hZ) (by simpa using yi z hZ)
      simp only [re_line,im_line] at hdis
      have hle := hdis.trans (localPotential_term hZ σ t him)
      have hp : 0 < ‖line σ t-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => xr z hZ (by simpa using congrArg Complex.re he)))
      exact (inv_le_comm₀ hD hp).mpr (by dsimp [D];linarith only [hle,inv_pos.mpr hd])
    · have hi : 1 ≤ ‖line σ t-z‖ := (le_of_not_ge him).trans (by simpa using abs_im_le_norm (line σ t-z))
      exact (show D⁻¹ ≤ 1 by simpa using inv_anti₀ zero_lt_one (by dsimp [D];linarith only [hP,inv_pos.mpr hd] : 1 ≤ D)).trans hi
  have raw := bound q χ σ t D⁻¹ ⟨by linarith,by linarith⟩ (inv_pos.mpr hD) sep
  rw [inv_inv] at raw
  have hL := logHeight_ge_one q t
  have hp := left_pole_dist hs' t
  have hf : ‖principalFlag χ‖ ≤ 1 := by by_cases h : χ=1 <;> simp [principalFlag,h]
  have hflag : ‖principalFlag χ/(line σ t-1)‖ ≤ 4 := by
    rw [norm_div];apply (div_le_iff₀ (by linarith : 0<‖line σ t-1‖)).mpr;linarith
  calc
    ‖contourLog χ (line σ t)‖ ≤ ‖logDeriv (regularizedL χ) (line σ t)‖ + ‖principalFlag χ/(line σ t-1)‖ := by
      simpa only [contourLog,norm_neg] using norm_add_le (-logDeriv (regularizedL χ) (line σ t)) (principalFlag χ/(line σ t-1))
    _ ≤ (C*(2+d⁻¹)+4)*logHeight q t*(1+P) := by
      change ‖logDeriv (regularizedL χ) (line σ t)‖ ≤ C*logHeight q t*(1+D) at raw
      have hfac : 1+D ≤ (2+d⁻¹)*(1+P) := by dsimp [D];nlinarith only [hP,mul_nonneg (inv_pos.mpr hd).le hP]
      have hh := mul_le_mul_of_nonneg_left hfac (mul_nonneg hC.le (by linarith : 0≤logHeight q t))
      nlinarith only [raw.trans hh,hflag,hL,mul_nonneg (by linarith : 0≤logHeight q t) hP]

end GoldbachTwistedMellin
end
end

section
open Set MeasureTheory
open scoped Interval Topology
noncomputable section
namespace GoldbachTwistedMellin

theorem exists_cluster_average {ι : Type*} (I : Finset ι) (Z : ι → Finset ℂ) (w : ι → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (bad : Finset ℝ) {a b M : ℝ} (hab : a < b)
    (hM : ∀ i ∈ I, ((Z i).card:ℝ) ≤ M) :
    ∃ σ ∈ Ioo a b, σ ∉ bad ∧
      (∑ i ∈ I, w i*(1+4*∑ z ∈ Z i,rootKernel (σ-z.re))) ≤
        (1+16*M/Real.sqrt (b-a))*(∑ i ∈ I,w i) := by
  classical
  let S := I.sigma Z
  let weight := fun p : Σ _ : ι, ℂ => w p.1
  obtain ⟨x,hx,hbad,avg⟩ := exists_weighted_rootKernel_bound S weight (fun p => p.2.re)
    (fun p hp => hw p.1 (Finset.mem_sigma.mp hp).1) bad hab
  simp only [S,weight,Finset.sum_sigma] at avg
  refine ⟨x,hx,hbad,?_⟩
  have sumWeight : (∑ i ∈ I,∑ _ ∈ Z i,w i) ≤ M*∑ i ∈ I,w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      simpa only [Finset.sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right (hM i hi) (hw i hi)
  have hg := avg.trans (mul_le_mul_of_nonneg_left sumWeight (by positivity))
  have eq : (∑ i ∈ I,w i*(1+4*∑ z ∈ Z i,rootKernel (x-z.re))) =
      (∑ i ∈ I,w i)+4*(∑ i ∈ I,∑ z ∈ Z i,w i*rootKernel (x-z.re)) := by
    simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_add,mul_one]
    simp only [mul_left_comm (w _)]
  rw [eq]
  calc
    _ ≤ (∑ i ∈ I,w i) + 4*((4/Real.sqrt (b-a))*(M*∑ i ∈ I,w i)) := by gcongr
    _ = (1+16*M/Real.sqrt (b-a))*(∑ i ∈ I,w i) := by ring

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem potential_localize {Z S : Finset ℂ} (σ t : ℝ)
    (hs : ∀ z ∈ Z, |t-z.im| ≤ 1 → z ∈ S) :
    localZeroPotential Z σ t ≤ ∑ z ∈ S, rootKernel (σ-z.re)*rootKernel (t-z.im) := by
  classical
  rw [localZeroPotential,← Finset.sum_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => hs z (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2)
    (fun z _ _ => mul_nonneg (rootKernel_nonneg _) (rootKernel_nonneg _))

theorem band_integral_majorant (S : Finset ℂ) (σ l H : ℝ) (hH : 0 ≤ H)
    (f : ℝ → ℝ) (hi : IntervalIntegrable f volume l (l+1))
    (hf : ∀ᵐ t ∂volume.restrict (Icc l (l+1)), f t ≤
      H*(1+∑ z ∈ S,rootKernel (σ-z.re)*rootKernel (t-z.im))) :
    (∫ t in l..l+1, f t) ≤ H*(1+4*∑ z ∈ S,rootKernel (σ-z.re)) := by
  let g (z : ℂ) (t : ℝ) := rootKernel (σ-z.re)*rootKernel (t-z.im)
  have ig (z : ℂ) : IntervalIntegrable (g z) volume l (l+1) :=
    (integrable_rootKernel l (l+1) z.im).const_mul _
  have isum : IntervalIntegrable (fun t => ∑ z ∈ S,g z t) volume l (l+1) :=
    ⟨integrable_finsetSum S (fun z _ => (ig z).1),integrable_finsetSum S (fun z _ => (ig z).2)⟩
  have hb := intervalIntegral.integral_mono_ae_restrict (by linarith : l ≤ l+1) hi
    ((intervalIntegrable_const.add isum).const_mul H) hf
  apply hb.trans
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add intervalIntegrable_const isum,
    intervalIntegral.integral_const,intervalIntegral.integral_finsetSum (fun z _ => ig z),Finset.mul_sum]
  simp only [add_sub_cancel_left,one_smul]
  apply mul_le_mul_of_nonneg_left _ hH
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro z hz
  rw [show (∫ t in l..l+1, g z t) = rootKernel (σ-z.re) * (∫ t in l..l+1,rootKernel (t-z.im)) from
    intervalIntegral.integral_const_mul ..]
  have hk := integral_rootKernel_le (by linarith : l ≤ l+1) z.im
  simp only [add_sub_cancel_left,Real.sqrt_one,mul_one] at hk
  exact (mul_le_mul_of_nonneg_left hk (rootKernel_nonneg _)).trans_eq (mul_comm ..)

theorem integrable_box_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ M : ℝ}
    (hs : 1/2 ≤ σ) (hs' : σ ≤ 3/4) {a b β : ℝ} (ha : 0 < a)
    (avoid : ∀ z ∈ boxZeros χ (1/2) 2 (-M-1) (M+1), σ ≠ z.re) :
    ContinuousOn (fun t : ℝ => integrand χ a b β (line σ t)) (Icc (-M) M) := by
  intro t ht
  let z := line σ t
  have hz : regularizedL χ z ≠ 0 := by
    intro hz
    have hm : z ∈ boxZeros χ (1/2) 2 (-M-1) (M+1) := by
      apply (mem_boxZeros χ _ _ _ _ z).mpr
      exact ⟨mem_reProdIm.mpr ⟨⟨by simpa [z] using hs,by dsimp [z];simp;linarith⟩,⟨by dsimp [z];simp;linarith [ht.1],by dsimp [z];simp;linarith [ht.2]⟩⟩,hz⟩
    exact avoid z hm (by simp [z])
  have hF := analytic_regularizedL χ z (mem_univ _)
  have hlog : AnalyticAt ℂ (logDeriv (regularizedL χ)) z := by
    simpa only [logDeriv,Pi.div_apply] using hF.deriv.div hF hz
  have hz1 : z-1 ≠ 0 := sub_ne_zero.mpr fun h => (by have he := congrArg Complex.re h; simp [z] at he;linarith)
  have hden : AnalyticAt ℂ (fun w : ℂ => w-1) z := analyticAt_id.sub analyticAt_const
  have hflag : AnalyticAt ℂ (fun _ : ℂ => principalFlag χ) z := analyticAt_const
  have hc : AnalyticAt ℂ (contourLog χ) z := hlog.neg.add (hflag.div hden hz1)
  have hi : AnalyticAt ℂ (integrand χ a b β) z := hc.mul ((analytic_transform ha b β).analyticAt z)
  exact (ContinuousAt.comp (f := line σ) (g := integrand χ a b β) (x := t) hi.continuousAt
    (continuous_line σ).continuousAt).continuousWithinAt

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- The three-unit interval contains all zeros within vertical distance one
of a point of the integration interval [l,l+1]. -/
noncomputable def bandZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (l : ℝ) :=
  boxZeros χ (1/2) 2 (l-1) (l+2)

theorem bandZeros_card :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (l M : ℝ),
      |l| ≤ M → ((bandZeros χ l).card:ℝ) ≤ C*logHeight q (M+2) := by
  obtain ⟨C,hC,bound⟩ := right_box_card
  refine ⟨2*C,by positivity,?_⟩
  intro q _ χ l M hm
  let P := boxZeros χ (1/2) 2 (l-1) (l+1)
  let N := boxZeros χ (1/2) 2 ((l+1)-1) ((l+1)+1)
  have hsub : bandZeros χ l ⊆ P ∪ N := by
    intro z hz
    obtain ⟨hb,hz0⟩ := (mem_boxZeros χ _ _ _ _ z).mp hz
    have h := mem_reProdIm.mp hb
    by_cases h' : z.im ≤ l+1
    · exact Finset.mem_union_left _ ((mem_boxZeros χ _ _ _ _ z).mpr ⟨mem_reProdIm.mpr ⟨h.1,h.2.1,h'⟩,hz0⟩)
    · exact Finset.mem_union_right _ ((mem_boxZeros χ _ _ _ _ z).mpr ⟨mem_reProdIm.mpr ⟨h.1,by linarith,by linarith [h.2.2]⟩,hz0⟩)
  have hn : (0:ℝ) ≤ M := (abs_nonneg _).trans hm
  have hp := (bound q χ l).trans (mul_le_mul_of_nonneg_left
    (logHeight_mono_abs q (by rw [abs_of_nonneg (by linarith : 0 ≤ M+2)];linarith : |l| ≤ |M+2|)) hC.le)
  have hh : |l+1| ≤ |M+2| := by
    rw [abs_of_nonneg (by linarith : 0 ≤ M+2)]
    linarith [abs_add_le l 1,abs_one (α:=ℝ)]
  have hN := (bound q χ (l+1)).trans (mul_le_mul_of_nonneg_left (logHeight_mono_abs q hh) hC.le)
  exact (show ((bandZeros χ l).card:ℝ) ≤ (P.card:ℝ)+(N.card:ℝ) by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le P N)).trans ((add_le_add hp hN).trans_eq (by ring))

theorem near_zero_in_band {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (l t M : ℝ)
    (ht : t ∈ Icc l (l+1)) {z : ℂ} (hz : z ∈ boxZeros χ (1/2) 2 (-M-1) (M+1))
    (h : |t-z.im|≤1) : z ∈ bandZeros χ l := by
  obtain ⟨hb,hz0⟩ := (mem_boxZeros χ _ _ _ _ z).mp hz
  have hi := abs_le.mp h
  exact (mem_boxZeros χ _ _ _ _ z).mpr ⟨mem_reProdIm.mpr ⟨(mem_reProdIm.mp hb).1,
    by linarith [ht.1,hi.2],by linarith [ht.2,hi.1]⟩,hz0⟩

end GoldbachTwistedMellin
end
end

section
open Set MeasureTheory Finset
open scoped Interval Topology
noncomputable section
namespace GoldbachTwistedMellin

def grid (M : ℕ) : Finset (Bool × ℕ) := Finset.univ ×ˢ Finset.range M

def gridStart (p : Bool × ℕ) : ℝ := if p.1 then (p.2:ℝ) else -((p.2:ℝ)+1)

theorem grid_geometry {M : ℕ} {p : Bool × ℕ} (hp : p ∈ grid M) :
    |gridStart p| ≤ M ∧ ∀ t ∈ Icc (gridStart p) (gridStart p+1), (p.2:ℝ) ≤ |t| ∧ |t| ≤ M := by
  have hj := Finset.mem_range.mp (Finset.mem_product.mp hp).2
  have hle : (p.2:ℝ)+1 ≤ M := by exact_mod_cast hj
  have hn : (0:ℝ) ≤ p.2 := by positivity
  cases he : p.1 <;> simp only [gridStart,he,Bool.false_eq_true,ite_false,ite_true,abs_neg,
    abs_of_nonneg hn,abs_of_nonneg (by linarith : 0≤(p.2:ℝ)+1)]
  · refine ⟨hle,?_⟩; intro t ht
    rw [abs_of_nonpos (by linarith [ht.2])]
    constructor <;> linarith [ht.1,ht.2]
  · refine ⟨by linarith,?_⟩;intro t ht
    rw [abs_of_nonneg (by linarith [ht.1])]
    exact ⟨ht.1,ht.2.trans hle⟩

theorem sum_grid_weight (M : ℕ) (w : ℕ → ℝ) :
    (∑ p ∈ grid M, w p.2) = 2*∑ j ∈ Finset.range M,w j := by
  simp [grid,Finset.sum_product,two_mul]

theorem sum_grid_integrals {M : ℕ} (f : ℝ → ℝ)
    (hi : ∀ p ∈ grid M, IntervalIntegrable f volume (gridStart p) (gridStart p+1)) :
    (∫ t in -(M:ℝ)..(M:ℝ), f t) = ∑ p ∈ grid M, ∫ t in gridStart p..gridStart p+1, f t := by
  have ip (j : ℕ) (hj : j < M) : IntervalIntegrable f volume (j:ℝ) ((j+1:ℕ):ℝ) := by
    simpa [gridStart,Nat.cast_add] using hi (true,j) (by simp [grid,hj])
  have im (j : ℕ) (hj : j < M) : IntervalIntegrable f volume (-(j:ℝ)) (-((j+1:ℕ):ℝ)) := by
    have h := (hi (false,j) (by simp [grid,hj])).symm
    simpa [gridStart,Nat.cast_add,neg_add_rev] using h
  have hp := intervalIntegral.sum_integral_adjacent_intervals (a:=fun k : ℕ => (k:ℝ)) ip
  have hm := intervalIntegral.sum_integral_adjacent_intervals (a:=fun k : ℕ => -(k:ℝ)) im
  have hip := IntervalIntegrable.trans_iterate ip
  have him := IntervalIntegrable.trans_iterate im
  simp only [Nat.cast_zero,neg_zero] at hp hm hip him
  have hneg := congrArg Neg.neg hm
  rw [← Finset.sum_neg_distrib,←intervalIntegral.integral_symm] at hneg
  simp_rw [← intervalIntegral.integral_symm] at hneg
  rw [← intervalIntegral.integral_add_adjacent_intervals him.symm hip,←hneg,←hp]
  simp [grid,gridStart,Finset.sum_product,Nat.cast_add,neg_add_rev,add_comm]

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Finset
open scoped Topology
noncomputable section
namespace GoldbachTwistedMellin

/-- Average the dyadic window over unit height intervals using the oscillatory
estimates of the earlier zero-integral proof. -/

noncomputable def profile (J j : ℕ) : ℝ :=
  if j = 0 then 1 else if j ≤ J then (3+5*Real.pi)/Real.sqrt j else 20/j

theorem profile_nonneg (J j : ℕ) : 0 ≤ profile J j := by
  unfold profile
  split_ifs <;> positivity

private theorem sqrt_step (j : ℕ) :
    1 / Real.sqrt (j+1:ℝ) ≤ 2*(Real.sqrt (j+1:ℝ)-Real.sqrt j) := by
  have hp : 0 < Real.sqrt (j+1:ℝ) := by positivity
  have hle := Real.sqrt_le_sqrt (show (j:ℝ) ≤ j+1 by linarith)
  have hs1 := Real.sq_sqrt (show 0 ≤ (j+1:ℝ) by positivity)
  have hs0 := Real.sq_sqrt (show 0 ≤ (j:ℝ) by positivity)
  apply (div_le_iff₀ hp).mpr
  nlinarith only [sq_nonneg (Real.sqrt (j+1:ℝ)-Real.sqrt j), hs1, hs0]

theorem profile_sum (J N : ℕ) :
    (∑ j ∈ Finset.range (N+1), profile J j) ≤
      1+2*(3+5*Real.pi)*Real.sqrt J + 20*(1+Real.log (N+1:ℝ)) := by
  have bound (n : ℕ) :
      (∑ j ∈ Finset.range (n+1), profile J j) ≤
        1+2*(3+5*Real.pi)*Real.sqrt (min n J) + 20*(harmonic n:ℝ) := by
    induction n with
    | zero => simp [profile, harmonic]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [show profile J (n+1) = (if n+1 ≤ J then (3+5*Real.pi)/Real.sqrt (n+1:ℝ) else 20/(n+1:ℝ)) by simp [profile]]
      rw [harmonic_succ]
      push_cast
      split_ifs with h
      · rw [min_eq_left (show (n:ℝ)+1 ≤ J by exact_mod_cast h)]
        rw [min_eq_left (show (n:ℝ) ≤ J by exact_mod_cast Nat.le_trans (Nat.le_succ n) h)] at ih
        have hs := mul_le_mul_of_nonneg_left (sqrt_step n) (show 0 ≤ 3+5*Real.pi by positivity)
        have hr : 0 ≤ ((n:ℝ)+1)⁻¹ := by positivity
        simp only [div_eq_mul_inv, one_mul] at hs ⊢
        linarith only [ih,hs,hr]
      · have hn : J ≤ n := by omega
        rw [min_eq_right (show (J:ℝ) ≤ n by exact_mod_cast hn)] at ih
        rw [min_eq_right (show (J:ℝ) ≤ n+1 by exact_mod_cast hn.trans (Nat.le_succ _))]
        simp only [div_eq_mul_inv]
        linarith only [ih]
  have hs := Real.sqrt_le_sqrt (show min (N:ℝ) J ≤ J by exact min_le_right _ _)
  have hs' := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*(3+5*Real.pi) by positivity)
  have hn := harmonic_le_one_add_log (N+1)
  have hh : (harmonic N : ℝ) ≤ harmonic (N+1) := by
    rw [harmonic_succ]
    push_cast
    have h : 0 ≤ ((N:ℝ)+1)⁻¹ := by positivity
    linarith
  push_cast at hn
  linarith only [bound N,hs',hn,hh]

theorem window_bin_bound {X a b β V σ t : ℝ} (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b)
    (hb : b+1 ≤ 2*X) (hs : 0 ≤ σ) (hs' : σ ≤ 1) (hV : σ ≤ V) {j J : ℕ}
    (ht : (j:ℝ) ≤ |t|) (hJ : 4 * |β| * X ≤ (J:ℝ)) :
    ‖transform a b β (line σ t)‖ ≤ X^V * profile J j := by
  obtain ⟨triv,curv,far⟩ := norm_window_modes (zero_lt_one.trans_le hX) ha hab hb β (line σ t)
    (by simpa using hs) (by simpa using hs')
  simp only [re_line,im_line] at triv curv far
  have hpow := Real.rpow_le_rpow_of_exponent_le hX hV
  apply le_trans _ (mul_le_mul_of_nonneg_right hpow (profile_nonneg J j))
  by_cases h0 : j=0
  · simpa [profile,h0] using triv
  have hj : 0 < (j:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
  have htpos := hj.trans_le ht
  by_cases hjJ : j ≤ J
  · rw [profile,ite_eq_right h0,ite_eq_left hjJ]
    apply (curv (abs_pos.mp htpos)).trans
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hj)
      (Real.sqrt_le_sqrt ht)) (Real.rpow_nonneg (by linarith) _)
  · rw [profile,ite_eq_right h0,ite_eq_right hjJ]
    have hfar := far htpos (hJ.trans ((by exact_mod_cast (Nat.le_of_not_ge hjJ) : (J:ℝ) ≤ j).trans ht))
    exact hfar.trans ((div_le_div_of_nonneg_left (by positivity) hj ht).trans_eq (by ring))

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem local_band_norm {d A X a b β V σ M l : ℝ} {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (j J : ℕ) (hd : 0 < d) (hA : 0 ≤ A)
    (hX : 1 ≤ X) (ha : X ≤ a) (hab : a+1 ≤ b) (hb : b+1 ≤ 2*X)
    (hs : 1/2+d ≤ σ) (hs' : σ ≤ 3/4) (hV : σ ≤ V) (hJ : 4 * |β| * X ≤ (J:ℝ))
    (hgrid : ∀ t ∈ Icc l (l+1), (j:ℝ) ≤ |t| ∧ |t| ≤ M)
    (avoid : ∀ z ∈ boxZeros χ (1/2) 2 (-M-1) (M+1), σ ≠ z.re)
    (hlog : ∀ t : ℝ, |t| ≤ M → (∀ z ∈ boxZeros χ (1/2) 2 (-M-1) (M+1), t ≠ z.im) →
      ‖contourLog χ (line σ t)‖ ≤ A*logHeight q t*(1+localZeroPotential (boxZeros χ (1/2) 2 (-M-1) (M+1)) σ t)) :
    (∫ t in l..l+1, ‖integrand χ a b β (line σ t)‖) ≤
      (A*logHeight q (M+2)*X^V)*profile J j *
      (1+4*∑ z ∈ bandZeros χ l,rootKernel (σ-z.re)) := by
  classical
  let Z := boxZeros χ (1/2) 2 (-M-1) (M+1)
  let S := bandZeros χ l
  let G (t : ℝ) := integrand χ a b β (line σ t)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hgrid l ⟨le_rfl,by linarith⟩).2
  have hL := logHeight_ge_one q (M+2)
  have hpow : 0 ≤ X^V := Real.rpow_nonneg (by linarith) _
  have hprof := profile_nonneg J j
  have H : 0 ≤ (A*logHeight q (M+2)*X^V)*profile J j := by positivity
  have hc := integrable_box_line (a:=a) (b:=b) (β:=β) χ (by linarith : 1/2 ≤ σ) hs' (zero_lt_one.trans_le (hX.trans ha)) avoid
  have hcont : ContinuousOn G (Icc l (l+1)) := hc.mono (fun t ht => abs_le.mp (hgrid t ht).2)
  have hi : IntervalIntegrable (fun t => ‖G t‖) volume l (l+1) :=
    hcont.norm.intervalIntegrable_of_Icc (by linarith)
  apply band_integral_majorant S σ l _ H _ hi
  let μ := volume.restrict (Icc l (l+1))
  have hnull : μ (↑(Z.image Complex.im):Set ℝ) = 0 := (Z.image Complex.im).measure_zero μ
  filter_upwards [ae_restrict_mem measurableSet_Icc,measure_eq_zero_iff_ae_notMem.mp hnull] with t ht him
  have yt : ∀ z ∈ Z, t ≠ z.im := fun z hz e => him (Finset.mem_image.mpr ⟨z,hz,e.symm⟩)
  have hh := hlog t (hgrid t ht).2 yt
  have hl : logHeight q t ≤ logHeight q (M+2) := by
    apply logHeight_mono_abs
    rw [abs_of_nonneg (by linarith : 0 ≤ M+2)]
    linarith [(hgrid t ht).2]
  have hloc := potential_localize (Z:=Z) (S:=S) σ t (fun z hz h => near_zero_in_band χ l t M ht hz h)
  have hw := window_bin_bound hX ha hab hb (by linarith : 0 ≤ σ) (by linarith : σ ≤ 1) hV (hgrid t ht).1 hJ
  have hsum := localPotential_nonneg Z σ t
  have h1 := (mul_le_mul (mul_le_mul_of_nonneg_left hl hA) (add_le_add_right hloc 1)
    (by linarith : 0 ≤ 1+localZeroPotential Z σ t) (by positivity)).trans' hh
  change ‖contourLog χ (line σ t)*transform a b β (line σ t)‖ ≤ _
  rw [norm_mul]
  have wn : 0 ≤ ∑ z ∈ S,rootKernel (σ-z.re)*rootKernel (t-z.im) :=
    Finset.sum_nonneg fun z _ => mul_nonneg (rootKernel_nonneg _) (rootKernel_nonneg _)
  exact (mul_le_mul h1 hw (norm_nonneg _) (by positivity)).trans_eq (by ring)

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter Finset
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem averaged_vertical {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/8) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M J : ℕ)
      (a b X β : ℝ), 1 ≤ X → X ≤ a → a+1 ≤ b → b+1 ≤ 2*X → 4 * |β| * X ≤ J →
      ∃ σ ∈ Ioo (1/2+d) (1/2+2*d), (∀ z ∈ boxZeros χ (1/2) 2 (-(M:ℝ)-1) ((M:ℝ)+1), σ ≠ z.re) ∧
        (∫ t : ℝ in -(M:ℝ)..(M:ℝ), ‖integrand χ a b β (line σ t)‖) ≤
          C*X^(1/2+2*d)*(logHeight q ((M:ℝ)+2))^2*
            (1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ))) := by
  classical
  obtain ⟨A,hA,logbound⟩ := log_control_via_potential hd
  obtain ⟨K,hK,cardbound⟩ := bandZeros_card
  let D := Real.sqrt d
  have hD : 0 < D := Real.sqrt_pos.mpr hd
  let C := 2*A*(1+16*K/D)
  have hC : 0 < C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro q _ χ M J a b X β hX ha hab hb hJ
  let u : ℝ := 1/2+d
  let v : ℝ := 1/2+2*d
  let L := logHeight q ((M:ℝ)+2)
  have hL : 1 ≤ L := logHeight_ge_one q _
  let Z := boxZeros χ (1/2) 2 (-(M:ℝ)-1) ((M:ℝ)+1)
  let S := fun p : Bool × ℕ => bandZeros χ (gridStart p)
  let w := fun p : Bool × ℕ => profile J p.2
  have hw (p : Bool × ℕ) (_ : p ∈ grid M) : 0 ≤ w p := profile_nonneg _ _
  have card (p : Bool × ℕ) (hp : p ∈ grid M) : ((S p).card:ℝ) ≤ K*L :=
    cardbound q χ (gridStart p) M (grid_geometry hp).1
  obtain ⟨σ,hσ,bad,avg⟩ := exists_cluster_average (grid M) S w hw (Z.image Complex.re)
    (by dsimp [u,v];linarith : u<v) card
  have hdiff : v-u=d := by dsimp [u,v];ring
  rw [hdiff] at avg
  have avoid (z : ℂ) (hz : z ∈ Z) : σ ≠ z.re := fun he => bad (Finset.mem_image.mpr ⟨z,hz,he.symm⟩)
  refine ⟨σ,hσ,avoid,?_⟩
  let V (t : ℝ) := ‖integrand χ a b β (line σ t)‖
  have hlo : 1/2+d ≤ σ := hσ.1.le
  have hup : σ ≤ 3/4 := by dsimp [v] at hσ;linarith [hσ.2]
  have cont := (integrable_box_line (a:=a) (b:=b) (β:=β) χ (by linarith : 1/2 ≤ σ) hup
    (zero_lt_one.trans_le (hX.trans ha)) avoid).norm
  have int (p : Bool × ℕ) (hp : p ∈ grid M) : IntervalIntegrable V volume (gridStart p) (gridStart p+1) :=
    (cont.mono fun t ht => abs_le.mp ((grid_geometry hp).2 t ht).2).intervalIntegrable_of_Icc (by linarith)
  have hlocal (p : Bool × ℕ) (hp : p ∈ grid M) :
      (∫ t in gridStart p..gridStart p+1,V t) ≤ (A*L*X^v)*
        (w p*(1+4*∑ z ∈ S p,rootKernel (σ-z.re))) := by
    have h := local_band_norm χ p.2 J hd hA.le hX ha hab hb hlo hup hσ.2.le hJ (grid_geometry hp).2
      avoid (fun t ht yt => logbound q χ σ t M hlo hup ht avoid yt)
    exact h.trans_eq (by dsimp [w,L,S];ring)
  have profileBound := profile_sum J M
  have prof : (∑ j ∈ range M,profile J j) ≤ 1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ)) :=
    (sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_succ M)) (fun i _ _ => profile_nonneg _ _)).trans profileBound
  have wsum : (∑ p ∈ grid M,w p) = 2*∑ j ∈ range M,profile J j := sum_grid_weight M (profile J)
  rw [wsum] at avg
  have hn := Finset.sum_nonneg (s:=range M) (fun i _ => profile_nonneg J i)
  have hvX : 0 ≤ X^v := Real.rpow_nonneg (by linarith) _
  have factor : 1+16*(K*L)/Real.sqrt d ≤ (1+16*K/D)*L := by dsimp [D]; simp only [div_eq_mul_inv]; nlinarith only [hL]
  have bound' := avg.trans (mul_le_mul factor (mul_le_mul_of_nonneg_left prof (by norm_num : (0:ℝ)≤2))
    (by positivity) (by positivity))
  change (∫ t in -(M:ℝ)..(M:ℝ), V t) ≤ _
  rw [sum_grid_integrals V int]
  have total := Finset.sum_le_sum hlocal
  rw [←Finset.mul_sum] at total
  exact (total.trans (mul_le_mul_of_nonneg_left bound' (by positivity))).trans_eq (by dsimp [C,v,L];ring)

end GoldbachTwistedMellin
end
end

section
open Set Filter MeasureTheory Complex Goldbach DirichletCharacter GoldbachSmoothing
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

/-- With a suitable contour the signed zero residues account for every term larger
than the square-root window error and the finite-height truncation error. -/
theorem unconditional_zero_model {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/8) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : ℝ)
      (M J a b : ℕ) (X β : ℝ), 2 ≤ B → B+1 ≤ (M:ℝ) →
      1 ≤ X → X ≤ (a:ℝ) → (a:ℝ)+1 ≤ b → (b:ℝ)+1 ≤ 2*X → |β| ≤ 1 → 4*|β| *X ≤ J →
      ∃ T ∈ Icc B (B+1), ∃ σ ∈ Ioo (1/2+d) (1/2+2*d),
        ‖(∑ n ∈ Finset.Ioc a b, twistedCoefficient χ n * phase β n) -
          (principalFlag χ*transform a b β 1 - zeroContribution χ a b β σ T)‖ ≤
        C*(X^(1/2+2*d)*(logHeight q ((M:ℝ)+2))^2*
           (1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ))) +
           X^4*(T⁻¹ + (logHeight q ((M:ℝ)+2))^2/T^2)) := by
  classical
  obtain ⟨A,hA,horiz⟩ := unconditional_horizontal_log hd
  obtain ⟨K,hK,tail⟩ := truncation_bound
  obtain ⟨D,hD,vertical⟩ := averaged_vertical hd hd'
  let c : ℝ := 1/(2*Real.pi)
  have hc : 0 < c := by dsimp [c];positivity
  let C := max (c*D) (max K (c*(2*(2*A*96))))
  have cv : c*D ≤ C := le_max_left ..
  have ct : K ≤ C := (le_max_left ..).trans (le_max_right ..)
  have ch : c*(2*(2*A*96)) ≤ C := (le_max_right ..).trans (le_max_right ..)
  refine ⟨C,hK.trans_le ct,?_⟩
  intro q _ χ B M J a b X β hB hBM hX ha hab hb hβ hJ
  obtain ⟨T,hTB,avoid,hlog⟩ := horiz q χ B hB
  obtain ⟨σ,hσ,avoidR,hV⟩ := vertical q χ M J a b X β hX ha hab hb hJ
  have hT : 0 < T := by linarith [hTB.1]
  have hTM : T ≤ (M:ℝ) := hTB.2.trans hBM
  have hs : σ < 1 := by linarith [hσ.2]
  have inner (z : ℂ) (hz : z ∈ boxZeros χ σ 2 (-T) T) : σ < z.re ∧ z.re < 2 ∧ -T < z.im ∧ z.im < T := by
    obtain ⟨h,z0⟩ := (mem_boxZeros χ _ _ _ _ z).mp hz
    obtain ⟨⟨hr,hr'⟩,hi,hi'⟩ := mem_reProdIm.mp h
    have hzZ : z ∈ boxZeros χ (1/2) 2 (-(M:ℝ)-1) ((M:ℝ)+1) := (mem_boxZeros χ _ _ _ _ z).mpr
      ⟨mem_reProdIm.mpr ⟨⟨by linarith [hσ.1],hr'⟩,by constructor <;> linarith⟩,z0⟩
    have him := avoid z (by linarith [hσ.1]) z0
    refine ⟨lt_of_le_of_ne hr (avoidR z hzZ),lt_of_le_of_ne hr' ?_,lt_of_le_of_ne hi ?_,lt_of_le_of_ne hi' ?_⟩
    · intro e;exact regularizedL_ne_zero_right χ (by rw [e];norm_num) z0
    · intro e;exact him (by rw [←e,abs_neg,abs_of_pos hT])
    · intro e;exact him (by rw [e,abs_of_pos hT])
  refine ⟨T,hTB,σ,hσ,?_⟩
  let F := integrand χ a b β
  let H (t : ℝ) := ∫ x : ℝ in σ..2, F (line x t)
  let V := ∫ t : ℝ in (-T)..T, F (line σ t)
  let R := truncationRemainder χ a b β T
  let L := logHeight q ((M:ℝ)+2)
  let P := 1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ))
  let U := X^(1/2+2*d)*L^2*P
  have logpos : 0 ≤ Real.log (M+1:ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) M])
  have hU : 0 ≤ U := by dsimp [U,P];positivity
  have hcomp : logHeight q (B+1) ≤ L := by
    apply logHeight_mono_abs
    rw [abs_of_nonneg (by linarith : 0≤B+1),abs_of_nonneg (by positivity : 0≤(M:ℝ)+2)]
    linarith
  have hH := @horizontal_edge_bound d σ T B A X β q _ χ a b hX ha hab hb hβ hd hσ.1.le hs hT hA.le hlog
  have ho (t : ℝ) (ht : |t|=T) : ‖H t‖ ≤ (2*A*96)*X^4*L^2/T^2 := by
    apply (hH ht).trans
    gcongr
    exact (zero_le_one.trans (logHeight_ge_one q (B+1)))
  have hlo := ho (-T) (by simp [abs_of_pos hT])
  have hhi := ho T (abs_of_pos hT)
  have hR := tail q χ a b X β T hX ha hab hb hβ hT
  have hi := (integrable_box_line (a:=(a:ℝ)) (b:=(b:ℝ)) (β:=β) χ (by linarith [hσ.1] : 1/2 ≤ σ)
    (by linarith [hσ.2] : σ ≤ 3/4) (zero_lt_one.trans_le (hX.trans ha)) avoidR).norm
  have hsmall : ‖V‖ ≤ ∫ t in (-T)..T, ‖F (line σ t)‖ := by
    dsimp only [V]
    rw [intervalIntegral.integral_of_le (by linarith : -T≤T),intervalIntegral.integral_of_le (by linarith : -T≤T)]
    exact norm_integral_le_integral_norm _
  have hlarge : (∫ t in (-T)..T, ‖F (line σ t)‖) ≤ ∫ t in -(M:ℝ)..(M:ℝ), ‖F (line σ t)‖ := intervalIntegral.integral_mono_interval (neg_le_neg hTM) (by linarith : -T≤T) hTM
    (ae_of_all _ (fun t => norm_nonneg (F (line σ t)))) (hi.intervalIntegrable_of_Icc (by linarith))
  have hvert : c*‖V‖ ≤ C*U := by
    calc
      _ ≤ c*(D*U) := mul_le_mul_of_nonneg_left ((hsmall.trans hlarge).trans (hV.trans_eq (by dsimp [U,P,L];ring))) hc.le
      _ ≤ C*U := by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right cv hU
  have hedge : c*‖H (-T)-H T‖ ≤ C*(X^4*(L^2/T^2)) := by
    calc
      _ ≤ c*(((2*A*96)*X^4*L^2/T^2)+((2*A*96)*X^4*L^2/T^2)) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add hlo hhi)) hc.le
      _ = (c*(2*(2*A*96)))*(X^4*(L^2/T^2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ch (by positivity)
  have htrunc : ‖R‖ ≤ C*(X^4*T⁻¹) := by
    apply hR.trans
    calc
      _ = K*(X^4*T⁻¹) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ct (by positivity)
  rw [exact_twisted_box χ hX ha hab hb hβ hs hT inner]
  unfold contourRemainder
  change ‖_ + c • (V + I*(H (-T) - H T)) + R - _‖ ≤ _
  have cancel (p l r : ℂ) : p+l+r-p=l+r := by abel
  rw [cancel,smul_add]
  apply (norm_add_le _ _).trans
  apply (add_le_add_left (norm_add_le _ _) _).trans
  rw [norm_smul,norm_smul,norm_mul,norm_I,one_mul,Real.norm_eq_abs,abs_of_pos hc]
  exact (add_le_add (add_le_add hvert hedge) htrunc).trans_eq (by dsimp [U,P,L];ring)
end GoldbachTwistedMellin
end
end

section
open Set Complex Goldbach DirichletCharacter GoldbachSmoothing
noncomputable section
namespace GoldbachTwistedMellin

/-- At a polynomial height the two tails are absorbed by the oscillatory window bound. -/
theorem dyadic_zero_model {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/8) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (a b : ℕ) (X β : ℝ), 1 ≤ X → X ≤ (a:ℝ) → (a:ℝ)+1 ≤ b → (b:ℝ)+1 ≤ 2*X → |β| ≤ 1 →
      ∃ T ∈ Icc (heightCut X) (heightCut X+1), ∃ σ ∈ Ioo (1/2+d) (1/2+2*d),
        ‖(∑ n ∈ Finset.Ioc a b, twistedCoefficient χ n * phase β n) -
          (principalFlag χ*transform a b β 1 - zeroContribution χ a b β σ T)‖ ≤
        C*X^(1/2+2*d)*(logBudget q X)^2*
           (1+Real.sqrt (1+4*|β| *X)+Real.log (heightCut X)) := by
  obtain ⟨C,hC,model⟩ := unconditional_zero_model hd hd'
  refine ⟨1000*C,by positivity,?_⟩
  intro q _ χ a b X β hX ha hab hb hβ
  let B := heightCut X
  let M := ⌈B+1⌉₊
  let J := ⌈4*|β| *X⌉₊
  have hB : 2 ≤ B := by dsimp [B];linarith [heightCut_ge hX]
  have hB0 : 0 < B := by linarith
  have hM : B+1 ≤ (M:ℝ) := Nat.le_ceil _
  have hJ : 4*|β| *X ≤ (J:ℝ) := Nat.le_ceil _
  have hM' : (M:ℝ) < B+1+1 := Nat.ceil_lt_add_one (by linarith)
  have hJ' : (J:ℝ) < 4*|β| *X+1 := Nat.ceil_lt_add_one (by positivity)
  obtain ⟨T,hT,σ,hσ,err⟩ := model q χ B M J a b X β hB hM hX ha hab hb hβ hJ
  refine ⟨T,hT,σ,hσ,err.trans ?_⟩
  let L := logBudget q X
  let W := 1+Real.sqrt (1+4*|β| *X)+Real.log B
  let S := X^(1/2+2*d)
  have hS : 1 ≤ S := Real.one_le_rpow hX (by linarith)
  have hL : 1 ≤ L := by dsimp [L,logBudget];linarith [logHeight_ge_one q (heightCut X)]
  have hln := Real.log_nonneg (by linarith : 1≤B)
  have hW : 1 ≤ W := by dsimp [W];linarith [Real.sqrt_nonneg (1+4*|β| *X)]
  have hq : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  have h3 := Real.log_le_sub_one_of_pos (by norm_num : 0<(3:ℝ))
  have hlogM : Real.log (M+1:ℝ) ≤ 2+Real.log B := by
    have h := Real.log_le_log (by positivity : 0 < (M:ℝ)+1) (by linarith : (M:ℝ)+1 ≤ 3*B)
    rw [Real.log_mul (by norm_num) hB0.ne'] at h
    linarith
  have hlogL : logHeight q ((M:ℝ)+2) ≤ 3*L := by
    have h : Real.log (2*(q:ℝ)*(2+((M:ℝ)+2))) ≤ Real.log (3*(2*(q:ℝ)*(2+B))) :=
      Real.log_le_log (by positivity) (by nlinarith only [mul_le_mul_of_nonneg_left (by linarith : 2+((M:ℝ)+2) ≤ 3*(2+B)) (by positivity : 0 ≤ 2*(q:ℝ))])
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0) (by positivity)] at h
    change Real.log (2*(q:ℝ)*(2+|(M:ℝ)+2|)) ≤ 3*(1+Real.log (2*(q:ℝ)*(2+|B|)))
    rw [abs_of_nonneg (by positivity : 0≤(M:ℝ)+2),abs_of_pos hB0]
    have hl := logHeight_ge_one q B
    change 1 ≤ Real.log (2*(q:ℝ)*(2+|B|)) at hl
    rw [abs_of_pos hB0] at hl
    linarith
  have hlsq : (logHeight q ((M:ℝ)+2))^2 ≤ 9*L^2 :=
    (pow_le_pow_left₀ (zero_le_one.trans (logHeight_ge_one q _)) hlogL 2).trans_eq (by ring)
  have hroot : Real.sqrt J ≤ Real.sqrt (1+4*|β| *X) := Real.sqrt_le_sqrt (by linarith)
  have hp : (1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ))) ≤ 100*W := by
    dsimp [W]
    nlinarith only [hlogM,hln,hroot,Real.sqrt_nonneg (1+4*|β| *X),
      mul_le_mul_of_nonneg_right Real.pi_lt_four.le (Real.sqrt_nonneg (J:ℝ))]
  have hp0 : 0 ≤ 1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ)) := by
    have := Real.log_nonneg (show 1≤(M:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) M])
    positivity
  have hvert := mul_le_mul (mul_le_mul_of_nonneg_left hlsq (zero_le_one.trans hS)) hp hp0 (by positivity : 0 ≤ S*(9*L^2))
  have hXT : X^4 ≤ T := by
    have hx := pow_le_pow_right₀ hX (show 4 ≤ 8 by decide)
    have h : X^8 ≤ B := by dsimp [B,heightCut];rw [mul_pow];norm_num;linarith [pow_nonneg (by linarith : 0≤X) 8]
    exact hx.trans (h.trans hT.1)
  have hT1 : 1 ≤ T := by linarith [hT.1]
  have hT0 : 0 < T := by linarith
  have ht₁ : X^4*T⁻¹ ≤ 1 := by rw [←div_eq_mul_inv];exact (div_le_one hT0).mpr hXT
  have ht₂ : X^4/T^2 ≤ 1 := (div_le_one (sq_pos_of_pos hT0)).mpr (hXT.trans (le_self_pow₀ hT1 (by decide)))
  have htail : X^4*(T⁻¹+(logHeight q ((M:ℝ)+2))^2/T^2) ≤ 1+9*L^2 := by
    calc
      _ = X^4*T⁻¹+(X^4/T^2)*(logHeight q ((M:ℝ)+2))^2 := by ring
      _ ≤ 1+1*(9*L^2) := add_le_add ht₁ (mul_le_mul ht₂ hlsq (sq_nonneg _) zero_le_one)
      _ = _ := by ring
  have hL₂ : 1 ≤ L^2 := one_le_pow₀ hL
  have hprod : L^2 ≤ S*L^2*W := (le_mul_of_one_le_left (sq_nonneg L) hS).trans
    (le_mul_of_one_le_right (by positivity) hW)
  have hall : S*(logHeight q ((M:ℝ)+2))^2*(1+2*(3+5*Real.pi)*Real.sqrt J+20*(1+Real.log (M+1:ℝ)))+
      X^4*(T⁻¹+(logHeight q ((M:ℝ)+2))^2/T^2) ≤ 1000*(S*L^2*W) := by
    nlinarith only [hvert,htail,hL₂,hprod]
  exact (mul_le_mul_of_nonneg_left hall hC.le).trans_eq (by dsimp [S,L,W,B];ring)
end GoldbachTwistedMellin
end
end

section
section GoldbachGRHWindowParseval

open scoped BigOperators ComplexConjugate
open Finset

namespace GoldbachGRHWindow

noncomputable section

variable {q : ℕ} [NeZero q]

omit [NeZero q] in

/-- The additive coefficient of the unit-uniform residue distribution. -/
noncomputable def additiveModel (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  (∑ u : (ZMod q)ˣ, ZMod.stdAddChar (a * (u : ZMod q))) / (q.totient : ℂ)


/-- Write the character of two natural residues without reducing either natural number. -/
theorem stdAddChar_nat_pair (a k : ℕ) :
    ZMod.stdAddChar ((a : ZMod q) * (k : ZMod q)) =
      Complex.exp (((2 * Real.pi * ((a : ℝ) * (k : ℝ) / (q : ℝ)) : ℝ) : ℂ) *
        Complex.I) := by
  have h := ZMod.stdAddChar_coe (N := q) (a * k : ℕ)
  push_cast at h
  rw [h]
  congr 1
  push_cast
  ring

/-- Express the unit-model coefficient as the exact reduced numerator sum
    occurring in the major-arc statements. -/
theorem additiveModel_eq_reduced_sum (a : ℕ) :
    additiveModel q (a : ZMod q) =
      (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        Complex.exp (((2 * Real.pi * ((a : ℝ) * (r : ℝ) / (q : ℝ)) : ℝ) : ℂ) *
          Complex.I)) / (q.totient : ℂ) := by
  unfold additiveModel
  congr 1
  apply Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q).val)
  · intro u _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt (u : ZMod q)), ZMod.val_coe_unit_coprime u⟩
  · intro u _ v _ huv
    apply Units.ext
    simpa only [ZMod.natCast_zmod_val] using congrArg (fun x : ℕ => (x : ZMod q)) huv
  · intro r hr
    obtain ⟨hrange, hcop⟩ := Finset.mem_filter.mp hr
    let hrunit : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).mpr hcop
    exact ⟨hrunit.unit, Finset.mem_univ _, by
      rw [IsUnit.unit_spec, ZMod.val_natCast_of_lt (Finset.mem_range.mp hrange)]⟩
  · intro u _
    rw [← stdAddChar_nat_pair (q := q) a ((u : ZMod q).val), ZMod.natCast_zmod_val]

/-- Prime-logarithmic weights, represented in the complex field. -/
noncomputable def primeLog (k : ℕ) : ℂ :=
  ((if Nat.Prime k then Real.log (k : ℝ) else 0 : ℝ) : ℂ)

/-- A prime in a nonunit residue must divide the modulus. Its total
    logarithmic mass in any window is at most the logarithm of the modulus. -/
theorem primeLog_nonunit_mass_le (I : Finset ℕ) :
    (∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖primeLog k‖) ≤
      Real.log (q : ℝ) := by
  let J := I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q))
  change (∑ k ∈ J, ‖primeLog k‖) ≤ _
  have hsub : J.filter Nat.Prime ⊆ q.primeFactors := by
    intro k hk
    obtain ⟨hkJ, hp⟩ := Finset.mem_filter.mp hk
    have hnu := (Finset.mem_filter.mp hkJ).2
    have hd : k ∣ q := by
      by_contra hnd
      exact hnu ((ZMod.isUnit_iff_coprime k q).mpr ((hp.coprime_iff_not_dvd).mpr hnd))
    exact Nat.mem_primeFactors.mpr ⟨hp, hd, NeZero.ne q⟩
  calc
    _ = ∑ k ∈ J.filter Nat.Prime, Real.log (k : ℝ) := by
      conv_rhs => rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hp : Nat.Prime k
      · have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k from hp.pos)
        simp only [primeLog, ite_eq_left hp, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hk)]
      · simp [primeLog, hp]
    _ ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
      exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
      symm
      exact Real.log_prod fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ _ := by
      apply Real.log_le_log (Finset.prod_pos fun p hp => by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (Nat.prod_primeFactors_dvd q)

end

end GoldbachGRHWindow

end GoldbachGRHWindowParseval


end

section
/-!
This reduction uses the uniform prime-sum estimate in Friedlander and Goldston,
Sums of Three or More Primes, p. 290, formula (1.15), as an explicit hypothesis.
-/


namespace DeepThreeQuarters

noncomputable def geometricPhase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

end DeepThreeQuarters

/-!
# Bounds for the reciprocal totient density

The finite-product argument and logarithmic bound below are the proof of the
private helpers `harm_prod` and `ratio_bound` from the accepted Goldbach Research
PR #1810 (TH-0073), https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/1810/files.
The logarithmic estimate is exposed here for reuse independently of that PR's
energy theorem. The power bounds are consequences for the deep minor arcs.
-/

namespace DeepThreeQuarters

private theorem harm_prod (s : Finset ℕ) :
    (∀ p ∈ s, 2 ≤ p) → ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1) ≤ (s.card : ℝ) + 1 := by
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s hlt ih =>
    intro h2
    have ha : a ∉ s := fun h => lt_irrefl _ (hlt a h)
    have ha2 : 2 ≤ a := h2 a (Finset.mem_insert_self _ _)
    have ih' := ih (fun p hp => h2 p (Finset.mem_insert_of_mem hp))
    have hsub : s ⊆ Finset.Ico 2 a := by
      intro x hx
      rw [Finset.mem_Ico]
      exact ⟨h2 x (Finset.mem_insert_of_mem hx), hlt x hx⟩
    have hk : s.card ≤ a - 2 := by
      have := Finset.card_le_card hsub
      simpa using this
    have hk' : (s.card : ℝ) + 2 ≤ a := by
      have : s.card + 2 ≤ a := by omega
      exact_mod_cast this
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    push_cast
    have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha2
    have hpos : (0:ℝ) < (a:ℝ) - 1 := by linarith
    have hP : 0 ≤ ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1) := by
      apply Finset.prod_nonneg
      intro p hp
      have : (2:ℝ) ≤ p := by exact_mod_cast h2 p (Finset.mem_insert_of_mem hp)
      apply div_nonneg <;> linarith
    have hfrac : (a:ℝ) / ((a:ℝ) - 1) * ((s.card : ℝ) + 1) ≤ (s.card : ℝ) + 1 + 1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith [Nat.cast_nonneg (α := ℝ) s.card]
    calc (a:ℝ) / ((a:ℝ) - 1) * ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1)
        ≤ (a:ℝ) / ((a:ℝ) - 1) * ((s.card : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left ih' (by positivity)
      _ ≤ _ := hfrac

theorem totient_ratio_le_four_log (q : ℕ) (hq : 0 < q) :
    (q:ℝ) / (q.totient : ℝ) ≤ 4 * Real.log ((q + 2 : ℕ) : ℝ) := by
  have hprime : ∀ p ∈ q.primeFactors, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hh := harm_prod q.primeFactors hprime
  have hid := Nat.totient_mul_prod_primeFactors q
  have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hP : (0:ℝ) < ∏ p ∈ q.primeFactors, (p:ℝ) := by
    apply Finset.prod_pos
    intro p hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hprime p hp
    linarith
  have hP1 : (0:ℝ) < ∏ p ∈ q.primeFactors, ((p:ℝ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hprime p hp
    linarith
  have hid' : (q.totient : ℝ) * ∏ p ∈ q.primeFactors, (p:ℝ)
      = (q:ℝ) * ∏ p ∈ q.primeFactors, ((p:ℝ) - 1) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hid
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [this]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
    simp
  have heq : (q:ℝ) / (q.totient : ℝ) = ∏ p ∈ q.primeFactors, (p:ℝ) / ((p:ℝ) - 1) := by
    rw [Finset.prod_div_distrib, div_eq_div_iff hφ.ne' hP1.ne']
    linarith
  have hpow : 2 ^ q.primeFactors.card ≤ q := by
    calc 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
          Finset.pow_card_le_prod _ _ _ hprime
      _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hlog2 : (1:ℝ) / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at this
    linarith
  have hk : (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log ((q + 2 : ℕ) : ℝ) := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    have : ((2 ^ q.primeFactors.card : ℕ) : ℝ) ≤ ((q + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 ^ q.primeFactors.card ≤ q + 2)
    simpa using this
  have hL : (1:ℝ) / 2 ≤ Real.log ((q + 2 : ℕ) : ℝ) := by
    refine hlog2.trans (Real.log_le_log (by norm_num) ?_)
    exact_mod_cast (by omega : 2 ≤ q + 2)
  have hc : (0:ℝ) ≤ q.primeFactors.card := Nat.cast_nonneg _
  rw [heq]
  have : (q.primeFactors.card : ℝ) * (1 / 2) ≤ q.primeFactors.card * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2 hc
  linarith

/-- A modulus-uniform bound for every positive exponent, with an explicit constant. -/
theorem totient_ratio_le_rpow {ε : ℝ} (hε : 0 < ε) (q : ℕ) (hq : 0 < q) :
    (q : ℝ) / (q.totient : ℝ) ≤ (8 + 4 / ε) * (q : ℝ) ^ ε := by
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpow : 1 ≤ (q : ℝ) ^ ε := Real.one_le_rpow hq₁ hε.le
  have hlog : Real.log ((q + 2 : ℕ) : ℝ) ≤ Real.log 3 + Real.log q := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have hthree : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
  calc
    (q : ℝ) / (q.totient : ℝ) ≤ 4 * Real.log ((q + 2 : ℕ) : ℝ) :=
      totient_ratio_le_four_log q hq
    _ ≤ 8 + 4 * ((q : ℝ) ^ ε / ε) := by
      linarith [Real.log_natCast_le_rpow_div q hε]
    _ ≤ 8 * (q : ℝ) ^ ε + 4 * ((q : ℝ) ^ ε / ε) := by linarith
    _ = (8 + 4 / ε) * (q : ℝ) ^ ε := by ring

end DeepThreeQuarters


open Filter


open Filter


end

section
open Set Filter MeasureTheory Complex
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

theorem phase_dist (β x y : ℝ) : ‖phase β x-phase β y‖ ≤ |β| * |x-y| := by
  exact (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (phase_deriv β z).hasDerivWithinAt)
    (fun z _ => by simp [Real.norm_eq_abs]) (mem_univ y) (mem_univ x)

theorem phase_cell {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (β : ℝ) (k : ℕ) :
    ‖(∫ x : ℝ in ((k:ℝ)+u)..((k:ℝ)+1+u), phase β x) - phase β ((k:ℝ)+1)‖ ≤ |β| := by
  have hi := (continuous_phase β).intervalIntegrable ((k:ℝ)+u) ((k:ℝ)+1+u) (μ := volume)
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (k:ℝ)+u) (b := (k:ℝ)+1+u)
    (f := fun x => phase β x-phase β ((k:ℝ)+1)) (C := |β|) (fun x hx => by
      rw [uIoc_of_le (by linarith)] at hx
      have h := phase_dist β x ((k:ℝ)+1)
      exact h.trans (by
        conv_rhs => rw [← mul_one |β|]
        exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [hu.1,hx.1],by linarith [hu.2,hx.2]⟩) (abs_nonneg _)))
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const,intervalIntegral.integral_const] at hh
  simpa [show (k:ℝ)+1+u-((k:ℝ)+u) = 1 by ring] using hh

theorem phase_cells {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (β : ℝ) (a b : ℕ) (hab : a ≤ b) :
    ‖(∫ x : ℝ in ((a:ℝ)+u)..((b:ℝ)+u), phase β x) - ∑ k ∈ Finset.Ioc a b, phase β k‖ ≤
      ((b:ℝ)-a)*|β| := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hI : Finset.Ioc a (b+1) = insert (b+1) (Finset.Ioc a b) := by
      ext k; simp only [Finset.mem_Ioc,Finset.mem_insert]; omega
    have hk : b+1 ∉ Finset.Ioc a b := by simp
    rw [hI,Finset.sum_insert hk,Nat.cast_succ,← intervalIntegral.integral_add_adjacent_intervals
      ((continuous_phase β).intervalIntegrable _ ((b:ℝ)+u)) ((continuous_phase β).intervalIntegrable _ _)]
    have h := norm_add_le ((∫ x : ℝ in ((a:ℝ)+u)..((b:ℝ)+u), phase β x) - ∑ k ∈ Finset.Ioc a b, phase β k)
      ((∫ x : ℝ in ((b:ℝ)+u)..((b:ℝ)+1+u), phase β x) - phase β ((b:ℝ)+1))
    rw [show ∀ A B C D : ℂ, A+B-(D+C) = (A-C)+(B-D) by intros; ring]
    exact h.trans ((add_le_add ih (phase_cell hu β b)).trans_eq (by ring))

theorem principal_approx {a b : ℕ} (ha : 0 < a) (hab : a+1 ≤ b) (β : ℝ) :
    ‖transform a b β 1 - ∑ k ∈ Finset.Ioc a b, phase β k‖ ≤ ((b:ℝ)-a)*|β| := by
  let S := ∑ k ∈ Finset.Ioc a b, phase β k
  let H := fun u : ℝ => ∫ x : ℝ in ((a:ℝ)+u)..((b:ℝ)+u), phase β x
  have hi (x y : ℝ) := (continuous_phase β).intervalIntegrable x y (μ := volume)
  have hc : Continuous H := by
    let P := fun v : ℝ => ∫ x : ℝ in (0:ℝ)..v, phase β x
    have cp : Continuous P := intervalIntegral.continuous_primitive hi 0
    have eqH : H = fun u => P ((b:ℝ)+u)-P ((a:ℝ)+u) := by
      funext u
      exact (eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals (hi 0 ((a:ℝ)+u)) (hi ((a:ℝ)+u) ((b:ℝ)+u))))
    rw [eqH]
    exact (cp.comp (continuous_const.add continuous_id)).sub (cp.comp (continuous_const.add continuous_id))
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun u => H u-S) (C := ((b:ℝ)-a)*|β|) (fun u hu => by
      rw [uIoc_of_le zero_le_one] at hu
      exact phase_cells ⟨hu.1.le,hu.2⟩ β a b (by omega))
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const] at h
  rw [transform_eq_average (by exact_mod_cast ha) (by exact_mod_cast hab)]
  simpa [H,S,density] using h

end GoldbachTwistedMellin
end
end

section
open Finset Set Filter MeasureTheory Complex GoldbachGRHWindow GoldbachSmoothing Goldbach
open scoped Topology Interval
noncomputable section
namespace GoldbachTwistedMellin

private theorem nonprime_mass (n : ℕ) :
    (∑ k ∈ range (n+1), if k.Prime then 0 else ArithmeticFunction.vonMangoldt k) =
      Chebyshev.psi n - Chebyshev.theta n := by
  rw [Chebyshev.psi_eq_sum_Icc,Chebyshev.theta_eq_sum_Icc,Nat.floor_natCast,
    sum_filter,←sum_sub_distrib,Nat.range_succ_eq_Icc_zero]
  apply sum_congr rfl
  intro k _
  by_cases hk : k.Prime <;> simp [hk,ArithmeticFunction.vonMangoldt_apply_prime]

theorem prime_removal {q : ℕ} (χ : DirichletCharacter ℂ q) (a b n : ℕ)
    (hb : b ≤ n) (hn : 1 ≤ n) (β : ℝ) :
    ‖(∑ k ∈ Finset.Ioc a b, (primeLog k*phase β k)*χ (k:ZMod q)) -
      (∑ k ∈ Finset.Ioc a b, twistedCoefficient χ k*phase β k)‖ ≤
      2*Real.sqrt n*Real.log n := by
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ k ∈ Finset.Ioc a b, if k.Prime then 0 else ArithmeticFunction.vonMangoldt k := by
      apply sum_le_sum
      intro k _
      by_cases hk : k.Prime
      · simp [primeLog,twistedCoefficient,hk,ArithmeticFunction.vonMangoldt_apply_prime hk,mul_comm,mul_left_comm,mul_assoc]
      · simp only [primeLog,ite_eq_right hk,ofReal_zero,zero_mul,zero_sub,norm_neg,
          twistedCoefficient,Pi.mul_apply,norm_mul,norm_phase,mul_one,Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact (mul_le_mul_of_nonneg_right (χ.norm_le_one _) ArithmeticFunction.vonMangoldt_nonneg).trans_eq (one_mul _)
    _ ≤ ∑ k ∈ range (n+1), if k.Prime then 0 else ArithmeticFunction.vonMangoldt k := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk; have := (mem_Ioc.mp hk).2; apply Finset.mem_range.mpr; omega
      · intro k _ _; split_ifs <;> positivity
    _ ≤ _ := by rw [nonprime_mass]; exact Chebyshev.psi_sub_theta_le (by exact_mod_cast hn)


end GoldbachTwistedMellin
end
end


section
open Set Real Goldbach
noncomputable section
namespace GoldbachTwistedMellin

def logScale (x : ℝ) := 1+Real.log (2*x)
theorem logScale_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ logScale x := by
  dsimp [logScale]
  linarith only [Real.log_nonneg (by linarith : 1 ≤ 2*x)]
theorem log_le_scale {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ logScale x := by
  dsimp [logScale]
  linarith only [Real.log_le_log (by linarith : 0 < x) (by linarith : x ≤ 2*x)]

theorem log_window_scale {X x : ℝ} {q : ℕ} [NeZero q] (hX : 1 ≤ X) (hXx : X ≤ x)
    (hq : (q:ℝ) ≤ x) : logBudget q X ≤ 10*logScale x ∧ Real.log (heightCut X) ≤ 8*logScale x := by
  have hx := hX.trans hXx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hT : 1 ≤ heightCut X := by dsimp [heightCut]; exact one_le_pow₀ (by linarith)
  have hT0 := zero_lt_one.trans_le hT
  have qpos : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  have ht : Real.log (heightCut X) ≤ 8*Real.log (2*x) := by
    rw [heightCut,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) (by norm_num)
  have ht' : 2+heightCut X ≤ 3*heightCut X := by linarith
  have hlog := Real.log_le_log (by linarith : 0 < 2+heightCut X) ht'
  rw [Real.log_mul (by norm_num) hT0.ne'] at hlog
  have hqlog := Real.log_le_log (by positivity : 0 < 2*(q:ℝ)) (by linarith : 2*(q:ℝ) ≤ 2*x)
  have hln3 := Real.log_le_sub_one_of_pos (by norm_num : 0<(3:ℝ))
  have hln := Real.log_nonneg (by linarith : 1 ≤ 2*x)
  dsimp only [logScale,logBudget,logHeight]
  rw [abs_of_pos hT0,Real.log_mul (by positivity) (by linarith : 2+heightCut X ≠ 0)]
  constructor <;> linarith

end GoldbachTwistedMellin
end
end


section
open Finset Complex Real Goldbach GoldbachGRHWindow DeepThreeQuarters
noncomputable section
namespace GoldbachTwistedMellin

theorem rational_phase {q : ℕ} [NeZero q] (a k : ℕ) (β : ℝ) :
    phase (2*Real.pi*β) k*ZMod.stdAddChar ((a:ZMod q)*(k:ZMod q)) =
      geometricPhase ((k:ℝ)*((a:ℝ)/q+β)) := by
  have hc (m : ℕ) : ZMod.stdAddChar ((m:ℕ):ZMod q) = Complex.exp (2*(Real.pi:ℂ)*I*(m:ℂ)/(q:ℂ)) := by
    simpa only [Int.cast_natCast] using ZMod.stdAddChar_coe (N := q) (m:ℤ)
  rw [← Nat.cast_mul,hc,phase,geometricPhase,←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem angular_range {n q : ℕ} {β : ℝ} (hn : 64 ≤ n) (hq : 1 ≤ q)
    (hβ : |β| ≤ 1/((q:ℝ)*Real.sqrt n)) :
    |2*Real.pi*β| ≤ 1 ∧ (q:ℝ)*|2*Real.pi*β| * (n:ℝ) ≤ 8*Real.sqrt n := by
  have hnR : (64:ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hs : (8:ℝ) ≤ Real.sqrt n := by
    calc
      _ = Real.sqrt 64 := by norm_num
      _ ≤ _ := Real.sqrt_le_sqrt hnR
  have ht := (le_div_iff₀ (by positivity : 0 < (q:ℝ)*Real.sqrt n)).mp hβ
  have hπ := Real.pi_lt_four
  have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2*Real.pi by positivity)
  rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
  have hD : 8 ≤ (q:ℝ)*Real.sqrt n :=
    hs.trans ((one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right hqR (Real.sqrt_nonneg _)))
  constructor
  · by_contra! h
    nlinarith only [hh,hπ,mul_lt_mul_of_pos_right h (show 0 < (q:ℝ)*Real.sqrt n by positivity),hD]
  · have hh' : (q:ℝ)*(2*Real.pi*|β|)*Real.sqrt n ≤ 8 := by nlinarith only [hh,hπ]
    calc
      _ = ((q:ℝ)*(2*Real.pi*|β|)*Real.sqrt n)*Real.sqrt n := by
        rw [mul_assoc _ (Real.sqrt n),←sq,Real.sq_sqrt (Nat.cast_nonneg n)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hh' (Real.sqrt_nonneg n)

end GoldbachTwistedMellin
end
end

section
open Finset Complex GoldbachGRHWindow
open scoped ComplexConjugate
noncomputable section
namespace GoldbachTwistedMellin
variable {q : ℕ} [NeZero q]

/-- Fourier coefficient of the additive phase on the group of units. -/
noncomputable def additiveWeight (a : ZMod q) (χ : DirichletCharacter ℂ q) : ℂ :=
  conj (∑ r : ZMod q, conj (ZMod.stdAddChar (a*r))*χ r) / (q.totient:ℂ)

theorem weight_expansion (a : ZMod q) (χ : DirichletCharacter ℂ q) :
    additiveWeight a χ = (∑ r : ZMod q, ZMod.stdAddChar (a*r)*conj (χ r))/(q.totient:ℂ) := by
  simp [additiveWeight,map_sum]

private theorem units_filter (F : ZMod q → ℂ) :
    (∑ r : ZMod q, if IsUnit r then F r else 0) = ∑ u : (ZMod q)ˣ, F u := by
  classical
  rw [← Finset.sum_filter]
  have hs : (univ : Finset (ZMod q)).filter IsUnit = (univ : Finset (ZMod q)ˣ).map ⟨(↑), Units.val_injective⟩ := by
    ext r
    simp [IsUnit]
  rw [hs, Finset.sum_map]
  rfl

theorem additiveWeight_one (a : ZMod q) : additiveWeight a 1 = additiveModel q a := by
  classical
  rw [weight_expansion,additiveModel]
  congr 1
  rw [← units_filter (fun r : ZMod q => ZMod.stdAddChar (a*r))]
  refine sum_congr rfl fun r _ => ?_
  by_cases hr : IsUnit r
  · simp [MulChar.one_apply,hr]
  · simp [MulChar.map_nonunit _ hr,hr]

theorem additiveWeight_inversion (a s : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, additiveWeight a χ * χ s) =
      (if IsUnit s then ZMod.stdAddChar (a*s) else 0) := by
  classical
  have orth (r : ZMod q) : (∑ χ : DirichletCharacter ℂ q, conj (χ r)*χ s) =
      if r=s ∧ IsUnit s then (q.totient:ℂ) else 0 := by
    by_cases hr : IsUnit r
    · have inv (χ : DirichletCharacter ℂ q) : conj (χ r) = χ r⁻¹ := by
        have hχr : χ r ≠ 0 := (hr.map χ).ne_zero
        have hi : χ r⁻¹ = (χ r)⁻¹ := by
          calc
            _ = χ r⁻¹ * (χ r * (χ r)⁻¹) := by rw [mul_inv_cancel₀ hχr,mul_one]
            _ = _ := by rw [←mul_assoc,←map_mul,ZMod.inv_mul_of_unit r hr,map_one,one_mul]
        exact (MulChar.star_apply' χ r).trans ((MulChar.inv_apply_eq_inv' χ r).trans hi.symm)
      simp_rw [inv]
      rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hr s]
      by_cases h : r=s
      · subst s;simp [hr]
      · simp [h]
    · simp only [MulChar.map_nonunit _ hr,map_zero,zero_mul,sum_const_zero]
      split_ifs with h
      · exact False.elim (hr (h.1.symm ▸ h.2))
      · rfl
  have hφ : (q.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  calc
    _ = (∑ r : ZMod q, ZMod.stdAddChar (a*r)*(∑ χ : DirichletCharacter ℂ q, conj (χ r)*χ s))/(q.totient:ℂ) := by
      simp_rw [weight_expansion,div_mul_eq_mul_div,Finset.sum_mul,Finset.mul_sum,mul_assoc]
      rw [←Finset.sum_div,Finset.sum_comm]
    _ = _ := by
      simp_rw [orth]
      by_cases hs : IsUnit s
      · simp [hs,mul_ite,hφ]
      · simp [hs]


end GoldbachTwistedMellin
end
end

section
open Finset Complex Goldbach GoldbachSmoothing GoldbachGRHWindow
noncomputable section
namespace GoldbachTwistedMellin
variable {q : ℕ} [NeZero q]

/-- Inverting the unit characters leaves exactly the nonunit terms. -/
theorem sum_character_transfer (I : Finset ℕ) (w : ℕ → ℂ) (a : ZMod q) :
    (∑ k ∈ I, w k*ZMod.stdAddChar (a*(k:ZMod q))) =
      (∑ χ : DirichletCharacter ℂ q, additiveWeight a χ*(∑ k ∈ I,w k*χ (k:ZMod q))) +
      ∑ k ∈ I.filter (fun k : ℕ => ¬IsUnit (k:ZMod q)), w k*ZMod.stdAddChar (a*(k:ZMod q)) := by
  classical
  rw [Finset.sum_filter]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm,←Finset.sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  have h := congrArg (w k * ·) (additiveWeight_inversion a (k:ZMod q))
  simp only [Finset.mul_sum] at h
  simp_rw [mul_left_comm (additiveWeight a _) (w k)]
  rw [h]
  by_cases hk : IsUnit (k:ZMod q) <;> simp [hk]


end GoldbachTwistedMellin
end
end


section
open Set Finset Complex Goldbach DirichletCharacter
noncomputable section
namespace GoldbachTwistedMellin

private def zeroBin (t : ℝ) : Bool × ℕ := (decide (0≤t),⌊|t|⌋₊)
private def binCenter (p : Bool × ℕ) : ℝ := if p.1 then (p.2:ℝ) else -(p.2:ℝ)

private theorem bin_properties (t : ℝ) :
    ((zeroBin t).2:ℝ) ≤ |t| ∧ |t-binCenter (zeroBin t)| ≤ 1 := by
  have h := Nat.floor_le (abs_nonneg t)
  have h' := Nat.lt_floor_add_one |t|
  refine ⟨h,?_⟩
  by_cases ht : 0≤t
  · simp only [abs_of_nonneg ht] at h h'
    simp [binCenter,zeroBin,ht,abs_of_nonneg ht,abs_le];constructor <;> linarith
  · have hn := le_of_not_ge ht
    simp only [abs_of_nonpos hn] at h h'
    simp [binCenter,zeroBin,ht,abs_of_nonpos hn,abs_le];constructor <;> linarith

private theorem binCenter_abs (p : Bool × ℕ) : |binCenter p|=(p.2:ℝ) := by
  dsimp [binCenter];split <;> simp

/-- Sum the Mellin transform over a narrow real-part strip, counting analytic
multiplicities. Uniform local Jensen bounds apply to every height bin. -/
theorem near_line_residues :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Z : Finset ℂ)
    (a b X β B V : ℝ), 1≤X → X≤a → a+1≤b → b+1≤2*X →
    2≤B → V≤1 → (∀ z∈Z, 1/2≤z.re ∧ z.re≤V ∧ |z.im|≤B) →
    (∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z:ℝ)*‖transform a b β z‖) ≤
      C*X^V*logHeight q B*(1+Real.sqrt (1+4*|β| *X)+Real.log B) := by
  classical
  obtain ⟨K,hK,slice⟩ := unconditional_right_slice_count
  refine ⟨200*K,by positivity,?_⟩
  intro q _ χ Z a b X β B V hX ha hab hb hB hV geom
  let J := ⌈4*|β| *X⌉₊
  let M := ⌊B⌋₊
  let y := fun z : ℂ => zeroBin z.im
  let mult := fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z:ℝ)
  let W := 1+Real.sqrt (1+4*|β| *X)+Real.log B
  have hJ : 4*|β| * X ≤ (J:ℝ) := Nat.le_ceil _
  have hJ' : (J:ℝ) < 4*|β| *X+1 := Nat.ceil_lt_add_one (by positivity)
  have hM : (M:ℝ) ≤ B := Nat.floor_le (by linarith)
  have hgrid (z : ℂ) (hz : z∈Z) : y z ∈ grid (M+1) := by
    apply Finset.mem_product.mpr
    exact ⟨mem_univ _,mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (geom z hz).2.2))⟩
  have per (p : Bool×ℕ) (hp : p∈grid (M+1)) :
      (∑ z ∈ Z.filter (fun z => y z=p), mult z*‖transform a b β z‖) ≤
        (K*logHeight q B*X^V)*profile J p.2 := by
    let Y := Z.filter (fun z => y z=p)
    have hwlt (z : ℂ) (hz : z∈Y) : ‖transform a b β z‖ ≤ X^V*profile J p.2 := by
      obtain ⟨hzZ,he⟩ := mem_filter.mp hz
      obtain ⟨hl,hr,_⟩ := geom z hzZ
      have h := window_bin_bound hX ha hab hb (by linarith : 0≤z.re) (hr.trans hV) hr (bin_properties z.im).1 hJ
      have heq : line z.re z.im = z := by apply Complex.ext <;> simp
      rw [heq] at h
      simpa only [←he,y] using h
    have hcount := slice q χ (binCenter p) Y (fun z hz => by
      obtain ⟨hzZ,he⟩ := mem_filter.mp hz
      obtain ⟨hl,hr,_⟩ := geom z hzZ
      exact ⟨hl,by linarith,by simpa only [←he,y] using (bin_properties z.im).2⟩)
    have hj : p.2 ≤ M := Nat.lt_succ_iff.mp (mem_range.mp (mem_product.mp hp).2)
    have hlog : logHeight q (binCenter p) ≤ logHeight q B := by
      apply logHeight_mono_abs;rw [binCenter_abs,abs_of_nonneg (by linarith : 0≤B)]
      exact (show (p.2:ℝ) ≤ M by exact_mod_cast hj).trans hM
    have hm : (∑ z ∈ Y,mult z) ≤ K*logHeight q B := hcount.trans (mul_le_mul_of_nonneg_left hlog hK.le)
    calc
      _ ≤ ∑ z ∈ Y,mult z*(X^V*profile J p.2) := sum_le_sum fun z hz =>
        mul_le_mul_of_nonneg_left (hwlt z hz) (Nat.cast_nonneg _)
      _ = (∑ z ∈ Y,mult z)*(X^V*profile J p.2) := (Finset.sum_mul ..).symm
      _ ≤ (K*logHeight q B)*(X^V*profile J p.2) :=
        mul_le_mul_of_nonneg_right hm (mul_nonneg (Real.rpow_nonneg (by linarith) _) (profile_nonneg ..))
      _ = _ := by ring
  have hlogB := Real.log_nonneg (by linarith : 1≤B)
  have hln : Real.log (M+1:ℝ) ≤ 1+Real.log B := by
    have hy := Real.log_le_log (by positivity : 0<(M:ℝ)+1) (by linarith : (M:ℝ)+1 ≤ 2*B)
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (by linarith)] at hy
    linarith only [hy,Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
  have hsqrt : Real.sqrt J ≤ Real.sqrt (1+4*|β| *X) := Real.sqrt_le_sqrt (by linarith)
  have hprof : (∑ j ∈ range (M+1),profile J j) ≤ 100*W := by
    apply (profile_sum J M).trans;dsimp [W]
    nlinarith only [hln,hlogB,hsqrt,Real.sqrt_nonneg (1+4*|β| *X),
      mul_le_mul_of_nonneg_right Real.pi_lt_four.le (Real.sqrt_nonneg (J:ℝ))]
  have tot := sum_le_sum per
  rw [Finset.sum_fiberwise_of_maps_to hgrid,←Finset.mul_sum,sum_grid_weight] at tot
  have hL : 0 ≤ logHeight q B := zero_le_one.trans (logHeight_ge_one q B)
  exact (tot.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprof (by norm_num : (0:ℝ)≤2))
    (by positivity))).trans_eq (by dsimp [W,mult];ring)
end GoldbachTwistedMellin
end
end

section
open Set Finset Complex Goldbach DirichletCharacter
noncomputable section
namespace GoldbachTwistedMellin

theorem high_edge_residues :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Z : Finset ℂ)
    (a b X β B : ℝ), 1≤X → X≤a → a+1≤b → b+1≤2*X → |β|≤1 → 2≤B → X^4≤B^2 →
    (∀ z∈Z, 1/2≤z.re ∧ z.re≤2 ∧ B≤|z.im| ∧ |z.im|≤B+1) →
    (∑ z ∈ Z,(analyticOrderNatAt (regularizedL χ) z:ℝ)*‖transform a b β z‖) ≤ C*logHeight q B := by
  classical
  obtain ⟨K,hK,slice⟩ := unconditional_right_slice_count
  refine ⟨192*K,by positivity,?_⟩
  intro q _ χ Z a b X β B hX ha hab hb hβ hB hBX geom
  let m := fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z:ℝ)
  let pos := fun z : ℂ => 0≤z.im
  have top := slice q χ B (Z.filter pos) (fun z hz => by
    obtain ⟨hzZ,hp⟩ := mem_filter.mp hz
    obtain ⟨hr,hr',hi,hi'⟩ := geom z hzZ
    rw [abs_of_nonneg hp] at hi hi'
    exact ⟨hr,hr',abs_le.mpr ⟨by linarith,by linarith⟩⟩)
  have bot := slice q χ (-B) (Z.filter fun z => ¬pos z) (fun z hz => by
    obtain ⟨hzZ,hn⟩ := mem_filter.mp hz
    obtain ⟨hr,hr',hi,hi'⟩ := geom z hzZ
    rw [abs_of_nonpos (le_of_not_ge hn)] at hi hi'
    exact ⟨hr,hr',abs_le.mpr ⟨by linarith,by linarith⟩⟩)
  rw [show logHeight q (-B)=logHeight q B by simp [logHeight]] at bot
  have cnt : (∑ z ∈ Z,m z) ≤ 2*K*logHeight q B := by
    rw [←Finset.sum_filter_add_sum_filter_not Z pos m]
    exact (add_le_add top bot).trans_eq (by ring)
  have hwin (z : ℂ) (hz : z∈Z) : ‖transform a b β z‖ ≤ 96 := by
    obtain ⟨hr,hr',hi,_⟩ := geom z hz
    apply (norm_transform_tail hX ha hab hb hβ z (by linarith) hr' (by linarith)).trans
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < |z.im|))).mpr
    exact mul_le_mul_of_nonneg_left (hBX.trans (pow_le_pow_left₀ (by linarith) hi _)) (by norm_num)
  calc
    _ ≤ ∑ z ∈ Z,m z*96 := sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (hwin z hz) (Nat.cast_nonneg _)
    _ = (∑ z ∈ Z,m z)*96 := (Finset.sum_mul ..).symm
    _ ≤ (2*K*logHeight q B)*96 := mul_le_mul_of_nonneg_right cnt (by norm_num)
    _ = _ := by ring
end GoldbachTwistedMellin
end
end

section
open Set Finset Complex Goldbach DirichletCharacter GoldbachSmoothing
noncomputable section
namespace GoldbachTwistedMellin


noncomputable def fixedZeroTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a b X β : ℝ) : ℂ :=
  ∑ z ∈ exceptionalZeros χ (heightCut X), (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform a b β z

/-- Remove contour choices from the explicit formula. Zeros between the two
abscissae are bounded at the window scale, and the two top slices have small tails. -/
theorem fixed_dyadic_model {d : ℝ} (hd : 0<d) (hd' : d≤1/8) :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a b : ℕ) (X β : ℝ),
      1≤X → X≤(a:ℝ) → (a:ℝ)+1≤b → (b:ℝ)+1≤2*X → |β|≤1 →
      ‖(∑ k ∈ Finset.Ioc a b,twistedCoefficient χ k*phase β k) -
        (principalFlag χ*transform a b β 1 - fixedZeroTerm χ a b X β)‖ ≤
      C*X^(1/2+2*d)*(logBudget q X)^2*(1+Real.sqrt (1+4*|β| *X)+Real.log (heightCut X)) := by
  classical
  obtain ⟨C,hC,model⟩ := dyadic_zero_model hd hd'
  obtain ⟨K,hK,narrow⟩ := near_line_residues
  obtain ⟨A,hA,high⟩ := high_edge_residues
  refine ⟨C+K+A,by positivity,?_⟩
  intro q _ χ a b X β hX ha hab hb hβ
  let B := heightCut X
  obtain ⟨T,hT,σ,hσ,e⟩ := model q χ a b X β hX ha hab hb hβ
  let V := 1/2+2*d
  let Z := exceptionalZeros χ B
  let Y := boxZeros χ σ 2 (-T) T
  let F := fun z : ℂ => (analyticOrderNatAt (regularizedL χ) z:ℂ)*transform a b β z
  let S := X^V
  let L := logBudget q X
  let W := 1+Real.sqrt (1+4*|β| *X)+Real.log B
  have hV : V≤1 := by dsimp [V];linarith
  have hS : 1 ≤ S := Real.one_le_rpow hX (by dsimp [V];linarith)
  have hB : 2≤B := by linarith [heightCut_ge hX]
  have hLB : 1≤logHeight q B := logHeight_ge_one _ _
  have hL : 1≤L := by dsimp [L,logBudget,B] at *;linarith only [hLB]
  have hW : 1≤W := by dsimp [W];linarith only [Real.sqrt_nonneg (1+4*|β| *X),Real.log_nonneg (by linarith : 1≤B)]
  have hLSq : logHeight q B ≤ L^2 := by
    have h' : logHeight q B ≤ L := by dsimp [L,logBudget,B];linarith
    exact h'.trans (le_self_pow₀ hL (by decide))
  have lowGeom (z : ℂ) (hz : z∈ Z \ Y) : 1/2≤z.re ∧ z.re≤V ∧ |z.im|≤B := by
    obtain ⟨hzZ,hn⟩ := mem_sdiff.mp hz
    obtain ⟨hr,hi,hzero⟩ := (mem_exceptionalZeros χ B z).mp hzZ
    have hright : z.re≤2 := by by_contra! h;exact regularizedL_ne_zero_right χ (by linarith) hzero
    refine ⟨hr.le,?_,hi⟩
    by_contra! h
    apply hn
    exact (mem_boxZeros χ _ _ _ _ z).mpr ⟨mem_reProdIm.mpr
      ⟨⟨hσ.2.le.trans (by exact h.le),hright⟩,abs_le.mp (hi.trans hT.1)⟩,hzero⟩
  have highGeom (z : ℂ) (hz : z∈ Y \ Z) : 1/2≤z.re ∧ z.re≤2 ∧ B ≤ |z.im| ∧ |z.im|≤B+1 := by
    obtain ⟨hzY,hn⟩ := mem_sdiff.mp hz
    obtain ⟨h,hzero⟩ := (mem_boxZeros χ _ _ _ _ z).mp hzY
    obtain ⟨hr,hi⟩ := mem_reProdIm.mp h
    have hstrict : 1/2<z.re := by linarith [hσ.1,hr.1]
    refine ⟨hstrict.le,hr.2,?_,(abs_le.mpr hi).trans hT.2⟩
    by_contra! h
    exact hn ((mem_exceptionalZeros χ B z).mpr ⟨hstrict,h.le,hzero⟩)
  have hpow : X^4 ≤ B^2 := by
    have h8 := pow_le_pow_right₀ hX (show 4≤8 by decide)
    have h : X^8≤B := by dsimp [B,heightCut];rw [mul_pow];norm_num;linarith [pow_nonneg (by linarith : 0≤X) 8]
    exact (h8.trans h).trans (le_self_pow₀ (by linarith : 1≤B) (by decide))
  have low := narrow q χ (Z \ Y) a b X β B V hX ha hab hb hB hV lowGeom
  have hi := high q χ (Y \ Z) a b X β B hX ha hab hb hβ hB hpow highGeom
  have nf (z : ℂ) : ‖F z‖ = (analyticOrderNatAt (regularizedL χ) z:ℝ)*‖transform a b β z‖ := by simp [F]
  have small : ‖(∑ z ∈ Z,F z)-(∑ z ∈ Y,F z)‖ ≤ (K+A)*S*L^2*W := by
    rw [←Finset.sum_sdiff_sub_sum_sdiff]
    apply (norm_sub_le ..).trans
    apply (add_le_add (norm_sum_le ..) (norm_sum_le ..)).trans
    simp_rw [nf]
    have low' : K*S*logHeight q B*W ≤ K*S*L^2*W := by gcongr
    have hh := (mul_le_mul_of_nonneg_left hLSq hA.le).trans (show A*L^2 ≤ A*S*L^2*W from by
      have h := le_mul_of_one_le_left (sq_nonneg L) hS
      have h' := le_mul_of_one_le_right (show 0≤S*L^2 by positivity) hW
      nlinarith only [mul_le_mul_of_nonneg_left (h.trans h') hA.le])
    exact (add_le_add (low.trans low') (hi.trans hh)).trans_eq (by ring)
  let P := ∑ k ∈ Finset.Ioc a b,twistedCoefficient χ k*phase β k
  let M := principalFlag χ*transform a b β 1
  change ‖P-(M-∑ z ∈ Z,F z)‖ ≤ _
  change ‖P-(M-∑ z ∈ Y,F z)‖ ≤ C*S*L^2*W at e
  have eq' : P-(M-∑ z ∈ Z,F z) = (P-(M-∑ z ∈ Y,F z))+((∑ z ∈ Z,F z)-(∑ z ∈ Y,F z)) := by abel
  rw [eq']
  exact (norm_add_le ..).trans ((add_le_add e small).trans_eq (by dsimp [S,L,W,V,B];ring))
end GoldbachTwistedMellin
end
end


section
open Finset Real Complex Goldbach DeepThreeQuarters Filter
noncomputable section
namespace GoldbachTwistedMellin

theorem quartic_log_scale {e : ℝ} (he : 0 < e) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x → logScale x^4 ≤ D*x^e := by
  let u := e/4
  have hu : 0 < u := by dsimp [u]; positivity
  let c := 1+Real.log 2+1/u
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c^4,by positivity,?_⟩
  intro x hx
  have hx0 := zero_lt_one.trans_le hx
  have hXu := Real.one_le_rpow hx hu.le
  have hlog := Real.log_le_rpow_div hx0.le hu
  have h : logScale x ≤ c*x^u := by
    rw [logScale,Real.log_mul (by norm_num) hx0.ne']
    dsimp [c]
    rw [one_div]
    rw [div_eq_mul_inv] at hlog
    nlinarith only [hlog,mul_le_mul_of_nonneg_left hXu (by linarith : 0 ≤ 1+Real.log 2)]
  refine (pow_le_pow_left₀ (zero_le_one.trans (logScale_one hx)) h 4).trans_eq ?_
  rw [mul_pow,←Real.rpow_mul_natCast hx0.le]
  have hu3 : u*(4:ℕ) = e := by dsimp [u]; ring
  rw [hu3]

end GoldbachTwistedMellin
end
end


open Goldbach GoldbachTwistedMellin
end

section



variable [GoldbachMajorCutoff]


section

namespace GoldbachSmoothMellin

open Complex MeasureTheory Set Filter GoldbachTwistedMellin
open scoped Topology
open scoped Interval

noncomputable def smoothTransform (a b β : ℝ) (w : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ x in a..b, (w x : ℂ) * density β s x

theorem smooth_transform_recurrence {w dw : ℝ → ℝ} {a b β : ℝ} {s : ℂ}
    (ha : 0 < a) (hab : a ≤ b) (hs : 0 < s.re)
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (dw x) x)
    (hdw : ContinuousOn dw (Icc a b)) (hL : w a = 0) (hR : w b = 0) :
    s * smoothTransform a b β w s =
      -(smoothTransform a b β dw (s + 1)) - ((β : ℂ) * I) * smoothTransform a b β w (s + 1) := by
  let H (x : ℝ) := s * ((w x : ℂ) * density β s x)
  let V (x : ℝ) := (dw x : ℂ) * density β (s+1) x
  let T (x : ℝ) := ((β : ℂ) * I) * ((w x : ℂ) * density β (s+1) x)
  have hwc : ContinuousOn w (Icc a b) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hC (z : ℂ) : ContinuousOn (density β z) (Icc a b) := fun x hx =>
    (continuousAt_density β z (ha.trans_le hx.1)).continuousWithinAt
  have hH : IntervalIntegrable H volume a b :=
    ((continuous_ofReal.comp_continuousOn hwc).mul (hC s) |>.const_mul s).intervalIntegrable_of_Icc hab
  have hV : IntervalIntegrable V volume a b :=
    ((continuous_ofReal.comp_continuousOn hdw).mul (hC (s+1))).intervalIntegrable_of_Icc hab
  have hT : IntervalIntegrable T volume a b :=
    ((continuous_ofReal.comp_continuousOn hwc).mul (hC (s+1)) |>.const_mul _).intervalIntegrable_of_Icc hab
  have hder (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt
      (fun y => (w y : ℂ) * density β (s+1) y) (H x + V x + T x) x := by
    have hne : s ≠ 0 := fun h => by simp [h] at hs
    have hp := (phase_deriv β x).mul (hasDerivAt_ofReal_cpow_const (ha.trans_le hx.1).ne' hne)
    have hp' : HasDerivAt (density β (s+1))
        (s * density β s x + ((β : ℂ) * I) * density β (s+1) x) x := by
      convert hp using 1
      · funext y
        exact density_succ β s y
      · rw [density_succ]
        unfold density
        ring
    convert ((hw x hx).ofReal_comp).mul hp' using 1
    dsimp only [H, V, T]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hder x ((uIcc_of_le hab) ▸ hx)) ((hH.add hV).add hT)
  rw [intervalIntegral.integral_add (hH.add hV) hT, intervalIntegral.integral_add hH hV] at h
  have heq : (∫ x in a..b, H x) = s * smoothTransform a b β w s := intervalIntegral.integral_const_mul _ _
  have ht : (∫ x in a..b, T x) = ((β : ℂ) * I) * smoothTransform a b β w (s+1) := intervalIntegral.integral_const_mul _ _
  rw [heq, ht] at h
  change s * smoothTransform a b β w s + smoothTransform a b β dw (s + 1) +
    ((β : ℂ) * I) * smoothTransform a b β w (s + 1) =
      (w b : ℂ) * density β (s+1) b - (w a : ℂ) * density β (s+1) a at h
  rw [hL, hR, ofReal_zero, zero_mul, zero_mul, sub_zero] at h
  linear_combination h

theorem smooth_transform_norm_bound {X a b β : ℝ} {w : ℝ → ℝ} {s : ℂ} {M : ℝ}
    (hX : 0 < X) (ha : X ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * X)
    (hs : 0 ≤ s.re) (hM : 0 ≤ M) (hw : ∀ x ∈ Icc a b, ‖w x‖ ≤ M) :
    ‖smoothTransform a b β w s‖ ≤ M * (2 * X) ^ s.re := by
  have hbnd (x : ℝ) (hx : x ∈ uIcc a b) :
      ‖(w x : ℂ) * density β s x‖ ≤ (M * (2*X) ^ s.re) / X := by
    rw [uIcc_of_le hab] at hx
    have hx₀ := hX.trans_le (ha.trans hx.1)
    have hx₂ := hx.2.trans hb
    have hz : ‖density β s x‖ ≤ (2 * X) ^ s.re / X := by
      rw [density, norm_mul, norm_phase, one_mul, norm_cpow_eq_rpow_re_of_pos hx₀,
        sub_re, one_re, Real.rpow_sub hx₀, Real.rpow_one]
      exact (div_le_div_of_nonneg_right (Real.rpow_le_rpow hx₀.le hx₂ hs) hx₀.le).trans
        (div_le_div_of_nonneg_left (by positivity) hX (ha.trans hx.1))
    rw [norm_mul, Complex.norm_real, mul_div_assoc]
    exact mul_le_mul (hw x hx) hz (norm_nonneg _) hM
  unfold smoothTransform
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => hbnd x (uIoc_subset_uIcc hx))).trans
  rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  calc
    _ ≤ (M * (2 * X) ^ s.re / X) * X := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := div_mul_cancel₀ _ hX.ne'

theorem half_recurrence_bound {u : ℕ → ℝ} {C M : ℝ} (hC : 0 ≤ C)
    (hB : ∀ n, u n ≤ M) (hrec : ∀ n, u n ≤ C + u (n+1)/2) (n : ℕ) :
    u n ≤ 2*C := by
  have hiter (k : ℕ) : ∀ m, u m ≤ 2*C + M*(1/2 : ℝ)^k := by
    induction k with
    | zero =>
      intro m
      norm_num
      linarith [hB m]
    | succ k ih =>
      intro m
      calc
        _ ≤ C + u (m+1)/2 := hrec m
        _ ≤ C + (2*C + M*(1/2 : ℝ)^k)/2 := by linarith only [ih (m+1)]
        _ = _ := by rw [pow_succ]; ring
  have ht : Tendsto (fun k : ℕ => 2*C + M*(1/2 : ℝ)^k) atTop (nhds (2*C)) := by
    simpa only [mul_zero, add_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)).const_mul M).const_add (2*C)
  exact ge_of_tendsto' ht (fun k => hiter k n)

private theorem smooth_mellin_gain (P Q : ℂ → ℂ) (s : ℂ)
    {R β U V : ℝ} (hR : 0 < R) (ht : 0 < |s.im|) (hV : 0 ≤ V)
    (hβ : 2 * R * |β| ≤ |s.im|) :
    let z (n : ℕ) := s + (n:ℂ)
    let A (n : ℕ) := R^(z n).re
    (∀ n : ℕ, (‖P (z n)‖ / A n) ≤ U) →
    (∀ n : ℕ, (‖Q (z n)‖ / A n) ≤ V) →
    (∀ n : ℕ, z n * P (z n) = -Q (z (n+1)) - ((β:ℂ)*I)*P (z (n+1))) →
    ∀ n : ℕ, ‖P (z n)‖ / A n ≤ ((2*R) / |s.im|) * V := by
  dsimp only
  intro hP hQ hrec
  let z (n : ℕ) := s + (n:ℂ)
  let A (n : ℕ) := R^(z n).re
  let t := |s.im|
  let u (n : ℕ) := ‖P (z n)‖ / A n
  let v (n : ℕ) := ‖Q (z n)‖ / A n
  have hA (n : ℕ) : 0 < A n := Real.rpow_pos_of_pos hR _
  have hAs (n : ℕ) : A (n+1) = R * A n := by
    have hz : (z (n+1)).re = (z n).re+1 := by simp [z, add_assoc]
    dsimp only [A]
    rw [hz, Real.rpow_add_one hR.ne', mul_comm]
  have hUn (n : ℕ) : 0 ≤ u n := div_nonneg (norm_nonneg _) (hA n).le
  have hUa (n : ℕ) : u n * A n = ‖P (z n)‖ := div_mul_cancel₀ _ (hA n).ne'
  have hVa (n : ℕ) : v n * A n = ‖Q (z n)‖ := div_mul_cancel₀ _ (hA n).ne'
  have hAngle (n : ℕ) : t ≤ ‖z n‖ := by simpa [z,t] using Complex.abs_im_le_norm (z n)
  have hfreq : ‖(β:ℂ)*I‖ = |β| := by simp [Complex.norm_real,Real.norm_eq_abs]
  have hsmall : |β| * R ≤ t/2 := by dsimp only [t]; nlinarith only [hβ]
  have hstep (n : ℕ) : u n ≤ (R/t)*V + u (n+1)/2 := by
    have h₁ : t*‖P (z n)‖ ≤ ‖Q (z (n+1))‖ + |β| * ‖P (z (n+1))‖ := by
      apply (mul_le_mul_of_nonneg_right (hAngle n) (norm_nonneg _)).trans
      rw [← norm_mul, hrec n]
      exact (norm_sub_le _ _).trans_eq (by rw [norm_neg,norm_mul,hfreq])
    rw [← hUa n, ← hVa (n+1), ← hUa (n+1), hAs] at h₁
    have h₂ : t*(u n) ≤ R*v (n+1)+(|β| * R)*u (n+1) := by
      apply le_of_mul_le_mul_right ?_ (hA n)
      convert h₁ using 1 <;> ring
    have hs := h₂.trans (add_le_add (mul_le_mul_of_nonneg_left (hQ (n+1)) hR.le)
      (mul_le_mul_of_nonneg_right hsmall (hUn (n+1))))
    apply le_of_mul_le_mul_right ?_ ht
    convert hs using 1
    · ring
    · field_simp [show t ≠ 0 from ht.ne']
      ring
  intro n
  apply (half_recurrence_bound (mul_nonneg (div_nonneg hR.le ht.le) hV) hP hstep n).trans_eq
  ring

end GoldbachSmoothMellin


namespace GoldbachSmoothWindow

open Set Filter
open scoped Topology ContDiff


theorem weight_range (t : ℝ) : 0 ≤ weight t ∧ weight t ≤ 1 :=
  ⟨bump.nonneg, bump.le_one⟩

theorem weight_one {t : ℝ} (ht : t ∈ Icc (9/8 : ℝ) (15/8)) : weight t = 1 := by
  apply bump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  change |t - 3/2| ≤ (3/8 : ℝ)
  exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩


theorem weight_smooth {n : ℕ} : ContDiff ℝ n weight := by
  change ContDiff ℝ ((n : ℕ∞) : ℕ∞ω) (bump : ℝ → ℝ)
  exact bump.contDiff

theorem weight_derivative_endpoint (j : ℕ) :
    iteratedDeriv j weight 1 = 0 ∧ iteratedDeriv j weight 2 = 0 := by
  have hL : weight =ᶠ[𝓝 (1 : ℝ)] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds (show (1 : ℝ) < 17/16 by norm_num)] with t ht
    exact weight_zero (Or.inl (le_of_lt ht))
  have hR : weight =ᶠ[𝓝 (2 : ℝ)] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds (show (31/16 : ℝ) < 2 by norm_num)] with t ht
    exact weight_zero (Or.inr (le_of_lt ht))
  exact ⟨(hL.iteratedDeriv_eq j).trans (by simp), (hR.iteratedDeriv_eq j).trans (by simp)⟩

theorem weight_derivative_bound (j : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖iteratedDeriv j weight t‖ ≤ M := by
  have hcs : ∀ k : ℕ, HasCompactSupport (iteratedDeriv k weight) := by
    intro k
    induction k with
    | zero =>
      change HasCompactSupport (iteratedDeriv 0 (bump : ℝ → ℝ))
      rw [iteratedDeriv_zero]
      exact bump.hasCompactSupport
    | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv
  have hh := (hcs j).exists_bound_of_continuous
    (weight_smooth.continuous_iteratedDeriv' j)
  obtain ⟨M, hM⟩ := hh
  exact ⟨M, (norm_nonneg _).trans (hM 1), hM⟩


theorem scaledWeight_derivative (j : ℕ) (X t : ℝ) :
    iteratedDeriv j (scaledWeight X) t = X⁻¹ ^ j * iteratedDeriv j weight (t / X) := by
  change iteratedDeriv j (fun y => weight (y / X)) t = _
  simp_rw [div_eq_mul_inv, mul_comm _ X⁻¹]
  rw [iteratedDeriv_comp_const_mul weight_smooth X⁻¹]

end GoldbachSmoothWindow
end

section
section

open Finset MeasureTheory
open scoped SchwartzMap FourierTransform ComplexInnerProductSpace ComplexConjugate

namespace GoldbachZeroStrip

private theorem inverse_square_sum_le (J : Finset ℕ) :
    (∑ k ∈ J, (1 : ℝ) / (1 + (k : ℝ)^2)) ≤ 4 := by
  have htel (n : ℕ) :
      (∑ k ∈ range n, (1 : ℝ) / (((k : ℝ)+1)*((k : ℝ)+2))) =
        1 - 1 / ((n : ℝ)+1) := by
    induction n with
    | zero => simp
    | succ n h =>
      rw [sum_range_succ, h]
      push_cast
      have h₁ : (n : ℝ) + 1 ≠ 0 := by positivity
      have h₂ : (n : ℝ) + 2 ≠ 0 := by positivity
      have he : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
      rw [he]
      field_simp
      ring
  let N := J.sup id + 1
  have hsubset : J ⊆ range N := by
    intro k hk
    have hle : k ≤ J.sup id := Finset.le_sup (f := id) hk
    exact mem_range.mpr (Nat.lt_succ_of_le hle)
  have hpos (k : ℕ) : (0 : ℝ) ≤ 1 / (((k : ℝ)+1)*((k : ℝ)+2)) := by positivity
  calc
    _ ≤ ∑ k ∈ J, 4 * ((1 : ℝ) / (((k : ℝ)+1)*((k : ℝ)+2))) := by
      apply sum_le_sum
      intro k hk
      rw [mul_one_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg ((k : ℝ) - 1 / 2)]
    _ = 4 * ∑ k ∈ J, (1 : ℝ) / (((k : ℝ)+1)*((k : ℝ)+2)) := by rw [mul_sum]
    _ ≤ 4 * ∑ k ∈ range N, (1 : ℝ) / (((k : ℝ)+1)*((k : ℝ)+2)) :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsubset (fun k _ _ => hpos k)) (by norm_num)
    _ ≤ _ := by rw [htel]; nlinarith [show (0 : ℝ) ≤ 1 / ((N : ℝ)+1) by positivity]

/-- A unit-window count controls the row sum of a quadratically decaying kernel. -/
theorem inverse_square_row_le {ι : Type*} (S : Finset ι) (height : ι → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hunit : ∀ y : ℝ, ((S.filter (fun i => y ≤ height i ∧ height i ≤ y + 1)).card : ℝ) ≤ B)
    (a : ℝ) :
    (∑ j ∈ S, (1 : ℝ) / (1 + (height j - a)^2)) ≤ 8*B := by
  classical
  let bucket (j : ι) : ℕ := ⌊|height j - a|⌋₊
  let I := S.image bucket
  have hmaps : (S : Set ι).MapsTo bucket I := by
    intro j hj
    exact mem_image_of_mem _ hj
  have hbucket (j : ι) : (bucket j : ℝ) ≤ |height j - a| ∧
      |height j - a| < (bucket j : ℝ) + 1 :=
    ⟨Nat.floor_le (abs_nonneg _), Nat.lt_floor_add_one _⟩
  have hcard (k : ℕ) : ((S.filter (fun j => bucket j = k)).card : ℝ) ≤ 2*B := by
    let l := S.filter (fun j => a - k - 1 ≤ height j ∧ height j ≤ a - k - 1 + 1)
    let r := S.filter (fun j => a + k ≤ height j ∧ height j ≤ a + k + 1)
    have hsub : S.filter (fun j => bucket j = k) ⊆ l ∪ r := by
      intro j hj
      obtain ⟨hjs, he⟩ := mem_filter.mp hj
      obtain ⟨hlo, hhi⟩ := hbucket j
      rw [he] at hlo hhi
      apply mem_union.mpr
      by_cases h : a ≤ height j
      · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hlo hhi
        exact Or.inr (mem_filter.mpr ⟨hjs, by constructor <;> linarith⟩)
      · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))] at hlo hhi
        exact Or.inl (mem_filter.mpr ⟨hjs, by constructor <;> linarith⟩)
    have hl : (l.card : ℝ) ≤ B := hunit (a-k-1)
    have hr : (r.card : ℝ) ≤ B := hunit (a+k)
    have hsum : ((S.filter (fun j => bucket j = k)).card : ℝ) ≤ (l.card : ℝ) + r.card := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le l r)
    linarith
  calc
    _ = ∑ k ∈ I, ∑ j ∈ S.filter (fun j => bucket j = k),
        (1 : ℝ) / (1 + (height j - a)^2) := (sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k ∈ I, (2*B) * ((1 : ℝ) / (1 + (k : ℝ)^2)) := by
      apply sum_le_sum
      intro k hk
      calc
        _ ≤ ∑ _j ∈ S.filter (fun j => bucket j = k), (1 : ℝ) / (1 + (k : ℝ)^2) := by
          apply sum_le_sum
          intro j hj
          have he := (mem_filter.mp hj).2
          have hb := (hbucket j).1
          rw [he] at hb
          have hp : (k : ℝ) ^ 2 ≤ (height j - a)^2 := by
            simpa only [sq_abs] using (sq_le_sq' (by linarith [abs_nonneg (height j - a)] : -|height j - a| ≤ (k : ℝ)) hb)
          exact one_div_le_one_div_of_le (by positivity) (by linarith)
        _ = ((S.filter (fun j => bucket j = k)).card : ℝ) *
            ((1 : ℝ) / (1 + (k : ℝ)^2)) := by simp [nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcard k) (by positivity)
    _ = (2*B) * ∑ k ∈ I, (1 : ℝ) / (1+(k : ℝ)^2) := by rw [mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (inverse_square_sum_le I) (show 0 ≤ 2*B by positivity)
      nlinarith


private theorem re_inner_self {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (g : V) : (inner ℂ g g).re = ‖g‖ ^ 2 := by
  change RCLike.re (inner ℂ g g) = _
  rw [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]

private theorem schwartz_norm_sq (f : 𝓢(ℝ, ℂ)) :
    (∫ x, ‖f x‖ ^ 2) = ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  let g := f.toLp 2 (volume : Measure ℝ)
  change _ = ‖g‖ ^ 2
  rw [← re_inner_self, L2.inner_def]
  change _ = RCLike.re (∫ x, inner ℂ (g x) (g x))
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) g g)]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 (volume : Measure ℝ)] with x hx
  change _ = (inner ℂ (g x) (g x)).re
  rw [show g x = f x from hx, re_inner_self]

/-- The Fourier energy of a finite sum is controlled by the pairwise inner products. -/
theorem fourier_energy_le {ι : Type*} (S : Finset ι) (f : ι → 𝓢(ℝ, ℂ)) :
    (∫ ξ : ℝ, ‖∑ j ∈ S, (𝓕 (f j)) ξ‖ ^ 2) ≤
      ∑ i ∈ S, ∑ j ∈ S,
        ‖inner ℂ ((f i).toLp 2 (volume : Measure ℝ)) ((f j).toLp 2 (volume : Measure ℝ))‖ := by
  let F : 𝓢(ℝ, ℂ) := ∑ i ∈ S, f i
  have hF (ξ : ℝ) : (𝓕 F) ξ = ∑ j ∈ S, (𝓕 (f j)) ξ := by
    dsimp only [F]
    rw [FourierTransform.fourier_sum, sum_apply]
  simp_rw [← hF]
  rw [schwartz_norm_sq, ← SchwartzMap.toLp_fourier_eq, Lp.norm_fourier_eq]
  let L := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)
  have hL : F.toLp 2 (volume : Measure ℝ) =
      ∑ i ∈ S, (f i).toLp 2 (volume : Measure ℝ) := by
    simpa only [F, L, SchwartzMap.toLpCLM_apply] using map_sum L f S
  rw [hL]
  let g (i : ι) := (f i).toLp 2 (volume : Measure ℝ)
  change ‖∑ i ∈ S, g i‖ ^ 2 ≤ ∑ i ∈ S, ∑ j ∈ S, ‖inner ℂ (g i) (g j)‖
  rw [← re_inner_self, sum_inner]
  simp only [inner_sum, Complex.re_sum]
  exact sum_le_sum (fun i _ => sum_le_sum (fun j _ => Complex.re_le_norm _))

private theorem inner_toLp_eq_integral (f g : 𝓢(ℝ, ℂ)) :
    inner ℂ (f.toLp 2 (volume : Measure ℝ)) (g.toLp 2 (volume : Measure ℝ)) =
      ∫ x, conj (f x) * g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 (volume : Measure ℝ), g.coeFn_toLp 2 (volume : Measure ℝ)] with x hf hg
  rw [hf, hg]
  exact RCLike.inner_apply' _ _

/-- The Gram integral of two weighted complex powers is a Fourier coefficient
of their common weight in logarithmic coordinates. -/
theorem log_power_gram {X : ℝ} (w : ℝ → ℝ)
    (z₁ z₂ : ℂ) (f₁ f₂ : 𝓢(ℝ, ℂ))
    (hzero : ∀ x ≤ 0, f₁ x = 0)
    (hf₁ : ∀ x > 0, f₁ x =
      (w (Real.log x - Real.log X) : ℂ) * Complex.exp ((z₁ - 1) * (Real.log x : ℂ)))
    (hf₂ : ∀ x > 0, f₂ x =
      (w (Real.log x - Real.log X) : ℂ) * Complex.exp ((z₂ - 1) * (Real.log x : ℂ))) :
    inner ℂ (f₁.toLp 2 (volume : Measure ℝ)) (f₂.toLp 2 (volume : Measure ℝ)) =
      Complex.exp ((conj z₁ + z₂ - 1) * (Real.log X : ℂ)) *
        (𝓕 (fun y : ℝ => (((w y)^2 * Real.exp ((z₁.re + z₂.re - 1) * y) : ℝ) : ℂ)))
          ((z₁.im - z₂.im)/(2*Real.pi)) := by
  let g (x : ℝ) := conj (f₁ x) * f₂ x
  let H (y : ℝ) := Real.exp y • g (Real.exp y)
  rw [inner_toLp_eq_integral]
  change (∫ x, g x) = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Ioi 0) (fun x hx => by simp [g, hzero x (le_of_not_gt hx)])]
  rw [← integral_comp_exp]
  change (∫ y, H y) = _
  rw [← integral_add_right_eq_self H (Real.log X), Real.fourier_eq', ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  have harg : y + Real.log X - Real.log X = y := by ring
  have hxy : 0 < Real.exp (y + Real.log X) := Real.exp_pos _
  simp only [H, g, hf₁ _ hxy, hf₂ _ hxy, Real.log_exp, harg, Complex.real_smul,
    Complex.ofReal_exp, map_mul, map_sub, map_one, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.ofReal_mul, Complex.ofReal_pow, smul_eq_mul]
  have hphase : -2 * Real.pi * inner ℝ y ((z₁.im-z₂.im)/(2*Real.pi)) =
      (z₂.im - z₁.im) * y := by
    change -2 * Real.pi * (((z₁.im-z₂.im)/(2*Real.pi)) * y) = _
    field_simp [Real.pi_ne_zero]
    ring
  have hExp : ((y + Real.log X : ℝ) : ℂ) +
      (conj z₁ - 1) * ((y + Real.log X : ℝ) : ℂ) +
      (z₂ - 1) * ((y + Real.log X : ℝ) : ℂ) =
    (conj z₁ + z₂ - 1) * (Real.log X : ℂ) +
      (((z₁.re + z₂.re - 1) * y : ℝ) : ℂ) +
      ((-2 * Real.pi * inner ℝ y ((z₁.im-z₂.im)/(2*Real.pi)) : ℝ) : ℂ) * Complex.I := by
    rw [hphase]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
        Complex.conj_re]
      ring
    · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_im,
        Complex.conj_im]
      ring
  have hExp' := congrArg Complex.exp hExp
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add] at hExp'
  simp only [Complex.ofReal_mul] at hExp'
  linear_combination ((w y : ℂ)^2) * hExp'

end GoldbachZeroStrip

open MeasureTheory Set

namespace GoldbachZeroStrip

private noncomputable def expWeight (g : ℝ → ℂ) (c : ℝ) (x : ℝ) :=
  Real.exp (c*x) • g x

private theorem deriv_expWeight {g : ℝ → ℂ} {x : ℝ}
    (hg : DifferentiableAt ℝ g x) (c : ℝ) :
    deriv (expWeight g c) x = Real.exp (c*x) • (c • g x + deriv g x) := by
  have he : HasDerivAt (fun x : ℝ => Real.exp (c*x)) (Real.exp (c*x)*c) x := by
    exact (Real.hasDerivAt_exp (c*x)).comp x (by simpa using (hasDerivAt_id x).const_mul c)
  change deriv ((fun y : ℝ => Real.exp (c*y)) • g) x = _
  simpa only [smul_add, mul_smul, add_comm] using (he.smul hg.hasDerivAt).deriv

private theorem two_deriv (g : ℝ → ℂ) :
    iteratedDeriv 2 g = deriv (deriv g) := by
  rw [show (2 : ℕ)=1+1 by decide, iteratedDeriv_succ, show (1 : ℕ)=0+1 by decide,
    iteratedDeriv_succ, iteratedDeriv_zero]

private theorem deriv_two_expWeight {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (c x : ℝ) :
    iteratedDeriv 2 (expWeight g c) x =
      Real.exp (c*x) • (c^2 • g x + (2*c) • deriv g x + iteratedDeriv 2 g x) := by
  have hdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdiff' : Differentiable ℝ (deriv g) := hg.differentiable_deriv_two
  have hd₁ : deriv (expWeight g c) = expWeight (fun z => c • g z + deriv g z) c :=
    funext fun z => deriv_expWeight (hdiff z) c
  have hd₂ : HasDerivAt (fun z => c • g z + deriv g z)
      (c • deriv g x + deriv (deriv g) x) x :=
    (hdiff x).hasDerivAt.const_smul c |>.add (hdiff' x).hasDerivAt
  rw [two_deriv, hd₁, deriv_expWeight hd₂.differentiableAt, hd₂.deriv, two_deriv]
  congr 1
  rw [smul_add, smul_smul, pow_two, show 2*c=c+c by ring, add_smul]
  abel

private theorem compact_iteratedDeriv {g : ℝ → ℂ} (h : HasCompactSupport g) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k g) := by
  induction k with
  | zero => exact h
  | succ k hk =>
      rw [iteratedDeriv_succ]
      exact hk.deriv

set_option maxHeartbeats 1200000 in
/-- Compact logarithmic weights have a common derivative-integral budget
after multiplying by (e^{cx}), uniformly for (|c|≤1). -/
theorem uniform_log_weight_budget {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    {D : ℝ} (hs : tsupport g ⊆ Icc (-D) D) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ c : ℝ, |c| ≤ 1 →
      let p := fun x : ℝ => Real.exp (c*x) • g x
      ContDiff ℝ 2 p ∧ (∀ k ≤ 2, Integrable (iteratedDeriv k p)) ∧
      (∫ y, ‖p y‖) + (4 * Real.pi ^ 2)⁻¹ * ∫ y, ‖iteratedDeriv 2 p y‖ ≤ A := by
  have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset isClosed_closure hs
  have hgi (k : ℕ) (hk : k ≤ 2) : Integrable (iteratedDeriv k g) :=
    (hg.continuous_iteratedDeriv k (by exact_mod_cast hk)).integrable_of_hasCompactSupport
      (compact_iteratedDeriv hgc k)
  let G (x : ℝ) := ‖g x‖ + 2 * ‖deriv g x‖ + ‖iteratedDeriv 2 g x‖
  have hg₂ : Integrable (iteratedDeriv 2 g) := hgi 2 le_rfl
  have hg₁ : Integrable (deriv g) := by simpa [iteratedDeriv_succ] using hgi 1 (by decide)
  have hg₀ : Integrable g := hgi 0 (by decide)
  have hGpos (x : ℝ) : 0 ≤ G x := by dsimp [G]; positivity
  have hGi : Integrable G := by
    exact (hg₀.norm.add (hg₁.norm.const_mul 2)).add hg₂.norm
  let A := (∫ x, Real.exp D * G x) + (4 * Real.pi ^ 2)⁻¹ * (∫ x, Real.exp D * G x)
  have hIpos : 0 ≤ ∫ x, Real.exp D * G x :=
    integral_nonneg fun x => mul_nonneg (Real.exp_nonneg _) (hGpos x)
  refine ⟨A, by unfold A; positivity, fun c hc => ?_⟩
  change ContDiff ℝ 2 (expWeight g c) ∧
    (∀ k ≤ 2, Integrable (iteratedDeriv k (expWeight g c))) ∧
    (∫ y, ‖expWeight g c y‖) +
      (4 * Real.pi ^ 2)⁻¹ * ∫ y, ‖iteratedDeriv 2 (expWeight g c) y‖ ≤ A
  have hpc : HasCompactSupport (expWeight g c) := by
    change HasCompactSupport ((fun y : ℝ => Real.exp (c*y)) • g)
    exact hgc.smul_left
  have hpd : ContDiff ℝ 2 (expWeight g c) :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).smul hg
  have hpi (k : ℕ) (hk : k ≤ 2) : Integrable (iteratedDeriv k (expWeight g c)) :=
    (hpd.continuous_iteratedDeriv k (by exact_mod_cast hk)).integrable_of_hasCompactSupport
      (compact_iteratedDeriv hpc k)
  refine ⟨hpd, hpi, ?_⟩
  have hexp (x : ℝ) (hx : x ∈ tsupport g) : Real.exp (c*x) ≤ Real.exp D := by
    have hxabs : |x| ≤ D := abs_le.mpr (hs hx)
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by rw [abs_mul]; nlinarith [abs_nonneg c, abs_nonneg x])
  have h0 (x : ℝ) : ‖expWeight g c x‖ ≤ Real.exp D * G x := by
    rw [expWeight, norm_smul, Real.norm_eq_abs, Real.abs_exp]
    by_cases hx : x ∈ tsupport g
    · have hbase : ‖g x‖ ≤ G x := by
        dsimp [G]
        linarith [norm_nonneg (deriv g x), norm_nonneg (iteratedDeriv 2 g x)]
      exact mul_le_mul (hexp x hx) hbase (norm_nonneg _) (Real.exp_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero, mul_zero]
      exact mul_nonneg (Real.exp_nonneg _) (hGpos x)
  have h2 (x : ℝ) : ‖iteratedDeriv 2 (expWeight g c) x‖ ≤ Real.exp D * G x := by
    rw [deriv_two_expWeight hg, norm_smul, Real.norm_eq_abs, Real.abs_exp]
    by_cases hx : x ∈ tsupport g
    · apply mul_le_mul (hexp x hx) _ (norm_nonneg _) (Real.exp_nonneg _)
      calc
        _ ≤ ‖c^2 • g x‖ + ‖(2*c) • deriv g x‖ + ‖iteratedDeriv 2 g x‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ G x := by
          unfold G
          simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg
            (by norm_num : (0:ℝ) ≤ 2)]
          apply add_le_add (add_le_add ?_ ?_) le_rfl
          · simpa only [one_mul] using
              mul_le_mul_of_nonneg_right (pow_le_one₀ (n := 2) (abs_nonneg c) hc) (norm_nonneg (g x))
          · exact mul_le_mul_of_nonneg_right (by linarith : 2*|c| ≤ 2) (norm_nonneg (deriv g x))
    · have hz₀ := image_eq_zero_of_notMem_tsupport hx
      have hx₁ : x ∉ tsupport (deriv g) := fun h => hx (tsupport_deriv_subset h)
      have hz₁ := image_eq_zero_of_notMem_tsupport hx₁
      have hz₂ := deriv_of_notMem_tsupport hx₁
      rw [hz₀, hz₁, two_deriv, hz₂]
      simp only [smul_zero, add_zero, norm_zero, mul_zero]
      exact mul_nonneg (Real.exp_nonneg _) (hGpos x)
  have hp₀ : Integrable (expWeight g c) := hpi 0 (by decide)
  have hp₂ : Integrable (iteratedDeriv 2 (expWeight g c)) := hpi 2 le_rfl
  have hBg : Integrable (fun x => Real.exp D * G x) := hGi.const_mul _
  exact add_le_add (integral_mono hp₀.norm hBg h0)
    (mul_le_mul_of_nonneg_left (integral_mono hp₂.norm hBg h2) (by positivity))

end GoldbachZeroStrip

open Set Filter
open scoped SchwartzMap ContDiff

namespace GoldbachZeroStrip

/-- A logarithmic cutoff extended by zero to the nonpositive reals. -/
noncomputable def weightedPower (X : ℝ) (w : ℝ → ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  if 0 < x then (w (Real.log x - Real.log X) : ℂ) *
    Complex.exp ((z-1) * (Real.log x : ℂ)) else 0

theorem weightedPower_compact {X D : ℝ} (hX : 0 < X) {w : ℝ → ℝ} (z : ℂ)
    (hs : tsupport w ⊆ Icc (-D) D) :
    HasCompactSupport (weightedPower X w z) := by
  have hsub : Function.support (weightedPower X w z) ⊆
      Icc (X * Real.exp (-D)) (X * Real.exp D) := by
    intro x hx
    have hne := Function.mem_support.mp hx
    have hxpos : 0 < x := by
      by_contra! h
      simp [weightedPower, h] at hne
    have hw : w (Real.log x - Real.log X) ≠ 0 := by
      intro h
      simp [weightedPower, hxpos, h] at hne
    obtain ⟨hlo, hhi⟩ := hs (subset_tsupport _ (Function.mem_support.mpr hw))
    have h₁ : 0 < X*Real.exp (-D) := by positivity
    have h₂ : 0 < X*Real.exp D := by positivity
    refine ⟨(Real.log_le_log_iff h₁ hxpos).mp ?_, (Real.log_le_log_iff hxpos h₂).mp ?_⟩
    · rw [Real.log_mul hX.ne' (Real.exp_pos _).ne', Real.log_exp]
      linarith
    · rw [Real.log_mul hX.ne' (Real.exp_pos _).ne', Real.log_exp]
      linarith
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal hsub isClosed_Icc)

theorem weightedPower_smooth {X D : ℝ} (hX : 0 < X) {w : ℝ → ℝ} (z : ℂ)
    (hw : ContDiff ℝ ∞ w) (hs : tsupport w ⊆ Icc (-D) D) :
    ContDiff ℝ ∞ (weightedPower X w z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hxpos : 0 < x
  · have hL : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.mpr hxpos.ne'
    have hW : ContDiffAt ℝ ∞ (fun y : ℝ => w (Real.log y - Real.log X)) x :=
      hw.contDiffAt.comp x (hL.sub contDiffAt_const)
    have hW' : ContDiffAt ℝ ∞ (fun y : ℝ => (w (Real.log y - Real.log X) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hW
    have hL' : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hL
    have hComplexExp : ContDiff ℂ ∞ Complex.exp := Complex.contDiff_exp
    have hExp : ContDiffAt ℝ ∞ Complex.exp ((z-1)*(Real.log x : ℂ)) :=
      hComplexExp.restrict_scalars ℝ |>.contDiffAt
    have hlocal := hW'.mul (hExp.comp x (contDiffAt_const.mul hL'))
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hxpos] with y hy
    simp [weightedPower, mem_Ioi.mp hy]
  · have hsmall : x < X * Real.exp (-D) :=
      (le_of_not_gt hxpos).trans_lt (by positivity)
    have hz : ContDiffAt ℝ ∞ (fun _ : ℝ => (0:ℂ)) x := contDiffAt_const
    apply hz.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hsmall] with y hy
    by_cases hypos : 0 < y
    · have h₁ : 0 < X * Real.exp (-D) := by positivity
      have hlog := (Real.log_lt_log_iff hypos h₁).mpr (mem_Iio.mp hy)
      rw [Real.log_mul hX.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
      have hnot : Real.log y - Real.log X ∉ tsupport w := by
        intro h
        have := (hs h).1
        linarith
      simp [weightedPower, hypos, image_eq_zero_of_notMem_tsupport hnot]
    · simp [weightedPower, hypos]

/-- The truncated complex power is represented by a Schwartz function. -/
noncomputable def weightedPowerSchwartz {X D : ℝ} (hX : 0 < X) {w : ℝ → ℝ} (z : ℂ)
    (hw : ContDiff ℝ ∞ w) (hs : tsupport w ⊆ Icc (-D) D) :
    𝓢(ℝ, ℂ) :=
  (weightedPower_compact hX z hs).toSchwartzMap (weightedPower_smooth hX z hw hs)

@[simp] theorem weightedPowerSchwartz_apply {X D : ℝ} (hX : 0 < X) {w : ℝ → ℝ} (z : ℂ)
    (hw : ContDiff ℝ ∞ w) (hs : tsupport w ⊆ Icc (-D) D) (x : ℝ) :
    weightedPowerSchwartz hX z hw hs x = weightedPower X w z x := rfl

end GoldbachZeroStrip


end

namespace GoldbachZeroStrip

open Finset MeasureTheory Set
open scoped SchwartzMap FourierTransform ComplexInnerProductSpace ComplexConjugate ContDiff

private theorem kernel_amplitude_le {ι : Type*} (S : Finset ι) (a : ι → ℝ) (k : ι → ι → ℝ)
    (hk : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ k i j)
    (hs : ∀ i ∈ S, ∀ j ∈ S, k i j = k j i) :
    (∑ i ∈ S, ∑ j ∈ S, k i j * (a i * a j)) ≤
      ∑ i ∈ S, (∑ j ∈ S, k i j) * (a i)^2 := by
  have hswap : (∑ i ∈ S, ∑ j ∈ S, k i j * (a j)^2) =
      ∑ i ∈ S, ∑ j ∈ S, k i j * (a i)^2 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [hs j hj i hi]
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, (k i j * (a i)^2 + k i j * (a j)^2) / 2 := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      have h := mul_nonneg (hk i hi j hj) (sq_nonneg (a i - a j))
      linarith only [show 0 ≤ k i j * (a i)^2 + k i j * (a j)^2 -
        2 * (k i j * (a i * a j)) from by convert h using 1; ring]
    _ = _ := by
      simp_rw [← sum_div, sum_add_distrib]
      rw [hswap]
      simp only [← sum_mul]
      ring

private theorem weighted_gram_row_bound {ι : Type*} (S : Finset ι) (height a : ι → ℝ)
    (f : ι → 𝓢(ℝ, ℂ)) {B A : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hunit : ∀ y : ℝ, ((S.filter (fun i => y ≤ height i ∧ height i ≤ y + 1)).card : ℝ) ≤ B)
    (hgram : ∀ i ∈ S, ∀ j ∈ S,
      ‖inner ℂ ((f i).toLp 2 (volume : Measure ℝ)) ((f j).toLp 2 (volume : Measure ℝ))‖ ≤
        (A / (1 + (height j - height i)^2)) * (a i * a j)) :
    (∫ ξ : ℝ, ‖∑ j ∈ S, (𝓕 (f j)) ξ‖ ^ 2) ≤ (A * (8 * B)) * ∑ j ∈ S, (a j)^2 := by
  let k (i j : ι) : ℝ := A / (1 + (height j - height i)^2)
  have hrow (i : ι) : (∑ j ∈ S, k i j) ≤ A * (8*B) := by
    calc
      _ = A * (∑ j ∈ S, 1 / (1 + (height j - height i)^2)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        exact div_eq_mul_one_div _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (inverse_square_row_le S height hB hunit (height i)) hA
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, k i j * (a i * a j) :=
      (fourier_energy_le S f).trans (sum_le_sum (fun i hi => sum_le_sum (fun j hj => hgram i hi j hj)))
    _ ≤ ∑ i ∈ S, (∑ j ∈ S, k i j) * (a i)^2 :=
      kernel_amplitude_le S a k (fun i _ j _ => by dsimp only [k]; positivity)
        (fun i _ j _ => by dsimp only [k]; congr 2; ring)
    _ ≤ _ := by
      rw [mul_sum]
      exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))

theorem compact_weighted_zero_energy {D : ℝ} {w : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hs : tsupport w ⊆ Icc (-D) D) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {ι : Type} (S : Finset ι) (z : ι → ℂ) (c : ι → ℂ)
      {X B : ℝ} (hX : 1 ≤ X), 0 ≤ B →
      (∀ j ∈ S, 0 ≤ (z j).re ∧ (z j).re ≤ 1) →
      (∀ y : ℝ, ((S.filter (fun j => y ≤ -(z j).im/(2*Real.pi) ∧
        -(z j).im/(2*Real.pi) ≤ y + 1)).card : ℝ) ≤ B) →
      (∫ ξ : ℝ, ‖∑ j ∈ S, c j * (𝓕 (weightedPowerSchwartz
        (show 0 < X by linarith) (z j) hw hs)) ξ‖ ^ 2) ≤
        (A * (8*B)) * (∑ j ∈ S, ‖c j‖^2 * X^(2*(z j).re - 1)) := by
  let g (y : ℝ) := (w y : ℂ)^2
  have hw₂ : ContDiff ℝ 2 w := hw.of_le (by norm_num)
  have hg : ContDiff ℝ 2 g := (Complex.ofRealCLM.contDiff.comp hw₂).pow 2
  have hgS : tsupport g ⊆ Icc (-D) D :=
    (closure_mono (show Function.support g ⊆ Function.support w from fun x hx =>
      Function.mem_support.mpr fun h => (Function.mem_support.mp hx) (by simp [g,h]))).trans hs
  obtain ⟨A,hA,budget⟩ := uniform_log_weight_budget hg hgS
  refine ⟨A,hA,?_⟩
  intro ι S z c X B hX hB hz hunit
  have hXp : 0 < X := by linarith
  let height (j : ι) := -(z j).im/(2*Real.pi)
  let amp (j : ι) := ‖c j‖ * X^((z j).re - 1/2)
  let f (j : ι) := weightedPowerSchwartz hXp (z j) hw hs
  let F (j : ι) := c j • f j
  have hLp (j : ι) : (F j).toLp 2 (volume : Measure ℝ) =
      c j • (f j).toLp 2 (volume : Measure ℝ) := by
    simpa only [F, SchwartzMap.toLpCLM_apply] using
      map_smul (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)) (c j) (f j)
  have hrow := weighted_gram_row_bound S height amp F hB hA hunit ?_
  · have he (j : ι) : (amp j)^2 = ‖c j‖^2 * X^(2*(z j).re - 1) := by
      dsimp only [amp]
      rw [mul_pow, ← Real.rpow_mul_natCast hXp.le]
      congr 2
      push_cast
      ring
    simpa only [F, f, FourierTransform.fourier_smul, smul_apply, smul_eq_mul, he] using hrow
  · intro i hi j hj
    let σ := (z i).re + (z j).re - 1
    let p (y : ℝ) := Real.exp (σ*y) • g y
    have hσ : |σ| ≤ 1 := by dsimp only [σ]; exact abs_le.mpr ⟨by linarith [(hz i hi).1, (hz j hj).1], by linarith [(hz i hi).2, (hz j hj).2]⟩
    obtain ⟨hd, hI, hb⟩ := budget σ hσ
    have heq : (fun y : ℝ => (((w y)^2 * Real.exp (σ*y) : ℝ) : ℂ)) = p := by
      funext y
      simp only [p,g, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow]
      exact mul_comm ..
    have hθ : ((z i).im - (z j).im)/(2*Real.pi) = height j - height i := by
      dsimp only [height]
      ring
    have hgij := log_power_gram (X := X) w (z i) (z j) (f i) (f j)
      (fun x hx => by simp [f, weightedPower, not_lt_of_ge hx])
      (fun x hx => by simp [f, weightedPower, hx])
      (fun x hx => by simp [f, weightedPower, hx])
    rw [show ((z i).re + (z j).re - 1) = σ from rfl, heq, hθ] at hgij
    have hFourier := (Real.one_add_sq_mul_norm_fourier_le hd hI (height j-height i)).trans hb
    have hp : ‖(𝓕 p) (height j-height i)‖ ≤ A/(1+(height j-height i)^2) := by
      apply (le_div_iff₀ (by positivity)).mpr
      rwa [mul_comm]
    have hNorm : ‖Complex.exp ((conj (z i) + z j - 1) * (Real.log X : ℂ))‖ =
        X^((z i).re-1/2) * X^((z j).re-1/2) := by
      rw [Complex.norm_exp, ← Real.rpow_add hXp, Real.rpow_def_of_pos hXp]
      congr 1
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re]
      ring
    rw [hLp, hLp, inner_smul_left, inner_smul_right, hgij]
    simp only [norm_mul, RCLike.norm_conj, hNorm]
    have h := mul_le_mul_of_nonneg_left hp
      (by positivity : 0 ≤ ‖c i‖ * (‖c j‖ * (X ^ ((z i).re - 1 / 2) * X ^ ((z j).re - 1 / 2))))
    convert h using 1 <;> try dsimp only [amp]
    all_goals ring

end GoldbachZeroStrip
end

section

namespace GoldbachZeroStrip

open Complex Finset GoldbachSmoothMellin GoldbachSmoothWindow GoldbachTwistedMellin MeasureTheory Set
open scoped SchwartzMap FourierTransform ComplexInnerProductSpace ContDiff

noncomputable def logWindow (y : ℝ) : ℝ := GoldbachSmoothWindow.weight (Real.exp y)

theorem logWindow_smooth : ContDiff ℝ ∞ logWindow := by
  have hw : ContDiff ℝ ∞ (GoldbachSmoothWindow.bump : ℝ → ℝ) :=
    GoldbachSmoothWindow.bump.contDiff
  exact hw.comp Real.contDiff_exp

theorem logWindow_support : tsupport logWindow ⊆ Icc (-1 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  by_contra h
  change ¬ ((-1 : ℝ) ≤ y ∧ y ≤ 1) at h
  have hn := Function.mem_support.mp hy
  apply hn
  apply GoldbachSmoothWindow.weight_zero
  have ht := not_and_or.mp h
  rcases ht with h | h
  · left
    have hy0 : y ≤ 0 := by linarith
    exact (Real.exp_le_one_iff.mpr hy0).trans (by norm_num)
  · right
    linarith [Real.add_one_le_exp y]

private theorem logWindow_scaled {X x : ℝ} (hX : 0 < X) (hx : 0 < x) :
    logWindow (Real.log x - Real.log X) = scaledWeight X x := by
  unfold logWindow scaledWeight
  rw [Real.exp_sub, Real.exp_log hx, Real.exp_log hX]

noncomputable def logWindowSchwartz {X : ℝ} (hX : 0 < X) (s : ℂ) : 𝓢(ℝ, ℂ) :=
  weightedPowerSchwartz hX s logWindow_smooth logWindow_support

theorem smooth_mellin_eq_fourier {X : ℝ} (hX : 0 < X) (s : ℂ) (β : ℝ) :
    smoothTransform X (2*X) β (scaledWeight X) s =
      (𝓕 (logWindowSchwartz hX s)) (-(β/(2*Real.pi))) := by
  have hsupport (x : ℝ) (hx : x ∉ Icc X (2*X)) : logWindowSchwartz hX s x = 0 := by
    by_cases hx0 : 0 < x
    · have hn : x < X ∨ 2*X < x := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        exact hx
      have hz : scaledWeight X x = 0 := by
        unfold scaledWeight
        apply GoldbachSmoothWindow.weight_zero
        rcases hn with h | h
        · exact Or.inl ((div_le_one hX).mpr h.le |>.trans (by norm_num))
        · exact Or.inr ((le_div_iff₀ hX).mpr (by linarith))
      simp [logWindowSchwartz, weightedPower, hx0, logWindow_scaled hX hx0, hz]
    · simp [logWindowSchwartz, weightedPower, hx0]
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Icc X (2*X)) (fun x hx => by simp [hsupport x hx])]
  rw [integral_Icc_eq_integral_Ioc, smoothTransform, intervalIntegral.integral_of_le (by linarith : X ≤ 2*X)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hx0 : 0 < x := hX.trans hx.1
  have hexp : -2 * Real.pi * inner ℝ x (-(β/(2*Real.pi))) = β*x := by
    change -2 * Real.pi * ((-(β/(2*Real.pi)))*x) = _
    field_simp [Real.pi_ne_zero]
  simp only [hexp, logWindowSchwartz, weightedPowerSchwartz_apply, weightedPower, hx0, ite_true,
    logWindow_scaled hX hx0, density, phase, smul_eq_mul]
  have hPow : ((x:ℝ):ℂ) ^ (s-1) =
      Complex.exp ((s-1) * (Real.log x : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx0.ne'), ← Complex.ofReal_log hx0.le]
    congr 1
    ring
  rw [hPow]
  ring

theorem smooth_mellin_band_energy {X R : ℝ} (hX : 1 ≤ X) {ι : Type}
    (S : Finset ι) (z : ι → ℂ) (c : ι → ℂ) :
    (∫ β in Icc (-R) R, ‖∑ j ∈ S, c j * smoothTransform X (2*X) β (scaledWeight X) (z j)‖ ^ 2) ≤
      (2*Real.pi) * (∫ ξ : ℝ, ‖∑ j ∈ S, c j *
        (𝓕 (logWindowSchwartz (zero_lt_one.trans_le hX) (z j))) ξ‖ ^ 2) := by
  let F : 𝓢(ℝ, ℂ) := ∑ j ∈ S, c j • logWindowSchwartz (by linarith : 0 < X) (z j)
  let G (ξ : ℝ) : ℝ := ‖(𝓕 F) ξ‖ ^ 2
  let a : ℝ := -(1/(2*Real.pi))
  have ha : a ≠ 0 := neg_ne_zero.mpr (one_div_pos.mpr (by positivity)).ne'
  have aInv : |a⁻¹| = 2*Real.pi := by
    simp only [a, inv_neg, inv_div, div_one, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
  have eqF (ξ : ℝ) : (𝓕 F) ξ = ∑ j ∈ S, c j *
      (𝓕 (logWindowSchwartz (by linarith : 0 < X) (z j))) ξ := by
    simp only [F, FourierTransform.fourier_sum, FourierTransform.fourier_smul,
      sum_apply, smul_apply, smul_eq_mul]
  have hI : Integrable G := (memLp_two_iff_integrable_sq_norm
    (𝓕 F : 𝓢(ℝ, ℂ)).continuous.aestronglyMeasurable).mp ((𝓕 F : 𝓢(ℝ, ℂ)).memLp 2)
  have h₁ : ∀ β : ℝ, ‖∑ j ∈ S, c j * smoothTransform X (2*X) β (scaledWeight X) (z j)‖ ^ 2 =
      G (a * β) := by
    intro β
    simp_rw [smooth_mellin_eq_fourier (by linarith : 0 < X), G, eqF]
    have he : -(β/(2*Real.pi)) = a*β := by dsimp only [a]; ring
    rw [he]
  simp_rw [h₁, ← eqF]
  calc
    _ ≤ ∫ β, G (a*β) :=
      setIntegral_le_integral (hI.comp_mul_left' ha) (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    _ = _ := by simp only [Measure.integral_comp_mul_left G a, aInv, smul_eq_mul, G]

theorem smooth_mellin_weighted_energy :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {ι : Type} (S : Finset ι) (z : ι → ℂ) (c : ι → ℂ)
      {X R B : ℝ} (_hX : 1 ≤ X), 0 ≤ B →
      (∀ j ∈ S, 0 ≤ (z j).re ∧ (z j).re ≤ 1) →
      (∀ y : ℝ, ((S.filter (fun j => y ≤ -(z j).im/(2*Real.pi) ∧
        -(z j).im/(2*Real.pi) ≤ y + 1)).card : ℝ) ≤ B) →
      (∫ β in Icc (-R) R, ‖∑ j ∈ S, c j * smoothTransform X (2*X) β (scaledWeight X) (z j)‖ ^ 2) ≤
        (A * B) * (∑ j ∈ S, ‖c j‖^2 * X^(2*(z j).re - 1)) := by
  obtain ⟨A,hA,hE⟩ := compact_weighted_zero_energy logWindow_smooth logWindow_support
  refine ⟨2*Real.pi*A*8, by positivity, ?_⟩
  intro ι S z c X R B hX hB hz hunit
  apply (smooth_mellin_band_energy hX S z c (R := R)).trans
  exact (mul_le_mul_of_nonneg_left (hE S z c hX hB hz hunit) (by positivity)).trans_eq (by ring)

end GoldbachZeroStrip
end

section
section

open Finset Set GoldbachTwistedMellin

namespace GoldbachZeroStrip

private theorem sum_Ico_differences (w : ℕ → ℝ) {l r : ℕ} (h : l ≤ r) :
    ∑ k ∈ Finset.Ico l r, (w k - w (k+1)) = w l - w r := by
  induction r, h using Nat.le_induction with
  | base => simp
  | succ r hr ih =>
      rw [sum_Ico_succ_top hr, ih]
      ring

/-- Weighted nested tapers interpolate exactly between the sampled weights on
each unit interval. Their coefficients are the backward Abel differences. -/
theorem taper_sum_on_cell (w : ℕ → ℝ) {a n b : ℕ} (han : a+1 ≤ n) (hnb : n ≤ b)
    (hb : w (b+1) = 0) {x : ℝ} (hx : x ∈ Icc (n:ℝ) ((n:ℝ)+1)) :
    (∑ k ∈ Finset.Ico (a+1) (b+1), (w k - w (k+1))*taper (a:ℝ) (k:ℝ) x) =
      (((n:ℝ)+1)-x)*w n + (x-(n:ℝ))*w (n+1) := by
  let f (k : ℕ) := (w k - w (k+1))*taper (a:ℝ) (k:ℝ) x
  change (∑ k ∈ Finset.Ico (a+1) (b+1), f k) = _
  have hsplit := sum_Ico_consecutive f han (show n ≤ b+1 by omega)
  have hsplit' := sum_Ico_consecutive f (Nat.le_succ n) (Nat.succ_le_succ hnb)
  rw [← hsplit, ← hsplit', Nat.Ico_succ_singleton, sum_singleton]
  have hz : (∑ k ∈ Finset.Ico (a+1) n, f k) = 0 := by
    apply sum_eq_zero
    intro k hk
    have hk' : (k:ℝ)+1 ≤ n := by exact_mod_cast (mem_Ico.mp hk).2
    dsimp [f]
    rw [taper_right (hk'.trans hx.1), mul_zero]
  have hn : f n = (w n - w (n+1))*(((n:ℝ)+1)-x) := by
    dsimp [f]
    rw [taper_fall (by exact_mod_cast han) hx]
  have htail : (∑ k ∈ Finset.Ico (n+1) (b+1), f k) = w (n+1) := by
    calc
      _ = ∑ k ∈ Finset.Ico (n+1) (b+1), (w k - w (k+1)) := by
        apply sum_congr rfl
        intro k hk
        obtain ⟨hlo,_⟩ := mem_Ico.mp hk
        have hlo' : (n:ℝ)+1 ≤ k := by exact_mod_cast hlo
        dsimp [f]
        rw [taper_flat ⟨(by exact_mod_cast han : (a:ℝ)+1 ≤ n).trans hx.1,
          hx.2.trans hlo'⟩, mul_one]
      _ = _ := by rw [sum_Ico_differences w (Nat.succ_le_succ hnb), hb, sub_zero]
  rw [hz, hn, htail]
  ring

private theorem second_diff_le (w : ℝ → ℝ) (hw : ContDiff ℝ 2 w) {M : ℝ}
    (hM : ∀ x, ‖deriv (deriv w) x‖ ≤ M) {d : ℝ} (hd : 0 ≤ d) (x : ℝ) :
    ‖w (x+d+d) - w (x+d) - (w (x+d) - w x)‖ ≤ M * d^2 := by
  have hdiff : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hdiff' : Differentiable ℝ (deriv w) := hw.differentiable_deriv_two
  let g (t : ℝ) := w (t+d) - w t
  have hg (t : ℝ) : HasDerivAt g (deriv w (t+d) - deriv w t) t := by
    change HasDerivAt ((w ∘ fun y : ℝ => y+d) - w)
      (deriv w (t+d) - deriv w t) t
    have hz : HasDerivAt (w ∘ fun y : ℝ => y+d) (deriv w (t+d)) t := by
      simpa only [id_eq, mul_one] using
        (hdiff (t+d)).hasDerivAt.comp t ((hasDerivAt_id t).add_const d)
    exact hz.sub (hdiff t).hasDerivAt
  have hdif (t : ℝ) : ‖deriv w (t+d) - deriv w t‖ ≤ M*d := by
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
      (fun u _ => hdiff' u) (fun u _ => hM u) convex_univ (x := t) (y := t+d) trivial trivial
    simpa only [add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg hd] using hh
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
    (fun t _ => (hg t).differentiableAt) (fun t _ => by rw [(hg t).deriv]; exact hdif t)
    convex_univ (x := x) (y := x+d) trivial trivial
  calc
    _ = ‖g (x+d) - g x‖ := rfl
    _ ≤ (M*d)*‖x+d-x‖ := hh
    _ = M*d^2 := by rw [add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg hd]; ring

/-- Adjacent slopes of a sampled weight have total variation bounded by the
sample count times the sup norm of its second derivative at mesh scale. -/
theorem sampled_slope_variation (w : ℝ → ℝ) (hw : ContDiff ℝ 2 w) {M : ℝ}
    (hM : ∀ x, ‖deriv (deriv w) x‖ ≤ M) {X : ℝ} (hX : 0 < X) (J : Finset ℕ) :
    (∑ k ∈ J, ‖w (((k:ℝ)+2)/X) - w (((k:ℝ)+1)/X) -
      (w (((k:ℝ)+1)/X) - w ((k:ℝ)/X))‖) ≤ (J.card : ℝ) * (M/X^2) := by
  calc
    _ ≤ ∑ _k ∈ J, M/X^2 := by
      apply sum_le_sum
      intro k hk
      have h₁ : (k:ℝ)/X + 1/X = ((k:ℝ)+1)/X := by rw [add_div]
      have h₂ : (k:ℝ)/X + 1/X + 1/X = ((k:ℝ)+2)/X := by field_simp; ring
      have h := second_diff_le w hw hM (one_div_nonneg.mpr hX.le) ((k:ℝ)/X)
      rw [h₂, h₁] at h
      simpa only [div_pow, one_pow, mul_one_div] using h
    _ = _ := by simp [nsmul_eq_mul]

end GoldbachZeroStrip
end
section

open MeasureTheory Finset
open scoped Interval

namespace GoldbachZeroStrip

/-- The only interior contributions of the cell boundaries are jumps from
one extended local formula to the next. -/
theorem sum_cell_boundary {a b : ℕ} (hab : a < b) (F : ℕ → ℕ → ℂ) :
    (∑ n ∈ Ico a b, (F n (n+1) - F n n)) =
      F (b-1) b - F a a + ∑ n ∈ Ico (a+1) b, (F (n-1) n - F n n) := by
  have h : a+1 ≤ b := by omega
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b h ih =>
      have hab' : a < b := by omega
      have h₀ : a ≤ b := by omega
      rw [sum_Ico_succ_top h₀, sum_Ico_succ_top h,
        Nat.add_sub_cancel, ih hab']
      abel

theorem norm_sum_cell_boundary_le_jumps {a b : ℕ} (hab : a < b) (F : ℕ → ℕ → ℂ)
    (hleft : F a a = 0) (hright : F (b-1) b = 0) :
    ‖∑ n ∈ Ico a b, (F n (n+1) - F n n)‖ ≤
      ∑ n ∈ Ico (a+1) b, ‖F (n-1) n - F n n‖ := by
  rw [sum_cell_boundary hab F, hleft, hright, sub_self, zero_add]
  exact norm_sum_le _ _

end GoldbachZeroStrip
end
section

open Filter
open scoped Topology

namespace GoldbachZeroStrip

/-- A bounded sequence satisfying a forward recurrence with contraction at
most one half is bounded by twice the recurrence's constant term. -/
theorem half_recurrence_bound {u : ℕ → ℝ} {C M : ℝ} (hC : 0 ≤ C)
    (hB : ∀ n, u n ≤ M) (hrec : ∀ n, u n ≤ C + u (n+1)/2) (n : ℕ) :
    u n ≤ 2*C := by
  have hiter (k : ℕ) : ∀ m, u m ≤ 2*C + M*(1/2 : ℝ)^k := by
    induction k with
    | zero =>
      intro m
      norm_num
      linarith [hB m]
    | succ k ih =>
      intro m
      calc
        _ ≤ C + u (m+1)/2 := hrec m
        _ ≤ C + (2*C + M*(1/2 : ℝ)^k)/2 := by linarith only [ih (m+1)]
        _ = _ := by rw [pow_succ]; ring
  have ht : Tendsto (fun k : ℕ => 2*C + M*(1/2 : ℝ)^k) atTop (nhds (2*C)) := by
    simpa only [mul_zero, add_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)).const_mul M).const_add (2*C)
  exact ge_of_tendsto' ht (fun k => hiter k n)

/-- Two consecutive Mellin recurrences propagate the derivative variation
bound to quadratic decay in the imaginary part. The sequences are the
transforms normalized at the right endpoint of the weight support. -/
theorem twice_contracted_decay {u v : ℕ → ℝ} {R t J M N : ℝ}
    (hR : 0 ≤ R) (ht : 0 < t) (hJ : 0 ≤ J)
    (hu : ∀ n, u n ≤ M) (hv : ∀ n, v n ≤ N)
    (hvRec : ∀ n, v n ≤ J/t + v (n+1)/2)
    (huRec : ∀ n, u n ≤ (R/t)*v (n+1) + u (n+1)/2) :
    u 0 ≤ 4*R*J/t^2 := by
  have hV (n : ℕ) : v n ≤ 2*(J/t) :=
    half_recurrence_bound (div_nonneg hJ ht.le) hv hvRec n
  have hU (n : ℕ) : u n ≤ ((R/t)*(2*(J/t))) + u (n+1)/2 :=
    (huRec n).trans (add_le_add (mul_le_mul_of_nonneg_left
      (hV (n+1)) (div_nonneg hR ht.le)) le_rfl)
  have h := half_recurrence_bound (by positivity : 0 ≤ (R/t)*(2*(J/t))) hu hU 0
  exact h.trans_eq (by field_simp; ring)


/-- Normalized Mellin recurrences imply a uniform off-stationary tail.
The support endpoint is R, t is the absolute ordinate, J bounds the
variation term, and the twist satisfies 2R|β|≤t. -/
theorem mellin_tail_of_recurrences (P V : ℂ → ℂ) (E : ℕ → ℂ)
    (s : ℂ) {R β J U W : ℝ} (hR : 0 < R) (ht : 0 < |s.im|) (hJ : 0 ≤ J)
    (hβ : 2 * R * |β| ≤ |s.im|) :
    let z (n : ℕ) := s + (n:ℂ)
    let A (n : ℕ) := R^(z n).re
    (∀ n : ℕ, ‖P (z n)‖ ≤ U*A n) →
    (∀ n : ℕ, ‖V (z n)‖ ≤ W*A n) →
    (∀ n : ℕ, ‖E n‖ ≤ J*A n) →
    (∀ n : ℕ, z n * P (z n) = -V (z (n+1)) - ((β:ℂ)*Complex.I)*P (z (n+1))) →
    (∀ n : ℕ, z n * V (z n) = E n - ((β:ℂ)*Complex.I)*V (z (n+1))) →
    ‖P s‖ ≤ R^s.re * (4*R*J/|s.im|^2) := by
  dsimp only
  intro hP hV hE hPr hVr
  let z (n : ℕ) := s + (n:ℂ)
  let A (n : ℕ) := R^(z n).re
  let t := |s.im|
  let u (n : ℕ) := ‖P (z n)‖/A n
  let v (n : ℕ) := ‖V (z n)‖/A n
  have hA (n : ℕ) : 0 < A n := Real.rpow_pos_of_pos hR _
  have hAs (n : ℕ) : A (n+1) = R * A n := by
    have hz : (z (n+1)).re = (z n).re+1 := by simp [z, add_assoc]
    dsimp only [A]
    rw [hz, Real.rpow_add_one hR.ne', mul_comm]
  have hUn (n : ℕ) : 0 ≤ u n := div_nonneg (norm_nonneg _) (hA n).le
  have hVn (n : ℕ) : 0 ≤ v n := div_nonneg (norm_nonneg _) (hA n).le
  have hUa (n : ℕ) : u n * A n = ‖P (z n)‖ := by
    dsimp only [u]
    exact div_mul_cancel₀ _ (hA n).ne'
  have hVa (n : ℕ) : v n * A n = ‖V (z n)‖ := by
    dsimp only [v]
    exact div_mul_cancel₀ _ (hA n).ne'
  have hAngle (n : ℕ) : t ≤ ‖z n‖ := by simpa [z,t] using Complex.abs_im_le_norm (z n)
  have hfreq : ‖(β:ℂ)*Complex.I‖ = |β| := by simp [Complex.norm_real,Real.norm_eq_abs]
  have hsmall : |β| * R ≤ t/2 := by dsimp only [t]; nlinarith only [hβ]
  have huRec (n : ℕ) : u n ≤ (R/t)*v (n+1) + u (n+1)/2 := by
    have h₁ : t*‖P (z n)‖ ≤ ‖V (z (n+1))‖ + |β| * ‖P (z (n+1))‖ := by
      apply (mul_le_mul_of_nonneg_right (hAngle n) (norm_nonneg _)).trans
      rw [← norm_mul, hPr n]
      exact (norm_sub_le _ _).trans_eq (by rw [norm_neg,norm_mul,hfreq])
    rw [← hUa n, ← hVa (n+1), ← hUa (n+1), hAs] at h₁
    have h₂ : t*(u n) ≤ R*v (n+1)+(|β| * R)*u (n+1) := by
      apply le_of_mul_le_mul_right ?_ (hA n)
      convert h₁ using 1 <;> ring
    have hs := h₂.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hsmall (hUn (n+1))))
    apply le_of_mul_le_mul_right ?_ ht
    convert hs using 1
    · ring
    · field_simp [show t ≠ 0 from ht.ne']
      ring
  have hvRec (n : ℕ) : v n ≤ J/t + v (n+1)/2 := by
    have h₁ : t*‖V (z n)‖ ≤ J*A n + |β| * ‖V (z (n+1))‖ := by
      apply (mul_le_mul_of_nonneg_right (hAngle n) (norm_nonneg _)).trans
      rw [← norm_mul, hVr n]
      exact (norm_sub_le _ _).trans (add_le_add (hE n) (by rw [norm_mul,hfreq]))
    rw [← hVa n, ← hVa (n+1), hAs] at h₁
    have h₂ : t*(v n) ≤ J+(|β| * R)*v (n+1) := by
      apply le_of_mul_le_mul_right ?_ (hA n)
      convert h₁ using 1 <;> ring
    have hs := h₂.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hsmall (hVn (n+1))))
    apply le_of_mul_le_mul_right ?_ ht
    convert hs using 1
    · ring
    · field_simp [show t ≠ 0 from ht.ne']
      ring
  have hbU (n) : u n ≤ U := (div_le_iff₀ (hA n)).mpr (hP n)
  have hbV (n) : v n ≤ W := (div_le_iff₀ (hA n)).mpr (hV n)
  have hu := twice_contracted_decay hR.le ht hJ hbU hbV hvRec huRec
  have hb := (div_le_iff₀ (hA 0)).mp hu
  simpa [u,z,A,t,mul_comm] using hb

end GoldbachZeroStrip
end
section

open MeasureTheory Finset Complex GoldbachTwistedMellin
open scoped Interval

namespace GoldbachZeroStrip

private theorem sum_differences_complex (w : ℕ → ℝ) {l r : ℕ} (h : l ≤ r) :
    ∑ k ∈ Ico l r, ((w k - w (k+1) : ℝ) : ℂ) = ((w l - w r : ℝ) : ℂ) := by
  induction r, h using Nat.le_induction with
  | base => simp
  | succ r hr ih =>
      rw [sum_Ico_succ_top hr, ih]
      push_cast
      ring

/-- Mellin transform of the weighted sum of nested tapers. -/
noncomputable def weightedTaperTransform (a b : ℕ) (w : ℕ → ℝ) (β : ℝ) (s : ℂ) : ℂ :=
  ∑ k ∈ Ico (a+1) (b+1), ((w k - w (k+1) : ℝ) : ℂ)*transform (a:ℝ) (k:ℝ) β s

/-- Mellin transform of a step profile with cell coefficients d. -/
noncomputable def stepTransform (a b : ℕ) (d : ℕ → ℝ) (β : ℝ) (s : ℂ) : ℂ :=
  ∑ k ∈ Ico (a+1) (b+1), (d k:ℂ)*(∫ x in (k:ℝ)..(k:ℝ)+1, density β s x)

/-- The weighted taper recurrence gives the transform of its step derivative,
with the oscillatory twist kept as a shifted higher real part. -/
theorem mul_weightedTaperTransform {a b : ℕ} (ha : 0 < a) (hab : a+1 ≤ b+1)
    (w : ℕ → ℝ) (hL : w (a+1) = 0) (hR : w (b+1) = 0)
    (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    s*weightedTaperTransform a b w β s =
      -stepTransform a b (fun k => w (k+1)-w k) β (s+1) -
        ((β:ℂ)*I)*weightedTaperTransform a b w β (s+1) := by
  let J := Ico (a+1) (b+1)
  let U (k : ℕ) := ((w k-w (k+1):ℝ):ℂ)
  let H (k : ℕ) := ∫ x in (k:ℝ)..(k:ℝ)+1, density β (s+1) x
  let T (k : ℕ) (z : ℂ) := transform (a:ℝ) (k:ℝ) β z
  have hsum : ∑ k ∈ J, U k = 0 := by
    dsimp only [J, U]
    rw [sum_differences_complex w hab, hL, hR, sub_self, ofReal_zero]
  have hRec (k : ℕ) (hk : k ∈ J) :
      s*T k s = H k - H a - ((β:ℂ)*I)*T k (s+1) :=
    transform_recurrence (by exact_mod_cast ha) (by exact_mod_cast (mem_Ico.mp hk).1) β hs
  have hstep : stepTransform a b (fun k => w (k+1)-w k) β (s+1) =
      -(∑ k ∈ J, U k*H k) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro k hk
    simp only [U,H,ofReal_sub]
    ring
  change s*(∑ k ∈ J, U k*T k s) =
    -stepTransform a b (fun k => w (k+1)-w k) β (s+1) - ((β:ℂ)*I)*(∑ k ∈ J, U k*T k (s+1))
  rw [hstep, neg_neg, mul_sum]
  calc
    _ = ∑ k ∈ J, U k*(H k-H a-((β:ℂ)*I)*T k (s+1)) := by
      apply sum_congr rfl
      intro k hk
      rw [← hRec k hk]
      ring
    _ = (∑ k ∈ J, U k*H k) - (∑ k ∈ J, U k)*H a -
        ((β:ℂ)*I)*(∑ k ∈ J, U k*T k (s+1)) := by
      simp only [sum_sub_distrib, mul_sub, mul_sum, sum_mul]
      congr 1
      apply sum_congr rfl
      intro k hk
      ring
    _ = _ := by rw [hsum,zero_mul,sub_zero]

private theorem mul_integral_density {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r)
    (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    s*(∫ x in l..r, density β s x) =
      density β (s+1) r - density β (s+1) l -
        ((β:ℂ)*I)*(∫ x in l..r, density β (s+1) x) := by
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt (density β (s+1)) (s*density β s x+((β:ℂ)*I)*density β (s+1) x) x := by
    have hne : s ≠ 0 := fun h => by simp [h] at hs
    have h := (phase_deriv β x).mul (hasDerivAt_ofReal_cpow_const hx.ne' hne)
    convert h using 1
    · funext y
      exact density_succ β s y
    · rw [density_succ]
      unfold density
      ring
  have h₀ := (integral_density hl hlr β s).const_mul s
  have h₁ := (integral_density hl hlr β (s+1)).const_mul ((β:ℂ)*I)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := density β (s+1)) (a := l) (b := r)
    (fun x hx => hd x (hl.trans_le (((Set.uIcc_of_le hlr) ▸ hx).1))) (h₀.add h₁)
  rw [intervalIntegral.integral_add h₀ h₁, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  exact eq_sub_of_add_eq h

/-- The step derivative recurrence has only weighted cell endpoints.
After telescoping, the boundary sum is bounded by the slope variation. -/
theorem mul_stepTransform {a b : ℕ} (d : ℕ → ℝ) (β : ℝ) {s : ℂ} (hs : 0 < s.re) :
    s*stepTransform a b d β s =
      (∑ k ∈ Ico (a+1) (b+1), ((d k:ℂ) * density β (s+1) ((k:ℝ)+1) -
        (d k:ℂ) * density β (s+1) (k:ℝ))) -
        ((β:ℂ)*I)*stepTransform a b d β (s+1) := by
  unfold stepTransform
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k hk
  have hkp : 0 < (k:ℝ) := by
    exact_mod_cast (show 0 < k by have := (mem_Ico.mp hk).1; omega)
  rw [show s*((d k:ℂ)*(∫ x in (k:ℝ)..(k:ℝ)+1, density β s x)) =
    (d k:ℂ)*(s*(∫ x in (k:ℝ)..(k:ℝ)+1, density β s x)) by ring,
    mul_integral_density hkp (by linarith) β hs]
  ring

end GoldbachZeroStrip
end
section

section
open MeasureTheory Finset Complex GoldbachTwistedMellin
open scoped Interval

namespace GoldbachZeroStrip

private theorem norm_density_integral_uniform {X l r : ℝ}
    (hX : 1 ≤ X) (hl : X ≤ l) (hlr : l ≤ r) (hr : r ≤ 2*X)
    (β : ℝ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖∫ x in l..r, density β s x‖ ≤ (2*X)^s.re := by
  have hxp : 0 < X := by linarith
  let A := (2*X)^s.re
  have hA : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  have hb (x : ℝ) (hx : x ∈ Set.uIoc l r) : ‖density β s x‖ ≤ A/X := by
    rw [Set.uIoc_of_le hlr] at hx
    have hp : 0 < x := hxp.trans_le (hl.trans hx.1.le)
    rw [density, norm_mul, norm_phase, one_mul, norm_cpow_eq_rpow_re_of_pos hp,
      sub_re, one_re, Real.rpow_sub hp, Real.rpow_one]
    exact (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow hp.le (hx.2.trans hr) hs) hp.le).trans
      (div_le_div_of_nonneg_left hA hxp (hl.trans hx.1.le))
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [abs_of_nonneg (sub_nonneg.mpr hlr)] at h
  apply h.trans
  calc
    _ ≤ A/X*X := mul_le_mul_of_nonneg_left (by linarith only [hl, hr]) (div_nonneg hA hxp.le)
    _ = A := div_mul_cancel₀ _ hxp.ne'

/-- Off-stationary quadratic Mellin decay of an exact weighted sum of nested
tapers. The derivative jumps are counted by the finite variation bound J. -/
theorem weighted_taper_transform_tail {X : ℝ} (hX : 1 ≤ X)
    {a b : ℕ} (ha : X ≤ (a:ℝ)) (hb : (b:ℝ)+1 ≤ 2*X) (hab : a+2 ≤ b)
    (w : ℕ → ℝ) (hL : w (a+1) = 0) (hR : w (b+1) = 0)
    (β : ℝ) (s : ℂ) (hs : 0 < s.re) (ht : 0 < |s.im|)
    (hβ : 4*X*|β| ≤ |s.im|) {J : ℝ} (hJ : 0 ≤ J) :
    let d := fun k => w (k+1)-w k
    d (a+1)=0 → d b=0 →
    (∑ k ∈ Ico (a+2) (b+1), |d (k-1)-d k|) ≤ J →
    ‖weightedTaperTransform a b w β s‖ ≤ (2*X)^s.re*(4*(2*X)*J/|s.im|^2) := by
  intro d hdL hdR hdVar
  let P := weightedTaperTransform a b w β
  let V := stepTransform a b d β
  let z (n : ℕ) := s + (n:ℂ)
  let F (n k j : ℕ) := (d k:ℂ)*density β (z n+1) (j:ℝ)
  let E (n : ℕ) := ∑ k ∈ Ico (a+1) (b+1), (F n k (k+1)-F n k k)
  have hsRe (n : ℕ) : 0 < (z n).re := by simp [z]; positivity
  have haNat : 0 < a := by
    exact_mod_cast (show (0:ℝ) < a by linarith)
  have hXpos : 0 < X := by linarith
  have hGeom (k : ℕ) (hk : k ∈ Ico (a+1) (b+1)) :
      (X ≤ (k:ℝ)) ∧ (a:ℝ)+1 ≤ k ∧ (k:ℝ)+1 ≤ 2*X := by
    obtain ⟨hl,hr⟩ := mem_Ico.mp hk
    have h₁ : (a:ℝ)+1 ≤ k := by exact_mod_cast hl
    have h₂ : (k:ℝ) ≤ b := by exact_mod_cast (Nat.lt_succ_iff.mp hr)
    exact ⟨by linarith, h₁, by linarith⟩
  have hP (n : ℕ) : ‖P (z n)‖ ≤
      (∑ k ∈ Ico (a+1) (b+1), |w k-w (k+1)|)*(2*X)^(z n).re := by
    unfold P weightedTaperTransform
    apply (norm_sum_le _ _).trans
    rw [sum_mul]
    apply sum_le_sum
    intro k hk
    obtain ⟨_,hkl,hkr⟩ := hGeom k hk
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (norm_transform_le hXpos ha hkl hkr β (z n)
        (fun _ _ hl hm hr => norm_density_integral_uniform hX hl hm hr β (hsRe n).le))
      (abs_nonneg _)
  have hV (n : ℕ) : ‖V (z n)‖ ≤
      (∑ k ∈ Ico (a+1) (b+1), |d k|)*(2*X)^(z n).re := by
    unfold V stepTransform
    apply (norm_sum_le _ _).trans
    rw [sum_mul]
    apply sum_le_sum
    intro k hk
    obtain ⟨hkl,_,hkr⟩ := hGeom k hk
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (norm_density_integral_uniform hX hkl (by linarith) hkr β (hsRe n).le)
      (abs_nonneg _)
  have hE (n : ℕ) : ‖E n‖ ≤ J*(2*X)^(z n).re := by
    have hbound := norm_sum_cell_boundary_le_jumps (by omega : a+1<b+1) (F n)
      (by simp [F,hdL]) (by simp [F,hdR])
    refine hbound.trans ?_
    refine (sum_le_sum (s := Ico (a+2) (b+1))
      (g := fun k => |d (k-1)-d k| * (2*X)^(z n).re) fun k hk => ?_).trans ?_
    · obtain ⟨hkl,hkr⟩ := mem_Ico.mp hk
      have hk' := hGeom k (mem_Ico.mpr ⟨by omega,hkr⟩)
      have hp : 0 < (k:ℝ) := hXpos.trans_le hk'.1
      dsimp only [F]
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, density_succ,
        norm_mul,norm_phase,one_mul,norm_cpow_eq_rpow_re_of_pos hp]
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp.le (by linarith [hk'.2.2]) (hsRe n).le)
      positivity
    · rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right hdVar (Real.rpow_nonneg (by positivity) _)
  have hzsucc (n : ℕ) : z (n+1)=z n+1 := by simp [z,Nat.cast_add,add_assoc]
  exact mellin_tail_of_recurrences P V E s (by positivity) ht hJ (by nlinarith only [hβ])
    hP hV hE
    (fun n => by
      change z n * P (z n) = -V (z (n+1)) - ((β:ℂ)*I)*P (z (n+1))
      rw [hzsucc]
      exact mul_weightedTaperTransform haNat (by omega) w hL hR β (hsRe n))
    (fun n => by
      change z n * V (z n) = E n - ((β:ℂ)*I)*V (z (n+1))
      rw [hzsucc]
      simpa only [E,F,Nat.cast_add,Nat.cast_one] using mul_stepTransform d β (hsRe n))

end GoldbachZeroStrip
end
end
end

section

namespace GoldbachSmoothApproximation

open Set Real

theorem linear_interpolation_error {w w' : ℝ → ℝ} {l h x M : ℝ}
    (hh : 0 < h) (hM : 0 ≤ M) (hx : x ∈ Icc l (l + h))
    (hderiv : ∀ t ∈ Icc l (l + h), HasDerivAt w (w' t) t)
    (hLip : ∀ t ∈ Icc l (l + h), ‖w' t - w' l‖ ≤ M * (t - l)) :
    ‖(1 - (x-l)/h) * w l + ((x-l)/h) * w (l+h) - w x‖ ≤ 2 * M * h ^ 2 := by
  let g (t : ℝ) := w t - w l - w' l * (t-l)
  have hl : l ∈ Icc l (l+h) := ⟨le_rfl, by linarith⟩
  have hr : l+h ∈ Icc l (l+h) := ⟨by linarith, le_rfl⟩
  have hgl : g l = 0 := by simp [g]
  have hg (t : ℝ) (ht : t ∈ Icc l (l+h)) : HasDerivAt g (w' t - w' l) t := by
    simpa only [g, Pi.sub_apply, id_eq, mul_one] using
      ((hderiv t ht).sub_const (w l)).fun_sub (((hasDerivAt_id t).sub_const l).const_mul (w' l))
  have hgb (t : ℝ) (ht : t ∈ Icc l (l+h)) : ‖g t‖ ≤ M * h ^ 2 := by
    have hd (y : ℝ) (hy : y ∈ Icc l (l+h)) : ‖deriv g y‖ ≤ M*h := by
      rw [(hg y hy).deriv]
      exact (hLip y hy).trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) hM)
    have hd' := (convex_Icc l (l+h)).norm_image_sub_le_of_norm_deriv_le
      (fun y hy => (hg y hy).differentiableAt) hd hl ht
    rw [hgl, sub_zero, Real.norm_eq_abs (t-l), abs_of_nonneg (sub_nonneg.mpr ht.1)] at hd'
    exact hd'.trans (by
      have hh' := mul_le_mul_of_nonneg_left (show t-l ≤ h by linarith [ht.2])
        (mul_nonneg hM hh.le)
      nlinarith only [hh'])
  let r := (x-l)/h
  have hr₀ : 0 ≤ r := div_nonneg (sub_nonneg.mpr hx.1) hh.le
  have hr₁ : r ≤ 1 := (div_le_one hh).mpr (by linarith [hx.2])
  have hcancel : (1-r) * w l + r * w (l+h) - w x = r * g (l+h) - g x := by
    dsimp only [r,g]
    field_simp
    ring
  change ‖(1-r) * w l + r * w (l+h) - w x‖ ≤ _
  rw [hcancel]
  apply (norm_sub_le _ _).trans
  rw [norm_mul, Real.norm_eq_abs r, abs_of_nonneg hr₀]
  have hd := (mul_le_of_le_one_left (norm_nonneg (g (l+h))) hr₁).trans (hgb _ hr)
  linarith only [hd, hgb _ hx]

theorem scaled_linear_interpolation_error {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w)
    {M X : ℝ} (hM : 0 ≤ M) (hM₂ : ∀ t, ‖deriv (deriv w) t‖ ≤ M)
    (hX : 0 < X) {n x : ℝ} (hx : x ∈ Icc n (n+1)) :
    ‖(n+1-x) * w (n/X) + (x-n) * w ((n+1)/X) - w (x/X)‖ ≤ 2*M/X^2 := by
  have hdiff : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hdiff' : Differentiable ℝ (deriv w) := hw.differentiable_deriv_two
  have hd : n / X + 1 / X = (n+1) / X := (add_div _ _ _).symm
  have hxn : x/X ∈ Icc (n/X) (n/X+1/X) := by
    rw [hd]
    exact ⟨div_le_div_of_nonneg_right hx.1 hX.le, div_le_div_of_nonneg_right hx.2 hX.le⟩
  have hLip (y : ℝ) (hy : y ∈ Icc (n/X) (n/X+1/X)) :
      ‖deriv w y - deriv w (n/X)‖ ≤ M*(y-n/X) := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
      (fun t _ => hdiff' t) (fun t _ => hM₂ t) convex_univ
      (x := n/X) (y := y) trivial trivial
    rwa [Real.norm_eq_abs (y - n/X), abs_of_nonneg (sub_nonneg.mpr hy.1)] at h
  have h := linear_interpolation_error (one_div_pos.mpr hX) hM hxn
    (fun y _ => (hdiff y).hasDerivAt) hLip
  have hf : (x/X - n/X) / (1/X) = x-n := by field_simp
  rw [hf, hd, div_pow, one_pow] at h
  convert h using 2 <;> ring

end GoldbachSmoothApproximation
end

section

namespace GoldbachSmoothApproximation

open Complex MeasureTheory Set Finset GoldbachTwistedMellin GoldbachZeroStrip
open scoped Interval

noncomputable def taperProfile (a b : ℕ) (w : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Ico (a+1) (b+1), (w k - w (k+1)) * taper a k x

private theorem interval_integrable_taper_density (a k : ℕ) (β : ℝ) (s : ℂ)
    {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) :
    IntervalIntegrable (fun x => (taper a k x : ℂ) * density β s x) volume l r := by
  have hC : ContinuousOn (fun x => (taper a k x : ℂ) * density β s x) (Icc l r) :=
    (continuous_ofReal.comp (continuous_taper _ _)).continuousOn.mul
      (fun x hx => (continuousAt_density β s (hl.trans_le hx.1)).continuousWithinAt)
  exact hC.intervalIntegrable_of_Icc hlr

theorem weightedTaperTransform_eq_integral {a b : ℕ} (ha : 0 < a)
    (w : ℕ → ℝ) (β : ℝ) (s : ℂ) (hab : a ≤ b) :
    weightedTaperTransform a b w β s =
      ∫ x in (a : ℝ)..(b : ℝ)+1, (taperProfile a b w x : ℂ) * density β s x := by
  have ha₀ : (0 : ℝ) < a := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ (b : ℝ) + 1 := by
    have h : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  unfold weightedTaperTransform taperProfile
  simp_rw [Complex.ofReal_sum, Complex.ofReal_mul, sum_mul, mul_assoc]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro k hk
    obtain ⟨hkL, hkR⟩ := mem_Ico.mp hk
    have hka : (a : ℝ) + 1 ≤ k := by exact_mod_cast hkL
    have hkb : (k : ℝ) + 1 ≤ (b : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.lt_succ_iff.mp hkR)
    rw [intervalIntegral.integral_const_mul, transform_eq_taper_integral ha₀ hka]
    congr 1
    let g (x : ℝ) := (taper a k x : ℂ) * density β s x
    have hak : (a : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have hk₀ : (0 : ℝ) < (k : ℝ) + 1 := ha₀.trans_le hak
    have h := intervalIntegral.integral_add_adjacent_intervals
      (interval_integrable_taper_density a k β s ha₀ hak)
      (interval_integrable_taper_density a k β s hk₀ hkb)
    have hz : (∫ x in (k : ℝ)+1..(b : ℝ)+1, g x) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ))]
      · simp
      · intro x hx
        rw [uIcc_of_le hkb] at hx
        simp [g, taper_right hx.1]
    change (∫ x in (a:ℝ)..(k:ℝ)+1, g x) = ∫ x in (a:ℝ)..(b:ℝ)+1, g x
    change (∫ x in (a:ℝ)..(k:ℝ)+1, g x) + (∫ x in (k:ℝ)+1..(b:ℝ)+1, g x) =
      (∫ x in (a:ℝ)..(b:ℝ)+1, g x) at h
    simpa only [hz, add_zero] using h
  · intro k _
    exact (interval_integrable_taper_density a k β s ha₀ habR).const_mul _

private theorem sample_differences (w : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Ico a b, (w k - w (k+1))) = w a - w b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b h ih =>
    rw [sum_Ico_succ_top h, ih]
    ring

theorem taperProfile_left_zero {a b : ℕ} (hab : a+1 ≤ b+1) (w : ℕ → ℝ)
    (hL : w (a+1) = 0) (hR : w (b+1) = 0) {x : ℝ}
    (hx : x ∈ Icc (a : ℝ) ((a : ℝ) + 1)) :
    taperProfile a b w x = 0 := by
  unfold taperProfile
  have he : (∑ k ∈ Ico (a+1) (b+1), (w k - w (k+1)) * taper a k x) =
      (∑ k ∈ Ico (a+1) (b+1), (w k - w (k+1))) * (x-(a:ℝ)) := by
    rw [sum_mul]
    apply sum_congr rfl
    intro k hk
    rw [taper_rise (by exact_mod_cast (mem_Ico.mp hk).1) hx]
  rw [he, sample_differences w hab, hL, hR, sub_self, zero_mul]

theorem taperProfile_compare {a b : ℕ} (hab : a+1 ≤ b) {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) {M X : ℝ} (hM : 0 ≤ M)
    (hM₂ : ∀ t, ‖deriv (deriv w) t‖ ≤ M) (hX : 0 < X)
    (hR : w (((b+1:ℕ):ℝ)/X) = 0) {x : ℝ}
    (hx : x ∈ Icc ((a : ℝ)+1) ((b : ℝ)+1)) :
    ‖taperProfile a b (fun k => w ((k:ℝ)/X)) x - w (x/X)‖ ≤ 2*M/X^2 := by
  let n := min b ⌊x⌋₊
  have hna : a+1 ≤ n := Nat.le_min.mpr ⟨hab, Nat.le_floor (by exact_mod_cast hx.1)⟩
  have hnb : n ≤ b := min_le_left _ _
  have hx₀ : 0 ≤ x := by linarith only [hx.1, Nat.cast_nonneg (α := ℝ) a]
  have hnx : (n : ℝ) ≤ x := by
    have h : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast min_le_right b ⌊x⌋₊
    exact h.trans (Nat.floor_le hx₀)
  have hnx' : x ≤ (n : ℝ) + 1 := by
    rcases le_or_gt b ⌊x⌋₊ with h | h
    · simpa [n, min_eq_left h] using hx.2
    · simpa [n, min_eq_right h.le] using (Nat.lt_floor_add_one x).le
  unfold taperProfile
  rw [taper_sum_on_cell _ hna hnb hR ⟨hnx, hnx'⟩]
  simpa only [Nat.cast_add, Nat.cast_one] using scaled_linear_interpolation_error hw hM hM₂ hX ⟨hnx, hnx'⟩


theorem exact_weighted_transform_approx {a b : ℕ} (hab : a+1 ≤ b) {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) {M X : ℝ} (hM : 0 ≤ M)
    (hM₂ : ∀ t, ‖deriv (deriv w) t‖ ≤ M) (hX : 0 < X)
    (ha : X ≤ (a : ℝ)) (hb : (b : ℝ)+1 ≤ 2*X)
    (hL : ∀ x ∈ Icc (a : ℝ) ((a : ℝ)+1), w (x/X) = 0)
    (hR : w (((b+1:ℕ):ℝ)/X) = 0) (β : ℝ) (s : ℂ) (hs : 0 ≤ s.re) :
    ‖weightedTaperTransform a b (fun k => w ((k:ℝ)/X)) β s -
        (∫ x in (a:ℝ)..(b:ℝ)+1, (w (x/X) : ℂ) * density β s x)‖ ≤
      (2*M / X^2) * (2*X)^s.re := by
  let l : ℝ := a
  let r : ℝ := (b : ℝ) + 1
  have hlr : l ≤ r := by
    have h : (a:ℝ) ≤ b := by exact_mod_cast (show a ≤ b by omega)
    dsimp [l,r]; linarith
  have haNat : 0 < a := by exact_mod_cast hX.trans_le ha
  let W := taperProfile a b (fun k => w ((k:ℝ)/X))
  let v (x : ℝ) := w (x/X)
  have hW : Continuous W := by
    unfold W taperProfile
    exact continuous_finsetSum _ (fun _ _ => (continuous_taper ..).const_mul _)
  have hv : Continuous v := hw.continuous.comp (continuous_id.div_const X)
  have hC : ContinuousOn (density β s) (Icc l r) := fun x hx =>
    (continuousAt_density β s (hX.trans_le (ha.trans hx.1))).continuousWithinAt
  have hI_W : IntervalIntegrable (fun x => (W x : ℂ)*density β s x) volume l r :=
    ((continuous_ofReal.comp hW).continuousOn.mul hC).intervalIntegrable_of_Icc hlr
  have hI_v : IntervalIntegrable (fun x => (v x : ℂ)*density β s x) volume l r :=
    ((continuous_ofReal.comp hv).continuousOn.mul hC).intervalIntegrable_of_Icc hlr
  have hbound (x : ℝ) (hx : x ∈ Icc l r) : ‖W x - v x‖ ≤ 2*M/X^2 := by
    rcases le_or_gt x ((a:ℝ)+1) with hl | hr
    · have hmem : x ∈ Icc (a:ℝ) ((a:ℝ)+1) := ⟨hx.1, hl⟩
      have hWz : W x = 0 := taperProfile_left_zero (Nat.le_succ_of_le hab) _
        (by simpa only [Nat.cast_add, Nat.cast_one] using hL ((a:ℝ)+1) ⟨by linarith, le_rfl⟩) hR hmem
      rw [hWz, show v x = 0 from hL x hmem, sub_zero, norm_zero]
      positivity
    · exact taperProfile_compare hab hw hM hM₂ hX hR ⟨hr.le, hx.2⟩
  have hnorm_density (x : ℝ) (hx : x ∈ Icc l r) : ‖density β s x‖ ≤ (2*X)^s.re / X := by
    have hx₀ := hX.trans_le (ha.trans hx.1)
    rw [density, norm_mul, norm_phase, one_mul, norm_cpow_eq_rpow_re_of_pos hx₀,
      sub_re, one_re, Real.rpow_sub hx₀, Real.rpow_one]
    exact (div_le_div_of_nonneg_right (Real.rpow_le_rpow hx₀.le (hx.2.trans hb) hs) hx₀.le).trans
      (div_le_div_of_nonneg_left (by positivity) hX (ha.trans hx.1))
  rw [weightedTaperTransform_eq_integral haNat _ β s (by omega)]
  change ‖(∫ x in l..r, (W x : ℂ)*density β s x) - ∫ x in l..r, (v x : ℂ)*density β s x‖ ≤ _
  rw [← intervalIntegral.integral_sub hI_W hI_v]
  have h (x : ℝ) (hx : x ∈ Ι l r) :
      ‖(W x : ℂ)*density β s x - (v x : ℂ)*density β s x‖ ≤
        (2*M/X^2) * (2*X)^s.re / X := by
    have hx' : x ∈ Icc l r := uIcc_of_le hlr ▸ uIoc_subset_uIcc hx
    rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, mul_div_assoc]
    exact mul_le_mul (hbound x hx') (hnorm_density x hx') (norm_nonneg _) (by positivity)
  apply (intervalIntegral.norm_integral_le_of_norm_le_const h).trans
  rw [abs_of_nonneg (sub_nonneg.mpr hlr)]
  calc
    _ ≤ (2*M/X^2) * (2*X)^s.re / X * X := mul_le_mul_of_nonneg_left
      (by dsimp [l,r]; linarith only [ha, hb]) (by positivity)
    _ = _ := div_mul_cancel₀ _ hX.ne'

end GoldbachSmoothApproximation
end

section

namespace GoldbachHeightTail

open Finset

private theorem inv_pow_le_diff {x : ℝ} (hx : 1 ≤ x) {p : ℕ} (hp : p = 2 ∨ p = 3) :
    1 / x^p ≤ 2 * (1 / x^(p-1) - 1 / (x+1)^(p-1)) := by
  have hpos : 0 < x := zero_lt_one.trans_le hx
  have hpos' : 0 < x + 1 := by linarith
  rcases hp with rfl | rfl
  · norm_num
    have hmul : 0 < x^2 * (x+1) := by positivity
    apply le_of_mul_le_mul_right ?_ hmul
    have h₁ : (x^2)⁻¹ * (x^2*(x+1)) = x+1 := by field_simp
    have h₂ : 2*(x⁻¹ - (x+1)⁻¹) * (x^2*(x+1)) = 2*x := by field_simp; ring
    rw [h₁, h₂]
    linarith
  · norm_num
    have hmul : 0 < x^3 * (x+1)^2 := by positivity
    apply le_of_mul_le_mul_right ?_ hmul
    have h₁ : (x^3)⁻¹ * (x^3*(x+1)^2) = (x+1)^2 := by field_simp
    have h₂ : 2*((x^2)⁻¹ - ((x+1)^2)⁻¹) * (x^3*(x+1)^2) =
        2*x*((x+1)^2 - x^2) := by field_simp
    rw [h₁, h₂]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hx) (by positivity : 0 ≤ x + 1)]

private theorem inverse_power_sum_le (J : Finset ℕ) {H : ℝ} (hH : 1 ≤ H) {p : ℕ}
    (hp : p = 2 ∨ p = 3) :
    (∑ k ∈ J, (1:ℝ)/(H+(k:ℝ))^p) ≤ 2/H^(p-1) := by
  let f (k : ℕ) := 1 / (H+(k:ℝ))^(p-1)
  have htel (n : ℕ) : (∑ k ∈ range n, (f k - f (k+1))) = f 0 - f n := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; ring
  let N := J.sup id + 1
  have hsub : J ⊆ range N := fun k hk => mem_range.mpr (Nat.lt_succ_of_le
    (Finset.le_sup (f := id) hk))
  calc
    _ ≤ ∑ k ∈ range N, (1:ℝ)/(H+(k:ℝ))^p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ k ∈ range N, 2*(f k-f (k+1)) := by
      apply sum_le_sum
      intro k _
      simpa only [f, Nat.cast_add, Nat.cast_one, ← add_assoc] using
        inv_pow_le_diff (show 1 ≤ H+(k:ℝ) by linarith [Nat.cast_nonneg (α := ℝ) k]) hp
    _ ≤ _ := by
      rw [← mul_sum, htel]
      simp only [f, Nat.cast_zero, add_zero]
      calc
        _ ≤ 2 * (1/H^(p-1)) := mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by norm_num)
        _ = _ := by ring

theorem inverse_height_weighted_le {ι : Type*} (S : Finset ι) (height c : ι → ℝ)
    {H B : ℝ} (hH : 1 ≤ H) (hB : 0 ≤ B) {p : ℕ} (hp : p = 2 ∨ p = 3)
    (hc : ∀ i ∈ S, 0 ≤ c i)
    (hunit : ∀ t : ℝ, (∑ i ∈ S.filter (fun i => t ≤ height i ∧ height i ≤ t+1), c i) ≤ B) :
    (∑ i ∈ S.filter (fun i => H ≤ height i), c i / (height i)^p) ≤ 2*B/H^(p-1) := by
  classical
  let T := S.filter (fun i => H ≤ height i)
  let bin (i : ι) := ⌊height i-H⌋₊
  let J := T.image bin
  have hmap : (T : Set ι).MapsTo bin J := fun i hi => mem_image_of_mem _ hi
  have hbin (k : ℕ) (i : ι) (hi : i ∈ T.filter (fun i => bin i = k)) :
      H+(k:ℝ) ≤ height i ∧ height i ≤ H+k+1 := by
    obtain ⟨hiT,hk⟩ := mem_filter.mp hi
    have ht := (mem_filter.mp hiT).2
    have h₀ : (bin i : ℝ) ≤ height i-H := Nat.floor_le (sub_nonneg.mpr ht)
    have h₁ : height i-H < (bin i:ℝ)+1 := Nat.lt_floor_add_one _
    rw [hk] at h₀ h₁
    exact ⟨by linarith, by linarith⟩
  have hcard (k : ℕ) : (∑ i ∈ T.filter (fun i => bin i = k), c i) ≤ B := by
    have hsub : T.filter (fun i => bin i = k) ⊆
        S.filter (fun i => H+(k:ℝ) ≤ height i ∧ height i ≤ H+k+1) := fun i hi =>
      mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hi).1).1, hbin k i hi⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hc i (mem_filter.mp hi).1)).trans
      (hunit (H+k))
  change (∑ i ∈ T, c i/(height i)^p) ≤ _
  calc
    _ = ∑ k ∈ J, ∑ i ∈ T.filter (fun i => bin i = k), c i/(height i)^p :=
      (sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ k ∈ J, B * (1/(H+(k:ℝ))^p) := by
      apply sum_le_sum
      intro k _
      calc
        _ ≤ ∑ i ∈ T.filter (fun i => bin i = k), c i * (1/(H+(k:ℝ))^p) := by
          refine sum_le_sum fun i hi => ?_
          have hHp : 0 < H+(k:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity)
            (pow_le_pow_left₀ hHp.le (hbin k i hi).1 p)) (hc i (mem_filter.mp (mem_filter.mp hi).1).1)
        _ ≤ _ := by
          rw [← sum_mul]
          exact mul_le_mul_of_nonneg_right (hcard k) (by positivity)
    _ = B * ∑ k ∈ J, 1 / (H+(k:ℝ))^p := by rw [mul_sum]
    _ ≤ _ := (mul_le_mul_of_nonneg_left (inverse_power_sum_le J hH hp) hB).trans_eq (by ring)

theorem unit_abs_height_weight {ι : Type*} (S : Finset ι) (height c : ι → ℝ) {B : ℝ}
    (hc : ∀ i ∈ S, 0 ≤ c i)
    (hunit : ∀ t : ℝ, (∑ i ∈ S.filter (fun i => t ≤ height i ∧ height i ≤ t+1), c i) ≤ B)
    (t : ℝ) :
    (∑ i ∈ S.filter (fun i => t ≤ |height i| ∧ |height i| ≤ t+1), c i) ≤ 2*B := by
  classical
  let L := S.filter (fun i => t ≤ height i ∧ height i ≤ t+1)
  let R := S.filter (fun i => -t-1 ≤ height i ∧ height i ≤ (-t-1)+1)
  have hsub : S.filter (fun i => t ≤ |height i| ∧ |height i| ≤ t+1) ⊆ L ∪ R := by
    intro i hi
    obtain ⟨hiS, h⟩ := mem_filter.mp hi
    apply mem_union.mpr
    rcases le_or_gt 0 (height i) with hh | hh
    · exact Or.inl (mem_filter.mpr ⟨hiS, by simpa only [abs_of_nonneg hh] using h⟩)
    · rw [abs_of_neg hh] at h
      exact Or.inr (mem_filter.mpr ⟨hiS, ⟨by linarith [h.2], by linarith [h.1]⟩⟩)
  calc
    _ ≤ ∑ i ∈ L ∪ R, c i := sum_le_sum_of_subset_of_nonneg hsub
      (fun i hi _ => hc i ((mem_union.mp hi).elim (fun h => (mem_filter.mp h).1) (fun h => (mem_filter.mp h).1)))
    _ ≤ (∑ i ∈ L, c i) + ∑ i ∈ R, c i := by
      have he := sum_union_inter (f := c) (s₁ := L) (s₂ := R)
      have hI : 0 ≤ ∑ i ∈ L ∩ R, c i := sum_nonneg (fun i hi => hc i (mem_filter.mp (mem_inter.mp hi).1).1)
      linarith
    _ ≤ _ := by linarith [hunit t, hunit (-t-1)]

end GoldbachHeightTail
end

section

namespace GoldbachModelTail

open Complex Finset GoldbachSmoothWindow GoldbachSmoothMellin
open scoped ContDiff

theorem exact_taper_quadratic_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ), 32 ≤ X → ∀ {β : ℝ} {s : ℂ},
      0 < s.re → 0 < |s.im| → 4*(X:ℝ)*|β| ≤ |s.im| →
      ‖GoldbachZeroStrip.weightedTaperTransform X (2*X-1)
        (fun n => scaledWeight X n) β s‖ ≤ (2*(X:ℝ))^s.re * (A / |s.im|^2) := by
  obtain ⟨M,hM,hder⟩ := weight_derivative_bound 2
  have hdd (t : ℝ) : ‖deriv (deriv weight) t‖ ≤ M := by
    have he : iteratedDeriv 2 weight = deriv (deriv weight) := by
      change iteratedDeriv (1+1) weight = _
      rw [iteratedDeriv_succ, show (1:ℕ)=0+1 by decide, iteratedDeriv_succ, iteratedDeriv_zero]
    exact he ▸ hder t
  refine ⟨8*M, by positivity, ?_⟩
  intro X hX β s hs ht hβ
  let x : ℝ := X
  let b := 2*X-1
  let w (n : ℕ) := scaledWeight x n
  have hx : 32 ≤ x := by dsimp only [x]; exact_mod_cast hX
  have hx0 : 0 < x := by linarith
  have hbNat : b+1 = 2*X := by dsimp only [b]; omega
  have hb : (b:ℝ)+1 = 2*x := by
    dsimp only [x]
    exact_mod_cast hbNat
  have hW (t : ℕ) : w t = weight ((t:ℝ)/x) := rfl
  have hL₁ : w (X+1) = 0 := by
    rw [hW]
    exact weight_zero (Or.inl ((div_le_iff₀ hx0).mpr (by push_cast; dsimp only [x] at hx ⊢; linarith)))
  have hL₂ : w (X+2) = 0 := by
    rw [hW]
    exact weight_zero (Or.inl ((div_le_iff₀ hx0).mpr (by push_cast; dsimp only [x] at hx ⊢; linarith)))
  have hR₁ : w b = 0 := by
    rw [hW]
    exact weight_zero (Or.inr ((le_div_iff₀ hx0).mpr (by linarith)))
  have hR₂ : w (b+1) = 0 := by
    rw [hW,Nat.cast_add,Nat.cast_one,hb,mul_div_cancel_right₀ _ hx0.ne']
    exact weight_zero (Or.inr (by norm_num))
  let d (k : ℕ) := w (k+1)-w k
  let J := Ico (X+2) (b+1)
  have hpoint (k : ℕ) (hk : k ∈ J) : |d (k-1)-d k| ≤ M/x^2 := by
    have hk1 : 1 ≤ k := by
      have := (mem_Ico.mp hk).1
      omega
    have he : ((k-1:ℕ):ℝ)+1 = k := by
      exact_mod_cast Nat.sub_add_cancel hk1
    have h := GoldbachZeroStrip.sampled_slope_variation weight weight_smooth hdd hx0 ({k-1} : Finset ℕ)
    simp only [sum_singleton, card_singleton, Nat.cast_one, one_mul, Real.norm_eq_abs, he,
      show ((k-1:ℕ):ℝ)+2 = (k:ℝ)+1 by linarith only [he]] at h
    simpa only [d,hW,Nat.sub_add_cancel hk1,Nat.cast_add,Nat.cast_one, he, abs_sub_comm
      (weight (((k:ℝ)+1)/x) - weight ((k:ℝ)/x))] using h
  have hjcard : (J.card : ℝ) ≤ x := by
    unfold J
    rw [Nat.card_Ico]
    dsimp only [x]
    exact_mod_cast (by omega : b+1-(X+2) ≤ X)
  have hV : (∑ k ∈ J, |d (k-1)-d k|) ≤ M/x := calc
    _ ≤ ∑ _k ∈ J, M/x^2 := sum_le_sum hpoint
    _ = (J.card:ℝ)*(M/x^2) := by simp [nsmul_eq_mul]
    _ ≤ x*(M/x^2) := mul_le_mul_of_nonneg_right hjcard (by positivity)
    _ = _ := by field_simp
  have h := GoldbachZeroStrip.weighted_taper_transform_tail (show 1 ≤ x by linarith)
    (a := X) (b := b) le_rfl hb.le (by dsimp only [b]; omega) w hL₁ hR₂ β s hs ht hβ (by positivity : 0 ≤ M/x)
    (show d (X+1)=0 by dsimp only [d]; rw [show X+1+1=X+2 by omega,hL₁,hL₂,sub_self])
    (show d b=0 by dsimp only [d]; rw [hR₁,hR₂,sub_self]) hV
  change ‖GoldbachZeroStrip.weightedTaperTransform X b w β s‖ ≤ (2*x)^s.re * (8*M/|s.im|^2)
  apply h.trans_eq
  have he : 4*(2*x)*(M/x) = 8*M := by field_simp; ring
  rw [he]

end GoldbachModelTail
end

section

namespace GoldbachSmoothHighOrder

open MeasureTheory Set Complex GoldbachTwistedMellin GoldbachSmoothMellin GoldbachSmoothWindow
open scoped Interval ContDiff

private theorem smooth_mellin_gain (P Q : ℂ → ℂ) (s : ℂ)
    {R β U V : ℝ} (hR : 0 < R) (ht : 0 < |s.im|) (hV : 0 ≤ V)
    (hβ : 2 * R * |β| ≤ |s.im|) :
    let z (n : ℕ) := s + (n:ℂ)
    let A (n : ℕ) := R^(z n).re
    (∀ n : ℕ, (‖P (z n)‖ / A n) ≤ U) →
    (∀ n : ℕ, (‖Q (z n)‖ / A n) ≤ V) →
    (∀ n : ℕ, z n * P (z n) = -Q (z (n+1)) - ((β:ℂ)*I)*P (z (n+1))) →
    ∀ n : ℕ, ‖P (z n)‖ / A n ≤ ((2*R) / |s.im|) * V := by
  dsimp only
  intro hP hQ hrec
  let z (n : ℕ) := s + (n:ℂ)
  let A (n : ℕ) := R^(z n).re
  let t := |s.im|
  let u (n : ℕ) := ‖P (z n)‖ / A n
  let v (n : ℕ) := ‖Q (z n)‖ / A n
  have hA (n : ℕ) : 0 < A n := Real.rpow_pos_of_pos hR _
  have hAs (n : ℕ) : A (n+1) = R * A n := by
    have hz : (z (n+1)).re = (z n).re+1 := by simp [z, add_assoc]
    dsimp only [A]
    rw [hz, Real.rpow_add_one hR.ne', mul_comm]
  have hUn (n : ℕ) : 0 ≤ u n := div_nonneg (norm_nonneg _) (hA n).le
  have hUa (n : ℕ) : u n * A n = ‖P (z n)‖ := div_mul_cancel₀ _ (hA n).ne'
  have hVa (n : ℕ) : v n * A n = ‖Q (z n)‖ := div_mul_cancel₀ _ (hA n).ne'
  have hAngle (n : ℕ) : t ≤ ‖z n‖ := by simpa [z,t] using Complex.abs_im_le_norm (z n)
  have hfreq : ‖(β:ℂ)*I‖ = |β| := by simp [Complex.norm_real,Real.norm_eq_abs]
  have hsmall : |β| * R ≤ t/2 := by dsimp only [t]; nlinarith only [hβ]
  have hstep (n : ℕ) : u n ≤ (R/t)*V + u (n+1)/2 := by
    have h₁ : t*‖P (z n)‖ ≤ ‖Q (z (n+1))‖ + |β| * ‖P (z (n+1))‖ := by
      apply (mul_le_mul_of_nonneg_right (hAngle n) (norm_nonneg _)).trans
      rw [← norm_mul, hrec n]
      exact (norm_sub_le _ _).trans_eq (by rw [norm_neg,norm_mul,hfreq])
    rw [← hUa n, ← hVa (n+1), ← hUa (n+1), hAs] at h₁
    have h₂ : t*(u n) ≤ R*v (n+1)+(|β| * R)*u (n+1) := by
      apply le_of_mul_le_mul_right ?_ (hA n)
      convert h₁ using 1 <;> ring
    have hs := h₂.trans (add_le_add (mul_le_mul_of_nonneg_left (hQ (n+1)) hR.le)
      (mul_le_mul_of_nonneg_right hsmall (hUn (n+1))))
    apply le_of_mul_le_mul_right ?_ ht
    convert hs using 1
    · ring
    · field_simp [show t ≠ 0 from ht.ne']
      ring
  intro n
  apply (half_recurrence_bound (mul_nonneg (div_nonneg hR.le ht.le) hV) hP hstep n).trans_eq
  ring

end GoldbachSmoothHighOrder

end

section

namespace GoldbachCorrectionBands

open Complex Finset Set MeasureTheory GoldbachTwistedMellin
open scoped Interval

theorem continuous_mellin_band {w : ℝ → ℂ} (hw : Continuous w)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (s : ℂ) :
    Continuous (fun β : ℝ => ∫ x in a..b, w x * density β s x) := by
  let g (β x : ℝ) := w x * phase β x * Complex.exp ((s-1)*((Real.log (max (a/2) x):ℝ):ℂ))
  have hz : Continuous (fun u : ℝ×ℝ => Real.log (max (a/2) u.2)) :=
    (continuous_const.max continuous_snd).log
      (fun p => ne_of_gt ((half_pos ha).trans_le (le_max_left (a/2) p.2)))
  have hg : Continuous g.uncurry := by
    change Continuous (fun p : ℝ×ℝ =>
      w p.2 * phase p.1 p.2 * Complex.exp ((s-1)*((Real.log (max (a/2) p.2):ℝ):ℂ)))
    unfold phase
    fun_prop
  have h : Continuous (fun β : ℝ => ∫ x in Set.Icc a b, g β x) :=
    continuous_parametric_integral_of_continuous hg isCompact_Icc
  convert h using 1
  funext β
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  have ht₀ : 0 < t := ha.trans ht.1
  have hmax : max (a/2) t = t := max_eq_right (by linarith [ht.1])
  have hcp : ((t:ℝ):ℂ)^(s-1) = Complex.exp ((s-1)*(Real.log t:ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht₀.ne'), ← Complex.ofReal_log ht₀.le]
    congr 1
    ring
  simp only [g,density,hmax,hcp]
  ring

theorem continuous_zero_taper {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) (w : ℕ → ℝ) (s : ℂ) :
    Continuous (fun β : ℝ => GoldbachZeroStrip.weightedTaperTransform a b w β s) := by
  have hW : Continuous (GoldbachSmoothApproximation.taperProfile a b w) := by
    unfold GoldbachSmoothApproximation.taperProfile
    exact continuous_finsetSum _ (fun _ _ => (continuous_taper ..).const_mul _)
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ (b : ℝ)+1 := by
    have h : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  simp_rw [GoldbachSmoothApproximation.weightedTaperTransform_eq_integral ha w _ s hab]
  exact continuous_mellin_band (continuous_ofReal.comp hW) haR habR s

theorem split_taper_correction {ι : Type*} (S : Finset ι) (γ : ι → ℝ) (c e w : ι → ℂ)
    {H J : ℝ} (hHJ : H ≤ J) :
    let low := S.filter (fun i => |γ i| < H)
    let med := S.filter (fun i => H ≤ |γ i| ∧ |γ i| < J)
    let inner := S.filter (fun i => |γ i| < J)
    let high := S.filter (fun i => J ≤ |γ i|)
    (∑ i ∈ S, c i * e i) =
      (∑ i ∈ low, c i*w i) + (∑ i ∈ med, c i*w i) +
        (∑ i ∈ inner, c i*(e i-w i)) + (∑ i ∈ high, c i*e i) := by
  classical
  dsimp only
  let base := S.filter (fun i => |γ i| < J)
  have hl : base.filter (fun i => |γ i| < H) = S.filter (fun i => |γ i| < H) := by
    ext i
    simp only [base, Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1,h.2.trans_le hHJ⟩,h.2⟩
  have hm : base.filter (fun i => ¬ |γ i| < H) =
      S.filter (fun i => H ≤ |γ i| ∧ |γ i| < J) := by
    ext i
    simp only [base, Finset.mem_filter, not_lt]
    tauto
  have hfirst := Finset.sum_filter_add_sum_filter_not (s := S) (p := fun i => |γ i| < J)
    (f := fun i => c i*e i)
  change (∑ i ∈ base, c i*e i) +
    (∑ i ∈ S.filter (fun i => ¬ |γ i| < J), c i*e i) = _ at hfirst
  simp only [not_lt] at hfirst
  have hsecond := Finset.sum_filter_add_sum_filter_not (s := base) (p := fun i => |γ i| < H)
    (f := fun i => c i*w i)
  rw [hl,hm] at hsecond
  rw [← hfirst, hsecond]
  change (∑ i ∈ base, _) + _ = _ + (∑ i ∈ base, _) + _
  simp only [mul_sub, sum_sub_distrib]
  abel

theorem norm_add_four_sq_le (a b c d : ℂ) :
    ‖a+b+c+d‖^2 ≤ 4*(‖a‖^2+‖b‖^2+‖c‖^2+‖d‖^2) := by
  have h2 (x y : ℂ) : ‖x+y‖^2 ≤ 2*(‖x‖^2+‖y‖^2) := by
    have h := pow_le_pow_left₀ (norm_nonneg (x+y)) (norm_add_le x y) 2
    nlinarith only [h, sq_nonneg (‖x‖-‖y‖)]
  rw [show a+b+c+d = (a+b)+(c+d) by abel]
  exact (h2 (a+b) (c+d)).trans (by linarith only [h2 a b,h2 c d])

theorem band_integral_add_four_sq_le (f g h k : ℝ → ℂ) (T : ℝ)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (hk : Continuous k) :
    (∫ x in Set.Icc (-T) T, ‖f x+g x+h x+k x‖^2) ≤
      4*((∫ x in Set.Icc (-T) T, ‖f x‖^2) +
         (∫ x in Set.Icc (-T) T, ‖g x‖^2) +
         (∫ x in Set.Icc (-T) T, ‖h x‖^2) +
         (∫ x in Set.Icc (-T) T, ‖k x‖^2)) := by
  have hI (a : ℝ → ℂ) (ha : Continuous a) : IntegrableOn (fun x => ‖a x‖^2) (Set.Icc (-T) T) :=
    (ha.norm.pow 2).integrableOn_Icc
  calc
    _ ≤ ∫ x in Set.Icc (-T) T, 4*(‖f x‖^2+‖g x‖^2+‖h x‖^2+‖k x‖^2) := by
      apply integral_mono ((hf.add hg |>.add hh |>.add hk).norm.pow 2).integrableOn_Icc
        ((((hf.norm.pow 2).add (hg.norm.pow 2) |>.add (hh.norm.pow 2) |>.add (hk.norm.pow 2)).const_mul 4).integrableOn_Icc)
      intro x
      exact norm_add_four_sq_le ..
    _ = _ := by
      rw [integral_const_mul, integral_add, integral_add, integral_add]
      · exact hI f hf
      · exact hI g hg
      · exact (hI f hf).add (hI g hg)
      · exact hI h hh
      · exact ((hI f hf).add (hI g hg)).add (hI h hh)
      · exact hI k hk

end GoldbachCorrectionBands
end

section

namespace GoldbachCorrectionBands

open Finset MeasureTheory GoldbachHeightTail GoldbachModelTail
open GoldbachSmoothWindow GoldbachSmoothMellin GoldbachSmoothApproximation GoldbachZeroStrip
open scoped Interval

theorem weighted_absolute_tail_sup {ι : Type*} (S : Finset ι) (γ : ι → ℝ) (c F : ι → ℂ)
    {H B K : ℝ} (hH : 1 ≤ H) (hB : 0 ≤ B) (hK : 0 ≤ K) {p : ℕ} (hp : p = 2 ∨ p = 3)
    (hunit : ∀ t : ℝ, (∑ i ∈ S.filter (fun i => t ≤ γ i ∧ γ i ≤ t+1), ‖c i‖) ≤ B)
    (hF : ∀ i ∈ S, H ≤ |γ i| → ‖F i‖ ≤ K/|γ i|^p) :
    ‖∑ i ∈ S.filter (fun i => H ≤ |γ i|), c i*F i‖ ≤ 4*B*K/H^(p-1) := by
  have hsum := inverse_height_weighted_le S (fun i => |γ i|) (fun i => ‖c i‖)
    hH (by positivity : 0 ≤ 2*B) hp (fun i _ => norm_nonneg _)
    (unit_abs_height_weight S γ (fun i => ‖c i‖) (fun i _ => norm_nonneg _) hunit)
  calc
    _ ≤ ∑ i ∈ S.filter (fun i => H ≤ |γ i|), ‖c i*F i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S.filter (fun i => H ≤ |γ i|), ‖c i‖*(K/|γ i|^p) := by
      apply sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hF i (mem_filter.mp hi).1 (mem_filter.mp hi).2) (norm_nonneg _)
    _ = K * (∑ i ∈ S.filter (fun i => H ≤ |γ i|), ‖c i‖/|γ i|^p) := by
      rw [mul_sum]
      exact sum_congr rfl (fun _ _ => by ring)
    _ ≤ _ := (mul_le_mul_of_nonneg_left hsum hK).trans_eq (by ring)

theorem band_energy_of_sup {f : ℝ → ℂ} (hf : Continuous f) {R M : ℝ} (hR : 0 ≤ R)
    (_hM : 0 ≤ M) (hF : ∀ t ∈ Set.Icc (-R) R, ‖f t‖ ≤ M) :
    (∫ t in Set.Icc (-R) R, ‖f t‖^2) ≤ 2*R*M^2 := by
  have hle : -R ≤ R := by linarith
  simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  calc
    _ ≤ ∫ _t in (-R)..R, M^2 := by
      apply intervalIntegral.integral_mono_on hle ((hf.norm.pow 2).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)
      intro t ht
      exact pow_le_pow_left₀ (norm_nonneg _) (hF t ht) 2
    _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]; ring

private theorem constant_scaled_endpoint {X : ℕ} (hX : 1 ≤ X) :
    (((2*X-1 : ℕ):ℝ)+1) = 2*(X:ℝ) := by
  exact_mod_cast (by omega : 2*X-1+1=2*X)

theorem exact_taper_smooth_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ), 32 ≤ X → ∀ (β : ℝ) (s : ℂ), 0 ≤ s.re →
      ‖weightedTaperTransform X (2*X-1) (fun n => scaledWeight X n) β s -
        smoothTransform X (2*(X:ℝ)) β (scaledWeight X) s‖ ≤
      (2*(X:ℝ))^s.re * (C / (X:ℝ)^2) := by
  obtain ⟨M,hM,hder⟩ := weight_derivative_bound 2
  have hdd (t : ℝ) : ‖deriv (deriv weight) t‖ ≤ M := by
    have he : iteratedDeriv 2 weight = deriv (deriv weight) := by
      change iteratedDeriv (1+1) weight = _
      rw [iteratedDeriv_succ, show (1:ℕ)=0+1 by decide, iteratedDeriv_succ, iteratedDeriv_zero]
    exact he ▸ hder t
  refine ⟨2*M, by positivity, ?_⟩
  intro X hX β s hs
  have hx : (32:ℝ) ≤ X := by exact_mod_cast hX
  have hx0 : 0 < (X : ℝ) := by linarith
  have hb := constant_scaled_endpoint (show 1 ≤ X by omega)
  have hL : ∀ t ∈ Set.Icc (X:ℝ) ((X:ℝ)+1), weight (t/(X:ℝ)) = 0 := by
    intro t ht
    apply weight_zero
    exact Or.inl ((div_le_iff₀ hx0).mpr (by linarith [ht.2]))
  have hR : weight ((((2*X-1+1:ℕ):ℝ))/(X:ℝ)) = 0 := by
    rw [Nat.cast_add,Nat.cast_one,hb,mul_div_cancel_right₀]
    · exact weight_zero (Or.inr (by norm_num))
    · exact hx0.ne'
  have h := exact_weighted_transform_approx (a := X) (b := 2*X-1) (by omega)
    weight_smooth hM hdd hx0 le_rfl hb.le hL hR β s hs
  rw [hb] at h
  unfold smoothTransform scaledWeight
  exact h.trans_eq (mul_comm _ _)

end GoldbachCorrectionBands

end


section

namespace GoldbachSpectralGeometry

open Finset

noncomputable def profileHeight (x P r : ℝ) : ℝ := 32 * x^(17/200 : ℝ) * P / r

noncomputable def outerHeight (x : ℝ) : ℝ := x^(1/2 : ℝ)

noncomputable def angularRadius (x P r : ℝ) : ℝ := 2 * Real.pi * (P / (r * (4*x)))

theorem profile_heights {x P r : ℝ} (hx : (2:ℝ)^200 ≤ x)
    (hr : 1 ≤ r) (hrP : r ≤ P) (hP : P ≤ 4 * x^(41/200 : ℝ)) :
    let H := profileHeight x P r
    let J := outerHeight x
    let R := angularRadius x P r
    1 ≤ x ∧ 0 ≤ R ∧ x^(17/200 : ℝ) ≤ H ∧ 1 ≤ H ∧ H ≤ J ∧ 4*x*R ≤ H := by
  dsimp only
  have hx1 : 1 ≤ x := (by norm_num : (1:ℝ) ≤ 2^200).trans hx
  have hxp : 0 < x := zero_lt_one.trans_le hx1
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hPp : 0 < P := hrp.trans_le hrP
  have hΓ : (1:ℝ) ≤ x^(17/200 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hhr : x^(17/200 : ℝ) ≤ profileHeight x P r := by
    apply (le_div_iff₀ hrp).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hrP (show 0 ≤ x^(17/200 : ℝ) by positivity),
      show 0 ≤ x^(17/200 : ℝ) * P by positivity]
  have hLo : (128:ℝ) ≤ x^(21/100 : ℝ) := calc
    _ ≤ (2:ℝ)^((200:ℝ)*(21/100)) := by
      norm_num [show ((200:ℝ)*(21/100)) = (42:ℕ) by norm_num, Real.rpow_natCast]
    _ = ((2:ℝ)^200)^(21/100 : ℝ) := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have hHJ : profileHeight x P r ≤ outerHeight x := by
    calc
      _ ≤ 32 * x^(17/200 : ℝ) * P := div_le_self (by positivity) hr
      _ ≤ 32 * x^(17/200 : ℝ) * (4 * x^(41/200 : ℝ)) :=
        mul_le_mul_of_nonneg_left hP (by positivity)
      _ = 128 * x^(29/100 : ℝ) := by
        rw [show 32 * x^(17/200 : ℝ) * (4 * x^(41/200 : ℝ)) =
          128 * (x^(17/200 : ℝ) * x^(41/200 : ℝ)) by ring, ← Real.rpow_add hxp]
        norm_num
      _ ≤ x^(21/100 : ℝ) * x^(29/100 : ℝ) :=
        mul_le_mul_of_nonneg_right hLo (by positivity)
      _ = _ := by rw [← Real.rpow_add hxp]; norm_num [outerHeight]
  refine ⟨hx1, by unfold angularRadius; positivity, hhr, hΓ.trans hhr, hHJ, ?_⟩
  have hR : 4*x*angularRadius x P r = (2*Real.pi)*P/r := by
    unfold angularRadius
    field_simp
  rw [hR]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by nlinarith only [hΓ,Real.pi_lt_four]) hPp.le) hrp.le

end GoldbachSpectralGeometry

end


section

namespace GoldbachDensitySlices

open Finset Set Complex Goldbach GoldbachTwistedMellin

noncomputable section

private theorem logHeight_le_of_level_and_ordinate {q Q : ℕ} [NeZero q]
    {s t : ℝ} (hqQ : q ≤ Q) (h : |s| ≤ |t|) : logHeight q s ≤ logHeight Q t := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqQ' : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  unfold logHeight
  apply Real.log_le_log (by positivity)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hqQ' (by norm_num)) (by linarith only [h])
    (by positivity) (by positivity)

theorem exceptional_subset_geometry {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {B : ℝ} {Z : Finset ℂ}
    (hZ : Z ⊆ exceptionalZeros χ B) :
    ∀ z ∈ Z, 1/2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ B ∧ regularizedL χ z = 0 := by
  intro z hz
  obtain ⟨hl, ht, hzero⟩ := (mem_exceptionalZeros χ B z).mp (hZ hz)
  refine ⟨hl.le, le_of_not_gt ?_, ht, hzero⟩
  intro h
  exact (regularizedL_ne_zero_right χ (by linarith only [h])) hzero

/-- A unit interval on the signed ordinate axis has logarithmically bounded total order. -/
theorem unit_height_multiplicity_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Q : ℕ), q ≤ Q →
        ∀ (T : ℝ), 0 ≤ T → ∀ (Z : Finset ℂ),
        (∀ z ∈ Z, 1/2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ T) →
        ∀ y : ℝ,
          (∑ z ∈ Z.filter (fun z => y ≤ z.im ∧ z.im ≤ y + 1),
            (analyticOrderNatAt (regularizedL χ) z : ℝ)) ≤ C * logHeight Q (T+2) := by
  classical
  obtain ⟨C, hC, hslice⟩ := unconditional_right_slice_count
  refine ⟨C, hC, ?_⟩
  intro q _ χ Q hqQ T hT Z hZ y
  let S := Z.filter (fun z => y ≤ z.im ∧ z.im ≤ y+1)
  change (∑ z ∈ S, (analyticOrderNatAt (regularizedL χ) z : ℝ)) ≤ _
  by_cases hs : S.Nonempty
  · obtain ⟨z,hz⟩ := hs
    have hz' := mem_filter.mp hz
    have hzT := abs_le.mp (hZ z hz'.1).2.2
    have hwindow := hz'.2
    have hy : |y+1/2| ≤ |T+2| := by
      rw [abs_of_nonneg (by linarith only [hT] : 0 ≤ T+2)]
      exact abs_le.mpr ⟨by linarith only [hwindow.2, hzT.1], by linarith only [hwindow.1, hzT.2]⟩
    have hmem (w : ℂ) (hw : w ∈ S) : 1/2 ≤ w.re ∧ w.re ≤ 2 ∧ |w.im-(y+1/2)| ≤ 1 := by
      obtain ⟨hwZ, hwl, hwh⟩ := mem_filter.mp hw
      exact ⟨(hZ w hwZ).1, (hZ w hwZ).2.1, abs_le.mpr ⟨by linarith only [hwl], by linarith only [hwh]⟩⟩
    exact (hslice q χ (y+1/2) S hmem).trans
      (mul_le_mul_of_nonneg_left (logHeight_le_of_level_and_ordinate hqQ hy) hC.le)
  · have : NeZero Q := ⟨((NeZero.pos q).trans_le hqQ).ne'⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty]
    exact mul_nonneg hC.le (zero_le_one.trans (logHeight_ge_one Q _))

/-- The order at any one point of the strip is bounded by the same local estimate. -/
theorem individual_multiplicity_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Q : ℕ), q ≤ Q →
        ∀ (T : ℝ), 0 ≤ T → ∀ (Z : Finset ℂ),
        (∀ z ∈ Z, 1/2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ T) →
        ∀ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z : ℝ) ≤ C * logHeight Q (T+2) := by
  classical
  obtain ⟨C,hC,hunit⟩ := unit_height_multiplicity_bound
  refine ⟨C,hC,?_⟩
  intro q _ χ Q hqQ T hT Z hZ z hz
  let S := Z.filter (fun w => z.im ≤ w.im ∧ w.im ≤ z.im+1)
  have hzS : z ∈ S := mem_filter.mpr ⟨hz,le_rfl,by linarith⟩
  exact (Finset.single_le_sum (s := S) (fun _ _ => Nat.cast_nonneg _ : ∀ w ∈ S,
        0 ≤ (analyticOrderNatAt (regularizedL χ) w : ℝ)) hzS).trans
    (hunit q χ Q hqQ T hT Z hZ z.im)

/-- Partition an ordinate interval of length at most `K` into at most `K`
signed unit intervals. The upper endpoint is open for the covering assertion. -/
private theorem interval_weight_le {ι : Type*} (Z : Finset ι) (ordinate : ι → ℝ)
    (weight : ι → ℝ) {a B : ℝ} {K : ℕ} (hweight : ∀ z ∈ Z, 0 ≤ weight z)
    (hcover : ∀ z ∈ Z, a ≤ ordinate z ∧ ordinate z < a + (K : ℝ))
    (hunit : ∀ y : ℝ, (∑ z ∈ Z.filter (fun z => y ≤ ordinate z ∧ ordinate z ≤ y+1),
      weight z) ≤ B) :
    (∑ z ∈ Z, weight z) ≤ (K : ℝ) * B := by
  let k := fun z => ⌊ordinate z-a⌋₊
  have hk (z) (hz : z ∈ Z) : k z ∈ range K := by
    have ht := hcover z hz
    have hfloor : (k z : ℝ) ≤ ordinate z-a := Nat.floor_le (sub_nonneg.mpr ht.1)
    have hlt : (k z : ℝ) < K := hfloor.trans_lt (by linarith only [ht.2])
    exact mem_range.mpr (by exact_mod_cast hlt)
  have hsub (j : ℕ) : Z.filter (fun z => k z = j) ⊆
      Z.filter (fun z => a+(j:ℝ) ≤ ordinate z ∧ ordinate z ≤ (a+(j:ℝ))+1) := by
    intro z hz
    obtain ⟨hzZ,hzj⟩ := mem_filter.mp hz
    have hlo : (k z : ℝ) ≤ ordinate z-a := Nat.floor_le (sub_nonneg.mpr (hcover z hzZ).1)
    have hhi : ordinate z-a < (k z : ℝ)+1 := Nat.lt_floor_add_one _
    rw [hzj] at hlo hhi
    exact mem_filter.mpr ⟨hzZ,by linarith only [hlo],by linarith only [hhi]⟩
  rw [← Finset.sum_fiberwise_of_maps_to hk]
  calc
    _ ≤ ∑ _j ∈ range K, B := by
      apply sum_le_sum
      intro j _
      exact (sum_le_sum_of_subset_of_nonneg (hsub j)
        (fun z hz _ => hweight z (mem_filter.mp hz).1)).trans (hunit (a+(j:ℝ)))
    _ = _ := by simp

/-- An interval of heights `[-H,H]` has total multiplicity `O((H+1) logHeight Q (H+2))`. -/
theorem total_multiplicity_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Q : ℕ), q ≤ Q →
        ∀ (H : ℝ), 0 ≤ H → ∀ (Z : Finset ℂ),
        (∀ z ∈ Z, 1/2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ H) →
        (∑ z ∈ Z, (analyticOrderNatAt (regularizedL χ) z : ℝ)) ≤
          C * (H+1) * logHeight Q (H+2) := by
  obtain ⟨C,hC,hunit⟩ := unit_height_multiplicity_bound
  refine ⟨2*C,by positivity,?_⟩
  intro q _ χ Q hqQ H hH Z hZ
  let K := ⌊2*H⌋₊ + 1
  have : NeZero Q := ⟨((NeZero.pos q).trans_le hqQ).ne'⟩
  have hKlow : 2*H < (K:ℝ) := by
    simpa only [K,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (2*H)
  have hKhigh : (K:ℝ) ≤ 2*(H+1) := by
    have h := Nat.floor_le (show 0 ≤ 2*H by positivity)
    simp only [K,Nat.cast_add,Nat.cast_one]
    linarith only [h]
  have hlog : 0 ≤ logHeight Q (H+2) := zero_le_one.trans (logHeight_ge_one Q _)
  have hc := interval_weight_le Z Complex.im (fun z => (analyticOrderNatAt (regularizedL χ) z : ℝ))
    (a := -H) (K := K) (B := C*logHeight Q (H+2)) (fun _ _ => Nat.cast_nonneg _)
    (fun z hz => by
      have h := abs_le.mp (hZ z hz).2.2
      exact ⟨h.1,by linarith only [h.2,hKlow]⟩)
    (hunit q χ Q hqQ H hH Z hZ)
  calc
    _ ≤ (K:ℝ)*(C*logHeight Q (H+2)) := hc
    _ ≤ (2*(H+1))*(C*logHeight Q (H+2)) :=
      mul_le_mul_of_nonneg_right hKhigh (mul_nonneg hC.le hlog)
    _ = _ := by ring

/-- A unit interval for `-Im z/(2π)` is covered by eight signed ordinate intervals. -/
theorem normalized_unit_height_card_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Q : ℕ), q ≤ Q →
        ∀ (T : ℝ), 0 ≤ T → ∀ (Z : Finset ℂ),
        (∀ z ∈ Z, 1/2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ T ∧ regularizedL χ z = 0) →
        ∀ y : ℝ,
          ((Z.filter (fun z => y ≤ -z.im/(2*Real.pi) ∧ -z.im/(2*Real.pi) ≤ y+1)).card : ℝ) ≤
            C * logHeight Q (T+2) := by
  obtain ⟨C,hC,hunit⟩ := unit_height_multiplicity_bound
  refine ⟨8*C,by positivity,?_⟩
  intro q _ χ Q hqQ T hT Z hZ y
  let S := Z.filter (fun z => y ≤ -z.im/(2*Real.pi) ∧ -z.im/(2*Real.pi) ≤ y+1)
  let a := -(y+1)*(2*Real.pi)
  have hpi : 0 < 2*Real.pi := by positivity [Real.pi_pos]
  have hcover (z : ℂ) (hz : z ∈ S) : a ≤ z.im ∧ z.im < a+((8:ℕ):ℝ) := by
    obtain ⟨_,hl,hr⟩ := mem_filter.mp hz
    have h₁ := (le_div_iff₀ hpi).1 hl
    have h₂ := (div_le_iff₀ hpi).1 hr
    dsimp only [a]
    constructor
    · linarith only [h₂]
    · norm_num
      linarith only [h₁,Real.pi_lt_four]
  have hs (z : ℂ) (hz : z ∈ S) : 1/2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ T := by
    obtain ⟨hl,hr,ht,_⟩ := hZ z (mem_filter.mp hz).1
    exact ⟨hl,hr,ht⟩
  have ht := interval_weight_le S Complex.im (fun z => (analyticOrderNatAt (regularizedL χ) z : ℝ))
    (K := 8) (B := C*logHeight Q (T+2)) (fun _ _ => Nat.cast_nonneg _) hcover
    (hunit q χ Q hqQ T hT S hs)
  have hcard : (S.card : ℝ) ≤ ∑ z ∈ S, (analyticOrderNatAt (regularizedL χ) z : ℝ) := by
    calc
      _ = ∑ _z ∈ S, (1:ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro z hz
        exact_mod_cast (regularizedL_analyticOrderNatAt_pos_iff χ z).2
          (hZ z (mem_filter.mp hz).1).2.2.2
  calc
    _ ≤ ((8:ℕ):ℝ)*(C*logHeight Q (T+2)) := hcard.trans ht
    _ = _ := by norm_num; ring

end
end GoldbachDensitySlices

end

section

namespace GoldbachCorrectionCounts

open Finset Goldbach GoldbachTwistedMellin GoldbachDensitySlices

theorem log_height_le {X : ℕ} (hX : 1 ≤ X) {T : ℝ} (hT : 0 ≤ T)
    (hcut : T ≤ heightCut (X : ℝ)) :
    logHeight X (T + 2) ≤ 530 * (1 + Real.log (X : ℝ)) := by
  let x : ℝ := X
  have hx : 1 ≤ x := by dsimp only [x]; exact_mod_cast hX
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hx8 : 1 ≤ x ^ 8 := one_le_pow₀ hx
  change Real.log (2 * x * (2 + |T+2|)) ≤ 530 * (1 + Real.log x)
  rw [abs_of_nonneg (by linarith only [hT])]
  have he : heightCut (X : ℝ) = 256 * x ^ 8 := by unfold heightCut; ring
  have harg : 2*x*(2+(T+2)) ≤ 520 * x^9 := by
    rw [he] at hcut
    calc
      _ ≤ (2*x)*(260*x^8) := mul_le_mul_of_nonneg_left (by linarith only [hcut,hx8]) (by positivity)
      _ = _ := by ring
  refine (Real.log_le_log (by positivity) harg).trans ?_
  rw [Real.log_mul (by norm_num : (520:ℝ) ≠ 0) (by positivity : x^9 ≠ 0), Real.log_pow]
  have hbase := Real.log_le_sub_one_of_pos (show (0:ℝ) < 520 by norm_num)
  norm_num at hbase ⊢
  linarith only [Real.log_nonneg hx,hbase]

theorem uniform_exception_counts :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ), 1 ≤ X → ∀ (q : ℕ) [NeZero q], q ≤ X →
      ∀ (χ : DirichletCharacter ℂ q),
      let S := exceptionalZeros χ (heightCut (X : ℝ))
      let c z := (analyticOrderNatAt (regularizedL χ) z : ℂ)
      let B := C * (1 + Real.log (X : ℝ))
      (∀ t : ℝ, (∑ z ∈ S.filter (fun z => t ≤ z.im ∧ z.im ≤ t + 1), ‖c z‖) ≤ B) ∧
      (∀ t : ℝ, ((S.filter (fun z => t ≤ -z.im/(2*Real.pi) ∧ -z.im/(2*Real.pi) ≤ t+1)).card : ℝ) ≤ B) ∧
      (∀ J : ℝ, 0 ≤ J → J ≤ heightCut (X : ℝ) →
        (∑ z ∈ S.filter (fun z => |z.im| < J), ‖c z‖) ≤ B*(J+1)) := by
  obtain ⟨A,hA,hunit⟩ := unit_height_multiplicity_bound
  obtain ⟨D,hD,hcard⟩ := normalized_unit_height_card_bound
  obtain ⟨E,hE,hmass⟩ := total_multiplicity_bound
  refine ⟨530*(A+D+E), by positivity, ?_⟩
  intro X hX q _ hq χ
  dsimp only
  let τ := heightCut (X : ℝ)
  let S := exceptionalZeros χ τ
  have hτ : 0 ≤ τ := by dsimp only [τ,heightCut]; positivity
  have hx : (1:ℝ) ≤ X := by exact_mod_cast hX
  let M := 1 + Real.log (X : ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity [Real.log_nonneg hx]
  have ho (z : ℂ) : ‖(analyticOrderNatAt (regularizedL χ) z : ℂ)‖ =
      (analyticOrderNatAt (regularizedL χ) z : ℝ) := Complex.norm_natCast _
  have hs := exceptional_subset_geometry χ (B := τ) (Z := S) (fun _ h => h)
  have hs' (z : ℂ) (hz : z ∈ S) : 1/2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ τ :=
    ⟨(hs z hz).1,(hs z hz).2.1,(hs z hz).2.2.1⟩
  have hlog := log_height_le hX hτ (le_refl τ)
  refine ⟨?_,?_,?_⟩
  · intro t
    simp_rw [ho]
    exact (hunit q χ X hq τ hτ S hs' t).trans <|
      (mul_le_mul_of_nonneg_left hlog hA.le).trans (by dsimp only [M] at hM ⊢; nlinarith)
  · intro t
    exact (hcard q χ X hq τ hτ S hs t).trans <|
      (mul_le_mul_of_nonneg_left hlog hD.le).trans (by dsimp only [M] at hM ⊢; nlinarith)
  · intro J hJ hJτ
    simp_rw [ho]
    have hm := hmass q χ X hq J hJ (S.filter (fun z => |z.im| < J)) (fun z h => by
      obtain ⟨hz, hj⟩ := mem_filter.mp h
      exact ⟨(hs z hz).1,(hs z hz).2.1,hj.le⟩)
    refine hm.trans ?_
    calc
      _ ≤ (E * (J+1)) * (530*M) :=
        mul_le_mul_of_nonneg_left (log_height_le hX hJ hJτ) (by positivity)
      _ = (530*E*M)*(J+1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp only [M] at hM ⊢; nlinarith) (by positivity)

end GoldbachCorrectionCounts

end

section


namespace GoldbachExceptionalTail

open Finset

theorem laplace_tail_of_measured_count {ι : Type*} (S : Finset ι) (height c : ι → ℝ)
    {a L C : ℝ} (ha : a < 1) (hC : 0 ≤ C) (hc : ∀ j ∈ S, 0 ≤ c j)
    (hcount : ∀ b ≥ L, (∑ j ∈ S.filter (fun j => height j ≤ b), c j) ≤ C * Real.exp (a*b)) :
    (∑ j ∈ S.filter (fun j => L ≤ height j), c j * Real.exp (-height j)) ≤
      C * Real.exp (a + (a-1)*L) / (1 - Real.exp (a-1)) := by
  classical
  let T := S.filter (fun j => L ≤ height j)
  let bin (j : ι) : ℕ := ⌊height j - L⌋₊
  let B := T.image bin
  let r := Real.exp (a-1)
  let A := C * Real.exp (a+(a-1)*L)
  have hA : 0 ≤ A := mul_nonneg hC (Real.exp_pos _).le
  have hr₀ : 0 ≤ r := (Real.exp_pos _).le
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hmap : (T : Set ι).MapsTo bin B := fun j hj => mem_image_of_mem _ hj
  have hbin (k : ℕ) (j : ι) (hj : j ∈ T.filter (fun j => bin j = k)) :
      L + (k : ℝ) ≤ height j ∧ height j ≤ L + k + 1 := by
    obtain ⟨hjT, hk⟩ := mem_filter.mp hj
    have hjL := (mem_filter.mp hjT).2
    have h₀ : (bin j : ℝ) ≤ height j - L := Nat.floor_le (sub_nonneg.mpr hjL)
    have h₁ : height j - L < (bin j : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [hk] at h₀ h₁
    exact ⟨by linarith, by linarith⟩
  have hmass (k : ℕ) : (∑ j ∈ T.filter (fun j => bin j = k), c j) ≤
      C * Real.exp (a*(L+k+1)) := by
    have hsub : T.filter (fun j => bin j = k) ⊆ S.filter (fun j => height j ≤ L+k+1) := by
      intro j hj
      exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hj).1).1, (hbin k j hj).2⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => hc j (mem_filter.mp hj).1)).trans
      (hcount _ (by linarith [Nat.cast_nonneg (α := ℝ) k]))
  have hgeom := hasSum_geometric_of_lt_one hr₀ hr₁
  change (∑ j ∈ T, c j * Real.exp (-height j)) ≤ A/(1-r)
  calc
    _ = ∑ k ∈ B, ∑ j ∈ T.filter (fun j => bin j = k), c j * Real.exp (-height j) :=
      (sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ k ∈ B, A * r^k := by
      apply sum_le_sum
      intro k _
      calc
        _ ≤ ∑ j ∈ T.filter (fun j => bin j = k), c j * Real.exp (-(L+k)) := by
          apply sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg (hbin k j hj).1))
            (hc j (mem_filter.mp (mem_filter.mp hj).1).1)
        _ = (∑ j ∈ T.filter (fun j => bin j = k), c j) * Real.exp (-(L+k)) := by
          rw [sum_mul]
        _ ≤ (C * Real.exp (a*(L+k+1))) * Real.exp (-(L+k)) :=
          mul_le_mul_of_nonneg_right (hmass k) (Real.exp_pos _).le
        _ = A * r^k := by
          dsimp only [A,r]
          simp only [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
          congr 2
          ring
    _ = A * ∑ k ∈ B, r^k := by rw [mul_sum]
    _ ≤ _ := by
      rw [div_eq_mul_inv, ← hgeom.tsum_eq]
      exact mul_le_mul_of_nonneg_left (hgeom.summable.sum_le_tsum _ (fun _ _ => by positivity)) hA

theorem measured_density_sum_le {ι : Type*} (S : Finset ι) (b c : ι → ℝ) {X d H a K : ℝ}
    (hX : 1 < X) (hdH : d ≤ H) (ha₀ : 0 ≤ a) (ha₁ : a < 1) (hK : 0 ≤ K)
    (hc : ∀ i ∈ S, 0 ≤ c i) (hstrip : ∀ i ∈ S, 1-H ≤ b i ∧ b i ≤ 1-d)
    (hdensity : ∀ h ∈ Set.Icc d H,
      (∑ i ∈ S.filter (fun i => 1 - h ≤ b i), c i) ≤ K * X^(2*a*h)) :
    (∑ i ∈ S, c i * X^(2*b i-1)) ≤
      (K*Real.exp a/(1-Real.exp (a-1))) * X^(1-2*(1-a)*d) := by
  classical
  let g : ℝ := 2 * Real.log X
  have hg : 0 < g := mul_pos (by norm_num) (Real.log_pos hX)
  have hXp : 0 < X := zero_lt_one.trans hX
  let gapHeight (i : ι) := (1-b i) * g
  have hL (i : ι) (hi : i ∈ S) : d*g ≤ gapHeight i :=
    mul_le_mul_of_nonneg_right (by linarith [(hstrip i hi).2]) hg.le
  have hfilter : S.filter (fun i => d*g ≤ gapHeight i) = S := Finset.filter_eq_self.mpr hL
  have hcount (t : ℝ) (ht : d*g ≤ t) :
      (∑ i ∈ S.filter (fun i => gapHeight i ≤ t), c i) ≤ K * Real.exp (a*t) := by
    let h := min H (t/g)
    have hdh : d ≤ h := le_min hdH ((le_div_iff₀ hg).mpr ht)
    have hhH : h ≤ H := min_le_left _ _
    have hsub : S.filter (fun i => gapHeight i ≤ t) ⊆ S.filter (fun i => 1-h ≤ b i) := by
      intro i hi
      obtain ⟨hiS, hgap⟩ := mem_filter.mp hi
      have hratio : 1-b i ≤ t/g := (le_div_iff₀ hg).mpr hgap
      have hi' : 1 - b i ≤ h := le_min (by linarith [(hstrip i hiS).1]) hratio
      exact mem_filter.mpr ⟨hiS, by linarith⟩
    have hmass := sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hc i (mem_filter.mp hi).1)
    refine hmass.trans ((hdensity h ⟨hdh, hhH⟩).trans ?_)
    apply mul_le_mul_of_nonneg_left _ hK
    rw [Real.rpow_def_of_pos hXp]
    apply Real.exp_le_exp.mpr
    have hht : h * g ≤ t := (le_div_iff₀ hg).mp (min_le_right _ _)
    have hpp := mul_le_mul_of_nonneg_left hht ha₀
    dsimp only [g] at hpp
    nlinarith only [hpp]
  have ht := laplace_tail_of_measured_count S gapHeight c ha₁ hK hc hcount
  rw [hfilter] at ht
  have he (i : ι) : X^(2*b i-1) = X * Real.exp (-gapHeight i) := by
    calc
      _ = Real.exp (Real.log X - gapHeight i) := by
        rw [Real.rpow_def_of_pos hXp]
        congr 1
        dsimp only [gapHeight,g]
        ring
      _ = _ := by rw [Real.exp_sub, Real.exp_log hXp, Real.exp_neg, div_eq_mul_inv]
  have hE : X * Real.exp ((a-1)*(d*g)) = X^(1-2*(1-a)*d) := by
    rw [Real.rpow_def_of_pos hXp]
    calc
      _ = Real.exp (Real.log X) * Real.exp ((a-1)*(d*g)) := by rw [Real.exp_log hXp]
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [g]
        ring
  calc
    _ = X * ∑ i ∈ S, c i * Real.exp (-gapHeight i) := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ => by rw [he]; ring
    _ ≤ X * (K * Real.exp (a+(a-1)*(d*g))/(1-Real.exp (a-1))) :=
      mul_le_mul_of_nonneg_left ht hXp.le
    _ = (K*Real.exp a/(1-Real.exp (a-1))) * (X * Real.exp ((a-1)*(d*g))) := by
      rw [Real.exp_add]
      ring
    _ = _ := by rw [hE]

theorem logarithmic_gap_factor {X c a : ℝ} (hX : 1 < X) :
    X^(1-2*(1-a)*(c*Real.log (Real.log X)/Real.log X)) =
      X * (Real.log X)^(-2*(1-a)*c) := by
  have hp := Real.log_pos hX
  have hx0 := zero_lt_one.trans hX
  rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hp]
  calc
    _ = Real.exp (Real.log X + Real.log (Real.log X) * (-2*(1-a)*c)) := by
      congr 1
      field_simp
      ring
    _ = _ := by rw [Real.exp_add, Real.exp_log hx0]

end GoldbachExceptionalTail
end

section

section


section


section


section


namespace GoldbachPrincipalSeries

open Filter Finset Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc
open scoped ComplexConjugate Classical

theorem norm_ram_le_gcd (q m : ℕ) : ‖ram q m‖ ≤ (q.gcd m : ℝ) := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ j =>
      have hpow : p ^ j ∣ p ^ (j + 1) := pow_dvd_pow p (Nat.le_succ j)
      have hpos := Nat.gcd_pos_of_pos_left m (pow_pos hp.pos (j + 1))
      rw [ram_primePower p j m hp]
      by_cases h : p ^ (j + 1) ∣ m
      · rw [ite_eq_left h, ite_eq_left (hpow.trans h)]
        have hcast : (((p ^ (j + 1) : ℕ) : ℂ) - ((p ^ j : ℕ) : ℂ)) =
            Complex.ofReal (((p ^ (j + 1) : ℕ) : ℝ) - ((p ^ j : ℕ) : ℝ)) := by
          simp [Complex.ofReal_sub]
        have hle : ((p ^ j : ℕ) : ℝ) ≤ ((p ^ (j + 1) : ℕ) : ℝ) := by
          exact_mod_cast Nat.pow_le_pow_right hp.pos (Nat.le_succ j)
        have hnrm : ‖Complex.ofReal (((p ^ (j + 1) : ℕ) : ℝ) - ((p ^ j : ℕ) : ℝ))‖ =
            (((p ^ (j + 1) : ℕ) : ℝ) - ((p ^ j : ℕ) : ℝ)) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)]
        have hg : ((p ^ (j + 1) : ℕ) : ℝ) ≤ ((p ^ (j + 1)).gcd m : ℝ) := by
          exact_mod_cast Nat.le_of_dvd hpos (Nat.dvd_gcd dvd_rfl h)
        exact (congrArg norm hcast).trans_le (hnrm.trans_le
          (by linarith [Nat.cast_nonneg (α := ℝ) (p ^ j)]))
      · rw [ite_eq_right h]
        by_cases h' : p ^ j ∣ m
        · rw [ite_eq_left h', zero_sub, norm_neg, Complex.norm_natCast]
          exact_mod_cast Nat.le_of_dvd hpos (Nat.dvd_gcd hpow h')
        · simp [h']
  | coprime q r hq hr hc ihq ihr =>
    have hg : (q * r).gcd m = q.gcd m * r.gcd m := by
      calc
        _ = m.gcd (q * r) := Nat.gcd_comm _ _
        _ = m.gcd q * m.gcd r := hc.gcd_mul m
        _ = _ := by rw [Nat.gcd_comm m q, Nat.gcd_comm m r]
    rw [ram_mul (by omega) (by omega) hc, norm_mul, hg, Nat.cast_mul]
    exact mul_le_mul ihq ihr (norm_nonneg _) (Nat.cast_nonneg _)

private theorem inv_totient_bound {q : ℕ} (hq : 0 < q) :
    (q.totient : ℝ)⁻¹ ≤ 40 * (q : ℝ) ^ (-7 / 8 : ℝ) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have ht := DeepThreeQuarters.totient_ratio_le_rpow (ε := 1 / 8)
    (by norm_num) q hq
  norm_num at ht
  have hφ : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  calc
    (q.totient : ℝ)⁻¹ = ((q : ℝ) / (q.totient : ℝ)) / (q : ℝ) := by
      field_simp [hφ, hqR.ne']
    _ ≤ (40 * (q : ℝ) ^ (1 / 8 : ℝ)) / (q : ℝ) :=
      div_le_div_of_nonneg_right (by simpa using ht) hqR.le
    _ = _ := by
      rw [mul_div_assoc, ← Real.rpow_sub_one hqR.ne']
      norm_num

theorem coefficient_norm_le {q m : ℕ} (hq : 0 < q) :
    ‖coefficient q m‖ ≤ 1600 * (q.gcd m : ℝ) * (q : ℝ) ^ (-7 / 4 : ℝ) := by
  have hunit : ‖ram q 1‖ ≤ 1 := by simpa using norm_ram_le_gcd q 1
  have ht : 0 ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  have hu : ‖ram q 1‖ / (q.totient : ℝ) ≤ 40 * (q : ℝ) ^ (-7 / 8 : ℝ) := by
    apply (div_le_div_of_nonneg_right hunit ht).trans
    rw [one_div]
    exact inv_totient_bound hq
  rw [coefficient, norm_mul, norm_pow, norm_div, Complex.norm_natCast, Complex.norm_conj]
  calc
    _ ≤ (40 * (q : ℝ) ^ (-7 / 8 : ℝ)) ^ 2 * (q.gcd m : ℝ) :=
      mul_le_mul (pow_le_pow_left₀ (div_nonneg (norm_nonneg _) ht) hu 2)
        (norm_ram_le_gcd q m) (norm_nonneg _) (sq_nonneg _)
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg q)]
      norm_num
      ring

private noncomputable def seriesBudget : ℝ := ∑' k : ℕ, (k : ℝ) ^ (-5 / 4 : ℝ)

private theorem seriesBudget_nonneg : 0 ≤ seriesBudget :=
  tsum_nonneg fun k => Real.rpow_nonneg (Nat.cast_nonneg k) _

private theorem multiple_sum_bound (s : Finset ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ q ∈ s.filter (fun q => d ∣ q), (d : ℝ) * (q : ℝ) ^ (-5 / 4 : ℝ)) ≤ seriesBudget := by
  let A := s.filter (fun q => d ∣ q)
  have hinj : Set.InjOn (fun q : ℕ => q / d) (A : Set ℕ) := by
    intro q hq r hr h
    have hq' : d ∣ q := (Finset.mem_filter.mp hq).2
    have hr' : d ∣ r := (Finset.mem_filter.mp hr).2
    change q / d = r / d at h
    rw [← Nat.div_mul_cancel hq', ← Nat.div_mul_cancel hr', h]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdR' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hf (q : ℕ) (hq : q ∈ A) :
      (d : ℝ) * (q : ℝ) ^ (-5 / 4 : ℝ) ≤ ((q / d : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
    have hq' : d ∣ q := (Finset.mem_filter.mp hq).2
    let k := q / d
    have hcast : (q : ℝ) = (d : ℝ) * (k : ℝ) := by
      exact_mod_cast (by rw [mul_comm, Nat.div_mul_cancel hq'] : q = d * (q / d))
    change (d : ℝ) * (q : ℝ) ^ (-5 / 4 : ℝ) ≤ (k : ℝ) ^ (-5 / 4 : ℝ)
    rw [hcast, Real.mul_rpow hdR.le (Nat.cast_nonneg k), ← mul_assoc]
    have he : (d : ℝ) * (d : ℝ) ^ (-5 / 4 : ℝ) = (d : ℝ) ^ (-1 / 4 : ℝ) := by
      nth_rw 1 [← Real.rpow_one (d : ℝ)]
      rw [← Real.rpow_add hdR]
      norm_num
    rw [he]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg k) _)
      (Real.rpow_le_one_of_one_le_of_nonpos hdR' (by norm_num))
  have hsum : Summable (fun k : ℕ => (k : ℝ) ^ (-5 / 4 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  calc
    _ ≤ ∑ q ∈ A, ((q / d : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := Finset.sum_le_sum hf
    _ = ∑ k ∈ A.image (fun q => q / d), (k : ℝ) ^ (-5 / 4 : ℝ) := by
      exact (Finset.sum_image (f := fun k : ℕ => (k : ℝ) ^ (-5 / 4 : ℝ)) hinj).symm
    _ ≤ seriesBudget := hsum.sum_le_tsum _ (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _)

private theorem sum_gcd_decay_le (s : Finset ℕ) {m : ℕ} (hm : 0 < m) :
    (∑ q ∈ s, (q.gcd m : ℝ) * (q : ℝ) ^ (-5 / 4 : ℝ)) ≤
      (m.divisors.card : ℝ) * seriesBudget := by
  have hsum (q : ℕ) :
      (q.gcd m : ℝ) ≤ ∑ d ∈ m.divisors.filter (fun d => d ∣ q), (d : ℝ) := by
    apply Finset.single_le_sum (f := fun d : ℕ => (d : ℝ)) (fun d _ => Nat.cast_nonneg _)
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right q m, hm.ne'⟩, Nat.gcd_dvd_left q m⟩
  calc
    _ ≤ ∑ q ∈ s, (∑ d ∈ m.divisors.filter (fun d => d ∣ q), (d : ℝ)) *
        (q : ℝ) ^ (-5 / 4 : ℝ) := by
      exact Finset.sum_le_sum fun q _ =>
        mul_le_mul_of_nonneg_right (hsum q) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
    _ = ∑ d ∈ m.divisors, ∑ q ∈ s.filter (fun q => d ∣ q),
        (d : ℝ) * (q : ℝ) ^ (-5 / 4 : ℝ) := by
      simp_rw [Finset.sum_filter, Finset.sum_mul, ite_mul, zero_mul]
      exact Finset.sum_comm
    _ ≤ ∑ _d ∈ m.divisors, seriesBudget := Finset.sum_le_sum fun d hd =>
      multiple_sum_bound s (Nat.pos_of_mem_divisors hd)
    _ = _ := by simp [nsmul_eq_mul]

/-- Divisor growth estimate from the verified B13 far-inner arithmetic cuts,
adapted there from goldbach-proofs PR #2468, revision
3d9be84b446f4e30f46b52e1c83dc7e49e4535d9 (Apache-2.0). -/
private theorem divisorPower (K : ℕ) (hK : 0<K) :
    ∃ C : ℝ,1≤C ∧ ∀ n : ℕ, 0<n → (n.divisors.card:ℝ)^K ≤ C*n := by
  have hl := (isLittleO_pow_const_const_pow_of_one_lt (R:=ℝ) K (by norm_num : (1:ℝ)<2)).bound (by norm_num : (0:ℝ)<1)
  obtain ⟨E,hE⟩ := eventually_atTop.mp hl
  let c : ℝ := (2:ℝ)^K*((E:ℝ)+1)^K
  have hc : 1≤c := by
    dsimp [c]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) E]))
  have small (e : ℕ) : ((e:ℝ)+1)^K ≤ c*(2:ℝ)^e := by
    by_cases he : e<E
    · have hle : ((e:ℝ)+1)^K ≤ ((E:ℝ)+1)^K := pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show e+1≤E+1 by omega)) _
      have h2 : (1:ℝ)≤2^K := one_le_pow₀ (by norm_num)
      have h3 : (1:ℝ)≤2^e := one_le_pow₀ (by norm_num)
      exact hle.trans ((le_mul_of_one_le_left (by positivity) h2).trans (le_mul_of_one_le_right (by positivity) h3))
    · have hs := hE (e+1) (by omega)
      simp only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one, abs_of_nonneg (pow_nonneg (by positivity : 0 ≤ (e : ℝ) + 1) K), one_mul, pow_succ] at hs
      rw [abs_of_nonneg (by positivity)] at hs
      have hK1 : (2:ℝ)≤2^K := by simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hK)
      have hE1 : (1:ℝ)≤((E:ℝ)+1)^K := one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) E])
      have hc2 : (2:ℝ)≤c := hK1.trans (le_mul_of_one_le_right (by positivity) hE1)
      exact hs.trans (by nlinarith [mul_le_mul_of_nonneg_right hc2 (by positivity : 0≤(2:ℝ)^e)])
  let P : ℕ := 2^K
  refine ⟨c^P,one_le_pow₀ hc,?_⟩
  intro n hn
  have hprod : (∏ p ∈ n.primeFactors,(p:ℝ)^(n.factorization p))=n := by
    exact_mod_cast (by simpa [Finsupp.prod,Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn.ne' :
      (∏ p ∈ n.primeFactors,p^(n.factorization p))=n)
  have hlocal (p : ℕ) (hp : p∈n.primeFactors) :
      ((n.factorization p:ℝ)+1)^K ≤ (if p<P then c else 1)*(p:ℝ)^(n.factorization p) := by
    have h2 : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with h
    · exact (small _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h2 _) (by linarith))
    · rw [one_mul]
      have he : ∀ e : ℕ,(e:ℝ)+1 ≤ (2:ℝ)^e := by
        intro e; induction e with
        | zero => norm_num
        | succ e ih => push_cast; rw [pow_succ]; linarith [show (0:ℝ)≤e by positivity]
      calc
        _ ≤ ((2:ℝ)^n.factorization p)^K := pow_le_pow_left₀ (by positivity) (he _) _
        _ = ((2:ℝ)^K)^n.factorization p := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
        _ ≤ _ := pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show 2^K≤p by omega)) _
  have hcount : ((n.primeFactors.filter (·<P)).card)≤P := by
    have : n.primeFactors.filter (·<P)⊆range P := fun _ h => mem_range.mpr (mem_filter.mp h).2
    simpa using card_le_card this
  have hfactor : (∏ p ∈ n.primeFactors, if p<P then c else 1)≤c^P := by
    rw [←prod_filter,prod_const]; exact pow_le_pow_right₀ hc hcount
  rw [Nat.card_divisors hn.ne',Nat.cast_prod,←prod_pow]
  simp only [Nat.cast_add,Nat.cast_one]
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (if p<P then c else 1)*(p:ℝ)^(n.factorization p) :=
      prod_le_prod₀ (fun _ _ => by positivity) hlocal
    _ ≤ _ := by rw [prod_mul_distrib,hprod]; exact mul_le_mul_of_nonneg_right hfactor (by positivity)

theorem divisor_envelope (k : ℕ) (hk : 0 < k) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n m : ℕ, m ≤ n →
    (m.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / (k : ℝ) : ℝ) := by
  obtain ⟨C, CLower, estimate⟩ := divisorPower k hk
  let p : ℝ := 1 / (k : ℝ)
  have CNonnegative : 0 ≤ C := zero_le_one.trans CLower
  refine ⟨C ^ p, Real.one_le_rpow CLower (by unfold p; positivity), fun n m upper => ?_⟩
  by_cases mPositive : 0 < m
  · have mReal : (m : ℝ) ≤ n := by exact_mod_cast upper
    have standard := (estimate m mPositive).trans (mul_le_mul_of_nonneg_left mReal CNonnegative)
    have powered := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg m.divisors.card) k) standard
      (show 0 ≤ p by dsimp [p]; positivity)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m.divisors.card),
      Real.mul_rpow CNonnegative (Nat.cast_nonneg n)] at powered
    have kReal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have kp : (k : ℝ) * p = 1 := by unfold p; field_simp
    rw [kp, Real.rpow_one] at powered
    exact powered
  · have mZero : m = 0 := by omega
    subst m
    simp only [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero]
    positivity

end GoldbachPrincipalSeries


open Set Finset MeasureTheory
open scoped ENNReal

namespace GoldbachNarrowMajor

noncomputable section

def arcs (n P : ℕ) : Set ℝ := {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ P ∧ a ≤ q ∧
  Nat.Coprime a q ∧ |t - (a : ℝ) / q| ≤ (P : ℝ) / ((q : ℝ) * n)}


end

end GoldbachNarrowMajor

namespace GoldbachPrincipalSeries

open Finset MeasureTheory Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc
open scoped ComplexConjugate

noncomputable def finiteModel (w : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), (w j : ℂ) * phase ((j : ℝ) * t)

theorem finiteModel_continuous (w : ℕ → ℝ) (n : ℕ) : Continuous (finiteModel w n) := by
  unfold finiteModel phase
  fun_prop

private theorem centered_mode (j : ℤ) :
    (∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), phase ((j : ℝ) * t)) =
      if j = 0 then 1 else 0 := by
  by_cases hz : j = 0
  · subst j
    norm_num [phase]
  let c : ℂ := (j : ℂ) * (2 * Real.pi * Complex.I)
  have hphase (t : ℝ) : phase ((j : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold phase c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hz)
    (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  have hc1 : Complex.exp c = 1 := Complex.exp_int_mul_two_pi_mul_I j
  simp_rw [hphase]
  rw [integral_exp_mul_complex hc]
  have hp : Complex.exp (c * ((1 / 2 : ℝ) : ℂ)) =
      Complex.exp (c * ((-(1 / 2 : ℝ)) : ℂ)) := by
    rw [show c * ((1 / 2 : ℝ) : ℂ) = c * ((-(1 / 2 : ℝ)) : ℂ) + c by push_cast; ring,
      Complex.exp_add, hc1, mul_one]
  rw [hp]
  simp [hz]


private theorem phase_conj (t : ℝ) : conj (phase t) = phase (-t) := by
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- Parseval on the centered full period of the finite principal model. -/
theorem finiteModel_energy (w : ℕ → ℝ) (n : ℕ) :
    (∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), ‖finiteModel w n t‖ ^ 2) =
      ∑ k ∈ Finset.range (n + 1), w k ^ 2 := by
  let S := Finset.range (n + 1)
  let term (k j : ℕ) (t : ℝ) :=
    ((w k : ℂ) * (w j : ℂ)) * phase ((((k : ℤ) - j : ℤ) : ℝ) * t)
  have hcont (k j : ℕ) : Continuous (term k j) := by
    unfold term phase
    fun_prop
  have hpoint (t : ℝ) : Complex.ofReal (‖finiteModel w n t‖ ^ 2) =
      ∑ k ∈ S, ∑ j ∈ S, term k j t := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    unfold finiteModel
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    unfold term
    push_cast
    rw [map_mul, Complex.conj_ofReal, phase_conj,
      show ((k : ℝ) - j) * t = (k : ℝ) * t + -((j : ℝ) * t) by ring, ← phase_mul]
    ring
  have hrow (k : ℕ) (hk : k ∈ S) :
      (∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), ∑ j ∈ S, term k j t) = Complex.ofReal (w k ^ 2) := by
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont k j).intervalIntegrable _ _)]
    simp only [term, intervalIntegral.integral_const_mul, centered_mode]
    rw [Finset.sum_eq_single_of_mem k hk]
    · simp [pow_two]
    · intro j _ hn
      have hne : (k : ℤ) - j ≠ 0 := by omega
      simp [hne]
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (continuous_finsetSum S (fun j _ => hcont k j)).intervalIntegrable _ _), Complex.ofReal_sum]
  exact Finset.sum_congr rfl hrow

end GoldbachPrincipalSeries

namespace GoldbachPrincipalSeries

open Finset Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc

noncomputable def totalVariation (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  |w 0| + (∑ j ∈ Finset.range n, |w (j + 1) - w j|) + |w n|

end GoldbachPrincipalSeries


namespace GoldbachPrincipalSeries

open Finset Set GoldbachSmoothWindow Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc

private theorem smooth_weight_variation : ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 0 < X →
    totalVariation (fun j => scaledWeight (X : ℝ) (j : ℝ)) (2 * X) ≤ 4 * K := by
  obtain ⟨M, hM, hderiv⟩ := weight_derivative_bound 1
  refine ⟨M, hM, ?_⟩
  intro X hX
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hLip (x y : ℝ) : |weight y - weight x| ≤ M * |y - x| := by
    have hb (t : ℝ) : ‖deriv weight t‖ ≤ M := by
      simpa only [iteratedDeriv_one] using hderiv t
    simpa only [Real.norm_eq_abs] using
      (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun t _ => (weight_smooth (n := 1)).differentiable (by norm_num) t)
      (fun t _ => hb t) (mem_univ x) (mem_univ y)
  have h0 : scaledWeight (X : ℝ) ((0 : ℕ) : ℝ) = 0 := by
    apply weight_zero
    left
    norm_num
  have h2 : scaledWeight (X : ℝ) ((2 * X : ℕ) : ℝ) = 0 := by
    apply weight_zero
    right
    push_cast
    exact (le_div_iff₀ hXR).mpr (by linarith)
  have hs (j : ℕ) :
      |scaledWeight (X : ℝ) ((j + 1 : ℕ) : ℝ) - scaledWeight (X : ℝ) (j : ℝ)| ≤ M / (X : ℝ) := by
    unfold scaledWeight
    have he : ((j + 1 : ℕ) : ℝ) / (X : ℝ) - (j : ℝ) / (X : ℝ) = 1 / (X : ℝ) := by
      push_cast
      rw [← sub_div]
      ring
    simpa only [he, abs_of_pos (one_div_pos.mpr hXR), mul_one_div] using
      hLip ((j : ℝ) / (X : ℝ)) (((j + 1 : ℕ) : ℝ) / (X : ℝ))
  unfold totalVariation
  dsimp only
  rw [h0, h2, abs_zero, zero_add, add_zero]
  calc
    _ ≤ ∑ _j ∈ Finset.range (2 * X), M / (X : ℝ) := Finset.sum_le_sum fun j _ => hs j
    _ = 2 * M := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      field_simp
    _ ≤ _ := by linarith

end GoldbachPrincipalSeries

namespace GoldbachPrincipalSeries

open Finset Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc

private theorem phase_int_eq_one (j : ℤ) : phase (j : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I j using 1
  congr 1
  push_cast
  ring

/-- An integral Fourier mode has period one. -/
theorem phase_int_frequency_periodic (j : ℤ) :
    Function.Periodic (fun t : ℝ => phase ((j : ℝ) * t)) 1 := by
  intro t
  dsimp only
  rw [mul_add, mul_one, ← phase_mul, phase_int_eq_one, mul_one]

theorem finiteModel_periodic (w : ℕ → ℝ) (n : ℕ) : Function.Periodic (finiteModel w n) 1 := by
  intro t
  unfold finiteModel
  apply Finset.sum_congr rfl
  intro k _
  have h := phase_int_frequency_periodic (k : ℤ) t
  exact congrArg ((w k : ℂ) * ·) (by exact_mod_cast h)

theorem phase_square_periodic {S : ℝ → ℂ} (hp : Function.Periodic S 1) (m : ℕ) :
    Function.Periodic (fun t : ℝ => S t ^ 2 * phase (-(m : ℝ) * t)) 1 := by
  intro t
  dsimp only
  rw [hp t]
  rw [show phase (-(m : ℝ) * (t + 1)) = phase (-(m : ℝ) * t) by
    simpa using phase_int_frequency_periodic (-(m : ℤ)) t]

end GoldbachPrincipalSeries


namespace GoldbachNarrowMajor

open Finset Set MeasureTheory
open scoped Function

private abbrev Center := Σ _ : ℕ, ℕ

private def reducedCenters (P : ℕ) : Finset Center :=
  (Finset.Icc 1 P).sigma (fun q => (Finset.range q).filter (fun a => a.Coprime q))

private noncomputable def centerValue (i : Center) : ℝ := (i.2 : ℝ) / i.1
private noncomputable def radius (n P q : ℕ) : ℝ := (P : ℝ) / ((q : ℝ) * (n : ℝ))

private noncomputable def fullWindow (n P : ℕ) (i : Center) : Set ℝ :=
  Set.Icc (centerValue i - radius n P i.1) (centerValue i + radius n P i.1)

private noncomputable def clippedWindow (n P : ℕ) (i : Center) : Set ℝ :=
  fullWindow n P i ∩ Set.Icc 0 1

private theorem mem_reducedCenters {P : ℕ} {i : Center} :
    i ∈ reducedCenters P ↔ 1 ≤ i.1 ∧ i.1 ≤ P ∧ i.2 < i.1 ∧ i.2.Coprime i.1 := by
  simp [reducedCenters, and_assoc]

private theorem eq_of_cross_mul {q a r b : ℕ} (hq : 0 < q) (ha : a.Coprime q)
    (hb : b.Coprime r) (he : a * r = b * q) : q = r ∧ a = b := by
  have hqdr : q ∣ r := ha.symm.dvd_of_dvd_mul_left (he.symm ▸ (dvd_mul_left q b))
  have hrdq : r ∣ q := hb.symm.dvd_of_dvd_mul_left (he ▸ (dvd_mul_left r a))
  have hqr := Nat.dvd_antisymm hqdr hrdq
  exact ⟨hqr, Nat.eq_of_mul_eq_mul_right hq (by simpa only [← hqr] using he)⟩

private theorem rational_windows_disjoint {n P : ℕ} (h : 2 * P ^ 2 < n)
    {i j : Center} (hi : 1 ≤ i.1 ∧ i.1 ≤ P ∧ i.2.Coprime i.1)
    (hj : 1 ≤ j.1 ∧ j.1 ≤ P ∧ j.2.Coprime j.1) (hij : i ≠ j) :
    Disjoint (fullWindow n P i) (fullWindow n P j) := by
  obtain ⟨q, a⟩ := i
  obtain ⟨r, b⟩ := j
  obtain ⟨hq, hqP, ha⟩ := hi
  obtain ⟨hr, hrP, hb⟩ := hj
  dsimp only at hq hqP ha hr hrP hb
  have hcross : (a : ℤ) * (r : ℤ) - (b : ℤ) * (q : ℤ) ≠ 0 := by
    intro h0
    have he : a * r = b * q := by
      exact_mod_cast (sub_eq_zero.mp h0)
    exact hij (by obtain ⟨rfl, rfl⟩ := eq_of_cross_mul hq ha hb he; rfl)
  have hgapZ : (1 : ℤ) ≤ |(a : ℤ) * (r : ℤ) - (b : ℤ) * (q : ℤ)| := by
    have ht := abs_pos.mpr hcross
    omega
  have hgapR : (1 : ℝ) ≤ |(a : ℝ) * (r : ℝ) - (b : ℝ) * (q : ℝ)| := by exact_mod_cast hgapZ
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hP : 2 * (P : ℝ) ^ 2 < n := by exact_mod_cast h
  have hqrP : (q : ℝ) + (r : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast (show q + r ≤ 2 * P by omega)
  have hwidth : ((P : ℝ) * ((q : ℝ) + (r : ℝ))) / (n : ℝ) < 1 := by
    apply (div_lt_iff₀ hnR).mpr
    have hmul := mul_le_mul_of_nonneg_left hqrP (Nat.cast_nonneg P : 0 ≤ (P : ℝ))
    nlinarith
  refine Set.disjoint_left.mpr ?_
  intro x hxi hxj
  change (a : ℝ) / q - (P : ℝ) / ((q : ℝ) * n) ≤ x ∧
    x ≤ (a : ℝ) / q + (P : ℝ) / ((q : ℝ) * n) at hxi
  change (b : ℝ) / r - (P : ℝ) / ((r : ℝ) * n) ≤ x ∧
    x ≤ (b : ℝ) / r + (P : ℝ) / ((r : ℝ) * n) at hxj
  have hi' : |x - (a : ℝ) / q| ≤ (P : ℝ) / ((q : ℝ) * n) :=
    abs_le.mpr ⟨by linarith [hxi.1], by linarith [hxi.2]⟩
  have hj' : |x - (b : ℝ) / r| ≤ (P : ℝ) / ((r : ℝ) * n) :=
    abs_le.mpr ⟨by linarith [hxj.1], by linarith [hxj.2]⟩
  have ht : |(a : ℝ) / q - (b : ℝ) / r| ≤
      (P : ℝ) / ((q : ℝ) * n) + (P : ℝ) / ((r : ℝ) * n) := by
    rw [show (a : ℝ) / q - (b : ℝ) / r = (x - (b : ℝ) / r) - (x - (a : ℝ) / q) by ring]
    have ht := abs_sub_le (x - (b : ℝ) / r) 0 (x - (a : ℝ) / q)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    exact ht.trans (by simpa only [add_comm] using add_le_add hj' hi')
  have hmul := mul_le_mul_of_nonneg_right ht (mul_nonneg hqR.le hrR.le)
  have hleft : |(a : ℝ) / q - (b : ℝ) / r| * ((q : ℝ) * (r : ℝ)) =
      |(a : ℝ) * (r : ℝ) - (b : ℝ) * (q : ℝ)| := by
    rw [← abs_of_nonneg (mul_nonneg hqR.le hrR.le), ← abs_mul]
    congr 1
    field_simp
  have hright : ((P : ℝ) / ((q : ℝ) * n) + (P : ℝ) / ((r : ℝ) * n)) * ((q : ℝ) * (r : ℝ)) =
      (P : ℝ) * ((q : ℝ) + (r : ℝ)) / (n : ℝ) := by
    field_simp
    ring
  rw [hleft, hright] at hmul
  exact (not_lt_of_ge (hgapR.trans hmul)) hwidth

private def zeroCenter : Center := ⟨1, 0⟩
private def oneCenter : Center := ⟨1, 1⟩

private theorem zeroCenter_mem {P : ℕ} (hP : 1 ≤ P) : zeroCenter ∈ reducedCenters P := by
  simpa [mem_reducedCenters, zeroCenter] using hP

private theorem oneCenter_not_mem (P : ℕ) : oneCenter ∉ reducedCenters P := by
  simp [mem_reducedCenters, oneCenter]

private theorem clipped_eq_full {n P : ℕ} (h : 2 * P ^ 2 < n) {i : Center}
    (hi : i ∈ reducedCenters P) (h0 : i ≠ zeroCenter) :
    clippedWindow n P i = fullWindow n P i := by
  obtain ⟨q,a⟩ := i
  obtain ⟨hq, hqP, ha, hc⟩ := mem_reducedCenters.mp hi
  dsimp only at hq hqP ha hc
  have hapos : 1 ≤ a := by
    by_contra! hz
    have ha0 : a = 0 := by omega
    have hq1 : q = 1 := by simpa [ha0] using hc
    exact h0 (by simp [zeroCenter, ha0, hq1])
  have hPn : P < n := by nlinarith [show 1 ≤ P by omega]
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hr : radius n P q ≤ 1 / (q : ℝ) := by
    unfold radius
    apply (div_le_iff₀ (mul_pos hqR hnR)).mpr
    have he : (1 / (q : ℝ)) * ((q : ℝ) * n) = (n : ℝ) := by field_simp
    rw [he]
    exact_mod_cast hPn.le
  have hl : 1 / (q : ℝ) ≤ (a : ℝ) / q := div_le_div_of_nonneg_right (by exact_mod_cast hapos) hqR.le
  have hu : (a : ℝ) / q + 1 / (q : ℝ) ≤ 1 := by
    rw [← add_div]
    exact (div_le_one hqR).mpr (by exact_mod_cast (show a + 1 ≤ q by omega))
  apply Set.inter_eq_left.mpr
  intro x hx
  change (a : ℝ) / q - radius n P q ≤ x ∧ x ≤ (a : ℝ) / q + radius n P q at hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

private theorem clipped_union (n P : ℕ) (hP : 1 ≤ P) :
    arcs n P ∩ Set.Icc (0 : ℝ) 1 =
      ⋃ i ∈ insert oneCenter (reducedCenters P), clippedWindow n P i := by
  ext x
  constructor
  · rintro ⟨⟨q, a, hq, hqP, haq, ha, hx⟩, hx01⟩
    have hw : x ∈ fullWindow n P ⟨q, a⟩ := by
      change (a : ℝ) / q - (P : ℝ) / ((q : ℝ) * n) ≤ x ∧
        x ≤ (a : ℝ) / q + (P : ℝ) / ((q : ℝ) * n)
      have hb := abs_le.mp hx
      exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
    have hi : (⟨q, a⟩ : Center) ∈ insert oneCenter (reducedCenters P) := by
      rcases lt_or_eq_of_le haq with hlt | he
      · exact Finset.mem_insert_of_mem (mem_reducedCenters.mpr ⟨hq, hqP, hlt, ha⟩)
      · subst a
        have hq1 : q = 1 := by simpa using ha
        subst q
        exact Finset.mem_insert_self _ _
    exact mem_iUnion.mpr ⟨⟨q, a⟩, mem_iUnion.mpr ⟨hi, hw, hx01⟩⟩
  · intro hx
    obtain ⟨⟨q,a⟩, ha⟩ := mem_iUnion.mp hx
    obtain ⟨hi, hfull, hx01⟩ := mem_iUnion.mp ha
    have hidx : 1 ≤ q ∧ q ≤ P ∧ a ≤ q ∧ a.Coprime q := by
      rcases Finset.mem_insert.mp hi with he | he
      · have hq : q = 1 := congrArg Sigma.fst he
        subst q
        have ha : a = 1 := by simpa [oneCenter] using he
        subst a
        simp [hP]
      · obtain ⟨hq, hqP, ha, hc⟩ := mem_reducedCenters.mp he
        exact ⟨hq, hqP, ha.le, hc⟩
    refine ⟨⟨q, a, hidx.1, hidx.2.1, hidx.2.2.1, hidx.2.2.2, abs_le.mpr ?_⟩, hx01⟩
    change (a : ℝ) / q - (P : ℝ) / ((q : ℝ) * n) ≤ x ∧
      x ≤ (a : ℝ) / q + (P : ℝ) / ((q : ℝ) * n) at hfull
    exact ⟨by linarith [hfull.1], by linarith [hfull.2]⟩

private theorem edge_integrals {n P : ℕ} {f : ℝ → ℂ} (hf : Continuous f)
    (hper : Function.Periodic f 1) (hρ : 0 ≤ radius n P 1) (hρ' : radius n P 1 ≤ 1) :
    (∫ x in clippedWindow n P zeroCenter, f x) + (∫ x in clippedWindow n P oneCenter, f x) =
      ∫ x in fullWindow n P zeroCenter, f x := by
  let ρ := radius n P 1
  have hzero : clippedWindow n P zeroCenter = Icc 0 ρ := by
    ext x
    simp only [clippedWindow, fullWindow, zeroCenter, centerValue, Nat.cast_zero, Nat.cast_one,
      zero_div, zero_sub, zero_add, mem_inter_iff, Set.mem_Icc]
    constructor
    · rintro ⟨⟨_, hx⟩, hz, _⟩
      exact ⟨hz, hx⟩
    · rintro ⟨hz, hx⟩
      exact ⟨⟨by linarith, hx⟩, hz, hx.trans hρ'⟩
  have hone : clippedWindow n P oneCenter = Icc (1 - ρ) 1 := by
    ext x
    simp only [clippedWindow, fullWindow, oneCenter, centerValue, Nat.cast_one, div_one,
      mem_inter_iff, Set.mem_Icc]
    constructor
    · rintro ⟨⟨hx, _⟩, _, hy⟩
      exact ⟨hx, hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨⟨hx, by linarith⟩, by linarith, hy⟩
  have hfull : fullWindow n P zeroCenter = Icc (-ρ) ρ := by
    simp [fullWindow, zeroCenter, centerValue, ρ]
  rw [hzero, hone, hfull]
  simp only [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hρ, ← intervalIntegral.integral_of_le (by linarith : 1 - ρ ≤ 1),
    ← intervalIntegral.integral_of_le (by linarith : -ρ ≤ ρ)]
  have htranslate : (∫ x in (1 - ρ)..(1:ℝ), f x) = ∫ x in (-ρ)..(0:ℝ), f x := by
    calc
      _ = ∫ x in (-ρ)..(0:ℝ), f (x + 1) := by
        rw [intervalIntegral.integral_comp_add_right]
        ring_nf
      _ = _ := by
        have hshift (x : ℝ) : f (x + 1) = f x := hper x
        simp_rw [hshift]
  rw [htranslate, add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

/-- Integrate on the real representatives of one torus period, then reunite
its two endpoint pieces as the single reduced center for denominator one. -/
theorem integral_torus_major_arcs {n P : ℕ} (hP : 1 ≤ P) (hsep : 2 * P ^ 2 < n)
    {f : ℝ → ℂ} (hf : Continuous f) (hper : Function.Periodic f 1) :
    (∫ x in arcs n P ∩ Set.Icc (0 : ℝ) 1, f x) =
      ∑ q ∈ Finset.Icc 1 P, ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
        ∫ β in -((P : ℝ) / ((q : ℝ) * n))..((P : ℝ) / ((q : ℝ) * n)), f (β + (a : ℝ) / q) := by
  let I := reducedCenters P
  let J := insert oneCenter I
  have hcenter (i : Center) (hi : i ∈ J) : 1 ≤ i.1 ∧ i.1 ≤ P ∧ i.2.Coprime i.1 := by
    rcases Finset.mem_insert.mp hi with he | he
    · subst i
      simp [oneCenter, hP]
    · obtain ⟨hq, hqP, _, ha⟩ := mem_reducedCenters.mp he
      exact ⟨hq, hqP, ha⟩
  have pairwise : Set.Pairwise (↑J : Set Center) (Disjoint on clippedWindow n P) := by
    intro i hi j hj hij
    exact (rational_windows_disjoint hsep (hcenter i hi) (hcenter j hj) hij).mono
      Set.inter_subset_left Set.inter_subset_left
  let A (i : Center) := ∫ x in clippedWindow n P i, f x
  let B (i : Center) := ∫ x in fullWindow n P i, f x
  have hmeasure : (∫ x in arcs n P ∩ Set.Icc (0 : ℝ) 1, f x) = ∑ i ∈ J, A i := by
    rw [clipped_union n P hP]
    exact integral_biUnion_finset J (fun _ _ => measurableSet_Icc.inter measurableSet_Icc)
      pairwise (fun _ _ => hf.integrableOn_Icc.mono_set Set.inter_subset_left)
  have hρ : 0 ≤ radius n P 1 := by unfold radius; positivity
  have hρ' : radius n P 1 ≤ 1 := by
    have hn : 0 < n := by omega
    have hPn : P ≤ n := by nlinarith
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    simpa [radius] using (div_le_one hnR).mpr (by exact_mod_cast hPn)
  have hsplit : (∑ i ∈ J, A i) = ∑ i ∈ I, B i := by
    change (∑ i ∈ insert oneCenter I, A i) = ∑ i ∈ I, B i
    rw [Finset.sum_insert (oneCenter_not_mem P), ← Finset.sum_erase_add I A (zeroCenter_mem hP),
      ← Finset.sum_erase_add I B (zeroCenter_mem hP)]
    have hrest : (∑ i ∈ I.erase zeroCenter, A i) = ∑ i ∈ I.erase zeroCenter, B i := by
      apply Finset.sum_congr rfl
      intro i hi
      obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hi
      change (∫ x in clippedWindow n P i, f x) = ∫ x in fullWindow n P i, f x
      rw [clipped_eq_full hsep hmem hne]
    have h01 : A zeroCenter + A oneCenter = B zeroCenter := edge_integrals hf hper hρ hρ'
    rw [hrest, ← h01]
    abel
  rw [hmeasure, hsplit]
  change (∑ i ∈ (Finset.Icc 1 P).sigma (fun q => (Finset.range q).filter (fun a => a.Coprime q)), B i) = _
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro a _
  unfold B fullWindow centerValue
  simp only [integral_Icc_eq_integral_Ioc]
  have hr : 0 ≤ radius n P q := by unfold radius; positivity
  rw [← intervalIntegral.integral_of_le (by linarith :
    (a : ℝ) / q - radius n P q ≤ (a : ℝ) / q + radius n P q),
    intervalIntegral.integral_comp_add_right]
  unfold radius
  ring_nf

end GoldbachNarrowMajor

end

section


/-! A polynomial exceptional-set bound for the minor-arc term of the
binary Goldbach problem, uniform in the lower endpoint of the prime sum.
The argument is the Vaughan–Bessel estimate of Pintz, arXiv:1804.09084,
§2, equation (2.6). The reduced-approximant and prime-power comparisons
are adapted from the repository's EstermannAlmostAllPolylog. This variant narrows the cutoff in
zxg0623's reference proof at PR 3782, f17e266f (Apache-2.0). -/

namespace GoldbachPolynomialMinor205

open Finset Filter MeasureTheory
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMovingWindows (primeLog primeLog_energy)
open scoped BigOperators Topology

noncomputable section


def series (n : ℕ) (u : ℕ → ℝ) (t : ℝ) := ∑ k ∈ range (n+1), (u k : ℂ)*wave ((k : ℝ)*t)

def arcs (n P : ℕ) := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ P ∧ a ≤ q ∧ a.Coprime q ∧
  |t-(a : ℝ)/q| ≤ (P : ℝ)/((q : ℝ)*n)}


private theorem vaughan_denominator_terms {x q P T : ℝ} (hx : 0 < x) (hT : 0 < T)
    (hP : 0 < P) (hTsize : T ≤ Real.sqrt P) (hlow : P ≤ q) (hhigh : q ≤ x/P) :
    x / Real.sqrt q ≤ x/T ∧ Real.sqrt (x*q) ≤ x/T := by
  have hq := hP.trans_le hlow
  have hT2 : T^2 ≤ P := (Real.le_sqrt (by positivity) hP.le).mp hTsize
  constructor
  · exact div_le_div_of_nonneg_left hx.le hT (hTsize.trans (Real.sqrt_le_sqrt hlow))
  · apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    have hprod := (le_div_iff₀ hP).mp hhigh
    nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT2 hq.le) hx.le,
      mul_le_mul_of_nonneg_left hprod hx.le]

private theorem minor_approximant (Q n : ℕ) (t : ℝ) (hQ : 1 ≤ Q) (hQn : Q ≤ n)
    (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hminor : t ∉ {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧
      |t - a/(q:ℝ)| ≤ (Q:ℝ)/(q*n)}) :
    ∃ q a : ℕ, Q < q ∧ q ≤ n / Q ∧ a ≤ q ∧ a.Coprime q ∧
      |t - a/(q:ℝ)| ≤ 1 / ((q:ℝ)*((n/Q : ℕ)+1 : ℝ)) := by
  let B := n / Q
  have hB : 0 < B := Nat.div_pos hQn hQ
  obtain ⟨s,hs,hd⟩ := Real.exists_rat_abs_sub_le_and_den_le t hB
  have hdpos : (0 : ℝ) < s.den := Nat.cast_pos.mpr s.pos
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hQB : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [Rat.cast_def, mul_comm ((B : ℝ) + 1) (s.den : ℝ)] at hs
  have hclose : |t * s.den - s.num| < 1 := by
    have h := (mul_le_mul_of_nonneg_right hs hdpos.le)
    rw [← abs_of_pos hdpos, ← abs_mul, abs_of_pos hdpos] at h
    rw [sub_mul, div_mul_cancel₀ _ hdpos.ne'] at h
    refine h.trans_lt ?_
    rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    nlinarith
  obtain ⟨hl,hu⟩ := abs_lt.mp hclose
  have ht0 : 0 ≤ t * s.den := mul_nonneg ht.1 hdpos.le
  have ht1 : t * s.den ≤ s.den := by simpa using mul_le_mul_of_nonneg_right ht.2 hdpos.le
  have hnlo : (-1 : ℤ) < s.num := by exact_mod_cast (show (-1 : ℝ) < s.num by linarith)
  have hnhi : s.num < (s.den : ℤ) + 1 := by exact_mod_cast (show (s.num : ℝ) < s.den + 1 by linarith)
  have hcast : (s.num.natAbs : ℤ) = s.num := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
  have hcast' : (s.num.natAbs : ℝ) = s.num := by
    calc (s.num.natAbs : ℝ) = ((s.num.natAbs : ℤ) : ℝ) := by simp
         _ = _ := congrArg (fun z : ℤ => (z : ℝ)) hcast
  have hle : s.num.natAbs ≤ s.den := by exact_mod_cast (show (s.num.natAbs : ℤ) ≤ s.den by omega)
  rw [← hcast'] at hs
  refine ⟨s.den, s.num.natAbs, ?_, hd, hle, s.reduced, hs⟩
  by_contra! hsmall
  apply hminor
  refine ⟨s.den, s.num.natAbs, s.pos, hsmall, hle, s.reduced, hs.trans ?_⟩
  have hbound : (n : ℝ) < Q * ((B : ℝ) + 1) := by exact_mod_cast Nat.lt_mul_div_succ n hQ
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hbound.le hdpos.le]

private theorem mangoldt_pointwise_bridge (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0
    let e := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ):ℂ)*Complex.I)
    ‖∑ k ∈ Finset.range (n+1), ((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) * e ((k:ℝ)*t)‖ ≤
      2 * Real.sqrt n * Real.log n := by
  intro w e
  have hnon (k : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt k - w k := by
    by_cases hk : k.Prime <;> simp [w,hk,ArithmeticFunction.vonMangoldt_apply_prime]
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), ‖((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) * e ((k:ℝ)*t)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - w k) := by
      simp only [norm_mul,e,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hnon _)]
    _ = Chebyshev.psi n - Chebyshev.theta n := by
      rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
      simp [Chebyshev.psi,Chebyshev.theta,w,Finset.sum_filter,Finset.sum_sub_distrib]
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast hn)

private theorem prime_mass (Y : ℕ) (t : ℝ) :
    ‖series Y primeLog t‖ ≤ 2*(Y : ℝ) := by
  have hnon (k : ℕ) : |primeLog k| = primeLog k := abs_of_nonneg (by
    by_cases hk : k.Prime <;> simp [GoldbachMovingWindows.primeLog,hk,Real.log_natCast_nonneg])
  have h4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num1
    linarith [Real.log_two_lt_d9]
  calc
  _ ≤ ∑ k ∈ range (Y+1), ‖(primeLog k : ℂ)*wave ((k : ℝ)*t)‖ := norm_sum_le _ _
  _ = Chebyshev.theta Y := by
    simp only [wave, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, hnon]
    unfold GoldbachMovingWindows.primeLog
    rw [← Finset.sum_filter, Chebyshev.theta_eq_sum_primesLE_log]
    congr 1
  _ ≤ _ := (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg Y)).trans
    (mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg Y))

private theorem prime_approx (Y q : ℕ) (t : ℝ) (hY : 1 ≤ Y)
    (h : ‖OAI.Problem337.Vaughan.weightedSum (Ioc 0 Y)
      (fun k => OAI.Problem337.VaughanBilinear.phase (t*k)) ArithmeticFunction.vonMangoldt‖ ≤
      16200*(Real.log Y)^4*OAI.Problem337.Vaughan.approximationEnvelope Y q) :
    ‖series Y primeLog t‖ ≤ 16200*(Real.log Y)^4*OAI.Problem337.Vaughan.approximationEnvelope Y q
      + 2*Real.sqrt Y*Real.log Y := by
  have heq : series Y ArithmeticFunction.vonMangoldt t =
      OAI.Problem337.Vaughan.weightedSum (Ioc 0 Y)
        (fun k => OAI.Problem337.VaughanBilinear.phase (t*k)) ArithmeticFunction.vonMangoldt := by
    dsimp [series,wave,OAI.Problem337.Vaughan.weightedSum,OAI.Problem337.VaughanBilinear.phase]
    rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le Y)]
    simp only [ArithmeticFunction.map_zero,Complex.ofReal_zero,zero_mul,zero_add,Real.fourierChar_apply]
    apply Finset.sum_congr rfl
    intro k _; rw [mul_comm t (k : ℝ)]
  have herr : ‖series Y ArithmeticFunction.vonMangoldt t-series Y primeLog t‖ ≤
      2*Real.sqrt Y*Real.log Y := by
    simpa only [series, wave, GoldbachMovingWindows.primeLog, ← sum_sub_distrib, ← sub_mul,
      ← Complex.ofReal_sub] using mangoldt_pointwise_bridge Y hY t
  have htr := norm_sub_le (series Y ArithmeticFunction.vonMangoldt t)
    (series Y ArithmeticFunction.vonMangoldt t-series Y primeLog t)
  rw [sub_sub_cancel] at htr
  exact htr.trans (add_le_add (heq ▸ h) herr)


/-- One reduced approximation controls all initial segment lengths, including those
shorter than its denominator. This permits the lower cutoff in Pintz's sum. -/
theorem prefix_bound : ∀ᶠ n : ℕ in atTop, ∀ P : ℕ, 1 ≤ P → P ≤ n →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ arcs n P → ∀ Y ≤ n,
    ‖series Y primeLog t‖ ≤ 50000*(Real.log n)^4*scale n P := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 OAI.Problem337.Vaughan.eventually_vonMangoldt_sum_log_bound
  have ht := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards [eventually_ge_atTop ((max N 1)^2),
    (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1] with n hn hL
  intro P hP hPn t ht' hminor Y hYn
  have hpr : (0 : ℝ) < P := Nat.cast_pos.mpr hP
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsr : 0 < Real.sqrt (P : ℝ) := Real.sqrt_pos.2 hpr
  have hs1 : 1 ≤ Real.sqrt (P : ℝ) := (Real.le_sqrt (by norm_num) hpr.le).2 (by exact_mod_cast hP)
  have hsP : Real.sqrt (P : ℝ) ≤ P := by
    nlinarith only [Real.sq_sqrt hpr.le, mul_nonneg (sub_nonneg.mpr hs1) hsr.le]
  have hns := Real.sqrt_le_sqrt (by exact_mod_cast hPn : (P : ℝ) ≤ n)
  have hroot : Real.sqrt (n : ℝ) ≤ (n : ℝ)/Real.sqrt P := by
    apply (le_div_iff₀ hsr).2
    exact (mul_le_mul_of_nonneg_left hns (Real.sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt hnr.le)
  have hNn : (N : ℝ) ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (Nat.cast_nonneg N) hnr.le).2
    exact_mod_cast (Nat.pow_le_pow_left (le_max_left N 1) 2).trans hn
  obtain ⟨q,a,hPq,hqB,_,hcop,happ⟩ := minor_approximant P n t hP hPn ht' hminor
  have hq : 0 < q := by omega
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hhigh : (q : ℝ) ≤ (n : ℝ)/P := (le_div_iff₀ hpr).2
    (by exact_mod_cast (Nat.le_div_iff_mul_le hP).1 hqB)
  have hcut : (n : ℝ)/Real.sqrt P ≤ scale n P := le_add_of_nonneg_right (Real.rpow_nonneg hnr.le _)
  have hB := div_le_div_of_nonneg_left hnr.le hsr hsP
  have hscale : 0 ≤ scale n P := by dsimp [scale]; positivity
  have hL' : 1 ≤ Real.log (n : ℝ) := hL
  have hl4 : 1 ≤ (Real.log n)^4 := one_le_pow₀ hL'
  by_cases hsmall : Y ≤ q ∨ Y ≤ N
  · have hY : (Y : ℝ) ≤ scale n P := hsmall.elim
      (fun h => (Nat.cast_le.mpr h).trans (hhigh.trans (hB.trans hcut)))
      (fun h => (Nat.cast_le.mpr h).trans (hNn.trans (hroot.trans hcut)))
    exact (prime_mass Y t).trans ((mul_le_mul_of_nonneg_left hY (by norm_num)).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hl4]) hscale))
  push Not at hsmall
  have happrox : |t-(a:ℝ)/q| ≤ 1/(q:ℝ)^2 := by
    apply happ.trans
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ_of_le hqB) hqr.le
  have hval := hN Y hsmall.2.le t (a:ℤ) q hq hcop.isCoprime (by simpa using happrox) hsmall.1.le
  have hYp : 0 < Y := by omega
  have hYr : (0 : ℝ) < Y := Nat.cast_pos.mpr hYp
  have hYn' : (Y : ℝ) ≤ n := by exact_mod_cast hYn
  obtain ⟨hu,hv⟩ := vaughan_denominator_terms hnr hsr hpr le_rfl (by exact_mod_cast hPq.le) hhigh
  have hen : OAI.Problem337.Vaughan.approximationEnvelope Y q ≤ 2*scale n P := by
    dsimp [OAI.Problem337.Vaughan.approximationEnvelope,scale]
    have h₁ := (div_le_div_of_nonneg_right hYn' (Real.sqrt_nonneg _)).trans hu
    have h₂ := Real.rpow_le_rpow hYr.le hYn' (by norm_num : (0 : ℝ) ≤ 4/5)
    have h₃ := (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hYn' hqr.le)).trans hv
    linarith only [h₁,h₂,h₃,Real.rpow_nonneg hnr.le (4/5)]
  have hlY := Real.log_le_log hYr hYn'
  have hlog4 := pow_le_pow_left₀ (Real.log_natCast_nonneg Y) hlY 4
  have ham := mul_le_mul (mul_le_mul_of_nonneg_left hlog4 (by norm_num : (0:ℝ)≤16200))
    hen (OAI.Problem337.Vaughan.approximationEnvelope_nonneg _ _ hYr.le) (by positivity)
  have hlogpow : Real.log (n : ℝ) ≤ (Real.log n)^4 := by
    simpa using pow_le_pow_right₀ hL' (by decide : 1 ≤ 4)
  have hres := mul_le_mul (mul_le_mul_of_nonneg_left
    ((Real.sqrt_le_sqrt hYn').trans (hroot.trans hcut)) (by norm_num : (0:ℝ)≤2))
    (hlY.trans hlogpow) (Real.log_natCast_nonneg Y) (by positivity)
  apply (prime_approx Y q t hYp hval).trans
  nlinarith only [add_le_add ham hres, mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) 4) hscale]

private theorem scale_sq_le {n P : ℕ} (hn : 0 < (n : ℝ)) (hP : 0 < (P : ℝ)) :
    (scale n P)^2 ≤ 2*((n : ℝ)*((n : ℝ)/P+(n : ℝ)^(3/5 : ℝ))) := by
  let u := (n : ℝ)/Real.sqrt P
  let v := (n : ℝ)^(4/5 : ℝ)
  have hu : u^2 = (n : ℝ)*((n : ℝ)/P) := by
    dsimp [u]; rw [div_pow,Real.sq_sqrt hP.le]; ring
  have hv : v^2 = (n : ℝ)*(n : ℝ)^(3/5 : ℝ) := by
    dsimp [v]; rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_one_add' hn.le (by norm_num)]
    norm_num
  change (u+v)^2 ≤ _
  calc (u+v)^2 ≤ 2*(u^2+v^2) := by nlinarith only [sq_nonneg (u-v)]
       _ = _ := by rw [hu,hv]; ring

def exponents (X : ℕ) := Icc 1 (Nat.log 2 X/2)

def representations (m : ℕ) :=
  ((range (m+1)).filter (fun p => p.Prime ∧ (m-p).Prime)).card

def failedShifts (X : ℕ) :=
  (Ico X (2*X)).filter (fun n => Even n ∧
    0 < ((exponents X).filter (fun e => representations (n-2^e)=0)).card)

end
end GoldbachPolynomialMinor205

open Finset Goldbach GoldbachSmoothing GoldbachTwistedMellin

namespace GoldbachNarrowMajor

noncomputable section

/-- The coefficients obtained when summation by parts puts the weight on
the cumulative sums over a single dyadic block. -/
def abelWeight (a b : ℕ) (w : ℕ → ℂ) : (ℕ → ℂ) →ₗ[ℂ] ℂ where
  toFun F := w b * F b + ∑ j ∈ Ioc a (b - 1), (w j - w (j + 1)) * F j
  map_add' F G := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    abel
  map_smul' c F := by
    change w b * (c * F b) + (∑ j ∈ Ioc a (b - 1), (w j - w (j + 1)) * (c * F j)) =
      c * (w b * F b + ∑ j ∈ Ioc a (b - 1), (w j - w (j + 1)) * F j)
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      ring

def abelVariation (a b : ℕ) (w : ℕ → ℂ) : ℝ :=
  ‖w b‖ + ∑ j ∈ Ioc a (b - 1), ‖w j - w (j + 1)‖

private theorem abel_eq (a b : ℕ) (hab : a < b) (w f : ℕ → ℂ) :
    (∑ k ∈ Ioc a b, w k * f k) =
      abelWeight a b w (fun j => ∑ k ∈ Ioc a j, f k) := by
  let g := fun k => if a < k then f k else 0
  have hg (j : ℕ) : (∑ k ∈ range (j + 1), g k) = ∑ k ∈ Ioc a j, f k := by
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, Nat.lt_succ_iff]
    tauto
  have h := Finset.sum_Ioc_by_parts w g hab
  simp only [smul_eq_mul, hg, Ioc_self, sum_empty, mul_zero, sub_zero] at h
  calc
    _ = ∑ k ∈ Ioc a b, w k * g k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [g, (Finset.mem_Ioc.mp hk).1]
    _ = _ := by
      rw [h]
      change _ = w b * (∑ k ∈ Ioc a b, f k) +
        ∑ j ∈ Ioc a (b - 1), (w j - w (j + 1)) * (∑ k ∈ Ioc a j, f k)
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring

private theorem abel_norm_le (a b : ℕ) (w F : ℕ → ℂ) (B : ℝ)
    (hF : ∀ j ∈ Ioc a b, ‖F j‖ ≤ B) (hab : a < b) :
    ‖abelWeight a b w F‖ ≤ abelVariation a b w * B := by
  let d := fun j => w j - w (j + 1)
  have hb := hF b (mem_Ioc.mpr ⟨hab, le_rfl⟩)
  have hj : ∀ j ∈ Ioc a (b - 1), ‖F j‖ ≤ B := by
    intro j hj
    obtain ⟨hl, hr⟩ := mem_Ioc.mp hj
    exact hF j (mem_Ioc.mpr ⟨hl, hr.trans (Nat.sub_le _ _)⟩)
  calc
    _ ≤ ‖w b * F b‖ + ‖∑ j ∈ Ioc a (b - 1), d j * F j‖ := norm_add_le _ _
    _ ≤ ‖w b‖ * B + ∑ j ∈ Ioc a (b - 1), ‖d j‖ * B := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum fun j h => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hj j h) (norm_nonneg _)
    _ = _ := by
      dsimp only [abelVariation, d]
      rw [add_mul, Finset.sum_mul]

/-- The model transform for the smoothed finite prime sum. -/
def weightedTransform (a b : ℕ) (β : ℝ) (w : ℕ → ℂ) (s : ℂ) : ℂ :=
  abelWeight a b w (fun j => transform (a : ℝ) (j : ℝ) β s)

/-- Partial summation of the existing explicit formula. The same finite
zero set applies to every initial segment, so the weighted error has only the
variation factor from the weight. -/
theorem weighted_explicit_formula {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1 / 8) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (a b : ℕ) (X β : ℝ) (w : ℕ → ℂ),
      1 ≤ X → X ≤ (a : ℝ) → a < b → (b : ℝ) + 1 ≤ 2 * X → |β| ≤ 1 →
      ‖(∑ k ∈ Ioc a b, w k * (twistedCoefficient χ k * phase β k)) -
        (principalFlag χ * weightedTransform a b β w 1 -
          ∑ z ∈ exceptionalZeros χ (heightCut X),
            (analyticOrderNatAt (regularizedL χ) z : ℂ) * weightedTransform a b β w z)‖ ≤
        abelVariation a b w *
          (C * X ^ (1 / 2 + 2 * d) * (logBudget q X) ^ 2 *
            (1 + Real.sqrt (1 + 4 * |β| * X) + Real.log (heightCut X))) := by
  obtain ⟨C, hC, model⟩ := fixed_dyadic_model hd hd'
  refine ⟨C, hC, ?_⟩
  intro q _ χ a b X β w hX ha hab hb hβ
  let F := fun j => ∑ k ∈ Ioc a j, twistedCoefficient χ k * phase β k
  let M := fun j : ℕ => principalFlag χ * transform (a : ℝ) (j : ℝ) β 1 -
    fixedZeroTerm χ (a : ℝ) (j : ℝ) X β
  let W := abelWeight a b w
  have hM : W M = principalFlag χ * weightedTransform a b β w 1 -
      ∑ z ∈ exceptionalZeros χ (heightCut X),
        (analyticOrderNatAt (regularizedL χ) z : ℂ) * weightedTransform a b β w z := by
    have hm : M = (principalFlag χ) • (fun j : ℕ => transform a j β 1) -
        ∑ z ∈ exceptionalZeros χ (heightCut X),
          (analyticOrderNatAt (regularizedL χ) z : ℂ) •
            (fun j : ℕ => transform a j β z) := by
      funext j
      simp only [M, fixedZeroTerm, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [hm, map_sub, map_sum, map_smul]
    simp only [map_smul, smul_eq_mul, W, weightedTransform]
  rw [abel_eq a b hab, ← hM]
  change ‖W F - W M‖ ≤ _
  rw [← map_sub]
  apply abel_norm_le _ _ _ _ _ ?_ hab
  intro j hj
  obtain ⟨hl, hr⟩ := mem_Ioc.mp hj
  exact model q χ a j X β hX ha
    (by exact_mod_cast (show a + 1 ≤ j by omega))
    (by
      have hc : (j : ℝ) ≤ b := by exact_mod_cast hr
      linarith only [hc, hb])
    hβ

end

end GoldbachNarrowMajor


open Filter Finset GoldbachPolynomialMinor205
open GoldbachMovingWindows (primeLog)

namespace GoldbachNarrowMajor

/-- The same minor-arc pointwise bound works after applying weights of
bounded variation inside any subinterval of the prime sum. -/
theorem weighted_minor_prefix : ∀ᶠ n : ℕ in atTop, ∀ P : ℕ, 1 ≤ P → P ≤ n →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ GoldbachPolynomialMinor205.arcs n P →
    ∀ a b : ℕ, a < b → b ≤ n → ∀ w : ℕ → ℂ,
    ‖∑ k ∈ Finset.Ioc a b, w k * ((primeLog k : ℂ) * wave ((k : ℝ) * t))‖ ≤
      abelVariation a b w * (100000 * (Real.log n) ^ 4 * scale n P) := by
  filter_upwards [prefix_bound] with n hn
  intro P hP hPn t ht hminor a b hab hbn w
  rw [abel_eq a b hab]
  apply abel_norm_le _ _ _ _ _ ?_ hab
  intro j hj
  have ha : a ≤ j := (Finset.mem_Ioc.mp hj).1.le
  have hjn : j ≤ n := (Finset.mem_Ioc.mp hj).2.trans hbn
  have han : a ≤ n := ha.trans hjn
  have equ :
      (∑ k ∈ Finset.Ioc a j, (primeLog k : ℂ) * wave ((k : ℝ) * t)) =
        series j primeLog t - series a primeLog t := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sub]
    · rfl
    · omega
  rw [equ]
  refine (norm_sub_le _ _).trans ((add_le_add
    (hn P hP hPn t ht hminor j hjn) (hn P hP hPn t ht hminor a han)).trans_eq ?_)
  ring

end GoldbachNarrowMajor

end

section


namespace GoldbachCenterWindows

open Finset

def centralWindow (X : ℕ) := (Icc 0 (4*X)).filter (fun m => 5*X ≤ 2*m ∧ 2*m ≤ 7*X)

theorem mem_centralWindow {X m : ℕ} :
    m ∈ centralWindow X ↔ 5*X ≤ 2*m ∧ 2*m ≤ 7*X := by
  simp only [centralWindow, mem_filter, mem_Icc, zero_le, true_and]
  omega

theorem centralWindows_cover (Z : ℕ) (hZ : 100 ≤ Z) :
    Icc Z (2*Z) ⊆ centralWindow (Z/3) ∪ centralWindow (4*Z/9) ∪ centralWindow (16*Z/27) := by
  intro m hm
  obtain ⟨hlo, hhi⟩ := mem_Icc.mp hm
  simp only [mem_union, mem_centralWindow]
  by_cases h : 2*m ≤ 7*(Z/3)
  · exact Or.inl (Or.inl ⟨by omega, h⟩)
  · by_cases h' : 2*m ≤ 7*(4*Z/9)
    · exact Or.inl (Or.inr ⟨by omega, h'⟩)
    · exact Or.inr ⟨by omega, by omega⟩

theorem dyadic_count_of_central_bound (E : ℕ → Prop) [DecidablePred E]
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (N : ℕ)
    (h : ∀ X ≥ N, (((centralWindow X).filter E).card : ℝ) ≤ C * (X : ℝ)^a) :
    ∀ Z ≥ max 100 (3*N+1),
      (((Icc Z (2*Z)).filter E).card : ℝ) ≤ (3*C) * (Z : ℝ)^a := by
  intro Z hZ
  have hsub : (Icc Z (2*Z)).filter E ⊆
      ((centralWindow (Z/3)).filter E) ∪ ((centralWindow (4*Z/9)).filter E) ∪
        ((centralWindow (16*Z/27)).filter E) := by
    intro m hm
    obtain ⟨hmI, hE⟩ := mem_filter.mp hm
    have hc := mem_union.mp (centralWindows_cover Z (le_of_max_le_left hZ) hmI)
    rcases hc with hc | hc
    · rcases mem_union.mp hc with ⟨hL⟩ | ⟨hM⟩
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hL, hE⟩))
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hM, hE⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨hc, hE⟩)
  have hb {X : ℕ} (hNX : N ≤ X) (hXZ : X ≤ Z) :
      (((centralWindow X).filter E).card : ℝ) ≤ C * (Z : ℝ)^a :=
    (h X hNX).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast hXZ) ha) hC)
  have h₁ := hb (X := Z/3) (by omega) (by omega)
  have h₂ := hb (X := 4*Z/9) (by omega) (by omega)
  have h₃ := hb (X := 16*Z/27) (by omega) (by omega)
  have hcount : (((Icc Z (2*Z)).filter E).card : ℝ) ≤
      (((centralWindow (Z/3)).filter E).card : ℝ) +
      (((centralWindow (4*Z/9)).filter E).card : ℝ) +
      (((centralWindow (16*Z/27)).filter E).card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans
      ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
  linarith

end GoldbachCenterWindows

end

section

namespace GoldbachWeightedException

open Finset Filter MeasureTheory
open GoldbachSmoothWindow GoldbachPrincipalSeries
open GoldbachPolynomialMinor205 (series wave scale representations failedShifts exponents)
open GoldbachMovingWindows (primeLog primeLog_energy)
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open scoped Topology

noncomputable section

def cutoff (X : ℕ) : ℕ := GoldbachMajorCutoff.value X

theorem chosen_cutoff_bounds {X : ℕ} (hX : 2^200 ≤ 4*X) :
    let n := 4*X
    let P := cutoff X
    1 ≤ P ∧ ((n:ℕ):ℝ)^(1/5:ℝ) ≤ (P:ℝ) ∧
      (P:ℝ) ≤ ((n:ℕ):ℝ)^(41/200:ℝ) ∧ 2*P ≤ n ∧ 2*P^2 < n := by
  let n := 4*X
  let P := cutoff X
  let x : ℝ := n
  have hnR : (2 : ℝ)^200 ≤ x := by dsimp only [x,n]; exact_mod_cast hX
  have hX1 : 1 < x := (by norm_num : (1:ℝ) < 2^200).trans_le hnR
  have hx := zero_lt_one.trans hX1
  have hPmain : x^(1/5:ℝ) ≤ (P:ℝ) := GoldbachMajorCutoff.principalLower X hX
  have hPupper : (P:ℝ) ≤ x^(41/200:ℝ) := GoldbachMajorCutoff.upper X hX
  have hP1R : (1:ℝ) ≤ P := (Real.one_le_rpow hX1.le (by norm_num)).trans hPmain
  have hP1 : 1 ≤ P := by exact_mod_cast hP1R
  have hsep : 2*P^2 < n := by
    have h2 : (2:ℝ) < x^(59/100:ℝ) := by
      have hsmall : (2:ℝ) ≤ x^(1/200:ℝ) := by
        calc
          _ = ((2:ℝ)^200)^(1/200:ℝ) := by
            rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2)]
            norm_num [Real.rpow_one]
          _ ≤ _ := Real.rpow_le_rpow (by positivity) hnR (by norm_num)
      exact hsmall.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hX1 (by norm_num))
    have hb : (P:ℝ)^2 ≤ x^(41/100:ℝ) := by
      have h := pow_le_pow_left₀ (Nat.cast_nonneg P) hPupper 2
      rwa [← Real.rpow_mul_natCast hx.le,show (41/200:ℝ)*(2:ℕ)=41/100 by norm_num] at h
    have ht : 2*x^(41/100:ℝ)<x := calc
      _ < x^(59/100:ℝ)*x^(41/100:ℝ) :=
        mul_lt_mul_of_pos_right h2 (Real.rpow_pos_of_pos hx _)
      _ = _ := by rw [← Real.rpow_add hx]; norm_num
    have hcast : (2:ℝ)*(P:ℝ)^2 < (n:ℝ) :=
      (mul_le_mul_of_nonneg_left hb (by norm_num)).trans_lt ht
    exact_mod_cast hcast
  have hP2 : P ≤ P^2 := by simpa only [one_mul,pow_two] using Nat.mul_le_mul_right P hP1
  exact ⟨hP1,hPmain,hPupper,((Nat.mul_le_mul_left 2 hP2).trans_lt hsep).le,hsep⟩

def primeWeight (X k : ℕ) : ℝ := scaledWeight (X : ℝ) (k : ℝ) * primeLog k

def primeSeries (X : ℕ) : ℝ → ℂ := series (4 * X) (primeWeight X)

def integrand (X m : ℕ) (t : ℝ) : ℂ := (primeSeries X t) ^ 2 * wave (-(m : ℝ) * t)

def majorCoefficient (X m : ℕ) : ℂ :=
  ∫ t in GoldbachNarrowMajor.arcs (4 * X) (cutoff X) ∩ Set.Icc (0 : ℝ) 1, integrand X m t

def minorCoefficient (X m : ℕ) : ℂ :=
  intervalIntegral ((GoldbachNarrowMajor.arcs (4 * X) (cutoff X))ᶜ.indicator (integrand X m)) 0 1 volume

def ordinaryException (m : ℕ) : Prop := Even m ∧ representations m = 0

instance : DecidablePred ordinaryException := fun m => inferInstanceAs (Decidable (Even m ∧ representations m = 0))


/-- Restrict the weighted exponential sum to the block of the local explicit formula. -/
theorem primeSeries_eq_block {X : ℕ} (hX : 0 < X) (t : ℝ) : primeSeries X t =
    ∑ k ∈ Finset.Ioc X (2 * X - 1), (scaledWeight (X : ℝ) (k : ℝ) : ℂ) *
      ((primeLog k : ℂ) * wave ((k : ℝ) * t)) := by
  unfold primeSeries series
  have hsub : Finset.Ioc X (2 * X - 1) ⊆ Finset.range (4 * X + 1) := by
    intro k hk
    exact mem_range.mpr (by have h := (mem_Ioc.mp hk).2; omega)
  rw [← Finset.sum_subset hsub (fun k _ hk => ?_)]
  · apply Finset.sum_congr rfl
    intro k _
    simp [primeWeight, Complex.ofReal_mul, mul_assoc]
  · have h : k ≤ X ∨ 2 * X ≤ k := by
      simp only [Finset.mem_Ioc] at hk
      omega
    simp [primeWeight, support hX h]

private theorem weight_energy (X : ℕ) :
    (∑ k ∈ Finset.range (4 * X + 1), (primeWeight X k)^2) ≤
      Real.log 4 * ((4 * X : ℕ) : ℝ) * Real.log ((4 * X : ℕ) : ℝ) := by
  refine (Finset.sum_le_sum (g := fun k => (primeLog k)^2) fun k _ => ?_).trans (primeLog_energy (4 * X))
  obtain ⟨hl, hu⟩ := weight_range ((k : ℝ) / (X : ℝ))
  rw [primeWeight, mul_pow]
  have hw : (scaledWeight (X : ℝ) (k : ℝ)) ^ 2 ≤ 1 := by
    simpa only [scaledWeight, one_pow] using pow_le_pow_left₀ hl hu 2
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (sq_nonneg (primeLog k))

private theorem weight_variation : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 0 < X →
    GoldbachNarrowMajor.abelVariation X (2 * X - 1)
       (fun k => (scaledWeight (X : ℝ) (k : ℝ) : ℂ)) ≤ C := by
  obtain ⟨K, hK, hvar⟩ := GoldbachPrincipalSeries.smooth_weight_variation
  refine ⟨1 + 4 * K, by positivity, ?_⟩
  intro X hX
  let w (k : ℕ) := scaledWeight (X : ℝ) (k : ℝ)
  have hw (k : ℕ) : 0 ≤ w k ∧ w k ≤ 1 := weight_range ((k : ℝ) / (X : ℝ))
  have hsub : Finset.Ioc X (2 * X - 1 - 1) ⊆ Finset.range (2 * X) := by
    intro k hk
    have hh := (mem_Ioc.mp hk).2
    exact mem_range.mpr (by omega)
  have hterm (k : ℕ) : ‖((w k : ℝ) : ℂ) - ((w (k + 1) : ℝ) : ℂ)‖ = |w (k + 1) - w k| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  change ‖(w (2 * X - 1) : ℂ)‖ + ∑ j ∈ Finset.Ioc X (2 * X - 1 - 1),
    ‖(w j : ℂ) - (w (j + 1) : ℂ)‖ ≤ 1 + 4 * K
  simp_rw [hterm]
  refine add_le_add ?_ ?_
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _).1]
    exact (hw _).2
  · apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)).trans
    have hh := hvar X hX
    change |w 0| + (∑ j ∈ Finset.range (2 * X), |w (j + 1) - w j|) + |w (2 * X)| ≤ 4 * K at hh
    linarith only [hh, abs_nonneg (w 0), abs_nonneg (w (2 * X))]

private theorem arc_measurable (X : ℕ) : MeasurableSet (GoldbachNarrowMajor.arcs (4 * X) (cutoff X)) :=
  GoldbachEstermann.measurable_block_arcs (cutoff X) (4 * X)

private theorem integrand_continuous (X m : ℕ) : Continuous (integrand X m) := by
  unfold integrand primeSeries series wave
  fun_prop

theorem major_eq_indicator (X m : ℕ) : majorCoefficient X m =
    intervalIntegral ((GoldbachNarrowMajor.arcs (4 * X) (cutoff X)).indicator (integrand X m)) 0 1 volume := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), ← integral_Icc_eq_integral_Ioc,
    setIntegral_indicator (arc_measurable X), Set.inter_comm]
  rfl

private theorem coefficients_cancel {X m : ℕ} (hm : representations m = 0) :
    majorCoefficient X m + minorCoefficient X m = 0 := by
  have hpairs (i j : ℕ) (he : i + j = m) : primeWeight X i * primeWeight X j = 0 := by
    have hn : ¬ (i.Prime ∧ j.Prime) := by
      intro h
      have hf : i ∈ (Finset.range (m + 1)).filter (fun p => p.Prime ∧ (m - p).Prime) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h.1, ?_⟩
        rw [show m - i = j by omega]
        exact h.2
      exact (Nat.ne_of_gt (Finset.card_pos.mpr ⟨i, hf⟩)) hm
    by_cases hi : i.Prime
    · have hj : ¬ j.Prime := fun h => hn ⟨hi, h⟩
      simp [primeWeight, primeLog, hj]
    · simp [primeWeight, primeLog, hi]
  have hz : (∫ t in (0 : ℝ)..1, integrand X m t) = 0 :=
    WindowBessel.ExceptionalCoefficients.zero_from_pairs (primeWeight X) m (4 * X) hpairs
  rw [major_eq_indicator]
  exact (WindowBessel.ExceptionalCoefficients.indicator_integral_split
    (arc_measurable X) ((integrand_continuous X m).intervalIntegrable 0 1)).trans hz

end

end GoldbachWeightedException

end

section

namespace GoldbachWeightedException

open Finset Filter MeasureTheory
open GoldbachSmoothWindow GoldbachPrincipalSeries
open GoldbachPolynomialMinor205 (series wave scale representations failedShifts exponents)
open GoldbachMovingWindows (primeLog primeLog_energy)
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open scoped Topology

noncomputable section

private theorem minor_fourth_moment : ∃ D : ℝ, 0 < D ∧ ∀ᶠ X : ℕ in atTop, ∀ M : ℕ,
    let n : ℕ := 4 * X
    (∑ m ∈ Finset.range M, ‖minorCoefficient X m‖ ^ 2) ≤
      (D * (100000 * Real.log n ^ 4 * scale n (cutoff X))) ^ 2 *
        (Real.log 4 * (n : ℝ) * Real.log n) := by
  obtain ⟨D, hD, hvar⟩ := weight_variation
  obtain ⟨N, hN⟩ := eventually_atTop.1 GoldbachNarrowMajor.weighted_minor_prefix
  refine ⟨D, hD, ?_⟩
  filter_upwards [eventually_ge_atTop (max N (2 ^ 200))] with X hX
  intro M
  let n := 4 * X
  let P := cutoff X
  have hX0 : 0 < X := by
    have h := (le_max_right N (2 ^ 200)).trans hX
    exact (by positivity : 0 < (2 ^ 200 : ℕ)).trans_le h
  have hn : 2 ^ 200 ≤ n := ((le_max_right N _).trans hX).trans (by dsimp [n]; omega)
  have hnN : N ≤ n := ((le_max_left N _).trans hX).trans (by dsimp [n]; omega)
  obtain ⟨hP, _, _, hPn, _⟩ := GoldbachWeightedException.chosen_cutoff_bounds (X:=X) hn
  have hPN : P ≤ n := by change 2 * P ≤ n at hPn; omega
  have hP' : 1 ≤ P := hP
  let B := 100000 * Real.log (n : ℝ) ^ 4 * scale n P
  have hB : 0 ≤ B := by unfold B scale; positivity
  have hminor : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ GoldbachNarrowMajor.arcs n P →
      ‖series n (primeWeight X) t‖ ≤ D * B := by
    intro t ht hnot
    change ‖primeSeries X t‖ ≤ D * B
    rw [primeSeries_eq_block hX0]
    have hab : X < 2 * X - 1 := by
      have h : 2 ≤ X := (by norm_num : 2 ≤ 2 ^ (200 : ℕ)).trans ((le_max_right N _).trans hX)
      omega
    have h := hN n hnN P hP' hPN t ht hnot X (2 * X - 1) hab (by dsimp [n]; omega)
      (fun k => (scaledWeight (X : ℝ) (k : ℝ) : ℂ))
    exact h.trans (mul_le_mul_of_nonneg_right (hvar X hX0) hB)
  exact (WindowBessel.minorFourthMoment n M (primeWeight X) (GoldbachNarrowMajor.arcs n P)
    (D * B) (arc_measurable X) (mul_nonneg hD.le hB) hminor).trans
      (mul_le_mul_of_nonneg_left (weight_energy X) (sq_nonneg _))

private theorem scale_budget {n P : ℕ} (hn : 0 < n) (hP : 1 ≤ P)
    (hcut : (n : ℝ) ^ (203 / 1000 : ℝ) ≤ 2 * (P : ℝ)) :
    (scale n P)^2 ≤ 2 * (n : ℝ) * (3 * (n : ℝ) ^ (797 / 1000 : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hq : (n : ℝ) / P ≤ 2 * (n : ℝ) ^ (797 / 1000 : ℝ) := by
    apply (div_le_iff₀ hP0).mpr
    have h := mul_le_mul_of_nonneg_left hcut (Real.rpow_nonneg hn0.le (797/1000 : ℝ))
    rw [← Real.rpow_add hn0, show (797 / 1000 : ℝ) + 203 / 1000 = 1 by norm_num, Real.rpow_one] at h
    linarith only [h]
  have hterms : (n : ℝ) / P + (n : ℝ) ^ (3 / 5 : ℝ) ≤ 3 * (n : ℝ) ^ (797 / 1000 : ℝ) := by
    linarith only [hq, Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (3/5 : ℝ) ≤ 797/1000)]
  calc
    _ ≤ 2 * ((n : ℝ) * ((n : ℝ) / P + (n : ℝ) ^ (3 / 5 : ℝ))) :=
      GoldbachPolynomialMinor205.scale_sq_le hn0 hP0
    _ = 2 * (n : ℝ) * ((n : ℝ) / P + (n : ℝ) ^ (3 / 5 : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hterms (by positivity)

end

end GoldbachWeightedException

end

section

namespace GoldbachWeightedException

open Finset Filter MeasureTheory
open GoldbachSmoothWindow GoldbachPrincipalSeries
open GoldbachPolynomialMinor205 (series wave scale representations failedShifts exponents)
open Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc (unitMean)
open scoped Topology

noncomputable section

/-- The finite form of the union bound over all permitted binary shifts. -/
theorem failed_shifts_card {X : ℕ} (hX : 1 ≤ X) :
    (failedShifts X).card ≤ Nat.sqrt X + (Nat.log 2 X / 2) *
      ((Finset.Icc X (2 * X)).filter ordinaryException).card := by
  let I := exponents X
  let E := (Finset.Icc X (2 * X)).filter ordinaryException
  let B := Finset.Ico X (X + Nat.sqrt X)
  have hsub : failedShifts X ⊆ B ∪ I.biUnion (fun e => E.image (fun m => m + 2 ^ e)) := by
    intro n hn
    obtain ⟨hI, heven, hp⟩ := mem_filter.mp hn
    obtain ⟨e, he⟩ := card_pos.mp hp
    obtain ⟨heI, hrep⟩ := mem_filter.mp he
    obtain ⟨hnlo, hnhi⟩ := mem_Ico.mp hI
    by_cases hbound : n < X + Nat.sqrt X
    · exact mem_union_left _ (mem_Ico.mpr ⟨hnlo, hbound⟩)
    have heb : 1 ≤ e ∧ e ≤ Nat.log 2 X / 2 := mem_Icc.mp heI
    have hpow := (Nat.pow_le_pow_right (by decide : 0 < 2)
      (show e * 2 ≤ Nat.log 2 X by omega)).trans (Nat.pow_log_le_self 2 (by omega : X ≠ 0))
    rw [pow_mul] at hpow
    have hsh : 2 ^ e ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by simpa only [sq] using hpow)
    have hev : Even (2 ^ e) := Even.pow_of_ne_zero (by decide : Even (2 : ℕ)) (by omega)
    have hle : 2 ^ e ≤ n := by omega
    apply mem_union_right
    refine mem_biUnion.mpr ⟨e, heI, mem_image.mpr ⟨n - 2 ^ e, ?_, Nat.sub_add_cancel hle⟩⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, (Nat.sub_le n _).trans hnhi.le⟩,
      (Nat.even_sub hle).2 (iff_of_true heven hev), hrep⟩
  have hu : (I.biUnion (fun e => E.image (fun m => m + 2 ^ e))).card ≤ I.card * E.card := calc
    _ ≤ ∑ e ∈ I, (E.image (fun m => m + 2 ^ e)).card := card_biUnion_le
    _ ≤ ∑ _e ∈ I, E.card := sum_le_sum (fun _ _ => card_image_le)
    _ = _ := by simp
  have h := (card_le_card hsub).trans (card_union_le _ _)
  exact h.trans (by simpa [B, I, E, exponents] using Nat.add_le_add_left hu B.card)

/-- One ordinary dyadic exceptional-set estimate pays every binary shift. -/
theorem failed_shifts_of_dyadic
    (H : ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      (((Finset.Icc X (2 * X)).filter ordinaryException).card : ℝ) ≤
        C * (X : ℝ) ^ (319 / 400 : ℝ)) :
    ∃ N : ℕ, ∀ X ≥ N, (failedShifts X).card ^ 5 ≤ X ^ 4 := by
  obtain ⟨C, hC, hE⟩ := H
  have ht := tendsto_natCast_atTop_atTop (R := ℝ)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 800)).comp_tendsto ht).bound h2
  have hp := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 800)).comp ht).eventually_ge_atTop (1 + C)
  apply eventually_atTop.1
  filter_upwards [hE, hs, hp, eventually_ge_atTop (1 : ℕ)] with X hcount hlog hgap hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXR : 0 < (X : ℝ) := zero_lt_one.trans_le hX1
  have hlog' : Real.log X ≤ Real.log 2 * (X : ℝ) ^ (1 / 800 : ℝ) := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg X),
      abs_of_nonneg (Real.rpow_nonneg hXR.le _)] using hlog
  have hL : ((Nat.log 2 X / 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (1 / 800 : ℝ) := calc
    _ ≤ Real.log X / Real.log 2 :=
      (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans (Real.natLog_le_logb X 2)
    _ ≤ _ := (div_le_iff₀ h2).2 (by simpa only [mul_comm] using hlog')
  have hEdge : ((Nat.sqrt X : ℕ) : ℝ) ≤ (X : ℝ) ^ (639 / 800 : ℝ) := calc
    _ ≤ Real.sqrt (X : ℝ) := (Real.le_sqrt (Nat.cast_nonneg _) hXR.le).2
      (by exact_mod_cast Nat.sqrt_le' X)
    _ ≤ _ := by rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hpair := mul_le_mul hL hcount (Nat.cast_nonneg _) (Real.rpow_nonneg hXR.le _)
  have hprod : ((Nat.log 2 X / 2 : ℕ) : ℝ) *
      (((Finset.Icc X (2 * X)).filter ordinaryException).card : ℝ) ≤ C * (X : ℝ) ^ (639 / 800 : ℝ) := by
    convert hpair using 1
    rw [← mul_assoc, mul_comm ((X : ℝ) ^ (1 / 800 : ℝ)) C, mul_assoc, ← Real.rpow_add hXR]
    norm_num
  have hCard : ((failedShifts X).card : ℝ) ≤ (Nat.sqrt X : ℕ) +
      ((Nat.log 2 X / 2 : ℕ) : ℝ) * (((Finset.Icc X (2 * X)).filter ordinaryException).card : ℝ) := by
    exact_mod_cast failed_shifts_card hX
  have hV : ((failedShifts X).card : ℝ) ≤ (X : ℝ) ^ (4 / 5 : ℝ) := calc
    _ ≤ (1 + C) * (X : ℝ) ^ (639 / 800 : ℝ) := by linarith only [hCard, hEdge, hprod]
    _ ≤ (X : ℝ) ^ (1 / 800 : ℝ) * (X : ℝ) ^ (639 / 800 : ℝ) :=
      mul_le_mul_of_nonneg_right hgap (by positivity)
    _ = _ := by rw [← Real.rpow_add hXR]; norm_num
  have hpw := pow_le_pow_left₀ (Nat.cast_nonneg _) hV 5
  rw [← Real.rpow_mul_natCast hXR.le] at hpw
  norm_num at hpw
  exact_mod_cast hpw


/-- Express the actual major coefficient in the same local windows as its model. -/
theorem major_eq_window_sum {X : ℕ} (hX : 2 ^ 200 ≤ 4 * X) (m : ℕ) :
    majorCoefficient X m =
      ∑ q ∈ Finset.Icc 1 (cutoff X), ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
        ∫ β in (-((cutoff X : ℝ) / ((q : ℝ) * ((4 * X : ℕ) : ℝ))))..
          ((cutoff X : ℝ) / ((q : ℝ) * ((4 * X : ℕ) : ℝ))), integrand X m (β + (a : ℝ) / q) := by
  obtain ⟨hP, _, _, _, hsep⟩ := GoldbachWeightedException.chosen_cutoff_bounds (X:=X) hX
  have hperiod : Function.Periodic (integrand X m) 1 :=
    phase_square_periodic (finiteModel_periodic (primeWeight X) (4 * X)) m
  exact GoldbachNarrowMajor.integral_torus_major_arcs (n := 4 * X) (P := cutoff X)
    hP hsep (integrand_continuous X m) hperiod

end

end GoldbachWeightedException

end

end

section


namespace GoldbachMajorEnergy

open Finset Complex GoldbachTwistedMellin
open scoped ComplexConjugate Classical

noncomputable section

private theorem norm_energy_of_columns {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] (K : A → B → ℂ) (D : A → ℝ)
    (hK : ∀ r s : A, (∑ b : B, conj (K r b) * K s b) =
      if r = s then (D r : ℂ) else 0) (f : A → ℂ) :
    (∑ b : B, ‖∑ r : A, f r * K r b‖ ^ 2) =
      ∑ r : A, D r * ‖f r‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.conj_mul']
  calc
    _ = ∑ b : B, ∑ r : A, ∑ s : A, conj (f r) * f s * (conj (K r b) * K s b) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
      ring
    _ = ∑ r : A, ∑ s : A, conj (f r) * f s * (∑ b : B, conj (K r b) * K s b) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [hK, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring

variable {q : ℕ} [NeZero q]

theorem additiveWeight_unit_factor (a : (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) :
    additiveWeight (a : ZMod q) χ = additiveWeight 1 χ * χ (a : ZMod q) := by
  have hgauss (u : ZMod q) :
      additiveWeight u χ = gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift u) / (q.totient : ℂ) := by
    rw [weight_expansion]
    congr 1
    unfold gaussSum
    apply sum_congr rfl
    intro r _
    simp only [AddChar.mulShift_apply, starRingEnd_apply, MulChar.star_apply']
    rw [mul_comm]
  rw [hgauss, hgauss, gaussSum_mulShift_eq, inv_inv, AddChar.mulShift_one]
  ring

theorem character_energy_identity (f : DirichletCharacter ℂ q → ℂ) :
    (∑ a : (ZMod q)ˣ, ‖∑ χ : DirichletCharacter ℂ q, f χ * additiveWeight (a : ZMod q) χ‖ ^ 2) =
      ∑ χ : DirichletCharacter ℂ q, (q.totient : ℝ) * ‖f χ * additiveWeight 1 χ‖ ^ 2 := by
  have horth (χ ψ : DirichletCharacter ℂ q) :
      (∑ b : (ZMod q)ˣ, conj (χ (b : ZMod q)) * ψ (b : ZMod q)) =
      if χ = ψ then (q.totient : ℂ) else 0 := by
    have he (b : ZMod q) : conj (χ b) * ψ b = (χ⁻¹ * ψ) b := by
      rw [MulChar.mul_apply, ← MulChar.star_apply', starRingEnd_apply]
    simp_rw [he]
    have hs (θ : DirichletCharacter ℂ q) :
        (∑ a : (ZMod q)ˣ, θ (a : ZMod q)) = ∑ a : ZMod q, θ a := by
      apply Fintype.sum_of_injective Units.val Units.val_injective
      · intro a ha
        exact MulChar.map_nonunit _ (fun ⟨b, hb⟩ => ha ⟨b, hb⟩)
      · intro a
        rfl
    rw [hs]
    by_cases h : χ = ψ
    · subst ψ
      rw [inv_mul_cancel, ite_eq_left rfl, MulChar.sum_one_eq_card_units,
        ZMod.card_units_eq_totient]
    · rw [ite_eq_right h, MulChar.sum_eq_zero_of_ne_one]
      intro hh
      apply h
      rw [← mul_left_cancel_iff (a := χ⁻¹), hh, inv_mul_cancel]
  rw [← norm_energy_of_columns (fun χ (b : (ZMod q)ˣ) => χ (b : ZMod q))
    (fun _ => (q.totient : ℝ)) (by simpa only [Complex.ofReal_natCast] using horth)
    (fun χ => f χ * additiveWeight 1 χ)]
  simp_rw [additiveWeight_unit_factor, mul_assoc]

theorem character_energy_conductor_bound (f : DirichletCharacter ℂ q → ℂ)
    (hgauss : ∀ χ : DirichletCharacter ℂ q, ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 ≤ χ.conductor) :
    (∑ a : (ZMod q)ˣ, ‖∑ χ : DirichletCharacter ℂ q, f χ * additiveWeight (a : ZMod q) χ‖ ^ 2) ≤
      ∑ χ : DirichletCharacter ℂ q, (χ.conductor : ℝ) / q.totient * ‖f χ‖ ^ 2 := by
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [character_energy_identity]
  apply sum_le_sum
  intro χ _
  have hf : additiveWeight 1 χ = gaussSum χ⁻¹ ZMod.stdAddChar / (q.totient : ℂ) := by
    rw [weight_expansion]
    simp only [gaussSum, one_mul, ← MulChar.star_apply', starRingEnd_apply]
    congr 1
    exact Finset.sum_congr rfl (fun r _ => mul_comm _ _)
  rw [hf, norm_mul, norm_div, Complex.norm_natCast, mul_pow, div_pow]
  calc
    _ = ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 / (q.totient : ℝ) * ‖f χ‖ ^ 2 := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hgauss χ) hφ.le) (sq_nonneg _)

theorem reduced_fraction_energy_le (f : DirichletCharacter ℂ q → ℂ) :
    (∑ a : (ZMod q)ˣ, ‖∑ χ : DirichletCharacter ℂ q, f χ * additiveWeight (a : ZMod q) χ‖ ^ 2) ≤
      ∑ χ : DirichletCharacter ℂ q, (χ.conductor : ℝ) / q.totient * ‖f χ‖ ^ 2 := by
  apply character_energy_conductor_bound
  intro χ
  have hs := B13BilateralVaughanReductionProof.DyadicMixedB4CharacterFactorBound.norm_dirichlet_gauss_standard χ⁻¹
  rw [DirichletCharacter.conductor_inv] at hs
  exact (pow_le_pow_left₀ (norm_nonneg _) hs 2).trans_eq (Real.sq_sqrt (Nat.cast_nonneg _))

end
end GoldbachMajorEnergy

end

section

namespace GoldbachWeightedMajorResidual

open Finset Filter MeasureTheory Goldbach GoldbachSmoothing GoldbachTwistedMellin
open GoldbachNarrowMajor GoldbachSmoothWindow GoldbachPrincipalSeries
open GoldbachWeightedException (cutoff primeSeries)
open Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc (unitMean)
open scoped Topology

noncomputable section

private abbrev block (X : ℕ) : Finset ℕ := Finset.Ioc X (2 * X - 1)


/-- The angle in the explicit formula is in radians, while the arc variable is in turns. -/
def zeroTerm {q : ℕ} [NeZero q] (X : ℕ) (χ : DirichletCharacter ℂ q) (β : ℝ) : ℂ :=
  ∑ z ∈ exceptionalZeros χ (heightCut (X : ℝ)),
    (analyticOrderNatAt (regularizedL χ) z : ℂ) *
      weightedTransform X (2 * X - 1) (γ β) (w X) z

def correction {q : ℕ} [NeZero q] (X : ℕ) (a : ZMod q) (β : ℝ) : ℂ :=
  ∑ χ : DirichletCharacter ℂ q, additiveWeight a χ * zeroTerm X χ β

def arcCorrection (X q a : ℕ) (β : ℝ) : ℂ :=
  if hq : q ≠ 0 then @correction q ⟨hq⟩ X (a : ZMod q) β else 0

def discreteModel (X : ℕ) (β : ℝ) : ℂ :=
  finiteModel (fun k => scaledWeight (X : ℝ) (k : ℝ)) (2 * X) β

def arcRadius (X q : ℕ) : ℝ := (cutoff X : ℝ) / ((q : ℝ) * ((4 * X : ℕ) : ℝ))

def arcResidual (X q a : ℕ) (β : ℝ) : ℂ :=
  primeSeries X ((a : ℝ) / q + β) - unitMean q a * discreteModel X β +
    arcCorrection X q a β

private theorem phase_angle (β : ℝ) (k : ℕ) :
    GoldbachTwistedMellin.phase (γ β) k = GoldbachPolynomialMinor205.wave ((k : ℝ) * β) := by
  unfold GoldbachTwistedMellin.phase GoldbachPolynomialMinor205.wave
  congr 1
  push_cast
  ring

private theorem model_eq_block {X : ℕ} (hX : 0 < X) (β : ℝ) : discreteModel X β =
    ∑ k ∈ block X, w X k * GoldbachTwistedMellin.phase (γ β) k := by
  unfold discreteModel finiteModel
  have hsub : block X ⊆ Finset.range (2 * X + 1) := by
    intro k hk
    exact mem_range.mpr (by have h := (mem_Ioc.mp hk).2; omega)
  rw [← Finset.sum_subset hsub (fun k _ hk => ?_)]
  · apply Finset.sum_congr rfl
    intro k _
    rw [phase_angle]
    rfl
  · have h : k ≤ X ∨ 2 * X ≤ k := by simp only [block, Finset.mem_Ioc] at hk; omega
    simp [GoldbachWeightedException.support hX h]

private theorem unitMean_of_cast (q a : ℕ) [NeZero q] :
    GoldbachGRHWindow.additiveModel q (a : ZMod q) = unitMean q a := by
  rw [GoldbachGRHWindow.additiveModel_eq_reduced_sum, unitMean]
  apply congrArg (fun z : ℂ => z / (q.totient : ℂ))
  apply Finset.sum_congr rfl
  intro k _
  unfold Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.phase
  congr 1
  push_cast
  ring

private theorem weighted_prime_removal {q : ℕ} (χ : DirichletCharacter ℂ q)
    {a b n : ℕ} (hab : a < b) (hb : b ≤ n) (hn : 1 ≤ n) (β : ℝ) (W : ℕ → ℂ) :
    ‖(∑ k ∈ Finset.Ioc a b, W k * ((GoldbachGRHWindow.primeLog k * phase β k) * χ (k : ZMod q))) -
      (∑ k ∈ Finset.Ioc a b, W k * (twistedCoefficient χ k * phase β k))‖ ≤
      abelVariation a b W * (2 * Real.sqrt n * Real.log n) := by
  rw [GoldbachNarrowMajor.abel_eq a b hab, GoldbachNarrowMajor.abel_eq a b hab, ← map_sub]
  apply GoldbachNarrowMajor.abel_norm_le a b W _ _ _ hab
  intro j hj
  exact prime_removal χ a j n ((mem_Ioc.mp hj).2.trans hb) hn β

private theorem weighted_principal_approx {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (W : ℕ → ℂ) (β : ℝ) :
    ‖weightedTransform a b β W 1 - (∑ k ∈ Finset.Ioc a b, W k * phase β k)‖ ≤
      abelVariation a b W * (((b : ℝ) - a) * |β|) := by
  rw [weightedTransform, GoldbachNarrowMajor.abel_eq a b hab, ← map_sub]
  apply GoldbachNarrowMajor.abel_norm_le a b W _ _ _ hab
  intro j hj
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hj
  refine (principal_approx ha hlo β).trans (mul_le_mul_of_nonneg_right (sub_le_sub_right ?_ _) (abs_nonneg _))
  exact_mod_cast hhi

private def charPrime {q : ℕ} (X : ℕ) (χ : DirichletCharacter ℂ q) (β : ℝ) : ℂ :=
  ∑ k ∈ block X, w X k * ((GoldbachGRHWindow.primeLog k * phase (γ β) k) * χ (k : ZMod q))

private def charResidual {q : ℕ} [NeZero q] (X : ℕ) (χ : DirichletCharacter ℂ q) (β : ℝ) : ℂ :=
  charPrime X χ β - (if χ = 1 then discreteModel X β else 0) + zeroTerm X χ β

private def nonunitTerm {q : ℕ} [NeZero q] (X : ℕ) (a : ZMod q) (β : ℝ) : ℂ :=
  ∑ k ∈ (block X).filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)),
    (w X k * (GoldbachGRHWindow.primeLog k * phase (γ β) k)) * ZMod.stdAddChar (a * (k : ZMod q))

private theorem nonunit_bound {q : ℕ} [NeZero q] (X : ℕ) (a : ZMod q) (β : ℝ) :
    ‖nonunitTerm X a β‖ ≤ Real.log (q : ℝ) := by
  unfold nonunitTerm
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun k => ‖GoldbachGRHWindow.primeLog k‖) (fun k _ => ?_)).trans
    (GoldbachGRHWindow.primeLog_nonunit_mass_le (q := q) (block X))
  have hw := weight_range ((k : ℝ) / (X : ℝ))
  have hnorm : ‖w X k‖ ≤ 1 := by
    change 0 ≤ scaledWeight (X : ℝ) (k : ℝ) ∧ scaledWeight (X : ℝ) (k : ℝ) ≤ 1 at hw
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw.1]
    exact hw.2
  simp only [norm_mul, GoldbachTwistedMellin.norm_phase, mul_one,
    ZMod.stdAddChar_apply, Circle.norm_coe]
  exact (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans_eq (one_mul _)

private theorem residual_eq_character_sum {X q : ℕ} [NeZero q] (hX : 0 < X) (a : ℕ) (β : ℝ) :
    arcResidual X q a β =
      (∑ χ : DirichletCharacter ℂ q, additiveWeight (a : ZMod q) χ * charResidual X χ β) +
      nonunitTerm X (a : ZMod q) β := by
  let p (k : ℕ) := w X k * (GoldbachGRHWindow.primeLog k * phase (γ β) k)
  have hp : primeSeries X ((a : ℝ) / q + β) =
      ∑ k ∈ block X, p k * ZMod.stdAddChar ((a : ZMod q) * (k : ZMod q)) := by
    rw [GoldbachWeightedException.primeSeries_eq_block hX]
    apply Finset.sum_congr rfl
    intro k _
    calc
      _ = w X k * (GoldbachGRHWindow.primeLog k *
          (GoldbachTwistedMellin.phase (2 * Real.pi * β) k *
            ZMod.stdAddChar ((a : ZMod q) * (k : ZMod q)))) := by
        rw [rational_phase]
        rfl
      _ = _ := by unfold p; simp only [mul_assoc]
  have hc (χ : DirichletCharacter ℂ q) :
      (∑ k ∈ block X, p k * χ (k : ZMod q)) = charPrime X χ β := by
    unfold p charPrime
    simp only [mul_assoc]
  have hsingle : (∑ χ : DirichletCharacter ℂ q, additiveWeight (a : ZMod q) χ *
      (if χ = 1 then discreteModel X β else 0)) = unitMean q a * discreteModel X β := by
    simp [mul_ite, additiveWeight_one, unitMean_of_cast]
  unfold arcResidual arcCorrection charResidual nonunitTerm
  rw [dite_eq_left (NeZero.ne q), hp, sum_character_transfer]
  simp_rw [hc]
  simp only [correction, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsingle]
  dsimp [p]
  abel

end
end GoldbachWeightedMajorResidual

end

section

namespace GoldbachWeightedMajorResidual

open Finset Filter MeasureTheory Goldbach GoldbachSmoothing GoldbachTwistedMellin
open GoldbachNarrowMajor GoldbachSmoothWindow GoldbachPrincipalSeries
open GoldbachWeightedException (cutoff primeSeries)

noncomputable section

private theorem arc_angle_budget {X q : ℕ} [NeZero q] {β : ℝ}
    (hX : 2 ^ 200 ≤ 4 * X) (hβ : |β| ≤ arcRadius X q) :
    |γ β| ≤ 1 ∧ |γ β| * ((4 * X : ℕ) : ℝ) ≤ 8 * (cutoff X : ℝ) ∧
      Real.sqrt (1 + 4 * |γ β| * (X : ℝ)) ≤
        3 * (((4 * X : ℕ) : ℝ) ^ (41 / 400 : ℝ)) := by
  let n : ℕ := 4 * X
  let P := cutoff X
  let x := (n : ℝ)
  have hn1 : 1 ≤ n := (by norm_num : 1 ≤ 2 ^ (200 : ℕ)).trans hX
  have hx1 : 1 ≤ x := by change (1 : ℝ) ≤ (n : ℝ); exact_mod_cast hn1
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  obtain ⟨hP, _, hp, _, _⟩ := GoldbachWeightedException.chosen_cutoff_bounds (X:=X) hX
  have hp1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hs : (P : ℝ) ≤ Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    exact hp.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos_of_pos hx0
  have hb' : |β| ≤ 1 / ((q : ℝ) * Real.sqrt x) := by
    change |β| ≤ (P : ℝ) / ((q : ℝ) * x) at hβ
    refine hβ.trans ((div_le_div_of_nonneg_right hs (by positivity)).trans_eq ?_)
    field_simp
    nlinarith only [Real.sq_sqrt hx0.le]
  have hn64 : 64 ≤ n := (by norm_num : 64 ≤ 2 ^ (200 : ℕ)).trans hX
  have hangle := (angular_range hn64 (NeZero.pos q) hb').1
  have hβx : |β| * x ≤ (P : ℝ) := by
    change |β| ≤ (P : ℝ) / ((q : ℝ) * x) at hβ
    have hmul := (le_div_iff₀ (mul_pos hq0 hx0)).mp hβ
    exact (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hx0.le hq1) (abs_nonneg β)).trans hmul
  have hγx : |γ β| * x ≤ 8 * (P : ℝ) := by
    rw [show |γ β| * x = (2 * Real.pi) * (|β| * x) by
      unfold γ; rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]; ring]
    exact mul_le_mul (by linarith only [Real.pi_lt_four]) hβx (by positivity) (by norm_num)
  refine ⟨hangle, hγx, ?_⟩
  have hxX : x = 4 * (X : ℝ) := by simp [x,n]
  have hh : 1 + 4 * |γ β| * (X : ℝ) ≤ 9 * (P : ℝ) := by
    rw [hxX] at hγx
    linarith only [hγx, hp1]
  calc
    _ ≤ Real.sqrt (9 * (P : ℝ)) := Real.sqrt_le_sqrt hh
    _ = 3 * Real.sqrt (P : ℝ) := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]; norm_num
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      refine (Real.sqrt_le_sqrt hp).trans_eq ?_
      change Real.sqrt (x ^ (41 / 200 : ℝ)) = x ^ (41 / 400 : ℝ)
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
      norm_num

private theorem uniform_char_budget : ∃ C : ℝ, 0 < C ∧ ∀ (X q : ℕ) [NeZero q],
    2 ^ 200 ≤ 4 * X → q ≤ cutoff X → ∀ β : ℝ, |β| ≤ arcRadius X q →
    (∀ χ : DirichletCharacter ℂ q, ‖charResidual X χ β‖ ≤ C * (((4 * X : ℕ) : ℝ) ^ (7 / 10 : ℝ))) ∧
      Real.log (q : ℝ) ≤ C * (((4 * X : ℕ) : ℝ) ^ (7 / 10 : ℝ)) := by
  obtain ⟨D, hD, hvar⟩ := GoldbachWeightedException.weight_variation
  obtain ⟨K, hK, hf⟩ := weighted_explicit_formula (d := 1 / 400) (by norm_num) (by norm_num)
  obtain ⟨A, hA, hlogpow⟩ := quartic_log_scale (e := 1 / 20) (by norm_num)
  let C := (D * (10 + 1200 * K) + 1) * A
  have hC : 0 < C := by unfold C; positivity
  refine ⟨C, hC, ?_⟩
  intro X q _ hX hqP β hβ
  let n : ℕ := 4 * X
  let x := (n : ℝ)
  let P := cutoff X
  let b := 2 * X - 1
  let L := logScale x
  let r := x ^ (41 / 400 : ℝ)
  let R := x ^ (243 / 400 : ℝ) * L ^ 4
  have hX2 : 2 ≤ X := by
    have hh := (by norm_num : 8 ≤ 2 ^ (200 : ℕ)).trans hX
    omega
  have hX0 : 0 < X := by omega
  have hX1R : 1 ≤ (X : ℝ) := by exact_mod_cast hX0
  have hXn : (X : ℝ) ≤ x := by
    change (X : ℝ) ≤ (n : ℝ)
    exact_mod_cast (show X ≤ n by dsimp [n]; omega)
  have hx1 := hX1R.trans hXn
  have hx0 := zero_lt_one.trans_le hx1
  have hL := logScale_one hx1
  have hl0 : 0 ≤ L := zero_le_one.trans hL
  have hr := Real.one_le_rpow hx1 (by norm_num : 0 ≤ (41 / 400 : ℝ))
  have hab : X < b := by dsimp [b]; omega
  have hb : b ≤ n := by dsimp [b,n]; omega
  have hbn : (b : ℝ) + 1 ≤ 2 * (X : ℝ) := by exact_mod_cast (show b + 1 ≤ 2 * X by dsimp [b]; omega)
  obtain ⟨_, _, hP, hPn, _⟩ := GoldbachWeightedException.chosen_cutoff_bounds (X:=X) hX
  have hqn : q ≤ n := by
    change 2 * P ≤ n at hPn
    omega
  have hqnR : (q : ℝ) ≤ x := by change (q : ℝ) ≤ (n : ℝ); exact_mod_cast hqn
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  obtain ⟨hlogq, hheight⟩ := log_window_scale hX1R hXn hqnR
  have hlogq0 : 0 ≤ logBudget q (X : ℝ) := by
    unfold logBudget Goldbach.logHeight
    have hprod : (1 : ℝ) ≤ 2 * (q : ℝ) * (2 + |heightCut (X : ℝ)|) := by
      have hprod := one_le_mul_of_one_le_of_one_le (by linarith : (1 : ℝ) ≤ 2 * (q : ℝ))
        (by linarith only [abs_nonneg (heightCut (X : ℝ))] : (1 : ℝ) ≤ 2 + |heightCut (X : ℝ)|)
      exact hprod
    exact add_nonneg zero_le_one (Real.log_nonneg hprod)
  obtain ⟨hsmall, hγx, hβsqrt⟩ := arc_angle_budget hX hβ
  have hR : 0 ≤ R := by unfold R; positivity
  have hR' : R ≤ A * x ^ (7 / 10 : ℝ) := calc
    _ ≤ x ^ (243 / 400 : ℝ) * (A * x ^ (1 / 20 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hlogpow x hx1) (by positivity)
    _ = A * x ^ (263 / 400 : ℝ) := by
      rw [show x ^ (243 / 400 : ℝ) * (A * x ^ (1 / 20 : ℝ)) =
        A * (x ^ (243 / 400 : ℝ) * x ^ (1 / 20 : ℝ)) by ring, ← Real.rpow_add hx0]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) hA.le
  have hL4 : L ≤ L ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hL (by norm_num : 1 ≤ (4 : ℕ))
  have hlog_logscale : Real.log x ≤ L := log_le_scale hx1
  have hpowSmall {e : ℝ} (he : e ≤ 243 / 400) : x ^ e ≤ x ^ (243 / 400 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 he
  have hprime : 2 * Real.sqrt x * Real.log x ≤ 2 * R := by
    rw [Real.sqrt_eq_rpow]
    unfold R
    have hlog0 := Real.log_nonneg hx1
    have ht := mul_le_mul (hpowSmall (e := 1 / 2) (by norm_num)) (hlog_logscale.trans hL4)
      hlog0 (by positivity)
    linarith only [ht]
  have hprincipal : ((b : ℝ) - (X : ℝ)) * |γ β| ≤ 8 * R := by
    have hbR : (b : ℝ) ≤ x := by change (b : ℝ) ≤ (n : ℝ); exact_mod_cast hb
    have hγx' : x * |γ β| ≤ 8 * (P : ℝ) := by rw [mul_comm x]; exact hγx
    have hrpow : (P : ℝ) ≤ R := calc
      _ ≤ x ^ (41 / 200 : ℝ) := hP
      _ ≤ x ^ (243 / 400 : ℝ) := hpowSmall (by norm_num)
      _ ≤ _ := le_mul_of_one_le_right (by positivity : 0 ≤ x ^ (243 / 400 : ℝ)) (one_le_pow₀ hL)
    exact (mul_le_mul_of_nonneg_right (by linarith only [hbR, Nat.cast_nonneg (α := ℝ) X])
      (abs_nonneg _)).trans (hγx'.trans (mul_le_mul_of_nonneg_left hrpow (by norm_num)))
  have hqt : Real.log (q : ℝ) ≤ R := calc
    _ ≤ Real.log x := Real.log_le_log (zero_lt_one.trans_le hq1) hqnR
    _ ≤ L ^ 4 := hlog_logscale.trans hL4
    _ ≤ _ := le_mul_of_one_le_left (by positivity) (Real.one_le_rpow hx1 (by norm_num))
  have hfactor : 1 + Real.sqrt (1 + 4 * |γ β| * (X : ℝ)) + Real.log (heightCut (X : ℝ)) ≤ 12 * L * r := by
    have h1 : 1 ≤ L * r := one_le_mul_of_one_le_of_one_le hL hr
    have h2 : r ≤ L * r := le_mul_of_one_le_left (zero_le_one.trans hr) hL
    have h3 : L ≤ L * r := le_mul_of_one_le_right hl0 hr
    linarith only [h1,h2,h3,hβsqrt,hheight]
  have hfactor0 : 0 ≤ 1 + Real.sqrt (1 + 4 * |γ β| * (X : ℝ)) + Real.log (heightCut (X : ℝ)) := by
    have hh : 1 ≤ heightCut (X : ℝ) := (by linarith : (1 : ℝ) ≤ 1 + 4 * (X : ℝ)).trans (heightCut_ge hX1R)
    exact add_nonneg (by positivity) (Real.log_nonneg hh)
  have hexpl : K * (X : ℝ) ^ (1 / 2 + 2 * (1 / 400) : ℝ) * (logBudget q (X : ℝ)) ^ 2 *
      (1 + Real.sqrt (1 + 4 * |γ β| * (X : ℝ)) + Real.log (heightCut (X : ℝ))) ≤ 1200 * K * R := by
    have hsmallX := Real.rpow_le_rpow (Nat.cast_nonneg X) hXn (by norm_num : 0 ≤ (1 / 2 + 2 * (1 / 400) : ℝ))
    have hb2 := pow_le_pow_left₀ hlogq0 hlogq 2
    calc
      _ ≤ (K * x ^ (1 / 2 + 2 * (1 / 400) : ℝ) * (10 * L) ^ 2) * (12 * L * r) :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hsmallX hK.le) hb2 (sq_nonneg _) (by positivity))
          hfactor hfactor0 (by positivity)
      _ = (1200 * K) * (x ^ (1 / 2 + 2 * (1 / 400) : ℝ) * r) * L ^ 3 := by ring
      _ = (1200 * K) * x ^ (243 / 400 : ℝ) * L ^ 3 := by
        unfold r
        rw [← Real.rpow_add hx0]
        norm_num
      _ ≤ _ := by
        unfold R
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by norm_num : (3 : ℕ) ≤ 4)) (by positivity)
  have hDn := hvar X hX0
  have hbound : (D * (10 + 1200 * K) + 1) * R ≤ C * x ^ (7 / 10 : ℝ) := by
    calc
      _ ≤ (D * (10 + 1200 * K) + 1) * (A * x ^ (7 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_left hR' (by positivity)
      _ = _ := by unfold C; ring
  have hc₁ : 1 ≤ D * (10 + 1200 * K) + 1 := by
    have ht : 0 ≤ D * (10 + 1200 * K) := by positivity
    linarith
  refine ⟨?_, hqt.trans ((le_mul_of_one_le_left hR hc₁).trans hbound)⟩
  intro χ
  let T := ∑ k ∈ block X, w X k * (twistedCoefficient χ k * phase (γ β) k)
  let M := principalFlag χ * weightedTransform X b (γ β) (w X) 1
  let Pm := if χ = 1 then discreteModel X β else 0
  have h1 : ‖charPrime X χ β - T‖ ≤ D * (2 * R) :=
    (weighted_prime_removal χ hab hb (by omega) (γ β) (w X)).trans
      (mul_le_mul hDn hprime (by positivity) hD.le)
  have h2 : ‖T - (M - zeroTerm X χ β)‖ ≤ D * (1200 * K * R) :=
    (hf q χ X b X (γ β) (w X) hX1R le_rfl hab hbn hsmall).trans
      (mul_le_mul hDn hexpl (by positivity) hD.le)
  have h3 : ‖M - Pm‖ ≤ D * (8 * R) := by
    by_cases hχ : χ = 1
    · rw [show M - Pm = weightedTransform X b (γ β) (w X) 1 -
        ∑ k ∈ block X, w X k * phase (γ β) k by
        simp [M, Pm, principalFlag, hχ, model_eq_block hX0]]
      exact (weighted_principal_approx hX0 hab (w X) (γ β)).trans
        (mul_le_mul hDn hprincipal (by
          have hbXR : (X : ℝ) ≤ b := by exact_mod_cast hab.le
          positivity) hD.le)
    · simpa [M, Pm, principalFlag, hχ] using (mul_nonneg hD.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hR))
  have he : charResidual X χ β =
      ((charPrime X χ β - T) + (T - (M - zeroTerm X χ β))) + (M - Pm) := by
    unfold charResidual Pm
    abel
  rw [he]
  have hh := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)
  exact hh.trans ((by nlinarith only [hR] : D * (2 * R) + D * (1200 * K * R) + D * (8 * R) ≤
    (D * (10 + 1200 * K) + 1) * R).trans hbound)

end
end GoldbachWeightedMajorResidual

end

section

namespace GoldbachWeightedMajorResidual

open Finset Filter MeasureTheory Goldbach GoldbachSmoothing GoldbachTwistedMellin
open GoldbachNarrowMajor GoldbachSmoothWindow GoldbachPrincipalSeries
open GoldbachWeightedException (cutoff primeSeries)

noncomputable section

private theorem transform_continuous_angle {a b : ℝ} (ha : 0 < a) (hab : a + 1 ≤ b) (z : ℂ) :
    Continuous (fun t : ℝ => transform a b t z) := by
  let f (t x : ℝ) := (taper a b x : ℂ) * (phase t x * ((max (a / 2) x : ℝ) : ℂ) ^ (z - 1))
  have hp : Continuous (fun x : ℝ => ((max (a / 2) x : ℝ) : ℂ) ^ (z - 1)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hx : 0 < max (a / 2) x := (half_pos ha).trans_le (le_max_left _ _)
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx.ne')).comp
      (continuous_const.max continuous_id).continuousAt
  have hf : Continuous (Function.uncurry f) := by
    unfold Function.uncurry f
    have ht : Continuous (fun p : ℝ × ℝ => (taper a b p.2 : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_taper a b).comp continuous_snd)
    have hphase : Continuous (fun p : ℝ × ℝ => phase p.1 p.2) := by unfold phase; fun_prop
    exact ht.mul (hphase.mul (hp.comp continuous_snd))
  have he (t : ℝ) : transform a b t z = ∫ x in a..(b + 1), f t x := by
    rw [transform_eq_taper_integral ha hab]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith : a ≤ b + 1)] at hx
    simp only [f, density, max_eq_right (show a / 2 ≤ x by linarith [hx.1])]
  simp_rw [he]
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf a (b + 1)

private theorem weightedTransform_continuous {X : ℕ} (hX : 2 ≤ X) (z : ℂ) :
    Continuous (fun β : ℝ => weightedTransform X (2 * X - 1) (γ β) (w X) z) := by
  let b := 2 * X - 1
  have ha : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hb : X + 1 ≤ b := by dsimp [b]; omega
  have h (j : ℕ) (hj : X + 1 ≤ j) : Continuous (fun β : ℝ => transform X j (γ β) z) :=
    (transform_continuous_angle ha (by exact_mod_cast hj) z).comp (by unfold γ; fun_prop)
  change Continuous (fun β : ℝ => w X b * transform X b (γ β) z +
    ∑ j ∈ Finset.Ioc X (b - 1), (w X j - w X (j + 1)) * transform X j (γ β) z)
  apply ((h b hb).const_mul _).add
  apply continuous_finsetSum
  intro j hj
  exact (h j (mem_Ioc.mp hj).1).const_mul _

private theorem arcResidual_continuous {X : ℕ} (hX : 2 ≤ X) (q a : ℕ) :
    Continuous (arcResidual X q a) := by
  have hleft : Continuous (fun β : ℝ => primeSeries X ((a : ℝ) / q + β)) := by
    unfold primeSeries GoldbachPolynomialMinor205.series GoldbachPolynomialMinor205.wave
    fun_prop
  have hmid : Continuous (fun β : ℝ =>
      Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.unitMean q a * discreteModel X β) :=
    (finiteModel_continuous _ _).const_mul _
  unfold arcResidual
  apply (hleft.sub hmid).add
  by_cases hq : q = 0
  · subst q
    have he : arcCorrection X 0 a = fun _ : ℝ => 0 := by
      funext β
      simp [arcCorrection]
    rw [he]
    exact continuous_const
  · let _ : NeZero q := ⟨hq⟩
    have he : arcCorrection X q a = fun β : ℝ => correction X (a : ZMod q) β := by
      funext β
      simp only [arcCorrection, dite_eq_left hq]
    rw [he]
    simp only [correction, zeroTerm]
    apply continuous_finsetSum
    intro χ _
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro z _
    exact (weightedTransform_continuous hX z).const_mul _

private theorem sum_over_reduced {q : ℕ} [NeZero q] (f : ℕ → ℝ) :
    (∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), f a) =
      ∑ a : (ZMod q)ˣ, f (a : ZMod q).val := by
  symm
  apply Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q).val)
  · intro u _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt (u : ZMod q)), ZMod.val_coe_unit_coprime u⟩
  · intro u _ v _ huv
    apply Units.ext
    simpa only [ZMod.natCast_zmod_val] using congrArg (fun x : ℕ => (x : ZMod q)) huv
  · intro r hr
    obtain ⟨hrange, hcop⟩ := Finset.mem_filter.mp hr
    let hu : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).mpr hcop
    exact ⟨hu.unit, Finset.mem_univ _, by rw [IsUnit.unit_spec, ZMod.val_natCast_of_lt (Finset.mem_range.mp hrange)]⟩
  · intro u _
    rfl

private theorem energy_on_fiber {X q : ℕ} [NeZero q] (hX : 0 < X) (β : ℝ) {B : ℝ}
    (hχ : ∀ χ : DirichletCharacter ℂ q, ‖charResidual X χ β‖ ≤ B)
    (hq : Real.log (q : ℝ) ≤ B) :
    (∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), ‖arcResidual X q a β‖ ^ 2) ≤
      4 * (q : ℝ) * B ^ 2 := by
  rw [sum_over_reduced]
  let F (a : (ZMod q)ˣ) :=
    ∑ χ : DirichletCharacter ℂ q, charResidual X χ β * additiveWeight (a : ZMod q) χ
  let N (a : (ZMod q)ˣ) := nonunitTerm X (a : ZMod q) β
  have hres (a : (ZMod q)ˣ) : arcResidual X q (a : ZMod q).val β = F a + N a := by
    rw [residual_eq_character_sum hX, ZMod.natCast_zmod_val]
    simp only [F, N, mul_comm]
  have hf : (∑ a : (ZMod q)ˣ, ‖F a‖ ^ 2) ≤ (q : ℝ) * B ^ 2 := by
    refine (GoldbachMajorEnergy.reduced_fraction_energy_le (fun χ => charResidual X χ β)).trans ?_
    have hφ : (0 : ℝ) < q.totient := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
    have ht : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    calc
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, ((q : ℝ) / q.totient) * B ^ 2 := by
        apply Finset.sum_le_sum
        intro χ _
        have hcond : (χ.conductor : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
        exact mul_le_mul (div_le_div_of_nonneg_right hcond hφ.le)
          (pow_le_pow_left₀ (norm_nonneg _) (hχ χ) 2) (sq_nonneg _) (by positivity)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ht]
        field_simp
  have hn : (∑ a : (ZMod q)ˣ, ‖N a‖ ^ 2) ≤ (q : ℝ) * B ^ 2 := calc
    _ ≤ ∑ _a : (ZMod q)ˣ, B ^ 2 := by
      apply Finset.sum_le_sum
      intro a _
      exact pow_le_pow_left₀ (norm_nonneg _) ((nonunit_bound X (a : ZMod q) β).trans hq) 2
    _ = (q.totient : ℝ) * B ^ 2 := by rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le q) (sq_nonneg _)
  simp_rw [hres]
  calc
    _ ≤ ∑ a : (ZMod q)ˣ, 2 * (‖F a‖ ^ 2 + ‖N a‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans (by nlinarith only [sq_nonneg (‖F a‖ - ‖N a‖)])
    _ = 2 * ((∑ a : (ZMod q)ˣ, ‖F a‖ ^ 2) + (∑ a : (ZMod q)ˣ, ‖N a‖ ^ 2)) := by
      simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    _ ≤ _ := by linarith only [hf, hn]

def residualEnergy (X : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (cutoff X), ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
    ∫ β in Set.Icc (-arcRadius X q) (arcRadius X q), ‖arcResidual X q a β‖ ^ 2

/-- The character diagonal saves one factor of the denominator in the actual
numerator-averaged square error, uniformly through the stated cutoff. -/
theorem residual_energy_bound : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ^ 200 ≤ 4 * X →
    residualEnergy X ≤ C * (((4 * X : ℕ) : ℝ) ^ (81 / 100 : ℝ)) := by
  obtain ⟨A, hA, hbudget⟩ := uniform_char_budget
  refine ⟨8 * A ^ 2, by positivity, ?_⟩
  intro X hX
  let n : ℕ := 4 * X
  let x := (n : ℝ)
  let P := cutoff X
  let B := A * x ^ (7 / 10 : ℝ)
  have hX2 : 2 ≤ X := by
    have h := (by norm_num : 8 ≤ 2 ^ (200 : ℕ)).trans hX
    omega
  have hx0 : 0 < x := by unfold x n; positivity
  have hFiber (q : ℕ) (hq : q ∈ Finset.Icc 1 P) :
      (∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
        ∫ β in Set.Icc (-arcRadius X q) (arcRadius X q), ‖arcResidual X q a β‖ ^ 2) ≤
        8 * (P : ℝ) / x * B ^ 2 := by
    obtain ⟨hq1,hqP⟩ := Finset.mem_Icc.mp hq
    let _ : NeZero q := ⟨(show q ≠ 0 by omega)⟩
    let ρ := arcRadius X q
    have hρ : 0 ≤ ρ := by unfold ρ arcRadius; positivity
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (NeZero.pos q)
    let s := (Finset.range q).filter (fun a => a.Coprime q)
    let I := Set.Icc (-ρ) ρ
    let F (a : ℕ) (β : ℝ) := ‖arcResidual X q a β‖ ^ 2
    have hcont (a : ℕ) : Continuous (F a) := (arcResidual_continuous hX2 q a).norm.pow 2
    have hsum : (∫ β in I, ∑ a ∈ s, F a β) ≤ ∫ _ in I, 4 * (q : ℝ) * B ^ 2 := by
      apply setIntegral_mono_on ((continuous_finsetSum s (fun a _ => hcont a)).integrableOn_Icc)
        ((continuous_const : Continuous (fun _ : ℝ => 4 * (q : ℝ) * B ^ 2)).integrableOn_Icc) measurableSet_Icc
      intro β hβ
      have hβ' : |β| ≤ arcRadius X q := abs_le.mpr hβ
      obtain ⟨hχ, hl⟩ := hbudget X q hX hqP β hβ'
      exact energy_on_fiber (by omega : 0 < X) β hχ hl
    rw [MeasureTheory.integral_finsetSum s (fun a _ => (hcont a).integrableOn_Icc)] at hsum
    change _ ≤ (∫ _ in I, 4 * (q : ℝ) * B ^ 2) at hsum
    refine hsum.trans_eq ?_
    rw [setIntegral_const, Real.volume_real_Icc, sub_neg_eq_add, max_eq_left (by positivity)]
    change (ρ + ρ) * (4 * (q : ℝ) * B ^ 2) = _
    have hr : ρ = (P : ℝ) / ((q : ℝ) * x) := rfl
    rw [hr]
    field_simp
    ring
  have hsum : residualEnergy X ≤ (8 * A ^ 2) * ((P : ℝ) ^ 2 * x ^ (2 / 5 : ℝ)) := calc
    _ ≤ ∑ _q ∈ Finset.Icc 1 P, 8 * (P : ℝ) / x * B ^ 2 := Finset.sum_le_sum hFiber
    _ = (8 * A ^ 2) * ((P : ℝ) ^ 2 * x ^ (2 / 5 : ℝ)) := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      unfold B
      rw [mul_pow, ← Real.rpow_mul_natCast hx0.le]
      have heq : x ^ ((7 / 10 : ℝ) * ↑(2 : ℕ)) = x ^ (2 / 5 : ℝ) * x := calc
        _ = x ^ ((2 / 5 : ℝ) + 1) := by norm_num
        _ = _ := by rw [Real.rpow_add hx0, Real.rpow_one]
      rw [heq]
      field_simp
  obtain ⟨_, _, hP, _, _⟩ := GoldbachWeightedException.chosen_cutoff_bounds (X:=X) hX
  have hp2 := pow_le_pow_left₀ (Nat.cast_nonneg P) hP 2
  change (P : ℝ) ^ 2 ≤ (x ^ (41 / 200 : ℝ)) ^ 2 at hp2
  rw [← Real.rpow_mul_natCast hx0.le] at hp2
  change residualEnergy X ≤ (8 * A ^ 2) * x ^ (81 / 100 : ℝ)
  refine hsum.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp2 (by positivity)) (by positivity)).trans_eq ?_)
  rw [← Real.rpow_add hx0]
  norm_num

end
end GoldbachWeightedMajorResidual

end

end

section


open MeasureTheory

namespace GoldbachNarrowMajor

/-- On the major arcs, an (L²) bound for the linear model error
controls every signed coefficient of the quadratic sum. -/
theorem major_coefficient_error {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S V phase : α → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hphase : ∀ x, ‖phase x‖ ≤ 1)
    (hS : Integrable (fun x => (S x) ^ 2 * phase x) μ)
    (hV : Integrable (fun x => (V x) ^ 2 * phase x) μ)
    (hV2 : Integrable (fun x => ‖V x‖ ^ 2) μ)
    (hE2 : Integrable (fun x => ‖S x - V x‖ ^ 2) μ) :
    ‖(∫ x, (S x) ^ 2 * phase x ∂μ) - ∫ x, (V x) ^ 2 * phase x ∂μ‖ ≤
      δ * (∫ x, ‖V x‖ ^ 2 ∂μ) + (1 + δ⁻¹) * (∫ x, ‖S x - V x‖ ^ 2 ∂μ) := by
  let excess : α → ℂ := fun x => (S x) ^ 2 * phase x - (V x) ^ 2 * phase x
  let bound : α → ℝ := fun x => δ * ‖V x‖ ^ 2 + (1 + δ⁻¹) * ‖S x - V x‖ ^ 2
  have hb : Integrable bound μ := (hV2.const_mul δ).add (hE2.const_mul (1 + δ⁻¹))
  have hpoint (x : α) : ‖excess x‖ ≤ bound x := by
    let u := ‖V x‖
    let v := ‖S x - V x‖
    have hweighted : 2 * u * v ≤ δ * u ^ 2 + δ⁻¹ * v ^ 2 := by
      apply le_of_mul_le_mul_right _ hδ
      have he : (δ * u ^ 2 + δ⁻¹ * v ^ 2) * δ = (δ * u) ^ 2 + v ^ 2 := by
        field_simp
      rw [he]
      nlinarith only [sq_nonneg (δ * u - v)]
    have hx : excess x = ((S x - V x) ^ 2 + 2 * V x * (S x - V x)) * phase x := by
      dsimp only [excess]
      ring
    rw [hx, norm_mul]
    calc
      _ ≤ ‖(S x - V x) ^ 2 + 2 * V x * (S x - V x)‖ :=
        mul_le_of_le_one_right (norm_nonneg _) (hphase x)
      _ ≤ v ^ 2 + 2 * u * v := by
        have hz := norm_add_le ((S x - V x) ^ 2) (2 * V x * (S x - V x))
        rw [Complex.norm_pow] at hz
        simpa [u, v, norm_mul] using hz
      _ ≤ bound x := by
        dsimp only [bound, u, v] at *
        linarith only [hweighted]
  have h := norm_integral_le_of_norm_le hb (Filter.Eventually.of_forall hpoint)
  simpa only [excess, bound, integral_sub hS hV,
    integral_add (hV2.const_mul δ) (hE2.const_mul (1 + δ⁻¹)), integral_const_mul] using h

end GoldbachNarrowMajor

end

section

namespace GoldbachWeightedMajorResidual

open Finset Filter MeasureTheory GoldbachNarrowMajor GoldbachPrincipalSeries
open GoldbachWeightedException (cutoff primeSeries majorCoefficient)
open GoldbachPolynomialMinor205 (wave)
open Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc (unitMean)

noncomputable section

private def localPrime (X q a : ℕ) (β : ℝ) : ℂ := primeSeries X ((a : ℝ) / q + β)
private def localModel (X q a : ℕ) (β : ℝ) : ℂ := unitMean q a * discreteModel X β
private def localPhase (q a m : ℕ) (β : ℝ) : ℂ := wave (-(m : ℝ) * ((a : ℝ) / q + β))
private def domain (X q : ℕ) : Set ℝ := Set.Icc (-arcRadius X q) (arcRadius X q)

private theorem radius_nonneg (X q : ℕ) : 0 ≤ arcRadius X q := by unfold arcRadius; positivity

private theorem localPrime_cont (X q a : ℕ) : Continuous (localPrime X q a) := by
  unfold localPrime primeSeries GoldbachPolynomialMinor205.series GoldbachPolynomialMinor205.wave
  fun_prop

private theorem localModel_cont (X q a : ℕ) : Continuous (localModel X q a) :=
  (finiteModel_continuous _ _).const_mul _

private theorem localPhase_cont (q a m : ℕ) : Continuous (localPhase q a m) := by
  unfold localPhase wave
  fun_prop

private theorem wave_norm (t : ℝ) : ‖wave t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem correction_cont {X : ℕ} (hX : 2 ≤ X) (q a : ℕ) : Continuous (arcCorrection X q a) := by
  have he : arcCorrection X q a = arcResidual X q a - (localPrime X q a - localModel X q a) := by
    funext t
    unfold arcResidual localPrime localModel
    simp only [Pi.sub_apply]
    abel
  rw [he]
  exact (arcResidual_continuous hX q a).sub ((localPrime_cont X q a).sub (localModel_cont X q a))

private theorem major_as_integral_sum {X : ℕ} (hX : 2 ^ 200 ≤ 4 * X) (m : ℕ) :
    majorCoefficient X m =
      ∑ q ∈ Finset.Icc 1 (cutoff X), ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
        ∫ β in domain X q, (localPrime X q a β)^2 * localPhase q a m β := by
  rw [GoldbachWeightedException.major_eq_window_sum hX]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro a _
  have hρ : -arcRadius X q ≤ arcRadius X q := by linarith [radius_nonneg X q]
  change (∫ β in (-arcRadius X q)..(arcRadius X q),
    GoldbachWeightedException.integrand X m (β + (a : ℝ) / q)) = _
  rw [intervalIntegral.integral_of_le hρ, ← integral_Icc_eq_integral_Ioc]
  unfold domain localPrime localPhase GoldbachWeightedException.integrand
  simp only [add_comm]

private theorem localPrime_integral_energy {X : ℕ} (hX : 2 ^ 200 ≤ 4 * X) :
    (∑ q ∈ Finset.Icc 1 (cutoff X), ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
      ∫ β in domain X q, ‖localPrime X q a β‖ ^ 2) ≤
      Real.log 4 * ((4 * X : ℕ) : ℝ) * Real.log ((4 * X : ℕ) : ℝ) := by
  let n : ℕ := 4 * X
  let P := cutoff X
  let F (t : ℝ) : ℝ := ‖primeSeries X t‖ ^ 2
  have hc : Continuous F := (finiteModel_continuous (GoldbachWeightedException.primeWeight X) n).norm.pow 2
  have hper : Function.Periodic (primeSeries X) 1 := finiteModel_periodic _ _
  obtain ⟨hP, _, _, _, hsep⟩ := GoldbachWeightedException.chosen_cutoff_bounds (X:=X) hX
  have h := integral_torus_major_arcs (n := n) (P := P) hP hsep
    (Complex.continuous_ofReal.comp hc) (f := fun t => (F t : ℂ))
    (fun t => by dsimp [F]; rw [hper t])
  simp only [integral_complex_ofReal, intervalIntegral.integral_ofReal, ← Complex.ofReal_sum] at h
  have hh := Complex.ofReal_injective h
  have hr (q a : ℕ) : (∫ β in (-arcRadius X q)..(arcRadius X q),
      F (β + (a : ℝ) / q)) = ∫ β in domain X q, ‖localPrime X q a β‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith [radius_nonneg X q]), ← integral_Icc_eq_integral_Ioc]
    unfold F localPrime domain
    simp only [add_comm]
  change (∫ t in GoldbachNarrowMajor.arcs n P ∩ Set.Icc 0 1, F t) =
    ∑ q ∈ Finset.Icc 1 P, ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
      ∫ β in (-arcRadius X q)..(arcRadius X q), F (β + (a : ℝ) / q) at hh
  simp_rw [hr] at hh
  rw [← hh]
  calc
    _ ≤ ∫ t in Set.Icc (0 : ℝ) 1, F t := setIntegral_mono_set hc.integrableOn_Icc
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) (Filter.Eventually.of_forall Set.inter_subset_right)
    _ = ∑ k ∈ Finset.range (n + 1), (GoldbachWeightedException.primeWeight X k) ^ 2 := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      have hshift := (fun t : ℝ => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hper t))
      let fp : Function.Periodic F 1 := hshift
      have hi := fp.intervalIntegral_add_eq 0 (-(1 / 2 : ℝ))
      norm_num at hi
      rw [hi]
      exact finiteModel_energy _ _
    _ ≤ _ := GoldbachWeightedException.weight_energy X

end
end GoldbachWeightedMajorResidual

end


end

section

namespace GoldbachWeightedMajorResidual

open Finset Filter MeasureTheory GoldbachNarrowMajor
open GoldbachWeightedException (cutoff primeSeries majorCoefficient)

noncomputable section

/-- A continuous local term can be retained with its sign in the major model. -/
def signedModelCoefficient (D : ℕ → ℕ → ℕ → ℝ → ℂ) (X m : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 (cutoff X), ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
    ∫ β in domain X q, (localModel X q a β - D X q a β)^2 * localPhase q a m β

/-- Measure only the part of the zero correction omitted from the signed model. -/
def remainingCorrectionEnergy (D : ℕ → ℕ → ℕ → ℝ → ℂ) (X : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (cutoff X), ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
    ∫ β in domain X q, ‖arcCorrection X q a β - D X q a β‖ ^ 2

private theorem signed_fiber_error {X : ℕ} (hX : 2 ≤ X) (q a m : ℕ)
    {D : ℝ → ℂ} (hD : Continuous D) {δ : ℝ} (hδ : 0 < δ) :
    ‖(∫ β in domain X q, (localPrime X q a β)^2 * localPhase q a m β) -
        ∫ β in domain X q, (localModel X q a β - D β)^2 * localPhase q a m β‖ ≤
      δ * (∫ β in domain X q, ‖localPrime X q a β‖ ^ 2) +
        (1 + δ⁻¹) * (2 * ((∫ β in domain X q, ‖arcResidual X q a β‖ ^ 2) +
          ∫ β in domain X q, ‖arcCorrection X q a β - D β‖ ^ 2)) := by
  let V := fun β => localModel X q a β - D β
  have hS := localPrime_cont X q a
  have hV : Continuous V := (localModel_cont X q a).sub hD
  have hF := localPhase_cont q a m
  have hR := arcResidual_continuous hX q a
  have hZ := (correction_cont hX q a).sub hD
  rw [norm_sub_rev]
  have h0 := major_coefficient_error (volume.restrict (domain X q))
    V (localPrime X q a) (localPhase q a m) hδ
    (fun t => (wave_norm _).le) ((hV.pow 2).mul hF).integrableOn_Icc
    ((hS.pow 2).mul hF).integrableOn_Icc (hS.norm.pow 2).integrableOn_Icc
    ((hV.sub hS).norm.pow 2).integrableOn_Icc
  refine h0.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by positivity)))
  have hpt (t : ℝ) : ‖V t - localPrime X q a t‖ ^ 2 ≤
      2 * (‖arcResidual X q a t‖ ^ 2 + ‖arcCorrection X q a t - D t‖ ^ 2) := by
    rw [show V t - localPrime X q a t =
      (arcCorrection X q a t - D t) - arcResidual X q a t by
        unfold V localModel localPrime arcResidual
        abel]
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2).trans (by
      nlinarith only [sq_nonneg (‖arcResidual X q a t‖ - ‖arcCorrection X q a t - D t‖)])
  have hi := setIntegral_mono_on (μ := volume) ((hV.sub hS).norm.pow 2).integrableOn_Icc
    ((continuous_const.mul ((hR.norm.pow 2).add (hZ.norm.pow 2))).integrableOn_Icc)
    (measurableSet_Icc : MeasurableSet (domain X q)) (fun t _ => hpt t)
  change (∫ t in domain X q, ‖V t - localPrime X q a t‖ ^ 2) ≤
    ∫ t in domain X q, 2 * (‖arcResidual X q a t‖ ^ 2 + ‖arcCorrection X q a t - D t‖ ^ 2) at hi
  have hR2 : IntegrableOn (fun t : ℝ => ‖arcResidual X q a t‖ ^ 2) (domain X q) :=
    (hR.norm.pow 2).integrableOn_Icc
  have hZ2 : IntegrableOn (fun t : ℝ => ‖arcCorrection X q a t - D t‖ ^ 2) (domain X q) :=
    (hZ.norm.pow 2).integrableOn_Icc
  rwa [integral_const_mul, integral_add hR2 hZ2] at hi

/-- Compare the actual coefficient with the signed model on the exact reduced arcs. -/
theorem signed_coefficient_difference {X : ℕ} (hX : 2 ^ 200 ≤ 4 * X) (m : ℕ)
    (D : ℕ → ℕ → ℕ → ℝ → ℂ) (hD : ∀ q a : ℕ, Continuous (D X q a))
    {δ : ℝ} (hδ : 0 < δ) :
    ‖majorCoefficient X m - signedModelCoefficient D X m‖ ≤
      δ * (Real.log 4 * ((4 * X : ℕ) : ℝ) * Real.log ((4 * X : ℕ) : ℝ)) +
        2 * (1 + δ⁻¹) * (residualEnergy X + remainingCorrectionEnergy D X) := by
  have hx : 2 ≤ X := by
    have hh := (by norm_num : 8 ≤ 2 ^ (200 : ℕ)).trans hX
    omega
  let S (q a : ℕ) : ℂ := ∫ β in domain X q, (localPrime X q a β)^2 * localPhase q a m β
  let V (q a : ℕ) : ℂ := ∫ β in domain X q, (localModel X q a β - D X q a β)^2 * localPhase q a m β
  let s (q : ℕ) := (Finset.range q).filter (fun a => a.Coprime q)
  let Q := Finset.Icc 1 (cutoff X)
  let PE (q a : ℕ) := ∫ β in domain X q, ‖localPrime X q a β‖ ^ 2
  let RE (q a : ℕ) := ∫ β in domain X q, ‖arcResidual X q a β‖ ^ 2
  let CE (q a : ℕ) := ∫ β in domain X q, ‖arcCorrection X q a β - D X q a β‖ ^ 2
  have hh : ‖majorCoefficient X m - signedModelCoefficient D X m‖ =
      ‖∑ q ∈ Q, ∑ a ∈ s q, (S q a - V q a)‖ := by
    rw [major_as_integral_sum hX, signedModelCoefficient]
    simp only [Q, s, S, V, Finset.sum_sub_distrib]
  rw [hh]
  calc
    _ ≤ ∑ q ∈ Q, ∑ a ∈ s q, ‖S q a - V q a‖ := (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun q _ => norm_sum_le (s q) _)
    _ ≤ ∑ q ∈ Q, ∑ a ∈ s q, (δ * PE q a + (1 + δ⁻¹) * (2 * (RE q a + CE q a))) :=
      Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun a _ => signed_fiber_error hx q a m (hD q a) hδ))
    _ = δ * (∑ q ∈ Q, ∑ a ∈ s q, PE q a) +
        2 * (1 + δ⁻¹) * (residualEnergy X + remainingCorrectionEnergy D X) := by
      have hR : residualEnergy X = ∑ q ∈ Q, ∑ a ∈ s q, RE q a := rfl
      have hC : remainingCorrectionEnergy D X = ∑ q ∈ Q, ∑ a ∈ s q, CE q a := rfl
      rw [hR, hC]
      let K := 2 * (1 + δ⁻¹)
      change _ = δ * (∑ q ∈ Q, ∑ a ∈ s q, PE q a) +
        K * ((∑ q ∈ Q, ∑ a ∈ s q, RE q a) + ∑ q ∈ Q, ∑ a ∈ s q, CE q a)
      rw [mul_add K]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro a _
      unfold K
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (localPrime_integral_energy hX) hδ.le) le_rfl

end
end GoldbachWeightedMajorResidual

end

section

namespace GoldbachWeightedMajorResidual

open Filter GoldbachWeightedException GoldbachTwistedMellin
open scoped Topology

noncomputable section

/-- One inverse-cubic logarithmic energy bound certifies the omitted zero correction. -/
def RemainderLogSaving (D : ℕ → ℕ → ℕ → ℝ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
    let n := ((4 * X : ℕ) : ℝ)
    remainingCorrectionEnergy D X ≤ C * n / (1 + Real.log n) ^ 3

end
end GoldbachWeightedMajorResidual

end
end

section

namespace GoldbachConductorZeros

open Complex DirichletCharacter Finset Filter Goldbach Set
open scoped Topology

variable {q : ℕ} [NeZero q]


theorem regularized_primitive_order (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    {s : ℂ} (hs : 0 < s.re) :
    analyticOrderNatAt (regularizedL χ) s = analyticOrderNatAt (regularizedL χ.primitiveCharacter) s := by
  by_cases h : s = 1
  · subst s
    have hz {r : ℕ} [NeZero r] (ψ : DirichletCharacter ℂ r) :
        analyticOrderAt (regularizedL ψ) 1 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (Goldbach.regularizedL_ne_zero_at_one ψ))
    unfold analyticOrderNatAt
    rw [hz χ, hz χ.primitiveCharacter]
  · simpa only [changeLevel_primitiveCharacter χ] using
      changeLevel_regularized_order χ.conductor_dvd_level χ.primitiveCharacter hs h

end GoldbachConductorZeros
end

section

namespace GoldbachConductorRegroup

open Finset DirichletCharacter
open scoped Classical


theorem sum_by_conductor {A : Type*} [AddCommMonoid A] (q : ℕ) [NeZero q]
    (F : (r : ℕ) → DirichletCharacter ℂ r → A) :
    (∑ χ : DirichletCharacter ℂ q, F χ.conductor χ.primitiveCharacter) =
      ∑ r ∈ q.divisors, ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
        (fun ψ => ψ.IsPrimitive), F r ψ := by
  classical
  let S := q.divisors.sigma fun r => (univ : Finset (DirichletCharacter ℂ r)).filter
    (fun ψ => ψ.IsPrimitive)
  let tag (χ : DirichletCharacter ℂ q) : Σ r : ℕ, DirichletCharacter ℂ r :=
    ⟨χ.conductor, χ.primitiveCharacter⟩
  have hinj : Function.Injective tag := by
    let recover (x : Σ r : ℕ, DirichletCharacter ℂ r) : DirichletCharacter ℂ q :=
      if h : x.1 ∣ q then changeLevel h x.2 else 1
    have hL : Function.LeftInverse recover tag := by
      intro χ
      dsimp only [tag, recover]
      rw [dite_eq_left χ.conductor_dvd_level, changeLevel_primitiveCharacter]
    exact hL.injective
  have hsum : (∑ x ∈ S, F x.1 x.2) =
      ∑ r ∈ q.divisors, ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter
        (fun ψ => ψ.IsPrimitive), F r ψ := by
    simp only [S, Finset.sum_sigma]
  rw [← hsum]
  refine Finset.sum_bij (fun χ _ => tag χ) ?_ ?_ ?_ ?_
  · intro χ _
    exact Finset.mem_sigma.mpr ⟨Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, NeZero.ne q⟩,
      mem_filter.mpr ⟨mem_univ _, χ.primitiveCharacter_isPrimitive⟩⟩
  · intro χ _ ψ _ h
    exact hinj h
  · rintro ⟨r, ψ⟩ hx
    obtain ⟨hr, hp⟩ := Finset.mem_sigma.mp hx
    let h := (Nat.mem_divisors.mp hr).1
    exact ⟨changeLevel h ψ, mem_univ _,
      primitiveCharacter_sigma_changeLevel h ψ (mem_filter.mp hp).2⟩
  · intro χ _
    rfl

end GoldbachConductorRegroup

namespace GoldbachConductorRegroup

open Finset

noncomputable def reciprocalSum (P : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 P, (k : ℝ)⁻¹

theorem modulus_multiples_weight_le (P r : ℕ) (hr : 0 < r) :
    (∑ q ∈ (Icc 1 P).filter (fun q => r ∣ q), (r : ℝ) / q.totient) ≤
      (4 * Real.log ((P+2 : ℕ) : ℝ)) * reciprocalSum P := by
  let S := (Icc 1 P).filter (fun q => r ∣ q)
  let C := 4 * Real.log ((P+2 : ℕ) : ℝ)
  have hC : 0 ≤ C := by
    unfold C
    apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ P + 2)
  have hsub : S ⊆ (Icc 1 P).image (fun k => r * k) := by
    intro q hq
    obtain ⟨⟨hq0, hqP⟩, k, rfl⟩ := mem_filter.mp hq |>.imp mem_Icc.mp id
    have hk : 1 ≤ k := by
      by_contra! hh
      have : k = 0 := by omega
      simp [this] at hq0
    exact mem_image.mpr ⟨k, mem_Icc.mpr ⟨hk, (Nat.le_mul_of_pos_left k hr).trans hqP⟩, rfl⟩
  have hinj : Function.Injective (fun k : ℕ => r*k) :=
    fun _ _ h => mul_left_cancel₀ hr.ne' h
  change (∑ q ∈ S, (r:ℝ)/q.totient) ≤ C * reciprocalSum P
  calc
    _ ≤ ∑ q ∈ S, C * (((q/r : ℕ) : ℝ)⁻¹) := by
      apply sum_le_sum
      intro q hq
      obtain ⟨⟨hq0, hqP⟩, hdiv⟩ := mem_filter.mp hq |>.imp mem_Icc.mp id
      have hw := DeepThreeQuarters.totient_ratio_le_four_log q hq0
      have hlog : 4 * Real.log ((q+2 : ℕ) : ℝ) ≤ C := by
        exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hqP 2)) (by norm_num)
      obtain ⟨k, rfl⟩ := hdiv
      rw [Nat.mul_div_cancel_left k hr]
      have hk : 0 < k := by
        by_contra! hn
        have : k = 0 := by omega
        simp [this] at hq0
      have he : (r:ℝ) / (r*k).totient = ((r*k : ℕ):ℝ) / (r*k).totient * (k:ℝ)⁻¹ := by
        push_cast
        field_simp [Nat.cast_ne_zero.mpr hk.ne']
      rw [he]
      exact mul_le_mul_of_nonneg_right (hw.trans hlog) (by positivity)
    _ ≤ ∑ q ∈ (Icc 1 P).image (fun k => r*k), C * (((q/r : ℕ) : ℝ)⁻¹) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    _ = _ := by
      rw [Finset.sum_image hinj.injOn]
      simp only [reciprocalSum, Nat.mul_div_cancel_left _ hr, mul_sum]

theorem sum_divisor_weight_le (P : ℕ) (F : ℕ → ℝ) (hF : ∀ r, 0 ≤ F r) :
    (∑ q ∈ Icc 1 P, ∑ r ∈ q.divisors, (r : ℝ) / q.totient * F r) ≤
      ((4 * Real.log ((P+2 : ℕ) : ℝ)) * reciprocalSum P) * (∑ r ∈ Icc 1 P, F r) := by
  have hset (q : ℕ) (hq : q ∈ Icc 1 P) :
      q.divisors = (Icc 1 P).filter (fun r => r ∣ q) := by
    obtain ⟨hq0, hqP⟩ := mem_Icc.mp hq
    ext r
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · intro h
      exact ⟨⟨Nat.pos_of_dvd_of_pos h.1 hq0, (Nat.le_of_dvd hq0 h.1).trans hqP⟩, h.1⟩
    · exact fun h => ⟨h.2, (show 0 < q from hq0).ne'⟩
  calc
    _ = ∑ q ∈ Icc 1 P, ∑ r ∈ Icc 1 P, if r ∣ q then (r:ℝ)/q.totient * F r else 0 := by
      apply sum_congr rfl
      intro q hq
      rw [hset q hq, sum_filter]
    _ = ∑ r ∈ Icc 1 P, (∑ q ∈ (Icc 1 P).filter (fun q => r ∣ q), (r:ℝ)/q.totient) * F r := by
      rw [sum_comm]
      apply sum_congr rfl
      intro r _
      rw [Finset.sum_mul, sum_filter]
    _ ≤ _ := by
      rw [mul_sum]
      exact sum_le_sum (fun r hr => mul_le_mul_of_nonneg_right
        (modulus_multiples_weight_le P r (mem_Icc.mp hr).1) (hF r))

end GoldbachConductorRegroup

namespace GoldbachConductorRegroup

open Finset MeasureTheory Set
open scoped Classical

noncomputable def bandEnergy (f : ℝ → ℂ) (R : ℝ) : ℝ :=
  ∫ t in Set.Icc (-R) R, ‖f t‖ ^ 2

theorem bandEnergy_nonneg (f : ℝ → ℂ) (R : ℝ) : 0 ≤ bandEnergy f R :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem bandEnergy_mono (f : ℝ → ℂ) (hf : Continuous f) {R S : ℝ} (hRS : R ≤ S) :
    bandEnergy f R ≤ bandEnergy f S :=
  setIntegral_mono_set (hf.norm.pow 2).integrableOn_Icc
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall (fun _ hx => ⟨(neg_le_neg hRS).trans hx.1, hx.2.trans hRS⟩))

theorem primitive_major_energy_le (P : ℕ) (X : ℝ) (hX : 0 < X)
    (F : (r : ℕ) → DirichletCharacter ℂ r → ℝ → ℂ)
    (hF : ∀ r ψ, Continuous (F r ψ)) :
    (∑ q ∈ Icc 1 P, ∑ χ : DirichletCharacter ℂ q,
      (χ.conductor : ℝ)/q.totient *
        bandEnergy (F χ.conductor χ.primitiveCharacter) (P / ((q : ℝ)*X))) ≤
      ((4 * Real.log ((P+2 : ℕ) : ℝ)) * reciprocalSum P) *
        (∑ r ∈ Icc 1 P, ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.IsPrimitive),
          bandEnergy (F r ψ) (P / ((r : ℝ)*X))) := by
  let U (r : ℕ) := ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.IsPrimitive),
    bandEnergy (F r ψ) (P / ((r : ℝ)*X))
  calc
    _ ≤ ∑ q ∈ Icc 1 P, ∑ χ : DirichletCharacter ℂ q,
        (χ.conductor : ℝ) / q.totient *
          bandEnergy (F χ.conductor χ.primitiveCharacter) (P / ((χ.conductor : ℝ)*X)) := by
      apply sum_le_sum
      intro q hq
      have : NeZero q := ⟨(show 0 < q from (mem_Icc.mp hq).1).ne'⟩
      apply sum_le_sum
      intro χ _
      have hr : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
      have hrq : (χ.conductor : ℝ) ≤ q := by
        exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
      have h01 := div_le_div_of_nonneg_left (Nat.cast_nonneg (α := ℝ) P) (mul_pos hr hX)
        (mul_le_mul_of_nonneg_right hrq hX.le)
      exact mul_le_mul_of_nonneg_left (bandEnergy_mono _ (hF _ _) h01) (by positivity)
    _ = ∑ q ∈ Icc 1 P, ∑ r ∈ q.divisors, (r : ℝ) / q.totient * U r := by
      apply sum_congr rfl
      intro q hq
      have : NeZero q := ⟨(show 0 < q from (mem_Icc.mp hq).1).ne'⟩
      simpa only [U, mul_sum] using
        sum_by_conductor q (fun r ψ => (r : ℝ)/q.totient * bandEnergy (F r ψ) (P / ((r : ℝ)*X)))
    _ ≤ _ := sum_divisor_weight_le P U (fun r => sum_nonneg (fun _ _ => bandEnergy_nonneg ..))

end GoldbachConductorRegroup
end

section


namespace GoldbachConductorRegroup

open Finset

theorem reciprocalSum_eq_harmonic (P : ℕ) : reciprocalSum P = (harmonic P : ℝ) := by
  simp only [reciprocalSum, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem reciprocalSum_le (P : ℕ) : reciprocalSum P ≤ 1 + Real.log (P : ℝ) := by
  rw [reciprocalSum_eq_harmonic]
  exact harmonic_le_one_add_log P

end GoldbachConductorRegroup

end

section

namespace GoldbachWeightedMajorResidual

open Finset MeasureTheory
open Goldbach GoldbachTwistedMellin GoldbachNarrowMajor GoldbachZeroStrip GoldbachSmoothWindow
open GoldbachConductorRegroup (bandEnergy)

open scoped Pointwise

noncomputable section

theorem weightedTransform_eq_weightedTaper {X : ℕ} (hX : 2 ≤ X) (β : ℝ) (z : ℂ) :
    weightedTransform X (2 * X - 1) β (fun k => (scaledWeight (X : ℝ) (k : ℝ) : ℂ)) z =
      weightedTaperTransform X (2 * X - 1) (fun k => scaledWeight (X : ℝ) (k : ℝ)) β z := by
  let b := 2 * X - 1
  let w (k : ℕ) := scaledWeight (X : ℝ) (k : ℝ)
  have hb : X + 1 ≤ b := by dsimp [b]; omega
  have hbc : b + 1 = 2 * X := by dsimp [b]; omega
  have hX' : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlast : w (b+1) = 0 := by
    rw [hbc]
    apply weight_zero (Or.inr ?_)
    push_cast
    rw [mul_div_cancel_right₀ _ hX'.ne']
    norm_num
  have hI : Ioc X (b-1) = Ico (X+1) b := by
    ext k
    simp only [mem_Ioc, mem_Ico]
    omega
  change (w b : ℂ) * transform X b β z +
    (∑ k ∈ Ioc X (b-1), ((w k : ℂ) - w (k+1)) * transform X k β z) =
    (∑ k ∈ Ico (X+1) (b+1), ((w k - w (k+1) : ℝ) : ℂ) * transform X k β z)
  rw [sum_Ico_succ_top hb, hI, hlast, sub_zero, add_comm]
  push_cast
  rfl

end
end GoldbachWeightedMajorResidual

end

section

namespace GoldbachWeightedMajorResidual

open Finset MeasureTheory Goldbach GoldbachTwistedMellin
open GoldbachWeightedException (cutoff)
open GoldbachConductorRegroup GoldbachCorrectionBands GoldbachCorrectionCounts GoldbachSpectralGeometry
open scoped Classical

noncomputable section


theorem cutoff_scale {X : ℕ} (hX : 2 ^ 200 ≤ X) :
    1 ≤ cutoff X ∧ (cutoff X : ℝ) ≤ 4*(X:ℝ)^(41/200 : ℝ) ∧ cutoff X ≤ X := by
  have h4 : 2^200 ≤ 4 * X := by omega
  obtain ⟨hp,_,hp',_,_⟩ := GoldbachWeightedException.chosen_cutoff_bounds (X:=X) h4
  have hx : (2:ℝ) ^ 200 ≤ X := by exact_mod_cast hX
  have hx1 := (by norm_num : (1:ℝ) ≤ 2^200).trans hx
  have hx0 := zero_lt_one.trans_le hx1
  have he : ((4*X:ℕ):ℝ) = 4*(X:ℝ) := by push_cast; rfl
  have hb : (4:ℝ)^(41/200:ℝ) ≤ 4 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) (by norm_num : (41/200:ℝ) ≤ 1)
  change (cutoff X : ℝ) ≤ ((4*X:ℕ):ℝ)^(41/200:ℝ) at hp'
  rw [he, Real.mul_rpow (by norm_num) hx0.le] at hp'
  have hp'' : (cutoff X : ℝ) ≤ 4*(X:ℝ)^(41/200 : ℝ) :=
    hp'.trans (mul_le_mul_of_nonneg_right hb (by positivity))
  have h4x : (4:ℝ) ≤ (X:ℝ)^(159/200:ℝ) := calc
    _ ≤ (2:ℝ)^((200:ℝ)*(159/200)) := by
      norm_num [show ((200:ℝ)*(159/200)) = (159:ℕ) by norm_num, Real.rpow_natCast]
    _ = ((2:ℝ)^200)^(159/200:ℝ) := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have hf : 4*(X:ℝ)^(41/200:ℝ) ≤ X := calc
    _ ≤ (X:ℝ)^(159/200:ℝ)*(X:ℝ)^(41/200:ℝ) :=
      mul_le_mul_of_nonneg_right h4x (by positivity)
    _ = _ := by
      rw [← Real.rpow_add hx0]
      rw [show (159/200:ℝ)+41/200 = 1 by norm_num,Real.rpow_one]
  refine ⟨hp,hp'',?_⟩
  exact_mod_cast hp''.trans hf

end
end GoldbachWeightedMajorResidual

end


section

section



-- Selected from openai/math, lean/OAI/NumberTheory/PrimeGaps/MultiplicativeSieve.lean, revision f5702854040e97fa7675c21ba37a9608f5f92dd3 (Apache-2.0, see upstream/LICENSE).


/-
Gallagher's finite frequency smoothing inequality, as in Gallagher,
A large sieve density estimate near σ = 1, p. 330, Lemma 1.
Adapted from Steve Hubbard's goldbach-lean, Apache-2.0, commit
05fe86a4649a4bb2728244a8805ec6bbc822d250,
entries/gallagher1975/LeanLab/Linnik/Decomp1532b.lean, U1394Fejer.lean,
LiLiuDisplay37.lean, and LeanLab/PNTPort/LargeSieve/Basic.lean.
-/


namespace GoldbachHybridSieve

open Finset MeasureTheory
open OAI.LargePrimeGaps
open scoped Classical

set_option maxHeartbeats 0 in
noncomputable def sieveCost (Q : ℕ) : ℝ :=
  (Q : ℝ) ^ 2 * (harmonic (Q ^ 2) : ℝ)

set_option maxHeartbeats 0 in
theorem sum_fin_Ioc {α : Type*} [AddCommMonoid α] (M L : ℕ) (f : ℕ → α) :
    (∑ n : Fin L, f (M + 1 + n.val)) = ∑ n ∈ Ioc M (M + L), f n := by
  refine Finset.sum_bij (fun n _ => M + 1 + n.val) ?_ ?_ ?_ ?_
  · intro n _
    rw [Finset.mem_Ioc]
    have := n.isLt
    omega
  · intro n _ m _ h
    apply Fin.ext
    omega
  · intro n hn
    rw [Finset.mem_Ioc] at hn
    exact ⟨⟨n - (M + 1), by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
  · intro n _
    rfl


open GoldbachGallagherKernel Set


end GoldbachHybridSieve
end


section

namespace GoldbachHybridSieve

open Finset
open scoped Classical

noncomputable def primitiveCharacters (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  univ.filter (fun χ => χ.IsPrimitive)


end GoldbachHybridSieve


end


section

section

open Complex Finset Set MeasureTheory GoldbachGrhGrowth


open Complex Set MeasureTheory Filter Asymptotics

namespace GoldbachDensityDetector
noncomputable section


/-- Residue at the pole of zeta after the quadratic Riesz shift. -/
def zetaRieszPole (Y : ℝ) (M ρ : ℂ) : ℂ :=
  ((Y : ℂ) ^ (1 - ρ) * M) *
    (2 / ((1 - ρ) * (1 - ρ + 1) * (1 - ρ + 2)))

theorem norm_zetaRieszPole_le {Y : ℝ} (hY : 0 < Y) (M ρ : ℂ) (hρ : ρ.im ≠ 0) :
    ‖zetaRieszPole Y M ρ‖ ≤ 2 * Y ^ (1 - ρ.re) * ‖M‖ / |ρ.im| ^ 3 := by
    have h₁ : |ρ.im| ≤ ‖1 - ρ‖ := by simpa using Complex.abs_im_le_norm ((1 : ℂ) - ρ)
    have h₂ : |ρ.im| ≤ ‖1 - ρ + 1‖ := by simpa using Complex.abs_im_le_norm ((1 : ℂ) - ρ + 1)
    have h₃ : |ρ.im| ≤ ‖1 - ρ + 2‖ := by
      simpa [show (2 : ℂ).im = 0 by norm_num] using Complex.abs_im_le_norm ((1 : ℂ) - ρ + 2)
    have hden : |ρ.im| ^ 3 ≤ ‖1 - ρ‖ * ‖1 - ρ + 1‖ * ‖1 - ρ + 2‖ := by
      rw [pow_succ, pow_succ, pow_one]
      gcongr
    have hab : 0 < |ρ.im| ^ 3 := pow_pos (abs_pos.mpr hρ) _
    unfold zetaRieszPole
    rw [norm_mul, norm_mul, norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hY,
      Complex.sub_re, Complex.one_re, show ‖(2 : ℂ)‖ = 2 by norm_num]
    calc
      _ = (2 * Y ^ (1 - ρ.re) * ‖M‖) /
          (‖1 - ρ‖ * ‖1 - ρ + 1‖ * ‖1 - ρ + 2‖) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hab hden

end
end GoldbachDensityDetector

open Complex Filter MeasureTheory Set
open scoped Topology


end

namespace GoldbachPrincipalDensity

open Complex Set Filter MeasureTheory GoldbachCubicRiesz GoldbachDensityDetector
open scoped Topology


private theorem regular_zeta_eq {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunctionTrivChar₁ 1 s = (s - 1) * riemannZeta s := by
  rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs]
  change (s - 1) * χ₁.LFunction s = _
  rw [DirichletCharacter.LFunction_modOne_eq]

private theorem regular_zeta_one : DirichletCharacter.LFunctionTrivChar₁ 1 1 = 1 := by
  simp [DirichletCharacter.LFunctionTrivChar₁]


private theorem integrable_of_continuous_tail {f : ℝ → ℂ} (hf : Continuous f) {A C : ℝ}
    (hbound : ∀ t, A ≤ |t| → ‖f t‖ ≤ C / (1 + t ^ 2)) : Integrable f := by
  let S : Set ℝ := Icc (-A) A
  have hcomp : IntegrableOn f S := hf.continuousOn.integrableOn_Icc
  have htail : IntegrableOn f Sᶜ := by
    have hmaj : IntegrableOn (fun t : ℝ => C / (1 + t ^ 2)) Sᶜ := by
      simpa only [div_eq_mul_inv] using (integrable_inv_one_add_sq.const_mul C).integrableOn
    apply hmaj.mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_Icc.compl : MeasurableSet Sᶜ)] with t ht
    exact hbound t (le_of_not_ge fun hs => ht (abs_le.mp hs))
  have h := hcomp.union htail
  rwa [Set.union_compl_self, integrableOn_univ] at h


end GoldbachPrincipalDensity


end

section

namespace GoldbachScaledDensity

open Finset Goldbach GoldbachTwistedMellin GoldbachHybridSieve GoldbachTypeII

noncomputable section

private theorem log_two_upper : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h
  exact h


/-- The integer length used by both finite detectors. -/
def detectorLength (Q : ℕ) (T : ℝ) : ℕ :=
  max 2 ⌈(sieveCost Q+2)*(T+1)⌉₊

/-- Upper bounds for the integer detector length and the two logarithmic scales. -/
theorem detector_length_scales {X T : ℝ} (hX : 2 ≤ X) {Q : ℕ} (hQ : 1 ≤ Q)
    (hT : 0 ≤ T) (hscale : (Q : ℝ)^2*(T+1) ≤ 1024*X^(497/1000 : ℝ)) :
    let U := 1+Real.log X
    let D := detectorLength Q T
    2 ≤ D ∧ (sieveCost Q+2)*(T+1) ≤ D ∧
      (D : ℝ) ≤ (32768*U)*X^(497/1000 : ℝ) ∧
      1+Real.log (D:ℝ) ≤ 16*U ∧ logHeight Q (T+1) ≤ 13*U := by
  let U := 1+Real.log X
  let V := (sieveCost Q+2)*(T+1)
  let D := detectorLength Q T
  have hX₁ : 1 ≤ X := by linarith only [hX]
  have hXp := zero_lt_one.trans_le hX₁
  have hXlog := Real.log_nonneg hX₁
  have hU₁ : 1 ≤ U := by dsimp only [U]; linarith only [hXlog]
  have hU₀ := zero_lt_one.trans_le hU₁
  have hQ₁ : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ₀ := zero_lt_one.trans_le hQ₁
  have hp : X^(497/1000 : ℝ) ≤ X := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX₁ (show (497/1000 : ℝ) ≤ 1 by norm_num)
  have hp₁ : 1 ≤ X^(497/1000 : ℝ) := Real.one_le_rpow hX₁ (by norm_num)
  have hp₀ := zero_lt_one.trans_le hp₁
  have hscale' : (Q:ℝ)^2*(T+1) ≤ 1024*X :=
    hscale.trans (mul_le_mul_of_nonneg_left hp (by norm_num))
  have hQsq : (Q:ℝ) ≤ (Q:ℝ)^2 := by
    simpa only [pow_one] using pow_le_pow_right₀ hQ₁ (by norm_num : (1:ℕ) ≤ 2)
  have hrow : (Q:ℝ)*(T+1) ≤ (Q:ℝ)^2*(T+1) :=
    mul_le_mul_of_nonneg_right hQsq (by positivity)
  have hQX : (Q:ℝ) ≤ 1024*X := by
    apply le_trans _ (hrow.trans hscale')
    calc
      (Q:ℝ) = (Q:ℝ)*1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hT]) hQ₀.le
  have hlogQ : Real.log (Q:ℝ) ≤ 10+Real.log X := by
    have hlog := Real.log_le_log hQ₀ hQX
    rw [Real.log_mul (by norm_num) hXp.ne',show (1024:ℝ)=2^10 by norm_num,Real.log_pow] at hlog
    norm_num at hlog
    linarith only [hlog,log_two_upper]
  have hH : logHeight Q (T+1) ≤ 13*U := by
    unfold logHeight
    rw [abs_of_nonneg (by positivity)]
    have hA : 2*(Q:ℝ)*(2+(T+1)) ≤ (8192:ℝ)*X := by
      calc
        _ ≤ 6*((Q:ℝ)*(T+1)) := by
          nlinarith only [mul_nonneg hQ₀.le hT]
        _ ≤ 6*(1024*X) :=
          mul_le_mul_of_nonneg_left (hrow.trans hscale') (by norm_num)
        _ ≤ _ := by nlinarith only [hXp.le]
    have hlog := Real.log_le_log (by positivity) hA
    rw [Real.log_mul (by norm_num) hXp.ne',show (8192:ℝ)=2^13 by norm_num,Real.log_pow] at hlog
    norm_num at hlog
    dsimp only [U]
    linarith only [hlog,hXlog,log_two_upper]
  have hharm : (harmonic (Q^2) : ℝ) ≤ 23*U := by
    have h := harmonic_le_one_add_log (Q^2)
    rw [Nat.cast_pow,Real.log_pow] at h
    norm_num at h
    dsimp only [U]
    linarith only [h,hlogQ,hXlog]
  have hharm₀ : 0 ≤ (harmonic (Q^2) : ℝ) := by
    have h : (1:ℝ) ≤ (↑(Q^2+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (Q^2))
    exact (Real.log_nonneg h).trans (log_add_one_le_harmonic (Q^2))
  have hQsq₁ : 1 ≤ (Q:ℝ)^2 := one_le_pow₀ hQ₁
  have hV₀ : 0 ≤ V := by unfold V sieveCost; positivity
  have hVbound : V ≤ (25600*U)*X^(497/1000 : ℝ) := by
    unfold V sieveCost
    have hS : ((Q:ℝ)^2 * (harmonic (Q^2) : ℝ) + 2) ≤ (25*U)*(Q:ℝ)^2 := by
      have hs := mul_le_mul_of_nonneg_left hharm (sq_nonneg (Q:ℝ))
      have hu := mul_le_mul hU₁ hQsq₁ (by norm_num) hU₀.le
      nlinarith only [hs,hu]
    calc
      _ ≤ ((25*U)*(Q:ℝ)^2)*(T+1) := mul_le_mul_of_nonneg_right hS (by positivity)
      _ = (25*U)*((Q:ℝ)^2*(T+1)) := by ring
      _ ≤ (25*U)*(1024*X^(497/1000 : ℝ)) := mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by ring
  have hUprod : 1 ≤ U*X^(497/1000 : ℝ) := by
    simpa only [one_mul] using mul_le_mul hU₁ hp₁ (by norm_num) hU₀.le
  have hD₂ : 2 ≤ D := le_max_left _ _
  have hDS : V ≤ D := (Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_right 2 ⌈V⌉₊))
  have hD_bound : (D:ℝ) ≤ (32768*U)*X^(497/1000 : ℝ) := by
    change (↑(max 2 ⌈V⌉₊):ℝ) ≤ _
    rw [Nat.cast_max]
    apply max_le
    · norm_num
      nlinarith only [hUprod]
    · have hc := Nat.ceil_lt_add_one hV₀
      linarith only [hc,hVbound,hUprod]
  have hDlog : 1+Real.log (D:ℝ) ≤ 16*U := by
    have hDpos : (0:ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    have hlog := Real.log_le_log hDpos hD_bound
    rw [Real.log_mul (by positivity) hp₀.ne',Real.log_mul (by norm_num) hU₀.ne',
      Real.log_rpow hXp,show (32768:ℝ)=2^15 by norm_num,Real.log_pow] at hlog
    norm_num at hlog
    have hu := Real.log_le_sub_one_of_pos hU₀
    dsimp only [U] at hu ⊢
    nlinarith only [hlog,hu,log_two_upper,hXlog]
  exact ⟨hD₂,hDS,hD_bound,hDlog,hH⟩


section
open Finset Goldbach GoldbachDensitySlices GoldbachTypeII OAI.Ostmann
open scoped Classical

noncomputable section

private def ostmannCharacter {Q : ℕ} (i : ↥(primitiveNonprincipalFamily Q)) :
    PrimitiveComplexCharacter :=
  ⟨i.val.1.val+1,Nat.succ_pos _,i.val.2,
    (mem_primitiveNonprincipalFamily.mp i.property).1,
    (mem_primitiveNonprincipalFamily.mp i.property).2⟩

private theorem ostmannCharacter_injective (Q : ℕ) :
    Function.Injective (ostmannCharacter (Q:=Q)) := by
  intro i j h
  have hq : i.val.1=j.val.1 :=
    Fin.ext (Nat.add_right_cancel (congrArg PrimitiveComplexCharacter.modulus h))
  have he := congrArg
    (fun k : PrimitiveComplexCharacter => (⟨k.modulus,k.character⟩ : Σ q : ℕ, DirichletCharacter ℂ q)) h
  exact Subtype.ext (Sigma.ext hq (Sigma.mk.inj_iff.mp he).2)

private theorem ostmannCharacter_L {Q : ℕ} (i : ↥(primitiveNonprincipalFamily Q)) :
    (ostmannCharacter i).L = regularizedL i.val.2 := by
  rw [regularizedL,ite_eq_right (mem_primitiveNonprincipalFamily.mp i.property).2]
  rfl

/-- Transfer multiplicities through the certified equivalence between the
Ostmann indices and the actual Dirichlet L-function zero tags. -/
theorem densityZeros_order_le_ostmann_count {Q : ℕ} (i : ↥(primitiveNonprincipalFamily Q))
    {σ T U : ℝ} (hσ : 0 < σ) (hTU : T ≤ U) :
    (∑ ρ∈densityZeros i.val.2 σ T,analyticOrderNatAt (regularizedL i.val.2) ρ) ≤
      (V1 (ostmannCharacter i)).count σ U := by
  let D := densityZeros i.val.2 σ T
  let m := fun ρ : ℂ => analyticOrderNatAt (regularizedL i.val.2) ρ
  let F := D.attach.sigma (fun ρ => range (m ρ.val))
  let χ := ostmannCharacter i
  have hχ : i.val.2 ≠ 1 := (mem_primitiveNonprincipalFamily.mp i.property).2
  have he : χ.L = regularizedL i.val.2 := ostmannCharacter_L i
  have hL : χ.L = i.val.2.LFunction := by
    rw [he,regularizedL,ite_eq_right hχ]
  let packed (p : ↥F) : V2o χ := by
    obtain ⟨hρ,hρ₁,_,hz⟩ := mem_densityZeros.mp p.val.1.property
    have hz' : i.val.2.LFunction p.val.1.val=0 := by
      simpa only [regularizedL,ite_eq_right hχ] using hz
    have hρ' : (p.val.1.val).re<1 := lt_of_not_ge fun hh =>
      (i.val.2.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hh) hz'
    refine ⟨⟨p.val.1.val,p.val.2⟩,⟨hσ.trans_le hρ,hρ',by rw [hL,hz']⟩,?_⟩
    rw [he]
    exact mem_range.mp (mem_sigma.mp p.property).2
  let index (p : ↥F) := (V37 χ).symm (packed p)
  have hIndex (p : ↥F) : (V1 χ).zeros (index p)=p.val.1.val := by
    change ((V37 χ) ((V37 χ).symm (packed p))).val.1 = _
    rw [Equiv.apply_symm_apply]
  have hInj : Function.Injective index := by
    intro p p' hp
    have hh := congrArg Subtype.val ((V37 χ).symm.injective hp : packed p=packed p')
    change (p.val.1.val,p.val.2)=(p'.val.1.val,p'.val.2) at hh
    apply Subtype.ext
    refine Sigma.ext (Subtype.ext (congrArg Prod.fst hh)) ?_
    exact heq_of_eq (congrArg Prod.snd hh)
  have hCard : F.card = ((Finset.univ : Finset ↥F).card) := by simp
  calc
    _ = F.card := by simp only [F,card_sigma,card_range,m,Finset.sum_attach,D]
    _ = (Finset.univ : Finset ↥F).card := hCard
    _ ≤ _ := by
      unfold ComplexZeroEnumeration.count
      apply card_le_card_of_injOn index
      · intro p _
        obtain ⟨hρ,_,ht,_⟩ := mem_densityZeros.mp p.val.1.property
        refine mem_filter.mpr ⟨(ComplexZeroEnumeration.V2r (V1 χ) U _).mpr ?_,?_⟩
        · rw [hIndex]
          exact ht.trans hTU
        · rwa [hIndex]
      · intro p _ p' _ h
        exact hInj h

set_option maxHeartbeats 1700000 in
/-- V1eq.V1xi provides the exact previous density exponent and logarithmic
power on the conductor-height boxes used by the adaptive cutoff. -/
theorem nonprincipal_scaled_weighted_count_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : ℝ} (_hX : 2 ≤ X) (Q : ℕ) (_hQ : 1 ≤ Q) {σ T : ℝ},
      3/4 ≤ σ → σ ≤ 1 → 0 ≤ T →
      (Q:ℝ)^2*(T+1) ≤ 1024*X^(497/1000 : ℝ) →
      (∑ r ∈ familyZeroTags Q σ T,(analyticOrderNatAt (regularizedL r.1.2) r.2 : ℝ)) ≤
        C*(1+Real.log X)^13*X^(2*(497/500 : ℝ)*(1-σ)) := by
  obtain ⟨C,hC,hCount⟩ := V1eq.V1xi
  refine ⟨2048*12^13*C,by positivity,?_⟩
  intro X hX Q hQ σ T hσ hσ₁ hT hscale
  let U := max 2 T
  let F := (primitiveNonprincipalFamily Q).attach
  let j : (↥(primitiveNonprincipalFamily Q)) ↪ PrimitiveComplexCharacter :=
    ⟨ostmannCharacter,ostmannCharacter_injective Q⟩
  let S := F.map j
  have hS : ∀ c∈S,c.modulus≤Q := by
    intro c hc
    obtain ⟨i,_,rfl⟩ := mem_map.mp hc
    exact i.val.1.isLt
  have hFam :
      (∑ r ∈ familyZeroTags Q σ T,(analyticOrderNatAt (regularizedL r.1.2) r.2 : ℝ)) ≤
      ∑ c∈S,((V1 c).count σ U:ℝ) := by
    rw [familyZeroTags,Finset.sum_sigma,show S=F.map j from rfl,Finset.sum_map]
    rw [←Finset.sum_attach (s:=primitiveNonprincipalFamily Q)]
    apply sum_le_sum
    intro i _
    have hi := densityZeros_order_le_ostmann_count i
      (show 0<σ by linarith only [hσ]) (le_max_right 2 T)
    exact_mod_cast hi
  have hh := hCount Q hQ U σ (le_max_left 2 T) (by linarith only [hσ]) hσ₁ S hS
  refine hFam.trans (hh.trans ?_)
  have hX1 : 1≤X := by linarith only [hX]
  have hX0 := zero_lt_one.trans_le hX1
  have hQ1 : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hQ0 := zero_lt_one.trans_le hQ1
  have hU1 : 1≤U := (by norm_num : (1:ℝ)≤2).trans (le_max_left _ _)
  have hU0 := zero_lt_one.trans_le hU1
  have hU2 : U≤2*(T+1) := max_le (by linarith only [hT]) (by linarith only [hT])
  have hScale : (Q:ℝ)^2*U ≤ 2048*X^(497/1000:ℝ) := calc
    _ ≤ (Q:ℝ)^2*(2*(T+1)) := mul_le_mul_of_nonneg_left hU2 (sq_nonneg _)
    _ = 2*((Q:ℝ)^2*(T+1)) := by ring
    _ ≤ _ := by nlinarith only [hscale]
  have hPt : X^(497/1000:ℝ)≤X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1
      (by norm_num : (497/1000:ℝ)≤1)
  have hlog₀ : 0≤Real.log ((Q:ℝ)*U) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQ1 hU1)
  have hlog : Real.log ((Q:ℝ)*U) ≤ 12*(1+Real.log X) := by
    have hQsq : (Q:ℝ)≤(Q:ℝ)^2 := by nlinarith only [mul_nonneg hQ0.le (sub_nonneg.mpr hQ1)]
    have hProd := (mul_le_mul_of_nonneg_right hQsq hU0.le).trans
      (hScale.trans (mul_le_mul_of_nonneg_left hPt (by norm_num)))
    have h := Real.log_le_log (mul_pos hQ0 hU0) hProd
    rw [Real.log_mul (by norm_num) hX0.ne',show (2048:ℝ)=2^11 by norm_num,Real.log_pow] at h
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at ht h
    linarith only [h,ht,Real.log_nonneg hX1]
  let e := 4*(1-σ)
  have he₀ : 0≤e := by dsimp only [e]; positivity [sub_nonneg.mpr hσ₁]
  have he₁ : e≤1 := by dsimp only [e]; linarith only [hσ]
  have hCe : (2048:ℝ)^e≤2048 := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2048) he₁)
  have hP : ((Q:ℝ)^2*U)^e ≤ 2048*X^(2*(497/500:ℝ)*(1-σ)) := calc
    _ ≤ (2048*X^(497/1000:ℝ))^e :=
      Real.rpow_le_rpow (by positivity) hScale he₀
    _ = (2048:ℝ)^e*X^(2*(497/500:ℝ)*(1-σ)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity),← Real.rpow_mul hX0.le]
      congr 2
      dsimp only [e]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hCe (by positivity)
  have hLogPow := pow_le_pow_left₀ hlog₀ hlog (13:ℕ)
  calc
    _ ≤ C*(2048*X^(2*(497/500:ℝ)*(1-σ)))*(12*(1+Real.log X))^13 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hP hC.le) hLogPow (by positivity) (by positivity)
    _ = _ := by ring

end
end

end
end GoldbachScaledDensity

end


end

section

namespace GoldbachLowZeroEnergy

open Finset Goldbach GoldbachTwistedMellin GoldbachTypeII GoldbachDensitySlices
  GoldbachScaledDensity GoldbachPrincipalDensity GoldbachExceptionalTail GoldbachHybridSieve
open scoped Classical

noncomputable section

private theorem selected_point_order_bound : ∃ M : ℝ, 0 < M ∧
    ∀ {X T : ℝ} (Q : ℕ), 2 ≤ X → 1 ≤ Q → 0 ≤ T →
      (Q:ℝ)^2*(T+1) ≤ 1024*X^(497/1000:ℝ) →
      ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), q ≤ Q → ∀ ρ : ℂ,
        1/2 ≤ ρ.re → ρ.re ≤ 2 → |ρ.im| ≤ T →
        (analyticOrderNatAt (regularizedL χ) ρ : ℝ) ≤ M*(1+Real.log X) := by
  obtain ⟨A,hA,hcount⟩ := unconditional_right_slice_count
  refine ⟨13*A,by positivity,?_⟩
  intro X T Q hX hQ hT hscale q _ χ hq ρ hre hlo him
  obtain ⟨_,_,_,_,hH⟩ := detector_length_scales hX hQ hT hscale
  have hq₀ : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqQ : (q:ℝ) ≤ Q := by exact_mod_cast hq
  have hlog : logHeight q ρ.im ≤ logHeight Q (T+1) := by
    unfold logHeight
    rw [abs_of_nonneg (by positivity : 0 ≤ T+1)]
    apply Real.log_le_log (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hqQ (by norm_num))
      (by linarith only [him]) (by positivity) (by positivity)
  have hlocal := hcount q χ ρ.im ({ρ} : Finset ℂ) (by
    intro z hz
    rw [mem_singleton.mp hz]
    exact ⟨hre,hlo,by norm_num⟩)
  calc
    _ ≤ A * logHeight q ρ.im := by simpa only [sum_singleton] using hlocal
    _ ≤ A * (13*(1+Real.log X)) := mul_le_mul_of_nonneg_left (hlog.trans hH) hA.le
    _ = _ := by ring

/-- Actual family zero tags restricted to the selected sets in one conductor bin. -/
def selectedTags (Q : ℕ) (F : (q : ℕ) → DirichletCharacter ℂ q → Finset ℂ) :
    Finset (TaggedZero Q) :=
  (primitiveNonprincipalFamily Q).sigma (fun i => F (i.1.val+1) i.2)

/-- The dependent character sum at a positive conductor, extended by zero at `q = 0`. -/
def nonprincipalFiberEnergy (X : ℝ) (q : ℕ)
    (F : (r : ℕ) → DirichletCharacter ℂ r → Finset ℂ) : ℝ :=
  if h : q = 0 then 0 else
    letI : NeZero q := ⟨h⟩
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive ∧ χ ≠ 1),
      ∑ ρ ∈ F q χ, (analyticOrderNatAt (regularizedL χ) ρ : ℝ)^2 * X^(2*ρ.re-1)

/-- The selected tag sum is the original sum over integer conductors and characters. -/
theorem selected_tag_energy_eq (X : ℝ) (Q : ℕ)
    (F : (q : ℕ) → DirichletCharacter ℂ q → Finset ℂ) :
    (∑ j ∈ selectedTags Q F,
      (analyticOrderNatAt (regularizedL j.1.2) j.2 : ℝ)^2 * X^(2*j.2.re-1)) =
    ∑ q ∈ Icc 1 Q, nonprincipalFiberEnergy X q F := by
  let f (q : ℕ) := nonprincipalFiberEnergy X q F
  have hIoc : Ioc 0 (0+Q) = Icc 1 Q := by ext q; simp; omega
  calc
    _ = ∑ q : Fin Q, f (q.val+1) := by
      rw [selectedTags, sum_sigma]
      simp only [primitiveNonprincipalFamily, sum_filter, Fintype.sum_sigma, f,
        nonprincipalFiberEnergy, Nat.succ_ne_zero, dite_false]
    _ = ∑ q : Fin Q, f (0+1+q.val) := by
      apply sum_congr rfl
      intro q _
      congr 1
      omega
    _ = _ := by rw [sum_fin_Ioc,hIoc]

/-- The square-order energy over all primitive characters at a positive conductor. -/
def primitiveFiberEnergy (X : ℝ) (q : ℕ)
    (F : (r : ℕ) → DirichletCharacter ℂ r → Finset ℂ) : ℝ :=
  if h : q = 0 then 0 else
    letI : NeZero q := ⟨h⟩
    ∑ χ ∈ primitiveCharacters q,
      ∑ ρ ∈ F q χ, (analyticOrderNatAt (regularizedL χ) ρ : ℝ)^2 * X^(2*ρ.re-1)

theorem primitive_fiber_energy_eq (X : ℝ) {q : ℕ} (hq : 1 ≤ q)
    (F : (r : ℕ) → DirichletCharacter ℂ r → Finset ℂ) :
    primitiveFiberEnergy X q F = nonprincipalFiberEnergy X q F +
      if q = 1 then ∑ ρ ∈ F 1 1,
        (analyticOrderNatAt (regularizedL (1:DirichletCharacter ℂ 1)) ρ : ℝ)^2 * X^(2*ρ.re-1)
      else 0 := by
  have hq₀ : q ≠ 0 := by omega
  let _ : NeZero q := ⟨hq₀⟩
  unfold primitiveFiberEnergy nonprincipalFiberEnergy
  rw [dite_eq_right hq₀,dite_eq_right hq₀]
  by_cases he : q = 1
  · subst q
    have hchars : primitiveCharacters 1 = {1} := by
      apply Finset.ext
      intro χ
      simp only [primitiveCharacters,mem_filter,mem_univ,true_and,mem_singleton]
      rw [DirichletCharacter.level_one χ]
      simp [DirichletCharacter.isPrimitive_one_level_one]
    simp [hchars,DirichletCharacter.level_one]
  · rw [ite_eq_right he, add_zero]
    congr 1
    ext χ
    simp only [primitiveCharacters,mem_filter,mem_univ,true_and]
    refine ⟨fun hp => ⟨hp,?_⟩,And.left⟩
    intro hc
    exact he (((DirichletCharacter.isPrimitive_def χ).mp hp).symm.trans
      (DirichletCharacter.eq_one_iff_conductor_eq_one.mp hc))

end
end GoldbachLowZeroEnergy

end

section

namespace GoldbachPowerBins

open Finset

noncomputable section

/-- The index of the interval of logarithmic length `1/1000` containing a conductor. -/
def binIndex (X r : ℝ) : ℕ :=
  ⌊1000 * (Real.log r / Real.log X)⌋₊

/-- Upper endpoint of a conductor bin. -/
def binUpper (X : ℝ) (k : ℕ) : ℝ :=
  X ^ (((k : ℝ) + 1) / 1000)

theorem binUpper_pos {X : ℝ} (hX : 0 < X) (k : ℕ) :
    0 < binUpper X k :=
  Real.rpow_pos_of_pos hX _

/-- Every conductor in `[1,X]` lies in one of the first 1001 bins. -/
theorem bin_geometry {X r : ℝ} (hX : 1 < X) (hr : 1 ≤ r) (hrX : r ≤ X) :
    let k := binIndex X r
    let R := binUpper X k
    R / X ^ (1/1000 : ℝ) ≤ r ∧ r ≤ R ∧ k ≤ 1000 := by
  let u := Real.log r / Real.log X
  have hX₀ := zero_lt_one.trans hX
  have hr₀ := zero_lt_one.trans_le hr
  have hlog := Real.log_pos hX
  have hu₀ : 0 ≤ u := div_nonneg (Real.log_nonneg hr) hlog.le
  have hu₁ : u ≤ 1 := (div_le_iff₀ hlog).2 (by
    simpa only [one_mul] using Real.log_le_log hr₀ hrX)
  have hrpow : X ^ u = r := Real.rpow_logb hX₀ hX.ne' hr₀
  let k := binIndex X r
  have hlo : (k : ℝ) ≤ 1000 * u := Nat.floor_le (by positivity)
  have hhi : 1000 * u < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk : k ≤ 1000 := by
    exact_mod_cast (show (k : ℝ) ≤ 1000 by linarith only [hlo, hu₁])
  change binUpper X k / X ^ (1/1000 : ℝ) ≤ r ∧ r ≤ binUpper X k ∧ k ≤ 1000
  refine ⟨?_, ?_, hk⟩
  · rw [binUpper, ← Real.rpow_sub hX₀, ← hrpow]
    apply Real.rpow_le_rpow_of_exponent_le hX.le
    linarith only [hlo]
  · rw [binUpper, ← hrpow]
    apply Real.rpow_le_rpow_of_exponent_le hX.le
    linarith only [hhi]

/-- Partition a finite collection into the fixed family of conductor bins. -/
theorem sum_partition {ι A : Type*} [AddCommMonoid A]
    (s : Finset ι) (r : ι → ℝ) (f : ι → A) {X P : ℝ} (hX : 1 < X) (hP : P ≤ X)
    (hr : ∀ i ∈ s, 1 ≤ r i ∧ r i ≤ P) :
    (∑ k ∈ range 1001, ∑ i ∈ s.filter (fun i => binIndex X (r i) = k), f i) =
      ∑ i ∈ s, f i := by
  apply sum_fiberwise_of_maps_to
  intro i hi
  obtain ⟨h₁, h₂⟩ := hr i hi
  exact mem_range.mpr (Nat.lt_succ_of_le (bin_geometry hX h₁ (h₂.trans hP)).2.2)

/-- The altitude cutoff attached to one conductor. -/
def conductorHeight (X P r : ℝ) : ℝ :=
  32 * X^(85/1000 : ℝ) * P / r

/-- A common altitude cutoff valid for all conductors in a bin. -/
def binHeight (X P : ℝ) (k : ℕ) : ℝ :=
  32 * X^(86/1000 : ℝ) * P / binUpper X k

theorem bin_upper_le {X r P : ℝ} (hX : 1 < X) (hr : 1 ≤ r)
    (hrP : r ≤ P) (hPX : P ≤ X) :
    binUpper X (binIndex X r) ≤ P * X^(1/1000 : ℝ) := by
  have hX₀ := zero_lt_one.trans hX
  have h := (bin_geometry hX hr (hrP.trans hPX)).1
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hX₀ _)] at h
  exact h.trans (mul_le_mul_of_nonneg_right hrP (Real.rpow_nonneg hX₀.le _))

/-- The first value is bounded by the bin cutoff for every member of the bin. -/
theorem conductorHeight_le_binHeight {X r P : ℝ} (hX : 1 < X) (hr : 1 ≤ r)
    (hrP : r ≤ P) (hPX : P ≤ X) :
    conductorHeight X P r ≤ binHeight X P (binIndex X r) := by
  have hX₀ := zero_lt_one.trans hX
  have hr₀ := zero_lt_one.trans_le hr
  let k := binIndex X r
  let R := binUpper X k
  have hR : 0 < R := binUpper_pos hX₀ k
  have hleft := (bin_geometry hX hr (hrP.trans hPX)).1
  change R / X^(1/1000 : ℝ) ≤ r at hleft
  have hR' := (div_le_iff₀ (Real.rpow_pos_of_pos hX₀ _)).1 hleft
  have hP₀ := hr₀.trans_le hrP
  unfold conductorHeight binHeight
  change 32 * X^(85/1000 : ℝ) * P / r ≤ 32 * X^(86/1000 : ℝ) * P / R
  apply (div_le_div_iff₀ hr₀ hR).2
  calc
    _ ≤ (32 * X^(85/1000 : ℝ) * P) * (r * X^(1/1000 : ℝ)) :=
      mul_le_mul_of_nonneg_left hR' (by positivity)
    _ = _ := by
      rw [show X^(86/1000 : ℝ) = X^(85/1000 : ℝ) * X^(1/1000 : ℝ) by
        rw [← Real.rpow_add hX₀]
        norm_num]
      ring

/-- For an occupied bin, the conductor-height product has fixed exponent `497/1000`. -/
theorem bin_density_scale_le {X r P : ℝ} (hX : 1 < X) (hr : 1 ≤ r)
    (hrP : r ≤ P) (hPX : P ≤ X) (hP : P ≤ 4 * X^(41/200 : ℝ)) :
    let k := binIndex X r
    (binUpper X k)^2 * binHeight X P k ≤ 512 * X^(497/1000 : ℝ) := by
  let k := binIndex X r
  let R := binUpper X k
  have hX₀ := zero_lt_one.trans hX
  have hR : 0 < R := binUpper_pos hX₀ k
  have hR' : R ≤ P * X^(1/1000 : ℝ) := bin_upper_le hX hr hrP hPX
  have hP₀ := (zero_lt_one.trans_le hr).trans_le hrP
  change R^2 * binHeight X P k ≤ _
  unfold binHeight
  change R^2 * (32 * X^(86/1000 : ℝ) * P / R) ≤ _
  calc
    _ = 32 * X^(86/1000 : ℝ) * P * R := by field_simp [hR.ne']
    _ ≤ 32 * X^(86/1000 : ℝ) * P * (P * X^(1/1000 : ℝ)) :=
      mul_le_mul_of_nonneg_left hR' (by positivity)
    _ = 32 * (X^(86/1000 : ℝ) * X^(1/1000 : ℝ)) * P^2 := by ring
    _ ≤ 32 * (X^(86/1000 : ℝ) * X^(1/1000 : ℝ)) * (4 * X^(41/200 : ℝ))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP₀.le hP 2) (by positivity)
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hX₀.le, ← Real.rpow_add hX₀]
      calc
        _ = 512 * (X^(86/1000 + 1/1000 : ℝ) * X^((41/200 : ℝ) * (2 : ℕ))) := by ring
        _ = _ := by rw [← Real.rpow_add hX₀]; norm_num

/-- The natural cutoff `floor R` preserves the `T+1` density scale in an occupied bin. -/
theorem occupied_bin_floor_scale {X r P : ℝ} (hX : 1 < X) (hr : 1 ≤ r)
    (hrP : r ≤ P) (hPX : P ≤ X) (hP : P ≤ 4*X^(41/200:ℝ)) :
    let k := binIndex X r
    let Q := ⌊binUpper X k⌋₊
    let T := binHeight X P k
    1 ≤ Q ∧ 1 ≤ T ∧ (Q:ℝ)^2*(T+1) ≤ 1024*X^(497/1000:ℝ) ∧ T+1 ≤ 1024*X := by
  let k := binIndex X r
  let R := binUpper X k
  let Q := ⌊R⌋₊
  let T := binHeight X P k
  have hX₀ := zero_lt_one.trans hX
  have hR : 0 < R := binUpper_pos hX₀ k
  have hR' : R ≤ P*X^(1/1000:ℝ) := bin_upper_le hX hr hrP hPX
  have hR₁ : 1 ≤ R := hr.trans (bin_geometry hX hr (hrP.trans hPX)).2.1
  have hQ₁ : 1 ≤ Q := (Nat.one_le_floor_iff R).mpr hR₁
  have hQ' : (Q:ℝ) ≤ R := Nat.floor_le hR.le
  have hT : 1 ≤ T := by
    change 1 ≤ 32*X^(86/1000:ℝ)*P/R
    apply (le_div_iff₀ hR).2
    rw [one_mul]
    refine hR'.trans ?_
    have hp : X^(1/1000:ℝ) ≤ X^(86/1000:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
    have hP₀ : 0 ≤ P := by linarith only [hr,hrP]
    calc
      _ ≤ P*X^(86/1000:ℝ) := mul_le_mul_of_nonneg_left hp hP₀
      _ ≤ _ := by nlinarith only [mul_nonneg hP₀ (Real.rpow_nonneg hX₀.le (86/1000:ℝ))]
  have hRT := bin_density_scale_le hX hr hrP hPX hP
  have hQT : (Q:ℝ)^2*(T+1) ≤ 1024*X^(497/1000:ℝ) := calc
    _ ≤ R^2*(2*T) := mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hQ' 2)
      (by linarith only [hT]) (by linarith only [hT]) (sq_nonneg _)
    _ = 2*(R^2*T) := by ring
    _ ≤ _ := by linarith only [hRT]
  have hpX : X^(497/1000:ℝ) ≤ X := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num : (497/1000:ℝ) ≤ 1)
  have hT' : T+1 ≤ 1024*X := calc
    _ ≤ (Q:ℝ)^2*(T+1) := by
      have hQ₁' : (1:ℝ) ≤ Q := by exact_mod_cast hQ₁
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hQ₁' : 1 ≤ (Q:ℝ)^2)
        (by linarith only [hT] : 0 ≤ T+1)
    _ ≤ 1024*X^(497/1000:ℝ) := hQT
    _ ≤ _ := mul_le_mul_of_nonneg_left hpX (by norm_num)
  exact ⟨hQ₁,hT,hQT,hT'⟩

/-- Every integer conductor meeting the bin's upper endpoint is within the natural cutoff. -/
theorem level_le_bin_floor {X : ℝ} {k q : ℕ} (hq : 1 ≤ q) (hb : (q:ℝ) ≤ binUpper X k) :
    q ≤ ⌊binUpper X k⌋₊ :=
  (Nat.le_floor_iff' (by omega : q ≠ 0)).2 hb

/-- The conductor cutoff stays below `X` once `X ≥ 16`. -/
theorem occupied_bin_floor_le_X {X r P : ℝ} (hX : 16 ≤ X) (hr : 1 ≤ r)
    (hrP : r ≤ P) (hPX : P ≤ X) (hP : P ≤ 4*X^(41/200:ℝ)) :
    (⌊binUpper X (binIndex X r)⌋₊:ℝ) ≤ X := by
  have hX₁ : 1 < X := by linarith only [hX]
  have hX₀ := zero_lt_one.trans hX₁
  have hR := bin_upper_le hX₁ hr hrP hPX
  have hsqrt : 4 ≤ Real.sqrt X := by
    have h := Real.sqrt_le_sqrt hX
    rw [show (16:ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)] at h
    exact h
  have hpow : X^(41/200 + 1/1000:ℝ) ≤ Real.sqrt X := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hX₁.le (by norm_num)
  calc
    _ ≤ binUpper X (binIndex X r) := Nat.floor_le (binUpper_pos hX₀ _).le
    _ ≤ P*X^(1/1000:ℝ) := hR
    _ ≤ (4*X^(41/200:ℝ))*X^(1/1000:ℝ) :=
      mul_le_mul_of_nonneg_right hP (Real.rpow_nonneg hX₀.le _)
    _ = 4*X^(41/200 + 1/1000:ℝ) := by rw [mul_assoc, ← Real.rpow_add hX₀]
    _ ≤ 4*Real.sqrt X := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ X := by nlinarith only [hsqrt,Real.sq_sqrt hX₀.le]

end
end GoldbachPowerBins

end

section

namespace GoldbachLowerStrip

open Complex Finset Goldbach GoldbachTwistedMellin GoldbachDensitySlices GoldbachHybridSieve
open scoped Classical

noncomputable def lowerStripEnergyAt (X H : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  if hq : q ≠ 0 then
    letI : NeZero q := ⟨hq⟩
    ∑ z ∈ (exceptionalZeros χ (heightCut X)).filter (fun z => |z.im| < H ∧ z.re < 3/4),
      (analyticOrderNatAt (regularizedL χ) z : ℝ)^2 * X^(2*z.re-1)
  else 0

theorem lowerStripEnergyAt_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X H : ℝ) :
    lowerStripEnergyAt X H q χ =
      ∑ z ∈ (exceptionalZeros χ (heightCut X)).filter (fun z => |z.im| < H ∧ z.re < 3/4),
        (analyticOrderNatAt (regularizedL χ) z : ℝ)^2 * X^(2*z.re-1) := by
  rw [lowerStripEnergyAt,dite_eq_left (NeZero.ne q)]

private theorem primitive_count_le {q : ℕ} [NeZero q] : (primitiveCharacters q).card ≤ q := by
  have hχ : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  exact ((Finset.card_le_univ _).trans_eq hχ).trans (Nat.totient_le q)

private theorem logHeight_upper {X T : ℝ} (hX : 2 ≤ X) (hT : 0 ≤ T) {Q : ℕ}
    (hQ : 1 ≤ Q) (hQX : (Q:ℝ) ≤ X) (hscale : (Q:ℝ)^2*(T+1) ≤ 1024*X^(497/1000:ℝ)) :
    logHeight Q (T+2) ≤ 14*(1+Real.log X) := by
  have hX1 : 1 ≤ X := by linarith only [hX]
  have hXp := zero_lt_one.trans_le hX1
  have hQ1 : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hTx : T+1 ≤ 1024*X := by
    have h := le_mul_of_one_le_left (show 0 ≤ T+1 by linarith only [hT])
      (show (1:ℝ) ≤ (Q:ℝ)^2 from one_le_pow₀ hQ1)
    have hx : X^(497/1000:ℝ) ≤ X := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1
        (by norm_num : (497/1000:ℝ)≤1)
    exact (h.trans hscale).trans (mul_le_mul_of_nonneg_left hx (by norm_num))
  unfold logHeight
  rw [abs_of_nonneg (by linarith only [hT] : 0 ≤ T+2)]
  have hy : 0 < 2*(Q:ℝ)*(2+(T+2)) := by positivity
  have hy' : 2*(Q:ℝ)*(2+(T+2)) ≤ 4096*X^2 := by
    have hT' : 2+(T+2) ≤ 2048*X := by linarith only [hTx,hX]
    calc
      _ ≤ (2*X)*(2048*X) := mul_le_mul (mul_le_mul_of_nonneg_left hQX (by norm_num))
        hT' (by positivity) (by positivity)
      _ = _ := by ring
  apply (Real.log_le_log hy hy').trans
  rw [Real.log_mul (by norm_num : (4096:ℝ) ≠ 0) (pow_ne_zero _ hXp.ne'),Real.log_pow]
  have hlog : Real.log 4096 ≤ 12 := by
    rw [show (4096:ℝ) = 2^(12:ℕ) by norm_num,Real.log_pow]
    norm_num
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  norm_num
  linarith only [hlog, Real.log_nonneg hX1]

set_option maxHeartbeats 1250000 in
/-- Every primitive character, including the character of conductor one,
contributes at most the Jensen mass times the maximum squared-order weight. -/
theorem lower_strip_primitive_energy_le : ∃ C : ℝ, 0 < C ∧
    ∀ {X T : ℝ}, 2 ≤ X → 0 ≤ T → ∀ (Q : ℕ), 1 ≤ Q → (Q:ℝ) ≤ X →
      (Q:ℝ)^2*(T+1) ≤ 1024*X^(497/1000:ℝ) →
      ∀ (H : ℕ → ℝ), (∀ q ∈ Icc 1 Q, H q ≤ T) →
      (∑ q ∈ Icc 1 Q, ∑ χ ∈ primitiveCharacters q, lowerStripEnergyAt X (H q) q χ) ≤
        C*(1+Real.log X)^2*X^(997/1000:ℝ) := by
  obtain ⟨C₁,hC₁,hind⟩ := individual_multiplicity_bound
  obtain ⟨C₂,hC₂,htotal⟩ := total_multiplicity_bound
  refine ⟨1024*14^2*C₁*C₂,by positivity,?_⟩
  intro X T hX hT Q hQ hQX hscale H hH
  let _ : NeZero Q := ⟨(Nat.zero_lt_one.trans_le hQ).ne'⟩
  let L := logHeight Q (T+2)
  let U := 1+Real.log X
  let W := X^(1/2:ℝ)
  let B := C₁*C₂*L^2*(T+1)*W
  have hX1 : 1 ≤ X := by linarith only [hX]
  have hXp := zero_lt_one.trans_le hX1
  have hL : 0 ≤ L := zero_le_one.trans (logHeight_ge_one Q _)
  have hU : 0 ≤ U := by dsimp [U]; positivity [Real.log_nonneg hX1]
  have hW : 0 ≤ W := Real.rpow_nonneg hXp.le _
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hlocal (q : ℕ) (hq : q ∈ Icc 1 Q) (χ : DirichletCharacter ℂ q) : lowerStripEnergyAt X (H q) q χ ≤ B := by
    have hq1 := (mem_Icc.mp hq).1
    have hqQ := (mem_Icc.mp hq).2
    let _ : NeZero q := ⟨(Nat.zero_lt_one.trans_le hq1).ne'⟩
    let S := (exceptionalZeros χ (heightCut X)).filter (fun z => |z.im| < H q ∧ z.re < 3/4)
    let ord (z : ℂ) : ℝ := (analyticOrderNatAt (regularizedL χ) z : ℝ)
    have hsub : S ⊆ exceptionalZeros χ (heightCut X) := filter_subset _ _
    have hgeo (z : ℂ) (hz : z ∈ S) : 1/2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ T := by
      obtain ⟨hl,hr,_,_⟩ := exceptional_subset_geometry χ hsub z hz
      exact ⟨hl,hr,(mem_filter.mp hz).2.1.le.trans (hH q hq)⟩
    have hi (z : ℂ) (hz : z ∈ S) : ord z ≤ C₁*L := hind q χ Q hqQ T hT S hgeo z hz
    have ht : (∑ z ∈ S, ord z) ≤ C₂*(T+1)*L := htotal q χ Q hqQ T hT S hgeo
    have hp (z : ℂ) (hz : z ∈ S) : ord z^2*X^(2*z.re-1) ≤ (C₁*L*W)*ord z := by
      have hpw : X^(2*z.re-1) ≤ W := by
        apply Real.rpow_le_rpow_of_exponent_le hX1
        linarith only [(mem_filter.mp hz).2.2]
      have h0 : 0 ≤ ord z := Nat.cast_nonneg _
      calc
        _ ≤ ((C₁*L)*ord z)*W := by
          exact mul_le_mul (by rw [pow_two]; exact mul_le_mul_of_nonneg_right (hi z hz) h0)
            hpw (Real.rpow_nonneg hXp.le _) (by positivity)
        _ = _ := by ring
    rw [lowerStripEnergyAt_eq]
    change (∑ z ∈ S, ord z^2*X^(2*z.re-1)) ≤ B
    calc
      _ ≤ ∑ z ∈ S, (C₁*L*W)*ord z := Finset.sum_le_sum hp
      _ ≤ (C₁*L*W)*(C₂*(T+1)*L) := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by dsimp only [B]; ring
  have hqsum (q : ℕ) (hq : q ∈ Icc 1 Q) :
      (∑ χ ∈ primitiveCharacters q, lowerStripEnergyAt X (H q) q χ) ≤ (Q:ℝ)*B := by
    let _ : NeZero q := ⟨(Nat.zero_lt_one.trans_le (mem_Icc.mp hq).1).ne'⟩
    calc
      _ ≤ ∑ _χ ∈ primitiveCharacters q, B := Finset.sum_le_sum (fun χ _ => hlocal q hq χ)
      _ = ((primitiveCharacters q).card:ℝ)*B := by simp [nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (primitive_count_le.trans (mem_Icc.mp hq).2)) hB
  have hQcard : (Icc 1 Q).card = Q := by rw [Nat.card_Icc]; omega
  have hLog2 : L^2 ≤ (14*U)^2 := pow_le_pow_left₀ hL (logHeight_upper hX hT hQ hQX hscale) 2
  have hsc : (((Q:ℝ)^2)*(T+1))*W ≤ 1024*X^(997/1000:ℝ) := by
    apply (mul_le_mul_of_nonneg_right hscale hW).trans_eq
    dsimp only [W]
    rw [mul_assoc,← Real.rpow_add hXp]
    congr 2
    norm_num
  calc
    _ ≤ ∑ _q ∈ Icc 1 Q, (Q:ℝ)*B := Finset.sum_le_sum hqsum
    _ = (Q:ℝ)^2*B := by simp only [Finset.sum_const,hQcard,nsmul_eq_mul]; ring
    _ = C₁*C₂*(L^2*(((Q:ℝ)^2)*(T+1)*W)) := by dsimp only [B]; ring
    _ ≤ C₁*C₂*((14*U)^2*(1024*X^(997/1000:ℝ))) := mul_le_mul_of_nonneg_left
      (mul_le_mul hLog2 hsc (by positivity) (by positivity)) (by positivity)
    _ = _ := by dsimp only [U]; ring

end GoldbachLowerStrip
end

section

section
namespace GoldbachPrincipalDensity

open Complex Filter Finset Goldbach
open scoped Topology Classical

noncomputable section

private theorem principal_order_eq_zeta_order {ρ : ℂ}
    (h : regularizedL (1 : DirichletCharacter ℂ 1) ρ=0) :
    ρ ∈ Vx.V59 ∨ ρ.re≤0 := by
  by_cases he : 0<ρ.re
  · have hρ : ρ ≠ 1 := fun h1 => regularizedL_ne_zero_at_one (1 : DirichletCharacter ℂ 1) (h1 ▸ h)
    have hz : riemannZeta ρ=0 := by
      rw [regularizedL, ite_eq_left rfl, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hρ] at h
      change (ρ-1)*(1:DirichletCharacter ℂ 1).LFunction ρ = 0 at h
      rw [DirichletCharacter.LFunction_modOne_eq] at h
      exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hρ)
    exact Or.inl ⟨he,lt_of_not_ge (fun h1=>riemannZeta_ne_zero_of_one_le_re h1 hz),hz⟩
  · exact Or.inr (le_of_not_gt he)

private theorem principal_zero_multiplicity_eq {ρ : ℂ} (hρ : ρ≠1) :
    analyticOrderNatAt (regularizedL (1 : DirichletCharacter ℂ 1)) ρ =
      analyticOrderNatAt riemannZeta ρ := by
  have he : regularizedL (1 : DirichletCharacter ℂ 1) =ᶠ[𝓝 ρ]
      (fun s : ℂ => (s-1)*riemannZeta s) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hρ)] with z hz
    rw [regularizedL,ite_eq_left rfl,DirichletCharacter.LFunctionTrivChar₁,
      Function.update_of_ne (Set.mem_compl_singleton_iff.mp hz)]
    change (z-1)*(1:DirichletCharacter ℂ 1).LFunction z = _
    rw [DirichletCharacter.LFunction_modOne_eq]
  have hAn : AnalyticAt ℂ (fun z : ℂ=>z-1) ρ := analyticAt_id.sub analyticAt_const
  have hZ : AnalyticAt ℂ riemannZeta ρ := by
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hρ)] with z hz
    exact differentiableAt_riemannZeta (Set.mem_compl_singleton_iff.mp hz)
  have hOrd := hAn.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hρ)
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr he,analyticOrderAt_fun_mul hAn hZ,hOrd,zero_add]

/-- Transfer the accepted multiplicity-tagged principal count to regularized
Dirichlet L-function zeros in an arbitrary finite set. -/
theorem regularized_principal_finite_count_three :
    ∃ C : ℝ, 0<C ∧ ∀ {T σ : ℝ}, 2≤T → 1/2≤σ → σ≤1 →
      ∀ S : Finset ℂ, (∀ ρ∈S, σ≤ρ.re ∧ |ρ.im|≤T ∧
        regularizedL (1 : DirichletCharacter ℂ 1) ρ=0) →
      (∑ ρ∈S,(analyticOrderNatAt (regularizedL (1 : DirichletCharacter ℂ 1)) ρ : ℝ)) ≤
        C*T^(3*(1-σ))*(Real.log T)^13 := by
  classical
  obtain ⟨C,hC,hCount⟩ := GoldbachPrincipalDensityThree.principal_density_three
  refine ⟨C,hC,?_⟩
  intro T σ hT hlo hhi S hS
  let m (ρ : ℂ) := analyticOrderNatAt (regularizedL (1 : DirichletCharacter ℂ 1)) ρ
  let D := S.attach.sigma (fun z=>range (m z.1))
  have hV (ρ : ℂ) (hρ : ρ∈S) : ρ ∈ Vx.V59 :=
    (principal_order_eq_zeta_order (hS ρ hρ).2.2).resolve_right (by
      have hd := hlo.trans (hS ρ hρ).1
      linarith only [hd])
  let f (t : D) : Vx.V1o := ⟨(t.1.1.1,t.1.2),hV t.1.1.1 t.1.1.2,by
    have hh := mem_range.mp (mem_sigma.mp t.2).2
    rw [← principal_zero_multiplicity_eq (fun h => regularizedL_ne_zero_at_one
      (1:DirichletCharacter ℂ 1) (h ▸ (hS t.1.1.1 t.1.1.2).2.2))]
    exact hh⟩
  have hf : Function.Injective f := by
    intro s t he
    have hv := congrArg Subtype.val he
    have hz : s.1.1=t.1.1 := Subtype.ext (congrArg Prod.fst hv)
    have hn : s.1.2=t.1.2 := congrArg Prod.snd hv
    exact Subtype.ext (Sigma.ext hz (heq_of_eq hn))
  let U := D.attach.image f
  have hCount' := hCount T σ hT hlo hhi U
    (fun t ht=>by obtain ⟨s,hs,rfl⟩:=mem_image.mp ht; exact (hS s.1.1.1 s.1.1.2).1)
    (fun t ht=>by obtain ⟨s,hs,rfl⟩:=mem_image.mp ht; exact (hS s.1.1.1 s.1.1.2).2.1)
  have hCard : (U.card:ℝ)=∑ ρ∈S,(m ρ:ℝ) := by
    rw [show U=D.attach.image f from rfl,card_image_of_injective _ hf,card_attach,card_sigma]
    simp only [card_range,Nat.cast_sum]
    exact sum_attach S (fun ρ:ℂ=>(m ρ:ℝ))
  rw [← hCard]
  exact hCount'

/-- The accepted count fits the existing energy argument's logarithmic
budget at every selected height. -/
theorem zeta_selected_density_scale_thirteen :
    ∃ C : ℝ, 0<C ∧ ∀ {X T σ : ℝ}, 2≤X → 0≤T → T+1≤1024*X^(497/1000:ℝ) →
      3/4≤σ → σ≤1 → ∀ S : Finset ℂ,
      (∀ ρ∈S, σ≤ρ.re ∧ |ρ.im|≤T ∧ regularizedL (1:DirichletCharacter ℂ 1) ρ=0) →
      (∑ ρ∈S,(analyticOrderNatAt (regularizedL (1:DirichletCharacter ℂ 1)) ρ : ℝ)) ≤
        C*(1+Real.log X)^13*X^(2*(497/500:ℝ)*(1-σ)) := by
  obtain ⟨C,hC,hM⟩ := regularized_principal_finite_count_three
  let A : ℝ := 1+Real.log 1024
  refine ⟨1024*C*A^13,by dsimp [A]; positivity,?_⟩
  intro X T σ hX hT hs hlo hhi S hS
  let U := max 2 T
  let d := 1-σ
  have hX₁ : 1≤X := by linarith only [hX]
  have hX₀ : 0<X := by linarith only [hX]
  have hd₀ : 0≤d := sub_nonneg.mpr hhi
  have hd₁ : 3*d≤1 := by dsimp [d]; linarith only [hlo]
  have hU : U≤1024*X^(497/1000:ℝ) := max_le
    (by have hh := Real.one_le_rpow hX₁ (by norm_num : (0:ℝ)≤497/1000); linarith only [hh])
    ((le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1)).trans hs)
  have hU₂ : 2≤U := le_max_left _ _
  have hU₀ : 0<U := by linarith only [hU₂]
  have hLog : Real.log U≤A*(1+Real.log X) := by
    have h := Real.log_le_log hU₀ hU
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hX₀ _).ne',Real.log_rpow hX₀] at h
    refine h.trans ?_
    dsimp [A]
    nlinarith only [Real.log_nonneg hX₁,Real.log_nonneg (by norm_num : (1:ℝ)≤1024),
      mul_nonneg (Real.log_nonneg hX₁) (Real.log_nonneg (by norm_num : (1:ℝ)≤1024))]
  have hPow : U^(3*d)≤1024*X^(2*(497/500:ℝ)*d) := calc
    _ ≤ (1024*X^(497/1000:ℝ))^(3*d) := Real.rpow_le_rpow hU₀.le hU (by positivity)
    _ = (1024:ℝ)^(3*d)*X^((497/1000:ℝ)*(3*d)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hX₀.le]
    _ ≤ _ := mul_le_mul
      ((Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤1024) hd₁).trans_eq (Real.rpow_one _))
      (Real.rpow_le_rpow_of_exponent_le hX₁ (by linarith only [hd₀]))
      (by positivity) (by norm_num)
  refine (hM hU₂ (by linarith only [hlo]) hhi S (fun ρ hρ=>?_)).trans ?_
  · obtain ⟨ha,hb,hc⟩ := hS ρ hρ
    exact ⟨ha,hb.trans (le_max_right _ _),hc⟩
  · calc
      _ ≤ C*(1024*X^(2*(497/500:ℝ)*d))*(A*(1+Real.log X))^13 := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hPow hC.le)
          (pow_le_pow_left₀ (Real.log_nonneg (by linarith only [hU₂])) hLog 13)
          (pow_nonneg (Real.log_nonneg (by linarith only [hU₂])) _) (by positivity)
      _ = _ := by rw [mul_pow]; ring

end
end GoldbachPrincipalDensity
end

namespace GoldbachLowZeroGapEnergy

open Finset Filter Goldbach GoldbachTwistedMellin GoldbachTypeII GoldbachDensitySlices
  GoldbachScaledDensity GoldbachPrincipalDensity GoldbachExceptionalTail GoldbachLowZeroEnergy
open scoped Classical Topology

noncomputable section

private theorem selected_point_order_bound : ∃ M : ℝ, 0 < M ∧
    ∀ {X T : ℝ} (Q : ℕ), 2 ≤ X → 1 ≤ Q → 0 ≤ T →
      (Q:ℝ)^2*(T+1) ≤ 1024*X^(497/1000:ℝ) →
      ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), q ≤ Q → ∀ ρ : ℂ,
        1/2 ≤ ρ.re → ρ.re ≤ 2 → |ρ.im| ≤ T →
        (analyticOrderNatAt (regularizedL χ) ρ : ℝ) ≤ M*(1+Real.log X) := by
  obtain ⟨A,hA,hcount⟩ := unconditional_right_slice_count
  refine ⟨13*A,by positivity,?_⟩
  intro X T Q hX hQ hT hscale q _ χ hq ρ hre hlo him
  obtain ⟨_,_,_,_,hH⟩ := detector_length_scales hX hQ hT hscale
  have hq₀ : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqQ : (q:ℝ) ≤ Q := by exact_mod_cast hq
  have hlog : logHeight q ρ.im ≤ logHeight Q (T+1) := by
    unfold logHeight
    rw [abs_of_nonneg (by positivity : 0 ≤ T+1)]
    apply Real.log_le_log (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hqQ (by norm_num))
      (by linarith only [him]) (by positivity) (by positivity)
  have hlocal := hcount q χ ρ.im ({ρ} : Finset ℂ) (by
    intro z hz
    rw [mem_singleton.mp hz]
    exact ⟨hre,hlo,by norm_num⟩)
  calc
    _ ≤ A * logHeight q ρ.im := by simpa only [sum_singleton] using hlocal
    _ ≤ A * (13*(1+Real.log X)) := mul_le_mul_of_nonneg_left (hlog.trans hH) hA.le
    _ = _ := by ring

/-- A weighted density bound and a logarithmic individual order bound
control the square-weighted energy on `3/4 ≤ Re ρ ≤ 1 - d`. -/
theorem square_energy_of_density_gap {ι : Type*} (S : Finset ι) (b : ι → ℝ) (m : ι → ℕ)
    {X d M A : ℝ} (hX : 2 ≤ X) (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1/4)
    (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hm : ∀ j ∈ S, (m j : ℝ) ≤ M*(1+Real.log X))
    (hstrip : ∀ j ∈ S, 3/4 ≤ b j ∧ b j ≤ 1-d)
    (hdensity : ∀ {σ : ℝ}, 3/4 ≤ σ → σ ≤ 1 →
      (∑ j ∈ S.filter (fun j => σ ≤ b j),(m j : ℝ)) ≤
        A*(1+Real.log X)^13*X^(2*(497/500:ℝ)*(1-σ))) :
    (∑ j ∈ S, (m j : ℝ)^2*X^(2*b j-1)) ≤
      (M*A*Real.exp (497/500)/(1-Real.exp (497/500-1))) *
        (1+Real.log X)^14*X^(1-2*(1-(497/500:ℝ))*d) := by
  let U := 1+Real.log X
  have hX₁ : 1 < X := by linarith only [hX]
  have hU : 0 ≤ U := by dsimp only [U]; linarith only [Real.log_nonneg hX₁.le]
  let c (j : ι) := (m j : ℝ)^2
  have hhM : 0 ≤ M*U := mul_nonneg hM hU
  have hc : ∀ j ∈ S, 0 ≤ c j := fun j _ => sq_nonneg _
  have hs : ∀ j ∈ S, 1-(1/4:ℝ) ≤ b j ∧ b j ≤ 1-d := by
    intro j hj
    obtain ⟨h₁,h₂⟩ := hstrip j hj
    constructor <;> linarith only [h₁,h₂]
  have hd : ∀ h ∈ Set.Icc d (1/4:ℝ),
      (∑ j ∈ S.filter (fun j => 1-h ≤ b j), c j) ≤
        (M*A*U^14) * X^(2*(497/500:ℝ)*h) := by
    intro h hh
    have hlo : 3/4 ≤ 1-h := by linarith only [hh.2]
    have hhi : 1-h ≤ 1 := by linarith only [hh.1,hd₀]
    have hraw := hdensity hlo hhi
    rw [show 1-(1-h)=h by ring] at hraw
    calc
      _ ≤ ∑ j ∈ S.filter (fun j => 1-h ≤ b j), (M*U)*(m j:ℝ) := by
        apply sum_le_sum
        intro j hj
        dsimp only [c]
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hm j (mem_filter.mp hj).1) (Nat.cast_nonneg _)
      _ = (M*U) * ∑ j ∈ S.filter (fun j => 1-h ≤ b j),(m j:ℝ) := by rw [mul_sum]
      _ ≤ (M*U) * (A*U^13*X^(2*(497/500:ℝ)*h)) := mul_le_mul_of_nonneg_left hraw hhM
      _ = _ := by ring
  have henergy := measured_density_sum_le S b c hX₁ hd₁
    (by norm_num : (0:ℝ) ≤ 497/500) (by norm_num : (497/500:ℝ) < 1)
    (show 0 ≤ M*A*U^14 by positivity) hc hs hd
  calc
    _ ≤ _ := henergy
    _ = _ := by
      change (M*A*U^14*Real.exp (497/500)/(1-Real.exp (497/500-1)))*X^(1-2*(1-(497/500:ℝ))*d) =
        (M*A*Real.exp (497/500)/(1-Real.exp (497/500-1)))*U^14*X^(1-2*(1-(497/500:ℝ))*d)
      ring

/-- The selected primitive nonprincipal low zeros in one bin are bounded in terms of the real-part gap. -/
theorem selected_nonprincipal_energy_le_gap : ∃ C : ℝ, 0 < C ∧
    ∀ {X T d : ℝ} (Q : ℕ), 2 ≤ X → 1 ≤ Q → 0 ≤ T →
      (Q:ℝ)^2*(T+1) ≤ 1024*X^(497/1000:ℝ) →
      0 ≤ d → d ≤ 1/4 →
      ∀ (F : (q : ℕ) → DirichletCharacter ℂ q → Finset ℂ),
      (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), q ≤ Q →
        χ.IsPrimitive → χ ≠ 1 → ∀ ρ ∈ F q χ,
          3/4 ≤ ρ.re ∧ ρ.re ≤ 1-d ∧ |ρ.im| ≤ T ∧ regularizedL χ ρ = 0) →
      (∑ q ∈ Icc 1 Q, nonprincipalFiberEnergy X q F) ≤
        C*(1+Real.log X)^14*X^(1-2*(1-(497/500:ℝ))*d) := by
  obtain ⟨M,hM,hpoint⟩ := selected_point_order_bound
  obtain ⟨A,hA,hfamily⟩ := nonprincipal_scaled_weighted_count_le
  have hden : 0 < 1-Real.exp (497/500-1:ℝ) := by
    have h := Real.exp_lt_one_iff.mpr (show (497/500:ℝ)-1 < 0 by norm_num)
    linarith only [h]
  refine ⟨M*A*Real.exp (497/500)/(1-Real.exp (497/500-1)),by positivity,?_⟩
  intro X T d Q hX hQ hT hscale hd₀ hd₁ F hF
  let S := selectedTags Q F
  let m (j : TaggedZero Q) : ℕ := analyticOrderNatAt (regularizedL j.1.2) j.2
  have hgeom (j : TaggedZero Q) (hj : j ∈ S) :
      3/4 ≤ j.2.re ∧ j.2.re ≤ 1-d ∧ |j.2.im| ≤ T ∧ regularizedL j.1.2 j.2 = 0 := by
    obtain ⟨hj₁,hj₂⟩ := mem_sigma.mp hj
    obtain ⟨hprim,hne⟩ := mem_primitiveNonprincipalFamily.mp hj₁
    exact hF (j.1.1.val+1) j.1.2 (by omega) hprim hne j.2 hj₂
  rw [← selected_tag_energy_eq X Q F]
  apply square_energy_of_density_gap S (fun j => j.2.re) m hX hd₀ hd₁ hM.le hA.le
  · intro j hj
    obtain ⟨hlo,hhi,ht,_⟩ := hgeom j hj
    exact hpoint Q hX hQ hT hscale j.1.2 (by omega) j.2 (by linarith only [hlo])
      (by linarith only [hhi,hd₀]) ht
  · intro j hj
    exact ⟨(hgeom j hj).1,(hgeom j hj).2.1⟩
  · intro σ hs₀ hs₁
    have hsub : S.filter (fun j => σ ≤ j.2.re) ⊆ familyZeroTags Q σ T := by
      intro j hj
      obtain ⟨hjS,hjσ⟩ := mem_filter.mp hj
      obtain ⟨_,hhi,him,hzero⟩ := hgeom j hjS
      exact mem_sigma.mpr ⟨(mem_sigma.mp hjS).1,
        mem_densityZeros.mpr ⟨hjσ,by linarith only [hhi,hd₀],him,hzero⟩⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)).trans
      (hfamily hX Q hQ hs₀ hs₁ hT hscale)

/-- The selected zeros of the conductor-one character in the same real strip. -/
theorem selected_principal_energy_le_gap : ∃ C : ℝ, 0 < C ∧
    ∀ {X T d : ℝ}, 2 ≤ X → 0 ≤ T → T+1 ≤ 1024*X^(497/1000:ℝ) →
      0 ≤ d → d ≤ 1/4 →
      ∀ (S : Finset ℂ), (∀ ρ ∈ S, 3/4 ≤ ρ.re ∧ ρ.re ≤ 1-d ∧ |ρ.im| ≤ T ∧
        regularizedL (1:DirichletCharacter ℂ 1) ρ = 0) →
      (∑ ρ ∈ S, (analyticOrderNatAt (regularizedL (1:DirichletCharacter ℂ 1)) ρ : ℝ)^2 *
        X^(2*ρ.re-1)) ≤ C*(1+Real.log X)^14*X^(1-2*(1-(497/500:ℝ))*d) := by
  obtain ⟨M,hM,hpoint⟩ := selected_point_order_bound
  obtain ⟨A,hA,hzeta⟩ := zeta_selected_density_scale_thirteen
  have hden : 0 < 1-Real.exp (497/500-1:ℝ) := by
    have h := Real.exp_lt_one_iff.mpr (show (497/500:ℝ)-1 < 0 by norm_num)
    linarith only [h]
  refine ⟨M*A*Real.exp (497/500)/(1-Real.exp (497/500-1)),by positivity,?_⟩
  intro X T d hX hT hscale hd₀ hd₁ S hS
  let χ : DirichletCharacter ℂ 1 := 1
  let m (ρ : ℂ) : ℕ := analyticOrderNatAt (regularizedL χ) ρ
  have hm (ρ : ℂ) (hρ : ρ ∈ S) : (m ρ:ℝ) ≤ M*(1+Real.log X) := by
    obtain ⟨hlo,hhi,ht,_⟩ := hS ρ hρ
    exact hpoint 1 hX le_rfl hT (by simpa using hscale) χ le_rfl ρ
      (by linarith only [hlo]) (by linarith only [hhi,hd₀]) ht
  apply square_energy_of_density_gap S Complex.re m hX hd₀ hd₁ hM.le hA.le hm
  · intro ρ hρ
    exact ⟨(hS ρ hρ).1,(hS ρ hρ).2.1⟩
  · intro σ hs₀ hs₁
    refine hzeta hX hT hscale hs₀ hs₁ (S.filter (fun ρ => σ ≤ ρ.re)) ?_
    intro ρ hρ
    obtain ⟨hρS,hρσ⟩ := mem_filter.mp hρ
    obtain ⟨_,_,him,hzero⟩ := hS ρ hρS
    exact ⟨hρσ,him,hzero⟩

/-- The complete selected family in one bin, with the principal fiber at level one. -/
theorem selected_primitive_energy_le_gap : ∃ C : ℝ, 0 < C ∧
    ∀ {X T d : ℝ} (Q : ℕ), 2 ≤ X → 1 ≤ Q → 0 ≤ T →
      (Q:ℝ)^2*(T+1) ≤ 1024*X^(497/1000:ℝ) →
      0 ≤ d → d ≤ 1/4 →
      ∀ (F : (q : ℕ) → DirichletCharacter ℂ q → Finset ℂ),
      (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), q ≤ Q →
        χ.IsPrimitive → ∀ ρ ∈ F q χ,
          3/4 ≤ ρ.re ∧ ρ.re ≤ 1-d ∧ |ρ.im| ≤ T ∧ regularizedL χ ρ = 0) →
      (∑ q ∈ Icc 1 Q, primitiveFiberEnergy X q F) ≤
        C*(1+Real.log X)^14*X^(1-2*(1-(497/500:ℝ))*d) := by
  obtain ⟨A,hA,hNon⟩ := selected_nonprincipal_energy_le_gap
  obtain ⟨B,hB,hPr⟩ := selected_principal_energy_le_gap
  refine ⟨A+B,add_pos hA hB,?_⟩
  intro X T d Q hX hQ hT hscale hd₀ hd₁ F hF
  let P := ∑ ρ ∈ F 1 1,
    (analyticOrderNatAt (regularizedL (1:DirichletCharacter ℂ 1)) ρ : ℝ)^2 * X^(2*ρ.re-1)
  have hQ' : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hscale' : T+1 ≤ 1024*X^(497/1000:ℝ) := by
    apply le_trans _ hscale
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hQ' : 1 ≤ (Q:ℝ)^2)
      (by positivity : 0 ≤ T+1)
  have hP : P ≤ B*(1+Real.log X)^14*X^(1-2*(1-(497/500:ℝ))*d) :=
    hPr hX hT hscale' hd₀ hd₁ (F 1 1) (hF 1 1 hQ DirichletCharacter.isPrimitive_one_level_one)
  have hN := hNon Q hX hQ hT hscale hd₀ hd₁ F (fun q _ χ hq hp _ => hF q χ hq hp)
  calc
    _ = (∑ q ∈ Icc 1 Q, nonprincipalFiberEnergy X q F) + P := by
      trans ∑ q ∈ Icc 1 Q, (nonprincipalFiberEnergy X q F + if q = 1 then P else 0)
      · apply sum_congr rfl
        intro q hq
        exact primitive_fiber_energy_eq X (mem_Icc.mp hq).1 F
      · rw [sum_add_distrib]
        simp [mem_Icc, hQ]
    _ ≤ A*(1+Real.log X)^14*X^(1-2*(1-(497/500:ℝ))*d) + B*(1+Real.log X)^14*X^(1-2*(1-(497/500:ℝ))*d) :=
      (add_le_add) hN hP
    _ = _ := by ring

/-- The gap that separates the part controlled by the density bound from zeros closer to one. -/
def farGap (X : ℝ) : ℝ := 3000*Real.log (Real.log X)/Real.log X

theorem farGap_nonneg {X : ℝ} (hL : 1 ≤ Real.log X) : 0 ≤ farGap X := by
  unfold farGap
  exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hL)) (by linarith only [hL])

theorem farGap_eventually : ∀ᶠ X : ℝ in atTop, 0 ≤ farGap X ∧ farGap X ≤ 1/4 := by
  have hsmall := Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < 1/12000 by norm_num)
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually hsmall] with X hL hsmallX
  have hL₀ : 0 < Real.log X := by linarith only [hL]
  have hlog : Real.log (Real.log X) ≤ (1/12000)*Real.log X := by
    simpa only [Real.norm_eq_abs, id_eq, abs_of_nonneg hL₀.le,
      abs_of_nonneg (Real.log_nonneg hL)] using hsmallX
  refine ⟨farGap_nonneg hL,?_⟩
  exact (div_le_iff₀ hL₀).mpr (by linarith only [hlog])

/-- The logarithmic gap beats at least twenty-two powers of the logarithmic scale. -/
theorem far_gap_energy_factor {X : ℝ} (hX : 1 < X) (hL : 1 ≤ Real.log X) :
    (1+Real.log X)^14*X^(1-2*(1-(497/500:ℝ))*farGap X) ≤
      (2:ℝ)^36*X/(1+Real.log X)^22 := by
  let L := Real.log X
  let U := 1+L
  have hL₀ : 0 < L := by linarith only [hL]
  have hU₀ : 0 < U := by dsimp only [U]; linarith only [hL₀]
  have hU : U ≤ 2*L := by dsimp only [U]; linarith only [hL]
  have hXp : 0 < X := by linarith only [hX]
  have hf : X^(1-2*(1-(497/500:ℝ))*farGap X) = X*(L^36)⁻¹ := by
    rw [farGap,logarithmic_gap_factor hX]
    have he : (-2*(1-(497/500:ℝ))*3000) = -((36:ℕ):ℝ) := by norm_num
    rw [he,Real.rpow_neg hL₀.le,Real.rpow_natCast]
  rw [hf]
  have hratio : (L^36)⁻¹ ≤ (2:ℝ)^36/U^36 := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (pow_pos hL₀ _) (pow_pos hU₀ _)).mpr
    simpa only [one_mul,mul_pow] using pow_le_pow_left₀ hU₀.le hU 36
  change U^14*(X*(L^36)⁻¹) ≤ (2:ℝ)^36*X/U^22
  calc
    _ ≤ U^14*(X*((2:ℝ)^36/U^36)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hratio hXp.le) (by positivity)
    _ = _ := by
      rw [show U^36 = U^14*U^22 by ring]
      field_simp [hU₀.ne']

/-- On an occupied power bin, the far portion of the selected low zeros is
bounded by `X / (1 + log X)^22`. -/
theorem far_selected_primitive_energy_le : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ X : ℝ in atTop, ∀ (Q : ℕ) {T : ℝ}, 1 ≤ Q → 0 ≤ T →
      (Q:ℝ)^2*(T+1) ≤ 1024*X^(497/1000:ℝ) →
      ∀ (F : (q : ℕ) → DirichletCharacter ℂ q → Finset ℂ),
      (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), q ≤ Q →
        χ.IsPrimitive → ∀ ρ ∈ F q χ,
          3/4 ≤ ρ.re ∧ ρ.re ≤ 1-farGap X ∧ |ρ.im| ≤ T ∧ regularizedL χ ρ = 0) →
      (∑ q ∈ Icc 1 Q, primitiveFiberEnergy X q F) ≤
        C*X/(1+Real.log X)^22 := by
  obtain ⟨C,hC,henergy⟩ := selected_primitive_energy_le_gap
  refine ⟨C*(2:ℝ)^36,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    farGap_eventually] with X hX hL hd
  intro Q T hQ hT hscale F hF
  have hX₁ : 1 < X := by linarith only [hX]
  have hb := far_gap_energy_factor hX₁ hL
  calc
    _ ≤ C*(1+Real.log X)^14*X^(1-2*(1-(497/500:ℝ))*farGap X) :=
      henergy Q hX hQ hT hscale hd.1 hd.2 F hF
    _ ≤ C*((2:ℝ)^36*X/(1+Real.log X)^22) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hb hC.le
    _ = _ := by ring

end
end GoldbachLowZeroGapEnergy

end

section

namespace GoldbachConductorEnergy

open Finset GoldbachPowerBins GoldbachLowZeroEnergy
open scoped Classical

private theorem primitive_energy_nonneg {X : ℝ} (hX : 0 ≤ X) (q : ℕ)
    (F : (r : ℕ) → DirichletCharacter ℂ r → Finset ℂ) :
    0 ≤ primitiveFiberEnergy X q F := by
  unfold primitiveFiberEnergy
  split
  · exact le_rfl
  · exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hX _)))

set_option maxHeartbeats 1000000 in
/-- Apply a uniform bound on each occupied conductor bin and sum over the fixed bin range. -/
theorem primitive_energy_all_bins_le {X cap : ℝ} (hX : 16 ≤ X) (P : ℕ)
    (hP : (P:ℝ) ≤ 4*X^(41/200:ℝ)) (hcap : 0 ≤ cap)
    (Z : (ℕ → ℝ) → (q : ℕ) → DirichletCharacter ℂ q → Finset ℂ)
    (hZ : ∀ (H K : ℕ → ℝ) (q : ℕ), H q = K q → ∀ χ, Z H q χ = Z K q χ)
    (henergy : ∀ (Q : ℕ) {T : ℝ}, 1 ≤ Q → (Q:ℝ) ≤ X → 0 ≤ T →
      (Q:ℝ)^2*(T+1) ≤ 1024*X^(497/1000:ℝ) →
      ∀ (H : ℕ → ℝ), (∀ q ∈ Icc 1 Q, H q ≤ T) →
      (∑ q ∈ Icc 1 Q, primitiveFiberEnergy X q (Z H)) ≤ cap) :
    (∑ q ∈ Icc 1 P, primitiveFiberEnergy X q
      (Z (fun r => 32*X^(17/200:ℝ)*(P:ℝ)/(r:ℝ)))) ≤ 1001*cap := by
  have hX1 : 1 < X := by linarith only [hX]
  have hXp := zero_lt_one.trans hX1
  have hPX : (P:ℝ) ≤ X := by
    have h4 : 4 ≤ Real.sqrt X := by
      have hh := Real.sqrt_le_sqrt hX
      rwa [show (16:ℝ)=4^2 by norm_num,Real.sqrt_sq (by norm_num : (0:ℝ)≤4)] at hh
    have hpow : X^(41/200:ℝ) ≤ Real.sqrt X := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
    calc
      _ ≤ 4*X^(41/200:ℝ) := hP
      _ ≤ 4*Real.sqrt X := mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ (Real.sqrt X)^2 := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg _)
      _ = _ := Real.sq_sqrt hXp.le
  let H : ℕ → ℝ := fun q => 32*X^(17/200:ℝ)*(P:ℝ)/(q:ℝ)
  let F (q : ℕ) := primitiveFiberEnergy X q (Z H)
  have hpart := sum_partition (Icc 1 P) (fun q : ℕ => (q:ℝ)) F hX1 hPX
    (fun q hq => ⟨by exact_mod_cast (mem_Icc.mp hq).1,by exact_mod_cast (mem_Icc.mp hq).2⟩)
  have hbin (k : ℕ) :
      (∑ q ∈ (Icc 1 P).filter (fun q : ℕ => binIndex X (q:ℝ) = k), F q) ≤ cap := by
    let S := (Icc 1 P).filter (fun q : ℕ => binIndex X (q:ℝ) = k)
    change (∑ q ∈ S, F q) ≤ cap
    by_cases hs : S.Nonempty
    · obtain ⟨r,hr⟩ := hs
      have hrbox := mem_Icc.mp (mem_filter.mp hr).1
      have hkr := (mem_filter.mp hr).2
      have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hrbox.1
      have hrP : (r:ℝ) ≤ P := by exact_mod_cast hrbox.2
      let Q := ⌊binUpper X k⌋₊
      let T := binHeight X (P:ℝ) k
      have hsc : 1 ≤ Q ∧ 1 ≤ T ∧ (Q:ℝ)^2*(T+1) ≤ 1024*X^(497/1000:ℝ) ∧
          T+1 ≤ 1024*X := by
        simpa only [hkr] using occupied_bin_floor_scale hX1 hr1 hrP hPX hP
      have hQX : (Q:ℝ) ≤ X := by
        simpa only [hkr] using occupied_bin_floor_le_X hX hr1 hrP hPX hP
      let H' (q : ℕ) := min (H q) T
      have hH' : ∀ q ∈ Icc 1 Q, H' q ≤ T := fun _ _ => min_le_right _ _
      have hsub : S ⊆ Icc 1 Q := by
        intro q hq
        have hqbox := mem_Icc.mp (mem_filter.mp hq).1
        have hkey := (mem_filter.mp hq).2
        have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hqbox.1
        have hqP : (q:ℝ) ≤ P := by exact_mod_cast hqbox.2
        have hqbin := (bin_geometry hX1 hq1 (hqP.trans hPX)).2.1
        rw [hkey] at hqbin
        exact mem_Icc.mpr ⟨hqbox.1,level_le_bin_floor hqbox.1 hqbin⟩
      have hHbin (q : ℕ) (hq : q ∈ S) : H q ≤ T := by
        have hqbox := mem_Icc.mp (mem_filter.mp hq).1
        have hkey := (mem_filter.mp hq).2
        have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hqbox.1
        have hqP : (q:ℝ) ≤ P := by exact_mod_cast hqbox.2
        have hhelper := conductorHeight_le_binHeight hX1 hq1 hqP hPX
        rw [hkey] at hhelper
        simpa only [H,conductorHeight,show (85/1000:ℝ)=17/200 by norm_num] using hhelper
      have hF (q : ℕ) (hq : q ∈ S) :
          F q = primitiveFiberEnergy X q (Z H') := by
        have hq₀ : q ≠ 0 := by have := (mem_Icc.mp (hsub hq)).1; omega
        simp only [F, primitiveFiberEnergy, dite_eq_right hq₀]
        apply sum_congr rfl
        intro χ _
        rw [hZ H H' q (min_eq_left (hHbin q hq)).symm χ]
      calc
        _ = ∑ q ∈ S, primitiveFiberEnergy X q (Z H') := sum_congr rfl hF
        _ ≤ ∑ q ∈ Icc 1 Q, primitiveFiberEnergy X q (Z H') :=
          sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => primitive_energy_nonneg hXp.le q _)
        _ ≤ _ := henergy Q hsc.1 hQX (zero_le_one.trans hsc.2.1) hsc.2.2.1 H' hH'
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs,sum_empty]
      exact hcap
  change (∑ q ∈ Icc 1 P,F q) ≤ _
  rw [← hpart]
  calc
    _ ≤ ∑ _k ∈ range 1001,cap := sum_le_sum (fun k _ => hbin k)
    _ = _ := by simp [nsmul_eq_mul]


end GoldbachConductorEnergy

end

section

namespace GoldbachFarZeroEnergy

open Finset Filter Goldbach GoldbachTwistedMellin GoldbachHybridSieve GoldbachLowZeroEnergy
  GoldbachLowerStrip GoldbachLowZeroGapEnergy GoldbachConductorEnergy GoldbachSpectralGeometry
open scoped Classical Topology

/-- The selected low-ordinate zeros with real part at most `1 - farGap X`. -/
noncomputable def selectedFarExceptionalZeros (X : ℝ) (H : ℕ → ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) : Finset ℂ :=
  if hq : q = 0 then ∅ else
    letI : NeZero q := ⟨hq⟩
    (exceptionalZeros χ (heightCut X)).filter (fun ρ => |ρ.im| < H q ∧ ρ.re ≤ 1-farGap X)

noncomputable def selectedFarHighRealZeros (X : ℝ) (H : ℕ → ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) : Finset ℂ :=
  (selectedFarExceptionalZeros X H q χ).filter (fun ρ => 3/4 ≤ ρ.re)

theorem selectedFarExceptionalZeros_mem {X : ℝ} {H : ℕ → ℝ} {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} {ρ : ℂ} :
    ρ ∈ selectedFarExceptionalZeros X H q χ ↔
      ρ ∈ exceptionalZeros χ (heightCut X) ∧ |ρ.im| < H q ∧ ρ.re ≤ 1-farGap X := by
  rw [selectedFarExceptionalZeros,dite_eq_right (NeZero.ne q),mem_filter]

private theorem selected_far_low_real_eq {q : ℕ} [NeZero q] (X : ℝ) (H : ℕ → ℝ)
    (hd : farGap X ≤ 1/4)
    (χ : DirichletCharacter ℂ q) :
    (selectedFarExceptionalZeros X H q χ).filter (fun ρ => ρ.re < 3/4) =
      (exceptionalZeros χ (heightCut X)).filter (fun ρ => |ρ.im| < H q ∧ ρ.re < 3/4) := by
  ext ρ
  simp only [mem_filter,selectedFarExceptionalZeros_mem]
  constructor
  · rintro ⟨⟨hz,hh,_⟩,hlo⟩
    exact ⟨hz,hh,hlo⟩
  · rintro ⟨hz,hh,hlo⟩
    exact ⟨⟨hz,hh,by linarith only [hlo,hd]⟩,hlo⟩

/-- The real-part boundary term belongs to the upper strip. -/
theorem selected_far_primitive_fiber_split (X : ℝ) (H : ℕ → ℝ) {q : ℕ} (hq : 1 ≤ q)
    (hd : farGap X ≤ 1/4) :
    primitiveFiberEnergy X q (selectedFarExceptionalZeros X H) =
      (∑ χ ∈ primitiveCharacters q, lowerStripEnergyAt X (H q) q χ) +
        primitiveFiberEnergy X q (selectedFarHighRealZeros X H) := by
  let _ : NeZero q := ⟨(Nat.zero_lt_one.trans_le hq).ne'⟩
  simp only [primitiveFiberEnergy,dite_eq_right (NeZero.ne q),lowerStripEnergyAt_eq]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro χ _
  let f (ρ : ℂ) := (analyticOrderNatAt (regularizedL χ) ρ : ℝ)^2 * X^(2*ρ.re-1)
  have he := sum_filter_add_sum_filter_not (selectedFarExceptionalZeros X H q χ) (fun ρ => ρ.re < 3/4) f
  rw [selected_far_low_real_eq X H hd] at he
  simpa only [f,not_lt,selectedFarHighRealZeros] using he.symm

/-- Below real part `3/4`, the fixed power saving absorbs twenty-four logarithms. -/
private theorem lower_energy_factor : ∃ D : ℝ, 0 < D ∧ ∀ X : ℝ, 1 ≤ X →
    (1+Real.log X)^2*X^(997/1000:ℝ) ≤ D*X/(1+Real.log X)^22 := by
  obtain ⟨D,hD,hlog⟩ := log_power_le_small_power 24 (δ := 3/1000) (by norm_num)
  refine ⟨D,hD,?_⟩
  intro X hX
  have hX₀ := zero_lt_one.trans_le hX
  let U := 1+Real.log X
  have hU : 0 < U := by dsimp only [U]; linarith only [Real.log_nonneg hX]
  change U^2*X^(997/1000:ℝ) ≤ D*X/U^22
  apply (le_div_iff₀ (pow_pos hU _)).mpr
  calc
    _ = U^24*X^(997/1000:ℝ) := by ring
    _ ≤ (D*X^(3/1000:ℝ))*X^(997/1000:ℝ) :=
      mul_le_mul_of_nonneg_right (hlog X hX) (Real.rpow_nonneg hX₀.le _)
    _ = _ := by
      rw [mul_assoc,← Real.rpow_add hX₀,show (3/1000:ℝ)+997/1000=1 by norm_num,Real.rpow_one]

/-- The full selected far energy in one conductor bin includes the lower real strip. -/
theorem selected_far_exceptional_primitive_energy_le : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ X : ℝ in atTop, ∀ (Q : ℕ) {T : ℝ}, 1 ≤ Q → (Q:ℝ) ≤ X → 0 ≤ T →
      (Q:ℝ)^2*(T+1) ≤ 1024*X^(497/1000:ℝ) →
      ∀ (H : ℕ → ℝ), (∀ q ∈ Icc 1 Q, H q ≤ T) →
      (∑ q ∈ Icc 1 Q, primitiveFiberEnergy X q (selectedFarExceptionalZeros X H)) ≤
        C*X/(1+Real.log X)^22 := by
  obtain ⟨A,hA,hLow⟩ := lower_strip_primitive_energy_le
  obtain ⟨B,hB,hHigh⟩ := far_selected_primitive_energy_le
  obtain ⟨D,hD,hfactor⟩ := lower_energy_factor
  refine ⟨A*D+B,by positivity,?_⟩
  filter_upwards [hHigh,farGap_eventually,eventually_ge_atTop (2:ℝ)] with X hHighX hd hX
  intro Q T hQ hQX hT hscale H hH
  have hX₁ : 1 ≤ X := by linarith only [hX]
  have hL := hLow hX hT Q hQ hQX hscale H hH
  have hL' : (∑ q ∈ Icc 1 Q, ∑ χ ∈ primitiveCharacters q, lowerStripEnergyAt X (H q) q χ) ≤
      (A*D)*X/(1+Real.log X)^22 := by
    apply hL.trans
    calc
      _ = A*((1+Real.log X)^2*X^(997/1000:ℝ)) := by ring
      _ ≤ A*(D*X/(1+Real.log X)^22) := mul_le_mul_of_nonneg_left (hfactor X hX₁) hA.le
      _ = _ := by ring
  have hgeometry (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hqQ : q ≤ Q)
      (_ : χ.IsPrimitive) (ρ : ℂ) (hρ : ρ ∈ selectedFarHighRealZeros X H q χ) :
      3/4 ≤ ρ.re ∧ ρ.re ≤ 1-farGap X ∧ |ρ.im| ≤ T ∧ regularizedL χ ρ = 0 := by
    obtain ⟨hsel,hhi⟩ := mem_filter.mp hρ
    obtain ⟨hz,hh,hβ⟩ := selectedFarExceptionalZeros_mem.mp hsel
    have hmem : q ∈ Icc 1 Q := mem_Icc.mpr ⟨NeZero.pos q,hqQ⟩
    exact ⟨hhi,hβ,hh.le.trans (hH q hmem),((mem_exceptionalZeros χ (heightCut X) ρ).mp hz).2.2⟩
  have hUpp := hHighX Q hQ hT hscale (selectedFarHighRealZeros X H) hgeometry
  calc
    _ = (∑ q ∈ Icc 1 Q, ∑ χ ∈ primitiveCharacters q, lowerStripEnergyAt X (H q) q χ) +
        (∑ q ∈ Icc 1 Q, primitiveFiberEnergy X q (selectedFarHighRealZeros X H)) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl (fun q hq => selected_far_primitive_fiber_split X H (mem_Icc.mp hq).1 hd.2)
    _ ≤ (A*D)*X/(1+Real.log X)^22 + B*X/(1+Real.log X)^22 := add_le_add hL' hUpp
    _ = _ := by ring

/-- A fixed number of power bins covers all selected far zeros through the conductor cutoff. -/
theorem selected_far_energy_all_conductors_le : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ X : ℝ in atTop, ∀ (P : ℕ), (P:ℝ) ≤ 4*X^(41/200:ℝ) →
      (∑ q ∈ Icc 1 P, primitiveFiberEnergy X q
        (selectedFarExceptionalZeros X (fun r => 32*X^(17/200:ℝ)*(P:ℝ)/(r:ℝ)))) ≤
        C*X/(1+Real.log X)^22 := by
  obtain ⟨C,hC,hbin⟩ := selected_far_exceptional_primitive_energy_le
  refine ⟨1001*C,by positivity,?_⟩
  filter_upwards [hbin,eventually_ge_atTop (16:ℝ)] with X hbinX hX
  intro P hP
  have hX₁ : 1 ≤ X := by linarith only [hX]
  have hU : 0 ≤ 1+Real.log X := by linarith only [Real.log_nonneg hX₁]
  have hcap : 0 ≤ C*X/(1+Real.log X)^22 := by positivity
  have hZ (H K : ℕ → ℝ) (q : ℕ) (h : H q = K q) (χ : DirichletCharacter ℂ q) :
      selectedFarExceptionalZeros X H q χ = selectedFarExceptionalZeros X K q χ := by
    by_cases hq : q = 0 <;> simp [selectedFarExceptionalZeros,hq,h]
  exact (primitive_energy_all_bins_le hX P hP hcap (selectedFarExceptionalZeros X) hZ hbinX).trans_eq
    (by ring)

end GoldbachFarZeroEnergy

end

section

namespace GoldbachWeightedMajorResidual

open Finset MeasureTheory Goldbach GoldbachTwistedMellin
open GoldbachSmoothWindow GoldbachNarrowMajor GoldbachZeroStrip GoldbachConductorZeros
open GoldbachWeightedException (cutoff)
open GoldbachConductorRegroup

open scoped Classical

noncomputable section

def zeroTermOn {q : ℕ} [NeZero q] (X : ℕ) (χ : DirichletCharacter ℂ q)
    (P : ℕ → ℂ → Prop) (β : ℝ) : ℂ :=
  ∑ z ∈ (exceptionalZeros χ (heightCut (X : ℝ))).filter (P χ.conductor),
    (analyticOrderNatAt (regularizedL χ) z : ℂ) *
      weightedTransform X (2*X-1) (2*Real.pi*β)
        (fun k => (scaledWeight (X:ℝ) (k:ℝ) : ℂ)) z

def arcCorrectionOn (X q a : ℕ) (P : ℕ → ℂ → Prop) (β : ℝ) : ℂ :=
  if hq : q ≠ 0 then
    let _ : NeZero q := ⟨hq⟩
    ∑ χ : DirichletCharacter ℂ q, additiveWeight (a : ZMod q) χ * zeroTermOn X χ P β
  else 0

theorem zeroTermOn_add_complement {q : ℕ} [NeZero q] (X : ℕ) (χ : DirichletCharacter ℂ q)
    (P : ℕ → ℂ → Prop) (β : ℝ) :
    zeroTermOn X χ P β + zeroTermOn X χ (fun r z => ¬P r z) β = zeroTerm X χ β := by
  unfold zeroTermOn zeroTerm
  simpa only [filter_congr_decidable] using
    sum_filter_add_sum_filter_not (exceptionalZeros χ (heightCut (X:ℝ))) (P χ.conductor)
      (fun z => (analyticOrderNatAt (regularizedL χ) z : ℂ) *
        weightedTransform X (2*X-1) (2*Real.pi*β) (fun k => (scaledWeight (X:ℝ) (k:ℝ) : ℂ)) z)

theorem arcCorrection_sub_on (X q a : ℕ) (P : ℕ → ℂ → Prop) (β : ℝ) :
    arcCorrection X q a β - arcCorrectionOn X q a P β =
      arcCorrectionOn X q a (fun r z => ¬P r z) β := by
  by_cases hq : q ≠ 0
  · let _ : NeZero q := ⟨hq⟩
    apply sub_eq_iff_eq_add.mpr
    simp only [arcCorrection, arcCorrectionOn, correction, dite_eq_left hq, ← sum_add_distrib]
    apply sum_congr rfl
    intro χ _
    rw [← mul_add, show zeroTermOn X χ (fun r z => ¬P r z) β + zeroTermOn X χ P β =
      zeroTerm X χ β from (add_comm _ _).trans (zeroTermOn_add_complement X χ P β)]
  · simp [arcCorrection, arcCorrectionOn, hq]

theorem filtered_exceptionalZeros_eq_primitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (P : ℕ → ℂ → Prop) (H : ℝ) :
    (exceptionalZeros χ H).filter (P χ.conductor) =
      (exceptionalZeros χ.primitiveCharacter H).filter (P χ.primitiveCharacter.conductor) := by
  have hc : χ.primitiveCharacter.conductor = χ.conductor :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  calc
    _ = (exceptionalZeros χ.primitiveCharacter H).filter (P χ.conductor) :=
      congrArg (fun S : Finset ℂ => S.filter (P χ.conductor)) (exceptionalZeros_primitive χ H)
    _ = _ := congrArg (fun r : ℕ => (exceptionalZeros χ.primitiveCharacter H).filter (P r)) hc.symm

theorem zeroTermOn_eq_primitive {q : ℕ} [NeZero q] (X : ℕ) (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (P : ℕ → ℂ → Prop) (β : ℝ) :
    zeroTermOn X χ P β = zeroTermOn X χ.primitiveCharacter P β := by
  unfold zeroTermOn
  apply sum_congr (filtered_exceptionalZeros_eq_primitive χ P (heightCut X))
  intro z hz
  have hr := ((mem_exceptionalZeros χ.primitiveCharacter (heightCut X) z).mp
    (mem_filter.mp hz).1).1
  have hpos := (show (0:ℝ) < 1/2 by norm_num).trans hr
  exact congrArg (fun (k : ℕ) => (k : ℂ) * _) (regularized_primitive_order χ hpos)

theorem zeroTermOn_eq_angular {q X : ℕ} [NeZero q] (hX : 2 ≤ X)
    (χ : DirichletCharacter ℂ q) (P : ℕ → ℂ → Prop) (β : ℝ) :
    zeroTermOn X χ P β =
      ∑ z ∈ (exceptionalZeros χ (heightCut (X : ℝ))).filter (P χ.conductor),
        (analyticOrderNatAt (regularizedL χ) z : ℂ) *
          weightedTaperTransform X (2 * X - 1) (fun k => scaledWeight X k) (2*Real.pi*β) z := by
  unfold zeroTermOn
  exact sum_congr rfl (fun z _ => congrArg (fun n => _ * n) (weightedTransform_eq_weightedTaper hX _ z))

theorem continuous_zeroTermOn {q X : ℕ} [NeZero q] (hX : 2 ≤ X)
    (χ : DirichletCharacter ℂ q) (P : ℕ → ℂ → Prop) :
    Continuous (zeroTermOn X χ P) := by
  simp_rw [show zeroTermOn X χ P = _ from funext (zeroTermOn_eq_angular hX χ P)]
  apply continuous_finsetSum
  intro z _
  have hk := GoldbachCorrectionBands.continuous_zero_taper
    (a := X) (b := 2*X-1) (by omega) (by omega) (fun k => scaledWeight (X:ℝ) k) z
  exact (hk.comp (by fun_prop : Continuous (fun β : ℝ => 2*Real.pi*β))).const_mul _

theorem continuous_arcCorrectionOn {X : ℕ} (hX : 2 ≤ X) (q a : ℕ) (P : ℕ → ℂ → Prop) :
    Continuous (arcCorrectionOn X q a P) := by
  by_cases hq : q ≠ 0
  · let _ : NeZero q := ⟨hq⟩
    have he : arcCorrectionOn X q a P =
        fun β => ∑ χ : DirichletCharacter ℂ q, additiveWeight (a : ZMod q) χ * zeroTermOn X χ P β := by
      funext β
      simp only [arcCorrectionOn, dite_eq_left hq]
    rw [he]
    apply continuous_finsetSum
    intro χ _
    exact (continuous_zeroTermOn hX χ P).const_mul _
  · have he : arcCorrectionOn X q a P = 0 := by
      funext β
      simp [arcCorrectionOn, hq]
    rw [he]
    exact continuous_const

end
end GoldbachWeightedMajorResidual

end

section

namespace GoldbachWeightedMajorResidual

open Finset MeasureTheory Goldbach GoldbachTwistedMellin
open GoldbachSmoothWindow GoldbachZeroStrip GoldbachConductorRegroup
open GoldbachWeightedException (cutoff)
open scoped Pointwise Classical

noncomputable section

def zeroProfileOn (keep : ℕ → ℂ → Prop) (X q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ → ℂ :=
  if hq : q ≠ 0 then fun β => @zeroTermOn q ⟨hq⟩ X χ keep β else 0

def angularZeroTermOn {q : ℕ} [NeZero q] (keep : ℕ → ℂ → Prop)
    (X : ℕ) (χ : DirichletCharacter ℂ q) (β : ℝ) : ℂ :=
  ∑ z ∈ (exceptionalZeros χ (heightCut (X : ℝ))).filter (keep χ.conductor),
    (analyticOrderNatAt (regularizedL χ) z : ℂ) *
      weightedTaperTransform X (2 * X - 1) (fun k => scaledWeight (X : ℝ) (k : ℝ)) β z

theorem zeroTermOn_profile_primitive {q : ℕ} [NeZero q] (X : ℕ) (χ : DirichletCharacter ℂ q)
    (keep : ℕ → ℂ → Prop) (β : ℝ) :
    zeroTermOn X χ keep β = zeroProfileOn keep X χ.conductor χ.primitiveCharacter β := by
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  simp only [zeroProfileOn, dite_eq_left χ.conductor_ne_zero]
  exact zeroTermOn_eq_primitive X χ keep β

theorem continuous_zeroProfileOn {X : ℕ} (hX : 2 ≤ X) (keep : ℕ → ℂ → Prop)
    (q : ℕ) (χ : DirichletCharacter ℂ q) : Continuous (zeroProfileOn keep X q χ) := by
  unfold zeroProfileOn
  split
  · rename_i hq
    let _ : NeZero q := ⟨hq⟩
    exact continuous_zeroTermOn hX χ keep
  · exact continuous_const

private theorem sum_over_reduced_on {q : ℕ} [NeZero q] (f : ℕ → ℝ) :
    (∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), f a) =
      ∑ a : (ZMod q)ˣ, f (a : ZMod q).val := by
  symm
  apply Finset.sum_bij (fun (u : (ZMod q)ˣ) _ => (u : ZMod q).val)
  · intro u _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (ZMod.val_lt (u : ZMod q)), ZMod.val_coe_unit_coprime u⟩
  · intro u _ v _ huv
    apply Units.ext
    simpa only [ZMod.natCast_zmod_val] using congrArg (fun x : ℕ => (x : ZMod q)) huv
  · intro r hr
    obtain ⟨hrange, hcop⟩ := Finset.mem_filter.mp hr
    let hu : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).mpr hcop
    exact ⟨hu.unit, Finset.mem_univ _, by rw [IsUnit.unit_spec, ZMod.val_natCast_of_lt (Finset.mem_range.mp hrange)]⟩
  · intro u _
    rfl

private theorem correction_on_band_fiber {X q : ℕ} [NeZero q] (hX : 2 ≤ X) (keep : ℕ → ℂ → Prop) :
    (∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
      bandEnergy (arcCorrectionOn X q a keep) (arcRadius X q)) ≤
      ∑ χ : DirichletCharacter ℂ q, (χ.conductor : ℝ) / q.totient *
        bandEnergy (zeroTermOn X χ keep) (arcRadius X q) := by
  classical
  rw [sum_over_reduced_on]
  simp only [bandEnergy, ← integral_const_mul]
  rw [← integral_finsetSum, ← integral_finsetSum]
  · apply integral_mono
    · exact integrable_finsetSum _ (fun a _ =>
        ((continuous_arcCorrectionOn hX q (a : ZMod q).val keep).norm.pow 2).integrableOn_Icc)
    · exact integrable_finsetSum _ (fun χ _ =>
        (((continuous_zeroTermOn hX χ keep).norm.pow 2).const_mul _).integrableOn_Icc)
    · intro β
      have he (a : (ZMod q)ˣ) : arcCorrectionOn X q (a : ZMod q).val keep β =
          ∑ χ : DirichletCharacter ℂ q, zeroTermOn X χ keep β * additiveWeight (a : ZMod q) χ := by
        simp only [arcCorrectionOn, dite_eq_left (NeZero.ne q), ZMod.natCast_zmod_val, mul_comm]
      simp_rw [he]
      exact GoldbachMajorEnergy.reduced_fraction_energy_le (fun χ => zeroTermOn X χ keep β)
  · intro χ _
    exact (((continuous_zeroTermOn hX χ keep).norm.pow 2).const_mul _).integrableOn_Icc
  · intro a _
    exact ((continuous_arcCorrectionOn hX q (a : ZMod q).val keep).norm.pow 2).integrableOn_Icc

/-- A character's spectral term is unchanged by the Euler factors in an imprimitive lift. -/
theorem correction_on_energy_le_primitive {X : ℕ} (hX : 2 ≤ X) (keep : ℕ → ℂ → Prop) :
    (∑ q ∈ Finset.Icc 1 (cutoff X), ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
      ∫ β in Set.Icc (-arcRadius X q) (arcRadius X q), ‖arcCorrectionOn X q a keep β‖ ^ 2) ≤
      ((4 * Real.log ((cutoff X + 2 : ℕ) : ℝ)) * reciprocalSum (cutoff X)) *
        (∑ r ∈ Finset.Icc 1 (cutoff X),
          ∑ ψ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.IsPrimitive),
            bandEnergy (zeroProfileOn keep X r ψ) (arcRadius X r)) := by
  classical
  have hx : (0 : ℝ) < ((4 * X : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 4 * X by omega)
  refine le_trans ?_ (primitive_major_energy_le (cutoff X) _ hx (zeroProfileOn keep X)
    (continuous_zeroProfileOn hX keep))
  apply sum_le_sum
  intro q hq
  let : NeZero q := ⟨(show 0 < q from (Finset.mem_Icc.mp hq).1).ne'⟩
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ q, (χ.conductor : ℝ) / q.totient *
        bandEnergy (zeroTermOn X χ keep) (arcRadius X q) := correction_on_band_fiber hX keep
    _ = _ := by
      apply sum_congr rfl
      intro χ _
      have he : zeroTermOn X χ keep = zeroProfileOn keep X χ.conductor χ.primitiveCharacter :=
        funext fun β => zeroTermOn_profile_primitive X χ keep β
      rw [he]
      rfl


private theorem smul_symmetric_interval_on {c R : ℝ} (hc : 0 < c) :
    c • Set.Icc (-R) R = Set.Icc (-(c * R)) (c * R) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', Set.mem_Icc, Set.mem_Icc]
  simp only [smul_eq_mul, ← div_eq_inv_mul]
  rw [le_div_iff₀ hc, div_le_iff₀ hc]
  constructor <;> rintro ⟨hl, hu⟩ <;> exact ⟨by linarith only [hl], by linarith only [hu]⟩

theorem bandEnergy_zeroProfileOn_le_angular {X q : ℕ} [NeZero q] (hX : 2 ≤ X)
    (χ : DirichletCharacter ℂ q) (keep : ℕ → ℂ → Prop) (R : ℝ) :
    bandEnergy (zeroProfileOn keep X q χ) R ≤ bandEnergy (angularZeroTermOn keep X χ) (2 * Real.pi * R) := by
  let c := 2 * Real.pi
  have hc : 0 < c := mul_pos (by norm_num) Real.pi_pos
  have hinv : c⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (show 1 ≤ c by dsimp [c]; linarith only [Real.pi_gt_three])
  have he : zeroProfileOn keep X q χ = fun β => angularZeroTermOn keep X χ (c * β) := by
    funext β
    rw [zeroProfileOn, dite_eq_left (NeZero.ne q)]
    exact zeroTermOn_eq_angular hX χ keep β
  rw [he]
  change (∫ β in Set.Icc (-R) R, ‖angularZeroTermOn keep X χ (c * β)‖ ^ 2) ≤ _
  have hz := Measure.setIntegral_comp_smul_of_pos (volume : Measure ℝ)
    (fun β : ℝ => ‖angularZeroTermOn keep X χ β‖ ^ 2) (Set.Icc (-R) R) hc
  simp only [smul_eq_mul, Module.finrank_self, pow_one, smul_symmetric_interval_on hc] at hz
  rw [hz]
  exact mul_le_of_le_one_left (GoldbachConductorRegroup.bandEnergy_nonneg
    (angularZeroTermOn keep X χ) (c * R)) hinv

end
end GoldbachWeightedMajorResidual

end

section

namespace GoldbachWeightedMajorResidual

open Finset MeasureTheory Goldbach GoldbachTwistedMellin
open GoldbachWeightedException (cutoff)
open GoldbachConductorRegroup GoldbachCorrectionBands GoldbachCorrectionCounts GoldbachSpectralGeometry
open scoped Classical

noncomputable section

def primitiveCorrectionEnergyOn (keep : ℕ → ℂ → Prop) (X : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (cutoff X),
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
      bandEnergy (zeroProfileOn keep X q χ) (arcRadius X q)

end
end GoldbachWeightedMajorResidual

end

section

namespace GoldbachWeightedMajorResidual

open Finset Filter MeasureTheory Goldbach GoldbachTwistedMellin
open GoldbachWeightedException (cutoff)
open GoldbachConductorRegroup GoldbachSpectralGeometry GoldbachFarZeroEnergy
open GoldbachLowZeroEnergy GoldbachLowZeroGapEnergy
open scoped Topology Classical

noncomputable section

def correctionEnergyOn (keep : ℕ → ℂ → Prop) (X : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (cutoff X), ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
    ∫ β in Set.Icc (-arcRadius X q) (arcRadius X q), ‖arcCorrectionOn X q a keep β‖ ^ 2

end
end GoldbachWeightedMajorResidual

end


section

namespace GoldbachSmoothMellinPower

open MeasureTheory Set Complex GoldbachTwistedMellin GoldbachSmoothMellin GoldbachSmoothWindow
open scoped Interval ContDiff

private theorem smooth_mellin_gain (P Q : ℂ → ℂ) (s : ℂ)
    {R β U V : ℝ} (hR : 0 < R) (ht : 0 < |s.im|) (hV : 0 ≤ V)
    (hβ : 2 * R * |β| ≤ |s.im|) :
    let z (n : ℕ) := s + (n:ℂ)
    let A (n : ℕ) := R^(z n).re
    (∀ n : ℕ, (‖P (z n)‖ / A n) ≤ U) →
    (∀ n : ℕ, (‖Q (z n)‖ / A n) ≤ V) →
    (∀ n : ℕ, z n * P (z n) = -Q (z (n+1)) - ((β:ℂ)*I)*P (z (n+1))) →
    ∀ n : ℕ, ‖P (z n)‖ / A n ≤ ((2*R) / |s.im|) * V := by
  dsimp only
  intro hP hQ hrec
  let z (n : ℕ) := s + (n:ℂ)
  let A (n : ℕ) := R^(z n).re
  let t := |s.im|
  let u (n : ℕ) := ‖P (z n)‖ / A n
  let v (n : ℕ) := ‖Q (z n)‖ / A n
  have hA (n : ℕ) : 0 < A n := Real.rpow_pos_of_pos hR _
  have hAs (n : ℕ) : A (n+1) = R * A n := by
    have hz : (z (n+1)).re = (z n).re+1 := by simp [z, add_assoc]
    dsimp only [A]
    rw [hz, Real.rpow_add_one hR.ne', mul_comm]
  have hUn (n : ℕ) : 0 ≤ u n := div_nonneg (norm_nonneg _) (hA n).le
  have hUa (n : ℕ) : u n * A n = ‖P (z n)‖ := div_mul_cancel₀ _ (hA n).ne'
  have hVa (n : ℕ) : v n * A n = ‖Q (z n)‖ := div_mul_cancel₀ _ (hA n).ne'
  have hAngle (n : ℕ) : t ≤ ‖z n‖ := by simpa [z,t] using Complex.abs_im_le_norm (z n)
  have hfreq : ‖(β:ℂ)*I‖ = |β| := by simp [Complex.norm_real,Real.norm_eq_abs]
  have hsmall : |β| * R ≤ t/2 := by dsimp only [t]; nlinarith only [hβ]
  have hstep (n : ℕ) : u n ≤ (R/t)*V + u (n+1)/2 := by
    have h₁ : t*‖P (z n)‖ ≤ ‖Q (z (n+1))‖ + |β| * ‖P (z (n+1))‖ := by
      apply (mul_le_mul_of_nonneg_right (hAngle n) (norm_nonneg _)).trans
      rw [← norm_mul, hrec n]
      exact (norm_sub_le _ _).trans_eq (by rw [norm_neg,norm_mul,hfreq])
    rw [← hUa n, ← hVa (n+1), ← hUa (n+1), hAs] at h₁
    have h₂ : t*(u n) ≤ R*v (n+1)+(|β| * R)*u (n+1) := by
      apply le_of_mul_le_mul_right ?_ (hA n)
      convert h₁ using 1 <;> ring
    have hs := h₂.trans (add_le_add (mul_le_mul_of_nonneg_left (hQ (n+1)) hR.le)
      (mul_le_mul_of_nonneg_right hsmall (hUn (n+1))))
    apply le_of_mul_le_mul_right ?_ ht
    convert hs using 1
    · ring
    · field_simp [show t ≠ 0 from ht.ne']
      ring
  intro n
  apply (half_recurrence_bound (mul_nonneg (div_nonneg hR.le ht.le) hV) hP hstep n).trans_eq
  ring

theorem smooth_transform_power_tail (d : ℕ) (w : ℕ → ℝ → ℝ) (M : ℕ → ℝ)
    {X a b β : ℝ} {s : ℂ} (hX : 0 < X) (ha : X ≤ a) (hab : a ≤ b) (hb : b ≤ 2*X)
    (hs : 0 < s.re) (ht : 0 < |s.im|) (hβ : 4*X*|β| ≤ |s.im|)
    (hC : ∀ j : ℕ, j ≤ d → ContinuousOn (w j) (Icc a b))
    (hw : ∀ j : ℕ, j < d → ∀ x ∈ Icc a b, HasDerivAt (w j) (w (j+1) x) x)
    (hend : ∀ j : ℕ, j < d → w j a = 0 ∧ w j b = 0)
    (hM : ∀ j : ℕ, 0 ≤ M j)
    (hW : ∀ j : ℕ, j ≤ d → ∀ x ∈ Icc a b, ‖w j x‖ ≤ M j) :
    ‖smoothTransform a b β (w 0) s‖ ≤
      (2*X) ^ s.re * (((4*X) / |s.im|)^d * M d) := by
  let P (j : ℕ) := smoothTransform a b β (w j)
  let R := 2*X
  let K := (2*R)/|s.im|
  let z (n : ℕ) := s + (n:ℂ)
  let A (n : ℕ) := R^(z n).re
  have hR : 0 < R := by dsimp [R]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hA (n : ℕ) : 0 < A n := Real.rpow_pos_of_pos hR _
  have hz (n : ℕ) : 0 < (z n).re := by simp [z]; positivity
  have hB (j : ℕ) (hj : j ≤ d) (n : ℕ) : ‖P j (z n)‖ / A n ≤ M j :=
    (div_le_iff₀ (hA n)).mpr (smooth_transform_norm_bound hX ha hab hb (hz n).le (hM j) (hW j hj))
  have hgain (j : ℕ) (hj : j < d) {C : ℝ} (hC0 : 0 ≤ C)
      (hQ : ∀ n : ℕ, ‖P (j+1) (z n)‖ / A n ≤ C) :
      ∀ n : ℕ, ‖P j (z n)‖ / A n ≤ K*C := by
    apply smooth_mellin_gain (P j) (P (j+1)) s (β := β) hR ht hC0 (by dsimp only [R]; linarith only [hβ])
      (hB j (by omega)) hQ
    intro n
    have hsucc : z (n+1) = z n + 1 := by simp [z, add_assoc]
    change z n * P j (z n) = -P (j+1) (z (n+1)) - _ * P j (z (n+1))
    rw [hsucc]
    exact smooth_transform_recurrence (hX.trans_le ha) hab (hz n) (hw j hj)
      (hC (j+1) (by omega)) (hend j hj).1 (hend j hj).2
  have hiter (k : ℕ) (hk : k ≤ d) :
      ∀ n, ‖P (d-k) (z n)‖ / A n ≤ K^k * M d := by
    induction k with
    | zero => simpa only [Nat.sub_zero,pow_zero,one_mul] using hB d le_rfl
    | succ k ih =>
      have hj : d-(k+1) < d := by omega
      have hc : 0 ≤ K^k * M d := mul_nonneg (pow_nonneg hK _) (hM d)
      have hstep : d-(k+1)+1=d-k := by omega
      have hi := ih (by omega)
      have hg := hgain (d-(k+1)) hj hc (by simpa only [hstep] using hi)
      simpa only [pow_succ',mul_assoc,Nat.succ_eq_add_one] using hg
  have hfinal := hiter d le_rfl 0
  rw [Nat.sub_self] at hfinal
  have hfin := (div_le_iff₀ (hA 0)).mp hfinal
  dsimp only [P, z, A, K, R] at hfin
  simp only [Nat.cast_zero, add_zero] at hfin
  convert hfin using 1
  ring

theorem smooth_model_power_bound (d : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {X β : ℝ} {s : ℂ}, 0 < X → 0 < s.re → 0 < |s.im| →
      4*X*|β| ≤ |s.im| →
      ‖smoothTransform X (2*X) β (scaledWeight X) s‖ ≤ (2*X)^s.re * (A / |s.im|^d) := by
  choose M hM₀ hM using weight_derivative_bound
  refine ⟨4^d*M d, mul_nonneg (by norm_num) (hM₀ d), ?_⟩
  intro X β s hX hs ht hb
  let W (j : ℕ) := iteratedDeriv j (scaledWeight X)
  let K (j : ℕ) := X⁻¹^j * M j
  have hscale (j : ℕ) : ContDiff ℝ j (scaledWeight X) :=
    (weight_smooth (n := j)).comp (contDiff_id.div_const X)
  have hK (j : ℕ) : 0 ≤ K j := mul_nonneg (by positivity) (hM₀ j)
  have hW (j : ℕ) (x : ℝ) : ‖W j x‖ ≤ K j := by
    dsimp only [W,K]
    rw [scaledWeight_derivative, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ X⁻¹^j)]
    exact mul_le_mul_of_nonneg_left (hM j _) (by positivity)
  have hderiv (j : ℕ) (x : ℝ) : HasDerivAt (W j) (W (j+1) x) x := by
    have h := ((hscale (j+1)).differentiable_iteratedDeriv' j x).hasDerivAt
    dsimp only [W]
    rw [iteratedDeriv_succ]
    exact h
  have hL (j : ℕ) : W j X = 0 := by
    dsimp only [W]
    rw [scaledWeight_derivative, div_self hX.ne', (weight_derivative_endpoint j).1, mul_zero]
  have hR (j : ℕ) : W j (2*X) = 0 := by
    dsimp only [W]
    rw [scaledWeight_derivative, mul_div_cancel_right₀ _ hX.ne',
      (weight_derivative_endpoint j).2, mul_zero]
  have hbound := smooth_transform_power_tail d W K hX le_rfl (by linarith) le_rfl hs ht hb
    (fun j _ => ((hscale j).continuous_iteratedDeriv' j).continuousOn)
    (fun j _ x _ => hderiv j x) (fun j _ => ⟨hL j,hR j⟩) hK (fun j _ x _ => hW j x)
  rw [show W 0 = scaledWeight X by dsimp only [W]; rw [iteratedDeriv_zero] ] at hbound
  apply hbound.trans_eq
  dsimp only [K]
  have he : ((4*X)/|s.im|)^d*(X⁻¹^d*M d) = (4^d*M d)/|s.im|^d := by
    rw [div_pow, mul_pow, inv_pow]
    have hpow : X^d ≠ 0 := pow_ne_zero _ hX.ne'
    have ht' : |s.im|^d ≠ 0 := pow_ne_zero _ ht.ne'
    field_simp
  rw [he]

end GoldbachSmoothMellinPower

end

section

namespace GoldbachCorrectionBands

open Finset MeasureTheory GoldbachHeightTail GoldbachModelTail GoldbachSmoothMellinPower
open GoldbachSmoothWindow GoldbachSmoothMellin GoldbachSmoothApproximation GoldbachZeroStrip
open scoped Interval

theorem dyadic_taper_high_order_energy_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧ ∀ (X : ℕ), 32 ≤ X →
      ∀ (S : Finset ℂ) (c : ℂ → ℂ) (R H J B θ : ℝ),
      0 ≤ R → 1 ≤ H → H ≤ J → 0 ≤ B → θ ≤ 1 → 4*(X:ℝ)*R ≤ H →
      (∀ s ∈ S, 0 < s.re ∧ s.re ≤ θ) →
      (∀ t : ℝ, (∑ s ∈ S.filter (fun s => t ≤ s.im ∧ s.im ≤ t+1), ‖c s‖) ≤ B) →
      (∀ t : ℝ, ((S.filter (fun s => t ≤ -s.im/(2*Real.pi) ∧ -s.im/(2*Real.pi) ≤ t+1)).card : ℝ) ≤ B) →
      (∑ s ∈ S.filter (fun s => |s.im| < J), ‖c s‖) ≤ B*(J+1) →
      let U := (2*(X:ℝ))^θ
      (∫ β in Set.Icc (-R) R,
        ‖∑ s ∈ S, c s * weightedTaperTransform X (2*X-1) (fun n => scaledWeight X n) β s‖^2) ≤
      4 * (A*B*(∑ s ∈ S.filter (fun s => |s.im| < H), ‖c s‖^2 * (X:ℝ)^(2*s.re-1)) +
           (2*R) * ((C*B*U/H^(d-1))^2 + (C*B*U/J)^2 + (C*B*U*(J+1)/(X:ℝ)^2)^2)) := by
  obtain ⟨A,hA,gram⟩ := smooth_mellin_weighted_energy
  obtain ⟨L,hL,highOrder⟩ := smooth_model_power_bound d
  obtain ⟨Q,hQ,quad⟩ := exact_taper_quadratic_bound
  obtain ⟨M,hM,approx⟩ := exact_taper_smooth_bound
  let C := 4*L + 4*Q + M
  have hCL : 4*L ≤ C := by dsimp only [C]; linarith
  have hCQ : 4*Q ≤ C := by dsimp only [C]; linarith
  have hCM : M ≤ C := by dsimp only [C]; linarith
  have hC : 0 ≤ C := hM.trans hCM
  refine ⟨A,C,hA,hC,?_⟩
  intro X hX S c R H J B θ hR hH hHJ hB hθ hRadius hz hunit hrow hmass
  dsimp only
  let x : ℝ := X
  let U := (2*x)^θ
  have hx1 : 1 ≤ x := by dsimp only [x]; exact_mod_cast (show 1 ≤ X by omega)
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hJp : 0 < J := hHp.trans_le hHJ
  let T (β : ℝ) (s : ℂ) := weightedTaperTransform X (2*X-1) (fun n => scaledWeight X n) β s
  let W (β : ℝ) (s : ℂ) := smoothTransform x (2*x) β (scaledWeight x) s
  let S₀ := S.filter (fun s => |s.im| < H)
  let S₁ := S.filter (fun s => H ≤ |s.im| ∧ |s.im| < J)
  let S₂ := S.filter (fun s => J ≤ |s.im|)
  let Sin := S.filter (fun s => |s.im| < J)
  let f (β : ℝ) := ∑ s ∈ S₀, c s * W β s
  let g (β : ℝ) := ∑ s ∈ S₁, c s * W β s
  let k (β : ℝ) := ∑ s ∈ S₂, c s * T β s
  let diff (β : ℝ) := ∑ s ∈ Sin, c s * (T β s - W β s)
  have hContW (s : ℂ) : Continuous (fun β => W β s) :=
    continuous_mellin_band (Complex.continuous_ofReal.comp ((weight_smooth (n := 1)).continuous.comp
      (continuous_id.div_const x))) hx0 (by linarith) s
  have hContT (s : ℂ) : Continuous (fun β => T β s) :=
    continuous_zero_taper (by omega) (by omega) _ s
  have hf : Continuous f := continuous_finsetSum _ (fun s _ => (hContW s).const_mul _)
  have hg : Continuous g := continuous_finsetSum _ (fun s _ => (hContW s).const_mul _)
  have hk : Continuous k := continuous_finsetSum _ (fun s _ => (hContT s).const_mul _)
  have hdif : Continuous diff := continuous_finsetSum _ (fun s _ => ((hContT s).sub (hContW s)).const_mul _)
  have hrp (s : ℂ) (hs : s ∈ S) : (2*x)^s.re ≤ U :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (hz s hs).2
  have hTwist (β : ℝ) (hb : β ∈ Set.Icc (-R) R) : 4*x*|β| ≤ H :=
    (mul_le_mul_of_nonneg_left (abs_le.mpr hb) (by positivity)).trans hRadius
  have hGram : (∫ β in Set.Icc (-R) R, ‖f β‖^2) ≤
      A*B*(∑ s ∈ S₀, ‖c s‖^2 * x^(2*s.re-1)) := by
    apply gram S₀ id c hx1 hB
    · intro s hs
      have h := hz s (mem_filter.mp hs).1
      exact ⟨h.1.le,h.2.trans hθ⟩
    · intro t
      have hsub : S₀.filter (fun s => t ≤ -s.im/(2*Real.pi) ∧ -s.im/(2*Real.pi) ≤ t+1) ⊆
          S.filter (fun s => t ≤ -s.im/(2*Real.pi) ∧ -s.im/(2*Real.pi) ≤ t+1) := by
        intro s hs
        exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hs).1).1,(mem_filter.mp hs).2⟩
      exact (show (((S₀.filter (fun s => t ≤ -s.im/(2*Real.pi) ∧ -s.im/(2*Real.pi) ≤ t+1)).card):ℝ) ≤
          ((S.filter (fun s => t ≤ -s.im/(2*Real.pi) ∧ -s.im/(2*Real.pi) ≤ t+1)).card : ℝ) by
        exact_mod_cast card_le_card hsub).trans (hrow t)
  have hIndex : Sin.filter (fun s => H ≤ |s.im|) = S₁ := by
    ext s
    simp only [Sin,S₁,Finset.mem_filter]
    tauto
  have hMid (β : ℝ) (hb : β ∈ Set.Icc (-R) R) : ‖g β‖ ≤ C*B*U/H^(d-1) := by
    have hUin (t : ℝ) : (∑ s ∈ Sin.filter (fun s => t ≤ s.im ∧ s.im ≤ t+1), ‖c s‖) ≤ B := by
      have hsub : Sin.filter (fun s => t ≤ s.im ∧ s.im ≤ t+1) ⊆
          S.filter (fun s => t ≤ s.im ∧ s.im ≤ t+1) := by
        intro s hs
        exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hs).1).1,(mem_filter.mp hs).2⟩
      exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)).trans (hunit t)
    have hW (s : ℂ) (hs : s ∈ Sin) (hh : H ≤ |s.im|) :
        ‖W β s‖ ≤ (L*U/H^(d-3))/|s.im|^3 := by
      have hi := (mem_filter.mp hs).1
      have hsp := hHp.trans_le hh
      have hbnd := highOrder hx0 (hz s hi).1 hsp ((hTwist β hb).trans hh)
      calc
        _ ≤ (L*U)/|s.im|^d :=
          hbnd.trans ((mul_le_mul_of_nonneg_right (hrp s hi) (by positivity)).trans_eq (by ring))
        _ = (L*U/|s.im|^(d-3))/|s.im|^3 := by
          rw [div_div, ← pow_add, Nat.sub_add_cancel hd]
        _ ≤ _ := div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_left (mul_nonneg hL hU) (pow_pos hHp _)
            (pow_le_pow_left₀ hHp.le hh _)) (by positivity)
    have h := weighted_absolute_tail_sup Sin Complex.im c (W β) hH hB
      (div_nonneg (mul_nonneg hL hU) (pow_nonneg hHp.le _)) (p := 3) (.inr rfl) hUin hW
    rw [hIndex] at h
    change ‖∑ s ∈ S₁, c s * W β s‖ ≤ _
    refine h.trans ?_
    calc
      4 * B * (L * U / H ^ (d-3)) / H ^ (3 - 1 : ℕ) = (4 * L) * (B * U) / H ^ (d-1) := by
        have hpow : H^(d-3) * H^2 = H^(d-1) := by rw [← pow_add, show d-3+2=d-1 by omega]
        rw [← hpow]
        norm_num
        ring
      _ ≤ C * (B * U) / H ^ (d-1) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCL (mul_nonneg hB hU)) (pow_nonneg hHp.le _)
      _ = C * B * U / H ^ (d-1) := by ring
  have hHigh (β : ℝ) (hb : β ∈ Set.Icc (-R) R) : ‖k β‖ ≤ C*B*U/J := by
    have hT (s : ℂ) (hs : s ∈ S) (hh : J ≤ |s.im|) :
        ‖T β s‖ ≤ (Q*U)/|s.im|^2 := by
      have hbnd := quad X hX (hz s hs).1 (hJp.trans_le hh) (((hTwist β hb).trans hHJ).trans hh)
      exact hbnd.trans ((mul_le_mul_of_nonneg_right (hrp s hs) (by positivity)).trans_eq (by ring))
    have h := weighted_absolute_tail_sup S Complex.im c (T β) (hH.trans hHJ) hB
      (mul_nonneg hQ hU) (p := 2) (.inl rfl) hunit hT
    refine h.trans ?_
    calc
      4 * B * (Q * U) / J ^ (2 - 1 : ℕ) = (4 * Q) * (B * U) / J := by
        norm_num
        ring
      _ ≤ C * (B * U) / J := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCQ (mul_nonneg hB hU)) hJp.le
      _ = C * B * U / J := by ring
  have hDiff (β : ℝ) : ‖diff β‖ ≤ C*B*U*(J+1)/x^2 := by
    unfold diff
    have hA (s : ℂ) (hs : s ∈ Sin) : ‖T β s-W β s‖ ≤ M*U/x^2 := by
      have hi := (mem_filter.mp hs).1
      have hbnd := approx X hX β s (hz s hi).1.le
      exact hbnd.trans ((mul_le_mul_of_nonneg_right (hrp s hi) (by positivity)).trans_eq (by ring))
    calc
      _ ≤ ∑ s ∈ Sin, ‖c s * (T β s-W β s)‖ := norm_sum_le _ _
      _ ≤ ∑ s ∈ Sin, ‖c s‖*(M*U/x^2) := sum_le_sum fun s hs => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hA s hs) (norm_nonneg _)
      _ = (∑ s ∈ Sin, ‖c s‖)*(M*U/x^2) := by rw [sum_mul]
      _ ≤ (B*(J+1))*(M*U/x^2) := mul_le_mul_of_nonneg_right hmass (by positivity)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hCM (show 0 ≤ B*(J+1)*U/x^2 by positivity)
        convert hh using 1 <;> ring
  have hEq (β : ℝ) : (∑ s ∈ S, c s * T β s) = f β + g β + diff β + k β :=
    split_taper_correction S Complex.im c (T β) (W β) hHJ
  change (∫ β in Set.Icc (-R) R, ‖∑ s ∈ S, c s * T β s‖^2) ≤ _
  simp_rw [hEq]
  exact (band_integral_add_four_sq_le f g diff k R hf hg hdif hk).trans (by
    have h₁ := band_energy_of_sup hg hR (by positivity) hMid
    have h₂ := band_energy_of_sup hk hR (by positivity) hHigh
    have h₃ := band_energy_of_sup hdif hR (by positivity) (fun β _ => hDiff β)
    dsimp only [x,U,S₀] at hGram h₁ h₂ h₃
    linarith only [hGram,h₁,h₂,h₃])

end GoldbachCorrectionBands

end

section

namespace GoldbachSpectralGeometry

noncomputable def shortHeight (x P r : ℝ) : ℝ := 32 * x^(1/25 : ℝ) * P / r

noncomputable def shortBinHeight (x P R : ℝ) : ℝ := 32 * x^(41/1000 : ℝ) * P / R

theorem short_height_geometry {x P r : ℝ} (hx : (2:ℝ)^200 ≤ x)
    (hr : 1 ≤ r) (hrP : r ≤ P) (hP : P ≤ 4*x^(41/200:ℝ)) :
    0 ≤ angularRadius x P r ∧ x^(1/25:ℝ) ≤ shortHeight x P r ∧
    1 ≤ shortHeight x P r ∧ shortHeight x P r ≤ outerHeight x ∧
    4*x*angularRadius x P r ≤ shortHeight x P r := by
  obtain ⟨hx1,hR,_,_,hJ,_⟩ := profile_heights hx hr hrP hP
  have hp : 0 < P := zero_lt_one.trans_le (hr.trans hrP)
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hΓ : (1:ℝ) ≤ x^(1/25:ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hH : x^(1/25:ℝ) ≤ shortHeight x P r := by
    apply (le_div_iff₀ hr0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hrP (show 0 ≤ x^(1/25:ℝ) by positivity),
      show 0 ≤ x^(1/25:ℝ)*P by positivity]
  have hs : shortHeight x P r ≤ profileHeight x P r := by
    unfold shortHeight profileHeight
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
        (by norm_num)) hp.le) hr0.le
  refine ⟨hR,hH,hΓ.trans hH,hs.trans hJ,?_⟩
  have he : 4*x*angularRadius x P r = 2*Real.pi*P/r := by
    unfold angularRadius
    have hx0 := zero_lt_one.trans_le hx1
    field_simp
  rw [he]
  have hpi : 2*Real.pi ≤ 32*x^(1/25:ℝ) := by linarith only [Real.pi_lt_four,hΓ]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpi hp.le) hr0.le

theorem short_height_le_bin {x P r R : ℝ} (hx : 1 ≤ x) (hP : 0 ≤ P)
    (hr : 0 < r) (hR : 0 < R) (hbin : R ≤ r*x^(1/1000:ℝ)) :
    shortHeight x P r ≤ shortBinHeight x P R := by
  have hx0 := zero_lt_one.trans_le hx
  apply (div_le_div_iff₀ hr hR).mpr
  calc
    (32*x^(1/25:ℝ)*P)*R ≤ (32*x^(1/25:ℝ)*P)*(r*x^(1/1000:ℝ)) :=
      mul_le_mul_of_nonneg_left hbin (by positivity)
    _ = (32*(x^(1/25:ℝ)*x^(1/1000:ℝ))*P)*r := by ring
    _ = _ := by rw [← Real.rpow_add hx0]; norm_num

/-- Global log-free density at the Pólya–Vinogradov scales has slack
for the first power of the zero amplitude. -/
theorem short_bin_q3_t4_scale {x P R : ℝ} (hx : 1 ≤ x)
    (hR : 1 ≤ R) (hP : P ≤ 4*x^(41/200:ℝ)) (hT : 1 ≤ shortBinHeight x P R) :
    let Q : ℕ := ⌊R⌋₊
    let T := shortBinHeight x P R
    (Q:ℝ)^3*(T+1)^4 ≤ (2:ℝ)^32*x^(123/125:ℝ) := by
  dsimp only
  let Q : ℕ := ⌊R⌋₊
  let T := shortBinHeight x P R
  have hx0 := zero_lt_one.trans_le hx
  have hR0 := zero_lt_one.trans_le hR
  have hQ : (Q:ℝ) ≤ R := Nat.floor_le hR0.le
  have hp : 0 ≤ P := by
    have hnum := (le_div_iff₀ hR0).mp hT
    by_contra! hn
    have hneg := mul_neg_of_pos_of_neg (show 0 < 32*x^(41/1000:ℝ) by positivity) hn
    linarith only [hnum,hR0,hneg]

  calc
    _ ≤ R^3*(2*T)^4 := by
      exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hQ 3)
        (pow_le_pow_left₀ (by linarith only [hT]) (by linarith only [hT]) 4)
        (by positivity) (by positivity)
    _ = ((64*x^(41/1000:ℝ)*P)^4)/R := by
      unfold T shortBinHeight
      field_simp
      ring
    _ ≤ (64*x^(41/1000:ℝ)*P)^4 := div_le_self (by positivity) hR
    _ ≤ (64*x^(41/1000:ℝ)*(4*x^(41/200:ℝ)))^4 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hP (by positivity)) 4
    _ = _ := by
      have h1 : 64*x^(41/1000:ℝ)*(4*x^(41/200:ℝ)) = 256*x^(123/500:ℝ) := by
        rw [show 64*x^(41/1000:ℝ)*(4*x^(41/200:ℝ)) =
          256*(x^(41/1000:ℝ)*x^(41/200:ℝ)) by ring, ← Real.rpow_add hx0]
        norm_num
      rw [h1,mul_pow,← Real.rpow_mul_natCast hx0.le]
      norm_num

private theorem half_height_powers_short {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ outerHeight x ∧ outerHeight x ^ 2 = x := by
  constructor
  · exact Real.one_le_rpow hx (by norm_num)
  · unfold outerHeight
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hx)]
    norm_num

theorem per_character_seventh_order_tail {x P r K : ℝ} (hx : 1 ≤ x)
    (hr : 0 < r) (hrP : r ≤ P) (hK : 0 ≤ K) :
    let R := angularRadius x P r
    let H := shortHeight x P r
    let J := outerHeight x
    2*R*((K*(2*x)/H^6)^2 + (K*(2*x)/J)^2 + (K*(2*x)*(J+1)/x^2)^2) ≤
      96*K^2*(P/r)*x^(13/25 : ℝ) := by
  dsimp only
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hp : 0 < P := hr.trans_le hrP
  let W := x^(38/25 : ℝ)
  let H := shortHeight x P r
  let J := outerHeight x
  let R := angularRadius x P r
  have hH : x^(1/25 : ℝ) ≤ H := by
    apply (le_div_iff₀ hr).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hrP (show 0 ≤ x^(1/25 : ℝ) by positivity),
      show 0 ≤ x^(1/25 : ℝ) * P by positivity]
  have hHpos : 0 < H := (Real.rpow_pos_of_pos hxp _).trans_le hH
  have hJ := half_height_powers_short hx
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hrp (a : ℝ) (ha : a ≤ 38/25) : x^a ≤ W := Real.rpow_le_rpow_of_exponent_le hx ha
  have hmid : (K*(2*x)/H^6)^2 ≤ 4*K^2*W := calc
    _ = (4*K^2) * ((x^2)/H^12) := by ring
    _ ≤ (4*K^2) * ((x^2)/(x^(1/25 : ℝ))^12) := by
      have hpow := pow_le_pow_left₀ (show 0 ≤ x^(1/25 : ℝ) by positivity) hH 12
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hpow)
        (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast x 2, ← Real.rpow_mul_natCast hxp.le, ← Real.rpow_sub hxp]
      norm_num [W]
  have hfar : (K*(2*x)/J)^2 ≤ 4*K^2*W := calc
    _ = 4*K^2*(x^2/J^2) := by ring
    _ = 4*K^2*x := by rw [hJ.2]; field_simp
    _ ≤ _ := by simpa only [Real.rpow_one] using
      mul_le_mul_of_nonneg_left (hrp 1 (by norm_num)) (show 0 ≤ 4*K^2 by positivity)
  have hdiff : (K*(2*x)*(J+1)/x^2)^2 ≤ 16*K^2*W := calc
    _ ≤ (K*(2*x)*(2*J)/x^2)^2 := by
      apply pow_le_pow_left₀ (by positivity [hJ.1])
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith [hJ.1]) (by positivity))
        (sq_nonneg _)
    _ = 16*K^2*(J^2/x^2) := by field_simp; ring
    _ = 16*K^2*x⁻¹ := by rw [hJ.2]; field_simp
    _ ≤ _ := by
      simpa only [Real.rpow_neg_one] using
        mul_le_mul_of_nonneg_left (hrp (-1) (by norm_num)) (show 0 ≤ 16*K^2 by positivity)
  have hR : 2*R ≤ 4*(P/r)/x := by
    have he : 2*R = Real.pi*(P/r)/x := by dsimp [R,angularRadius]; ring
    rw [he]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right Real.pi_lt_four.le (by positivity)) hxp.le
  change 2*R*((K*(2*x)/H^6)^2 + (K*(2*x)/J)^2 + (K*(2*x)*(J+1)/x^2)^2) ≤ _
  have htail : (K*(2*x)/H^6)^2 + (K*(2*x)/J)^2 + (K*(2*x)*(J+1)/x^2)^2 ≤
      24*K^2*W := by linarith only [hmid,hfar,hdiff]
  calc
    _ ≤ (4*(P/r)/x)*(24*K^2*W) := mul_le_mul hR htail (by positivity) (by positivity)
    _ = 96*K^2*(P/r)*(W/x) := by ring
    _ = _ := by
      dsimp only [W]
      rw [show x^(38/25:ℝ)/x = x^(13/25:ℝ) by
        conv_lhs => enter [2]; rw [← Real.rpow_one x]
        rw [← Real.rpow_sub hxp]; norm_num]

end GoldbachSpectralGeometry

end

section

namespace GoldbachWeightedMajorResidual

open Finset MeasureTheory Goldbach GoldbachTwistedMellin
open GoldbachWeightedException (cutoff)
open GoldbachConductorRegroup GoldbachCorrectionBands GoldbachCorrectionCounts GoldbachSpectralGeometry
open scoped Classical

noncomputable section

def shortLowZerosOn (keep : ℕ → ℂ → Prop) (X q : ℕ) (χ : DirichletCharacter ℂ q) : Finset ℂ :=
  if h : q = 0 then ∅ else
    let _ : NeZero q := ⟨h⟩
    ((exceptionalZeros χ (heightCut (X : ℝ))).filter (keep χ.conductor)).filter
      (fun z => |z.im| < shortHeight (X : ℝ) (cutoff X : ℝ) q)

def shortLowEnergyAtOn (keep : ℕ → ℂ → Prop) (X q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  if h : q = 0 then 0 else
    let _ : NeZero q := ⟨h⟩
    ∑ z ∈ shortLowZerosOn keep X q χ, (analyticOrderNatAt (regularizedL χ) z : ℝ)^2 * (X : ℝ)^(2*z.re-1)

def shortLowSpectralEnergyOn (keep : ℕ → ℂ → Prop) (X : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 (cutoff X),
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
      shortLowEnergyAtOn keep X q χ

private theorem outerHeight_le_heightCut_short {X : ℕ} (hx : 1 ≤ (X:ℝ)) :
    outerHeight X ≤ heightCut (X:ℝ) := by
  unfold outerHeight heightCut
  calc
    _ ≤ (X:ℝ)^(8:ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    _ = (X:ℝ)^8 := by rw [← Real.rpow_natCast]; norm_num
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith) _

private theorem angularRadius_eq_short {X q : ℕ} :
    2*Real.pi*arcRadius X q = angularRadius (X:ℝ) (cutoff X : ℝ) q := by
  simp only [arcRadius, angularRadius, Nat.cast_mul, Nat.cast_ofNat]

theorem primitive_on_energy_le_short_low_and_tail :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧ ∀ (X : ℕ), 2^200 ≤ X → ∀ (keep : ℕ → ℂ → Prop),
      primitiveCorrectionEnergyOn keep X ≤
        A*(1+Real.log (X:ℝ))*shortLowSpectralEnergyOn keep X +
          C*(1+Real.log (X:ℝ))^2*(X:ℝ)^(93/100 : ℝ) := by
  obtain ⟨A,C,hA,hC,hhighOrder⟩ := dyadic_taper_high_order_energy_bound 7 (by decide)
  obtain ⟨D,hD,hcount⟩ := uniform_exception_counts
  refine ⟨4*A*D,6144*(C*D)^2,by positivity,by positivity,?_⟩
  intro X hX keep
  let x : ℝ := X
  let P := cutoff X
  let L := 1 + Real.log x
  let B := D*L
  have hx2 : (2:ℝ)^200 ≤ x := by dsimp only [x]; exact_mod_cast hX
  have hx : 1 ≤ x := (by norm_num : (1:ℝ) ≤ 2^200).trans hx2
  have hx0 := zero_lt_one.trans_le hx
  have hL : 0 ≤ L := by dsimp only [L]; positivity [Real.log_nonneg hx]
  have hB : 0 ≤ B := mul_nonneg hD.le hL
  obtain ⟨hP,hPp,hPX⟩ := cutoff_scale hX
  have h32 : 32 ≤ X := by omega
  let Q := Finset.Icc 1 P
  let U (q : ℕ) := (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive)
  have hterm (q : ℕ) (hq : q ∈ Q) (χ : DirichletCharacter ℂ q) :
      bandEnergy (zeroProfileOn keep X q χ) (arcRadius X q) ≤
        (4*A*D)*L*shortLowEnergyAtOn keep X q χ +
        384*(C*B)^2*((P:ℝ)/(q:ℝ))*x^(13/25:ℝ) := by
    let H := shortHeight x (P:ℝ) q
    let J := outerHeight x
    let R := angularRadius x (P:ℝ) q
    have hqQ := mem_Icc.mp hq
    let _ : NeZero q := ⟨(show 0 < q from hqQ.1).ne'⟩
    have hqpos : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
    have hqr : (q:ℝ) ≤ P := by exact_mod_cast hqQ.2
    obtain ⟨hR,_,hH,hHJ,hshape⟩ := short_height_geometry hx2
      (by exact_mod_cast hqQ.1) hqr hPp
    let S := (exceptionalZeros χ (heightCut x)).filter (keep χ.conductor)
    let c (z : ℂ) := (analyticOrderNatAt (regularizedL χ) z : ℂ)
    have hz (z : ℂ) (hz : z ∈ S) : 0 < z.re ∧ z.re ≤ 1 := by
      obtain ⟨hre,_,hzero⟩ := (mem_exceptionalZeros χ (heightCut x) z).mp (mem_filter.mp hz).1
      exact ⟨(by norm_num : (0:ℝ) < 1/2).trans hre,
        le_of_not_gt (fun h => regularizedL_ne_zero_right χ h hzero)⟩
    obtain ⟨hunit0,hrow0,hmass0⟩ := hcount X (by omega) q (hqQ.2.trans hPX) χ
    have hsub (p : ℂ → Prop) [DecidablePred p] :
        S.filter p ⊆ (exceptionalZeros χ (heightCut x)).filter p := by
      intro z hz
      obtain ⟨hS, ht⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨(mem_filter.mp hS).1,ht⟩
    have hunit (t : ℝ) : (∑ z ∈ S.filter (fun z => t ≤ z.im ∧ z.im ≤ t+1), ‖c z‖) ≤ B :=
      (sum_le_sum_of_subset_of_nonneg (hsub (fun z => t ≤ z.im ∧ z.im ≤ t+1))
        (fun z _ _ => norm_nonneg (c z))).trans (hunit0 t)
    have hrow (t : ℝ) : ((S.filter (fun z => t ≤ -z.im/(2*Real.pi) ∧ -z.im/(2*Real.pi) ≤ t+1)).card : ℝ) ≤ B := by
      refine le_trans ?_ (hrow0 t)
      exact_mod_cast card_le_card (hsub (fun z => t ≤ -z.im/(2*Real.pi) ∧ -z.im/(2*Real.pi) ≤ t+1))
    have hmass (J : ℝ) (hj : 0 ≤ J) (hj' : J ≤ heightCut (X : ℝ)) :
        (∑ z ∈ S.filter (fun z => |z.im| < J), ‖c z‖) ≤ B*(J+1) :=
      (sum_le_sum_of_subset_of_nonneg (hsub (fun z => |z.im| < J))
        (fun z _ _ => norm_nonneg (c z))).trans (hmass0 J hj hj')
    have hjpos : 0 ≤ J := by dsimp only [J,outerHeight]; positivity
    have hs := hhighOrder X h32 S c R H J B 1 hR hH hHJ hB le_rfl hshape hz hunit hrow
      (hmass J hjpos (outerHeight_le_heightCut_short hx))
    have htail := per_character_seventh_order_tail hx hqpos hqr (mul_nonneg hC hB)
    have he : shortLowEnergyAtOn keep X q χ = ∑ z ∈ S.filter (fun z => |z.im| < H), ‖c z‖^2*x^(2*z.re-1) := by
      simp only [shortLowEnergyAtOn, shortLowZerosOn, dite_eq_right (NeZero.ne q),c,S,H,x,P,Complex.norm_natCast]
    have hu := bandEnergy_zeroProfileOn_le_angular (by omega : 2 ≤ X) χ keep (arcRadius X q)
    rw [angularRadius_eq_short] at hu
    refine hu.trans <| hs.trans ?_
    dsimp only at htail
    simp only [Real.rpow_one]
    rw [he]
    change 4 * (A*B*(∑ z ∈ S.filter (fun z => |z.im| < H), ‖c z‖^2*x^(2*z.re-1)) +
      2*R*((C*B*(2*x)/H^6)^2 + (C*B*(2*x)/J)^2 + (C*B*(2*x)*(J+1)/x^2)^2)) ≤ _
    dsimp only [B] at htail ⊢
    linarith only [htail]
  have hfiber (q : ℕ) (hq : q ∈ Q) :
      (∑ χ ∈ U q, bandEnergy (zeroProfileOn keep X q χ) (arcRadius X q)) ≤
        (4*A*D)*L*(∑ χ ∈ U q, shortLowEnergyAtOn keep X q χ) +
        384*(C*B)^2*(P:ℝ)*x^(13/25:ℝ) := by
    have hq0 := (show 0 < q from (mem_Icc.mp hq).1)
    let _ : NeZero q := ⟨hq0.ne'⟩
    have ht : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    have hcard : ((U q).card : ℝ) ≤ q := by
      exact_mod_cast ((Finset.card_filter_le _ _).trans ((Finset.card_univ.trans ht).le.trans (Nat.totient_le q)))
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq0
    calc
      _ ≤ ∑ χ ∈ U q, ((4*A*D)*L*shortLowEnergyAtOn keep X q χ +
          384*(C*B)^2*((P:ℝ)/(q:ℝ))*x^(13/25:ℝ)) := sum_le_sum (fun χ _ => hterm q hq χ)
      _ = (4*A*D)*L*(∑ χ ∈ U q, shortLowEnergyAtOn keep X q χ) +
          ((U q).card:ℝ)*(384*(C*B)^2*((P:ℝ)/(q:ℝ))*x^(13/25:ℝ)) := by
        simp only [sum_add_distrib, mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ _ := by
        have hc := mul_le_mul_of_nonneg_right hcard
          (show 0 ≤ 384*(C*B)^2*((P:ℝ)/(q:ℝ))*x^(13/25:ℝ) by positivity)
        refine add_le_add le_rfl (hc.trans_eq ?_)
        field_simp
  have hsum := sum_le_sum hfiber
  simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at hsum
  have hQCard : (Q.card : ℝ) = P := by simp [Q, Nat.card_Icc]
  rw [hQCard] at hsum
  have hp2 : (P:ℝ)^2 ≤ (4*x^(41/200:ℝ))^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg P) hPp 2
  have hpow : (x^(41/200:ℝ))^2*x^(13/25:ℝ) = x^(93/100:ℝ) := by
    rw [← Real.rpow_mul_natCast hx0.le, ← Real.rpow_add hx0]
    norm_num
  refine hsum.trans (add_le_add le_rfl ?_)
  calc
    _ = (384*(C*B)^2)*((P:ℝ)^2*x^(13/25:ℝ)) := by ring
    _ ≤ (384*(C*B)^2)*((4*x^(41/200:ℝ))^2*x^(13/25:ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp2 (by positivity)) (by positivity)
    _ = _ := by
      change _ = 6144*(C*D)^2*L^2*x^(93/100:ℝ)
      have hh : (4*x^(41/200:ℝ))^2*x^(13/25:ℝ) = 16*x^(93/100:ℝ) := by
        rw [show (4*x^(41/200:ℝ))^2*x^(13/25:ℝ) =
          16*((x^(41/200:ℝ))^2*x^(13/25:ℝ)) by ring, hpow]
      rw [hh]
      dsimp only [B]
      ring

end
end GoldbachWeightedMajorResidual

end

section

namespace GoldbachWeightedMajorResidual

open Finset Filter MeasureTheory Goldbach GoldbachTwistedMellin
open GoldbachWeightedException (cutoff)
open GoldbachConductorRegroup GoldbachSpectralGeometry GoldbachFarZeroEnergy
open GoldbachLowZeroEnergy GoldbachLowZeroGapEnergy
open scoped Topology Classical

noncomputable section

theorem correction_on_energy_le_short_low_and_tail :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧ ∀ (X : ℕ), 2^200 ≤ X → ∀ keep : ℕ → ℂ → Prop,
      correctionEnergyOn keep X ≤
        A*(1+Real.log (X:ℝ))^3*shortLowSpectralEnergyOn keep X +
          C*(1+Real.log (X:ℝ))^4*(X:ℝ)^(93/100 : ℝ) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := primitive_on_energy_le_short_low_and_tail
  refine ⟨12*A,12*C,by positivity,by positivity,?_⟩
  intro X hX keep
  let x : ℝ := X
  let P := cutoff X
  let L := 1 + Real.log x
  have hx : 1 ≤ x := by dsimp only [x]; exact_mod_cast (show 1 ≤ X by omega)
  have hx₀ := zero_lt_one.trans_le hx
  have hL : 0 ≤ L := by dsimp only [L]; positivity [Real.log_nonneg hx]
  obtain ⟨hP,_,hPX⟩ := cutoff_scale hX
  have hPpos : (0:ℝ) < P := by dsimp only [P]; exact_mod_cast (show 0 < cutoff X by omega)
  have hPx : (P:ℝ) ≤ x := by dsimp only [P,x]; exact_mod_cast hPX
  have hP2 : (P:ℝ)+2 ≤ 3*x := by linarith only [hPx,hx]
  have hlog : Real.log (P+2 : ℝ) ≤ 3*L := calc
    _ ≤ Real.log (3*x) := Real.log_le_log (by positivity) hP2
    _ ≤ _ := by
      rw [Real.log_mul (by norm_num) hx₀.ne']
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
      dsimp only [L]
      linarith only [h,Real.log_nonneg hx]
  have hsum : reciprocalSum P ≤ L :=
    (reciprocalSum_le P).trans (add_le_add le_rfl (Real.log_le_log hPpos hPx))
  have hposR : 0 ≤ reciprocalSum P := sum_nonneg (fun _ _ => by positivity)
  have hfactor : (4*Real.log ((P+2 : ℕ):ℝ))*reciprocalSum P ≤ 12*L^2 := by
    push_cast
    have ht := mul_le_mul (mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ) ≤ 4))
      hsum hposR (show 0 ≤ 4*(3*L) by positivity)
    exact ht.trans_eq (by ring)
  have hprim : 0 ≤ primitiveCorrectionEnergyOn keep X :=
    sum_nonneg (fun q _ => sum_nonneg (fun ψ _ => bandEnergy_nonneg (zeroProfileOn keep X q ψ) (arcRadius X q)))
  have hb : correctionEnergyOn keep X ≤
      ((4*Real.log ((P+2:ℕ):ℝ))*reciprocalSum P)*primitiveCorrectionEnergyOn keep X :=
    correction_on_energy_le_primitive (by omega) keep
  calc
    _ ≤ (12*L^2)*primitiveCorrectionEnergyOn keep X :=
      hb.trans (mul_le_mul_of_nonneg_right hfactor hprim)
    _ ≤ (12*L^2)*(A*L*shortLowSpectralEnergyOn keep X + C*L^2*x^(93/100:ℝ)) :=
      mul_le_mul_of_nonneg_left (hbound X hX keep) (by positivity)
    _ = _ := by change _ = 12*A*L^3*shortLowSpectralEnergyOn keep X + 12*C*L^4*x^(93/100:ℝ); ring

/-- The low-height spectral terms put into the signed model. -/
def shortNearZero (X r : ℕ) (z : ℂ) : Prop :=
  |z.im| < shortHeight (X : ℝ) (cutoff X : ℝ) r ∧ 1-farGap (X:ℝ) < z.re

def shortNearArcCorrection (X q a : ℕ) : ℝ → ℂ :=
  if 2 ≤ X then arcCorrectionOn X q a (shortNearZero X) else 0

theorem continuous_shortNearArcCorrection (X q a : ℕ) : Continuous (shortNearArcCorrection X q a) := by
  unfold shortNearArcCorrection
  split
  · exact continuous_arcCorrectionOn ‹2 ≤ X› q a (shortNearZero X)
  · exact continuous_const

private theorem short_low_on_far_eq (X : ℕ) :
    shortLowSpectralEnergyOn (fun r z => ¬shortNearZero X r z) X =
      ∑ q ∈ Icc 1 (cutoff X), primitiveFiberEnergy (X:ℝ) q
        (selectedFarExceptionalZeros (X:ℝ) (fun r => shortHeight (X:ℝ) (cutoff X:ℝ) r)) := by
  unfold shortLowSpectralEnergyOn
  apply sum_congr rfl
  intro q hq
  let _ : NeZero q := ⟨(show 0 < q from (mem_Icc.mp hq).1).ne'⟩
  simp only [primitiveFiberEnergy, dite_eq_right (NeZero.ne q)]
  apply sum_congr rfl
  intro χ hχ
  have hh : χ.conductor = q := (mem_filter.mp hχ).2
  have he : shortLowZerosOn (fun r z => ¬shortNearZero X r z) X q χ =
      selectedFarExceptionalZeros (X:ℝ) (fun r => shortHeight (X:ℝ) (cutoff X:ℝ) r) q χ := by
    apply Finset.ext
    intro z
    rw [selectedFarExceptionalZeros_mem]
    simp only [shortLowZerosOn, dite_eq_right (NeZero.ne q), mem_filter, shortNearZero, hh]
    constructor
    · rintro ⟨⟨hz, ha⟩, hb⟩
      exact ⟨hz, hb, le_of_not_gt (fun h => ha ⟨hb,h⟩)⟩
    · rintro ⟨hz, hb, ha⟩
      exact ⟨⟨hz, fun h => (not_lt_of_ge ha) h.2⟩, hb⟩
  simp only [shortLowEnergyAtOn, dite_eq_right (NeZero.ne q), he]

private theorem short_low_energy_without_near :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      shortLowSpectralEnergyOn (fun r z => ¬shortNearZero X r z) X ≤
        C*(X:ℝ)/(1+Real.log (X:ℝ))^22 := by
  obtain ⟨C,hC,hf⟩ := selected_far_energy_all_conductors_le
  refine ⟨C,hC,?_⟩
  have hx : Filter.Tendsto (fun X : ℕ => (X:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hx.eventually hf,eventually_ge_atTop (2^200 : ℕ)] with X hX hcut
  obtain ⟨_,hP,_⟩ := cutoff_scale hcut
  rw [short_low_on_far_eq]
  refine (show _ ≤ ∑ q ∈ Icc 1 (cutoff X), primitiveFiberEnergy (X:ℝ) q
    (selectedFarExceptionalZeros (X:ℝ) (fun r => profileHeight (X:ℝ) (cutoff X:ℝ) r)) by
    apply sum_le_sum
    intro q hq
    let _ : NeZero q := ⟨(show 0 < q from (mem_Icc.mp hq).1).ne'⟩
    simp only [primitiveFiberEnergy, dite_eq_right (NeZero.ne q)]
    apply sum_le_sum
    intro χ _
    apply sum_le_sum_of_subset_of_nonneg
    · intro z hz
      obtain ⟨hρ,hγ,hβ⟩ := selectedFarExceptionalZeros_mem.mp hz
      apply selectedFarExceptionalZeros_mem.mpr
      refine ⟨hρ,hγ.trans_le ?_,hβ⟩
      have hx : 1 ≤ (X:ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
      unfold shortHeight profileHeight
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))
          (by norm_num)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    · intro z _ _
      positivity).trans (hX (cutoff X) hP)

theorem correction_energy_without_short_near :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      correctionEnergyOn (fun r z => ¬shortNearZero X r z) X ≤
        C*(X:ℝ)/(1+Real.log (X:ℝ))^19 := by
  obtain ⟨A,C,hA,hC,hmain⟩ := correction_on_energy_le_short_low_and_tail
  obtain ⟨D,hD,hfar⟩ := short_low_energy_without_near
  obtain ⟨K,hK,hK'⟩ := log_power_le_small_power 23 (show (0:ℝ) < 7/100 by norm_num)
  refine ⟨A*D+C*K+1, by positivity, ?_⟩
  filter_upwards [hfar,eventually_ge_atTop (2^200 : ℕ)] with X hX hcut
  let x : ℝ := X
  let L := 1 + Real.log x
  have hx : 1 ≤ x := by dsimp only [x]; exact_mod_cast (show 1 ≤ X by omega)
  have hx0 := zero_lt_one.trans_le hx
  have hL : 0 < L := by dsimp only [L]; positivity [Real.log_nonneg hx]
  let keep (r : ℕ) (z : ℂ) := ¬shortNearZero X r z
  have ht := hmain X hcut keep
  have hs : A*L^3 * shortLowSpectralEnergyOn keep X ≤ (A*D)*x/L^19 := by
    refine (mul_le_mul_of_nonneg_left hX (show 0 ≤ A*L^3 by positivity)).trans_eq ?_
    change (A*L^3)*(D*x/L^22) = (A*D)*x/L^19
    field_simp
  have htail : C*L^4*x^(93/100:ℝ) ≤ (C*K)*x/L^19 := by
    apply (le_div_iff₀ (pow_pos hL _)).mpr
    calc
      _ = C*(L^23)*x^(93/100:ℝ) := by ring
      _ ≤ C*(K*x^(7/100:ℝ))*x^(93/100:ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hK' x hx) hC) (by positivity)
      _ = _ := by
        rw [← mul_assoc C K, mul_assoc, ← Real.rpow_add hx0,
          show (7/100:ℝ)+93/100 = 1 by norm_num, Real.rpow_one]
  refine ht.trans ((add_le_add hs htail).trans ?_)
  calc
    _ = (A*D+C*K)*x/L^19 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
      (by positivity)

theorem short_near_model_remainder_log_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      let n := ((4*X:ℕ):ℝ)
      (∑ q ∈ Icc 1 (cutoff X), ∑ a ∈ (range q).filter (fun a => a.Coprime q),
        ∫ β in Set.Icc (-arcRadius X q) (arcRadius X q),
          ‖arcCorrection X q a β - shortNearArcCorrection X q a β‖^2) ≤
        C*n/(1+Real.log n)^3 := by
  obtain ⟨K,hK,h⟩ := correction_energy_without_short_near
  refine ⟨64*K,by positivity,?_⟩
  filter_upwards [h,eventually_ge_atTop (2:ℕ)] with X hX h2
  dsimp only
  let x : ℝ := X
  let L := 1 + Real.log x
  have hx : 1 ≤ x := by dsimp only [x]; exact_mod_cast (show 1 ≤ X by omega)
  have hx0 := zero_lt_one.trans_le hx
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [Real.log_nonneg hx]
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hn : ((4*X:ℕ):ℝ) = 4*x := by simp [x]
  have hlog : 1+Real.log (4*x) ≤ 4*L := by
    rw [Real.log_mul (by norm_num) hx0.ne']
    have hlog := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)
    dsimp only [L]
    linarith only [Real.log_nonneg hx,hlog]
  have hLP : 0 < 1 + Real.log (4*x) := by
    positivity [Real.log_nonneg (show 1 ≤ 4*x by linarith)]
  simp only [shortNearArcCorrection, ite_eq_left h2, arcCorrection_sub_on]
  change correctionEnergyOn (fun r z => ¬shortNearZero X r z) X ≤ _
  rw [hn]
  refine hX.trans ?_
  change K*x/L^19 ≤ (64*K)*(4*x)/(1+Real.log (4*x))^3
  calc
    _ ≤ K*x/L^3 := div_le_div_of_nonneg_left (by positivity) (pow_pos hL0 _) (pow_le_pow_right₀ hL (by decide : 3≤19))
    _ = (64*K)*x/(4*L)^3 := by ring
    _ ≤ (64*K)*x/(1+Real.log (4*x))^3 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hLP _) (pow_le_pow_left₀ hLP.le hlog 3)
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by positivity)

end
end GoldbachWeightedMajorResidual

end


namespace GoldbachWeightedException

open Filter Finset MeasureTheory
open GoldbachSmoothWindow GoldbachPrincipalSeries
open GoldbachPolynomialMinor205 (series wave scale representations)
open scoped Topology

noncomputable section

def MajorFloorOutside (B : ℕ → Finset ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
    ∀ m ∈ GoldbachCenterWindows.centralWindow X, Even m → m ∉ B X →
      c*(X:ℝ) ≤ (majorCoefficient X m).re

theorem central_count_outside (B : ℕ → Finset ℕ) (H : MajorFloorOutside B) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
    (((GoldbachCenterWindows.centralWindow X).filter (fun m => ordinaryException m ∧ m ∉ B X)).card : ℝ) ≤
      C * (X : ℝ) ^ (319 / 400 : ℝ) := by
  obtain ⟨c, hc, hmajor⟩ := H
  obtain ⟨D, hD, hmoment⟩ := minor_fourth_moment
  let C : ℝ := (96 * (D * 100000) ^ 2 * Real.log 4 * 3 ^ 9 * (4 : ℝ) ^ (797 / 1000 : ℝ)) / c ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hs := ((isLittleO_log_rpow_rpow_atTop (9 : ℝ) (by norm_num : (0 : ℝ) < 1/2000)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hmajor, hmoment, hs, eventually_ge_atTop (2 ^ 200 : ℕ)] with X hmaj hmoment hlog hX
  let n := 4 * X
  let P := cutoff X
  let E := (GoldbachCenterWindows.centralWindow X).filter (fun m => ordinaryException m ∧ m ∉ B X)
  have hX2 : 2 ≤ X := (by norm_num : 2 ≤ 2 ^ (200 : ℕ)).trans hX
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hn : 2 ^ 200 ≤ n := hX.trans (by dsimp [n]; omega)
  have hn0 : 0 < n := by dsimp [n]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnX : (n : ℝ) = 4 * (X : ℝ) := by simp [n]
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have hlognX : Real.log (n : ℝ) ≤ 3 * Real.log (X : ℝ) := by
    rw [hnX, Real.log_mul (by norm_num) hXR.ne']
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [hlog4]
    have hX2R : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
    linarith only [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hX2R]
  obtain ⟨hP, _, _, _, _⟩ := GoldbachWeightedException.chosen_cutoff_bounds (X:=X) hn
  have hcut : (n : ℝ) ^ (203 / 1000 : ℝ) ≤ 2 * (P : ℝ) := GoldbachMajorCutoff.lower X hn
  have hE : E ⊆ Finset.range (n + 1) := by
    intro m hm
    obtain ⟨hhi, _⟩ := mem_filter.mp hm
    have hi := (GoldbachCenterWindows.mem_centralWindow.mp hhi).2
    exact mem_range.mpr (by dsimp [n]; omega)
  have hterm (m : ℕ) (hm : m ∈ E) : c * (X : ℝ) ≤ ‖minorCoefficient X m‖ := by
    obtain ⟨hcen, ⟨he, hrep⟩, hnot⟩ := mem_filter.mp hm
    have hmaj' := hmaj m hcen he hnot
    have hzero := congrArg Complex.re (coefficients_cancel (X := X) hrep)
    simp only [Complex.add_re, Complex.zero_re] at hzero
    have hnrm := (abs_le.mp (Complex.abs_re_le_norm (minorCoefficient X m))).1
    linarith only [hmaj', hzero, hnrm]
  have he : (E.card : ℝ) * (c * (X : ℝ)) ^ 2 ≤
      (D * (100000 * Real.log (n : ℝ) ^ 4 * scale n P)) ^ 2 *
        (Real.log 4 * (n : ℝ) * Real.log (n : ℝ)) := calc
    _ = ∑ _m ∈ E, (c * (X : ℝ)) ^ 2 := by simp
    _ ≤ ∑ m ∈ E, ‖minorCoefficient X m‖ ^ 2 := Finset.sum_le_sum fun m hm =>
      pow_le_pow_left₀ (by positivity) (hterm m hm) 2
    _ ≤ ∑ m ∈ Finset.range (n+1), ‖minorCoefficient X m‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hE (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := hmoment (n+1)
  have hbudget : (D * (100000 * Real.log (n : ℝ) ^ 4 * scale n P)) ^ 2 *
        (Real.log 4 * (n : ℝ) * Real.log (n : ℝ)) ≤
      (C * (Real.log X) ^ 9 * (X : ℝ) ^ (797 / 1000 : ℝ)) * (c * (X : ℝ)) ^ 2 := calc
    _ = ((D * 100000) ^ 2 * Real.log 4 * (n : ℝ) * Real.log (n : ℝ) ^ 9) * (scale n P)^2 := by ring
    _ ≤ ((D * 100000) ^ 2 * Real.log 4 * (n : ℝ) * Real.log (n : ℝ) ^ 9) *
        (2 * (n : ℝ) * (3 * (n : ℝ) ^ (797 / 1000 : ℝ))) :=
      mul_le_mul_of_nonneg_left (scale_budget hn0 hP hcut) (by positivity)
    _ = ((6 * (D * 100000) ^ 2 * Real.log 4 * (n : ℝ)^2) * (n : ℝ) ^ (797 / 1000 : ℝ)) *
        Real.log (n : ℝ) ^ 9 := by ring
    _ ≤ ((6 * (D * 100000) ^ 2 * Real.log 4 * (n : ℝ)^2) * (n : ℝ) ^ (797 / 1000 : ℝ)) *
        (3 * Real.log (X : ℝ)) ^ 9 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hlogn hlognX 9) (by positivity)
    _ = _ := by
      rw [hnX, Real.mul_rpow (by norm_num) hXR.le]
      dsimp [C]
      field_simp
      ring
  have hcount := le_of_mul_le_mul_right (he.trans hbudget) (sq_pos_of_pos (mul_pos hc hXR))
  have hlog' : (Real.log (X : ℝ)) ^ 9 ≤ (X : ℝ) ^ (1 / 2000 : ℝ) := by
    simpa only [Function.comp_apply, Real.rpow_natCast, Real.norm_eq_abs, Real.rpow_ofNat,
      abs_of_nonneg (Real.rpow_nonneg hXR.le _), abs_of_nonneg (pow_nonneg hlogX _), one_mul] using hlog
  refine hcount.trans ?_
  calc
    _ ≤ C * (X : ℝ) ^ (1 / 2000 : ℝ) * (X : ℝ) ^ (797 / 1000 : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog' hC.le) (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hXR]; norm_num


end

theorem dyadic_count_with_exception_floor (B : ℕ → Finset ℕ) (H : MajorFloorOutside B)
    {K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ᶠ X : ℕ in atTop, ((B X).card:ℝ) ≤ K*(X:ℝ)^(319/400:ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℕ in atTop,
      (((Finset.Icc Z (2*Z)).filter ordinaryException).card:ℝ) ≤ C*(Z:ℝ)^(319/400:ℝ) := by
  obtain ⟨C,hC,hcen⟩ := central_count_outside B H
  have hcen' : ∀ᶠ X : ℕ in atTop,
      (((GoldbachCenterWindows.centralWindow X).filter ordinaryException).card:ℝ) ≤
        (C+K)*(X:ℝ)^(319/400:ℝ) := by
    filter_upwards [hcen,hB] with X h₁ h₂
    let A := (GoldbachCenterWindows.centralWindow X).filter ordinaryException
    let F := (GoldbachCenterWindows.centralWindow X).filter
      (fun m => ordinaryException m ∧ m ∉ B X)
    have hsub : A ⊆ F ∪ B X := by
      intro m hm
      obtain ⟨hwindow,hE⟩ := mem_filter.mp hm
      by_cases hb : m ∈ B X
      · exact mem_union_right _ hb
      · exact mem_union_left _ (mem_filter.mpr ⟨hwindow,hE,hb⟩)
    have hcard : (A.card:ℝ) ≤ (F.card:ℝ)+(B X).card := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
    exact hcard.trans ((add_le_add h₁ h₂).trans_eq (by ring))
  obtain ⟨N,hN⟩ := eventually_atTop.1 hcen'
  have hm : 0<C+K := add_pos_of_pos_of_nonneg hC hK
  refine ⟨3*(C+K),by positivity,eventually_atTop.2 ?_⟩
  exact ⟨max 100 (3*N+1), GoldbachCenterWindows.dyadic_count_of_central_bound ordinaryException
    hm.le (by norm_num) N hN⟩

end GoldbachWeightedException

namespace GoldbachWeightedMajorResidual

open Finset Filter GoldbachWeightedException GoldbachTwistedMellin

noncomputable section

theorem signed_coefficient_error_le_eventually (D : ℕ → ℕ → ℕ → ℝ → ℂ)
    (hD : ∀ X q a : ℕ, Continuous (D X q a)) (Henergy : RemainderLogSaving D)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, ∀ m : ℕ,
      ‖majorCoefficient X m - signedModelCoefficient D X m‖ ≤ c * (X : ℝ) / 2 := by
  obtain ⟨C, hC, hcor⟩ := Henergy
  obtain ⟨A, hA, hres⟩ := residual_energy_bound
  obtain ⟨B, hB, hlogpow⟩ := quartic_log_scale (e := 19 / 100) (by norm_num)
  let K := A * B + C
  let K' := Real.log 4 + 4 * K
  have hK : 0 < K := by unfold K; positivity
  have hK' : 0 < K' := by unfold K'; positivity
  have hloglim := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hloglim.eventually_ge_atTop (8 * K' / c)
  filter_upwards [hcor, hlarge, eventually_ge_atTop (2 ^ 200 : ℕ)] with X hcZ hLarge hX
  intro m
  let n : ℕ := 4 * X
  let x := (n : ℝ)
  let L := 1 + Real.log x
  have hxX : x = 4 * (X : ℝ) := by simp [x, n]
  have hn : 2 ^ 200 ≤ n := hX.trans (by dsimp [n]; omega)
  have hx1 : 1 ≤ x := by
    change (1 : ℝ) ≤ (n : ℝ)
    exact_mod_cast ((by norm_num : 1 ≤ 2 ^ (200 : ℕ)).trans hn)
  have hx0 := zero_lt_one.trans_le hx1
  have hLg : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hL : 1 ≤ L := le_add_of_nonneg_right hLg
  have hL0 := zero_lt_one.trans_le hL
  have hlargeL : 8 * K' / c ≤ L := by
    change 8 * K' / c ≤ Real.log (X : ℝ) at hLarge
    have hX0 : (0 : ℝ) < X := by
      exact_mod_cast ((by norm_num : 0 < 2 ^ (200 : ℕ)).trans_le hX)
    have hxc : (X : ℝ) ≤ x := by rw [hxX]; linarith only [hX0]
    exact hLarge.trans ((Real.log_le_log hX0 hxc).trans (by unfold L; linarith))
  have hLscale : L ≤ logScale x := by
    unfold L logScale
    have hxx : x ≤ 2 * x := by linarith only [hx0]
    exact add_le_add le_rfl (Real.log_le_log hx0 hxx)
  have hLpow : L ^ 3 ≤ B * x ^ (19 / 100 : ℝ) := calc
    _ ≤ (logScale x) ^ 3 := pow_le_pow_left₀ hL0.le hLscale 3
    _ ≤ (logScale x) ^ 4 := pow_le_pow_right₀ (logScale_one hx1) (by norm_num)
    _ ≤ _ := hlogpow x hx1
  have hres' : residualEnergy X ≤ (A * B) * x / L ^ 3 := by
    have hr := hres X hn
    change residualEnergy X ≤ A * x ^ (81 / 100 : ℝ) at hr
    refine hr.trans ((le_div_iff₀ (pow_pos hL0 _)).mpr ?_)
    calc
      _ ≤ (A * x ^ (81 / 100 : ℝ)) * (B * x ^ (19 / 100 : ℝ)) :=
        mul_le_mul_of_nonneg_left hLpow (by positivity)
      _ = (A * B) * (x ^ (81 / 100 : ℝ) * x ^ (19 / 100 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hx0]; norm_num
  have hsum : residualEnergy X + remainingCorrectionEnergy D X ≤ K * x / L ^ 3 := by
    change remainingCorrectionEnergy D X ≤ C * x / L ^ 3 at hcZ
    unfold K
    rw [add_mul, add_div]
    exact add_le_add hres' hcZ
  let δ := (L ^ 2)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (pow_pos hL0 _)
  have hδinv : δ⁻¹ = L ^ 2 := inv_inv _
  have hfirst : δ * (Real.log 4 * x * Real.log x) ≤ Real.log 4 * x / L := calc
    _ ≤ δ * (Real.log 4 * x * L) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (by unfold L; linarith) (by positivity)) hδ.le
    _ = _ := by unfold δ; field_simp
  have hsecond : 2 * (1 + δ⁻¹) * (residualEnergy X + remainingCorrectionEnergy D X) ≤
      (4 * K) * x / L := calc
    _ ≤ 2 * (1 + δ⁻¹) * (K * x / L ^ 3) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 2 * (2 * L ^ 2) * (K * x / L ^ 3) := by
      rw [hδinv]
      have hLs : 1 ≤ L ^ 2 := one_le_pow₀ hL
      exact mul_le_mul_of_nonneg_right (by linarith only [hLs]) (by positivity)
    _ = _ := by field_simp; norm_num
  have hsmall : ‖majorCoefficient X m - signedModelCoefficient D X m‖ ≤ c * (X : ℝ) / 2 := calc
    _ ≤ δ * (Real.log 4 * x * Real.log x) +
      2 * (1 + δ⁻¹) * (residualEnergy X + remainingCorrectionEnergy D X) :=
      signed_coefficient_difference hn m D (hD X) hδ
    _ ≤ K' * x / L := by unfold K'; rw [add_mul, add_div]; exact add_le_add hfirst hsecond
    _ ≤ _ := by
      apply (div_le_iff₀ hL0).mpr
      have hh := (div_le_iff₀ hc).mp hlargeL
      have hhm := mul_le_mul_of_nonneg_right hh (show 0 ≤ x / 8 by positivity)
      rw [hxX] at hhm ⊢
      linarith only [hhm]
  exact hsmall

theorem failed_shifts_of_short_floor_outside (B : ℕ → Finset ℕ) {K c : ℝ}
    (hK : 0 ≤ K) (hc : 0 < c)
    (hB : ∀ᶠ X : ℕ in atTop, ((B X).card:ℝ) ≤ K*(X:ℝ)^(319/400:ℝ))
    (hFloor : ∀ᶠ X : ℕ in atTop, ∀ m ∈ GoldbachCenterWindows.centralWindow X, Even m →
      m ∉ B X → c*(X:ℝ) ≤ (signedModelCoefficient shortNearArcCorrection X m).re) :
    ∃ N : ℕ, ∀ X ≥ N, (GoldbachPolynomialMinor205.failedShifts X).card^5 ≤ X^4 := by
  apply failed_shifts_of_dyadic
  have hMS : MajorFloorOutside B := by
    refine ⟨c/2,by positivity,?_⟩
    filter_upwards [hFloor,signed_coefficient_error_le_eventually shortNearArcCorrection
      continuous_shortNearArcCorrection short_near_model_remainder_log_saving hc] with X hf herr
    intro m hm he hB
    have hs := hf m hm he hB
    have hd := herr m
    have hreal := (abs_le.mp (Complex.abs_re_le_norm
      (majorCoefficient X m - signedModelCoefficient shortNearArcCorrection X m))).1
    simp only [Complex.sub_re] at hreal
    linarith only [hs,hd,hreal]
  exact dyadic_count_with_exception_floor B hMS hK hB

end
end GoldbachWeightedMajorResidual


section

namespace GoldbachSignedPairs

open Finset MeasureTheory
open GoldbachPolynomialMinor205 (wave)

noncomputable section

def pairCoefficient {α ι : Type*} (A : Finset α) (center : α → ℝ) (n : ℕ)
    (a : α → ι → ℂ) (i j : ι) : ℂ :=
  ∑ u ∈ A, a u i * a u j * wave (-(n:ℝ)*center u)

def pairIntegral {ι : Type*} (R : ℝ) (n : ℕ) (f : ι → ℝ → ℂ) (i j : ι) : ℂ :=
  ∫ t in Set.Icc (-R) R, f i t * f j t * wave (-(n:ℝ)*t)

/-- Separation of the rational centers and the Mellin profiles in a finite model. -/
theorem signed_window_expansion {α ι : Type*} (A : Finset α) (S : Finset ι)
    (center : α → ℝ) (n : ℕ) (R : ℝ) (a : α → ι → ℂ) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ S, Continuous (f i)) :
    (∑ u ∈ A, ∫ t in Set.Icc (-R) R,
        (∑ i ∈ S, a u i * f i t)^2 * wave (-(n:ℝ)*(center u+t))) =
    ∑ i ∈ S, ∑ j ∈ S, pairCoefficient A center n a i j * pairIntegral R n f i j := by
  let K := Set.Icc (-R) R
  let e (t : ℝ) := wave (-(n:ℝ)*t)
  let c (u : α) (i j : ι) := a u i * a u j * e (center u)
  let g (i j : ι) (t : ℝ) := f i t * f j t * e t
  have he : Continuous e := by unfold e wave; fun_prop
  have hcont (u : α) (i j : ι) (hi : i ∈ S) (hj : j ∈ S) :
      Continuous (fun t => c u i j * g i j t) := ((hf i hi).mul (hf j hj) |>.mul he).const_mul _
  have hp (u : α) (t : ℝ) :
      (∑ i ∈ S, a u i * f i t)^2 * e (center u+t) =
        ∑ i ∈ S, ∑ j ∈ S, c u i j * g i j t := by
    have hphase : e (center u+t) = e (center u) * e t := by
      unfold e
      unfold wave
      rw [← Complex.exp_add]
      push_cast
      congr 1
      ring
    rw [pow_two, hphase, Finset.sum_mul_sum, Finset.sum_mul]
    apply sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply sum_congr rfl
    intro j _
    dsimp only [c,g]
    ring
  have hI (u : α) : (∫ t in K, ∑ i ∈ S, ∑ j ∈ S, c u i j * g i j t) =
      ∑ i ∈ S, ∑ j ∈ S, c u i j * ∫ t in K, g i j t := by
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro i hi
      rw [integral_finsetSum]
      · exact sum_congr rfl (fun j _ => integral_const_mul _ _)
      · exact fun j hj => (hcont u i j hi hj).integrableOn_Icc
    · intro i hi
      exact integrable_finsetSum _ (fun j hj => (hcont u i j hi hj).integrableOn_Icc)
  change (∑ u ∈ A, ∫ t in K, (∑ i ∈ S, a u i * f i t)^2 * e (center u+t)) = _
  simp_rw [hp,hI]
  change (∑ u ∈ A, ∑ i ∈ S, ∑ j ∈ S, c u i j * ∫ t in K, g i j t) =
    ∑ i ∈ S, ∑ j ∈ S, (∑ u ∈ A, c u i j) * ∫ t in K, g i j t
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  exact sum_congr rfl (fun j _ => (Finset.sum_mul _ _ _).symm)

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset MeasureTheory Goldbach GoldbachTwistedMellin
open GoldbachWeightedMajorResidual GoldbachSmoothWindow GoldbachZeroStrip
open GoldbachPrincipalSeries (finiteModel_continuous)
open GoldbachPolynomialMinor205 (wave)
open GoldbachWeightedException (cutoff)
open Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc (unitMean)
open scoped Classical

noncomputable section

abbrev Mode (q : ℕ) := Option (Σ _ : DirichletCharacter ℂ q, ℂ)

def signedProfile (X q : ℕ) [NeZero q] : Mode q → ℝ → ℂ
  | none => discreteModel X
  | some ⟨χ,z⟩ => fun β => -(analyticOrderNatAt (regularizedL χ) z : ℂ) *
      weightedTaperTransform X (2*X-1) (fun k => scaledWeight X k) (2*Real.pi*β) z

def rationalWeight (q : ℕ) [NeZero q] (a : ℕ) : Mode q → ℂ
  | none => unitMean q a
  | some ⟨χ,_⟩ => additiveWeight (a : ZMod q) χ

theorem continuous_signedProfile {X q : ℕ} [NeZero q] (hX : 2 ≤ X) (i : Mode q) :
    Continuous (signedProfile X q i) := by
  rcases i with _ | ⟨χ,z⟩
  · exact finiteModel_continuous _ _
  · have h := GoldbachCorrectionBands.continuous_zero_taper
      (a:=X) (b:=2*X-1) (by omega) (by omega) (fun k => scaledWeight (X:ℝ) k) z
    exact (h.comp (by fun_prop : Continuous (fun β : ℝ => 2*Real.pi*β))).const_mul _

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset DirichletCharacter GoldbachTwistedMellin ZMod
open scoped ComplexConjugate

noncomputable section

theorem additiveWeight_eq_dft {q : ℕ} [NeZero q] (a : ZMod q) (χ : DirichletCharacter ℂ q) :
    additiveWeight a χ = ZMod.dft (⇑χ⁻¹) (-a) / (q.totient : ℂ) := by
  rw [weight_expansion a χ,ZMod.dft_apply (⇑χ⁻¹) (-a)]
  apply congrArg (fun v : ℂ => v / (q.totient : ℂ))
  apply sum_congr rfl
  intro r _
  simp only [smul_eq_mul, mul_neg, neg_neg, mul_comm a r]
  exact congrArg (fun z : ℂ => stdAddChar (r * a) * z)
    (show conj (χ r) = χ⁻¹ r from MulChar.star_apply' χ r)

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset ZMod DirichletCharacter GoldbachTwistedMellin GoldbachMajorEnergy
open B13BilateralVaughanReductionProof.DyadicMixedB4CharacterFactorBound

noncomputable section

def unitPair {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) : ℂ :=
  ∑ a : (ZMod q)ˣ, additiveWeight (a : ZMod q) χ * additiveWeight (a : ZMod q) ψ *
    stdAddChar (-(m*(a : ZMod q)))

theorem gaussSum_eq_units {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ZMod q) :
    gaussSum χ (stdAddChar.mulShift b) =
      ∑ a : (ZMod q)ˣ, χ (a : ZMod q) * stdAddChar (b*(a : ZMod q)) := by
  classical
  let ι : (ZMod q)ˣ ↪ ZMod q := ⟨(↑),Units.val_injective⟩
  have hset : (Finset.univ : Finset (ZMod q)).filter IsUnit =
      (Finset.univ : Finset (ZMod q)ˣ).map ι := by
    ext a
    simp [ι,IsUnit]
  unfold gaussSum
  simp only [AddChar.mulShift_apply]
  have he : (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit, χ a*stdAddChar (b*a)) =
      ∑ a : (ZMod q)ˣ, χ (a : ZMod q)*stdAddChar (b*(a : ZMod q)) := by
    rw [hset,sum_map]
    rfl
  rw [← he]
  symm
  apply sum_subset (filter_subset _ _)
  intro a _ ha
  have h : ¬IsUnit a := fun h => ha (mem_filter.mpr ⟨mem_univ _,h⟩)
  rw [χ.map_nonunit h, zero_mul]

/-- Exact rational numerator factor even when both characters are lifted. -/
theorem unitPair_eq_gauss {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) :
    unitPair χ ψ m =
      additiveWeight 1 χ * additiveWeight 1 ψ *
        gaussSum (χ*ψ) (stdAddChar.mulShift (-m)) := by
  unfold unitPair
  rw [gaussSum_eq_units, mul_sum]
  apply sum_congr rfl
  intro a _
  simp only [additiveWeight_unit_factor, MulChar.mul_apply, neg_mul]
  ring

theorem additiveWeight_one_eq_gauss {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    additiveWeight 1 χ = gaussSum χ⁻¹ stdAddChar / (q.totient : ℂ) := by
  rw [additiveWeight_eq_dft, fourierTransform_eq_gaussSum_mulShift χ⁻¹,
    neg_neg, AddChar.mulShift_one]

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset GoldbachWeightedMajorResidual GoldbachTwistedMellin
open GoldbachPolynomialMinor205 (wave)
open Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc (unitMean)
open B13BilateralVaughanReductionProof.DyadicMixedB4DualCharacter

noncomputable section

def modeCharacter (q : ℕ) : Mode q → DirichletCharacter ℂ q
  | none => 1
  | some v => v.1

private theorem unitMean_eq_additiveWeight {q : ℕ} [NeZero q] (a : ℕ) :
    unitMean q a = additiveWeight (a:ZMod q) 1 := by
  rw [additiveWeight_one, GoldbachGRHWindow.additiveModel_eq_reduced_sum, unitMean]
  apply congrArg (fun z : ℂ => z / (q.totient:ℂ))
  apply sum_congr rfl
  intro k _
  unfold Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.phase
  congr 1
  push_cast
  ring

theorem rationalWeight_eq_additiveWeight {q : ℕ} [NeZero q] (a : ℕ) (i : Mode q) :
    rationalWeight q a i = additiveWeight (a:ZMod q) (modeCharacter q i) := by
  cases i with
  | none => exact unitMean_eq_additiveWeight a
  | some v => rfl

theorem wave_rational_center {q : ℕ} [NeZero q] (m a : ℕ) :
    wave (-(m:ℝ)*((a:ℝ)/q)) = ZMod.stdAddChar (-(m:ZMod q)*(a:ZMod q)) := by
  have hc : (-(m:ZMod q)*(a:ZMod q)) = ((-(m:ℤ)*(a:ℤ):ℤ):ZMod q) := by push_cast; rfl
  rw [hc,ZMod.stdAddChar_coe]
  unfold wave
  congr 1
  push_cast
  ring

private theorem reduced_nats_eq_units {q : ℕ} [NeZero q] (F : ZMod q → ℂ) :
    (∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), F (a:ZMod q)) =
      ∑ u : (ZMod q)ˣ, F (u:ZMod q) := by
  let ι : (ZMod q)ˣ ↪ ZMod q := ⟨(↑),Units.val_injective⟩
  have hset : (Finset.univ : Finset (ZMod q)).filter IsUnit =
      (Finset.univ : Finset (ZMod q)ˣ).map ι := by
    ext a
    simp [ι,IsUnit]
  have hF :
      (∑ z ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit, F z) =
        ∑ u : (ZMod q)ˣ, F (u:ZMod q) := by
    rw [hset,Finset.sum_map]
    rfl
  rw [← hF,Finset.sum_filter,Finset.sum_filter]
  have h := sum_natCast_range_eq_zmod (fun z : ZMod q => if IsUnit z then F z else 0)
  simpa only [ZMod.isUnit_iff_coprime] using h

set_option maxHeartbeats 2200000 in
theorem rational_pair_eq_unitPair {q : ℕ} [NeZero q] (m : ℕ) (i j : Mode q) :
    pairCoefficient ((Finset.range q).filter (fun a => a.Coprime q)) (fun a : ℕ => (a:ℝ)/q)
      m (rationalWeight q) i j =
    unitPair (modeCharacter q i) (modeCharacter q j) (m:ZMod q) := by
  let F (z : ZMod q) : ℂ := additiveWeight z (modeCharacter q i) *
    additiveWeight z (modeCharacter q j) * ZMod.stdAddChar (-((m:ZMod q)*z))
  calc
    _ = ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), F (a:ZMod q) := by
      unfold pairCoefficient
      apply sum_congr rfl
      intro a _
      rw [rationalWeight_eq_additiveWeight,rationalWeight_eq_additiveWeight,wave_rational_center]
      simp only [F,neg_mul]
    _ = ∑ u : (ZMod q)ˣ, F (u:ZMod q) := reduced_nats_eq_units F
    _ = _ := rfl

end
end GoldbachSignedPairs

end

section

/-! The generalized Goldbach singular series for two primitive Dirichlet
characters. Grouping finite Fourier frequencies by reduced denominator gives
the totient-normalized residue density. A uniform bound for the three Gauss
sums gives absolute convergence at every positive target. Taking finite
levels divisible by every fixed denominator proves the first inequality in
Pintz, “A new explicit formula in the additive theory of primes with
applications I”, §7, (7.7), https://arxiv.org/abs/1804.05561.

The Gauss sums here use the positive additive phase, so the target frequency
in the third Gauss sum is negative. -/

namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter
open scoped BigOperators Classical
open B13BilateralVaughanReductionProof

private theorem group_average {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (π : G →* H) (onto : Function.Surjective π) (F : H → ℂ) :
    (Fintype.card H : ℂ) * ∑ x : G, F (π x) = (Fintype.card G : ℂ) * ∑ y : H, F y := by
  have left (y : H) : (∑ x : G, F (y*π x)) = ∑ x : G, F (π x) := by
    obtain ⟨z,rfl⟩ := onto y
    simp_rw [← map_mul]
    exact Equiv.sum_comp (Equiv.mulLeft z) (fun x => F (π x))
  have right (x : G) : (∑ y : H, F (y*π x)) = ∑ y : H, F y :=
    Equiv.sum_comp (Equiv.mulRight (π x)) F
  calc
    _ = ∑ _y : H, ∑ x : G, F (π x) := by simp
    _ = ∑ y : H, ∑ x : G, F (y*π x) := sum_congr rfl (fun y _ => (left y).symm)
    _ = ∑ x : G, ∑ y : H, F (y*π x) := sum_comm
    _ = ∑ _x : G, ∑ y : H, F y := sum_congr rfl (fun x _ => right x)
    _ = _ := by simp

/-- Pushing a lifted character through the reduction of residues preserves
the totient-normalized weighted sum against every function on the divisor. -/
theorem induced_average {q d : ℕ} [NeZero q] [NeZero d] (h : d ∣ q)
    (θ : DirichletCharacter ℂ d) (F : ZMod d → ℂ) :
    (d.totient:ℂ)*(∑ x : ZMod q, changeLevel h θ x * F (ZMod.castHom h (ZMod d) x)) =
      (q.totient:ℂ)*(∑ y : ZMod d, θ y * F y) := by
  let _ : Fintype (ZMod q)ˣ := BombieriVinogradov.LargeSieve.characterReductionUnitFintype q
  let _ : Fintype (ZMod d)ˣ := BombieriVinogradov.LargeSieve.characterReductionUnitFintype d
  rw [← BombieriVinogradov.LargeSieve.sum_units_eq_sum_residues,
    ← BombieriVinogradov.LargeSieve.sum_units_eq_sum_residues θ]
  simp only [changeLevel_eq_cast_of_dvd, ZMod.castHom_apply]
  simpa only [ZMod.card_units_eq_totient, ZMod.unitsMap_val] using
    group_average (ZMod.unitsMap h) (ZMod.unitsMap_surjective h)
      (fun u : (ZMod d)ˣ => θ (u : ZMod d) * F u)

/-- When a character does not factor through the divisor, its whole
pushforward measure vanishes, even before choosing a Fourier phase. -/
theorem absent_average {q d : ℕ} [NeZero q] (h : d ∣ q) (χ : DirichletCharacter ℂ q)
    (hn : ¬χ.FactorsThrough d) (F : ZMod d → ℂ) :
    (∑ x : ZMod q, χ x * F (ZMod.castHom h (ZMod d) x)) = 0 := by
  classical
  have hk := mt (factorsThrough_iff_ker_unitsMap h).mpr hn
  obtain ⟨u,hu,hχ⟩ := Set.not_subset.mp hk
  have hmem : ZMod.unitsMap h u = 1 := hu
  have hne : χ (u : ZMod q) ≠ 1 := by
    intro he
    apply hχ
    apply Units.ext
    exact he
  have hu' : ZMod.castHom h (ZMod d) (u : ZMod q) = 1 := congrArg Units.val hmem
  apply eq_zero_of_mul_eq_self_left hne
  let G (x : ZMod q) := χ x * F (ZMod.castHom h (ZMod d) x)
  calc
    _ = ∑ x : ZMod q, G (u*x) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      simp only [G,map_mul,hu',one_mul,mul_assoc]
    _ = _ := u.mulLeft_bijective.sum_comp G

private theorem phase_descent {q d : ℕ} [NeZero q] [NeZero d] (h : d ∣ q)
    (k : ℕ) (x : ZMod q) :
    ZMod.stdAddChar (((q/d*k : ℕ) : ZMod q)*x) =
      ZMod.stdAddChar ((k : ZMod d)*ZMod.castHom h (ZMod d) x) := by
  obtain ⟨f,rfl⟩ := h
  obtain ⟨n,rfl⟩ : ∃ n : ℕ, (n : ZMod (d*f)) = x := ⟨x.val,ZMod.natCast_zmod_val x⟩
  rw [Nat.mul_div_cancel_left f (NeZero.pos d), map_natCast, ← Nat.cast_mul, ← Nat.cast_mul,
    DyadicMixedB4GaussLift.stdAddChar_nat_fraction, DyadicMixedB4GaussLift.stdAddChar_nat_fraction]
  congr 1
  have hf : f ≠ 0 := fun e => NeZero.ne (d*f) (by simp [e])
  push_cast
  field_simp [NeZero.ne d,hf]

noncomputable def amplitude {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (k : ℕ) : ℂ :=
  gaussSum χ (ZMod.stdAddChar.mulShift (k : ZMod q)) / (q.totient:ℂ)

theorem amplitude_at_divisor {q d : ℕ} [NeZero q] [NeZero d] (h : d ∣ q)
    (χ : DirichletCharacter ℂ q) (k : ℕ) :
    amplitude χ (q/d*k) = if H : χ.FactorsThrough d then amplitude H.χ₀ k else 0 := by
  classical
  unfold amplitude gaussSum
  simp only [AddChar.mulShift_apply,phase_descent h]
  split_ifs with H
  · apply (div_eq_div_iff (Nat.cast_ne_zero.mpr (NeZero.ne q.totient))
        (Nat.cast_ne_zero.mpr (NeZero.ne d.totient))).mpr
    calc
      _ = (d.totient:ℂ)*(∑ x : ZMod q, changeLevel h H.χ₀ x *
        ZMod.stdAddChar ((k : ZMod d)*ZMod.castHom h (ZMod d) x)) := by
          conv_lhs => rw [H.eq_changeLevel]
          ring
      _ = _ := (induced_average h H.χ₀ (fun y => ZMod.stdAddChar ((k : ZMod d)*y))).trans (mul_comm ..)
  · rw [absent_average h χ H (fun y => ZMod.stdAddChar ((k : ZMod d)*y)),zero_div]

/-- Sort the frequencies at level q by their reduced denominator.
The zero frequency is the unique reduced numerator at denominator one. -/
theorem reduced_denominators (q : ℕ) [NeZero q] (F : ℕ → ℂ) :
    ∑ k ∈ range q, F k =
      ∑ d ∈ q.divisors, ∑ a ∈ (range d).filter (fun a => d.Coprime a), F (q/d*a) := by
  classical
  let T (g : ℕ) := ∑ k ∈ (range q).filter (fun k => q.gcd k=g), F k
  have part : ∑ k ∈ range q, F k = ∑ g ∈ q.divisors, T g :=
    (sum_fiberwise_of_maps_to (fun k (_ : k ∈ range q) =>
      Nat.mem_divisors.mpr ⟨q.gcd_dvd_left k,NeZero.ne q⟩) F).symm
  rw [part, ← Nat.sum_div_divisors q T]
  apply sum_congr rfl
  intro d hd
  obtain ⟨g,hg⟩ := Nat.dvd_of_mem_divisors hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hgpos : 0 < g := by
    by_contra! hg0
    exact NeZero.ne q (by simp [hg,show g=0 by omega])
  have hquot : q/d=g := by rw [hg,Nat.mul_div_cancel_left g hdpos]
  rw [hquot]
  unfold T
  symm
  apply sum_bij (fun a _ => g*a)
  · intro a ha
    obtain ⟨ha,hc⟩ := mem_filter.mp ha
    have hq : q=g*d := hg.trans (mul_comm d g)
    exact mem_filter.mpr ⟨mem_range.mpr (hq ▸ Nat.mul_lt_mul_of_pos_left (mem_range.mp ha) hgpos),
      by rw [hq,Nat.gcd_mul_left,hc.gcd_eq_one,mul_one]⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hgpos hab
  · intro k hk
    obtain ⟨hk,hc⟩ := mem_filter.mp hk
    obtain ⟨a,rfl⟩ : g ∣ k := hc ▸ q.gcd_dvd_right k
    have hq : q=g*d := hg.trans (mul_comm d g)
    rw [hq,Nat.gcd_mul_left] at hc
    have ha : a<d := (Nat.mul_lt_mul_left hgpos).mp (hq ▸ mem_range.mp hk)
    exact ⟨a,mem_filter.mpr ⟨mem_range.mpr ha, (mul_eq_left₀ hgpos.ne').mp hc⟩,rfl⟩
  · intro _ _
    rfl

noncomputable def normalized {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ℕ) : ℂ :=
  ((q:ℂ)*∑ x : ZMod q, χ x * ψ ((m : ZMod q)-x)) / (q.totient:ℂ)^2

/-- The contribution of the reduced fractions of denominator d. It is zero
unless both characters descend. Its phases and Gauss sums are all at d. -/
noncomputable def denominatorTerm {q : ℕ} (χ ψ : DirichletCharacter ℂ q) (m d : ℕ) : ℂ := by
  classical
  exact if hd : d ≠ 0 then
    let _ : NeZero d := ⟨hd⟩
    if H : χ.FactorsThrough d then
      if K : ψ.FactorsThrough d then
        ∑ a ∈ (range d).filter (fun a => d.Coprime a),
          ZMod.stdAddChar ((a : ZMod d)*(-(m : ZMod d))) * amplitude H.χ₀ a * amplitude K.χ₀ a
      else 0
    else 0
  else 0

private theorem synthesis {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) :
    (∑ t : ZMod q, ZMod.stdAddChar (t*(-m)) * (gaussSum χ (ZMod.stdAddChar.mulShift t) *
      gaussSum ψ (ZMod.stdAddChar.mulShift t))) = (q:ℂ) * ∑ x : ZMod q, χ x * ψ (m-x) := by
  let J (s : ZMod q) := ∑ x : ZMod q, χ x * ψ (s-x)
  have h (t : ZMod q) : ZMod.dft J (-t) =
      gaussSum χ (ZMod.stdAddChar.mulShift t) * gaussSum ψ (ZMod.stdAddChar.mulShift t) := by
    rw [gaussSum_mul,ZMod.dft_apply]
    apply sum_congr rfl
    intro s _
    rw [← sum_mul]
    simp only [J,smul_eq_mul,mul_neg,neg_neg,AddChar.mulShift_apply,mul_comm]
  calc
    _ = ZMod.dft (fun t => ZMod.dft J (-t)) m := by
      rw [ZMod.dft_apply]
      apply sum_congr rfl
      intro t _
      rw [h,smul_eq_mul,mul_neg]
    _ = _ := by rw [ZMod.dft_comp_neg,ZMod.dft_dft]; simp only [J,neg_neg,smul_eq_mul]

theorem finite_expansion {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ℕ) :
    normalized χ ψ m = ∑ d ∈ q.divisors, denominatorTerm χ ψ m d := by
  let F (k : ℕ) := ZMod.stdAddChar ((k : ZMod q)*(-(m : ZMod q))) * amplitude χ k * amplitude ψ k
  have H : normalized χ ψ m = ∑ k ∈ range q, F k := by
    unfold normalized
    rw [← synthesis, ← DyadicMixedB4DualCharacter.sum_natCast_range_eq_zmod, sum_div]
    apply sum_congr rfl
    intro k _
    dsimp only [F,amplitude]
    ring
  rw [H,reduced_denominators q F]
  apply sum_congr rfl
  intro d hd
  have hd0 := (Nat.pos_of_mem_divisors hd).ne'
  let _ : NeZero d := ⟨hd0⟩
  have divides := Nat.dvd_of_mem_divisors hd
  unfold denominatorTerm
  simp only [dite_eq_left hd0]
  by_cases Hχ : χ.FactorsThrough d <;> by_cases Hψ : ψ.FactorsThrough d <;>
    simp only [F,amplitude_at_divisor divides,phase_descent divides,map_neg,map_natCast,Hχ,Hψ,
      dite_true,dite_false,mul_zero,zero_mul,sum_const_zero]

private theorem principal_count {q : ℕ} [NeZero q] (m : ZMod q) :
    (∑ x : ZMod q, (1 : DirichletCharacter ℂ q) x * (1 : DirichletCharacter ℂ q) (m-x)) =
      (((univ : Finset (ZMod q)).filter (fun x => IsUnit x ∧ IsUnit (m-x))).card:ℂ) := by
  calc
    _ = ∑ x : ZMod q, if IsUnit x ∧ IsUnit (m-x) then (1:ℂ) else 0 := by
      apply sum_congr rfl
      intro x _
      by_cases hu : IsUnit x <;> by_cases hv : IsUnit (m-x) <;>
        simp [hu,hv,MulChar.one_apply,MulChar.map_nonunit]
    _ = _ := by simp

private theorem chars_le_units {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q)
    (m : ZMod q) : ‖∑ x : ZMod q, χ x * ψ (m-x)‖ ≤
      ‖∑ x : ZMod q, (1 : DirichletCharacter ℂ q) x * (1 : DirichletCharacter ℂ q) (m-x)‖ := by
  rw [principal_count,Complex.norm_natCast]
  calc
    _ ≤ ∑ x : ZMod q, ‖χ x * ψ (m-x)‖ := norm_sum_le _ _
    _ ≤ ∑ x : ZMod q, if IsUnit x ∧ IsUnit (m-x) then (1:ℝ) else 0 := by
      apply sum_le_sum
      intro x _
      by_cases hu : IsUnit x
      · by_cases hv : IsUnit (m-x)
        · rw [ite_eq_left ⟨hu,hv⟩,norm_mul]
          simpa only [one_mul] using mul_le_mul (χ.norm_le_one x) (ψ.norm_le_one (m-x))
            (norm_nonneg _) zero_le_one
        · simp [hv,ψ.map_nonunit hv]
      · simp [hu,χ.map_nonunit hu]
    _ = _ := by simp

/-- Every complete divisor sum is dominated by the ordinary singular-series
sum at the same level and target, without any primitivity assumption. -/
theorem domination {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ℕ) :
    ‖∑ d ∈ q.divisors, denominatorTerm χ ψ m d‖ ≤
      ‖∑ d ∈ q.divisors, denominatorTerm (1 : DirichletCharacter ℂ q) 1 m d‖ := by
  rw [← finite_expansion,← finite_expansion]
  simp only [normalized,norm_div,norm_mul]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (chars_le_units χ ψ _) (norm_nonneg _))
    (norm_nonneg _)


theorem reduced_numerators {d : ℕ} [NeZero d] (χ ψ : DirichletCharacter ℂ d) (m : ℕ) :
    (∑ a ∈ (range d).filter (fun a => d.Coprime a), ZMod.stdAddChar ((a : ZMod d)*(-(m : ZMod d))) *
      amplitude χ a * amplitude ψ a) = gaussCoefficient χ ψ m := by
  let A := gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar / (d.totient:ℂ)^2
  let F (z : ZMod d) := (χ*ψ)⁻¹ z * ZMod.stdAddChar ((-(m : ZMod d))*z)
  have shift (θ : DirichletCharacter ℂ d) (a : ℕ) (hc : a.Coprime d) :
      gaussSum θ (ZMod.stdAddChar.mulShift (a : ZMod d)) =
        θ⁻¹ (a : ZMod d) * gaussSum θ ZMod.stdAddChar :=
    gaussSum_mulShift_eq θ ZMod.stdAddChar (ZMod.unitOfCoprime a hc)
  rw [sum_filter]
  calc
    _ = ∑ a ∈ range d, A * F (a : ZMod d) := by
      apply sum_congr rfl
      intro a _
      by_cases hc : d.Coprime a
      · simp only [ite_eq_left hc,A,F,amplitude,shift _ _ hc.symm,mul_inv,MulChar.mul_apply]
        rw [mul_comm (a : ZMod d) (-(m : ZMod d))]
        ring
      · have hnu : ¬IsUnit (a : ZMod d) := fun hu => hc ((ZMod.isUnit_iff_coprime a d).mp hu).symm
        simp only [ite_eq_right hc,F,MulChar.map_nonunit _ hnu,zero_mul,mul_zero]
    _ = A * ∑ z : ZMod d, F z := by
      rw [← mul_sum,DyadicMixedB4DualCharacter.sum_natCast_range_eq_zmod F]
    _ = _ := by unfold A F gaussCoefficient gaussSum; simp only [AddChar.mulShift_apply]; ring


private theorem factors_iff_source {r q d : ℕ} [NeZero q] {α : DirichletCharacter ℂ r}
    (hα : α.IsPrimitive) (hr : r ∣ q) (hd : d ∣ q) :
    (changeLevel hr α).FactorsThrough d ↔ r ∣ d := by
  constructor
  · intro H
    simpa only [conductor_changeLevel,show α.conductor=r from hα] using
      conductor_dvd_of_mem_conductorSet (changeLevel hr α) H
  · intro h
    exact ⟨hd,changeLevel h α,changeLevel_trans α h hd⟩

private theorem descended_character {r q d : ℕ} [NeZero q] (α : DirichletCharacter ℂ r)
    (hr : r ∣ q) (hd : d ∣ q) (h : r ∣ d) (H : (changeLevel hr α).FactorsThrough d) :
    H.χ₀ = changeLevel h α :=
  changeLevel_injective hd (H.eq_changeLevel.symm.trans (changeLevel_trans α h hd))

theorem stable_denominator {r s q : ℕ} [NeZero q] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ q) (hs : s ∣ q) (m d : ℕ) (hd : d ∣ q) :
    denominatorTerm (changeLevel hr α) (changeLevel hs β) m d = coefficient α β m d := by
  have hd0 : d ≠ 0 := fun e => NeZero.ne q (Nat.eq_zero_of_zero_dvd (e ▸ hd))
  let _ : NeZero d := ⟨hd0⟩
  simp only [denominatorTerm,coefficient,dite_eq_left hd0]
  by_cases H : r ∣ d
  · have H' := (factors_iff_source hα hr hd).mpr H
    by_cases K : s ∣ d
    · have K' := (factors_iff_source hβ hs hd).mpr K
      simp only [dite_eq_left H',dite_eq_left K',dite_eq_left (And.intro H K),reduced_numerators,
        descended_character α hr hd H H',descended_character β hs hd K K']
    · have K' := mt (factors_iff_source hβ hs hd).mp K
      simp only [dite_eq_left H',dite_eq_right K',dite_eq_right (not_and_of_not_right _ K)]
  · have H' := mt (factors_iff_source hα hr hd).mp H
    simp only [dite_eq_right H',dite_eq_right (not_and_of_not_left _ H)]

private theorem estimate_at_multiple {r s d : ℕ} [NeZero r] [NeZero s] [NeZero d]
    (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (hr : r ∣ d) (hs : s ∣ d)
    (m : ℕ) (hm : 0 < m) :
    let R := Real.sqrt ((r*s:ℕ):ℝ)
    let M := ∑ f ∈ m.divisors, (f:ℝ)
    ‖gaussCoefficient (changeLevel hr α) (changeLevel hs β) m‖ ≤ R*R*(R*M)/(d.totient:ℝ)^2 := by
  intro R M
  let A := changeLevel hr α
  let B := changeLevel hs β
  let Z := (A*B)⁻¹
  have hrpos := Nat.mul_pos (NeZero.pos r) (NeZero.pos s)
  have cA : A.conductor ∣ r*s := by
    dsimp only [A]
    rw [conductor_changeLevel]
    exact α.conductor_dvd_level.trans (dvd_mul_right r s)
  have cB : B.conductor ∣ r*s := by
    dsimp only [B]
    rw [conductor_changeLevel]
    exact β.conductor_dvd_level.trans (dvd_mul_left s r)
  have cZ : Z.conductor ∣ r*s := by
    rw [show Z.conductor=(A*B).conductor from conductor_inv _]
    exact (conductor_mul_dvd_lcm_conductor A B).trans (Nat.lcm_dvd cA cB)
  have root {t : ℕ} (h : t ∣ r*s) : Real.sqrt t ≤ R :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd hrpos h)
  have hA := (DyadicMixedB4CharacterFactorBound.norm_dirichlet_gauss_standard A).trans (root cA)
  have hB := (DyadicMixedB4CharacterFactorBound.norm_dirichlet_gauss_standard B).trans (root cB)
  have mass : (∑ f ∈ m.divisors.filter (fun f => Z.conductor*f ∣ d), (f:ℝ)) ≤ M :=
    sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun i _ _ => Nat.cast_nonneg i)
  have hsft := DyadicMixedB4CharacterFactorBound.norm_dirichlet_gauss_induced (dvd_refl d) Z m hm
  rw [changeLevel_self] at hsft
  have hZ := (DyadicMixedB4CharacterFactorBound.norm_gauss_neg_shift_le Z (m : ZMod d)).trans
    (hsft.trans (mul_le_mul (root cZ) mass (by positivity) (Real.sqrt_nonneg _)))
  change ‖(gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
    gaussSum Z (ZMod.stdAddChar.mulShift (-(m : ZMod d))))/(d.totient:ℂ)^2‖ ≤ _
  rw [norm_div,norm_pow,Complex.norm_natCast,norm_mul,norm_mul]
  exact div_le_div_of_nonneg_right (mul_le_mul
    (mul_le_mul hA hB (norm_nonneg _) (Real.sqrt_nonneg _)) hZ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) (sq_nonneg _)

private theorem totient_weight {d : ℕ} (hd : 0 < d) :
    1/(d.totient:ℝ)^2 ≤ 576 * (d:ℝ)^(-(3/2):ℝ) := by
  have h := DeepThreeQuarters.totient_ratio_le_rpow (show (0:ℝ)<1/4 by norm_num) d hd
  norm_num at h
  have dp : (0:ℝ)<d := by exact_mod_cast hd
  have hp : (0:ℝ)<d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have invbound : 1/(d.totient:ℝ) ≤ 24*(d:ℝ)^(-(3/4):ℝ) := by
    calc
      _ = ((d:ℝ)/d.totient)/d := by field_simp
      _ ≤ (24*(d:ℝ)^(1/4:ℝ))/d := div_le_div_of_nonneg_right h dp.le
      _ = _ := by
        rw [show (-(3/4):ℝ)=1/4-1 by norm_num,Real.rpow_sub dp,Real.rpow_one]
        ring
  have square := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1/d.totient) invbound 2
  rw [div_pow,one_pow,mul_pow,← Real.rpow_mul_natCast dp.le] at square
  norm_num at square ⊢
  exact square

/-- Absolute convergence holds at every positive target. The divisor sum of
m controls the third Gauss sum uniformly as the reduced denominator varies. -/
theorem summable_coefficients {r s : ℕ} [NeZero r] [NeZero s]
    (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) (hm : 0 < m) :
    Summable (fun d : ℕ => ‖coefficient α β m d‖) := by
  let R := Real.sqrt ((r*s:ℕ):ℝ)
  let M := ∑ f ∈ m.divisors, (f:ℝ)
  let C := R*R*(R*M)
  have hC : 0≤C := by dsimp [C,M,R]; positivity
  have summable : Summable (fun d : ℕ => (d:ℝ)^(-(3/2):ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (summable.mul_left (C*576))
  intro d
  by_cases hd : d=0
  · simp [coefficient,hd,Real.zero_rpow (by norm_num : (-(3/2):ℝ) ≠ 0)]
  have bound0 : 0 ≤ C*576*(d:ℝ)^(-(3/2):ℝ) := by positivity
  let _ : NeZero d := ⟨hd⟩
  by_cases h : r ∣ d ∧ s ∣ d
  · simp only [coefficient,dite_eq_left hd,dite_eq_left h]
    calc
      _ ≤ C/(d.totient:ℝ)^2 := estimate_at_multiple α β h.1 h.2 m hm
      _ = C*(1/(d.totient:ℝ)^2) := by ring
      _ ≤ C*(576*(d:ℝ)^(-(3/2):ℝ)) := mul_le_mul_of_nonneg_left (totient_weight (Nat.pos_of_ne_zero hd)) hC
      _ = _ := by ring
  · simpa only [coefficient,dite_eq_left hd,dite_eq_right h,norm_zero] using bound0

theorem ambient_sum {r s q : ℕ} [NeZero q] {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (hr : r ∣ q) (hs : s ∣ q) (m : ℕ) :
    normalized (changeLevel hr α) (changeLevel hs β) m =
      ∑ d ∈ q.divisors, coefficient α β m d :=
  (finite_expansion _ _ m).trans (sum_congr rfl (fun d hd =>
    stable_denominator hα hβ hr hs m d (Nat.dvd_of_mem_divisors hd)))

open Filter Topology

private theorem cofinal_divisors (L : ℕ) (hL : L ≠ 0) :
    Tendsto (fun n : ℕ => insert 0 (L*n.factorial).divisors) atTop atTop := by
  apply tendsto_atTop.2
  intro S
  filter_upwards [eventually_ge_atTop (S.sup id)] with n hn
  intro d hd
  by_cases h : d=0
  · simp [h]
  apply mem_insert_of_mem
  have hdn : d≤n := (S.le_sup (f := id) hd).trans hn
  exact Nat.mem_divisors.mpr ⟨(Nat.dvd_factorial (Nat.pos_of_ne_zero h) hdn).trans
    (dvd_mul_left n.factorial L),mul_ne_zero hL n.factorial_ne_zero⟩

private theorem partial_limit {r s : ℕ} [NeZero r] [NeZero s]
    (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) (hm : 0 < m)
    (L : ℕ) (hL : L ≠ 0) :
    Tendsto (fun n : ℕ => ∑ d ∈ (L*n.factorial).divisors, coefficient α β m d)
      atTop (𝓝 (∑' d : ℕ, coefficient α β m d)) := by
  have h := (summable_coefficients α β m hm).of_norm.hasSum
  have hl := h.comp (cofinal_divisors L hL)
  apply hl.congr'
  filter_upwards with n
  simp [coefficient]

private theorem principal_real (q : ℕ) [NeZero q] (m : ℕ) :
    ‖normalized (1 : DirichletCharacter ℂ q) 1 m‖ = (normalized (1 : DirichletCharacter ℂ q) 1 m).re := by
  let N := ((univ : Finset (ZMod q)).filter (fun x => IsUnit x ∧ IsUnit ((m:ZMod q)-x))).card
  let v : ℝ := q*N/(q.totient:ℝ)^2
  have hv : 0≤v := by dsimp [v]; positivity
  have e : normalized (1 : DirichletCharacter ℂ q) 1 m = (v:ℂ) := by
    unfold normalized v
    rw [principal_count]
    push_cast
    rfl
  rw [e,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hv,Complex.ofReal_re]

/-- The absolute value of the full twisted singular series is at most the
ordinary singular series at each positive target. Both series converge
absolutely, with no zero-free hypothesis. -/
theorem infinite_domination {r s : ℕ} [NeZero r] [NeZero s]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) :
    ‖∑' d : ℕ, coefficient α β m d‖ ≤
      (∑' d : ℕ, coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d).re := by
  let L := r*s
  have hL : L ≠ 0 := mul_ne_zero (NeZero.ne r) (NeZero.ne s)
  let oneχ : DirichletCharacter ℂ 1 := 1
  have main := partial_limit oneχ oneχ m hm L hL
  apply le_of_tendsto_of_tendsto' (partial_limit α β m hm L hL).norm (Complex.continuous_re.tendsto _ |>.comp main)
  intro n
  let q := L*n.factorial
  let _ : NeZero q := ⟨mul_ne_zero hL n.factorial_ne_zero⟩
  have hr : r ∣ q := (dvd_mul_right r s).trans (dvd_mul_right L n.factorial)
  have hs : s ∣ q := (dvd_mul_left s r).trans (dvd_mul_right L n.factorial)
  have ordinary := ambient_sum (α := oneχ) (β := oneχ) isPrimitive_one_level_one
    isPrimitive_one_level_one (one_dvd q) (one_dvd q) m
  simp only [oneχ,map_one] at ordinary
  change ‖∑ d ∈ q.divisors, coefficient α β m d‖ ≤
    (∑ d ∈ q.divisors, coefficient oneχ oneχ m d).re
  rw [← ambient_sum hα hβ hr hs m,← ordinary,← principal_real]
  simpa only [← finite_expansion] using domination (changeLevel hr α) (changeLevel hs β) m

end Conjectures.Goldbach.TwistedGoldbachSingularSeries


namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter Complex
open scoped BigOperators Classical
open B13BilateralVaughanReductionProof

noncomputable def crtCharacter {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : DirichletCharacter ℂ (q*r) :=
  changeLevel (dvd_mul_right q r) χ * changeLevel (dvd_mul_left r q) ψ


theorem crtCharacter_apply {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (x : ZMod (q*r)) :
    crtCharacter χ ψ x = χ (ZMod.chineseRemainder h x).1 * ψ (ZMod.chineseRemainder h x).2 := by
  by_cases hu : IsUnit x
  · obtain ⟨u,rfl⟩ := hu
    rw [crtCharacter,MulChar.mul_apply,changeLevel_eq_cast_of_dvd,changeLevel_eq_cast_of_dvd,
      crt_fst h,crt_snd h,ZMod.castHom_apply,ZMod.castHom_apply]
  · have hpair : ¬(IsUnit (ZMod.chineseRemainder h x).1 ∧ IsUnit (ZMod.chineseRemainder h x).2) :=
      fun hh => hu ((isUnit_map_iff (ZMod.chineseRemainder h) x).mp (Prod.isUnit_iff.mpr hh))
    rw [MulChar.map_nonunit _ hu]
    by_cases hq : IsUnit (ZMod.chineseRemainder h x).1
    · rw [MulChar.map_nonunit ψ (fun hr => hpair ⟨hq,hr⟩),mul_zero]
    · rw [MulChar.map_nonunit χ hq,zero_mul]

/-- The CRT permutation with the local coordinates multiplied by the
complementary moduli. This choice splits the standard additive phase. -/
noncomputable def scaledCRT {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r) :
    (ZMod q × ZMod r) ≃ ZMod (q*r) :=
  (Equiv.prodCongr (ZMod.unitOfCoprime r h.symm).mulLeft (ZMod.unitOfCoprime q h).mulLeft).trans
    (ZMod.chineseRemainder h).symm.toEquiv

private theorem scaledCRT_coords {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r)
    (p : ZMod q × ZMod r) :
    ZMod.chineseRemainder h (scaledCRT h p) = ((r:ZMod q)*p.1,(q:ZMod r)*p.2) := by
  change ZMod.chineseRemainder h ((ZMod.chineseRemainder h).symm _) = _
  rw [RingEquiv.apply_symm_apply]
  cases p
  rfl

private theorem scaledCRT_cast {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r)
    (p : ZMod q × ZMod r) :
    scaledCRT h p = ((r*p.1.val+q*p.2.val:ℕ):ZMod (q*r)) := by
  apply (ZMod.chineseRemainder h).injective
  rw [scaledCRT_coords,map_natCast]
  apply Prod.ext
  · simp [Nat.cast_add,Nat.cast_mul]
  · simp [Nat.cast_add,Nat.cast_mul]

private theorem phase_mul_modulus {q r : ℕ} [NeZero q] [NeZero r] (n : ℕ) :
    ZMod.stdAddChar (((r*n:ℕ):ZMod (q*r))) = ZMod.stdAddChar (n:ZMod q) := by
  rw [DyadicMixedB4GaussLift.stdAddChar_nat_fraction,DyadicMixedB4GaussLift.stdAddChar_nat_fraction]
  congr 1
  push_cast
  have hq : (q:ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hr : (r:ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  field_simp

private theorem phase_mul_left_modulus {q r : ℕ} [NeZero q] [NeZero r] (n : ℕ) :
    ZMod.stdAddChar (((q*n:ℕ):ZMod (q*r))) = ZMod.stdAddChar (n:ZMod r) := by
  rw [DyadicMixedB4GaussLift.stdAddChar_nat_fraction,DyadicMixedB4GaussLift.stdAddChar_nat_fraction]
  congr 1
  push_cast
  have hq : (q:ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hr : (r:ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  field_simp

private theorem phase_scaledCRT {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r)
    (k : ZMod (q*r)) (p : ZMod q × ZMod r) :
    ZMod.stdAddChar (k*scaledCRT h p) =
      ZMod.stdAddChar ((ZMod.chineseRemainder h k).1*p.1) *
        ZMod.stdAddChar ((ZMod.chineseRemainder h k).2*p.2) := by
  obtain ⟨n,rfl⟩ : ∃ n : ℕ, (n:ZMod (q*r))=k := ⟨k.val,ZMod.natCast_zmod_val k⟩
  rw [scaledCRT_cast,← Nat.cast_mul,Nat.mul_add,Nat.cast_add,AddChar.map_add_eq_mul,
    show n*(r*p.1.val)=r*(n*p.1.val) by ring,
    show n*(q*p.2.val)=q*(n*p.2.val) by ring,
    phase_mul_modulus,phase_mul_left_modulus,map_natCast (ZMod.chineseRemainder h) n]
  simp [Nat.cast_mul,ZMod.natCast_zmod_val]

/-- A Gauss sum at a CRT product splits up to two explicit unit values. -/
theorem gaussSum_crtCharacter {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (k : ZMod (q*r)) :
    gaussSum (crtCharacter χ ψ) (ZMod.stdAddChar.mulShift k) =
      (χ (r:ZMod q)*ψ (q:ZMod r)) *
        (gaussSum χ (ZMod.stdAddChar.mulShift (ZMod.chineseRemainder h k).1) *
          gaussSum ψ (ZMod.stdAddChar.mulShift (ZMod.chineseRemainder h k).2)) := by
  let F (x : ZMod (q*r)) := crtCharacter χ ψ x * ZMod.stdAddChar (k*x)
  let L (x : ZMod q) := χ x * ZMod.stdAddChar ((ZMod.chineseRemainder h k).1*x)
  let R (x : ZMod r) := ψ x * ZMod.stdAddChar ((ZMod.chineseRemainder h k).2*x)
  let A := χ (r:ZMod q)*ψ (q:ZMod r)
  simp only [gaussSum,AddChar.mulShift_apply]
  change (∑ x, F x)=A*((∑ x,L x)*(∑ y,R y))
  calc
    _ = ∑ p : ZMod q × ZMod r, F (scaledCRT h p) :=
      (Equiv.sum_comp (scaledCRT h) F).symm
    _ = ∑ p : ZMod q × ZMod r, A*(L p.1*R p.2) := by
      apply sum_congr rfl
      intro p _
      dsimp only [F,A,L,R]
      rw [crtCharacter_apply h,scaledCRT_coords,phase_scaledCRT,map_mul,map_mul]
      ring
    _ = _ := by
      rw [← mul_sum,Fintype.sum_prod_type,Finset.sum_mul_sum]

end Conjectures.Goldbach.TwistedGoldbachSingularSeries

namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter Complex
open scoped BigOperators Classical

private theorem crtCharacter_mul_for_gauss {q r : ℕ} [NeZero q] [NeZero r]
    (χ₁ ψ₁ : DirichletCharacter ℂ q) (χ₂ ψ₂ : DirichletCharacter ℂ r) :
    crtCharacter χ₁ χ₂ * crtCharacter ψ₁ ψ₂ = crtCharacter (χ₁*ψ₁) (χ₂*ψ₂) := by
  simp only [crtCharacter,map_mul]
  exact mul_mul_mul_comm _ _ _ _

private theorem crtCharacter_inv_for_gauss {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    (crtCharacter χ ψ)⁻¹ = crtCharacter χ⁻¹ ψ⁻¹ := by
  simp only [crtCharacter,map_inv,mul_inv]

private theorem gaussSum_crtCharacter_standard {q r : ℕ} [NeZero q] [NeZero r]
    (h : q.Coprime r) (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    gaussSum (crtCharacter χ ψ) ZMod.stdAddChar =
      (χ (r:ZMod q)*ψ (q:ZMod r))*(gaussSum χ ZMod.stdAddChar*gaussSum ψ ZMod.stdAddChar) := by
  simpa only [map_one,Prod.fst_one,Prod.snd_one,AddChar.mulShift_one]
    using gaussSum_crtCharacter h χ ψ (1:ZMod (q*r))

private theorem gaussSum_crtCharacter_target {q r : ℕ} [NeZero q] [NeZero r]
    (h : q.Coprime r) (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (m : ℕ) :
    gaussSum (crtCharacter χ ψ) (ZMod.stdAddChar.mulShift (-(m:ZMod (q*r)))) =
      (χ (r:ZMod q)*ψ (q:ZMod r))*
        (gaussSum χ (ZMod.stdAddChar.mulShift (-(m:ZMod q)))*
          gaussSum ψ (ZMod.stdAddChar.mulShift (-(m:ZMod r)))) := by
  simpa only [map_neg,map_natCast,Prod.fst_neg,Prod.snd_neg,Prod.fst_natCast,Prod.snd_natCast]
    using gaussSum_crtCharacter h χ ψ (-(m:ZMod (q*r)))

private theorem unit_values_cancel {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q)
    (u : (ZMod q)ˣ) : χ (u:ZMod q)*ψ (u:ZMod q)*(χ*ψ)⁻¹ (u:ZMod q)=1 := by
  simpa only [MulChar.mul_apply,MulChar.one_apply_coe] using
    congrArg (fun f : DirichletCharacter ℂ q => f (u:ZMod q)) (mul_inv_cancel (χ*ψ))

/-- The three local unit factors from CRT cancel exactly in the normalized
Goldbach denominator coefficient. -/
theorem gaussCoefficient_crtCharacter {q r : ℕ} [NeZero q] [NeZero r]
    (h : q.Coprime r) (χ₁ ψ₁ : DirichletCharacter ℂ q)
    (χ₂ ψ₂ : DirichletCharacter ℂ r) (m : ℕ) :
    gaussCoefficient (crtCharacter χ₁ χ₂) (crtCharacter ψ₁ ψ₂) m =
      gaussCoefficient χ₁ ψ₁ m * gaussCoefficient χ₂ ψ₂ m := by
  let δ₁ := (χ₁*ψ₁)⁻¹
  let δ₂ := (χ₂*ψ₂)⁻¹
  have hq : χ₁ (r:ZMod q)*ψ₁ (r:ZMod q)*δ₁ (r:ZMod q)=1 :=
    unit_values_cancel χ₁ ψ₁ (ZMod.unitOfCoprime r h.symm)
  have hr : χ₂ (q:ZMod r)*ψ₂ (q:ZMod r)*δ₂ (q:ZMod r)=1 :=
    unit_values_cancel χ₂ ψ₂ (ZMod.unitOfCoprime q h)
  let G₁ := gaussSum χ₁ ZMod.stdAddChar * gaussSum ψ₁ ZMod.stdAddChar *
    gaussSum δ₁ (ZMod.stdAddChar.mulShift (-(m:ZMod q)))
  let G₂ := gaussSum χ₂ ZMod.stdAddChar * gaussSum ψ₂ ZMod.stdAddChar *
    gaussSum δ₂ (ZMod.stdAddChar.mulShift (-(m:ZMod r)))
  have hG :
      gaussSum (crtCharacter χ₁ χ₂) ZMod.stdAddChar *
        gaussSum (crtCharacter ψ₁ ψ₂) ZMod.stdAddChar *
        gaussSum (crtCharacter χ₁ χ₂ * crtCharacter ψ₁ ψ₂)⁻¹
          (ZMod.stdAddChar.mulShift (-(m:ZMod (q*r)))) = G₁*G₂ := by
    rw [gaussSum_crtCharacter_standard h,gaussSum_crtCharacter_standard h,
      crtCharacter_mul_for_gauss,crtCharacter_inv_for_gauss]
    change _ * _ * gaussSum (crtCharacter δ₁ δ₂) (ZMod.stdAddChar.mulShift (-(m:ZMod (q*r)))) = _
    rw [gaussSum_crtCharacter_target h]
    calc
      _ = (χ₁ (r:ZMod q)*ψ₁ (r:ZMod q)*δ₁ (r:ZMod q)) *
          (χ₂ (q:ZMod r)*ψ₂ (q:ZMod r)*δ₂ (q:ZMod r)) * (G₁*G₂) := by
        dsimp only [G₁,G₂]
        ring
      _ = _ := by rw [hq,hr,one_mul,one_mul]
  unfold gaussCoefficient
  rw [hG,Nat.totient_mul h,Nat.cast_mul,mul_pow,div_mul_div_comm] <;> rfl

/-- The ordinary denominator coefficients are multiplicative. -/
theorem principal_gaussCoefficient_mul {q r : ℕ} [NeZero q] [NeZero r]
    (h : q.Coprime r) (m : ℕ) :
    gaussCoefficient (1:DirichletCharacter ℂ (q*r)) 1 m =
      gaussCoefficient (1:DirichletCharacter ℂ q) 1 m *
        gaussCoefficient (1:DirichletCharacter ℂ r) 1 m := by
  simpa only [crtCharacter,map_one,mul_one] using
    gaussCoefficient_crtCharacter h (1:DirichletCharacter ℂ q) 1 (1:DirichletCharacter ℂ r) 1 m

end Conjectures.Goldbach.TwistedGoldbachSingularSeries

namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter Complex ArithmeticFunction
open scoped BigOperators Classical ArithmeticFunction.Moebius
open B13BilateralVaughanReductionProof
open B13BilateralVaughanReductionProof.DyadicMixedB4Ramanujan
open B13BilateralVaughanReductionProof.DyadicMixedB4MoebiusGauss

/-- The standard principal Gauss sum is the Möbius value. -/
theorem principal_gauss_standard_eq_moebius (q : ℕ) [NeZero q] :
    gaussSum (1:DirichletCharacter ℂ q) ZMod.stdAddChar = moebiusComplex q := by
  by_cases hq : q=1
  · subst q
    have hval (x : ZMod 1) : (1:DirichletCharacter ℂ 1) x*ZMod.stdAddChar x=1 := by
      have hχ : (1:DirichletCharacter ℂ 1) x=1 := by rw [Subsingleton.elim x 1,map_one]
      have hψ : ZMod.stdAddChar x=1 := by rw [Subsingleton.elim x 0,AddChar.map_zero_eq_one]
      rw [hχ,hψ,one_mul]
    unfold gaussSum
    calc
      _ = ∑ _x : ZMod 1, (1:ℂ) := sum_congr rfl (fun x _ => hval x)
      _ = _ := by simp [ZMod.card,moebiusComplex]
  · have hq' : 1<q := by have hh := NeZero.pos q; omega
    have he := ramanujan_natural_gauss hq' 1
    simp only [Nat.cast_one,AddChar.mulShift_one] at he
    have hr := ramanujan_moebius hq' 1
    simp only [Nat.cast_one] at hr
    rw [← he,hr,sum_eq_single q]
    · simp [Nat.div_self (NeZero.pos q)]
    · intro d hd hdq
      have hnd : ¬q/d∣1 := by
        intro h
        apply hdq
        have he := Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1
        rw [Nat.dvd_one.mp h,one_mul] at he
        exact he
      simp [hnd]
    · intro h
      exact (h (Nat.mem_divisors.mpr ⟨dvd_refl _,NeZero.ne q⟩)).elim

theorem principal_gauss_neg_shift_eq {q : ℕ} [NeZero q] (k : ZMod q) :
    gaussSum (1:DirichletCharacter ℂ q) (ZMod.stdAddChar.mulShift (-k)) =
      gaussSum (1:DirichletCharacter ℂ q) (ZMod.stdAddChar.mulShift k) := by
  have he := gaussSum_mulShift (1:DirichletCharacter ℂ q) (ZMod.stdAddChar.mulShift k)
    (-1:(ZMod q)ˣ)
  have hχ : (1:DirichletCharacter ℂ q) (((-1:(ZMod q)ˣ):ZMod q))=1 :=
    MulChar.one_apply_coe _
  rw [hχ,one_mul,AddChar.mulShift_mulShift] at he
  simpa using he

theorem principal_gaussCoefficient_eq_zero_of_not_squarefree {q : ℕ} [NeZero q]
    (hq : ¬Squarefree q) (m : ℕ) :
    gaussCoefficient (1:DirichletCharacter ℂ q) 1 m=0 := by
  unfold gaussCoefficient
  rw [principal_gauss_standard_eq_moebius]
  simp [moebiusComplex,moebius_eq_zero_of_not_squarefree hq]

private theorem principal_prime_gauss_shift {p : ℕ} [NeZero p] (hp : p.Prime) (m : ℕ) :
    gaussSum (1:DirichletCharacter ℂ p) (ZMod.stdAddChar.mulShift (m:ZMod p)) =
      if p∣m then (p:ℂ)-1 else -1 := by
  rw [← ramanujan_natural_gauss hp.one_lt,ramanujan_moebius hp.one_lt,hp.divisors,
    sum_insert (by simpa using hp.ne_one.symm),sum_singleton]
  simp [moebiusComplex,moebius_apply_prime hp,Nat.div_self hp.pos]
  split_ifs <;> ring

/-- The local signed coefficient is `1/(p-1)` when the prime divides the
target and `-1/(p-1)^2` otherwise. -/
theorem principal_gaussCoefficient_prime {p : ℕ} [NeZero p] (hp : p.Prime) (m : ℕ) :
    gaussCoefficient (1:DirichletCharacter ℂ p) 1 m =
      (if p∣m then (p:ℂ)-1 else -1)/((p:ℂ)-1)^2 := by
  have ht : (p.totient:ℂ)=(p:ℂ)-1 := by
    rw [Nat.totient_prime hp,Nat.cast_sub hp.one_lt.le,Nat.cast_one]
  unfold gaussCoefficient
  simp only [one_mul,inv_one,principal_gauss_standard_eq_moebius,principal_gauss_neg_shift_eq,
    principal_prime_gauss_shift hp,ht,moebiusComplex,moebius_apply_prime hp,Int.cast_neg,Int.cast_one,
    neg_mul_neg,one_mul]

/-- The ordinary absolute Euler factor at a prime for the Goldbach series. -/
theorem principal_absolute_euler_factor_prime {p : ℕ} [NeZero p] (hp : p.Prime) (m : ℕ) :
    1+‖gaussCoefficient (1:DirichletCharacter ℂ p) 1 m‖ =
      if p∣m then 1+1/((p:ℝ)-1) else 1+1/((p:ℝ)-1)^2 := by
  have hRe : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hpos : 0<(p:ℝ)-1 := sub_pos.mpr hRe
  have he : ‖(p:ℂ)-1‖=(p:ℝ)-1 := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hpos]
  rw [principal_gaussCoefficient_prime hp,norm_div,norm_pow,he]
  split_ifs
  · rw [he]
    field_simp
  · simp

end Conjectures.Goldbach.TwistedGoldbachSingularSeries

namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter Complex ArithmeticFunction
open scoped BigOperators Classical ArithmeticFunction.zeta
open B13BilateralVaughanReductionProof.DyadicMixedB4MoebiusGauss

theorem principalCoefficient_eq_gauss {q : ℕ} [NeZero q] (m : ℕ) :
    coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m q =
      gaussCoefficient (1:DirichletCharacter ℂ q) 1 m := by
  simp [coefficient,NeZero.ne,map_one]

private theorem principal_gaussCoefficient_one (m : ℕ) :
    gaussCoefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m = 1 := by
  have hm : -(m:ZMod 1)=1 := Subsingleton.elim _ _
  unfold gaussCoefficient
  simp [hm,AddChar.mulShift_one,principal_gauss_standard_eq_moebius,moebiusComplex]

private noncomputable def principalAbsArithmetic (m : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun q => ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m q‖,by simp [coefficient]⟩

private theorem principalAbsArithmetic_apply (m q : ℕ) :
    principalAbsArithmetic m q = ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m q‖ := rfl

private theorem principalAbsArithmetic_mult (m : ℕ) :
    (principalAbsArithmetic m).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨?_,?_⟩
  · rw [principalAbsArithmetic_apply,principalCoefficient_eq_gauss,principal_gaussCoefficient_one,norm_one]
  · intro q r hq hr h
    let : NeZero q := ⟨hq⟩
    let : NeZero r := ⟨hr⟩
    simp only [principalAbsArithmetic_apply,principalCoefficient_eq_gauss,principal_gaussCoefficient_mul h,norm_mul]

private theorem principalAbsArithmetic_prime_power_zero {p : ℕ} (hp : p.Prime)
    (m j : ℕ) (hj : 2≤j) : principalAbsArithmetic m (p^j)=0 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hnsq : ¬Squarefree (p^j) := by
    intro hs
    have hdiv : p*p∣p^j := by
      rw [← pow_two,show j=2+(j-2) by omega,pow_add]
      exact dvd_mul_right _ _
    exact hp.ne_one (Nat.isUnit_iff.mp (hs p hdiv))
  rw [principalAbsArithmetic_apply,principalCoefficient_eq_gauss,
    principal_gaussCoefficient_eq_zero_of_not_squarefree hnsq,norm_zero]

private theorem principalAbsArithmetic_sum_prime_power {p : ℕ} (hp : p.Prime)
    (m k : ℕ) (hk : k≠0) :
    (∑ d ∈ (p^k).divisors,principalAbsArithmetic m d) = 1+principalAbsArithmetic m p := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [Nat.sum_divisors_prime_pow hp]
  simp only [Nat.succ_eq_add_one]
  rw [Finset.sum_range_succ',Finset.sum_range_succ']
  have htail : (∑ j ∈ range k,principalAbsArithmetic m (p^(j+1+1)))=0 :=
    sum_eq_zero (fun j _ => principalAbsArithmetic_prime_power_zero hp m _ (by omega))
  rw [htail,pow_zero,pow_one,(principalAbsArithmetic_mult m).map_one]
  ring

/-- The finite ordinary absolute divisor sum is the product of its explicit
prime factors, with all higher prime powers already zero. -/
theorem ordinary_absolute_divisor_product (q m : ℕ) (hq : q≠0) :
    (∑ d ∈ q.divisors,‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d‖) =
      ∏ p ∈ q.primeFactors, if p∣m then 1+1/((p:ℝ)-1) else 1+1/((p:ℝ)-1)^2 := by
  let f := principalAbsArithmetic m
  let g := f*(ζ:ArithmeticFunction ℝ)
  have hg : g.IsMultiplicative :=
    (principalAbsArithmetic_mult m).mul ArithmeticFunction.isMultiplicative_zeta.natCast
  change (∑ d ∈ q.divisors,f d)=_
  rw [← coe_mul_zeta_apply]
  change g q=_
  rw [hg.multiplicative_factorization g hq,Nat.prod_factorization_eq_prod_primeFactors]
  apply prod_congr rfl
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  let : NeZero p := ⟨hpr.ne_zero⟩
  have hk : q.factorization p≠0 := by
    have he : p ∈ q.factorization.support := by simpa only [Nat.support_factorization] using hp
    exact Finsupp.mem_support_iff.mp he
  change (f*(ζ:ArithmeticFunction ℝ)) (p^q.factorization p)=_
  rw [coe_mul_zeta_apply]
  change (∑ d ∈ (p^q.factorization p).divisors,principalAbsArithmetic m d)=_
  rw [principalAbsArithmetic_sum_prime_power hpr m _ hk,principalAbsArithmetic_apply,principalCoefficient_eq_gauss]
  exact principal_absolute_euler_factor_prime hpr m

private noncomputable def principalAbsCoprimeArithmetic (L m : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if L.Coprime n then principalAbsArithmetic m n else 0,by simp⟩

private theorem principalAbsCoprimeArithmetic_mult (L m : ℕ) :
    (principalAbsCoprimeArithmetic L m).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨?_,?_⟩
  · change (if L.Coprime 1 then principalAbsArithmetic m 1 else 0)=1
    simp [(principalAbsArithmetic_mult m).map_one]
  · intro q r _ _ h
    change (if L.Coprime (q*r) then principalAbsArithmetic m (q*r) else 0) =
      (if L.Coprime q then principalAbsArithmetic m q else 0) *
        (if L.Coprime r then principalAbsArithmetic m r else 0)
    simp only [Nat.coprime_mul_iff_right,(principalAbsArithmetic_mult m).map_mul_of_coprime h]
    by_cases hq : L.Coprime q
    · by_cases hr : L.Coprime r
      · rw [ite_eq_left (show L.Coprime q ∧ L.Coprime r from ⟨hq,hr⟩),
          ite_eq_left hq,ite_eq_left hr]
      · rw [ite_eq_right (fun h : L.Coprime q ∧ L.Coprime r => hr h.2),
          ite_eq_left hq,ite_eq_right hr,mul_zero]
    · rw [ite_eq_right (fun h : L.Coprime q ∧ L.Coprime r => hq h.1),
        ite_eq_right hq,zero_mul]

private theorem principalAbsCoprime_sum_prime_power {p : ℕ} (hp : p.Prime)
    (L m k : ℕ) (hk : k≠0) :
    (∑ d ∈ (p^k).divisors,principalAbsCoprimeArithmetic L m d) =
      if L.Coprime p then 1+principalAbsArithmetic m p else 1 := by
  by_cases hLp : L.Coprime p
  · rw [ite_eq_left hLp,← principalAbsArithmetic_sum_prime_power hp m k hk]
    apply sum_congr rfl
    intro d hd
    have hLd := (hLp.pow_right k).coprime_dvd_right (Nat.dvd_of_mem_divisors hd)
    change (if L.Coprime d then principalAbsArithmetic m d else 0) = _
    rw [ite_eq_left hLd]
  · rw [ite_eq_right hLp,Nat.sum_divisors_prime_pow hp,sum_eq_single 0]
    · simp [principalAbsCoprimeArithmetic,(principalAbsArithmetic_mult m).map_one]
    · intro j _ hj
      have hbad : ¬L.Coprime (p^j) := fun h => hLp
        (h.coprime_dvd_right (dvd_pow_self p hj))
      change (if L.Coprime (p^j) then principalAbsArithmetic m (p^j) else 0)=0
      rw [ite_eq_right hbad]
    · intro h
      exact (h (mem_range.mpr (Nat.succ_pos k))).elim

/-- The finite ordinary absolute sum restricted to moduli coprime to a
given level omits precisely that level's prime factors. -/
theorem ordinary_absolute_coprime_divisor_product (L q m : ℕ) (hq : q≠0) :
    (∑ d ∈ q.divisors.filter (fun d => L.Coprime d),
      ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d‖) =
      ∏ p ∈ q.primeFactors, if L.Coprime p then
        (if p∣m then 1+1/((p:ℝ)-1) else 1+1/((p:ℝ)-1)^2) else 1 := by
  let f := principalAbsCoprimeArithmetic L m
  let g := f*(ζ:ArithmeticFunction ℝ)
  have hg : g.IsMultiplicative :=
    (principalAbsCoprimeArithmetic_mult L m).mul ArithmeticFunction.isMultiplicative_zeta.natCast
  rw [sum_filter]
  change (∑ d ∈ q.divisors,f d)=_
  rw [← coe_mul_zeta_apply]
  change g q=_
  rw [hg.multiplicative_factorization g hq,Nat.prod_factorization_eq_prod_primeFactors]
  apply prod_congr rfl
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  let : NeZero p := ⟨hpr.ne_zero⟩
  have hk : q.factorization p≠0 := by
    have he : p ∈ q.factorization.support := by simpa only [Nat.support_factorization] using hp
    exact Finsupp.mem_support_iff.mp he
  change (f*(ζ:ArithmeticFunction ℝ)) (p^q.factorization p)=_
  rw [coe_mul_zeta_apply]
  change (∑ d ∈ (p^q.factorization p).divisors,principalAbsCoprimeArithmetic L m d)=_
  rw [principalAbsCoprime_sum_prime_power hpr L m _ hk,principalAbsArithmetic_apply,
    principalCoefficient_eq_gauss,principal_absolute_euler_factor_prime hpr]

end Conjectures.Goldbach.TwistedGoldbachSingularSeries

namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter Complex
open scoped Classical BigOperators
open B13BilateralVaughanReductionProof
open B13BilateralVaughanReductionProof.DyadicMixedB4MoebiusGauss
open B13BilateralVaughanReductionProof.DyadicMixedB4ImprimitiveBound

theorem coefficient_of_dvd {r s d : ℕ} [NeZero d]
    (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s)
    (m : ℕ) (hr : r∣d) (hs : s∣d) :
    coefficient α β m d = gaussCoefficient (changeLevel hr α) (changeLevel hs β) m := by
  simp [coefficient,NeZero.ne,hr,hs]

theorem coefficient_eq_zero_of_not_lcm_dvd {r s d : ℕ}
    (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s)
    (m : ℕ) (h : ¬r.lcm s∣d) : coefficient α β m d=0 := by
  unfold coefficient
  split_ifs with hd h'
  · exact (h (Nat.lcm_dvd h'.1 h'.2)).elim
  all_goals rfl

/-- At frequency one, a lifted primitive Gauss sum vanishes when the
quotient modulus shares a prime with its primitive source level. -/
theorem gaussSum_lift_eq_zero_of_not_coprime_quotient {r d : ℕ} [NeZero r] [NeZero d]
    {α : DirichletCharacter ℂ r} (hα : α.IsPrimitive) (hr : r∣d)
    (hbad : ¬(d/r).Coprime r) :
    gaussSum (changeLevel hr α) ZMod.stdAddChar=0 := by
  rw [← AddChar.mulShift_one (ZMod.stdAddChar : AddChar (ZMod d) ℂ),
    ← Nat.cast_one, sum_inducedGauss_moebius]
  apply sum_eq_zero
  intro e he
  have hNo : ¬(e.Coprime r ∧ (d/e/r)∣1) := by
    intro hh
    obtain ⟨_,_,hprod⟩ := conductor_cofactor hr he hh.1
    rw [Nat.dvd_one.mp hh.2,mul_one] at hprod
    apply hbad
    rw [← hprod,mul_comm e r,Nat.mul_div_cancel_left e (NeZero.pos r)]
    exact hh.1
  apply norm_eq_zero.mp
  have hb := norm_induced_gauss_term hr he 1 hα
  rw [ite_eq_right hNo] at hb
  exact le_antisymm hb (norm_nonneg _)

private theorem coprime_lcm_right {k r s : ℕ} (hr : k.Coprime r) (hs : k.Coprime s) :
    k.Coprime (r.lcm s) :=
  (hr.mul_right hs).coprime_dvd_right (Nat.lcm_dvd (dvd_mul_right r s) (dvd_mul_left s r))

/-- The remaining multiplier of the common conductor is coprime to it
whenever the fixed-pair coefficient can be nonzero. -/
theorem coefficient_eq_zero_of_not_coprime_lcm_quotient {r s d : ℕ}
    [NeZero r] [NeZero s] [NeZero d]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ)
    (hd : r.lcm s∣d) (hbad : ¬(d/(r.lcm s)).Coprime (r.lcm s)) :
    coefficient α β m d=0 := by
  have hrL : r∣r.lcm s := Nat.dvd_lcm_left _ _
  have hsL : s∣r.lcm s := Nat.dvd_lcm_right _ _
  have hr := hrL.trans hd
  have hs := hsL.trans hd
  have hkr : d/(r.lcm s)∣d/r := (Nat.dvd_div_iff_mul_dvd hr).mpr (by
    have hh := Nat.mul_dvd_mul_right hrL (d/(r.lcm s))
    rw [Nat.mul_div_cancel' hd] at hh
    simpa [mul_comm] using hh)
  have hks : d/(r.lcm s)∣d/s := (Nat.dvd_div_iff_mul_dvd hs).mpr (by
    have hh := Nat.mul_dvd_mul_right hsL (d/(r.lcm s))
    rw [Nat.mul_div_cancel' hd] at hh
    simpa [mul_comm] using hh)
  rw [coefficient_of_dvd α β m hr hs]
  unfold gaussCoefficient
  by_cases hrc : (d/r).Coprime r
  · have hsc : ¬(d/s).Coprime s := fun hsc => hbad
      (coprime_lcm_right (hrc.coprime_dvd_left hkr) (hsc.coprime_dvd_left hks))
    rw [gaussSum_lift_eq_zero_of_not_coprime_quotient hβ hs hsc,mul_zero,zero_mul,zero_div]
  · rw [gaussSum_lift_eq_zero_of_not_coprime_quotient hα hr hrc,zero_mul,zero_mul,zero_div]

/-- The fixed pair factors through its common conductor and the ordinary
principal coefficient of a coprime multiplier. -/
theorem coefficient_lcm_mul_coprime {r s k : ℕ} [NeZero r] [NeZero s] [NeZero k]
    (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ)
    (hk : (r.lcm s).Coprime k) :
    coefficient α β m ((r.lcm s)*k) =
      coefficient α β m (r.lcm s) * gaussCoefficient (1:DirichletCharacter ℂ k) 1 m := by
  let L := r.lcm s
  let : NeZero L := ⟨Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s)⟩
  have hrL : r∣L := Nat.dvd_lcm_left _ _
  have hsL : s∣L := Nat.dvd_lcm_right _ _
  have hd : L∣L*k := dvd_mul_right _ _
  have hα : changeLevel (hrL.trans hd) α =
      crtCharacter (changeLevel hrL α) (1:DirichletCharacter ℂ k) := by
    simp only [crtCharacter,map_one,mul_one]
    exact changeLevel_trans α hrL hd
  have hβ : changeLevel (hsL.trans hd) β =
      crtCharacter (changeLevel hsL β) (1:DirichletCharacter ℂ k) := by
    simp only [crtCharacter,map_one,mul_one]
    exact changeLevel_trans β hsL hd
  change coefficient α β m (L*k)=coefficient α β m L*_
  rw [coefficient_of_dvd α β m hrL hsL,coefficient_of_dvd α β m (hrL.trans hd) (hsL.trans hd),
    hα,hβ,gaussCoefficient_crtCharacter hk]

end Conjectures.Goldbach.TwistedGoldbachSingularSeries

namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter Filter Complex
open scoped Classical BigOperators Topology

/-- At any containing modulus, all surviving fixed-pair denominator terms
are indexed exactly by coprime divisors of the remaining quotient. -/
theorem fixed_pair_absolute_divisor_sum {r s q : ℕ} [NeZero r] [NeZero s] [NeZero q]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hq : r.lcm s∣q) :
    (∑ d ∈ q.divisors,‖coefficient α β m d‖) =
      ‖coefficient α β m (r.lcm s)‖ *
        ∑ k ∈ (q/(r.lcm s)).divisors.filter (fun k => (r.lcm s).Coprime k),
          ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m k‖ := by
  let L := r.lcm s
  have hL : 0<L := Nat.pos_of_ne_zero (Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s))
  let : NeZero L := ⟨hL.ne'⟩
  let D := q.divisors.filter (fun d => L∣d ∧ L.Coprime (d/L))
  let K := (q/L).divisors.filter (fun k => L.Coprime k)
  have hz : q/L≠0 := (Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hq) hL).ne'
  have hImage : K.image (fun k => L*k)=D := by
    ext d
    constructor
    · intro hd
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hd
      have hk' := mem_filter.mp hk
      have hdv : L*k∣q := by
        have hh := Nat.mul_dvd_mul_left L (Nat.mem_divisors.mp hk'.1).1
        rwa [Nat.mul_div_cancel' hq] at hh
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdv,NeZero.ne q⟩,
        dvd_mul_right _ _,by rw [Nat.mul_div_cancel_left k hL]; exact hk'.2⟩
    · intro hd
      have hh := mem_filter.mp hd
      refine mem_image.mpr ⟨d/L,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_,hz⟩,hh.2.2⟩,
        Nat.mul_div_cancel' hh.2.1⟩
      apply (Nat.dvd_div_iff_mul_dvd hq).mpr
      change L*(d/L)∣q
      rw [Nat.mul_div_cancel' hh.2.1]
      exact (Nat.mem_divisors.mp hh.1).1
  have hSum : (∑ d ∈ D,‖coefficient α β m d‖) = ∑ d ∈ q.divisors,‖coefficient α β m d‖ := by
    apply sum_subset (filter_subset _ _)
    intro d hd hnd
    let : NeZero d := ⟨(Nat.pos_of_mem_divisors hd).ne'⟩
    have hbad : ¬(L∣d ∧ L.Coprime (d/L)) := fun h => hnd (mem_filter.mpr ⟨hd,h⟩)
    by_cases hLdiv : L∣d
    · have hc : ¬(d/L).Coprime L := fun h => hbad ⟨hLdiv,h.symm⟩
      rw [coefficient_eq_zero_of_not_coprime_lcm_quotient hα hβ m hLdiv hc,norm_zero]
    · rw [coefficient_eq_zero_of_not_lcm_dvd α β m hLdiv,norm_zero]
  change (∑ d ∈ q.divisors,‖coefficient α β m d‖) =
    ‖coefficient α β m L‖*∑ k ∈ K,‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m k‖
  rw [← hSum,← hImage,sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hL h),mul_sum]
  apply sum_congr rfl
  intro k hk
  obtain ⟨hk',hkc⟩ := mem_filter.mp hk
  let : NeZero k := ⟨(Nat.pos_of_mem_divisors hk').ne'⟩
  rw [coefficient_lcm_mul_coprime α β m hkc,norm_mul,principalCoefficient_eq_gauss]

private theorem factorial_divisors_limit {f : ℕ → ℝ} (hf : Summable f) (h0 : f 0=0)
    (L : ℕ) (hL : L≠0) :
    Tendsto (fun n : ℕ => ∑ d ∈ (L*n.factorial).divisors, f d) atTop (𝓝 (∑' d, f d)) := by
  have hc : Tendsto (fun n : ℕ => insert 0 (L*n.factorial).divisors) atTop atTop := by
    apply tendsto_atTop.2
    intro S
    filter_upwards [eventually_ge_atTop (S.sup id)] with n hn
    intro d hd
    by_cases h : d=0
    · simp [h]
    apply mem_insert_of_mem
    have hdn : d≤n := (S.le_sup (f:=id) hd).trans hn
    exact Nat.mem_divisors.mpr ⟨(Nat.dvd_factorial (Nat.pos_of_ne_zero h) hdn).trans
      (dvd_mul_left n.factorial L),mul_ne_zero hL n.factorial_ne_zero⟩
  apply (hf.hasSum.comp hc).congr'
  filter_upwards with n
  simp [h0]

/-- The exact infinite absolute mass of a fixed primitive pair is its common
conductor coefficient times the ordinary absolute mass over coprime terms. -/
theorem fixed_pair_absolute_total_eq {r s : ℕ} [NeZero r] [NeZero s]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) :
    (∑' d : ℕ, ‖coefficient α β m d‖) =
      ‖coefficient α β m (r.lcm s)‖ *
        (∑' k : ℕ, if (r.lcm s).Coprime k then ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m k‖ else 0) := by
  let L := r.lcm s
  have hL : L≠0 := Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s)
  let g := fun k : ℕ => if L.Coprime k then ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m k‖ else 0
  have hg : Summable g := by
    apply Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
      (summable_coefficients (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m hm)
    · dsimp only [g]
      split_ifs <;> positivity
    · dsimp only [g]
      split_ifs <;> first | exact le_rfl | exact norm_nonneg _
  have hleft := factorial_divisors_limit (summable_coefficients α β m hm) (by simp [coefficient]) L hL
  have hright := (factorial_divisors_limit hg (by simp [g,coefficient]) 1 one_ne_zero).const_mul
    ‖coefficient α β m L‖
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards with n
  let : NeZero (L*n.factorial) := ⟨mul_ne_zero hL n.factorial_ne_zero⟩
  have he := fixed_pair_absolute_divisor_sum (q:=L*n.factorial) hα hβ m (dvd_mul_right _ _)
  rw [Nat.mul_div_cancel_left n.factorial (Nat.pos_of_ne_zero hL),sum_filter] at he
  simpa only [L,g,one_mul] using he.symm


/-- Splitting off all primes of a fixed level gives an exact finite
factorization of the ordinary absolute mass. -/
theorem ordinary_absolute_divisor_factorization {L q : ℕ} (hL : L≠0) (hq : q≠0)
    (hLq : L∣q) (m : ℕ) :
    (∑ d ∈ q.divisors,‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d‖) =
      (∑ d ∈ L.divisors,‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d‖) *
      (∑ d ∈ q.divisors.filter (fun d => L.Coprime d),
        ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d‖) := by
  let A (p : ℕ) : ℝ := if p∣m then 1+1/((p:ℝ)-1) else 1+1/((p:ℝ)-1)^2
  rw [ordinary_absolute_divisor_product q m hq,ordinary_absolute_divisor_product L m hL,
    ordinary_absolute_coprime_divisor_product L q m hq]
  change (∏ p ∈ q.primeFactors,A p) =
    (∏ p ∈ L.primeFactors,A p)*(∏ p ∈ q.primeFactors,if L.Coprime p then A p else 1)
  have hsmall : L.primeFactors⊆q.primeFactors := Nat.primeFactors_mono hLq hq
  have hF : q.primeFactors.filter (fun p => ¬ L.Coprime p) = L.primeFactors := by
    ext p
    rw [mem_filter]
    constructor
    · rintro ⟨hp,hp'⟩
      have hpr := Nat.prime_of_mem_primeFactors hp
      rw [Nat.coprime_comm,hpr.coprime_iff_not_dvd,not_not] at hp'
      have hpd : p ∣ L := hp'
      exact Nat.mem_primeFactors.mpr ⟨hpr,hpd,hL⟩
    · intro hp
      have ⟨hpr,hpd,_⟩ := Nat.mem_primeFactors.mp hp
      exact ⟨hsmall hp,fun hh => (hpr.coprime_iff_not_dvd.mp hh.symm) hpd⟩
  rw [← Finset.prod_filter,← hF,mul_comm,Finset.prod_filter_mul_prod_filter_not]


/-- The ordinary relative product with a fixed level omitted. -/
theorem ordinary_absolute_total_factorization (L : ℕ) (hL : L≠0) (m : ℕ) (hm : 0 < m) :
    (∑' d : ℕ, ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d‖) =
      (∑ d ∈ L.divisors, ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d‖) *
        (∑' k : ℕ, if L.Coprime k then
          ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m k‖ else 0) := by
  let f := fun d : ℕ => ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d‖
  let g := fun d : ℕ => if L.Coprime d then f d else 0
  have hf : Summable f := summable_coefficients _ _ m hm
  have h0 : f 0=0 := by simp [f,coefficient]
  have hg : Summable g := by
    apply Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) hf
    · dsimp only [g]
      split_ifs <;> positivity
    · dsimp only [g]
      split_ifs <;> first | exact le_rfl | exact norm_nonneg _
  have hleft := factorial_divisors_limit hf h0 L hL
  have hright := (factorial_divisors_limit hg (by simp [g,h0]) L hL).const_mul
    (∑ d ∈ L.divisors,f d)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards with n
  have he := ordinary_absolute_divisor_factorization hL (mul_ne_zero hL n.factorial_ne_zero)
    (dvd_mul_right L n.factorial) m
  rw [sum_filter] at he
  exact he.symm

/-- Relative absolute total for a fixed primitive pair. The ordinary
Euler factors at primes in its common conductor are replaced by one finite
twisted coefficient. -/
theorem fixed_pair_relative_absolute_total {r s : ℕ} [NeZero r] [NeZero s]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) :
    (∑' d : ℕ,‖coefficient α β m d‖) *
      (∏ p ∈ (r.lcm s).primeFactors,
        if p∣m then 1+1/((p:ℝ)-1) else 1+1/((p:ℝ)-1)^2) =
      ‖coefficient α β m (r.lcm s)‖ *
        (∑' d : ℕ, ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d‖) := by
  have hL : r.lcm s≠0 := Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s)
  rw [← ordinary_absolute_divisor_product (r.lcm s) m hL,
    fixed_pair_absolute_total_eq hα hβ m hm,ordinary_absolute_total_factorization (r.lcm s) hL m hm]
  ring

theorem ordinary_absolute_relative_factor_pos (L m : ℕ) :
    0 < ∏ p ∈ L.primeFactors,
      if p∣m then 1+1/((p:ℝ)-1) else 1+1/((p:ℝ)-1)^2 := by
  apply Finset.prod_pos
  intro p hp
  have hp' : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hpos := sub_pos.mpr hp'
  split_ifs <;> positivity

/-- Relative absolute total, normalized by the positive local product of
the ordinary coefficients. -/
theorem fixed_pair_relative_absolute_total_div {r s : ℕ} [NeZero r] [NeZero s]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) :
    (∑' d : ℕ,‖coefficient α β m d‖) =
      (‖coefficient α β m (r.lcm s)‖ /
        (∏ p ∈ (r.lcm s).primeFactors,
          if p∣m then 1+1/((p:ℝ)-1) else 1+1/((p:ℝ)-1)^2)) *
        (∑' d : ℕ, ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d‖) := by
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (ordinary_absolute_relative_factor_pos (r.lcm s) m).ne').mpr
  exact fixed_pair_relative_absolute_total hα hβ m hm

end Conjectures.Goldbach.TwistedGoldbachSingularSeries

namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open DirichletCharacter
open scoped Classical

private def crtUnitEquiv {q r : ℕ} (h : q.Coprime r) :
    (ZMod (q*r))ˣ ≃* (ZMod q)ˣ × (ZMod r)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans (MulEquiv.prodUnits)

private theorem crtUnitEquiv_fst {q r : ℕ} (h : q.Coprime r) (u : (ZMod (q*r))ˣ) :
    (((crtUnitEquiv h u).1 : (ZMod q)ˣ):ZMod q) = (ZMod.chineseRemainder h (u:ZMod (q*r))).1 := rfl

private theorem crtUnitEquiv_snd {q r : ℕ} (h : q.Coprime r) (u : (ZMod (q*r))ˣ) :
    (((crtUnitEquiv h u).2 : (ZMod r)ˣ):ZMod r) = (ZMod.chineseRemainder h (u:ZMod (q*r))).2 := rfl

noncomputable def crtLeftCharacter {q r : ℕ} (h : q.Coprime r)
    (A : DirichletCharacter ℂ (q*r)) : DirichletCharacter ℂ q :=
  MulChar.ofUnitHom (A.toUnitHom.comp ((crtUnitEquiv h).symm.toMonoidHom.comp
    (MonoidHom.inl (ZMod q)ˣ (ZMod r)ˣ)))

noncomputable def crtRightCharacter {q r : ℕ} (h : q.Coprime r)
    (A : DirichletCharacter ℂ (q*r)) : DirichletCharacter ℂ r :=
  MulChar.ofUnitHom (A.toUnitHom.comp ((crtUnitEquiv h).symm.toMonoidHom.comp
    (MonoidHom.inr (ZMod q)ˣ (ZMod r)ˣ)))

private theorem crtLeftCharacter_apply {q r : ℕ} (h : q.Coprime r)
    (A : DirichletCharacter ℂ (q*r)) (u : (ZMod q)ˣ) :
    crtLeftCharacter h A u = A (((crtUnitEquiv h).symm (u,1)):ZMod (q*r)) := by
  simp only [crtLeftCharacter,MulChar.ofUnitHom_coe,MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom,MonoidHom.inl_apply,MulChar.coe_toUnitHom]

private theorem crtRightCharacter_apply {q r : ℕ} (h : q.Coprime r)
    (A : DirichletCharacter ℂ (q*r)) (v : (ZMod r)ˣ) :
    crtRightCharacter h A v = A (((crtUnitEquiv h).symm (1,v)):ZMod (q*r)) := by
  simp only [crtRightCharacter,MulChar.ofUnitHom_coe,MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom,MonoidHom.inr_apply,MulChar.coe_toUnitHom]

/-- Every character splits canonically through the CRT projections. -/
theorem crtCharacter_factor {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r)
    (A : DirichletCharacter ℂ (q*r)) :
    crtCharacter (crtLeftCharacter h A) (crtRightCharacter h A) = A := by
  apply MulChar.ext
  intro u
  rw [crtCharacter_apply h,← crtUnitEquiv_fst h u,← crtUnitEquiv_snd h u,
    crtLeftCharacter_apply,crtRightCharacter_apply,← map_mul,← Units.val_mul,← map_mul]
  have hpair : ((crtUnitEquiv h u).1,1)*((1,(crtUnitEquiv h u).2)) = crtUnitEquiv h u := by
    exact Prod.ext (mul_one _) (one_mul _)
  rw [hpair,MulEquiv.symm_apply_apply]


theorem crtLeftCharacter_crtCharacter {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    crtLeftCharacter h (crtCharacter χ ψ) = χ := by
  apply MulChar.ext
  intro u
  rw [crtLeftCharacter_apply,crtCharacter_apply h,
    ← crtUnitEquiv_fst h,← crtUnitEquiv_snd h, MulEquiv.apply_symm_apply]
  simp

theorem crtRightCharacter_crtCharacter {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    crtRightCharacter h (crtCharacter χ ψ) = ψ := by
  apply MulChar.ext
  intro v
  rw [crtRightCharacter_apply,crtCharacter_apply h,
    ← crtUnitEquiv_fst h,← crtUnitEquiv_snd h, MulEquiv.apply_symm_apply]
  simp

/-- Inflation commutes with CRT because both projections are natural. -/
theorem crtCharacter_changeLevel {q r q' r' : ℕ}
    (hq : q∣q') (hr : r∣r') (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    changeLevel (Nat.mul_dvd_mul hq hr) (crtCharacter χ ψ) =
      crtCharacter (changeLevel hq χ) (changeLevel hr ψ) := by
  simp only [crtCharacter,map_mul,← changeLevel_trans]

/-- The conductor factors exactly through coprime CRT pieces. -/
theorem conductor_crtCharacter {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    (crtCharacter χ ψ).conductor = χ.conductor*ψ.conductor := by
  letI : NeZero (q*r) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
  let A := crtCharacter χ ψ
  let c := A.conductor
  have hcd : c ∣ q*r := A.conductor_dvd_level
  have hc₀ : c ≠ 0 := fun hc => NeZero.ne (q*r) (conductor_eq_zero_iff_level_eq_zero.mp hc)
  letI : NeZero c := ⟨hc₀⟩
  have hχ := χ.conductor_dvd_level
  have hψ := ψ.conductor_dvd_level
  have hup : c ∣ χ.conductor*ψ.conductor := by
    apply conductor_dvd_of_mem_conductorSet
    refine ⟨Nat.mul_dvd_mul hχ hψ,crtCharacter χ.primitiveCharacter ψ.primitiveCharacter,?_⟩
    rw [crtCharacter_changeLevel hχ hψ,changeLevel_primitiveCharacter,changeLevel_primitiveCharacter]
  let g := c.gcd q
  let k := c.gcd r
  have hg : g∣q := Nat.gcd_dvd_right c q
  have hk : k∣r := Nat.gcd_dvd_right c r
  have hcop : g.Coprime k := h.of_dvd_left hg |>.of_dvd_right hk
  have he : g*k=c := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hcd
  have hA : A.FactorsThrough (g*k) := by
    rw [he]
    exact A.factorsThrough_conductor
  letI : NeZero g := ⟨fun hz => hc₀ (by rw [← he,hz,zero_mul])⟩
  letI : NeZero k := ⟨fun hz => hc₀ (by rw [← he,hz,mul_zero])⟩
  obtain ⟨_,θ,hθ⟩ := hA
  change A = changeLevel (Nat.mul_dvd_mul hg hk) θ at hθ
  nth_rewrite 1 [← crtCharacter_factor hcop θ] at hθ
  rw [crtCharacter_changeLevel hg hk] at hθ
  have hleft := congrArg (crtLeftCharacter h) hθ
  have hright := congrArg (crtRightCharacter h) hθ
  change crtLeftCharacter h (crtCharacter χ ψ) =
    crtLeftCharacter h (crtCharacter _ _) at hleft
  change crtRightCharacter h (crtCharacter χ ψ) =
    crtRightCharacter h (crtCharacter _ _) at hright
  rw [crtLeftCharacter_crtCharacter,crtLeftCharacter_crtCharacter] at hleft
  rw [crtRightCharacter_crtCharacter,crtRightCharacter_crtCharacter] at hright
  apply Nat.dvd_antisymm hup
  rw [← he]
  exact Nat.mul_dvd_mul
    (conductor_dvd_of_mem_conductorSet χ ⟨hg,_,hleft⟩)
    (conductor_dvd_of_mem_conductorSet ψ ⟨hk,_,hright⟩)

theorem crtCharacter_mul {q r : ℕ} (A C : DirichletCharacter ℂ q)
    (B D : DirichletCharacter ℂ r) :
    crtCharacter A B * crtCharacter C D = crtCharacter (A*C) (B*D) := by
  simp only [crtCharacter,map_mul]
  ac_rfl

theorem crtCharacter_inv {q r : ℕ} (A : DirichletCharacter ℂ q)
    (B : DirichletCharacter ℂ r) :
    (crtCharacter A B)⁻¹ = crtCharacter A⁻¹ B⁻¹ := by
  simp [crtCharacter,mul_comm]

end Conjectures.Goldbach.TwistedGoldbachSingularSeries

namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter
open scoped BigOperators Classical
open B13BilateralVaughanReductionProof
open DyadicMixedB4MoebiusGauss DyadicMixedB4ImprimitiveBound
open DyadicMixedB4CharacterFactorBound

theorem prime_divisor_power_of_ne_one {p n d : ℕ} (hp : p.Prime)
    (hd : d ∣ p^n) (hd₁ : d ≠ 1) : p ∣ d := by
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hj₀ : j ≠ 0 := by rintro rfl; exact hd₁ (pow_zero p)
  exact dvd_pow_self p hj₀

/-- A nontrivial conductor at a prime power introduces no additional
Möbius terms. This saves its square root without an ambient-level loss. -/
theorem norm_gauss_prime_power_conductor {p n : ℕ} (hp : p.Prime) [NeZero (p^n)]
    (χ : DirichletCharacter ℂ (p^n)) (hc : χ.conductor ≠ 1) (m : ℕ) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(m : ZMod (p^n))))‖ ≤
      (p^n : ℝ) / Real.sqrt χ.conductor := by
  let c := χ.conductor
  letI : NeZero c := ⟨fun h => NeZero.ne (p^n) (conductor_eq_zero_iff_level_eq_zero.mp h)⟩
  have hd := χ.conductor_dvd_level
  have hpc : p ∣ c := prime_divisor_power_of_ne_one hp hd hc
  apply (norm_gauss_neg_shift_le χ _).trans
  nth_rewrite 1 [← χ.changeLevel_primitiveCharacter]
  rw [sum_inducedGauss_moebius]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun e he =>
    norm_induced_gauss_term hd he m χ.primitiveCharacter_isPrimitive).trans ?_)
  rw [sum_eq_single 1]
  · simp only [Nat.div_one]
    have hcast : ((p^n / c : ℕ) : ℝ) * (c : ℝ) = (p^n : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel hd
    have hs : 0 < Real.sqrt (c : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos c)
    have htarget : ((p^n / c : ℕ) : ℝ) * Real.sqrt (c : ℝ) =
        (p^n : ℝ) / Real.sqrt (c : ℝ) := by
      apply (eq_div_iff hs.ne').2
      rw [mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg c),hcast]
    split_ifs
    · exact htarget.le
    · positivity
  · intro e he hne
    have hpe := prime_divisor_power_of_ne_one hp (Nat.dvd_of_mem_divisors he) hne
    have hnot : ¬ e.Coprime c := fun h => hp.ne_one
      (Nat.eq_one_of_dvd_coprimes h hpe hpc)
    exact ite_eq_right (fun h => hnot h.1)
  · exact fun h => False.elim (h (Nat.one_mem_divisors.mpr (NeZero.ne _)))

theorem principal_gauss_prime_shift {p : ℕ} [NeZero p] (hp : p.Prime) (m : ℕ) :
    gaussSum (1:DirichletCharacter ℂ p) (ZMod.stdAddChar.mulShift (m:ZMod p)) =
      if p ∣ m then (p:ℂ)-1 else -1 := by
  open DyadicMixedB4Ramanujan in
  rw [← ramanujan_natural_gauss hp.one_lt,ramanujan_moebius hp.one_lt,hp.divisors,
    sum_insert (by simpa using hp.ne_one.symm),sum_singleton]
  simp [moebiusComplex,ArithmeticFunction.moebius_apply_prime hp,Nat.div_self hp.pos]
  split_ifs <;> ring

theorem principal_lifted_prime_gauss {p j : ℕ} [NeZero p] [NeZero (p^j)]
    [NeZero (p*p^j)] (m : ℕ) :
    gaussSum (1:DirichletCharacter ℂ (p*p^j)) (ZMod.stdAddChar.mulShift (m:ZMod (p*p^j))) =
      if p^j ∣ m then (p^j:ℕ) * gaussSum (1:DirichletCharacter ℂ p)
        (ZMod.stdAddChar.mulShift ((m/(p^j):ℕ):ZMod p)) else 0 := by
  rw [DyadicMixedB4GaussLift.gaussSum_as_fraction_sum]
  have hchar (a : ℕ) : (1:DirichletCharacter ℂ (p*p^j)) (a:ZMod (p*p^j)) =
      (1:DirichletCharacter ℂ p) (a:ZMod p) := by
    by_cases h : a.Coprime p
    · have hc := Nat.coprime_mul_iff_right.mpr ⟨h,h.pow_right j⟩
      rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime _ _).mpr hc),
        MulChar.one_apply ((ZMod.isUnit_iff_coprime _ _).mpr h)]
    · rw [MulChar.map_nonunit _ (fun hu => h
        (Nat.coprime_mul_iff_right.mp ((ZMod.isUnit_iff_coprime _ _).mp hu)).1),
        MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime _ _).mp hu))]
  simp only [hchar,Nat.cast_mul]
  exact DyadicMixedB4GaussLift.lift_gaussSum (1:DirichletCharacter ℂ p) m

private theorem principal_gauss_prime_pow_nondividing {p j m : ℕ}
    (hp : p.Prime) [NeZero (p^(j+1))] (hm : ¬p ∣ m) :
    ‖gaussSum (1:DirichletCharacter ℂ (p^(j+1)))
      (ZMod.stdAddChar.mulShift (-(m:ZMod (p^(j+1)))))‖ ≤ 1 := by
  apply (norm_gauss_neg_shift_le _ _).trans
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hlocal (q : ℕ) [NeZero q] (hq : q = p*p^j) :
      ‖gaussSum (1:DirichletCharacter ℂ q) (ZMod.stdAddChar.mulShift (m:ZMod q))‖ ≤ 1 := by
    subst q
    letI : NeZero (p^j) := ⟨pow_ne_zero _ hp.ne_zero⟩
    rw [principal_lifted_prime_gauss]
    cases j with
    | zero =>
      simp [principal_gauss_prime_shift hp,hm]
    | succ j =>
      rw [ite_eq_right (fun h => hm ((dvd_pow_self p (by omega)).trans h)),norm_zero]
      norm_num
  exact hlocal _ (pow_succ' p j)

private theorem norm_gauss_one_le_totient {q : ℕ} [NeZero q] (x : ZMod q) :
    ‖gaussSum (1:DirichletCharacter ℂ q) (ZMod.stdAddChar.mulShift x)‖ ≤ (q.totient:ℝ) := by
  unfold gaussSum
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ a : ZMod q,
      ‖(1:DirichletCharacter ℂ q) a * ZMod.stdAddChar.mulShift x a‖ =
        if IsUnit a then (1:ℝ) else 0 := by
    intro a
    by_cases ha : IsUnit a
    · simp [ha,MulChar.one_apply ha,AddChar.norm_apply]
    · simp [ha,MulChar.map_nonunit _ ha]
  simp only [hterm]
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
  have hcard : ((Finset.univ : Finset (ZMod q)).filter IsUnit).card = q.totient := by
    rw [← ZMod.card_units_eq_totient,← Fintype.card_coe]
    exact Fintype.card_congr ⟨fun a => (mem_filter.mp a.2).2.unit,
      fun u => ⟨(u:ZMod q),mem_filter.mpr ⟨mem_univ _,u.isUnit⟩⟩,
      fun a => Subtype.ext (mem_filter.mp a.2).2.unit_spec,
      fun u => Units.ext u.isUnit.unit_spec⟩
  exact_mod_cast hcard.le

private theorem norm_standard_pair_le_level {q : ℕ} [NeZero q]
    (A B : DirichletCharacter ℂ q) :
    ‖gaussSum A ZMod.stdAddChar‖ * ‖gaussSum B ZMod.stdAddChar‖ ≤ (q:ℝ) := by
  have h (χ : DirichletCharacter ℂ q) : ‖gaussSum χ ZMod.stdAddChar‖ ≤ Real.sqrt q :=
    (norm_dirichlet_gauss_standard χ).trans (Real.sqrt_le_sqrt
      (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level))
  simpa only [Real.mul_self_sqrt (Nat.cast_nonneg q)] using
    mul_le_mul (h A) (h B) (norm_nonneg _) (Real.sqrt_nonneg _)

theorem norm_gaussCoefficient_le {q : ℕ} [NeZero q]
    (A B : DirichletCharacter ℂ q) (m : ℕ) :
    ‖gaussCoefficient A B m‖ ≤ (q:ℝ) *
      ‖gaussSum ((A*B)⁻¹) (ZMod.stdAddChar.mulShift (-(m:ZMod q)))‖ / (q.totient:ℝ)^2 := by
  unfold gaussCoefficient
  simp only [norm_div,norm_mul,norm_pow,Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (norm_standard_pair_le_level A B) (norm_nonneg _)) (sq_nonneg _)

theorem prime_power_totient_ratio {p j : ℕ} (hp : p.Prime) :
    ((p^(j+1):ℕ):ℝ) / ((p^(j+1)).totient:ℝ) = (p:ℝ)/((p:ℝ)-1) := by
  have hp₀ : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hp₁ : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  rw [Nat.totient_prime_pow_succ hp,Nat.cast_pow,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_sub hp.one_lt.le,Nat.cast_one,pow_succ]
  field_simp

/-- The local relative absolute factor incurs a correction only at primes
dividing the conductor of the product. -/
theorem prime_power_relative_absolute_le {p j : ℕ} (hp : p.Prime) [NeZero (p^(j+1))]
    (A B : DirichletCharacter ℂ (p^(j+1))) (m : ℕ) :
    ‖gaussCoefficient A B m‖ ≤
      (if p ∣ m then 1+1/((p:ℝ)-1) else 1+1/((p:ℝ)-1)^2) *
      (if ((A*B)⁻¹).conductor = 1 then 1 else
        ((p:ℝ)/((p:ℝ)-1))^2 / Real.sqrt ((A*B)⁻¹).conductor) := by
  let q := p^(j+1)
  let γ := (A*B)⁻¹
  have hp₁ : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hr : (q:ℝ)/(q.totient:ℝ) = (p:ℝ)/((p:ℝ)-1) := prime_power_totient_ratio (j:=j) hp
  have hA : 1 ≤ (if p ∣ m then 1+1/((p:ℝ)-1) else 1+1/((p:ℝ)-1)^2) := by
    split_ifs <;> linarith [div_nonneg (by norm_num : (0:ℝ)≤1) (sub_nonneg.mpr hp₁.le),
      div_nonneg (by norm_num : (0:ℝ)≤1) (sq_nonneg ((p:ℝ)-1))]
  refine (norm_gaussCoefficient_le A B m).trans ?_
  change (q:ℝ) * ‖gaussSum γ (ZMod.stdAddChar.mulShift (-(m:ZMod q)))‖ / (q.totient:ℝ)^2 ≤ _
  by_cases hc : γ.conductor = 1
  · have hγ : γ=1 := (eq_one_iff_conductor_eq_one (χ:=γ)).mpr hc
    rw [show ((A*B)⁻¹).conductor=1 from hc,if_pos rfl,mul_one,hγ]
    by_cases hm : p ∣ m
    · rw [if_pos hm]
      calc
        _ ≤ (q:ℝ) * (q.totient:ℝ) / (q.totient:ℝ)^2 := by
          gcongr
          exact norm_gauss_one_le_totient _
        _ = (q:ℝ)/(q.totient:ℝ) := by field_simp
        _ = (p:ℝ)/((p:ℝ)-1) := hr
        _ = _ := by field_simp; ring
    · rw [if_neg hm]
      calc
        _ ≤ (q:ℝ)*1/(q.totient:ℝ)^2 := by
          gcongr
          exact principal_gauss_prime_pow_nondividing hp hm
        _ = ((p:ℝ)/((p:ℝ)-1))/(q.totient:ℝ) := by
          rw [← hr]
          field_simp
        _ ≤ ((p:ℝ)/((p:ℝ)-1))/((p:ℝ)-1) := by
          have hφ' : (p:ℝ)-1 ≤ (q.totient:ℝ) := by
            dsimp [q]
            rw [Nat.totient_prime_pow_succ hp,Nat.cast_mul,Nat.cast_pow,
              Nat.cast_sub hp.one_lt.le,Nat.cast_one]
            exact le_mul_of_one_le_left (sub_nonneg.mpr hp₁.le) (one_le_pow₀ (by linarith))
          gcongr
        _ ≤ _ := by
          rw [div_div,← pow_two]
          apply (div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hp₁))).2
          rw [add_mul,one_mul,div_mul_cancel₀ _ (pow_ne_zero _ (sub_ne_zero.mpr hp₁.ne'))]
          have hp₂ : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
          nlinarith [sq_nonneg ((p:ℝ)-2)]
  · rw [if_neg (show ((A*B)⁻¹).conductor ≠ 1 from hc)]
    have hγ := norm_gauss_prime_power_conductor hp γ hc m
    have hγ₀ : γ.conductor ≠ 0 := fun zz =>
      NeZero.ne q (conductor_eq_zero_iff_level_eq_zero.mp zz)
    have hs : 0 < Real.sqrt (γ.conductor:ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hγ₀)
    calc
      _ ≤ (q:ℝ) * ((q:ℝ) / Real.sqrt γ.conductor) / (q.totient:ℝ)^2 := by
        gcongr
        simpa only [q,Nat.cast_pow] using hγ
      _ = ((p:ℝ)/((p:ℝ)-1))^2 / Real.sqrt γ.conductor := by
        rw [← hr]
        field_simp [hφ.ne',hs.ne']
        <;> ring
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hA

end Conjectures.Goldbach.TwistedGoldbachSingularSeries

namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter
open scoped Classical BigOperators

noncomputable def ordinaryAbsolutePrime (m p : ℕ) : ℝ :=
  if p ∣ m then 1+1/((p:ℝ)-1) else 1+1/((p:ℝ)-1)^2

noncomputable def productConductorCorrection (p : ℕ) : ℝ := ((p:ℝ)/((p:ℝ)-1))^2

private theorem ordinaryAbsolutePrime_pos {m p : ℕ} (hp : p.Prime) :
    0 < ordinaryAbsolutePrime m p := by
  have hp' : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  unfold ordinaryAbsolutePrime
  split_ifs <;> positivity

private theorem conductor_prime_power_product {p n : ℕ} (hp : p.Prime) [NeZero (p^n)]
    (A : DirichletCharacter ℂ (p^n)) :
    (∏ b ∈ A.conductor.primeFactors, productConductorCorrection b) =
      if A.conductor = 1 then 1 else productConductorCorrection p := by
  obtain ⟨j,_,hj⟩ := (Nat.dvd_prime_pow hp).mp A.conductor_dvd_level
  rw [hj]
  cases j with
  | zero => simp
  | succ j =>
    rw [Nat.primeFactors_prime_pow (Nat.succ_ne_zero j) hp,prod_singleton,
      ite_eq_right ((one_lt_pow₀ hp.one_lt (Nat.succ_ne_zero j)).ne')]

/-- Only primes of the product-character conductor enter the correction
for the full conductor-level Gauss coefficient. -/
theorem gaussCoefficient_product_conductor_bound (q : ℕ) [NeZero q]
    (A B : DirichletCharacter ℂ q) (m : ℕ) :
    ‖gaussCoefficient A B m‖ ≤
      (∏ p ∈ q.primeFactors, ordinaryAbsolutePrime m p) *
        (∏ p ∈ ((A*B)⁻¹).conductor.primeFactors, productConductorCorrection p) /
          Real.sqrt ((A*B)⁻¹).conductor := by
  revert ‹NeZero q› A B
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact False.elim (h.out rfl)
  | one =>
    intro _ A B
    rw [level_one A,level_one B]
    have hm : -(m:ZMod 1)=1 := Subsingleton.elim _ _
    simp [gaussCoefficient,hm,AddChar.mulShift_one,principal_gauss_standard_eq_moebius,
      B13BilateralVaughanReductionProof.DyadicMixedB4MoebiusGauss.moebiusComplex,conductor_one]
  | prime_pow p n hp hn =>
    obtain ⟨j,rfl⟩ : ∃ j, n=j+1 := ⟨n-1,by omega⟩
    intro h A B
    rw [Nat.primeFactors_prime_pow (by omega : j+1≠0) hp,prod_singleton,
      conductor_prime_power_product hp]
    let γ := (A*B)⁻¹
    change ‖gaussCoefficient A B m‖ ≤ ordinaryAbsolutePrime m p *
      (if γ.conductor = 1 then 1 else productConductorCorrection p) / Real.sqrt γ.conductor
    have hlocal := prime_power_relative_absolute_le hp A B m
    change ‖gaussCoefficient A B m‖ ≤ ordinaryAbsolutePrime m p *
      (if γ.conductor = 1 then 1 else productConductorCorrection p / Real.sqrt γ.conductor) at hlocal
    by_cases hγ : γ.conductor = 1
    · simp only [hγ,ite_true,Nat.cast_one,Real.sqrt_one,mul_one,div_one] at hlocal ⊢
      exact hlocal
    · rw [ite_eq_right hγ,mul_div_assoc]
      rwa [ite_eq_right hγ] at hlocal
  | coprime a b ha hb hab iha ihb =>
    intro _ A B
    letI : NeZero a := ⟨by omega⟩
    letI : NeZero b := ⟨by omega⟩
    let A₁ := crtLeftCharacter hab A
    let A₂ := crtRightCharacter hab A
    let B₁ := crtLeftCharacter hab B
    let B₂ := crtRightCharacter hab B
    rw [← crtCharacter_factor hab A,← crtCharacter_factor hab B]
    change ‖gaussCoefficient (crtCharacter A₁ A₂) (crtCharacter B₁ B₂) m‖ ≤ _
    rw [gaussCoefficient_crtCharacter hab,norm_mul,
      crtCharacter_mul,crtCharacter_inv,conductor_crtCharacter hab,
      Nat.primeFactors_mul (NeZero.ne a) (NeZero.ne b),
      prod_union hab.disjoint_primeFactors]
    let c₁ := ((A₁*B₁)⁻¹).conductor
    let c₂ := ((A₂*B₂)⁻¹).conductor
    have hc₁ : c₁ ≠ 0 := fun h => NeZero.ne a
      (conductor_eq_zero_iff_level_eq_zero.mp h)
    have hc₂ : c₂ ≠ 0 := fun h => NeZero.ne b
      (conductor_eq_zero_iff_level_eq_zero.mp h)
    have hcc : c₁.Coprime c₂ := hab.of_dvd
      (((A₁*B₁)⁻¹).conductor_dvd_level) (((A₂*B₂)⁻¹).conductor_dvd_level)
    rw [Nat.primeFactors_mul hc₁ hc₂,prod_union hcc.disjoint_primeFactors,
      Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg c₁)]
    have h₁ := iha A₁ B₁
    have h₂ := ihb A₂ B₂
    have hpos : 0 ≤ (∏ p ∈ a.primeFactors, ordinaryAbsolutePrime m p) *
        (∏ p ∈ c₁.primeFactors, productConductorCorrection p) / Real.sqrt c₁ := by
      apply div_nonneg _ (Real.sqrt_nonneg _)
      exact mul_nonneg (prod_nonneg fun p hp => (ordinaryAbsolutePrime_pos
        (m:=m) (Nat.prime_of_mem_primeFactors hp)).le)
        (prod_nonneg fun p hp => sq_nonneg _)
    refine (mul_le_mul h₁ h₂ (norm_nonneg _) hpos).trans ?_
    rw [div_mul_div_comm]
    apply le_of_eq
    congr 1
    ac_rfl

/-- The product of local corrections is bounded by an arbitrarily small
power of the product conductor alone. -/
theorem productConductorCorrection_subpower {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℕ, 0 < c →
      (∏ p ∈ c.primeFactors, productConductorCorrection p) ≤ C*(c:ℝ)^ε := by
  obtain ⟨D,hD,hpow⟩ := GoldbachHybridGrowth.primeFactor_twopow_le_rpow
    (show 0 < ε/2 by linarith)
  refine ⟨D^2,by positivity,?_⟩
  intro c hc
  have hterm (p : ℕ) (hp : p∈c.primeFactors) : productConductorCorrection p ≤ 4 := by
    have h₂ : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hs : (0:ℝ) < (p:ℝ)-1 := by linarith
    have hh : (p:ℝ)/((p:ℝ)-1) ≤ 2 := (div_le_iff₀ hs).mpr (by linarith)
    unfold productConductorCorrection
    nlinarith [sq_nonneg ((p:ℝ)/((p:ℝ)-1)),mul_nonneg
      (sub_nonneg.mpr hh) (show 0 ≤ 2+(p:ℝ)/((p:ℝ)-1) by positivity)]
  calc
    _ ≤ ∏ p ∈ c.primeFactors, (4:ℝ) :=
      prod_le_prod₀ (fun p hp => sq_nonneg _) hterm
    _ = ((2:ℝ)^c.primeFactors.card)^2 := by
      rw [prod_const,← pow_mul, Nat.mul_comm,pow_mul]
      norm_num
    _ ≤ (D*(c:ℝ)^(ε/2))^2 := by gcongr; exact hpow c hc
    _ = D^2*(c:ℝ)^ε := by
      rw [mul_pow,← Real.rpow_natCast ((c:ℝ)^(ε/2)) 2,
        ← Real.rpow_mul (Nat.cast_nonneg c)]
      norm_num

/-- Uniform relative absolute suppression by the conductor of the
primitive product, independently of the ambient levels of the inputs. -/
theorem fixed_pair_absolute_total_product_conductor {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {r s : ℕ} [NeZero r] [NeZero s]
      (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m →
      (∑' d : ℕ, ‖coefficient α β m d‖) ≤
        C * ((α.mul β).conductor:ℝ)^(ε-1/2) *
          (∑' d : ℕ, ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d‖) := by
  obtain ⟨C,hC,hpow⟩ := productConductorCorrection_subpower hε
  refine ⟨C,hC,?_⟩
  intro r s _ _ α β hα hβ m hm
  let L := r.lcm s
  letI : NeZero L := ⟨Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s)⟩
  let A := changeLevel (Nat.dvd_lcm_left r s) α
  let B := changeLevel (Nat.dvd_lcm_right r s) β
  let c := (α.mul β).conductor
  have hc₀ : 0 < c := Nat.pos_of_ne_zero (fun h => NeZero.ne L
    (conductor_eq_zero_iff_level_eq_zero.mp h))
  have hc : ((A*B)⁻¹).conductor = c := conductor_inv (A*B)
  have hcoeff := gaussCoefficient_product_conductor_bound L A B m
  rw [hc] at hcoeff
  have hlocal := ordinary_absolute_relative_factor_pos L m
  have hmain := fixed_pair_relative_absolute_total_div hα hβ m hm
  rw [hmain]
  refine mul_le_mul_of_nonneg_right ?_ (tsum_nonneg fun d => norm_nonneg _)
  apply (div_le_iff₀ hlocal).2
  have hco : coefficient α β m L = gaussCoefficient A B m :=
    coefficient_of_dvd α β m (Nat.dvd_lcm_left r s) (Nat.dvd_lcm_right r s)
  rw [hco]
  let F := ∏ p ∈ L.primeFactors, ordinaryAbsolutePrime m p
  let R := ∏ p ∈ c.primeFactors, productConductorCorrection p
  change ‖gaussCoefficient A B m‖ ≤ (C*(c:ℝ)^(ε-1/2))*F
  have hF : 0 ≤ F := prod_nonneg fun p hp => (ordinaryAbsolutePrime_pos
    (m:=m) (Nat.prime_of_mem_primeFactors hp)).le
  have hcast : (0:ℝ)<c := by exact_mod_cast hc₀
  calc
    _ ≤ F*R/Real.sqrt c := hcoeff
    _ ≤ F*(C*(c:ℝ)^ε)/Real.sqrt c := by gcongr; exact hpow c hc₀
    _ = _ := by
      rw [Real.sqrt_eq_rpow,Real.rpow_sub hcast]
      ring

end Conjectures.Goldbach.TwistedGoldbachSingularSeries

namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter Complex ArithmeticFunction Filter Topology
open scoped BigOperators Classical ArithmeticFunction.zeta
open B13BilateralVaughanReductionProof.DyadicMixedB4MoebiusGauss

private noncomputable def ordinarySignedArithmetic (m : ℕ) : ArithmeticFunction ℂ :=
  ⟨coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m,by simp [coefficient]⟩

private theorem ordinarySignedArithmetic_mult (m : ℕ) : (ordinarySignedArithmetic m).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨?_,?_⟩
  · change coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m 1 = 1
    rw [principalCoefficient_eq_gauss]
    have hm : -(m:ZMod 1)=1 := Subsingleton.elim _ _
    simp [gaussCoefficient,hm,AddChar.mulShift_one,principal_gauss_standard_eq_moebius,moebiusComplex]
  · intro q r hq hr h
    let : NeZero q := ⟨hq⟩
    let : NeZero r := ⟨hr⟩
    change coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m (q*r) = _
    simp only [ordinarySignedArithmetic,ArithmeticFunction.coe_mk,
      principalCoefficient_eq_gauss,principal_gaussCoefficient_mul h]

private theorem ordinarySignedArithmetic_prime_power_zero {p : ℕ} (hp : p.Prime)
    (m j : ℕ) (hj : 2≤j) : ordinarySignedArithmetic m (p^j)=0 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hnsq : ¬Squarefree (p^j) := by
    intro hs
    have hdiv : p*p∣p^j := by
      rw [← pow_two,show j=2+(j-2) by omega,pow_add]
      exact dvd_mul_right _ _
    exact hp.ne_one (Nat.isUnit_iff.mp (hs p hdiv))
  change coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m (p^j)=0
  rw [principalCoefficient_eq_gauss,principal_gaussCoefficient_eq_zero_of_not_squarefree hnsq]

private theorem ordinarySignedArithmetic_sum_prime_power {p : ℕ} (hp : p.Prime)
    (m k : ℕ) (hk : k≠0) :
    (∑ d ∈ (p^k).divisors,ordinarySignedArithmetic m d) = 1+ordinarySignedArithmetic m p := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [Nat.sum_divisors_prime_pow hp]
  simp only [Nat.succ_eq_add_one]
  rw [Finset.sum_range_succ',Finset.sum_range_succ']
  have htail : (∑ j ∈ range k,ordinarySignedArithmetic m (p^(j+1+1)))=0 :=
    sum_eq_zero (fun j _ => ordinarySignedArithmetic_prime_power_zero hp m _ (by omega))
  rw [htail,pow_zero,pow_one,(ordinarySignedArithmetic_mult m).map_one]
  ring

noncomputable def ordinarySignedPrime (m p : ℕ) : ℝ :=
  if p∣m then 1+1/((p:ℝ)-1) else 1-1/((p:ℝ)-1)^2

/-- The finite ordinary signed divisor sum is the product of its signed local
Euler factors. The identity is valid at odd as well as even arguments. -/
theorem ordinary_signed_divisor_product (q m : ℕ) (hq : q≠0) :
    (∑ d ∈ q.divisors,coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d) =
      (↑(∏ p ∈ q.primeFactors, ordinarySignedPrime m p):ℂ) := by
  let f := ordinarySignedArithmetic m
  let g := f*(ζ:ArithmeticFunction ℂ)
  have hg : g.IsMultiplicative :=
    (ordinarySignedArithmetic_mult m).mul ArithmeticFunction.isMultiplicative_zeta.natCast
  change (∑ d ∈ q.divisors,f d)=_
  rw [← coe_mul_zeta_apply]
  change g q=_
  rw [hg.multiplicative_factorization g hq,Nat.prod_factorization_eq_prod_primeFactors,Complex.ofReal_prod]
  apply prod_congr rfl
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  let : NeZero p := ⟨hpr.ne_zero⟩
  have hk : q.factorization p≠0 := by
    have he : p ∈ q.factorization.support := by simpa only [Nat.support_factorization] using hp
    exact Finsupp.mem_support_iff.mp he
  change (f*(ζ:ArithmeticFunction ℂ)) (p^q.factorization p)=_
  rw [coe_mul_zeta_apply]
  change (∑ d ∈ (p^q.factorization p).divisors,ordinarySignedArithmetic m d)=_
  rw [ordinarySignedArithmetic_sum_prime_power hpr m _ hk]
  change 1+coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m p = _
  rw [principalCoefficient_eq_gauss,principal_gaussCoefficient_prime hpr]
  unfold ordinarySignedPrime
  by_cases hm : p ∣ m
  · rw [ite_eq_left hm,ite_eq_left hm]
    push_cast
    have hp₁ : (1:ℂ) ≠ (p:ℂ) := by exact_mod_cast hpr.ne_one.symm
    field_simp
  · rw [ite_eq_right hm,ite_eq_right hm]
    push_cast
    ring

private theorem local_abs_le_signed_exp {p m : ℕ} (hp : p.Prime) (hm : Even m) :
    (if p∣m then 1+1/((p:ℝ)-1) else 1+1/((p:ℝ)-1)^2) ≤
      ordinarySignedPrime m p * Real.exp (16/(p:ℝ)^2) := by
  have hp₂ : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hden : 0 < (p:ℝ)-1 := by linarith
  unfold ordinarySignedPrime
  by_cases hpd : p ∣ m
  · rw [ite_eq_left hpd,ite_eq_left hpd]
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
  · rw [ite_eq_right hpd,ite_eq_right hpd]
    have hp₃ : (3:ℝ) ≤ p := by
      have hpnot : p ≠ 2 := fun he => hpd (he ▸ even_iff_two_dvd.mp hm)
      exact_mod_cast (show 3 ≤ p by have hh := hp.two_le; omega)
    let y := 1/((p:ℝ)-1)^2
    have hy₀ : 0 ≤ y := by positivity
    have hy : y ≤ 1/4 := by
      dsimp [y]
      apply one_div_le_one_div_of_le (by norm_num)
      nlinarith [mul_nonneg (show 0≤(p:ℝ)-3 by linarith) (show 0≤(p:ℝ)+1 by positivity)]
    have hscale : 4*y ≤ 16/(p:ℝ)^2 := by
      dsimp [y]
      apply (le_div_iff₀ (by positivity)).2
      have hp' : (0:ℝ)<p := by linarith
      field_simp [hden.ne']
      nlinarith [mul_nonneg (show 0≤(p:ℝ)-2 by linarith)
        (show 0≤3*(p:ℝ)-2 by linarith)]
    calc
      1+y ≤ (1-y)*(1+4*y) := by nlinarith [mul_nonneg (show 0≤1-4*y by linarith) hy₀]
      _ ≤ (1-y)*Real.exp (4*y) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (4*y)]) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hscale) (by linarith)

private theorem ordinarySignedPrime_nonneg {p m : ℕ} (hp : p.Prime) :
    0 ≤ ordinarySignedPrime m p := by
  have hp₂ : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hden : 0 < (p:ℝ)-1 := by linarith
  unfold ordinarySignedPrime
  split_ifs
  · positivity
  · have hx : 1/((p:ℝ)-1)^2 ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [mul_nonneg (show 0≤(p:ℝ)-2 by linarith) (show 0≤(p:ℝ) by positivity)]
    linarith

private theorem ordinary_abs_le_signed_divisor_sum_uniform :
    ∃ C : ℝ, 0<C ∧ ∀ q m : ℕ, q≠0 → Even m →
      (∑ d ∈ q.divisors, ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d‖) ≤
        C*(∑ d ∈ q.divisors,coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d).re := by
  let f : ℕ → ℝ := fun p => 16/(p:ℝ)^2
  have hf : Summable f := by
    simpa only [f,mul_one_div] using
      (Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).mul_left 16
  refine ⟨Real.exp (∑' n, f n),Real.exp_pos _,?_⟩
  intro q m hq hm
  rw [ordinary_absolute_divisor_product q m hq,ordinary_signed_divisor_product q m hq,Complex.ofReal_re]
  calc
    _ ≤ ∏ p ∈ q.primeFactors, ordinarySignedPrime m p * Real.exp (f p) := by
      apply prod_le_prod₀
      · intro p hp
        have hp₂ : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        have hden : 0 < (p:ℝ)-1 := by linarith
        split_ifs <;> positivity
      · exact fun p hp => local_abs_le_signed_exp (Nat.prime_of_mem_primeFactors hp) hm
    _ = (∏ p ∈ q.primeFactors, ordinarySignedPrime m p) *
        Real.exp (∑ p ∈ q.primeFactors,f p) := by rw [prod_mul_distrib,Real.exp_sum]
    _ ≤ _ := by
      rw [mul_comm (Real.exp (∑' n, f n))]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
        (prod_nonneg fun p hp => ordinarySignedPrime_nonneg (Nat.prime_of_mem_primeFactors hp))
      exact hf.sum_le_tsum _ (fun n _ => by dsimp [f]; positivity)

private theorem ordinary_factorial_limit {E : Type*} [NormedAddCommGroup E] {f : ℕ → E}
    (hf : Summable f) (h0 : f 0=0) :
    Tendsto (fun n : ℕ => ∑ d ∈ n.factorial.divisors, f d) atTop (𝓝 (∑' d, f d)) := by
  have hc : Tendsto (fun n : ℕ => insert 0 n.factorial.divisors) atTop atTop := by
    apply tendsto_atTop.2
    intro S
    filter_upwards [eventually_ge_atTop (S.sup id)] with n hn
    intro d hd
    by_cases h : d=0
    · simp [h]
    apply mem_insert_of_mem
    have hdn : d≤n := (S.le_sup (f:=id) hd).trans hn
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial (Nat.pos_of_ne_zero h) hdn,n.factorial_ne_zero⟩
  apply (hf.hasSum.comp hc).congr'
  filter_upwards with n
  simp [h0]

/-- The ordinary absolute singular series is bounded by an absolute constant
times the signed ordinary series at all positive even targets. -/
theorem ordinary_absolute_total_le_signed :
    ∃ C : ℝ, 0<C ∧ ∀ m : ℕ, 0 < m → Even m →
      (∑' d : ℕ, ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d‖) ≤
        C*(∑' d : ℕ,coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d).re := by
  obtain ⟨C,hC,hfin⟩ := ordinary_abs_le_signed_divisor_sum_uniform
  refine ⟨C,hC,?_⟩
  intro m hm he
  have hs := summable_coefficients (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m hm
  have hleft := ordinary_factorial_limit hs (by simp [coefficient])
  have hright := ((Complex.continuous_re.tendsto _).comp
    (ordinary_factorial_limit hs.of_norm (by simp [coefficient]))).const_mul C
  exact le_of_tendsto_of_tendsto' hleft hright (fun n => hfin _ _ n.factorial_ne_zero he)

end Conjectures.Goldbach.TwistedGoldbachSingularSeries

namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter
open scoped Classical BigOperators

/-- At a positive even target, the absolute contribution of any finite
denominator selection is bounded relative to the signed ordinary series by
an arbitrarily small loss in the square-root product conductor saving. -/
theorem finite_absolute_product_conductor_le_ordinary_signed {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {r s : ℕ} [NeZero r] [NeZero s]
      (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m →
      ∀ D : Finset ℕ, (∑ d ∈ D, ‖coefficient α β m d‖) ≤
        C * ((α.mul β).conductor:ℝ)^(ε-1/2) *
          (∑' d : ℕ,coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d).re := by
  obtain ⟨C,hC,hC'⟩ := fixed_pair_absolute_total_product_conductor hε
  obtain ⟨A,hA,hA'⟩ := ordinary_absolute_total_le_signed
  refine ⟨C*A,by positivity,?_⟩
  intro r s _ _ α β hα hβ m hm he D
  calc
    _ ≤ ∑' d : ℕ,‖coefficient α β m d‖ :=
      (summable_coefficients α β m hm).sum_le_tsum _ (fun _ _ => norm_nonneg _)
    _ ≤ C*((α.mul β).conductor:ℝ)^(ε-1/2) *
        (∑' d : ℕ,‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d‖) :=
      hC' α β hα hβ m hm
    _ ≤ (C*((α.mul β).conductor:ℝ)^(ε-1/2)) *
        (A * (∑' d : ℕ,coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m d).re) :=
      mul_le_mul_of_nonneg_left (hA' m hm he) (by positivity)
    _ = _ := by ring

end Conjectures.Goldbach.TwistedGoldbachSingularSeries


namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter
open scoped BigOperators Classical
open B13BilateralVaughanReductionProof
open DyadicMixedB4MoebiusGauss DyadicMixedB4ImprimitiveBound DyadicMixedB4CharacterFactorBound

private theorem norm_gauss_prime_power_eq_zero_of_not_dvd {p n : ℕ} (hp : p.Prime)
    [NeZero (p^n)] (χ : DirichletCharacter ℂ (p^n)) (hc : χ.conductor ≠ 1) (m : ℕ)
    (hm : ¬ (p^n/χ.conductor) ∣ m) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(m:ZMod (p^n))))‖ = 0 := by
  let c := χ.conductor
  let : NeZero c := ⟨fun h => NeZero.ne (p^n) (conductor_eq_zero_iff_level_eq_zero.mp h)⟩
  have hd := χ.conductor_dvd_level
  have hpc : p ∣ c := prime_divisor_power_of_ne_one hp hd hc
  apply le_antisymm _ (norm_nonneg _)
  refine (norm_gauss_neg_shift_le χ _).trans ?_
  nth_rewrite 1 [← χ.changeLevel_primitiveCharacter]
  rw [sum_inducedGauss_moebius]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun e he =>
    norm_induced_gauss_term hd he m χ.primitiveCharacter_isPrimitive).trans ?_)
  apply le_of_eq
  apply sum_eq_zero
  intro e he
  by_cases h : e=1
  · subst e
    exact ite_eq_right (fun h => hm (by simpa only [Nat.div_one] using h.2))
  · have hpe := prime_divisor_power_of_ne_one hp (Nat.dvd_of_mem_divisors he) h
    exact ite_eq_right (fun h => hp.ne_one (Nat.eq_one_of_dvd_coprimes h.1 hpe hpc))

private theorem norm_principal_gauss_prime_power_incomplete {p j m : ℕ} (hp : p.Prime)
    [NeZero (p^(j+1))] (hm : ¬p^(j+1) ∣ m) :
    ‖gaussSum (1:DirichletCharacter ℂ (p^(j+1))) (ZMod.stdAddChar.mulShift (-(m:ZMod (p^(j+1)))))‖ ≤
      if p^j ∣ m then (p:ℝ)^j else 0 := by
  refine (norm_gauss_neg_shift_le _ _).trans ?_
  have hlocal (q : ℕ) [NeZero q] (hq : q=p*p^j) :
      ‖gaussSum (1:DirichletCharacter ℂ q) (ZMod.stdAddChar.mulShift (m:ZMod q))‖ ≤
        if p^j ∣ m then (p:ℝ)^j else 0 := by
    subst q
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : NeZero (p^j) := ⟨pow_ne_zero _ hp.ne_zero⟩
    rw [principal_lifted_prime_gauss]
    by_cases hj : p^j ∣ m
    · have hpm : ¬p ∣ m/(p^j) := by
        intro h
        apply hm
        rw [pow_succ]
        exact (Nat.dvd_div_iff_mul_dvd hj).mp h
      rw [ite_eq_left hj,ite_eq_left hj,principal_gauss_prime_shift hp,ite_eq_right hpm,
        norm_mul,norm_neg,norm_one,mul_one,Complex.norm_natCast,Nat.cast_pow]
    · rw [ite_eq_right hj,ite_eq_right hj,norm_zero]
  exact hlocal _ (pow_succ' p j)

private theorem absPrime_one_le (p m : ℕ) (hp : p.Prime) :
    1 ≤ ordinaryAbsolutePrime m p := by
  have h₁ : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hp₀ : 0 < (p:ℝ)-1 := sub_pos.mpr h₁
  unfold ordinaryAbsolutePrime
  split_ifs <;> linarith [div_nonneg zero_le_one hp₀.le,
    div_nonneg zero_le_one (sq_nonneg ((p:ℝ)-1))]

/-- A failed divisibility at a prime power gives an additional factor 2/P
after ordinary normalization. -/
theorem prime_power_relative_divisibility_le {p j P : ℕ} (hp : p.Prime) [NeZero (p^(j+1))]
    (hP : 2≤P) (A B : DirichletCharacter ℂ (p^(j+1))) (m : ℕ)
    (hfail : ¬ p^(j+1) ∣ ((A*B)⁻¹).conductor*P.factorial*m) :
    ‖gaussCoefficient A B m‖ ≤ ordinaryAbsolutePrime m p *
      (if ((A*B)⁻¹).conductor=1 then 1 else
        productConductorCorrection p / Real.sqrt ((A*B)⁻¹).conductor) * (2/(P:ℝ)) := by
  let q := p^(j+1)
  let γ := (A*B)⁻¹
  let c := γ.conductor
  have hP₀ : (0:ℝ) < P := by exact_mod_cast (show 0<P by omega)
  have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  change ¬ q ∣ c*P.factorial*m at hfail
  change ‖gaussCoefficient A B m‖ ≤ ordinaryAbsolutePrime m p *
    (if c=1 then 1 else productConductorCorrection p / Real.sqrt c) * (2/(P:ℝ))
  have hmain := norm_gaussCoefficient_le A B m
  change ‖gaussCoefficient A B m‖ ≤ (q:ℝ) *
    ‖gaussSum γ (ZMod.stdAddChar.mulShift (-(m:ZMod q)))‖ / (q.totient:ℝ)^2 at hmain
  by_cases hc : c=1
  · rw [ite_eq_left hc,mul_one]
    have hγ : γ=1 := (eq_one_iff_conductor_eq_one (χ:=γ)).mpr hc
    rw [hγ] at hmain
    have hqm : ¬q ∣ m := fun hm => hfail (hm.trans (dvd_mul_left _ _))
    have hsmall := norm_principal_gauss_prime_power_incomplete hp hqm
    by_cases hj : p^j ∣ m
    · rw [ite_eq_left hj] at hsmall
      have hpP : P < p := by
        by_contra! h
        have hpF : p∣P.factorial := Nat.dvd_factorial hp.pos h
        apply hfail
        rw [hc,one_mul,show q=p*p^j from pow_succ' p j]
        exact Nat.mul_dvd_mul hpF hj
      have hpR : (P:ℝ) ≤ (p:ℝ)-1 := by
        have hh : P+1≤p := by omega
        exact le_sub_iff_add_le.mpr (by exact_mod_cast hh)
      have hp₂ : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
      have hp₀ : 0 < (p:ℝ)-1 := by linarith
      calc
        _ ≤ (q:ℝ)*(p:ℝ)^j/(q.totient:ℝ)^2 := hmain.trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg q))
            (sq_nonneg _))
        _ = (p:ℝ)/((p:ℝ)-1)^2 := by
          dsimp [q]
          rw [Nat.totient_prime_pow_succ hp,Nat.cast_mul,Nat.cast_pow,
            Nat.cast_sub hp.one_lt.le,Nat.cast_one,Nat.cast_pow,pow_succ]
          have hp₀' : (0:ℝ)<p := by linarith
          field_simp
          <;> ring
        _ = ((p:ℝ)/((p:ℝ)-1))/((p:ℝ)-1) := by rw [div_div,pow_two]
        _ ≤ 2/(P:ℝ) := by
          apply div_le_div₀ (by norm_num) _ hP₀ hpR
          exact (div_le_iff₀ hp₀).mpr (by linarith)
        _ ≤ _ := le_mul_of_one_le_left (by positivity) (absPrime_one_le p m hp)
    · rw [ite_eq_right hj] at hsmall
      exact hmain.trans ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall
        (Nat.cast_nonneg q)) (sq_nonneg _)).trans (by
          simp only [mul_zero,zero_div]
          exact mul_nonneg (zero_le_one.trans (absPrime_one_le p m hp)) (by positivity)))
  · rw [ite_eq_right hc]
    have hdm : ¬ (q/c) ∣ m := by
      intro h
      apply hfail
      have h1 : q ∣ c*m := by
        have hel : c*(q/c)=q := Nat.mul_div_cancel' γ.conductor_dvd_level
        rw [← hel]
        exact Nat.mul_dvd_mul_left _ h
      apply h1.trans
      rw [mul_right_comm c P.factorial m]
      exact dvd_mul_right _ _
    have hzero := norm_gauss_prime_power_eq_zero_of_not_dvd hp γ hc m hdm
    rw [hzero,mul_zero,zero_div] at hmain
    exact hmain.trans (mul_nonneg (mul_nonneg (zero_le_one.trans (absPrime_one_le p m hp))
      (div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))) (by positivity))

end Conjectures.Goldbach.TwistedGoldbachSingularSeries


namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter
open scoped Classical BigOperators

private theorem conductor_prime_power_product' {p n : ℕ} (hp : p.Prime) [NeZero (p^n)]
    (A : DirichletCharacter ℂ (p^n)) :
    (∏ b ∈ A.conductor.primeFactors, productConductorCorrection b) =
      if A.conductor = 1 then 1 else productConductorCorrection p := by
  obtain ⟨j,_,hj⟩ := (Nat.dvd_prime_pow hp).mp A.conductor_dvd_level
  rw [hj]
  cases j with
  | zero => simp
  | succ j =>
    rw [Nat.primeFactors_prime_pow (Nat.succ_ne_zero j) hp,prod_singleton,
      ite_eq_right ((one_lt_pow₀ hp.one_lt (Nat.succ_ne_zero j)).ne')]

/-- A failure of level divisibility propagates through the CRT and supplies
one factor 2/P in addition to the product-conductor correction. -/
theorem gaussCoefficient_product_conductor_not_dvd_bound (q : ℕ) [NeZero q]
    (A B : DirichletCharacter ℂ q) (m : ℕ) {P : ℕ} (hP : 2≤P)
    (hfail : ¬ q ∣ ((A*B)⁻¹).conductor*P.factorial*m) :
    ‖gaussCoefficient A B m‖ ≤
      ((∏ p ∈ q.primeFactors, ordinaryAbsolutePrime m p) *
        (∏ p ∈ ((A*B)⁻¹).conductor.primeFactors, productConductorCorrection p) /
          Real.sqrt ((A*B)⁻¹).conductor) * (2/(P:ℝ)) := by
  revert ‹NeZero q› A B
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact False.elim (h.out rfl)
  | one => intro _ A B h; exact (h (one_dvd _)).elim
  | prime_pow p n hp hn =>
    obtain ⟨j,rfl⟩ : ∃ j, n=j+1 := ⟨n-1,by omega⟩
    intro h A B hfail
    rw [Nat.primeFactors_prime_pow (by omega : j+1≠0) hp,prod_singleton,
      conductor_prime_power_product' hp]
    let γ := (A*B)⁻¹
    change ‖gaussCoefficient A B m‖ ≤ (ordinaryAbsolutePrime m p *
      (if γ.conductor = 1 then 1 else productConductorCorrection p) / Real.sqrt γ.conductor) *
      (2/(P:ℝ))
    have hlocal := prime_power_relative_divisibility_le hp hP A B m hfail
    change ‖gaussCoefficient A B m‖ ≤ ordinaryAbsolutePrime m p *
      (if γ.conductor = 1 then 1 else productConductorCorrection p / Real.sqrt γ.conductor) *
      (2/(P:ℝ)) at hlocal
    by_cases hγ : γ.conductor = 1
    · simpa only [hγ,ite_true,Nat.cast_one,Real.sqrt_one,mul_one,div_one] using hlocal
    · rw [ite_eq_right hγ,mul_div_assoc]
      rwa [ite_eq_right hγ] at hlocal
  | coprime a b ha hb hab iha ihb =>
    intro _ A B hfail
    letI : NeZero a := ⟨by omega⟩
    letI : NeZero b := ⟨by omega⟩
    let A₁ := crtLeftCharacter hab A
    let A₂ := crtRightCharacter hab A
    let B₁ := crtLeftCharacter hab B
    let B₂ := crtRightCharacter hab B
    rw [← crtCharacter_factor hab A,← crtCharacter_factor hab B,
      crtCharacter_mul,crtCharacter_inv,conductor_crtCharacter hab] at hfail
    rw [← crtCharacter_factor hab A,← crtCharacter_factor hab B]
    change ‖gaussCoefficient (crtCharacter A₁ A₂) (crtCharacter B₁ B₂) m‖ ≤ _
    rw [gaussCoefficient_crtCharacter hab,norm_mul,
      crtCharacter_mul,crtCharacter_inv,conductor_crtCharacter hab,
      Nat.primeFactors_mul (NeZero.ne a) (NeZero.ne b),
      prod_union hab.disjoint_primeFactors]
    let c₁ := ((A₁*B₁)⁻¹).conductor
    let c₂ := ((A₂*B₂)⁻¹).conductor
    have hc₁ : c₁ ≠ 0 := fun h => NeZero.ne a
      (conductor_eq_zero_iff_level_eq_zero.mp h)
    have hc₂ : c₂ ≠ 0 := fun h => NeZero.ne b
      (conductor_eq_zero_iff_level_eq_zero.mp h)
    have hcc : c₁.Coprime c₂ := hab.of_dvd
      (((A₁*B₁)⁻¹).conductor_dvd_level) (((A₂*B₂)⁻¹).conductor_dvd_level)
    rw [Nat.primeFactors_mul hc₁ hc₂,prod_union hcc.disjoint_primeFactors,
      Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg c₁)]
    let F₁ := ∏ p ∈ a.primeFactors, ordinaryAbsolutePrime m p
    let F₂ := ∏ p ∈ b.primeFactors, ordinaryAbsolutePrime m p
    let R₁ := ∏ p ∈ c₁.primeFactors, productConductorCorrection p
    let R₂ := ∏ p ∈ c₂.primeFactors, productConductorCorrection p
    let U := F₁*R₁/Real.sqrt c₁
    let V := F₂*R₂/Real.sqrt c₂
    let δ := 2/(P:ℝ)
    change ‖gaussCoefficient A₁ B₁ m‖ * ‖gaussCoefficient A₂ B₂ m‖ ≤
      ((F₁*F₂)*(R₁*R₂)/(Real.sqrt c₁*Real.sqrt c₂))*δ
    have hcombine : U*V = (F₁*F₂)*(R₁*R₂)/(Real.sqrt c₁*Real.sqrt c₂) := by
      dsimp [U,V]
      rw [div_mul_div_comm]
      congr 1
      ac_rfl
    rw [← hcombine]
    have h₁ : ‖gaussCoefficient A₁ B₁ m‖ ≤ U := gaussCoefficient_product_conductor_bound a A₁ B₁ m
    have h₂ : ‖gaussCoefficient A₂ B₂ m‖ ≤ V := gaussCoefficient_product_conductor_bound b A₂ B₂ m
    have hU := (norm_nonneg _).trans h₁
    have hV := (norm_nonneg _).trans h₂
    have hδ : 0 ≤ δ := by dsimp [δ]; positivity
    have hbad : ¬ (a ∣ c₁*P.factorial*m ∧ b ∣ c₂*P.factorial*m) := by
      rintro ⟨hleft,hright⟩
      apply hfail
      change a*b ∣ (c₁*c₂)*P.factorial*m
      apply hab.mul_dvd_of_dvd_of_dvd
      · exact hleft.trans ⟨c₂,by ac_rfl⟩
      · exact hright.trans ⟨c₁,by ac_rfl⟩
    rcases not_and_or.mp hbad with hleft|hright
    · have h₁' : ‖gaussCoefficient A₁ B₁ m‖ ≤ U*δ := iha A₁ B₁ hleft
      exact (mul_le_mul h₁' h₂ (norm_nonneg _) (mul_nonneg hU hδ)).trans_eq
        (by ac_rfl)
    · have h₂' : ‖gaussCoefficient A₂ B₂ m‖ ≤ V*δ := ihb A₂ B₂ hright
      exact (mul_le_mul h₁ h₂' (norm_nonneg _) hU).trans_eq (by ac_rfl)

/-- Uniform ordinary-relative absolute suppression at a target for which
the least common multiple of the input levels fails divisibility. -/
theorem fixed_pair_absolute_total_not_dvd :
    ∃ C : ℝ, 0 < C ∧ ∀ {P : ℕ}, 2≤P →
      ∀ {r s : ℕ} [NeZero r] [NeZero s]
      (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m →
      ¬ r.lcm s ∣ (α.mul β).conductor*P.factorial*m →
      (∑' d : ℕ, ‖coefficient α β m d‖) ≤
        (C/(P:ℝ)) * (∑' d : ℕ, ‖coefficient (1:DirichletCharacter ℂ 1)
          (1:DirichletCharacter ℂ 1) m d‖) := by
  obtain ⟨D,hD,hpow⟩ := productConductorCorrection_subpower (show (0:ℝ)<1/2 by norm_num)
  refine ⟨2*D,by positivity,?_⟩
  intro P hP r s _ _ α β hα hβ m hm hfail
  let L := r.lcm s
  letI : NeZero L := ⟨Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s)⟩
  let A := changeLevel (Nat.dvd_lcm_left r s) α
  let B := changeLevel (Nat.dvd_lcm_right r s) β
  let c := (α.mul β).conductor
  have hc₀ : 0 < c := Nat.pos_of_ne_zero (fun h => NeZero.ne L
    (conductor_eq_zero_iff_level_eq_zero.mp h))
  have hc : ((A*B)⁻¹).conductor = c := conductor_inv (A*B)
  have hcFail : ¬ L ∣ ((A*B)⁻¹).conductor*P.factorial*m := by rw [hc]; exact hfail
  have hcoeff := gaussCoefficient_product_conductor_not_dvd_bound L A B m hP hcFail
  rw [hc] at hcoeff
  have hlocal := ordinary_absolute_relative_factor_pos L m
  rw [fixed_pair_relative_absolute_total_div hα hβ m hm]
  refine mul_le_mul_of_nonneg_right ?_ (tsum_nonneg fun _ => norm_nonneg _)
  apply (div_le_iff₀ hlocal).2
  rw [coefficient_of_dvd α β m (Nat.dvd_lcm_left r s) (Nat.dvd_lcm_right r s)]
  let F := ∏ p ∈ L.primeFactors, ordinaryAbsolutePrime m p
  let R := ∏ p ∈ c.primeFactors, productConductorCorrection p
  change ‖gaussCoefficient A B m‖ ≤ ((2*D)/(P:ℝ))*F
  have hF : 0 ≤ F := hlocal.le
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 (by exact_mod_cast hc₀)
  have hR : R ≤ D*Real.sqrt c := by rw [Real.sqrt_eq_rpow]; exact hpow c hc₀
  calc
    _ ≤ (F*R/Real.sqrt c)*(2/(P:ℝ)) := hcoeff
    _ ≤ (F*(D*Real.sqrt c)/Real.sqrt c)*(2/(P:ℝ)) := by gcongr
    _ = _ := by field_simp [hs.ne']

/-- Among bounded product conductors, the pairs whose input-level
least common multiple fails to divide a fixed multiple of the target
have arbitrarily small contribution to any denominator selection. -/
theorem finite_absolute_bounded_product_not_dvd {η : ℝ} (hη : 0 < η) (K : ℕ) :
    ∃ H : ℕ, 0 < H ∧
      ∀ {r s : ℕ} [NeZero r] [NeZero s]
      (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → (α.mul β).conductor≤K →
      ∀ m : ℕ, 0 < m → Even m → (¬ r.lcm s ∣ H*m) →
      ∀ D : Finset ℕ, (∑ d ∈ D, ‖coefficient α β m d‖) ≤
        η*(∑' d : ℕ, coefficient (1:DirichletCharacter ℂ 1)
          (1:DirichletCharacter ℂ 1) m d).re := by
  obtain ⟨C,hC,hC'⟩ := ordinary_absolute_total_le_signed
  obtain ⟨D,hD,hD'⟩ := fixed_pair_absolute_total_not_dvd
  obtain ⟨P₀,hP₀⟩ := exists_nat_gt (D*C/η)
  let P := max 2 P₀
  have hP : 2≤P := le_max_left _ _
  have hP₁ : (D*C)/η < (P:ℝ) := hP₀.trans_le (by exact_mod_cast le_max_right 2 P₀)
  refine ⟨K.factorial*P.factorial,Nat.mul_pos K.factorial_pos P.factorial_pos,?_⟩
  intro r s _ _ α β hα hβ hK m hm he hfail S
  let c := (α.mul β).conductor
  have hc₀ : 0 < c := Nat.pos_of_ne_zero (fun h =>
    (Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s)) (conductor_eq_zero_iff_level_eq_zero.mp h))
  have hcD : c ∣ K.factorial := Nat.dvd_factorial hc₀ hK
  have hf : ¬ r.lcm s ∣ c*P.factorial*m :=
    fun h => hfail (h.trans (Nat.mul_dvd_mul (Nat.mul_dvd_mul hcD (dvd_refl _)) (dvd_refl _)))
  have hsmall : (D*C)/(P:ℝ) ≤ η := by
    have hP' : (0:ℝ)<P := by exact_mod_cast (show 0<P by omega)
    apply (div_le_iff₀ hP').2
    linarith [(div_lt_iff₀ hη).1 hP₁]
  have hAbs : (∑' d : ℕ, ‖coefficient (1:DirichletCharacter ℂ 1)
      (1:DirichletCharacter ℂ 1) m d‖) ≤
      C*(∑' d : ℕ, coefficient (1:DirichletCharacter ℂ 1)
        (1:DirichletCharacter ℂ 1) m d).re := hC' m hm he
  have hOrd : 0 ≤ (∑' d : ℕ, coefficient (1:DirichletCharacter ℂ 1)
      (1:DirichletCharacter ℂ 1) m d).re := by
    have h₀ : 0 ≤ C*(∑' d : ℕ, coefficient (1:DirichletCharacter ℂ 1)
      (1:DirichletCharacter ℂ 1) m d).re := (tsum_nonneg fun _ => norm_nonneg _).trans hAbs
    exact nonneg_of_mul_nonneg_right h₀ hC
  have htot := hD' hP α β hα hβ m hm hf
  calc
    _ ≤ ∑' d : ℕ, ‖coefficient α β m d‖ :=
      (summable_coefficients α β m hm).sum_le_tsum _ (fun _ _ => norm_nonneg _)
    _ ≤ _ := htot
    _ ≤ (D/(P:ℝ))*(C*(∑' d : ℕ, coefficient (1:DirichletCharacter ℂ 1)
        (1:DirichletCharacter ℂ 1) m d).re) := mul_le_mul_of_nonneg_left hAbs (by positivity)
    _ = ((D*C)/(P:ℝ))*(∑' d : ℕ, coefficient (1:DirichletCharacter ℂ 1)
        (1:DirichletCharacter ℂ 1) m d).re := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hOrd

end Conjectures.Goldbach.TwistedGoldbachSingularSeries


namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter Filter Topology
open scoped Classical BigOperators

/-- Any finite denominator selection outside the prescribed bounded product
conductors and target divisibility has arbitrarily small ordinary-relative
absolute mass. Both thresholds are independent of the input levels. -/
theorem finite_absolute_off_bounded_divisibility_support {η : ℝ} (hη : 0 < η) :
    ∃ K H : ℕ, 0 < K ∧ 0 < H ∧
      ∀ {r s : ℕ} [NeZero r] [NeZero s]
      (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m →
      ¬ ((α.mul β).conductor≤K ∧ r.lcm s∣H*m) →
      ∀ D : Finset ℕ, (∑ d ∈ D, ‖coefficient α β m d‖) ≤
        η*(∑' d : ℕ, coefficient (1:DirichletCharacter ℂ 1)
          (1:DirichletCharacter ℂ 1) m d).re := by
  obtain ⟨C,hC,hC'⟩ := finite_absolute_product_conductor_le_ordinary_signed
    (show (0:ℝ)<1/4 by norm_num)
  have hlim : Tendsto (fun n : ℕ => C*((n:ℝ)^(-(1/4):ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using ((tendsto_rpow_neg_atTop (show (0:ℝ)<1/4 by norm_num)).comp
      tendsto_natCast_atTop_atTop).const_mul C
  obtain ⟨K₀,hK₀⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 η hη)
  let K := max 1 K₀
  obtain ⟨H,hH,hsmall⟩ := finite_absolute_bounded_product_not_dvd hη K
  refine ⟨K,H,lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _),hH,?_⟩
  intro r s _ _ α β hα hβ m hm he hout D
  by_cases hK : (α.mul β).conductor≤K
  · exact hsmall α β hα hβ hK m hm he (fun h => hout ⟨hK,h⟩) D
  · have hco := hC' α β hα hβ m hm he D
    rw [show (1/4:ℝ)-1/2=-(1/4) by norm_num] at hco
    have hη' : C*((((α.mul β).conductor:ℝ)^(-(1/4):ℝ))) < η :=
      hK₀ _ ((le_max_right 1 K₀).trans (le_of_not_ge hK))
    have hOrd : 0 ≤ (∑' d : ℕ, coefficient (1:DirichletCharacter ℂ 1)
        (1:DirichletCharacter ℂ 1) m d).re := by
      obtain ⟨A,hA,hA'⟩ := ordinary_absolute_total_le_signed
      exact nonneg_of_mul_nonneg_right ((tsum_nonneg fun _ => norm_nonneg _).trans (hA' m hm he)) hA
    exact hco.trans (mul_le_mul_of_nonneg_right hη'.le hOrd)

end Conjectures.Goldbach.TwistedGoldbachSingularSeries

namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter Filter Topology
open scoped BigOperators Classical ComplexConjugate
open B13BilateralVaughanReductionProof
open DyadicMixedB4GaussLift


private theorem principal_gauss_eq_majorRam (q m : ℕ) [NeZero q] :
    gaussSum (1:DirichletCharacter ℂ q) (ZMod.stdAddChar.mulShift (m:ZMod q)) =
      Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.ram q m := by
  rw [gaussSum_as_fraction_sum,Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.ram,sum_filter]
  apply sum_congr rfl
  intro a _
  have hphase : BombieriVinogradov.LargeSieve.additivePhase ((m:ℝ)*a/q) =
      Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.phase ((m:ℝ)*a/q) := (DyadicMixedB4Ramanujan.phase_eq_additivePhase _).symm
  by_cases h : a.Coprime q
  · rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime a q).mpr h),one_mul,hphase,ite_eq_left h]
  · rw [MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime a q).mp hu)),
      zero_mul,ite_eq_right h]

private theorem majorRam_conj (q m : ℕ) : conj (Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.ram q m) = Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.ram q m := by
  open Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc in
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ j =>
      rw [ram_primePower p j m hp,map_sub]
      split_ifs <;> simp
  | coprime q r hq hr hc ihq ihr =>
    rw [ram_mul (by omega) (by omega) hc,map_mul,ihq,ihr]

theorem ordinaryCoefficient_eq_majorCoefficient (q m : ℕ) [NeZero q] :
    (coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1)) m q = Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.coefficient q m := by
  have hOne : gaussSum (1:DirichletCharacter ℂ q) ZMod.stdAddChar = Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.ram q 1 := by
    simpa only [Nat.cast_one,AddChar.mulShift_one] using principal_gauss_eq_majorRam q 1
  rw [principalCoefficient_eq_gauss,gaussCoefficient]
  simp only [one_mul,inv_one,principal_gauss_neg_shift_eq,hOne,principal_gauss_eq_majorRam,
    Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.coefficient,majorRam_conj]
  ring

/-- The ordinary denominator coefficients have a uniformly bounded
quarter-power moment up to an arbitrary small power of the target. -/
theorem ordinary_absolute_weighted_finite {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ D : Finset ℕ,
      (∑ d ∈ D, ‖(coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1)) m d‖*(d:ℝ)^(1/4:ℝ)) ≤ C*(m:ℝ)^ε := by
  obtain ⟨k,hk⟩ := exists_nat_gt (1/ε)
  have hk₀ : 0 < k := by
    exact_mod_cast (show (0:ℝ) < k from (one_div_pos.mpr hε).trans hk)
  have hkR : (0:ℝ) < k := by exact_mod_cast hk₀
  have hpow : (1/(k:ℝ))≤ε := by
    apply (div_le_iff₀ hkR).2
    nlinarith [(div_lt_iff₀ hε).1 hk]
  obtain ⟨A,hA,hA'⟩ := GoldbachPrincipalSeries.divisor_envelope k hk₀
  let B := GoldbachPrincipalSeries.seriesBudget
  have hB := GoldbachPrincipalSeries.seriesBudget_nonneg
  refine ⟨1600*(B+1)*A,by positivity,?_⟩
  intro m hm D
  have hm₁ : (1:ℝ)≤ m := by exact_mod_cast hm
  have hCard : (m.divisors.card:ℝ) ≤ A*(m:ℝ)^ε :=
    (hA' m m le_rfl).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hm₁ hpow) (zero_le_one.trans hA))
  have hterm (d : ℕ) :
      ‖(coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1)) m d‖*(d:ℝ)^(1/4:ℝ) ≤
        1600*((d.gcd m:ℝ)*(d:ℝ)^(-5/4:ℝ)) := by
    by_cases hd : d=0
    · simp [hd,coefficient]
    · letI : NeZero d := ⟨hd⟩
      have hdR : (0:ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
      have hd₁ : (1:ℝ) ≤ d := by exact_mod_cast Nat.pos_of_ne_zero hd
      rw [ordinaryCoefficient_eq_majorCoefficient]
      calc
        _ ≤ (1600*(d.gcd m:ℝ)*(d:ℝ)^(-7/4:ℝ))*(d:ℝ)^(1/4:ℝ) :=
          mul_le_mul_of_nonneg_right (GoldbachPrincipalSeries.coefficient_norm_le (Nat.pos_of_ne_zero hd))
            (by positivity)
        _ = 1600*((d.gcd m:ℝ)*(d:ℝ)^(-3/2:ℝ)) := by
          rw [mul_assoc,← Real.rpow_add hdR]
          norm_num
          ring
        _ ≤ _ := by
          have hpow' : (d:ℝ)^(-3/2:ℝ) ≤ (d:ℝ)^(-5/4:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hd₁ (by norm_num)
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpow' (Nat.cast_nonneg _)) (by norm_num)
  calc
    _ ≤ ∑ d ∈ D,1600*((d.gcd m:ℝ)*(d:ℝ)^(-5/4:ℝ)) := sum_le_sum fun d _ => hterm d
    _ = 1600*(∑ d ∈ D,(d.gcd m:ℝ)*(d:ℝ)^(-5/4:ℝ)) := (mul_sum ..).symm
    _ ≤ 1600*((m.divisors.card:ℝ)*B) := mul_le_mul_of_nonneg_left
      (GoldbachPrincipalSeries.sum_gcd_decay_le D hm) (by norm_num)
    _ ≤ 1600*((A*(m:ℝ)^ε)*(B+1)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul hCard (by linarith) hB (by positivity)
    _ = _ := by ring

theorem finite_tail_rankin {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) {T : ℝ} (hT : 0 < T)
    (D : Finset ℕ) :
    (∑ k ∈ D.filter (fun k : ℕ => T < (k:ℝ)), f k) ≤
      (∑ k ∈ D.filter (fun k : ℕ => T < (k:ℝ)), f k*(k:ℝ)^(1/4:ℝ))*T^(-1/4:ℝ) := by
  rw [sum_mul]
  apply sum_le_sum
  intro k hk
  have hk' := (mem_filter.mp hk).2
  have hpow : T^(1/4:ℝ) ≤ (k:ℝ)^(1/4:ℝ) :=
    Real.rpow_le_rpow hT.le hk'.le (by norm_num)
  calc
    _ = (f k*T^(1/4:ℝ))*T^(-1/4:ℝ) := by
      rw [mul_assoc,← Real.rpow_add hT]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (hf k)) (by positivity)

end Conjectures.Goldbach.TwistedGoldbachSingularSeries


namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter Filter Topology
open scoped BigOperators Classical


/-- The moment of a fixed primitive pair factors through the common
conductor and a finite selection of ordinary coprime coefficients. -/
theorem fixed_pair_weighted_sum_eq {r s : ℕ} [NeZero r] [NeZero s]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (D : Finset ℕ) :
    let L := r.lcm s
    let S := D.filter (fun d => d ≠ 0 ∧ L ∣ d ∧ L.Coprime (d/L))
    (∑ d ∈ D, ‖coefficient α β m d‖*(d:ℝ)^(1/4:ℝ)) =
      (‖coefficient α β m L‖*(L:ℝ)^(1/4:ℝ)) *
        (∑ k ∈ S.image (fun d => d/L), ‖(coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1)) m k‖*(k:ℝ)^(1/4:ℝ)) := by
  dsimp only
  let L := r.lcm s
  have hL : L ≠ 0 := Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s)
  let S := D.filter (fun d => d ≠ 0 ∧ L ∣ d ∧ L.Coprime (d/L))
  let w (d : ℕ) := ‖coefficient α β m d‖*(d:ℝ)^(1/4:ℝ)
  let g (k : ℕ) := ‖(coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1)) m k‖*(k:ℝ)^(1/4:ℝ)
  change (∑ d ∈ D,w d) = (‖coefficient α β m L‖*(L:ℝ)^(1/4:ℝ)) *
    (∑ k ∈ S.image (fun d => d/L),g k)
  have hS : ∀ d ∈ S, d ≠ 0 ∧ L ∣ d ∧ L.Coprime (d/L) :=
    fun d hd => (mem_filter.mp hd).2
  have hinj : Set.InjOn (fun d : ℕ => d/L) (S : Set ℕ) := by
    intro d hd e he hde
    change d/L=e/L at hde
    rw [← Nat.mul_div_cancel' (hS d hd).2.1,← Nat.mul_div_cancel' (hS e he).2.1,hde]
  have hdrop : (∑ d ∈ D,w d) = ∑ d ∈ S,w d := by
    rw [show S = D.filter (fun d => d ≠ 0 ∧ L ∣ d ∧ L.Coprime (d/L)) from rfl,sum_filter]
    apply sum_congr rfl
    intro d _
    split_ifs with h
    · rfl
    · by_cases hd : d=0
      · simp [w,hd,coefficient]
      · by_cases hLd : L∣d
        · letI : NeZero d := ⟨hd⟩
          have hbad : ¬(d/L).Coprime L := fun hc => h ⟨hd,hLd,hc.symm⟩
          change ‖coefficient α β m d‖*(d:ℝ)^(1/4:ℝ)=0
          rw [coefficient_eq_zero_of_not_coprime_lcm_quotient hα hβ m hLd hbad,
            norm_zero,zero_mul]
        · simp [w,coefficient_eq_zero_of_not_lcm_dvd α β m hLd]
  have hterm (d : ℕ) (hd : d∈S) :
      w d = (‖coefficient α β m L‖*(L:ℝ)^(1/4:ℝ))*g (d/L) := by
    have ⟨hd₀,hLd,hcop⟩ := hS d hd
    have hmul : L*(d/L)=d := Nat.mul_div_cancel' hLd
    have hk₀ : d/L ≠ 0 := fun hz => hd₀ (by rw [← hmul,hz,mul_zero])
    letI : NeZero (d/L) := ⟨hk₀⟩
    have hcoeff : coefficient α β m d = coefficient α β m L*(coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1)) m (d/L) := by
      conv_lhs => rw [← hmul]
      rw [coefficient_lcm_mul_coprime α β m hcop,principalCoefficient_eq_gauss]
    have hcast : (d:ℝ) = (L:ℝ)*((d/L:ℕ):ℝ) := by exact_mod_cast hmul.symm
    change ‖coefficient α β m d‖*(d:ℝ)^(1/4:ℝ) =
      (‖coefficient α β m L‖*(L:ℝ)^(1/4:ℝ))*(‖(coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1)) m (d/L)‖*((d/L:ℕ):ℝ)^(1/4:ℝ))
    rw [hcoeff,norm_mul,hcast,Real.mul_rpow (Nat.cast_nonneg L) (Nat.cast_nonneg (d/L))]
    ring
  rw [hdrop]
  calc
    _ = ∑ d ∈ S,(‖coefficient α β m L‖*(L:ℝ)^(1/4:ℝ))*g (d/L) := sum_congr rfl hterm
    _ = (‖coefficient α β m L‖*(L:ℝ)^(1/4:ℝ))*(∑ d ∈ S,g (d/L)) := (mul_sum ..).symm
    _ = _ := by rw [sum_image hinj]

/-- Above a positive cutoff T, a fixed pair incurs the common-conductor
factor L^(1/4) together with the ordinary Rankin decay T^(-1/4). -/
theorem fixed_pair_absolute_tail_finite {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {r s : ℕ} [NeZero r] [NeZero s]
      (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m →
      ∀ T : ℝ, 0 < T → ∀ D : Finset ℕ,
      let L := r.lcm s
      (∑ k ∈ D.filter (fun k : ℕ => T < (k:ℝ)), ‖coefficient α β m k‖) ≤
        (‖coefficient α β m L‖*(L:ℝ)^(1/4:ℝ)) * (C*(m:ℝ)^ε*T^(-1/4:ℝ)) := by
  obtain ⟨C,hC,hC'⟩ := ordinary_absolute_weighted_finite hε
  refine ⟨C,hC,?_⟩
  intro r s _ _ α β hα hβ m hm T hT D
  dsimp only
  refine (finite_tail_rankin (fun k => norm_nonneg (coefficient α β m k)) hT D).trans ?_
  rw [fixed_pair_weighted_sum_eq hα hβ]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul_of_nonneg_right (hC' m hm _) (by positivity)

end Conjectures.Goldbach.TwistedGoldbachSingularSeries

end

section

namespace GoldbachSignedPairs

open Finset MeasureTheory Goldbach GoldbachTwistedMellin
open GoldbachWeightedMajorResidual GoldbachSmoothWindow GoldbachZeroStrip
open GoldbachPrincipalSeries (finiteModel_continuous)
open GoldbachPolynomialMinor205 (wave)
open GoldbachWeightedException (cutoff)
open Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc (unitMean)
open scoped Classical

noncomputable section

def shortModesAt (X q : ℕ) [NeZero q] : Finset (Mode q) :=
  ((Finset.univ : Finset (DirichletCharacter ℂ q)).sigma
    (fun χ => (exceptionalZeros χ (heightCut (X:ℝ))).filter (shortNearZero X χ.conductor))).insertNone

theorem short_signedModel_eq_modes {X q : ℕ} [NeZero q] (hX : 2 ≤ X) (a : ℕ) (β : ℝ) :
    unitMean q a * discreteModel X β - shortNearArcCorrection X q a β =
      ∑ i ∈ shortModesAt X q, rationalWeight q a i * signedProfile X q i β := by
  unfold shortModesAt
  rw [Finset.sum_insertNone, Finset.sum_sigma]
  simp only [shortNearArcCorrection, ite_eq_left hX, arcCorrectionOn, dite_eq_left (NeZero.ne q),
    rationalWeight, signedProfile]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro χ _
  rw [zeroTermOn_eq_angular hX, mul_sum, ← Finset.sum_neg_distrib]
  apply sum_congr rfl
  intro z _
  ring

/-- The genuine truncated signed arc coefficient uses these two-character sums. -/
theorem short_signedFiber_eq_pair_sum {X q : ℕ} [NeZero q] (hX : 2 ≤ X) (m : ℕ) :
    let s := (Finset.range q).filter (fun a => a.Coprime q)
    let I := shortModesAt X q
    (∑ a ∈ s, ∫ β in Set.Icc (-arcRadius X q) (arcRadius X q),
        (unitMean q a * discreteModel X β - shortNearArcCorrection X q a β)^2 *
        wave (-(m:ℝ)*((a:ℝ)/q+β))) =
    ∑ i ∈ I, ∑ j ∈ I,
      pairCoefficient s (fun a : ℕ => (a:ℝ)/q) m (rationalWeight q) i j *
        pairIntegral (arcRadius X q) m (signedProfile X q) i j := by
  dsimp only
  simp_rw [short_signedModel_eq_modes hX]
  exact signed_window_expansion _ _ _ _ _ _ _ (fun i _ => continuous_signedProfile hX i)

theorem unitPair_eq_peer_coefficient {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q)
    (m : ℕ) :
    unitPair χ ψ (m:ZMod q) =
      Conjectures.Goldbach.TwistedGoldbachSingularSeries.gaussCoefficient χ⁻¹ ψ⁻¹ m := by
  rw [unitPair_eq_gauss, additiveWeight_one_eq_gauss, additiveWeight_one_eq_gauss]
  unfold Conjectures.Goldbach.TwistedGoldbachSingularSeries.gaussCoefficient
  rw [mul_inv, inv_inv, inv_inv]
  ring

set_option maxHeartbeats 2500000 in
theorem short_signedFiber_eq_gauss_pair_sum {X q : ℕ} [NeZero q] (hX : 2 ≤ X) (m : ℕ) :
    let s := (Finset.range q).filter (fun a => a.Coprime q)
    let I := shortModesAt X q
    (∑ a ∈ s, ∫ β in Set.Icc (-arcRadius X q) (arcRadius X q),
        (unitMean q a * discreteModel X β - shortNearArcCorrection X q a β)^2 *
        wave (-(m:ℝ)*((a:ℝ)/q+β))) =
    ∑ i ∈ I, ∑ j ∈ I,
      Conjectures.Goldbach.TwistedGoldbachSingularSeries.gaussCoefficient
        (modeCharacter q i)⁻¹ (modeCharacter q j)⁻¹ m *
        pairIntegral (arcRadius X q) m (signedProfile X q) i j := by
  dsimp only
  rw [short_signedFiber_eq_pair_sum hX]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [rational_pair_eq_unitPair, unitPair_eq_peer_coefficient]

end
end GoldbachSignedPairs


end

section

namespace GoldbachSignedPairs

open Finset MeasureTheory Goldbach GoldbachTwistedMellin DirichletCharacter
open GoldbachWeightedMajorResidual GoldbachSmoothWindow GoldbachZeroStrip GoldbachConductorZeros
open GoldbachConductorRegroup
open GoldbachWeightedException (cutoff)
open scoped Classical

noncomputable section

abbrev GlobalMode := Option (Σ r : ℕ, DirichletCharacter ℂ r × ℂ)

def globalLevel : GlobalMode → ℕ
  | none => 1
  | some r => r.1

def globalShortZeros (X r : ℕ) (χ : DirichletCharacter ℂ r) : Finset ℂ :=
  if hr : r ≠ 0 then
    let _ : NeZero r := ⟨hr⟩
    (exceptionalZeros χ (heightCut (X:ℝ))).filter (shortNearZero X r)
  else ∅

def globalModesAt (X : ℕ) : Finset GlobalMode :=
  ((Icc 1 (cutoff X)).sigma (fun r =>
    (((Finset.univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive)).sigma
      (globalShortZeros X r)).image (fun p => (p.1,p.2)))).insertNone

def globalLift (q : ℕ) : GlobalMode → Mode q
  | none => none
  | some ⟨r,χ,z⟩ => if h : r ∣ q then some ⟨changeLevel h χ,z⟩ else none

theorem mem_globalModesAt_zero {X r : ℕ} (χ : DirichletCharacter ℂ r) (z : ℂ) :
    (some ⟨r,χ,z⟩ : GlobalMode) ∈ globalModesAt X ↔
      1 ≤ r ∧ r ≤ cutoff X ∧ χ.IsPrimitive ∧ z ∈ globalShortZeros X r χ := by
  simp only [globalModesAt,some_mem_insertNone,mem_sigma,mem_Icc,mem_image,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨⟨h1,h2⟩,⟨⟨ψ,t⟩,⟨hψ,ht⟩,he⟩⟩
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨h1,h2,hψ,ht⟩
  · rintro ⟨h1,h2,hp,hz⟩
    exact ⟨⟨h1,h2⟩,⟨⟨χ,z⟩,⟨hp,hz⟩,rfl⟩⟩

theorem globalLift_injective {X q : ℕ} [NeZero q] :
    Set.InjOn (globalLift q) (↑((globalModesAt X).filter (fun i => globalLevel i ∣ q)) : Set GlobalMode) := by
  intro i hi j hj he
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some j =>
          have hd : j.1 ∣ q := (mem_filter.mp hj).2
          simp only [globalLift,dite_eq_left hd,reduceCtorEq] at he
  | some i =>
      cases j with
      | none =>
          have hd : i.1 ∣ q := (mem_filter.mp hi).2
          simp only [globalLift,dite_eq_left hd,reduceCtorEq] at he
      | some j =>
          obtain ⟨r,χ,z⟩ := i
          obtain ⟨s,ψ,w⟩ := j
          have hr : r ∣ q := (mem_filter.mp hi).2
          have hs : s ∣ q := (mem_filter.mp hj).2
          have hpχ := (mem_globalModesAt_zero χ z).mp (mem_filter.mp hi).1
          have hpψ := (mem_globalModesAt_zero ψ w).mp (mem_filter.mp hj).1
          have h : (⟨changeLevel hr χ,z⟩ : Σ _ : DirichletCharacter ℂ q, ℂ) =
              ⟨changeLevel hs ψ,w⟩ := by simpa only [globalLift,dite_eq_left hr,dite_eq_left hs,Option.some.injEq] using he
          have hc := congrArg (fun a : Σ _ : DirichletCharacter ℂ q, ℂ => a.1) h
          have hr' := congrArg DirichletCharacter.conductor hc
          change (changeLevel hr χ).conductor = (changeLevel hs ψ).conductor at hr'
          rw [conductor_changeLevel χ hr, conductor_changeLevel ψ hs,
            (isPrimitive_def _).mp hpχ.2.2.1, (isPrimitive_def _).mp hpψ.2.2.1] at hr'
          subst s
          have hχ : χ = ψ := changeLevel_injective hr hc
          have hZ : z = w := congrArg (fun a : Σ _ : DirichletCharacter ℂ q, ℂ => Sigma.snd a) h
          subst ψ
          subst w
          rfl

private theorem primitive_mem_short_lift {X q r : ℕ} [NeZero q] [NeZero r]
    (hrq : r ∣ q) {χ : DirichletCharacter ℂ r} (hχ : χ.IsPrimitive) {z : ℂ} :
    z ∈ globalShortZeros X r χ ↔
      z ∈ (exceptionalZeros (changeLevel hrq χ) (heightCut (X:ℝ))).filter
        (shortNearZero X (changeLevel hrq χ).conductor) := by
  have hp : (changeLevel hrq χ).conductor = r := (conductor_changeLevel χ hrq).trans hχ
  simp only [globalShortZeros,dite_eq_left (NeZero.ne r),mem_filter,hp]
  rw [mem_exceptionalZeros,mem_exceptionalZeros]
  constructor
  · rintro ⟨⟨hβ,ht,hZ⟩,hN⟩
    have hβp : 0 < z.re := by linarith
    have hne : z ≠ 1 := fun e => regularizedL_ne_zero_at_one χ (e ▸ hZ)
    exact ⟨⟨hβ,ht,(changeLevel_regularized_zero_iff hrq χ hβp hne).2 hZ⟩,hN⟩
  · rintro ⟨⟨hβ,ht,hZ⟩,hN⟩
    have hβp : 0 < z.re := by linarith
    have hne : z ≠ 1 := fun e => regularizedL_ne_zero_at_one (changeLevel hrq χ) (e ▸ hZ)
    exact ⟨⟨hβ,ht,(changeLevel_regularized_zero_iff hrq χ hβp hne).1 hZ⟩,hN⟩

theorem globalModes_lift_exact {X q : ℕ} [NeZero q] (hqP : q ≤ cutoff X) :
    ((globalModesAt X).filter (fun i => globalLevel i ∣ q)).image (globalLift q) = shortModesAt X q := by
  ext i
  simp only [mem_image,mem_filter]
  constructor
  · rintro ⟨j,⟨hG,hdiv⟩,rfl⟩
    rcases j with _ | ⟨r,χ,z⟩
    · simp [globalLift,shortModesAt]
    · obtain ⟨hr,_,hp,hz⟩ := (mem_globalModesAt_zero χ z).mp hG
      have hd : r ∣ q := hdiv
      let _ : NeZero r := ⟨(Nat.zero_lt_one.trans_le hr).ne'⟩
      simp only [globalLift,dite_eq_left hd,shortModesAt,some_mem_insertNone,mem_sigma,mem_univ,true_and]
      exact (primitive_mem_short_lift hd hp).mp hz
  · intro hi
    rcases i with _ | ⟨χ,z⟩
    · exact ⟨none,⟨by simp [globalModesAt],one_dvd _⟩,rfl⟩
    · have hz : z ∈ (exceptionalZeros χ (heightCut (X:ℝ))).filter (shortNearZero X χ.conductor) := by
        simpa only [shortModesAt,some_mem_insertNone,mem_sigma,mem_univ,true_and] using hi
      let r := χ.conductor
      let _ : NeZero r := ⟨χ.conductor_ne_zero⟩
      let ψ := χ.primitiveCharacter
      have hr1 : 1 ≤ r := Nat.zero_lt_of_ne_zero χ.conductor_ne_zero
      have hd : r ∣ q := χ.conductor_dvd_level
      have hrP : r ≤ cutoff X := (Nat.le_of_dvd (NeZero.pos q) hd).trans hqP
      refine ⟨some ⟨r,ψ,z⟩,⟨(mem_globalModesAt_zero ψ z).mpr ⟨hr1,hrP,χ.primitiveCharacter_isPrimitive,?_⟩,hd⟩,?_⟩
      · apply (primitive_mem_short_lift hd χ.primitiveCharacter_isPrimitive).mpr
        simpa only [ψ,changeLevel_primitiveCharacter χ] using hz
      · simp only [globalLift,dite_eq_left hd,ψ,changeLevel_primitiveCharacter χ]

def globalProfile (X : ℕ) : GlobalMode → ℝ → ℂ
  | none => discreteModel X
  | some ⟨r,χ,z⟩ => if hr : r ≠ 0 then
      let _ : NeZero r := ⟨hr⟩
      fun β => -(analyticOrderNatAt (regularizedL χ) z : ℂ) *
        weightedTaperTransform X (2*X-1) (fun k => scaledWeight X k) (2*Real.pi*β) z
    else 0

theorem signedProfile_lift_eq_global {X q : ℕ} [NeZero q] {i : GlobalMode}
    (hi : i ∈ globalModesAt X) (hd : globalLevel i ∣ q) :
    signedProfile X q (globalLift q i) = globalProfile X i := by
  rcases i with _ | ⟨r,χ,z⟩
  · rfl
  obtain ⟨hr,_,_,hz⟩ := (mem_globalModesAt_zero χ z).mp hi
  let _ : NeZero r := ⟨(Nat.zero_lt_one.trans_le hr).ne'⟩
  have hD : r ∣ q := hd
  have hf : z ∈ (exceptionalZeros χ (heightCut (X:ℝ))).filter (shortNearZero X r) := by
    simpa only [globalShortZeros,dite_eq_left (NeZero.ne r)] using hz
  have he := (mem_filter.mp hf).1
  obtain ⟨hβ,_,hzero⟩ := (mem_exceptionalZeros _ _ _).mp he
  have hβp : 0 < z.re := by linarith
  have hne : z ≠ 1 := fun e => regularizedL_ne_zero_at_one χ (e ▸ hzero)
  simp only [globalLift,dite_eq_left hD,signedProfile,globalProfile,dite_eq_left (NeZero.ne r),
    changeLevel_regularized_order hD χ hβp hne]

end
end GoldbachSignedPairs

end


section

namespace GoldbachSignedPairs

open Finset Complex Goldbach GoldbachTwistedMellin GoldbachWeightedMajorResidual
open scoped Classical

noncomputable section

def modeGap (X : ℕ) : GlobalMode → ℝ
  | none => 0
  | some ⟨_,_,z⟩ => (1-z.re)*Real.log (X:ℝ)

def modeOrder : GlobalMode → ℕ
  | none => 1
  | some ⟨r,χ,z⟩ => if hr : r ≠ 0 then
      let _ : NeZero r := ⟨hr⟩
      analyticOrderNatAt (regularizedL χ) z
    else 0

def modeMass (X : ℕ) (i : GlobalMode) : ℝ :=
  (modeOrder i:ℝ) * Real.exp (-modeGap X i)

private theorem global_mode_zero {X r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r} {z : ℂ}
    (hi : (some ⟨r,χ,z⟩ : GlobalMode) ∈ globalModesAt X) : regularizedL χ z = 0 := by
  have hz := (mem_globalModesAt_zero χ z).mp hi |>.2.2.2
  have ht : z ∈ (exceptionalZeros χ (heightCut (X:ℝ))).filter (shortNearZero X r) := by
    simpa only [globalShortZeros,dite_eq_left (NeZero.ne r)] using hz
  exact ((mem_exceptionalZeros χ (heightCut (X:ℝ)) z).mp (mem_filter.mp ht).1).2.2

theorem global_mode_order_pos {X : ℕ} {i : GlobalMode} (hi : i ∈ globalModesAt X) :
    0 < modeOrder i := by
  rcases i with _ | ⟨r,χ,z⟩
  · simp [modeOrder]
  have hr := (mem_globalModesAt_zero χ z).mp hi |>.1
  let _ : NeZero r := ⟨(Nat.zero_lt_one.trans_le hr).ne'⟩
  simp only [modeOrder,dite_eq_left (NeZero.ne r)]
  exact (regularizedL_analyticOrderNatAt_pos_iff χ z).mpr (global_mode_zero hi)

theorem modeMass_nonneg (X : ℕ) (i : GlobalMode) : 0 ≤ modeMass X i := by
  unfold modeMass
  positivity

theorem modeMass_eq_power {X r : ℕ} [NeZero r] (hX : 0 < X) (χ : DirichletCharacter ℂ r) (z : ℂ) :
    modeMass X (some ⟨r,χ,z⟩) =
      (analyticOrderNatAt (regularizedL χ) z : ℝ)*(X:ℝ)^(z.re-1) := by
  have hXp : (0:ℝ)<X := by exact_mod_cast hX
  simp only [modeMass,modeOrder,modeGap,dite_eq_left (NeZero.ne r),Real.rpow_def_of_pos hXp]
  congr 2
  ring

theorem capped_mode_card_le {X : ℕ} {A : ℝ}
    (hmass : (∑ i ∈ globalModesAt X, modeMass X i) ≤ A) (L : ℝ) :
    (((globalModesAt X).filter (fun i => modeGap X i ≤ L)).card:ℝ) ≤ A*Real.exp L := by
  let G := globalModesAt X
  let S := G.filter (fun i => modeGap X i ≤ L)
  have h₀ (i : GlobalMode) (hi : i ∈ S) : Real.exp (-L) ≤ modeMass X i := by
    obtain ⟨hG,hL⟩ := mem_filter.mp hi
    have ho : (1:ℝ) ≤ (modeOrder i:ℝ) := by exact_mod_cast global_mode_order_pos hG
    unfold modeMass
    calc
      _ ≤ Real.exp (-modeGap X i) := Real.exp_le_exp.mpr (neg_le_neg hL)
      _ ≤ _ := le_mul_of_one_le_left (Real.exp_pos _).le ho
  have hs : (S.card:ℝ)*Real.exp (-L) ≤ A := calc
    _ = ∑ _i ∈ S,Real.exp (-L) := by simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ S,modeMass X i := sum_le_sum h₀
    _ ≤ _ := (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => modeMass_nonneg X i)).trans hmass
  have hp := mul_le_mul_of_nonneg_right hs (Real.exp_pos L).le
  rw [mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one] at hp
  exact hp

end
end GoldbachSignedPairs

end

section

namespace GoldbachPrincipalPintz

open Complex Set Filter MeasureTheory GoldbachCubicRiesz GoldbachPrincipalDensity
open GoldbachDensityDetector (zetaRieszPole)
open scoped Topology

private theorem regular_zeta_eq {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunctionTrivChar₁ 1 s = (s - 1) * riemannZeta s := by
  rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs]
  change (s - 1) * χ₁.LFunction s = _
  rw [DirichletCharacter.LFunction_modOne_eq]

private theorem regular_zeta_one : DirichletCharacter.LFunctionTrivChar₁ 1 1 = 1 := by
  simp [DirichletCharacter.LFunctionTrivChar₁]

private theorem integrable_of_continuous_tail {f : ℝ → ℂ} (hf : Continuous f) {A C : ℝ}
    (hbound : ∀ t, A ≤ |t| → ‖f t‖ ≤ C / (1 + t ^ 2)) : Integrable f := by
  let S : Set ℝ := Icc (-A) A
  have hcomp : IntegrableOn f S := hf.continuousOn.integrableOn_Icc
  have htail : IntegrableOn f Sᶜ := by
    have hmaj : IntegrableOn (fun t : ℝ => C / (1 + t ^ 2)) Sᶜ := by
      simpa only [div_eq_mul_inv] using (integrable_inv_one_add_sq.const_mul C).integrableOn
    apply hmaj.mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_Icc.compl : MeasurableSet Sᶜ)] with t ht
    exact hbound t (le_of_not_ge fun hs => ht (abs_le.mp hs))
  have h := hcomp.union htail
  rwa [Set.union_compl_self, integrableOn_univ] at h

set_option maxHeartbeats 1700000 in
/-- At a zero of ζ the regularized cubic detector acquires just the residue
from its simple pole at 1. -/
theorem principal_pintz_detector_identity (ρ : ℂ) (hρ : ρ ≠ 1) (hzero : riemannZeta ρ = 0)
    (hρlo : 3 / 4 ≤ ρ.re) (hρhi : ρ.re ≤ 1) (M : ℂ → ℂ) (hMd : Differentiable ℂ M)
    {B : ℝ} (hB : 0 ≤ B) (hMb : ∀ s, 1/2 ≤ s.re → ‖M s‖ ≤ B)
    (b : ℕ → ℂ) (hbS : LSeriesSummable b (ρ+1))
    (hRight : ∀ t : ℝ, let s := ρ + ((1:ℂ)+t*I); riemannZeta s*M s = LSeries b s)
    {Y : ℝ} (hY : 1 ≤ Y) :
    mellinInv (1 / 2 - ρ.re) (fun w =>
      riemannZeta (ρ + w) * M (ρ + w) * symbol w) (1 / Y) +
      zetaRieszPole Y (M 1) ρ = cutoffSum (LSeries.term b ρ) Y := by
  let a : ℝ := 1 / 2 - ρ.re
  let p : ℂ := 1 - ρ
  let F (w : ℂ) := (Y : ℂ)^w * (riemannZeta (ρ+w) * M (ρ+w))
  let H (w : ℂ) := (Y : ℂ)^w * (DirichletCharacter.LFunctionTrivChar₁ 1 (ρ+w) * M (ρ+w))
  let R := regularizedKernel H
  let f (w : ℂ) := R w / (w - p)
  let g := dslope R p
  let E : ℝ := 2 * |ρ.im| + 2
  let C : ℝ := Y * (3 + 2 * (‖ρ‖ + 1)) * B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hY₀ : 0 < Y := zero_lt_one.trans_le hY
  have hp₀ : p ≠ 0 := sub_ne_zero.mpr hρ.symm
  have hpRe : p.re = 1 - ρ.re := by simp [p, Complex.sub_re]
  have ha : a < p.re := by rw [hpRe]; dsimp [a]; linarith
  have hb : p.re < 1 := by rw [hpRe]; linarith only [hρlo]
  have hab : a ≤ 1 := (ha.trans hb).le
  have ha₀ : -1 < a := by dsimp [a]; linarith only [hρhi]
  have ha_ne : a ≠ 0 := by dsimp [a]; intro he; linarith only [hρlo, he]
  have hF0 : F 0 = 0 := by simp [F, hzero]
  have hH0 : H 0 = 0 := by simp [H, regular_zeta_eq hρ, hzero]
  have hH : Differentiable ℂ H :=
    (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hY₀.ne'))).mul
      (((DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).comp
      (differentiable_id.const_add ρ)).mul ((hMd).comp
      (differentiable_id.const_add ρ)))
  have hR : DifferentiableOn ℂ R {w : ℂ | -1 < w.re} := differentiableOn_regularizedKernel hH
  have hR_at (w : ℂ) (hw : -1 < w.re) : AnalyticAt ℂ R w :=
    hR.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw)
  have hR_p : R p = zetaRieszPole Y (M 1) ρ := by
    have hsum : ρ+p = 1 := by dsimp [p]; ring
    dsimp only [R]
    rw [regularizedKernel_eq hH0 hp₀]
    dsimp only [H]
    rw [hsum, regular_zeta_one, one_mul]
    unfold zetaRieszPole
    change 2 * ((Y : ℂ)^p * M 1) / (p*(p+1)*(p+2)) = _
    simp only [div_eq_mul_inv]
    ring
  have hH_eq (w : ℂ) (hw : w ≠ p) : H w = (w-p) * F w := by
    have hz : ρ+w ≠ 1 := by
      intro he
      apply hw
      dsimp [p]
      linear_combination he
    dsimp only [H,F]
    rw [regular_zeta_eq hz]
    dsimp [p]
    ring
  have hf_eq (w : ℂ) (hw₀ : w ≠ 0) (hwp : w ≠ p) : f w = regularizedKernel F w := by
    dsimp only [f,R]
    rw [regularizedKernel_eq hH0 hw₀, regularizedKernel_eq hF0 hw₀, hH_eq w hwp]
    rw [show 2 * ((w-p) * F w) / (w*(w+1)*(w+2)) =
      (w-p) * (2*F w / (w*(w+1)*(w+2))) by ring]
    exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hwp)
  have hLineRe (x t : ℝ) : (((x : ℂ) + t * I) : ℂ).re = x := by simp [Complex.mul_re]
  have hLineIm (x t : ℝ) : (((x : ℂ) + t * I) : ℂ).im = t := by simp [Complex.mul_im]
  have hdecay (x : ℝ) (hx : x ∈ Icc a 1) (t : ℝ) (ht : E ≤ |t|) :
      ‖f ((x : ℂ) + t * I)‖ ≤ (8*C) / (1 + t^2) := by
    let w := (x : ℂ) + t * I
    have ht₁ : 1 ≤ |t| := by dsimp [E] at ht; linarith only [ht, abs_nonneg ρ.im]
    have hw₀ : w ≠ 0 := by
      intro h
      have h' := congrArg Complex.im h
      rw [hLineIm, Complex.zero_im] at h'
      norm_num [h'] at ht₁
    have him (s : ℂ) : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm _
    have hdist : 1 / 2 ≤ ‖(ρ+w) - 1‖ := by
      have h₁ : |t| ≤ |ρ.im + t| + |ρ.im| := by
        have h := abs_add_le (ρ.im+t) (-ρ.im)
        rw [abs_neg, show ρ.im+t + -ρ.im = t by ring] at h
        exact h
      have h₂ := him (ρ+w-1)
      rw [Complex.sub_im, Complex.add_im, Complex.one_im, sub_zero, hLineIm] at h₂
      dsimp [E] at ht
      linarith only [h₁,h₂,ht,abs_nonneg ρ.im]
    have hwp : w ≠ p := by
      intro he
      rw [he, show ρ+p-1 = 0 by dsimp [p]; ring, norm_zero] at hdist
      norm_num at hdist
    have hsRe : 1 / 2 ≤ (ρ+w).re := by
      rw [Complex.add_re, hLineRe]
      have hx₁ := hx.1
      dsimp [a] at hx₁
      linarith only [hx₁]
    have hxnorm : |x| ≤ 1 := abs_le.mpr ⟨by dsimp [a] at hx; linarith only [hx.1,hρhi], hx.2⟩
    have hw_norm : ‖w‖ ≤ 1 + |t| := by
      apply (norm_add_le _ _).trans
      rw [norm_mul, norm_I, mul_one, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      exact add_le_add hxnorm le_rfl
    have hsNorm : ‖ρ+w‖ ≤ (‖ρ‖+1)*(1+|t|) := by
      apply (norm_add_le _ _).trans
      nlinarith only [hw_norm, mul_nonneg (norm_nonneg ρ) (abs_nonneg t)]
    have hL : ‖riemannZeta (ρ+w)‖ ≤ (3+2*(‖ρ‖+1))*(1+|t|) := by
      apply (zeta_norm_le_of_dist hsRe hdist).trans
      nlinarith only [hsNorm, abs_nonneg t]
    have hpow : ‖(Y : ℂ)^w‖ ≤ Y := by
      rw [norm_cpow_eq_rpow_re_of_pos hY₀,hLineRe]
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hY hx.2
    have hF : ‖F w‖ ≤ C*(1+|t|) := by
      dsimp only [F]
      rw [norm_mul,norm_mul]
      exact (mul_le_mul hpow (mul_le_mul hL (hMb _ hsRe)
        (norm_nonneg _) (by positivity)) (by positivity) hY₀.le).trans_eq (by dsimp [C]; ring)
    rw [hf_eq w hw₀ hwp]
    simpa only [w,hLineIm] using regularizedKernel_decay hF0 hC (w := w)
      (by simpa only [w,hLineIm] using ht₁) (by simpa only [w,hLineIm] using hF)
  have hVertical {x : ℝ} (hx : x ∈ Icc a 1) (hxP : x ≠ p.re) :
      Integrable (fun t : ℝ => f ((x : ℂ) + t * I)) := by
    have hRc : Continuous (fun t : ℝ => R ((x : ℂ) + t * I)) := by
      apply continuousOn_univ.mp
      apply hR.continuousOn.comp (by fun_prop)
      intro t _
      show -1 < (((x : ℂ) + t * I) : ℂ).re
      exact (hLineRe x t).symm ▸ ha₀.trans_le hx.1
    have hc : Continuous (fun t : ℝ => f ((x : ℂ) + t * I)) := by
      dsimp only [f]
      apply hRc.div (by fun_prop)
      intro t h
      exact hxP (by simpa only [hLineRe] using congrArg Complex.re (sub_eq_zero.mp h))
    exact integrable_of_continuous_tail hc (hdecay x hx)
  have hshift := vertical_integral_eq_of_simplePole (f := f) (g := g) (r := R p) ha hb
    (show 0 ≤ 8*C by positivity) (A := E)
    (fun w hw => ((hR_at w (ha₀.trans_le hw.1)).dslope p).continuousAt.continuousWithinAt)
    (fun w hw _ _ => ((hR_at w (ha₀.trans hw)).dslope p).differentiableAt)
    (fun w _ _ hw => by
      dsimp only [f,g]
      rw [dslope_of_ne R hw,slope_def_field]
      field_simp [sub_ne_zero.mpr hw]
      ring)
    (hVertical (left_mem_Icc.mpr hab) ha.ne) (hVertical (right_mem_Icc.mpr hab) hb.ne') hdecay
  have hYpow (w : ℂ) : ((1 / Y : ℝ) : ℂ)^(-w) = (Y : ℂ)^w := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (one_div_pos.mpr hY₀).ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hY₀.ne'),
      ← Complex.ofReal_log (one_div_pos.mpr hY₀).le, ← Complex.ofReal_log hY₀.le,
      Real.log_div one_ne_zero hY₀.ne', Real.log_one, zero_sub, Complex.ofReal_neg]
    congr 1
    ring
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hc : c * (2 * (Real.pi : ℂ)) = 1 := by
    dsimp [c]
    norm_cast
    field_simp [Real.pi_ne_zero]
  let W (w : ℂ) := riemannZeta (ρ+w) * M (ρ+w) * symbol w
  have hline (x : ℝ) (hx₀ : x ≠ 0) (hxP : x ≠ p.re) :
      mellinInv x W (1 / Y) = c * ∫ t : ℝ, f ((x : ℂ) + t * I) := by
    simp only [mellinInv, Complex.real_smul, smul_eq_mul]
    apply congrArg (fun z : ℂ => c*z)
    apply integral_congr_ae
    filter_upwards [] with t
    let w := (x : ℂ)+t*I
    have hw₀ : w ≠ 0 := fun h => hx₀ (by simpa only [w,hLineRe,Complex.zero_re] using congrArg Complex.re h)
    have hwp : w ≠ p := fun h => hxP (by simpa only [w,hLineRe] using congrArg Complex.re h)
    change ((1 / Y : ℝ) : ℂ)^(-w) * W w = f w
    rw [hYpow,hf_eq w hw₀ hwp,regularizedKernel_eq hF0 hw₀]
    dsimp only [W,F,symbol]
    simp only [div_eq_mul_inv]
    ring
  calc
    _ = mellinInv 1 W (1 / Y) := by
      change mellinInv a W (1 / Y) + _ = _
      rw [hline a ha_ne ha.ne, hline 1 one_ne_zero hb.ne', hshift, hR_p,mul_add,← mul_assoc,hc,one_mul]
    _ = mellinInv 1 (fun w => LSeries b (ρ+w) * symbol w) (1/Y) := by
      simp only [mellinInv,Complex.real_smul,smul_eq_mul,W]
      apply congrArg (fun z : ℂ => ((1/(2*Real.pi):ℝ):ℂ)*z)
      apply integral_congr_ae
      filter_upwards [] with t
      rw [Complex.ofReal_one,hRight t]
    _ = _ := shifted_cutoff_mellinInv (by norm_num) hY₀ b ρ hbS

end GoldbachPrincipalPintz

end


section

namespace GoldbachPrincipalPintz

open Finset Filter Complex Goldbach GoldbachSieveSeries GoldbachDensityDetector
open scoped Topology

theorem norm_lcmPolynomial_at_one_le {q : ℕ} (χ : DirichletCharacter ℂ q) (D E : ℕ)
    (u v : ℕ → ℂ) (hu : ∀ d ∈ Icc 1 D, ‖u d‖ ≤ 1) (hv : ∀ e ∈ Icc 1 E, ‖v e‖ ≤ 1) :
    ‖lcmPolynomial χ (Icc 1 D) (Icc 1 E) u v 1‖ ≤ (1+Real.log (D+E+1 : ℝ))^3 := by
  unfold lcmPolynomial
  refine (norm_sum_le _ _).trans ((sum_le_sum ?_).trans (lcm_inverse_mass D E))
  intro d hd
  refine (norm_sum_le _ _).trans (sum_le_sum (fun e he => ?_))
  rw [norm_mul, norm_mul]
  have hprod : ‖u d‖ * ‖v e‖ ≤ 1 := by
    simpa only [mul_one] using mul_le_mul (hu d hd) (hv e he) (norm_nonneg _) (zero_le_one : (0:ℝ) ≤ 1)
  refine (mul_le_of_le_one_left (norm_nonneg _) hprod).trans ?_
  by_cases hr : d.lcm e = 0
  · simp [hr]
  rw [LSeries.norm_term_eq, ite_eq_right hr, Complex.one_re, Real.rpow_one]
  exact div_le_div_of_nonneg_right (χ.norm_le_one _) (Nat.cast_nonneg _)


theorem zeta_near_pole_eventually {K A b : ℝ} (hK : 0 < K) (hA : 0 ≤ A) (hb : 0 ≤ b) :
    ∀ᶠ X : ℝ in atTop, ∀ (Y : ℝ) (M ρ : ℂ),
      1 ≤ Y → Real.log Y ≤ A*Real.log X → ‖M‖ ≤ (Real.log X)^b →
      regularizedL (1 : DirichletCharacter ℂ 1) ρ = 0 → ρ.re ≤ 1 →
      1-ρ.re < K*Real.log (Real.log X)/Real.log X →
      ‖zetaRieszPole Y M ρ‖ ≤ 1/32 := by
  let p := K*A+b+3
  have hp : 0 ≤ p := by dsimp [p]; positivity
  filter_upwards [zeta_near_zero_height_eventually hK hp,Real.tendsto_log_atTop.eventually_ge_atTop 4]
    with X hheight h4 Y M ρ hY hlogY hM hzero hρ hnear
  let L := Real.log X
  have hL : 0 < L := (by norm_num : (0:ℝ)<4).trans_le h4
  have hL1 : 1 ≤ L := (by norm_num : (1:ℝ)≤4).trans h4
  have hpγ := hheight ρ hzero hnear
  have hγ : ρ.im ≠ 0 := by
    intro hz
    simp only [hz,abs_zero] at hpγ
    exact (not_lt_of_ge (Real.rpow_nonneg hL.le p)) hpγ
  have hY0 := zero_lt_one.trans_le hY
  have hYP : Y^(1-ρ.re) ≤ L^(K*A) := by
    rw [Real.rpow_def_of_pos hY0,Real.rpow_def_of_pos hL]
    apply Real.exp_le_exp.mpr
    have h₁ := mul_le_mul_of_nonneg_left hlogY (sub_nonneg.mpr hρ)
    have h₂ := (lt_div_iff₀ hL).mp hnear
    have h₃ := mul_le_mul_of_nonneg_left h₂.le hA
    linarith only [h₁,h₃,
      show (1-ρ.re)*(A*Real.log X) = A*((1-ρ.re)*Real.log X) by ring,
      show A*(K*Real.log (Real.log X)) = Real.log L*(K*A) by dsimp [L]; ring]
  have hn : 2 * Y^(1-ρ.re) * ‖M‖ ≤ 2 * L^(K*A+b) := by
    rw [Real.rpow_add hL, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hYP hM (norm_nonneg _) (Real.rpow_nonneg hL.le _)) (by norm_num)
  have hd : (L^p)^3 ≤ |ρ.im|^3 := pow_le_pow_left₀ (Real.rpow_nonneg hL.le _) hpγ.le 3
  have hPL : 0 < (L^p)^3 := pow_pos (Real.rpow_pos_of_pos hL _) _
  calc
    _ ≤ 2*Y^(1-ρ.re)*‖M‖/|ρ.im|^3 := norm_zetaRieszPole_le hY0 M ρ hγ
    _ ≤ 2*L^(K*A+b)/(L^p)^3 := div_le_div₀ (by positivity) hn hPL hd
    _ = 2*L^(K*A+b-p*3) := by
      rw [← Real.rpow_mul_natCast hL.le, mul_div_assoc, ← Real.rpow_sub hL]
      norm_num
    _ ≤ 2*L^(-3:ℝ) := by
      gcongr
      dsimp [p]
      nlinarith only [hA,hb,mul_nonneg hK.le hA]
    _ ≤ 1/32 := by
      rw [Real.rpow_neg hL.le, Real.rpow_ofNat, ← div_eq_mul_inv]
      apply (div_le_iff₀ (pow_pos hL 3)).mpr
      have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4) h4 3
      norm_num at hcube
      linarith only [hcube]

end GoldbachPrincipalPintz

end


section

namespace GoldbachPrincipalPintz

open Finset Complex MeasureTheory Goldbach GoldbachDensityDetector GoldbachHybridGrowth
open GoldbachCubicRiesz GoldbachSieveSeries GoldbachPintzTheta GoldbachPintzDetector

theorem norm_polynomial_one_le {q : ℕ} (χ : DirichletCharacter ℂ q) {U V W : ℝ}
    (hU : 0 < U) (hUV : U < V) (hθ : ∀ d, |θ d| ≤ 1) :
    ‖polynomial χ U V W θ 1‖ ≤ (1+Real.log (⌊V⌋₊+⌊W⌋₊+1 : ℝ))^3 := by
  rw [polynomial, ← lcmPolynomial_eq]
  apply norm_lcmPolynomial_at_one_le
  · intro d _
    simpa using abs_barbanVehov_le_one (d := d) hU hUV
  · intro d _
    simpa using hθ d

set_option maxHeartbeats 1500000 in
private theorem shifted_zeta_mellin_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℂ), (3/4:ℝ) ≤ ρ.re → ρ.re ≤ 1 →
    ∀ (Y B : ℝ), 1 ≤ Y → 0 ≤ B → ∀ M : ℂ → ℂ,
      (∀ s, 1/2 ≤ s.re → ‖M s‖ ≤ B) →
      ‖mellinInv (1/2-ρ.re) (fun w => riemannZeta (ρ+w)*M (ρ+w)*symbol w) (1/Y)‖ ≤
        C*B*Y^(1/2-ρ.re)*(1+|ρ.im|)^(1/2:ℝ) := by
  let K : ℝ := ∫ t : ℝ, (1+t^2)⁻¹
  have hK : 0 ≤ K := integral_nonneg (fun _ => by positivity)
  refine ⟨3000*(K+1), by positivity, ?_⟩
  intro ρ hlo hhi Y B hY hB M hM
  let a := (1/2:ℝ)-ρ.re
  let C : ℝ := 3000*B*Y^a*(1+|ρ.im|)^(1/2:ℝ)
  let F (t : ℝ) : ℂ := let w := (a:ℂ)+t*I
    (((1/Y : ℝ):ℂ)^(-w)) * (riemannZeta (ρ+w)*M (ρ+w)*symbol w)
  have hY0 := zero_lt_one.trans_le hY
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hG : Integrable (fun t : ℝ => C*(1+t^2)⁻¹) := integrable_inv_one_add_sq.const_mul C
  have hF (t : ℝ) : ‖F t‖ ≤ C*(1+t^2)⁻¹ := by
    let w := (a:ℂ)+t*I
    have hwR : w.re = a := by simp [w,Complex.mul_re]
    have hs : (ρ+w).re = 1/2 := by rw [Complex.add_re,hwR]; dsimp [a]; ring
    have hI : (ρ+w).im = ρ.im+t := by simp [w,Complex.mul_im]
    have hz := zeta_LFunction_bound (s:=ρ+w) (by rw [hs]; norm_num) (by rw [hs]; norm_num)
    rw [hs,hI,show ((2/(1-1/2)+1/(1/2):ℝ)) = 6 by norm_num,show (1:ℝ)-1/2=1/2 by norm_num] at hz
    have hle : 1+|ρ.im+t| ≤ (1+|ρ.im|)*(1+|t|) := by
      nlinarith only [abs_add_le ρ.im t,mul_nonneg (abs_nonneg ρ.im) (abs_nonneg t)]
    have hbound : ‖riemannZeta (ρ+w)‖ ≤ 12*(1+|ρ.im|)^(1/2:ℝ)*(1+|t|) := by
      refine hz.trans ?_
      have hmon := Real.rpow_le_rpow (show (0:ℝ) ≤ 4*(1+|ρ.im+t|) by positivity)
        (mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ)≤4)) (by norm_num : (0:ℝ)≤1/2)
      have hpow : (1+|t|)^(1/2:ℝ) ≤ 1+|t| := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
          (by linarith only [abs_nonneg t] : 1≤1+|t|) (by norm_num : (1/2:ℝ)≤1)
      calc
        _ ≤ 6*(4*((1+|ρ.im|)*(1+|t|)))^(1/2:ℝ) :=
          mul_le_mul_of_nonneg_left hmon (by norm_num)
        _ ≤ _ := by
          rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4) (show 0≤(1+|ρ.im|)*(1+|t|) by positivity)]
          rw [Real.mul_rpow (by positivity : 0≤1+|ρ.im|) (by positivity)]
          have hf : (4:ℝ)^(1/2:ℝ)=2 := by rw [← Real.sqrt_eq_rpow]; norm_num
          rw [hf]
          nlinarith only [mul_le_mul_of_nonneg_left hpow (show 0≤(1+|ρ.im|)^(1/2:ℝ) by positivity)]
    have hsym := GoldbachTypeII.symbol_left_bound (a:=a) (t:=t) (by dsimp [a]; linarith) (by dsimp [a]; linarith)
    have hsym' : ‖symbol w‖ ≤ 250/(1+|t|)^3 := by simpa [w] using hsym
    have hpow : ‖((1/Y:ℝ):ℂ)^(-w)‖ = Y^a := by
      rw [norm_cpow_eq_rpow_re_of_pos (one_div_pos.mpr hY0), Complex.neg_re, hwR,
        Real.div_rpow zero_le_one hY0.le, Real.one_rpow, Real.rpow_neg hY0.le, one_div, inv_inv]
    have hsum : 1+t^2 ≤ (1+|t|)^2 := by
      rw [← sq_abs t]
      nlinarith only [abs_nonneg t]
    have hMh := hM (ρ+w) (by rw [hs])
    change ‖((1/Y:ℝ):ℂ)^(-w) * (riemannZeta (ρ+w)*M (ρ+w)*symbol w)‖ ≤ _
    simp only [norm_mul,hpow]
    calc
      _ ≤ Y^a * ((12*(1+|ρ.im|)^(1/2:ℝ)*(1+|t|))*B*(250/(1+|t|)^3)) := by
        gcongr
      _ = C/(1+|t|)^2 := by
        dsimp [C]
        field_simp
        <;> ring
      _ ≤ _ := by rw [← div_eq_mul_inv]; exact div_le_div_of_nonneg_left hC (by positivity) hsum
  have hnorm := norm_integral_le_of_norm_le hG (Filter.Eventually.of_forall hF)
  rw [integral_const_mul] at hnorm
  have hpi : (1/(2*Real.pi) : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Real.pi_gt_three])
  have hpi0 : (0:ℝ)≤1/(2*Real.pi) := by positivity
  change ‖((1/(2*Real.pi):ℝ):ℂ) • ∫ t, F t‖ ≤ _
  rw [smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpi0]
  refine (mul_le_of_le_one_left (norm_nonneg _) hpi).trans (hnorm.trans ?_)
  calc
    _ ≤ C*(K+1) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hC
    _ = _ := by dsimp [C]; ring

set_option maxHeartbeats 1500000 in
theorem compact_zeta_detector_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℂ), ρ ≠ 1 → riemannZeta ρ = 0 →
    (3/4:ℝ) ≤ ρ.re → ρ.re ≤ 1 →
    ∀ {U V W Y : ℝ} {θ : ℕ → ℝ}, 2 ≤ U → U < V → 1 ≤ W → U ≤ Y →
      θ 1 = 1 → (∀ d, |θ d| ≤ 1) →
      (1/4:ℝ) ≤
        ‖∑ n ∈ support Y, LSeries.term (coefficient (1 : DirichletCharacter ℂ 1) U V W θ) ρ n *
          (differenceWeight Y U n : ℂ)‖ +
        C*(12*Real.sqrt V*Real.sqrt W)*Y^(1/2-ρ.re)*(1+|ρ.im|)^(1/2:ℝ) +
        ‖zetaRieszPole Y (polynomial (1 : DirichletCharacter ℂ 1) U V W θ 1) ρ‖ := by
  obtain ⟨C,hC,hleft⟩ := shifted_zeta_mellin_norm_bound
  refine ⟨C,hC,?_⟩
  intro ρ hρ hz hlo hhi U V W Y θ hU hUV hW hUY hθ1 hθ
  let χ : DirichletCharacter ℂ 1 := 1
  let b := coefficient χ U V W θ
  let f := LSeries.term b ρ
  let M := polynomial χ U V W θ
  let B := 12*Real.sqrt V*Real.sqrt W
  let leftTerm := mellinInv (1/2-ρ.re) (fun w => riemannZeta (ρ+w)*M (ρ+w)*symbol w) (1/Y)
  let P := zetaRieszPole Y (M 1) ρ
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hU0 : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hY := hU1.trans hUY
  have hM (s : ℂ) (hs : 1/2 ≤ s.re) : ‖M s‖ ≤ B := (norm_polynomial_le_bound χ U V W θ hs).trans
      (polynomialBound_le_sqrt χ hU0 hUV (zero_le_one.trans hW) hθ)
  have hb : LSeriesSummable b (ρ+1) := by
    apply sieveProduct_summable
    simp only [add_re,one_re]
    linarith
  have hright (t : ℝ) :
      let s := ρ + ((1:ℂ)+t*I)
      riemannZeta s * M s = LSeries b s := by
    dsimp only
    have hs : 1 < (ρ+((1 : ℂ)+t*I)).re := by simp [add_re,mul_re]; linarith
    rw [← DirichletCharacter.LFunction_modOne_eq (χ := χ)]
    change χ.LFunction (ρ+(1+t*I)) * polynomial χ U V W θ (ρ+(1+t*I)) =
      LSeries (coefficient χ U V W θ) (ρ+(1+t*I))
    rw [mul_comm]
    exact (sieveProduct_LSeries χ (support V) (support W)
      (fun d => (barbanVehov U V d:ℂ)) (fun d => (θ d:ℂ)) hs).symm
  have hidentity : leftTerm+P = cutoffSum f Y :=
    principal_pintz_detector_identity ρ hρ hz hlo hhi M (differentiable_polynomial χ _ _ _ _)
      hB hM b hb hright hY
  have hn : (1/4 : ℝ) ≤ ‖cutoffSum f U‖ := by
    rw [cutoff_short χ hU1 le_rfl hUV hW hθ1 ρ]
    have he : (1-1/(U : ℂ))^2 = (((1-1/U)^2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hu2 := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hU
    have hhalf : (1/2:ℝ) ≤ 1-1/U := by linarith
    nlinarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) hhalf 2]
  rw [← cutoff_sub_eq_difference f hU0 hUY]
  calc
    _ ≤ ‖cutoffSum f U‖ := hn
    _ = ‖leftTerm+P-(cutoffSum f Y-cutoffSum f U)‖ := by rw [hidentity]; congr 1; ring
    _ ≤ ‖leftTerm‖+‖P‖+‖cutoffSum f Y-cutoffSum f U‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      have hh : ‖leftTerm‖ ≤ C*B*Y^(1/2-ρ.re)*(1+|ρ.im|)^(1/2:ℝ) := hleft ρ hlo hhi Y B hY hB M hM
      dsimp only [P,B] at *
      linarith only [hh]

end GoldbachPrincipalPintz

end


section

namespace GoldbachPintzDiagonal

open Complex Finset Goldbach GoldbachTwistedMellin GoldbachLinnik
open GoldbachCubicRiesz GoldbachSieveSeries GoldbachPintzHalasz GoldbachPintzCharacters
open GoldbachPintzTheta GoldbachPintzDetector
open scoped ComplexConjugate

noncomputable section

/-- Same-character diagonal row for the compact Halász matrix, with full
analytic multiplicities and a separate left-line error per zero. -/
theorem regularized_same_character_gram_row_le {ε K L : ℝ} (hε : 0 < ε) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    ∃ A E : ℝ, 0 < A ∧ 0 < E ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), ∀ (Q : ℕ), q ≤ Q →
      ∀ {δ T W Y U : ℝ}, 0 ≤ δ → δ ≤ 1/8 → 0 ≤ T → 1 < W → 4 ≤ Real.log Y →
      logHeight Q (T+2) ≤ K*Real.log Y → Real.log Y ≤ L*Real.log W →
      1 ≤ U → U ≤ Y → ∀ (θ : ℕ → ℝ), (∀ j, |θ j| ≤ 1) →
      (((q^2 : ℕ).totient : ℝ)/((q^2 : ℕ) : ℝ))*quadratic (Icc 1 ⌊W⌋₊) θ (q^2) ≤
        16/Real.log W →
      ∀ (S : Finset ℂ), (∀ ω ∈ S, 1-δ ≤ ω.re ∧ ω.re < 1 ∧ |ω.im| ≤ T ∧ regularizedL χ ω = 0) →
      ∀ ρ ∈ S,
      (∑ ω ∈ S, (analyticOrderNatAt (regularizedL χ) ω : ℝ) *
        ‖gramSum (support Y) (differenceWeight Y U) (realDivisorWeight (Icc 1 ⌊W⌋₊) θ)
          (fun n => χ (n : ZMod q)) (fun n => χ (n : ZMod q)) ρ ω‖) ≤
        A*Y^(2*δ)*(1+δ*logHeight Q (T+2))*(1+Real.log (1+(S.card : ℝ))) +
        (E*W*U^(-(1/2 : ℝ)+2*δ)*(q : ℝ)^ε*(1+2*T)^(1/2 : ℝ)) *
          ∑ ω ∈ S, (analyticOrderNatAt (regularizedL χ) ω : ℝ) := by
  obtain ⟨E,hE,hEntry⟩ := same_character_gram_entry_le hε hL
  obtain ⟨C,hC,hRow⟩ := same_character_near_zero_row_le
  refine ⟨64*(L+1)*C*(K+1),E,by positivity,hE,?_⟩
  intro q _ χ Q hq δ T W Y U hδ hδmax hT hW hYlog hHeight hRatio hU hUY θ hθ hΘ S hS ρ hρ
  let ℓ := Real.log Y
  let H := logHeight Q (T+2)
  let d := max δ ℓ⁻¹
  let m (ω : ℂ) : ℝ := analyticOrderNatAt (regularizedL χ) ω
  let G (ω : ℂ) := gramSum (support Y) (differenceWeight Y U)
    (realDivisorWeight (Icc 1 ⌊W⌋₊) θ) (fun n => χ (n : ZMod q)) (fun n => χ (n : ZMod q)) ρ ω
  let B := 64*(L+1)*Y^(2*δ)
  let e := E*W*U^(-(1/2 : ℝ)+2*δ)*(q : ℝ)^ε*(1+2*T)^(1/2 : ℝ)
  have hℓ : 0 < ℓ := by dsimp only [ℓ]; linarith
  have hℓ₁ : 4 ≤ ℓ := hYlog
  have hd : 0 < d := (inv_pos.mpr hℓ).trans_le (le_max_right _ _)
  have hd₁ : d ≤ 1/4 := by
    apply max_le (hδmax.trans (by norm_num))
    rw [← one_div]
    exact (div_le_iff₀ hℓ).mpr (by linarith)
  have : NeZero Q := ⟨((NeZero.pos q).trans_le hq).ne'⟩
  have hH : 0 ≤ H := by
    dsimp only [H]
    exact zero_le_one.trans (logHeight_ge_one Q (T+2))
  have hYp : 0 ≤ Y := (zero_le_one.trans hU).trans hUY
  have hBH : 0 ≤ B := by dsimp only [B]; positivity
  have hθRow (ω : ℂ) (hω : ω ∈ S) :
      ‖G ω‖ ≤ B/(1+|(ω.im-ρ.im)/d|)+e := by
    obtain ⟨hρl,hρh,hρT,_⟩ := hS ρ hρ
    obtain ⟨hωl,hωh,hωT,_⟩ := hS ω hω
    exact hEntry q χ ρ ω hδ hδmax hρl hρh hωl hωh hρT hωT hW hℓ hRatio hU hUY
      hd (le_max_right _ _) θ hθ hΘ
  have hzero (ω : ℂ) (hω : ω ∈ S) :
      1-d ≤ ω.re ∧ ω.re ≤ 1 ∧ |ω.im| ≤ T ∧ regularizedL χ ω = 0 := by
    obtain ⟨hl,hh,ht,hz⟩ := hS ω hω
    refine ⟨(sub_le_sub_left (le_max_left δ ℓ⁻¹) 1).trans hl,hh.le,ht,?_⟩
    exact hz
  have hraw := hRow q χ Q hq d T ρ.im hd hd₁ hT S hzero
  have hEff : 1+d*H ≤ (K+1)*(1+δ*H) := by
    have hd' : d ≤ δ+ℓ⁻¹ :=
      max_le (le_add_of_nonneg_right (inv_nonneg.mpr hℓ.le)) (le_add_of_nonneg_left hδ)
    have hInv : ℓ⁻¹*H ≤ K := by
      rw [mul_comm, ← div_eq_mul_inv]
      exact (div_le_iff₀ hℓ).mpr hHeight
    have hprod := mul_le_mul_of_nonneg_right hd' hH
    have hCross : 0 ≤ K*δ*H := by positivity
    nlinarith only [hprod,hInv,hCross]
  have hLog : 0 ≤ 1+Real.log (1+(S.card : ℝ)) := by
    have hh := Real.log_nonneg (show 1 ≤ 1+(S.card : ℝ) from le_add_of_nonneg_right (Nat.cast_nonneg _))
    linarith
  have hsplit (ω : ℂ) : m ω*(B/(1+|(ω.im-ρ.im)/d|)+e) =
      B*(m ω/(1+|(ω.im-ρ.im)/d|))+e*m ω := by ring
  change (∑ ω ∈ S, m ω*‖G ω‖) ≤ _ + e*(∑ ω ∈ S, m ω)
  calc
    _ ≤ ∑ ω ∈ S, m ω*(B/(1+|(ω.im-ρ.im)/d|)+e) :=
      sum_le_sum (fun ω hω => mul_le_mul_of_nonneg_left (hθRow ω hω) (by dsimp only [m]; positivity))
    _ = B*(∑ ω ∈ S, m ω/(1+|(ω.im-ρ.im)/d|))+e*(∑ ω ∈ S, m ω) := by
      simp only [hsplit,Finset.sum_add_distrib,← Finset.mul_sum]
    _ ≤ B*(C*(1+d*H)*(1+Real.log (1+(S.card : ℝ))))+e*(∑ ω ∈ S,m ω) :=
      (add_le_add) (mul_le_mul_of_nonneg_left hraw hBH) le_rfl
    _ ≤ B*(C*((K+1)*(1+δ*H))*(1+Real.log (1+(S.card : ℝ))))+e*(∑ ω ∈ S,m ω) :=
      (add_le_add) (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEff hC.le) hLog) hBH) le_rfl
    _ = _ := by dsimp only [B,H]; ring

end
end GoldbachPintzDiagonal

end


section

namespace GoldbachPintzFamily

open Finset Complex Goldbach GoldbachTwistedMellin GoldbachTypeII GoldbachPintzHalasz GoldbachHalasz
open scoped Classical

noncomputable section

set_option maxHeartbeats 900000 in
/-- Apply the finite-table bound to full rows, retaining the uniform Gram error. -/
theorem count_of_full_height_rows {A K L τ ε : ℝ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hL : 0 ≤ L) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (Q : ℕ) {δ T Y : ℝ}, 0 ≤ δ → 1 ≤ Y →
      logHeight Q (T+2) ≤ K*Real.log Y →
      ∀ (Z : Finset ι) (order : ι → ℕ) (χ : ι → ℕ → ℂ) (ρ : ι → ℂ)
        (D E : Finset ℕ) (w ψ θ : ℕ → ℝ) (e : ℝ),
      let S := Icc 1 ⌊Y⌋₊
      L*e/τ^2 ≤ 1/2 → (∀ n ∈ S, 0 ≤ w n) →
      (∑ n ∈ S, (realDivisorWeight D ψ n)^2*w n/(n:ℝ)) ≤ L →
      (∀ r ∈ Z, τ ≤ ‖detectorSum S w (realDivisorWeight D ψ) (realDivisorWeight E θ) (χ r) (ρ r)‖) →
      (∀ r ∈ Z, (∑ s ∈ Z, (order s:ℝ)*‖gramSum S w (realDivisorWeight E θ) (χ r) (χ s) (ρ r) (ρ s)‖) ≤
        A*Y^(2*δ)*(1+δ*logHeight Q (T+2))*(1+Real.log (1+∑ s ∈ Z,(order s:ℝ)))+
          e*(∑ s ∈ Z,(order s:ℝ))) →
      (∑ r ∈ Z, (order r:ℝ)) ≤ C*Y^(2*δ*(1+ε)) := by
  have hA' : 0 ≤ A*(1+K) := by positivity
  obtain ⟨C,hC,hbound⟩ := count_le_of_multiplicity_full_rows hA' (by norm_num : (0:ℝ) ≤ 1) hL hτ hε
  refine ⟨max 1 C,zero_lt_one.trans_le (le_max_left _ _),?_⟩
  intro ι Q δ T Y hδ hY hHeight Z order χ ρ D E w ψ θ e S he₂ hw hE hdet hdiag
  let J : ℝ := ∑ s ∈ Z,(order s:ℝ)
  have hJ₀ : 0 ≤ J := sum_nonneg fun r _ => Nat.cast_nonneg (order r)
  have hY₀ := zero_lt_one.trans_le hY
  have hYpow : 0 ≤ Y^(2*δ*(1+ε)) := Real.rpow_nonneg hY₀.le _
  by_cases hsmall : J ≤ Y^(2*δ)
  · calc
      _ ≤ Y^(2*δ) := hsmall
      _ ≤ Y^(2*δ*(1+ε)) := Real.rpow_le_rpow_of_exponent_le hY
        (by nlinarith only [mul_nonneg hδ hε.le])
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) C) hYpow
  · have hh := heightGap_le_large_countLog hY₀ hδ hK hHeight (lt_of_not_ge hsmall)
    have hlog := Real.log_nonneg (show 1 ≤ 1+J from le_add_of_nonneg_right hJ₀)
    have hlog' : 0 ≤ 1+Real.log (1+J) := by linarith only [hlog]
    have hdiag' (r : ι) (hr : r ∈ Z) :
        (∑ s ∈ Z,(order s:ℝ)*‖gramSum S w (realDivisorWeight E θ) (χ r) (χ s) (ρ r) (ρ s)‖) ≤
          (A*(1+K))*Real.exp (1*(2*δ*Real.log Y))*(1+Real.log (1+J))^2+e*J := calc
      _ ≤ A*Y^(2*δ)*(1+δ*logHeight Q (T+2))*(1+Real.log (1+J))+e*J := hdiag r hr
      _ ≤ A*Y^(2*δ)*((1+K)*(1+Real.log (1+J)))*(1+Real.log (1+J))+e*J :=
        (add_le_add) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh
          (mul_nonneg hA (Real.rpow_nonneg hY₀.le _))) hlog') le_rfl
      _ = _ := by rw [one_mul,Real.rpow_def_of_pos hY₀,mul_comm (Real.log Y)]; ring
    have hS (n : ℕ) (hn : n ∈ S) : n ≠ 0 := (Nat.zero_lt_one.trans_le (mem_Icc.mp hn).1).ne'
    have hH := detector_gram_halasz S hS Z order w (realDivisorWeight D ψ)
      (realDivisorWeight E θ) hw χ ρ
    have h := hbound Z order (fun r => detectorSum S w (realDivisorWeight D ψ) (realDivisorWeight E θ) (χ r) (ρ r))
      (fun r s => gramSum S w (realDivisorWeight E θ) (χ r) (χ s) (ρ r) (ρ s))
      (2*δ*Real.log Y) e _ hE he₂ hdet hH hdiag'
    have h' : J ≤ C*Y^(2*δ*(1+ε)) := h.trans_eq (by
      rw [mul_one,Real.rpow_def_of_pos hY₀]
      congr 2
      ring)
    exact h'.trans (mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) C) hYpow)

end
end GoldbachPintzFamily

end


section

namespace GoldbachPrincipalPintz

open Finset Filter Complex Goldbach GoldbachDensityDetector GoldbachPintzScales
open GoldbachPintzHalasz GoldbachPintzFamily GoldbachPintzTheta GoldbachPintzDetector GoldbachSieveSeries
open scoped Classical Topology

private theorem at_one_polylog {X V W Y : ℝ} (hX : 4 ≤ Real.log X) (hY : 1 ≤ Y)
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hVY : V ≤ Y) (hWY : W ≤ Y)
    (hlogY : Real.log Y ≤ 3*Real.log X) :
    (1+Real.log (⌊V⌋₊+⌊W⌋₊+1 : ℝ))^3 ≤ (Real.log X)^(6:ℝ) := by
  have hlog3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
  have hVT := Nat.floor_le hV
  have hWT := Nat.floor_le hW
  have hM : (⌊V⌋₊+⌊W⌋₊+1:ℝ) ≤ 3*Y := by linarith only [hY,hVY,hWY,hVT,hWT]
  have hlog := Real.log_le_log (by positivity : 0 < (⌊V⌋₊+⌊W⌋₊+1:ℝ)) hM
  rw [Real.log_mul (by norm_num) (zero_lt_one.trans_le hY).ne'] at hlog
  have hp := mul_nonneg (sub_nonneg.mpr hX) (show 0≤Real.log X-3 by linarith only [hX])
  have hB : 1+Real.log (⌊V⌋₊+⌊W⌋₊+1 : ℝ) ≤ (Real.log X)^2 := by nlinarith only [hp,hlog,hlogY,hlog3,hX]
  have hB0 : 0 ≤ 1+Real.log (⌊V⌋₊+⌊W⌋₊+1 : ℝ) := by
    exact add_nonneg zero_le_one (Real.log_nonneg (by linarith only [Nat.cast_nonneg (α:=ℝ) ⌊V⌋₊,Nat.cast_nonneg (α:=ℝ) ⌊W⌋₊]))
  exact (pow_le_pow_left₀ hB0 hB 3).trans_eq (by rw [Real.rpow_ofNat]; ring)

private theorem regularized_one_zero (ρ : ℂ)
    (h : regularizedL (1 : DirichletCharacter ℂ 1) ρ = 0) : ρ ≠ 1 ∧ riemannZeta ρ = 0 := by
  have hρ : ρ ≠ 1 := fun he => regularizedL_ne_zero_at_one (1 : DirichletCharacter ℂ 1) (he ▸ h)
  refine ⟨hρ,?_⟩
  rw [regularizedL, ite_eq_left rfl, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hρ] at h
  change (ρ-1)*(1:DirichletCharacter ℂ 1).LFunction ρ = 0 at h
  rw [DirichletCharacter.LFunction_modOne_eq] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hρ)

private theorem eventually_small_canonical (CD CE : ℝ) :
    ∀ᶠ H : ℝ in atTop, 4 ≤ Real.log H ∧ Real.log 16 / loss ≤ Real.log H ∧
      CD*H^(-4*loss) ≤ 1/16 ∧ CE*H^(-3*loss)/(1/8:ℝ)^2 ≤ 1/2 := by
  have hD := tendsto_rpow_neg_atTop (by unfold loss; norm_num : 0 < 4*loss)
  have hE := tendsto_rpow_neg_atTop (by unfold loss; norm_num : 0 < 3*loss)
  have hD' : Tendsto (fun H : ℝ => CD*H^(-4*loss)) atTop (𝓝 0) := by
    simpa only [neg_mul, mul_zero] using hD.const_mul CD
  have hE' : Tendsto (fun H : ℝ => CE*H^(-3*loss)/(1/8:ℝ)^2) atTop (𝓝 0) := by
    simpa only [neg_mul, mul_zero, zero_div] using (hE.const_mul CE).div_const ((1/8:ℝ)^2)
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 4,
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.log 16 / loss),
    hD'.eventually_lt_const (by norm_num : (0:ℝ) < 1/16),
    hE'.eventually_lt_const (by norm_num : (0:ℝ) < 1/2)] with H h₁ h₂ h₃ h₄
  exact ⟨h₁,h₂,h₃.le,h₄.le⟩

set_option maxHeartbeats 1600000 in
theorem principal_logfree_density_near {K : ℝ} (hK : 0 < K) :
    ∃ C H₀ : ℝ, 0 < C ∧
    ∀ᶠ X : ℝ in atTop, ∀ {δ T : ℝ}, 0 ≤ δ → δ ≤ loss → 1 ≤ T → H₀ ≤ T+1 → T+1 ≤ X →
    ∀ Z : Finset ℂ, (∀ ρ ∈ Z, 1-δ ≤ ρ.re ∧ |ρ.im| ≤ T ∧
        regularizedL (1 : DirichletCharacter ℂ 1) ρ = 0 ∧
        1-ρ.re < K*Real.log (Real.log X)/Real.log X) →
    (∑ ρ ∈ Z, (analyticOrderNatAt (regularizedL (1 : DirichletCharacter ℂ 1)) ρ : ℝ)) ≤
      C*(((T+1)^4)^((1+1/100:ℝ)*δ)) := by
  have hLoss : 0 < loss := by unfold loss; norm_num
  have hRatio : 0 ≤ 3/loss := by positivity
  obtain ⟨A,E,hA,hE,hrow⟩ := GoldbachPintzDiagonal.regularized_same_character_gram_row_le
    hLoss (K:=4) (L:=3/loss) (by norm_num) hRatio
  obtain ⟨CD,hCD,hdet⟩ := compact_zeta_detector_lower
  obtain ⟨L,H₁,hL,hnormBound⟩ :=
    GoldbachGrahamDiagonal.canonical_compact_harmonic_from_graham
  obtain ⟨C,hC,hcount⟩ := count_of_full_height_rows (L:=L) (K:=4) (τ:=1/8) (ε:=1/200)
    hA.le (by norm_num) hL.le (by norm_num) (by norm_num)
  obtain ⟨H₀,hlarge⟩ := eventually_atTop.1 (eventually_small_canonical (12*CD) (L*(2*E)))
  refine ⟨C,max H₀ H₁,hC,?_⟩
  filter_upwards [zeta_near_pole_eventually (A:=3) (b:=6) hK (by norm_num) (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop 4] with X hPole h4 δ T hδ hδloss hT hH hTX Z hZ
  let χ : DirichletCharacter ℂ 1 := 1
  let W := thetaScale 1 T
  let U := lowerScale 1 T
  let V := U*W
  let Y := upperScale 1 T
  let H := T+1
  let m (ρ : ℂ) := analyticOrderNatAt (regularizedL χ) ρ
  let J : ℝ := ∑ ρ ∈ Z,(m ρ:ℝ)
  let w := differenceWeight Y U
  let ψ := barbanVehov U V
  have hH0 : 0 < H := by dsimp [H]; linarith
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  obtain ⟨hL₁,hL₁₆,hDetE,hGramE⟩ := hlarge H ((le_max_left H₀ H₁).trans hH)
  have hW : 16 ≤ W := by
    unfold W thetaScale thetaLog
    rw [← Real.exp_log (by norm_num : 0 < (16:ℝ))]
    apply Real.exp_le_exp.mpr
    simpa only [H, Real.log_one, zero_add, mul_comm loss] using (div_le_iff₀ hLoss).mp hL₁₆
  obtain ⟨θ,hθ₁,hθ,_,hθq⟩ := exists_theta_real_of_sharp hW
  obtain ⟨hU,hW1,hUV,hVY,hnum,hden,hlogYbound⟩ := scale_relations (Q:=1) le_rfl hT
  simp only [one_mul] at hlogYbound
  have hU0 : 0 < U := by linarith only [hU]
  have hUY : U ≤ Y := hUV.le.trans hVY
  have hY : 1 ≤ Y := (by norm_num : (1:ℝ)≤2).trans (hU.trans hUY)
  have hWY : W ≤ Y := (le_mul_of_one_le_left (thetaScale_pos 1 T).le
    ((by norm_num : (1:ℝ)≤2).trans hU)).trans hVY
  have hYlog : 4 ≤ Real.log Y := by
    have hn := Real.log_nonneg (show 1 ≤ T+1 by linarith only [hT])
    simp only [Y,upperScale,Real.log_exp,upperLog,Real.log_one,mul_zero,zero_add]
    have hp := mul_nonneg hLoss.le hn
    nlinarith only [hL₁,hn,hp]
  have hlogYratio : Real.log Y ≤ (3/loss)*Real.log W := by
    change (loss/3)*Real.log Y ≤ Real.log (U*W/U) at hden
    rw [mul_div_cancel_left₀ W hU0.ne'] at hden
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hLoss).mpr
    linarith only [hden,show loss/3*Real.log Y = loss*Real.log Y/3 by ring]
  have hEnergyThreshold : H₁≤(1:ℝ)*(T+1) := by
    simpa only [one_mul] using (le_max_right H₀ H₁).trans hH
  have hnorm := hnormBound 1 le_rfl hT0 (by simpa only [Nat.cast_one] using hEnergyThreshold)
  have hHeight : logHeight 1 (T+2) ≤ 4*Real.log Y := by
    simpa only [Y,upperScale,Real.log_exp,Nat.cast_one,Real.log_one,zero_add] using
      logHeight_le_four_upperLog (Q:=1) le_rfl hT0
        (by simpa only [H,Nat.cast_one,Real.log_one,zero_add] using (by linarith only [hL₁] : 1≤Real.log H))
  have hlogYX : Real.log Y ≤ 3*Real.log X := hlogYbound.trans (mul_le_mul_of_nonneg_left
    (Real.log_le_log hH0 hTX) (by norm_num))
  have hW0 := (thetaScale_pos 1 T).le
  have hV0 : 0 ≤ V := mul_nonneg hU0.le hW0
  have hPpoly := (norm_polynomial_one_le χ hU0 hUV hθ).trans
    (at_one_polylog h4 hY hV0 hW0 hVY hWY hlogYX)
  have hgeom (ρ : ℂ) (hρ : ρ ∈ Z) :
      1-δ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T ∧ regularizedL χ ρ = 0 := by
    obtain ⟨hlo,ht,hz,_⟩ := hZ ρ hρ
    exact ⟨hlo,lt_of_not_ge (fun hn => GoldbachZeroFree.regularizedL_ne_zero_ge_one χ hn hz),ht,hz⟩
  have hDet (ρ : ℂ) (hρ : ρ ∈ Z) :
      (1/8:ℝ) ≤ ‖detectorSum (support Y) w (realDivisorWeight (support V) ψ)
        (realDivisorWeight (support W) θ) (fun n => χ (n:ZMod 1)) ρ‖ := by
    obtain ⟨hβ,hβ',ht,hz⟩ := hgeom ρ hρ
    obtain ⟨hne,hζ⟩ := regularized_one_zero ρ hz
    have hpole := hPole Y (polynomial χ U V W θ 1) ρ hY hlogYX hPpoly hz hβ'.le (hZ ρ hρ).2.2.2
    have hlo : (3/4:ℝ)≤ρ.re := by unfold loss at hδloss; linarith only [hβ,hδloss]
    have hraw := hdet ρ hne hζ hlo hβ'.le hU hUV hW1.le hUY hθ₁ hθ
    have hi : Y^(1/2-ρ.re) ≤ Y^(-1/2+δ) := Real.rpow_le_rpow_of_exponent_le hY (by linarith only [hβ])
    have ht' : (1+|ρ.im|)^(1/2:ℝ) ≤ (T+1)^(1/2:ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith only [ht]) (by norm_num)
    have hs := detector_error_scale (Q:=1) le_rfl hT hδloss
    simp only [Real.one_rpow,one_mul,mul_one] at hs
    have he : CD*(12*Real.sqrt V*Real.sqrt W)*Y^(1/2-ρ.re)*(1+|ρ.im|)^(1/2:ℝ) ≤ 1/16 := calc
      _ ≤ CD*(12*Real.sqrt V*Real.sqrt W)*Y^(-1/2+δ)*(T+1)^(1/2:ℝ) := by gcongr
      _ = 12*CD*(Real.sqrt V*Real.sqrt W*Y^(-1/2+δ)*(T+1)^(1/2:ℝ)) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hs (by positivity)).trans hDetE
    rw [detectorSum_eq_sieveProduct]
    change (1/8:ℝ) ≤ ‖∑ n ∈ support Y, LSeries.term (coefficient χ U V W θ) ρ n * (w n:ℂ)‖
    linarith only [hraw,he,hpole]
  have hcard : (Z.card:ℝ) ≤ J := calc
    _ = ∑ _ρ ∈ Z, (1:ℝ) := by simp [nsmul_eq_mul]
    _ ≤ _ := sum_le_sum (fun ρ hρ => by
      exact_mod_cast (regularizedL_analyticOrderNatAt_pos_iff χ ρ).mpr (hgeom ρ hρ).2.2.2)
  let e := (2*E)*H^(-3*loss)
  have hEscale : E*W*U^(-(1/2:ℝ)+2*δ)*(1:ℝ)^loss*(1+2*T)^(1/2:ℝ) ≤ e := by
    have hs := comparison_error_scale (Q:=1) le_rfl hT hδloss
    simp only [Real.one_rpow,one_mul,mul_one] at hs
    have hTpow : (1+2*T)^(1/2:ℝ) ≤ 2*(T+1)^(1/2:ℝ) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      calc
        _ ≤ Real.sqrt (4*(T+1)) := Real.sqrt_le_sqrt (by linarith only [hT0])
        _ = _ := by
          rw [Real.sqrt_mul (by norm_num),show Real.sqrt (4:ℝ)=2 by norm_num]
    calc
      _ ≤ E*W*U^(-(1/2:ℝ)+2*δ)*(1:ℝ)^loss*(2*(T+1)^(1/2:ℝ)) := by gcongr
      _ = (2*E)*(W*U^(-(1/2:ℝ)+2*δ)*(T+1)^(1/2:ℝ)) := by rw [Real.one_rpow]; ring
      _ ≤ e := by
        dsimp [e]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        change W*U^(-(1/2:ℝ)+2*δ)*(T+1)^(1/2:ℝ) ≤ H^(-3*loss)
        rw [show -(1/2:ℝ) = -1/2 by norm_num]
        exact hs
  have hδmax : δ ≤ 1/8 := by unfold loss at hδloss; linarith
  have hΘ := hθq (1^2) (by norm_num)
  have hErr : L*e/(1/8:ℝ)^2 ≤ 1/2 := by simpa only [e,← mul_assoc] using hGramE
  have hRow (ρ : ℂ) (hρ : ρ ∈ Z) :
      (∑ s ∈ Z,(m s:ℝ)*‖gramSum (support Y) w (realDivisorWeight (support W) θ)
        (fun n => χ (n:ZMod 1)) (fun n => χ (n:ZMod 1)) ρ s‖) ≤
      A*Y^(2*δ)*(1+δ*logHeight 1 (T+2))*(1+Real.log (1+J))+e*J := by
    refine (hrow 1 χ 1 le_rfl hδ hδmax hT0 hW1 hYlog hHeight hlogYratio
      ((by norm_num : (1:ℝ)≤2).trans hU) hUY θ hθ hΘ Z hgeom ρ hρ).trans ?_
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left
      · exact add_le_add le_rfl (Real.log_le_log (by positivity) (add_le_add le_rfl hcard))
      · have hh := logHeight_ge_one 1 (T+2)
        positivity
    · exact mul_le_mul_of_nonneg_right hEscale (sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  have hcnt := hcount (ι:=ℂ) 1 hδ hY hHeight Z m (fun _ n => χ (n:ZMod 1)) id
    (support V) (support W) w ψ θ e hErr (fun n _ => (differenceWeight_bounds hU0 hUY n).1)
    hnorm hDet hRow
  have hpower := upperLog_density_scale (Q:=1) le_rfl hT0 hδ
  simp only [Nat.cast_one,one_pow,one_mul] at hpower
  exact hcnt.trans (mul_le_mul_of_nonneg_left hpower hC.le)

end GoldbachPrincipalPintz

end

section

namespace GoldbachPrincipalPintz

open Finset Filter Complex Goldbach GoldbachDensityDetector GoldbachPintzScales GoldbachExceptionalTail
open GoldbachSpectralGeometry GoldbachWeightedMajorResidual GoldbachLowZeroGapEnergy GoldbachTwistedMellin
open GoldbachWeightedException (cutoff)
open scoped Classical Topology

noncomputable section

theorem principal_first_power_eventually {K : ℝ} (hK : 0 < K) :
    ∃ D H₀ : ℝ, 0 < D ∧ ∀ᶠ X : ℝ in atTop, ∀ {T L : ℝ}, 1 ≤ T → 0 ≤ L → H₀ ≤ T+1 →
      T+1 ≤ X → (T+1)^4 ≤ (2:ℝ)^32*X^(123/125:ℝ) →
      ∀ Z : Finset ℂ, (∀ ρ ∈ Z, 1-loss ≤ ρ.re ∧ |ρ.im| ≤ T ∧
        regularizedL (1 : DirichletCharacter ℂ 1) ρ = 0 ∧
        1-ρ.re < K*Real.log (Real.log X)/Real.log X) →
      (∑ ρ ∈ Z.filter (fun ρ => L ≤ (1-ρ.re)*Real.log X),
        (analyticOrderNatAt (regularizedL (1 : DirichletCharacter ℂ 1)) ρ : ℝ)*
          X^(ρ.re-1)) ≤ D*Real.exp (-((77/12500:ℝ)*L)) := by
  obtain ⟨C,H₀,hC,hevent⟩ := principal_logfree_density_near hK
  let a : ℝ := 12423/12500
  let C' := C*(2:ℝ)^32
  have ha : a < 1 := by norm_num [a]
  have hC' : 0 < C' := by dsimp only [C']; positivity
  let D := C'*Real.exp a/(1-Real.exp (a-1))
  have hden : 0 < 1-Real.exp (a-1) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (sub_neg.mpr ha))
  refine ⟨D,H₀,div_pos (mul_pos hC' (Real.exp_pos _)) hden,?_⟩
  filter_upwards [hevent,eventually_gt_atTop (1:ℝ)] with X hcount hX T L hT hL hH hTX hbase Z hZ
  let c (ρ : ℂ) : ℝ := analyticOrderNatAt (regularizedL (1 : DirichletCharacter ℂ 1)) ρ
  let u (ρ : ℂ) : ℝ := (1-ρ.re)*Real.log X
  have hX₀ := zero_lt_one.trans hX
  have hlogX := Real.log_pos hX
  have hBase₀ : 0 ≤ (T+1)^4 := by positivity
  have hsp (b : ℝ) (hb : L ≤ b) : (∑ ρ ∈ Z.filter (fun ρ => u ρ ≤ b),c ρ) ≤ C'*Real.exp (a*b) := by
    let d : ℝ := min loss (b/Real.log X)
    have hLoss : 0 < loss := by unfold loss; norm_num
    have hd₀ : 0 ≤ d := le_min hLoss.le (div_nonneg (hL.trans hb) hlogX.le)
    have hd₁ : d ≤ loss := min_le_left _ _
    have hdB : d*Real.log X ≤ b := (le_div_iff₀ hlogX).mp (min_le_right _ _)
    have hsub (ρ : ℂ) (hρ : ρ ∈ Z.filter (fun ρ => u ρ ≤ b)) :
        1-d≤ρ.re ∧ |ρ.im|≤T ∧ regularizedL (1:DirichletCharacter ℂ 1) ρ=0 ∧
          1-ρ.re < K*Real.log (Real.log X)/Real.log X := by
      obtain ⟨hρZ,hρb⟩ := mem_filter.mp hρ
      obtain ⟨hβ,hT,hz,hnear⟩ := hZ ρ hρZ
      have hβ' : 1-ρ.re ≤ b/Real.log X := (le_div_iff₀ hlogX).mpr hρb
      have hh : 1-ρ.re ≤ d := le_min (by linarith only [hβ]) hβ'
      exact ⟨by linarith only [hh],hT,hz,hnear⟩
    let e : ℝ := (1+1/100:ℝ)*d
    have he₀ : 0 ≤ e := by dsimp only [e]; positivity
    have he₁ : e ≤ 1 := by dsimp only [e]; unfold loss at hd₁; linarith only [hd₁]
    have hnum : 1 ≤ (2:ℝ)^32 := by norm_num
    have hpowK : ((2:ℝ)^32)^e ≤ (2:ℝ)^32 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hnum he₁
    have hpowX : (X^(123/125:ℝ))^e ≤ Real.exp (a*b) := by
      rw [← Real.rpow_mul hX₀.le,Real.rpow_def_of_pos hX₀]
      apply Real.exp_le_exp.mpr
      dsimp only [e,a]
      nlinarith only [hdB]
    calc
      _ ≤ C*((T+1)^4)^e := hcount hd₀ hd₁ hT hH hTX _ hsub
      _ ≤ C*((2:ℝ)^32*X^(123/125:ℝ))^e :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hBase₀ hbase he₀) hC.le
      _ ≤ C*((2:ℝ)^32*Real.exp (a*b)) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hpowK hpowX (by positivity) (by positivity)) hC.le
      _ = _ := by unfold C'; ring
  have ht := laplace_tail_of_measured_count Z u c ha hC'.le (fun _ _ => Nat.cast_nonneg _) hsp
  have hs (ρ : ℂ) : Real.exp (-u ρ) = X^(ρ.re-1) := by
    rw [Real.rpow_def_of_pos hX₀]
    unfold u
    congr 1
    ring
  simp only [hs] at ht
  refine ht.trans_eq ?_
  unfold D
  rw [Real.exp_add]
  have hE : (a-1)*L = -((77/12500:ℝ)*L) := by norm_num [a]
  rw [hE]
  ring

end
end GoldbachPrincipalPintz

end

section

namespace GoldbachPrincipalPintz

open Finset Filter Complex Goldbach GoldbachPintzScales GoldbachSpectralGeometry
open GoldbachWeightedMajorResidual GoldbachLowZeroGapEnergy GoldbachTwistedMellin
open GoldbachWeightedException (cutoff)
open scoped Topology Classical

noncomputable section

def shortZetaZeros (X : ℕ) : Finset ℂ :=
  (exceptionalZeros (1 : DirichletCharacter ℂ 1) (heightCut (X:ℝ))).filter (shortNearZero X 1)

theorem farGap_eventually_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, farGap X ≤ ε := by
  have hsmall := Real.isLittleO_log_id_atTop.bound (show 0 < ε/3000 by positivity)
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually hsmall] with X hL hsmallX
  have hL₀ : 0 < Real.log X := by linarith
  have hlog : Real.log (Real.log X) ≤ (ε/3000)*Real.log X := by
    simpa only [Real.norm_eq_abs, id_eq, abs_of_nonneg hL₀.le,
      abs_of_nonneg (Real.log_nonneg hL)] using hsmallX
  apply (div_le_iff₀ hL₀).mpr
  linarith only [hlog]

theorem short_zeta_mass :
    ∃ D : ℝ, 0 < D ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀,
      (∑ ρ ∈ shortZetaZeros X,
        (analyticOrderNatAt (regularizedL (1 : DirichletCharacter ℂ 1)) ρ : ℝ)*(X:ℝ)^(ρ.re-1)) ≤ D ∧
      ∀ L : ℝ, 0 ≤ L →
        (∑ ρ ∈ (shortZetaZeros X).filter (fun ρ => L ≤ (1-ρ.re)*Real.log (X:ℝ)),
          (analyticOrderNatAt (regularizedL (1 : DirichletCharacter ℂ 1)) ρ : ℝ)*(X:ℝ)^(ρ.re-1)) ≤
          D*Real.exp (-((77/12500:ℝ)*L)) := by
  obtain ⟨D,H₀,hD,htail⟩ := principal_first_power_eventually (K:=3000) (by norm_num)
  have hLoss : 0 < loss := by unfold loss; norm_num
  have ht : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hH₀ : ∀ᶠ x : ℝ in atTop, H₀ ≤ x^(1/25:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/25)).eventually_ge_atTop H₀
  obtain ⟨X₀,hXX⟩ := eventually_atTop.mp <| ((ht.eventually htail).and
    ((ht.eventually (farGap_eventually_le hLoss)).and ((ht.eventually hH₀).and
      (eventually_ge_atTop (2^200:ℕ)))))
  refine ⟨D,hD,X₀,?_⟩
  intro X hX
  obtain ⟨hTail,hGap,hH,hX200⟩ := hXX X hX
  let x : ℝ := X
  let P := cutoff X
  let T := shortBinHeight x P 1
  have hx200 : (2:ℝ)^200 ≤ x := by dsimp only [x]; exact_mod_cast hX200
  have hx : 1 ≤ x := (by norm_num : (1:ℝ)≤2^200).trans hx200
  obtain ⟨hP,hPb,_⟩ := GoldbachWeightedMajorResidual.cutoff_scale hX200
  have hP1 : (1:ℝ)≤P := by exact_mod_cast hP
  have hP0 := zero_le_one.trans hP1
  obtain ⟨_,hShortLow,hShortOne,_,_⟩ := short_height_geometry (r:=1) hx200 le_rfl hP1 hPb
  have hShort : shortHeight x P 1 ≤ T :=
    short_height_le_bin hx hP0 zero_lt_one zero_lt_one
      (by simpa only [one_mul] using Real.one_le_rpow hx (by norm_num : (0:ℝ) ≤ 1/1000))
  have hT : 1 ≤ T := hShortOne.trans hShort
  have hTXH : H₀ ≤ T+1 := (hH.trans (hShortLow.trans hShort)).trans (le_add_of_nonneg_right zero_le_one)
  have hBase : (T+1)^4 ≤ (2:ℝ)^32*x^(123/125:ℝ) := by
    simpa only [Nat.floor_one,Nat.cast_one,one_pow,one_mul] using short_bin_q3_t4_scale hx
      (R:=1) le_rfl hPb hT
  have hTX : T+1 ≤ x := by
    have hscale : (2:ℝ)^32 ≤ x := (by norm_num : (2:ℝ)^32 ≤ 2^200).trans hx200
    have hXE : x^(123/125:ℝ) ≤ x := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (123/125:ℝ)≤1)
    have hs : (T+1)^4 ≤ x^4 := calc
      _ ≤ _ := hBase
      _ ≤ x*x := mul_le_mul hscale hXE (by positivity) (by positivity)
      _ = x^(2:ℝ) := by rw [Real.rpow_ofNat,pow_two]
      _ ≤ _ := by rw [← Real.rpow_ofNat]; exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    by_contra! h
    exact (not_lt_of_ge hs) (pow_lt_pow_left₀ h (zero_le_one.trans hx) (by decide))
  have hZ (ρ : ℂ) (hρ : ρ ∈ shortZetaZeros X) :
      1-loss ≤ ρ.re ∧ |ρ.im| ≤ T ∧ regularizedL (1:DirichletCharacter ℂ 1) ρ=0 ∧
        1-ρ.re < 3000*Real.log (Real.log x)/Real.log x := by
    obtain ⟨hE,hNear⟩ := mem_filter.mp hρ
    obtain ⟨_,_,hZero⟩ := (mem_exceptionalZeros _ _ _).mp hE
    obtain ⟨hHeight,hRe⟩ := hNear
    exact ⟨by linarith only [hGap,hRe],hHeight.le.trans hShort,hZero,by
      change 1-farGap x < ρ.re at hRe
      unfold farGap at hRe
      linarith only [hRe]⟩
  have hT' (L : ℝ) (hL : 0 ≤ L) := hTail hT hL hTXH hTX hBase (shortZetaZeros X) hZ
  refine ⟨?_,hT'⟩
  have hAll : (shortZetaZeros X).filter (fun ρ => 0 ≤ (1-ρ.re)*Real.log (X:ℝ)) = shortZetaZeros X := by
    apply filter_eq_self.mpr
    intro ρ hρ
    have hz := (hZ ρ hρ).2.2.1
    have hRe : ρ.re ≤ 1 := le_of_lt (lt_of_not_ge (fun h => GoldbachZeroFree.regularizedL_ne_zero_ge_one _ h hz))
    exact mul_nonneg (sub_nonneg.mpr hRe) (Real.log_nonneg hx)
  simpa only [hAll,mul_zero,neg_zero,Real.exp_zero,mul_one] using hT' 0 le_rfl

end
end GoldbachPrincipalPintz

end

section

namespace GoldbachPintzFamily

open Finset Goldbach GoldbachTypeII GoldbachDensitySlices GoldbachPintzScales GoldbachExceptionalTail
open scoped Classical

noncomputable section

/-- Convert the log-free family count into the first-power tail used in the
signed convolution, preserving the analytic zero orders. -/
theorem nonprincipal_first_power_tail_of_density
    {C : ℝ} (hC : 0 < C)
    (hcount : ∀ (Q : ℕ), 1 ≤ Q → ∀ {δ T : ℝ}, 0 ≤ δ → δ ≤ loss → 0 ≤ T →
      ∀ Z : Finset (TaggedZero Q), Z ⊆ familyZeroTags Q (1-δ) T →
      (∑ r ∈ Z,(order r:ℝ)) ≤ C*((Q:ℝ)^3*(T+1)^4)^((1+1/100:ℝ)*δ)) :
    ∃ D : ℝ, 0 < D ∧ ∀ (Q : ℕ), 1 ≤ Q → ∀ {X T L : ℝ}, 1 < X → 0 ≤ T → 0 ≤ L →
      (Q:ℝ)^3*(T+1)^4 ≤ (2:ℝ)^32*X^(123/125:ℝ) →
      ∀ Z : Finset (TaggedZero Q), Z ⊆ familyZeroTags Q (1-loss) T →
      (∑ r ∈ Z.filter (fun r => L ≤ (1-r.2.re)*Real.log X),
        (order r:ℝ)*X^(r.2.re-1)) ≤ D*Real.exp (-((77/12500:ℝ)*L)) := by
  let a : ℝ := 12423/12500
  let C' := C*(2:ℝ)^32
  have ha : a < 1 := by norm_num [a]
  have hC' : 0 < C' := by dsimp only [C']; positivity
  let D := C'*Real.exp a/(1-Real.exp (a-1))
  have hden : 0 < 1-Real.exp (a-1) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (sub_neg.mpr ha))
  refine ⟨D,div_pos (mul_pos hC' (Real.exp_pos _)) hden,?_⟩
  intro Q hQ X T L hX hT hL hbase Z hZ
  let c (r : TaggedZero Q) : ℝ := order r
  let u (r : TaggedZero Q) : ℝ := (1-r.2.re)*Real.log X
  have hX₀ := zero_lt_one.trans hX
  have hlogX := Real.log_pos hX
  have hBase₀ : 0 ≤ (Q:ℝ)^3*(T+1)^4 := by positivity
  have hsp (b : ℝ) (hb : L ≤ b) : (∑ r ∈ Z.filter (fun r => u r ≤ b),c r) ≤ C'*Real.exp (a*b) := by
    let d : ℝ := min loss (b/Real.log X)
    have hLoss : 0 < loss := by unfold loss; norm_num
    have hd₀ : 0 ≤ d := le_min hLoss.le (div_nonneg (hL.trans hb) hlogX.le)
    have hd₁ : d ≤ loss := min_le_left _ _
    have hdB : d*Real.log X ≤ b := (le_div_iff₀ hlogX).mp (min_le_right _ _)
    have hsub : Z.filter (fun r => u r ≤ b) ⊆ familyZeroTags Q (1-d) T := by
      intro r hr
      obtain ⟨hrZ,hrB⟩ := mem_filter.mp hr
      obtain ⟨hc,hz⟩ := mem_sigma.mp (hZ hrZ)
      obtain ⟨hrL,hrH,hrT,hr0⟩ := mem_densityZeros.mp hz
      have hβ : 1-d ≤ r.2.re := by
        have hβ' : 1-r.2.re ≤ b/Real.log X := (le_div_iff₀ hlogX).mpr hrB
        have hh : 1-r.2.re ≤ d := le_min (by linarith only [hrL]) hβ'
        linarith only [hh]
      exact mem_sigma.mpr ⟨hc,mem_densityZeros.mpr ⟨hβ,hrH,hrT,hr0⟩⟩
    let e : ℝ := (1+1/100:ℝ)*d
    have he₀ : 0 ≤ e := by dsimp only [e]; positivity
    have he₁ : e ≤ 1 := by dsimp only [e]; unfold loss at hd₁; linarith only [hd₁]
    have hnum : 1 ≤ (2:ℝ)^32 := by norm_num
    have hpowK : ((2:ℝ)^32)^e ≤ (2:ℝ)^32 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hnum he₁
    have hpowX : (X^(123/125:ℝ))^e ≤ Real.exp (a*b) := by
      rw [← Real.rpow_mul hX₀.le,Real.rpow_def_of_pos hX₀]
      apply Real.exp_le_exp.mpr
      dsimp only [e,a]
      nlinarith only [hdB]
    calc
      _ ≤ C*((Q:ℝ)^3*(T+1)^4)^e :=
        hcount Q hQ hd₀ hd₁ hT _ hsub
      _ ≤ C*((2:ℝ)^32*X^(123/125:ℝ))^e :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hBase₀ hbase he₀) hC.le
      _ ≤ C*((2:ℝ)^32*Real.exp (a*b)) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hpowK hpowX (by positivity) (by positivity)) hC.le
      _ = _ := by unfold C'; ring
  have ht := laplace_tail_of_measured_count Z u c ha hC'.le (fun _ _ => Nat.cast_nonneg _) hsp
  have hs (r : TaggedZero Q) : Real.exp (-u r) = X^(r.2.re-1) := by
    rw [Real.rpow_def_of_pos hX₀]
    unfold u
    congr 1
    ring
  simp only [hs] at ht
  refine ht.trans_eq ?_
  unfold D
  rw [Real.exp_add]
  have hE : (a-1)*L = -((77/12500:ℝ)*L) := by norm_num [a]
  rw [hE]
  ring

end
end GoldbachPintzFamily

end

section

namespace GoldbachPintzFamily

open Finset Filter Goldbach GoldbachTypeII GoldbachDensitySlices GoldbachTwistedMellin
open GoldbachWeightedMajorResidual GoldbachSpectralGeometry GoldbachLowZeroGapEnergy
open GoldbachWeightedException (cutoff)
open GoldbachPowerBins GoldbachPintzScales
open scoped Topology Classical

noncomputable section

/-- The actual short-height near-one zeros of primitive nonprincipal characters. -/
def shortNearNonprincipalTags (X : ℕ) : Finset (TaggedZero (cutoff X)) :=
  (primitiveNonprincipalFamily (cutoff X)).sigma
    (fun c => (exceptionalZeros c.2 (heightCut (X : ℝ))).filter
      (shortNearZero X c.2.conductor))

private theorem near_level_range {X : ℕ} (r : TaggedZero (cutoff X)) :
    1 ≤ level r ∧ level r ≤ cutoff X :=
  ⟨Nat.succ_le_succ (Nat.zero_le _), level_le r⟩

private theorem near_X_one_lt {X : ℕ} (hX : 2^200 ≤ X) : 1 < (X : ℝ) := by
  have h : 1 < (2 : ℕ)^200 := one_lt_pow' (by decide) (by decide)
  exact_mod_cast h.trans_le hX

/-- The fixed power-bin bound eventually absorbs the constant in the cutoff. -/
theorem near_cutoff_slack_eventually : ∀ᶠ X : ℕ in atTop, (4 : ℝ) ≤ (X : ℝ)^(1/2000 : ℝ) := by
  have h := (tendsto_rpow_atTop (show (0 : ℝ) < 1/2000 by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  exact h.eventually_ge_atTop 4

private theorem near_bin_index_lt {X : ℕ} (hX : 2^200 ≤ X)
    (hp : (4 : ℝ) ≤ (X : ℝ)^(1/2000 : ℝ)) {r : ℕ}
    (hr : 1 ≤ r) (hrP : r ≤ cutoff X) :
    binIndex (X : ℝ) (r : ℝ) < 206 := by
  let x : ℝ := X
  have hx1 : 1 < x := near_X_one_lt hX
  have hx0 := zero_lt_one.trans hx1
  have hlog := Real.log_pos hx1
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 := zero_lt_one.trans_le hr1
  have hrp : (r : ℝ) ≤ x^(411/2000 : ℝ) := by
    calc
      _ ≤ (cutoff X : ℝ) := by exact_mod_cast hrP
      _ ≤ 4*x^(41/200 : ℝ) := (cutoff_scale hX).2.1
      _ ≤ x^(1/2000 : ℝ)*x^(41/200 : ℝ) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by rw [← Real.rpow_add hx0]; norm_num
  have hR := Real.log_le_log hr0 hrp
  rw [Real.log_rpow hx0] at hR
  have hR' : Real.log (r : ℝ)/Real.log x ≤ 411/2000 := (div_le_iff₀ hlog).mpr hR
  have hFloor : ((binIndex x (r : ℝ) : ℕ) : ℝ) ≤
      1000*(Real.log (r : ℝ)/Real.log x) := Nat.floor_le
        (mul_nonneg (by norm_num) (div_nonneg (Real.log_nonneg hr1) hlog.le))
  exact_mod_cast (show ((binIndex x (r : ℝ) : ℕ) : ℝ) < 206 by linarith)

private theorem near_bin_scale {X : ℕ} (hX : 2^200 ≤ X) {r : ℕ}
    (hr : 1 ≤ r) (hrP : r ≤ cutoff X) :
    let R := binUpper (X : ℝ) (binIndex (X : ℝ) (r : ℝ))
    let Q := ⌊R⌋₊
    let T := shortBinHeight (X : ℝ) (cutoff X : ℝ) R
    1 ≤ Q ∧ 1 ≤ T ∧ (Q : ℝ)^3*(T+1)^4 ≤ (2 : ℝ)^32*(X : ℝ)^(123/125 : ℝ) := by
  let x : ℝ := X
  let P : ℝ := cutoff X
  let R := binUpper x (binIndex x (r : ℝ))
  let Q := ⌊R⌋₊
  let T := shortBinHeight x P R
  have hx1 : 1 < x := near_X_one_lt hX
  have hx0 := zero_lt_one.trans hx1
  obtain ⟨_,hP,hPX⟩ := cutoff_scale hX
  have hPX' : P ≤ x := by dsimp only [P,x]; exact_mod_cast hPX
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrP' : (r : ℝ) ≤ P := by dsimp only [P]; exact_mod_cast hrP
  have hP0 : 0 ≤ P := Nat.cast_nonneg _
  have hR : (r : ℝ) ≤ R := (bin_geometry hx1 hr1 (hrP'.trans hPX')).2.1
  have hR1 : 1 ≤ R := hr1.trans hR
  have hR0 := zero_lt_one.trans_le hR1
  have hRT : R ≤ P*x^(1/1000 : ℝ) := bin_upper_le hx1 hr1 hrP' hPX'
  have hT : 1 ≤ T := by
    change 1 ≤ 32*x^(41/1000 : ℝ)*P/R
    apply (le_div_iff₀ hR0).mpr
    rw [one_mul]
    refine hRT.trans ?_
    have hPow := Real.rpow_le_rpow_of_exponent_le hx1.le
      (show (1/1000 : ℝ) ≤ 41/1000 by norm_num)
    have hm := mul_le_mul_of_nonneg_left hPow hP0
    nlinarith only [hm, mul_nonneg hP0 (Real.rpow_nonneg hx0.le (41/1000 : ℝ))]
  exact ⟨(Nat.one_le_floor_iff R).mpr hR1,hT,short_bin_q3_t4_scale hx1.le hR1 hP hT⟩

private def retag {P Q : ℕ} (r : TaggedZero P) (h : level r ≤ Q) : TaggedZero Q :=
  ⟨⟨⟨r.1.1.val, Nat.lt_of_succ_le h⟩,r.1.2⟩,r.2⟩

private theorem retag_column {P Q : ℕ} (r : TaggedZero P) (h : level r ≤ Q) :
    column (retag r h) = column r := rfl

private theorem retag_injective {P Q : ℕ} {r s : TaggedZero P}
    (hr : level r ≤ Q) (hs : level s ≤ Q) (h : retag r hr = retag s hs) : r = s := by
  apply Sigma.ext
  · exact (column_eq_iff r s).mp
      (by simpa only [retag_column] using congrArg (column (Q:=Q)) h)
  · exact heq_of_eq (congrArg (fun t : TaggedZero Q => t.2) h)

private theorem level_le_near_bin_floor {X : ℕ} (hX : 1 < (X : ℝ))
    (hP : cutoff X ≤ X) (r : TaggedZero (cutoff X)) :
    level r ≤ ⌊binUpper (X : ℝ) (binIndex (X : ℝ) (level r : ℝ))⌋₊ := by
  obtain ⟨h₁,h₂⟩ := near_level_range r
  have h₁' : (1 : ℝ) ≤ level r := by exact_mod_cast h₁
  have h₂' : (level r : ℝ) ≤ X := by exact_mod_cast h₂.trans hP
  exact level_le_bin_floor h₁ (bin_geometry hX h₁' h₂').2.1

private theorem retag_short_near_mem {X Q : ℕ} (hX : 1 < (X : ℝ))
    (hP : cutoff X ≤ X) (hGap : farGap (X : ℝ) ≤ loss)
    (r : TaggedZero (cutoff X)) (hr : r ∈ shortNearNonprincipalTags X)
    (hQ : level r ≤ Q) {T : ℝ}
    (hT : shortBinHeight (X : ℝ) (cutoff X : ℝ)
      (binUpper (X : ℝ) (binIndex (X : ℝ) (level r : ℝ))) ≤ T) :
    retag r hQ ∈ familyZeroTags Q (1-loss) T := by
  obtain ⟨hc,hz⟩ := mem_sigma.mp hr
  obtain ⟨hz,hs⟩ := mem_filter.mp hz
  obtain ⟨hp,hn⟩ := mem_primitiveNonprincipalFamily.mp hc
  obtain ⟨_,_,hzero⟩ := (mem_exceptionalZeros r.1.2 (heightCut (X : ℝ)) r.2).mp hz
  have hcond : r.1.2.conductor = level r := hp
  have hshort : |r.2.im| < shortHeight (X : ℝ) (cutoff X : ℝ) (level r : ℝ) ∧
      1-farGap (X : ℝ) < r.2.re := by
    simpa only [shortNearZero,hcond] using hs
  obtain ⟨hr1,hrP⟩ := near_level_range r
  have hr1' : (1 : ℝ) ≤ level r := by exact_mod_cast hr1
  have hrP' : (level r : ℝ) ≤ cutoff X := by exact_mod_cast hrP
  have hrX : (level r : ℝ) ≤ X := by exact_mod_cast hrP.trans hP
  have hrp := zero_lt_one.trans_le hr1'
  have hxp := zero_lt_one.trans hX
  have hRL : binUpper (X : ℝ) (binIndex (X : ℝ) (level r : ℝ)) ≤
      (level r : ℝ)*(X : ℝ)^(1/1000 : ℝ) :=
    (div_le_iff₀ (Real.rpow_pos_of_pos hxp _)).mp (bin_geometry hX hr1' hrX).1
  have hh := short_height_le_bin hX.le (Nat.cast_nonneg (cutoff X)) hrp
    (binUpper_pos hxp _) hRL
  have hβ : 1-loss ≤ r.2.re := by linarith only [hshort.2,hGap]
  have hβ₁ : r.2.re ≤ 1 := by
    by_contra! h
    exact regularizedL_ne_zero_right r.1.2 h hzero
  refine mem_sigma.mpr ⟨mem_primitiveNonprincipalFamily.mpr ⟨hp,hn⟩,?_⟩
  exact mem_densityZeros.mpr ⟨hβ,hβ₁,(hshort.1.le.trans hh).trans hT,hzero⟩

private def retagEmbedding {P Q : ℕ} (B : Finset (TaggedZero P))
    (hQ : ∀ r ∈ B, level r ≤ Q) : {r : TaggedZero P // r ∈ B} ↪ TaggedZero Q :=
  ⟨fun r => retag r.1 (hQ r.1 r.2), fun r s h =>
    Subtype.ext (retag_injective (hQ r.1 r.2) (hQ s.1 s.2) h)⟩

private theorem sum_retag {P Q : ℕ} (B : Finset (TaggedZero P))
    (hQ : ∀ r ∈ B, level r ≤ Q) (x : ℝ) :
    (∑ r ∈ B.attach.map (retagEmbedding B hQ), (order r : ℝ)*x^(r.2.re-1)) =
    ∑ r ∈ B, (order r : ℝ)*x^(r.2.re-1) := by
  rw [Finset.sum_map]
  exact Finset.sum_attach B (fun r : TaggedZero P => (order r : ℝ)*x^(r.2.re-1))

private theorem retag_bin_subset {X Q : ℕ} {T L : ℝ}
    (hX : 1 < (X : ℝ)) (hP : cutoff X ≤ X) (hGap : farGap (X : ℝ) ≤ loss)
    (B : Finset (TaggedZero (cutoff X))) (hQ : ∀ r ∈ B, level r ≤ Q)
    (hB : ∀ r ∈ B, r ∈ shortNearNonprincipalTags X ∧
      shortBinHeight (X : ℝ) (cutoff X : ℝ)
        (binUpper (X : ℝ) (binIndex (X : ℝ) (level r : ℝ))) ≤ T ∧
      L ≤ (1-r.2.re)*Real.log (X : ℝ)) :
    let Z := B.attach.map (retagEmbedding B hQ)
    Z ⊆ familyZeroTags Q (1-loss) T ∧
      Z.filter (fun r => L ≤ (1-r.2.re)*Real.log (X : ℝ)) = Z := by
  dsimp only
  constructor
  · intro r hr
    obtain ⟨a,_,rfl⟩ := mem_map.mp hr
    obtain ⟨ha,hT,_⟩ := hB a.1 a.2
    exact retag_short_near_mem hX hP hGap a.1 ha (hQ a.1 a.2) hT
  · refine filter_eq_self.mpr ?_
    intro r hr
    obtain ⟨a,_,rfl⟩ := mem_map.mp hr
    exact (hB a.1 a.2).2.2

set_option maxHeartbeats 400000 in
private theorem short_near_bin_tail {D : ℝ} (hD : 0 < D)
    (hTail : ∀ (Q : ℕ), 1 ≤ Q → ∀ {X T L : ℝ}, 1 < X → 0 ≤ T → 0 ≤ L →
      (Q : ℝ)^3*(T+1)^4 ≤ (2 : ℝ)^32*X^(123/125 : ℝ) →
      ∀ Z : Finset (TaggedZero Q), Z ⊆ familyZeroTags Q (1-loss) T →
      (∑ r ∈ Z.filter (fun r => L ≤ (1-r.2.re)*Real.log X),
        (order r : ℝ)*X^(r.2.re-1)) ≤ D*Real.exp (-((77/12500 : ℝ)*L)))
    {X : ℕ} (hX : 2^200 ≤ X) (hGap : farGap (X : ℝ) ≤ loss)
    {L : ℝ} (hL : 0 ≤ L) (j : ℕ)
    (B : Finset (TaggedZero (cutoff X)))
    (hB : ∀ r ∈ B, r ∈ shortNearNonprincipalTags X ∧
      binIndex (X : ℝ) (level r : ℝ) = j ∧ L ≤ (1-r.2.re)*Real.log (X : ℝ)) :
    (∑ r ∈ B, (order r : ℝ)*(X : ℝ)^(r.2.re-1)) ≤ D*Real.exp (-((77/12500 : ℝ)*L)) := by
  classical
  obtain hEmpty | ⟨a,ha⟩ := B.eq_empty_or_nonempty
  · rw [hEmpty,sum_empty]
    positivity
  let x : ℝ := X
  let P := cutoff X
  let R := binUpper x j
  let Q := ⌊R⌋₊
  let T := shortBinHeight x (P : ℝ) R
  let k (r : TaggedZero P) := binIndex x (level r : ℝ)
  have ha' : k a = j := (hB a ha).2.1
  have hX₁ : 1 < x := near_X_one_lt hX
  have hP := (cutoff_scale hX).2.2
  have hsc : 1 ≤ Q ∧ 1 ≤ T ∧
      (Q : ℝ)^3*(T+1)^4 ≤ (2 : ℝ)^32*x^(123/125 : ℝ) := by
    simpa only [R,Q,T,P,x,← ha'] using near_bin_scale hX (near_level_range a).1 (near_level_range a).2
  have hQ (r : TaggedZero P) (hr : r ∈ B) : level r ≤ Q := by
    have hj : k r = j := (hB r hr).2.1
    simpa only [Q,R,← hj] using level_le_near_bin_floor hX₁ hP r
  have hb (r : TaggedZero P) (hr : r ∈ B) : r ∈ shortNearNonprincipalTags X ∧
      shortBinHeight x (P : ℝ) (binUpper x (k r)) ≤ T ∧ L ≤ (1-r.2.re)*Real.log x := by
    obtain ⟨hrS,hrj,hrL⟩ := hB r hr
    exact ⟨hrS, by rw [show k r = j from hrj], hrL⟩
  let Z := B.attach.map (retagEmbedding B hQ)
  obtain ⟨hZ,hZL⟩ := retag_bin_subset hX₁ hP hGap B hQ hb
  have hh := hTail Q hsc.1 hX₁ (zero_le_one.trans hsc.2.1) hL hsc.2.2 Z hZ
  rw [hZL, sum_retag B hQ] at hh
  exact hh

set_option maxHeartbeats 400000 in
/-- The fixed conductor bins preserve the actual analytic orders, giving
an exponentially small first-power tail uniformly in the near strip. -/
theorem short_near_nonprincipal_tail_of_density
    {C : ℝ} (hC : 0 < C)
    (hcount : ∀ (Q : ℕ), 1 ≤ Q → ∀ {δ T : ℝ}, 0 ≤ δ → δ ≤ loss → 0 ≤ T →
      ∀ Z : Finset (TaggedZero Q), Z ⊆ familyZeroTags Q (1-δ) T →
      (∑ r ∈ Z,(order r : ℝ)) ≤ C*((Q : ℝ)^3*(T+1)^4)^((1+1/100 : ℝ)*δ)) :
    ∃ A : ℝ, 0 < A ∧ ∀ (X : ℕ), 2^200 ≤ X → (4 : ℝ) ≤ (X : ℝ)^(1/2000 : ℝ) →
      farGap (X : ℝ) ≤ loss →
      ∀ L : ℝ, 0 ≤ L →
      (∑ r ∈ (shortNearNonprincipalTags X).filter (fun r => L ≤ (1-r.2.re)*Real.log (X : ℝ)),
        (order r : ℝ)*(X : ℝ)^(r.2.re-1)) ≤ A*Real.exp (-((77/12500 : ℝ)*L)) := by
  classical
  obtain ⟨D,hD,hTail⟩ := nonprincipal_first_power_tail_of_density hC hcount
  refine ⟨206*D,by positivity,?_⟩
  intro X hX hp hGap L hL
  let P := cutoff X
  let S := shortNearNonprincipalTags X
  let k (r : TaggedZero P) := binIndex (X : ℝ) (level r : ℝ)
  let F (r : TaggedZero P) := (order r : ℝ)*(X : ℝ)^(r.2.re-1)
  let W := S.filter (fun r => L ≤ (1-r.2.re)*Real.log (X : ℝ))
  have hpart : (∑ j ∈ range 206, ∑ r ∈ W.filter (fun r => k r = j), F r) =
      ∑ r ∈ W, F r := by
    apply sum_fiberwise_of_maps_to
    intro r _
    exact mem_range.mpr (near_bin_index_lt hX hp (near_level_range r).1 (near_level_range r).2)
  have hbin (j : ℕ) :
      (∑ r ∈ W.filter (fun r => k r = j), F r) ≤ D*Real.exp (-((77/12500 : ℝ)*L)) := by
    apply short_near_bin_tail hD hTail hX hGap hL j
    intro r hr
    obtain ⟨hrW,hrk⟩ := mem_filter.mp hr
    obtain ⟨hrS,hrL⟩ := mem_filter.mp hrW
    exact ⟨hrS,hrk,hrL⟩
  change (∑ r ∈ W, F r) ≤ _
  rw [← hpart]
  calc
    _ ≤ ∑ _j ∈ range 206, D*Real.exp (-((77/12500 : ℝ)*L)) := sum_le_sum (fun j _ => hbin j)
    _ = _ := by simp [nsmul_eq_mul,mul_assoc]

/-- The splitting gap eventually lies in the uniform log-free strip. -/
theorem farGap_eventually_le_pintz_loss : ∀ᶠ X : ℕ in atTop, farGap (X : ℝ) ≤ loss := by
  have hLoss : 0 < loss := by unfold loss; norm_num
  have hsmall := Real.isLittleO_log_id_atTop.bound (div_pos hLoss (by norm_num : (0 : ℝ) < 3000))
  have hreal : ∀ᶠ x : ℝ in atTop, farGap x ≤ loss := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
      Real.tendsto_log_atTop.eventually hsmall] with x hx hsmallx
    have hx0 : 0 < Real.log x := zero_lt_one.trans_le hx
    have hb : Real.log (Real.log x) ≤ (loss/3000)*Real.log x := by
      simpa only [Real.norm_eq_abs, id_eq, abs_of_nonneg hx0.le,
        abs_of_nonneg (Real.log_nonneg hx)] using hsmallx
    unfold farGap
    exact (div_le_iff₀ hx0).mpr (by linarith only [hb])
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hreal

end
end GoldbachPintzFamily

end


section

namespace GoldbachPintzFamily

open Finset Filter Goldbach GoldbachTypeII GoldbachTwistedMellin
open GoldbachWeightedMajorResidual GoldbachSpectralGeometry
open GoldbachWeightedException (cutoff)
open scoped Classical

noncomputable section

/-- A single uniform mass constant also controls all weighted tails of the
short-height near-one zeros of primitive nonprincipal characters. -/
theorem short_near_nonprincipal_mass_and_tail :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ X : ℕ in atTop,
      (∑ r ∈ shortNearNonprincipalTags X, (order r : ℝ)*(X : ℝ)^(r.2.re-1)) ≤ A ∧
      ∀ L : ℝ, 0 ≤ L →
        (∑ r ∈ (shortNearNonprincipalTags X).filter
          (fun r => L ≤ (1-r.2.re)*Real.log (X : ℝ)),
          (order r : ℝ)*(X : ℝ)^(r.2.re-1)) ≤ A*Real.exp (-((77/12500 : ℝ)*L)) := by
  obtain ⟨C,hC,hcount⟩ := nonprincipal_logfree_density
  obtain ⟨A,hA,hTail⟩ := short_near_nonprincipal_tail_of_density hC hcount
  refine ⟨A,hA,?_⟩
  filter_upwards [eventually_ge_atTop (2^200 : ℕ),near_cutoff_slack_eventually,
    farGap_eventually_le_pintz_loss] with X hX hp hGap
  refine ⟨?_,hTail X hX hp hGap⟩
  have hX₁ : 1 ≤ (X : ℝ) := by
    have h : 1 < (2 : ℕ)^200 := one_lt_pow' (by decide) (by decide)
    exact_mod_cast h.le.trans hX
  have hg : ∀ r ∈ shortNearNonprincipalTags X, 0 ≤ (1-r.2.re)*Real.log (X : ℝ) := by
    intro r hr
    obtain ⟨_,hz⟩ := mem_sigma.mp hr
    obtain ⟨hz,_⟩ := mem_filter.mp hz
    have hzero := ((mem_exceptionalZeros r.1.2 (heightCut (X : ℝ)) r.2).mp hz).2.2
    have hβ : r.2.re ≤ 1 := by
      by_contra! hh
      exact regularizedL_ne_zero_right r.1.2 hh hzero
    exact mul_nonneg (sub_nonneg.mpr hβ) (Real.log_nonneg hX₁)
  have h := hTail X hX hp hGap 0 le_rfl
  rwa [Finset.filter_eq_self.mpr hg,mul_zero,neg_zero,Real.exp_zero,mul_one] at h

end
end GoldbachPintzFamily

end

section

namespace GoldbachSignedPairs

open Finset Filter Goldbach GoldbachTypeII GoldbachDensitySlices GoldbachTwistedMellin DirichletCharacter
open GoldbachPrincipalPintz GoldbachPintzFamily GoldbachWeightedMajorResidual
open GoldbachWeightedException (cutoff)
open scoped Classical

noncomputable section

def zetaMode (ρ : ℂ) : GlobalMode := some ⟨1,(1:DirichletCharacter ℂ 1),ρ⟩

def taggedMode {Q : ℕ} (r : TaggedZero Q) : GlobalMode := some ⟨level r,r.1.2,r.2⟩

private theorem zetaMode_injective : Function.Injective zetaMode := by
  intro ρ σ h
  have hh := congrArg (fun a : GlobalMode => a.map (fun v => v.2.2)) h
  change some ρ = some σ at hh
  exact Option.some.inj hh

private theorem taggedMode_injective {Q : ℕ} : Function.Injective (taggedMode (Q:=Q)) := by
  intro r s h
  have hc : naturalColumn r.1 = naturalColumn s.1 := by
    have he := congrArg (fun a : GlobalMode => a.map (fun v => (⟨v.1,v.2.1⟩ : Σ n,DirichletCharacter ℂ n))) h
    exact Option.some.inj he
  have hf : r.1 = s.1 := (naturalColumn_injective Q) hc
  have hz : r.2 = s.2 := by
    have he := congrArg (fun a : GlobalMode => a.map (fun v => v.2.2)) h
    exact Option.some.inj he
  exact Sigma.ext hf (heq_of_eq hz)

private theorem taggedMode_mem_global {X : ℕ} {r : TaggedZero (cutoff X)}
    (hr : r ∈ shortNearNonprincipalTags X) : taggedMode r ∈ globalModesAt X := by
  obtain ⟨hc,hz⟩ := mem_sigma.mp hr
  obtain ⟨hP,hN⟩ := mem_primitiveNonprincipalFamily.mp hc
  have hq1 : 1 ≤ level r := Nat.succ_le_succ (Nat.zero_le _)
  have hq0 : level r ≠ 0 := (Nat.zero_lt_one.trans_le hq1).ne'
  refine (mem_globalModesAt_zero r.1.2 r.2).mpr ⟨hq1,level_le r,hP,?_⟩
  simpa only [globalShortZeros,dite_eq_left hq0,(isPrimitive_def _).mp hP] using hz

private theorem zetaMode_mem_global {X : ℕ} (hX : 2^200 ≤ X) {ρ : ℂ}
    (hρ : ρ ∈ shortZetaZeros X) : zetaMode ρ ∈ globalModesAt X := by
  refine (mem_globalModesAt_zero (1:DirichletCharacter ℂ 1) ρ).mpr
    ⟨le_rfl,(cutoff_scale hX).1,isPrimitive_one_level_one,?_⟩
  simpa only [globalShortZeros,dite_eq_left Nat.one_ne_zero,shortZetaZeros] using hρ

private theorem global_mode_partition {X : ℕ} (hX : 2^200 ≤ X) :
    globalModesAt X = insert none
      ((shortZetaZeros X).image zetaMode ∪ (shortNearNonprincipalTags X).image taggedMode) := by
  ext i
  constructor
  · intro hi
    rcases i with _ | ⟨r,χ,z⟩
    · exact mem_insert_self _ _
    obtain ⟨hr,hP,hp,hz⟩ := (mem_globalModesAt_zero χ z).mp hi
    let _ : NeZero r := ⟨(Nat.zero_lt_one.trans_le hr).ne'⟩
    apply mem_insert_of_mem
    by_cases hχ : χ=1
    · have hR : r=1 := ((isPrimitive_def _).mp hp).symm.trans (congrArg conductor hχ |>.trans conductor_one)
      subst r
      subst χ
      apply mem_union_left
      refine mem_image.mpr ⟨z,?_,rfl⟩
      simpa only [globalShortZeros,dite_eq_left Nat.one_ne_zero,shortZetaZeros] using hz
    · cases r with
      | zero => omega
      | succ j =>
        let k : Fin (cutoff X) := ⟨j, Nat.lt_of_succ_le hP⟩
        let t : TaggedZero (cutoff X) := ⟨⟨k,χ⟩,z⟩
        apply mem_union_right
        refine mem_image.mpr ⟨t,?_,rfl⟩
        refine mem_sigma.mpr ⟨mem_primitiveNonprincipalFamily.mpr ⟨hp,hχ⟩,?_⟩
        change z ∈ (exceptionalZeros χ (heightCut (X:ℝ))).filter (shortNearZero X χ.conductor)
        rw [(isPrimitive_def _).mp hp]
        simpa only [globalShortZeros,dite_eq_left (Nat.succ_ne_zero j)] using hz
  · intro hi
    rcases mem_insert.mp hi with h | h
    · subst i
      simp [globalModesAt]
    · rcases mem_union.mp h with h | h
      · obtain ⟨z,hz,rfl⟩ := mem_image.mp h
        exact zetaMode_mem_global hX hz
      · obtain ⟨r,hr,rfl⟩ := mem_image.mp h
        exact taggedMode_mem_global hr

private theorem global_modes_disjoint (X : ℕ) :
    Disjoint ((shortZetaZeros X).image zetaMode) ((shortNearNonprincipalTags X).image taggedMode) := by
  apply disjoint_left.mpr
  intro i hi hj
  obtain ⟨ρ,_,hr⟩ := mem_image.mp hi
  obtain ⟨r,hm,hs⟩ := mem_image.mp hj
  have he : zetaMode ρ = taggedMode r := hr.trans hs.symm
  have hEq : (1 : ℕ) = level r := by
    have hh := congrArg globalLevel he
    exact hh
  have hN := (mem_primitiveNonprincipalFamily.mp (mem_sigma.mp hm).1).2
  exact hN (DirichletCharacter.level_one' r.1.2 hEq.symm)

private theorem modeSum_partition {X : ℕ} (hX : 2^200 ≤ X) (f : GlobalMode → ℝ) :
    ∑ i ∈ globalModesAt X,f i =
      f none + (∑ ρ ∈ shortZetaZeros X, f (zetaMode ρ)) +
        (∑ r ∈ shortNearNonprincipalTags X,f (taggedMode r)) := by
  rw [global_mode_partition hX, sum_insert, sum_union (global_modes_disjoint X),
    sum_image zetaMode_injective.injOn, sum_image taggedMode_injective.injOn]
  · ring
  · simp [mem_union,mem_image,zetaMode,taggedMode]

/-- The actual global signed profile has uniformly bounded first-power mass. -/
theorem short_global_mass_and_tail :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ X : ℕ in atTop,
      (∑ i ∈ globalModesAt X,modeMass X i) ≤ A ∧
      ∀ L : ℝ, 0 ≤ L →
        (∑ i ∈ (globalModesAt X).filter (fun i => L ≤ modeGap X i),modeMass X i) ≤
          A*Real.exp (-((77/12500:ℝ)*L)) := by
  obtain ⟨D,hD,N,hD'⟩ := short_zeta_mass
  obtain ⟨E,hE,hE'⟩ := short_near_nonprincipal_mass_and_tail
  refine ⟨1+D+E,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (2^200:ℕ),eventually_ge_atTop N,hE'] with X hX hN hE
  have hp : 0 < X := (by norm_num : 0 < (2:ℕ)^200).trans_le hX
  obtain ⟨hD₁,hD₂⟩ := hD' X hN
  obtain ⟨hE₁,hE₂⟩ := hE
  have hζ (ρ : ℂ) :
      modeMass X (zetaMode ρ) =
        (analyticOrderNatAt (regularizedL (1:DirichletCharacter ℂ 1)) ρ:ℝ)*(X:ℝ)^(ρ.re-1) :=
    modeMass_eq_power hp _ _
  have hNP (r : TaggedZero (cutoff X)) :
      modeMass X (taggedMode r) = (order r:ℝ)*(X:ℝ)^(r.2.re-1) :=
    modeMass_eq_power hp _ _
  refine ⟨?_,?_⟩
  · rw [modeSum_partition hX]
    simp only [hζ,hNP]
    have hOne : modeMass X none = 1 := by simp [modeMass,modeOrder,modeGap]
    rw [hOne]
    linarith only [hD₁,hE₁]
  · intro L hL
    rw [sum_filter,modeSum_partition hX]
    have hζGap (ρ : ℂ) : modeGap X (zetaMode ρ) = (1-ρ.re)*Real.log (X:ℝ) := rfl
    have hNGap (r : TaggedZero (cutoff X)) :
        modeGap X (taggedMode r) = (1-r.2.re)*Real.log (X:ℝ) := rfl
    simp only [hζGap,hNGap,hζ,hNP,show modeGap X none = 0 by rfl]
    rw [← sum_filter,← sum_filter]
    have hP : (if L ≤ (0:ℝ) then modeMass X none else 0) ≤ Real.exp (-((77/12500:ℝ)*L)) := by
      split_ifs with h0
      · rw [le_antisymm h0 hL]
        simp [modeMass,modeOrder,modeGap]
      · exact (Real.exp_pos _).le
    have h := add_le_add (add_le_add hP (hD₂ L hL)) (hE₂ L hL)
    exact h.trans_eq (by ring)

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Complex Filter MeasureTheory Set GoldbachSmoothMellin GoldbachSmoothWindow GoldbachTwistedMellin
open scoped FourierTransform ContDiff Topology InnerProductSpace

noncomputable section

def smoothDensity (X : ℝ) (s : ℂ) (t : ℝ) : ℂ :=
  (scaledWeight X t : ℂ)*(t:ℂ)^(s-1)

theorem smoothDensity_zero_outside {X : ℝ} (hX : 0 < X) (s : ℂ) {t : ℝ}
    (ht : t ∉ Icc X (2*X)) : smoothDensity X s t = 0 := by
  have ht' : t < X ∨ 2*X < t := by
    simpa only [mem_Icc,not_and_or,not_le] using ht
  unfold smoothDensity scaledWeight
  have hw : weight (t/X) = 0 := by
    apply weight_zero
    rcases ht' with h | h
    · exact Or.inl ((div_le_iff₀ hX).mpr (by linarith))
    · exact Or.inr ((le_div_iff₀ hX).mpr (by linarith))
  rw [hw,Complex.ofReal_zero,zero_mul]

theorem smoothDensity_compact {X : ℝ} (hX : 0 < X) (s : ℂ) :
    HasCompactSupport (smoothDensity X s) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=X) (b:=2*X))
  intro t ht
  by_contra h
  exact ht (smoothDensity_zero_outside hX s h)

theorem smoothDensity_smooth {X : ℝ} (hX : 0 < X) (s : ℂ) :
    ContDiff ℝ 2 (smoothDensity X s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : 0 < t
  · have hw : ContDiff ℝ 2 (fun v => (scaledWeight X v : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (weight_smooth.comp (contDiff_id.div_const X))
    have hlog : ContDiffAt ℝ 2 (fun v : ℝ => (Real.log v : ℂ)) t :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp t (Real.contDiffAt_log.mpr ht.ne')
    have hexp : ContDiffAt ℝ 2 (fun v : ℝ => Complex.exp ((Real.log v : ℂ)*(s-1))) t :=
      Complex.contDiff_exp.contDiffAt.comp t (hlog.mul contDiffAt_const)
    refine (hw.contDiffAt.mul hexp).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with v hv
    have hv0 : 0 < v := hv
    simp only [smoothDensity,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hv0.ne'),
      ← Complex.ofReal_log hv0.le]
  · have htX : t < X := (le_of_not_gt ht).trans_lt hX
    refine (contDiffAt_const (c:= (0:ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds htX] with v hv
    exact smoothDensity_zero_outside hX s (fun h => (not_lt_of_ge h.1) hv)

private theorem integrable_fourier_of_smooth_compact {f : ℝ → ℂ}
    (hd : ContDiff ℝ 2 f) (hc : HasCompactSupport f) : Integrable (𝓕 f) := by
  have hf : Integrable f := hd.continuous.integrable_of_hasCompactSupport hc
  have hfd : ∀ k ≤ 2, Integrable (iteratedDeriv k f) := by
    intro k hk
    have hcont : Continuous (iteratedDeriv k f) := (hd.of_le (by exact_mod_cast hk : (k:ℕ∞ω) ≤ 2)).continuous_iteratedDeriv' k
    have hs : HasCompactSupport (iteratedDeriv k f) := by
      clear hcont
      induction k with
      | zero => simpa only [iteratedDeriv_zero] using hc
      | succ k ih =>
        simpa only [iteratedDeriv_succ] using (ih (Nat.le_of_succ_le hk)).deriv
    exact hcont.integrable_of_hasCompactSupport hs
  let B : ℝ := (∫ x, ‖f x‖)+(4*Real.pi^2)⁻¹*(∫ x, ‖iteratedDeriv 2 f x‖)
  have hB : Integrable (fun t : ℝ => B*(1+t^2)⁻¹) := integrable_inv_one_add_sq.const_mul B
  have hCF : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
  apply hB.mono' hCF.aestronglyMeasurable
  filter_upwards with u
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  simpa only [mul_comm (‖(𝓕 f) u‖)] using Real.one_add_sq_mul_norm_fourier_le hd hfd u

theorem integrable_fourier_smoothDensity {X : ℝ} (hX : 0 < X) (s : ℂ) :
    Integrable (𝓕 (smoothDensity X s)) :=
  integrable_fourier_of_smooth_compact (smoothDensity_smooth hX s) (smoothDensity_compact hX s)

theorem inverse_fourier_smoothDensity {X : ℝ} (hX : 0 < X) (s : ℂ) (t : ℝ) :
    (𝓕⁻ (smoothDensity X s)) t = smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) s := by
  have hXX : X ≤ 2*X := by linarith
  rw [smoothTransform,intervalIntegral.integral_of_le hXX,Real.fourierInv_eq']
  calc
    _ = ∫ v in Ioc X (2*X), Complex.exp ((2*Real.pi*⟪v,t⟫_ℝ:ℝ)*I) • smoothDensity X s v := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro v hv
      have hv' : v ≤ X ∨ 2*X < v := by simpa only [mem_Ioc,not_and_or,not_lt,not_le] using hv
      have hw : scaledWeight X v = 0 := by
        unfold scaledWeight
        apply weight_zero
        rcases hv' with hp | hp
        · exact Or.inl ((div_le_iff₀ hX).mpr (by linarith))
        · exact Or.inr ((le_div_iff₀ hX).mpr (by linarith))
      simp only [smoothDensity,hw,Complex.ofReal_zero,zero_mul,smul_zero]
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro v hv
      simp only [smul_eq_mul,smoothDensity,GoldbachTwistedMellin.density,GoldbachTwistedMellin.phase,Real.inner_apply]
      rw [mul_left_comm]
      congr 4 <;> ring

theorem smoothDensity_square_integral_le {X : ℝ} (hX : 0 < X) {s : ℂ} (hβ : s.re ≤ 1) :
    (∫ t : ℝ, ‖smoothDensity X s t‖^2) ≤ X^(2*s.re-1) := by
  have hx2 : X ≤ 2*X := by linarith
  have hFc := (smoothDensity_smooth hX s).continuous
  have hSc : HasCompactSupport (fun t => ‖smoothDensity X s t‖^2) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=X) (b:=2*X))
    intro t ht
    by_contra ht'
    exact ht (by simp [smoothDensity_zero_outside hX s ht'])
  have hfs : Integrable (fun t => ‖smoothDensity X s t‖^2) :=
    (hFc.norm.pow 2).integrable_of_hasCompactSupport hSc
  have hbound (t : ℝ) (ht : t ∈ Icc X (2*X)) :
      ‖smoothDensity X s t‖^2 ≤ (X^(s.re-1))^2 := by
    have hweight := weight_range (t/X)
    have ht0 := hX.trans_le ht.1
    have hT : t^(s.re-1) ≤ X^(s.re-1) := Real.rpow_le_rpow_of_nonpos hX ht.1 (sub_nonpos.mpr hβ)
    have hr : ‖smoothDensity X s t‖ ≤ X^(s.re-1) := by
      rw [smoothDensity,norm_mul,Complex.norm_real,scaledWeight,Real.norm_of_nonneg hweight.1,
        norm_cpow_eq_rpow_re_of_pos ht0,Complex.sub_re,Complex.one_re]
      exact (mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) hweight.2).trans hT
    exact pow_le_pow_left₀ (norm_nonneg _) hr 2
  calc
    _ = ∫ t in Icc X (2*X), ‖smoothDensity X s t‖^2 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      simp [smoothDensity_zero_outside hX s ht]
    _ ≤ ∫ _t in Icc X (2*X), (X^(s.re-1))^2 :=
      setIntegral_mono_on hfs.integrableOn (integrableOn_const (measure_Icc_lt_top.ne)) measurableSet_Icc hbound
    _ = X^(2*s.re-1) := by
      rw [setIntegral_const,Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith),smul_eq_mul,
        show 2*X-X=X by ring, ← Real.rpow_mul_natCast hX.le]
      nth_rewrite 1 [← Real.rpow_one X]
      rw [← Real.rpow_add hX]
      congr 1
      push_cast
      ring

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Complex Finset MeasureTheory Set GoldbachWeightedMajorResidual GoldbachSmoothWindow
open GoldbachSmoothMellin GoldbachTwistedMellin GoldbachPrincipalSeries
open scoped ContDiff Interval

private theorem norm_left_riemann_error (f : ℝ → ℂ) (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hf : Differentiable ℝ f) (hBound : ∀ t, ‖deriv f t‖ ≤ C) :
    ‖(∑ k ∈ range n, f (k:ℝ))-(∫ x in (0:ℝ)..(n:ℝ),f x)‖ ≤ C*n := by
  have hInt (k : ℕ) : IntervalIntegrable f volume (k:ℝ) (((k+1:ℕ):ℝ)) :=
    hf.continuous.intervalIntegrable _ _
  have hSum := intervalIntegral.sum_integral_adjacent_intervals
    (a:=fun k : ℕ => (k:ℝ)) (n:=n) (fun k _ => hInt k)
  simp only [Nat.cast_zero] at hSum
  rw [← hSum,← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _k ∈ range n,C := by
      apply sum_le_sum
      intro k _
      let a : ℝ := k
      let b : ℝ := (k+1:ℕ)
      have hb : b=a+1 := by simp [a,b]
      have hab : a≤b := by linarith only [hb]
      have hc : IntervalIntegrable (fun _ : ℝ => f a) volume a b := intervalIntegrable_const
      have hconst : (∫ _t in a..b, f a) = f a := by
        rw [intervalIntegral.integral_const, hb, show a+1-a=1 by ring, one_smul]
      change ‖f a - ∫ t in a..b,f t‖ ≤ C
      rw [← hconst, ← intervalIntegral.integral_sub hc (hInt k)]
      have hPt (t : ℝ) (ht : t ∈ uIoc a b) : ‖f a-f t‖ ≤ C := by
        rw [norm_sub_rev]
        have hh := Convex.norm_image_sub_le_of_norm_deriv_le (s:=(Set.univ:Set ℝ))
          (fun t _ => hf t) (fun t _ => hBound t) convex_univ (mem_univ a) (mem_univ t)
        refine hh.trans ?_
        have hs := uIoc_subset_uIcc ht
        rw [uIcc_of_le hab] at hs
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.1)]
        exact mul_le_of_le_one_right hC (by linarith only [hs.2,hb])
      refine (intervalIntegral.norm_integral_le_of_norm_le_const hPt).trans_eq ?_
      rw [hb,show a+1-a=1 by ring,abs_one,mul_one]
    _ = _ := by simp [nsmul_eq_mul,mul_comm]

set_option maxHeartbeats 1400000 in
theorem discrete_smooth_profile_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (X : ℕ), 0 < X → ∀ t : ℝ,
      ‖discreteModel X t -
        smoothTransform (X:ℝ) (2*(X:ℝ)) (2*Real.pi*t) (scaledWeight X) 1‖ ≤
        2*K+4*Real.pi*(X:ℝ)*|t| := by
  obtain ⟨K,hK,hW⟩ := weight_derivative_bound 1
  refine ⟨K,hK,?_⟩
  intro X hX t
  let x : ℝ := X
  let b := 2*Real.pi*t
  let f (u : ℝ) : ℂ := (scaledWeight x u:ℂ)*GoldbachTwistedMellin.phase b u
  let C := K/x+2*Real.pi*|t|
  have hx : 0 < x := by dsimp only [x]; exact_mod_cast hX
  have hWc : ContDiff ℝ 1 (scaledWeight x) := weight_smooth.comp (contDiff_id.div_const x)
  have hdf (u : ℝ) : HasDerivAt f
      (((deriv (scaledWeight x) u:ℝ):ℂ)*GoldbachTwistedMellin.phase b u +
        (scaledWeight x u:ℂ)*(GoldbachTwistedMellin.phase b u*((b:ℂ)*I))) u := by
    have hd := (((hWc.differentiable_one u).hasDerivAt).ofReal_comp).mul (phase_deriv b u)
    convert hd using 1
  have hf : Differentiable ℝ f := fun u => (hdf u).differentiableAt
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hC' (u : ℝ) : ‖deriv f u‖ ≤ C := by
    rw [(hdf u).deriv]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul,norm_real,norm_phase,norm_I,mul_one,one_mul]
    have hdu : ‖deriv (scaledWeight x) u‖ ≤ K/x := by
      have h := scaledWeight_derivative 1 x u
      simp only [iteratedDeriv_succ,iteratedDeriv_zero,pow_one] at h
      rw [h,norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hx.le)]
      have hw := hW (u/x)
      simp only [iteratedDeriv_succ,iteratedDeriv_zero] at hw
      calc
        _ ≤ x⁻¹*K := mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hx.le)
        _ = _ := by ring
    have hw := weight_range (u/x)
    have ha : ‖scaledWeight x u‖ ≤ 1 := by rw [scaledWeight,Real.norm_of_nonneg hw.1]; exact hw.2
    have hb : ‖b‖ = 2*Real.pi*|t| := by
      unfold b
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤2*Real.pi)]
    exact add_le_add hdu (by rw [hb]; exact mul_le_of_le_one_left (by positivity) ha)
  have hErr := norm_left_riemann_error f (2*X) hC hf hC'
  have hS : discreteModel X t = ∑ k ∈ range (2*X), f (k:ℝ) := by
    unfold discreteModel finiteModel
    rw [sum_range_succ]
    have hf2 : (scaledWeight x ((2*X:ℕ):ℝ):ℂ) = 0 := by
      unfold scaledWeight
      push_cast
      rw [mul_div_cancel_right₀ _ hx.ne']
      exact_mod_cast weight_zero (Or.inr (by norm_num : (31/16:ℝ)≤2))
    rw [hf2,zero_mul,add_zero]
    apply sum_congr rfl
    intro k _
    dsimp [f,b]
    unfold Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.phase GoldbachTwistedMellin.phase
    congr 3
    push_cast
    ring
  have hInt : smoothTransform x (2*x) b (scaledWeight x) 1 = ∫ u in (0:ℝ)..(2*x), f u := by
    unfold smoothTransform density
    simp only [sub_self,Complex.cpow_zero,mul_one]
    have hLeft : IntervalIntegrable f volume (0:ℝ) x := hf.continuous.intervalIntegrable _ _
    have hRight : IntervalIntegrable f volume x (2*x) := hf.continuous.intervalIntegrable _ _
    have hI := intervalIntegral.integral_add_adjacent_intervals hLeft hRight
    have hzero : (∫ u in (0:ℝ)..x,f u) = 0 := by
      rw [intervalIntegral.integral_congr (g:=fun _ => (0:ℂ))]
      · simp
      · intro u hu
        rw [uIcc_of_le hx.le] at hu
        dsimp [f,scaledWeight]
        rw [weight_zero (Or.inl ((div_le_iff₀ hx).mpr (by linarith only [hu.2,hx]))),
          ofReal_zero,zero_mul]
    simpa only [hzero,zero_add] using hI
  rw [hS, hInt]
  have hErr' : ‖(∑ k ∈ range (2*X), f (k:ℝ))-(∫ u in (0:ℝ)..(2*x),f u)‖ ≤ C*(2*x) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hErr
  refine hErr'.trans_eq ?_
  dsimp [C]
  field_simp [hx.ne']
  ring

end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Complex MeasureTheory Set Real
open scoped FourierTransform ComplexConjugate InnerProductSpace RealInnerProductSpace

private theorem vector_fourier_eq (f : ℝ → ℂ) :
    VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) f = 𝓕 f := rfl

private theorem vector_inverse_fourier_eq (f : ℝ → ℂ) :
    VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ ℝ) f = 𝓕⁻ f := rfl

theorem inverse_fourier_square_integrable {f : ℝ → ℂ} (hf : Integrable f)
    (hF : Integrable (𝓕 f)) : Integrable (fun u => ‖(𝓕⁻ f) u‖^2) := by
  have hFi : Integrable (𝓕⁻ f) := by
    rw [show (𝓕⁻ f) = fun t => (𝓕 f) (-t) from funext (Real.fourierInv_eq_fourier_neg f)]
    exact hF.comp_neg
  have hFc : Continuous (𝓕⁻ f) := by
    have hFun : (𝓕⁻ f) = fun t => (𝓕 f) (-t) := funext (Real.fourierInv_eq_fourier_neg f)
    rw [hFun]
    exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf).comp continuous_neg
  apply (hFi.norm.const_mul (∫ u, ‖f u‖)).mono' (hFc.norm.pow 2).aestronglyMeasurable
  filter_upwards with t
  have hbound : ‖(𝓕⁻ f) t‖ ≤ ∫ u, ‖f u‖ := by
    rw [Real.fourierInv_eq_fourier_neg]
    exact Real.norm_fourier_le_integral_norm f (-t)
  change ‖‖(𝓕⁻ f) t‖^2‖ ≤ (∫ u, ‖f u‖)*‖(𝓕⁻ f) t‖
  rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

set_option maxHeartbeats 1400000 in
theorem inverse_fourier_square_integral {f : ℝ → ℂ} (hc : Continuous f) (hf : Integrable f)
    (hF : Integrable (𝓕 f)) :
    (∫ u : ℝ, ‖(𝓕⁻ f) u‖^2) = ∫ x : ℝ, ‖f x‖^2 := by
  have h : (∫ u : ℝ, ‖(𝓕 f) u‖^2) = ∫ x : ℝ, ‖f x‖^2 := by
    have he := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
      (L:=innerₗ ℝ) (μ:=volume) (ν:=volume)
      (innerSL ℂ (E:=ℂ)) Real.continuous_fourierChar continuous_inner hf hF
    simp only [flip_innerₗ,vector_fourier_eq,vector_inverse_fourier_eq,innerSL_apply_apply] at he
    rw [hc.fourierInv_fourier_eq hf hF] at he
    have hinner (z : ℂ) : ⟪z,z⟫_ℂ = ((‖z‖^2:ℝ):ℂ) := by
      rw [Complex.ofReal_pow]
      exact inner_self_eq_norm_sq_to_K _
    simpa only [hinner,integral_complex_ofReal,Complex.ofReal_inj] using he
  have hn (u : ℝ) : ‖(𝓕⁻ f) u‖^2 = ‖(𝓕 f) (-u)‖^2 := by rw [Real.fourierInv_eq_fourier_neg]
  simp_rw [hn]
  let weight (u : ℝ) : ℝ := ‖(𝓕 f) u‖^2
  have h' : (∫ u, weight (-u)) = ∫ u, weight u :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (MeasurableEquiv.neg ℝ).measurableEmbedding weight
  exact h'.trans h

set_option maxHeartbeats 1400000 in
theorem inverse_fourier_real_convolution {f g : ℝ → ℂ} (hf : Integrable f)
    (hg : Integrable g) (hgc : Continuous g) (hG : Integrable (𝓕 g)) (m : ℝ) :
    (∫ u : ℝ, (𝓕⁻ f) u * (𝓕⁻ g) u * Complex.exp ((-2*Real.pi*m*u : ℝ)*I)) =
      ∫ x : ℝ, f x * g (m-x) := by
  let F := 𝓕⁻ f
  let G := 𝓕⁻ g
  let e (u : ℝ) : ℂ := Complex.exp ((-2*Real.pi*m*u : ℝ)*I)
  let b (u : ℝ) := G u*e u
  have hG' : Integrable G := by
    change Integrable (𝓕⁻ g)
    rw [show (𝓕⁻ g) = fun t => (𝓕 g) (-t) from funext (Real.fourierInv_eq_fourier_neg g)]
    exact hG.comp_neg
  have he (u : ℝ) : ‖e u‖ = 1 := by
    dsimp [e]
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hbe : Integrable b := by
    apply hG'.norm.mono' (hG'.aestronglyMeasurable.mul (by unfold e; fun_prop : Continuous e).aestronglyMeasurable)
    filter_upwards with u
    change ‖G u*e u‖ ≤ ‖G u‖
    simp [he]
  have hflip : (- innerₗ ℝ).flip = -innerₗ ℝ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change -⟪y,x⟫_ℝ = -⟪x,y⟫_ℝ
    rw [real_inner_comm]
  have hionv (x : ℝ) : (𝓕⁻ b) x = g (m-x) := by
    have h1 : (𝓕⁻ b) x = (𝓕⁻ G) (x-m) := by
      simp only [Real.fourierInv_eq',real_inner_comm,Real.inner_apply,smul_eq_mul]
      apply integral_congr_ae
      filter_upwards with u
      dsimp [b,e]
      rw [mul_left_comm _ (G u), ← Complex.exp_add, mul_comm _ (G u)]
      congr 3
      push_cast
      ring
    rw [h1, Real.fourierInv_eq_fourier_neg]
    dsimp [G]
    rw [Real.fourierInv_comm, hgc.fourierInv_fourier_eq hg hG]
    congr 1
    ring
  have hcont : Continuous (fun p : ℝ×ℝ => (-innerₗ ℝ) p.1 p.2) :=
    continuous_inner.neg
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L:= -innerₗ ℝ) (μ:=volume) (ν:=volume) Real.continuous_fourierChar hcont hf hbe
  simp only [hflip,vector_inverse_fourier_eq] at h
  simp only [hionv,smul_eq_mul] at h
  simpa only [b,F,G,e,mul_assoc] using h

end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset Complex MeasureTheory GoldbachSmoothMellin GoldbachSmoothWindow
open GoldbachPolynomialMinor205 (wave)
open scoped FourierTransform

private theorem continuous_inverse_fourier {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕⁻ f) := by
  have h : (𝓕⁻ f) = fun t => (𝓕 f) (-t) := funext (Real.fourierInv_eq_fourier_neg f)
  rw [h]
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf).comp continuous_neg

theorem arch_pair_window_le {X : ℝ} (hX : 0 < X) {s z : ℂ} (hs : s.re ≤ 1) (hz : z.re ≤ 1)
    (m R : ℝ) :
    ‖∫ t in Set.Icc (-R) R, smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) s *
      smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) z * wave (-m*t)‖ ≤
      X*X^(s.re-1)*X^(z.re-1) := by
  let f := smoothDensity X s
  let g := smoothDensity X z
  let F := 𝓕⁻ f
  let G := 𝓕⁻ g
  let S := Set.Icc (-R) R
  have hfC : Continuous f := (smoothDensity_smooth hX s).continuous
  have hgC : Continuous g := (smoothDensity_smooth hX z).continuous
  have hf : Integrable f := hfC.integrable_of_hasCompactSupport (smoothDensity_compact hX s)
  have hg : Integrable g := hgC.integrable_of_hasCompactSupport (smoothDensity_compact hX z)
  have hfF : Integrable (𝓕 f) := integrable_fourier_smoothDensity hX s
  have hgG : Integrable (𝓕 g) := integrable_fourier_smoothDensity hX z
  have hFSq : Integrable (fun t => ‖F t‖^2) := inverse_fourier_square_integrable hf hfF
  have hGSq : Integrable (fun t => ‖G t‖^2) := inverse_fourier_square_integrable hg hgG
  have hF2 : MemLp F 2 volume :=
    (memLp_two_iff_integrable_sq_norm (continuous_inverse_fourier hf).aestronglyMeasurable).mpr hFSq
  have hG2 : MemLp G 2 volume :=
    (memLp_two_iff_integrable_sq_norm (continuous_inverse_fourier hg).aestronglyMeasurable).mpr hGSq
  have hH := integral_mul_norm_le_Lp_mul_Lq (μ:=volume.restrict S)
    Real.HolderConjugate.two_two
    (by simpa using hF2.restrict S : MemLp F (ENNReal.ofReal 2) (volume.restrict S))
    (by simpa using hG2.restrict S : MemLp G (ENNReal.ofReal 2) (volume.restrict S))
  simp only [Real.rpow_ofNat,← Real.sqrt_eq_rpow] at hH
  have hSquF : (∫ t in S, ‖F t‖^2) ≤ X^(2*s.re-1) :=
    (integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hFSq).trans
      ((inverse_fourier_square_integral hfC hf hfF).le.trans (smoothDensity_square_integral_le hX hs))
  have hSquG : (∫ t in S, ‖G t‖^2) ≤ X^(2*z.re-1) :=
    (integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hGSq).trans
      ((inverse_fourier_square_integral hgC hg hgG).le.trans (smoothDensity_square_integral_le hX hz))
  simp_rw [← inverse_fourier_smoothDensity hX]
  change ‖∫ t in S, F t*G t*wave (-m*t)‖ ≤ _
  have hW (t : ℝ) : ‖wave (-m*t)‖ = 1 := by unfold wave; exact Complex.norm_exp_ofReal_mul_I _
  calc
    _ ≤ ∫ t in S, ‖F t*G t*wave (-m*t)‖ := norm_integral_le_integral_norm _
    _ = ∫ t in S, ‖F t‖*‖G t‖ := by simp only [norm_mul,hW,mul_one]
    _ ≤ Real.sqrt (∫ t in S, ‖F t‖^2)*Real.sqrt (∫ t in S, ‖G t‖^2) := hH
    _ ≤ Real.sqrt (X^(2*s.re-1))*Real.sqrt (X^(2*z.re-1)) :=
      mul_le_mul (Real.sqrt_le_sqrt hSquF) (Real.sqrt_le_sqrt hSquG)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hX.le,← Real.rpow_mul hX.le,← Real.rpow_add hX]
      have hf : X*X^(s.re-1) = X^s.re := by
        calc
          _ = X^(1:ℝ)*X^(s.re-1) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hX]; congr 1; ring
      rw [hf, ← Real.rpow_add hX]
      congr 1
      ring

/-- Untruncated smooth profiles reduce to an ordinary weighted convolution. -/
theorem arch_pair_full_eq {X : ℝ} (hX : 0 < X) (s z : ℂ) (m : ℝ) :
    (∫ t : ℝ, smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) s *
      smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) z * wave (-m*t)) =
      ∫ x : ℝ, smoothDensity X s x * smoothDensity X z (m-x) := by
  simp_rw [← inverse_fourier_smoothDensity hX]
  have hs := (smoothDensity_smooth hX s).continuous.integrable_of_hasCompactSupport (μ:=volume) (smoothDensity_compact hX s)
  have hzc := (smoothDensity_smooth hX z).continuous
  have hz := hzc.integrable_of_hasCompactSupport (μ:=volume) (smoothDensity_compact hX z)
  have h := inverse_fourier_real_convolution hs hz hzc (integrable_fourier_smoothDensity hX z) m
  have he (u : ℝ) : wave (-m*u) = Complex.exp ((-2*Real.pi*m*u:ℝ)*I) := by
    unfold wave
    congr 2
    push_cast
    ring
  simpa only [he] using h

end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Complex Finset MeasureTheory Goldbach GoldbachTwistedMellin GoldbachWeightedMajorResidual
open GoldbachZeroStrip GoldbachSmoothWindow GoldbachSmoothMellin
open GoldbachCorrectionBands
open scoped Classical

noncomputable section

def spectralPoint : GlobalMode → ℂ
  | none => 1
  | some r => r.2.2

def spectralCoefficient (i : GlobalMode) : ℂ :=
  if i = none then 1 else -(modeOrder i:ℂ)

def smoothGlobalProfile (X : ℕ) (i : GlobalMode) (t : ℝ) : ℂ :=
  spectralCoefficient i *
    smoothTransform (X:ℝ) (2*(X:ℝ)) (2*Real.pi*t) (scaledWeight (X:ℝ)) (spectralPoint i)

theorem spectralPoint_re_bounds {X : ℕ} {i : GlobalMode} (hi : i ∈ globalModesAt X) :
    0 ≤ (spectralPoint i).re ∧ (spectralPoint i).re ≤ 1 := by
  rcases i with _ | ⟨r,χ,z⟩
  · simp [spectralPoint]
  obtain ⟨hr,_,_,hzero⟩ := (mem_globalModesAt_zero χ z).mp hi
  let _ : NeZero r := ⟨(Nat.zero_lt_one.trans_le hr).ne'⟩
  have hmem : z ∈ (exceptionalZeros χ (heightCut (X:ℝ))).filter (shortNearZero X r) := by
    simpa only [globalShortZeros,dite_eq_left (NeZero.ne r)] using hzero
  obtain ⟨hβ,_,hz⟩ := ((mem_exceptionalZeros χ (heightCut (X:ℝ)) z).mp (mem_filter.mp hmem).1)
  exact ⟨by change 0 ≤ z.re; linarith,
    le_of_lt (lt_of_not_ge (fun h => GoldbachZeroFree.regularizedL_ne_zero_ge_one χ h hz))⟩

theorem norm_spectralCoefficient (i : GlobalMode) : ‖spectralCoefficient i‖ = modeOrder i := by
  rcases i with _ | ⟨r,χ,z⟩ <;> simp [spectralCoefficient,modeOrder]

theorem modeMass_eq_spectral_power {X : ℕ} (hX : 0 < X) {i : GlobalMode} (hi : i ∈ globalModesAt X) :
    modeMass X i = (modeOrder i:ℝ)*(X:ℝ)^((spectralPoint i).re-1) := by
  rcases i with _ | ⟨r,χ,z⟩
  · simp [modeMass,modeOrder,modeGap,spectralPoint]
  have hr := ((mem_globalModesAt_zero χ z).mp hi).1
  let _ : NeZero r := ⟨(Nat.zero_lt_one.trans_le hr).ne'⟩
  rw [modeMass_eq_power hX χ z]
  simp only [modeOrder,spectralPoint,dite_eq_left (NeZero.ne r)]

private theorem two_scale_re_le {X β : ℝ} (hX : 0 < X) (hβ : β ≤ 1) :
    (2*X)^β ≤ 2*(X^(β-1)*X) := by
  have hx : (X^(β-1)*X) = X^β := by
    calc
      _ = X^(β-1)*X^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hX,sub_add_cancel]
  rw [Real.mul_rpow (by norm_num) hX.le,hx]
  have ha : (2:ℝ)^β ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hβ
  exact mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hX.le _)

theorem norm_smooth_global_profile_le {X : ℕ} (hX : 0 < X) {i : GlobalMode} (hi : i ∈ globalModesAt X) (t : ℝ) :
    ‖smoothGlobalProfile X i t‖ ≤ 2*(X:ℝ)*modeMass X i := by
  have hx : (0:ℝ) < X := by exact_mod_cast hX
  obtain ⟨hβ,hβ'⟩ := spectralPoint_re_bounds hi
  have hTr := smooth_transform_norm_bound (X:=(X:ℝ))
    (β:=2*Real.pi*t) (w:=scaledWeight (X:ℝ)) (s:=spectralPoint i) (M:=1) hx le_rfl
    (by linarith) le_rfl hβ zero_le_one
    (fun x _ => by change ‖weight (x/(X:ℝ))‖ ≤ 1
                   rw [Real.norm_of_nonneg (weight_range _).1]
                   exact (weight_range _).2)
  simp only [one_mul] at hTr
  rw [smoothGlobalProfile,norm_mul,norm_spectralCoefficient,modeMass_eq_spectral_power hX hi]
  exact (mul_le_mul_of_nonneg_left (hTr.trans (two_scale_re_le hx hβ')) (Nat.cast_nonneg _)).trans_eq (by ring)

set_option maxHeartbeats 1800000 in
theorem actual_to_smooth_profile_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (X : ℕ), 32 ≤ X → ∀ i ∈ globalModesAt X, ∀ (t : ℝ),
      ‖globalProfile X i t-smoothGlobalProfile X i t‖ ≤
        K*(1+(X:ℝ)*|t|)*modeMass X i := by
  obtain ⟨D,hD,hD'⟩ := discrete_smooth_profile_error
  obtain ⟨E,hE,hE'⟩ := exact_taper_smooth_bound
  let K := 2*D+4*Real.pi+2*E
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro X hX i hi t
  have hp : 0 < X := by omega
  have hx : (0:ℝ)<X := by exact_mod_cast hp
  have hx1 : (1:ℝ)≤X := by exact_mod_cast (show 1≤X by omega)
  have hXT : 0 ≤ (X:ℝ)*|t| := by positivity
  have hK₁ : 2*D ≤ K := by dsimp [K]; linarith only [Real.pi_pos,hE]
  have hK₂ : 4*Real.pi ≤ K := by dsimp [K]; linarith only [hD,hE]
  have hK₃ : 2*E ≤ K := by dsimp [K]; linarith only [hD,Real.pi_pos]
  obtain ⟨hβ,hβ'⟩ := spectralPoint_re_bounds hi
  rcases i with _ | ⟨r,χ,z⟩
  · have hPole : spectralCoefficient none = 1 := by simp [spectralCoefficient]
    have hMass : modeMass X none = 1 := by simp [modeMass,modeOrder,modeGap]
    simp only [globalProfile,smoothGlobalProfile,hPole,hMass,spectralPoint,one_mul,mul_one]
    refine (hD' X hp t).trans ?_
    suffices 2*D+4*Real.pi*((X:ℝ)*|t|) ≤ K*(1+(X:ℝ)*|t|) by simpa only [mul_assoc,mul_one]
    nlinarith only [hK₁,mul_le_mul_of_nonneg_right hK₂ hXT]
  · have hr := ((mem_globalModesAt_zero χ z).mp hi).1
    let _ : NeZero r := ⟨(Nat.zero_lt_one.trans_le hr).ne'⟩
    have hg := hE' X hX (2*Real.pi*t) z hβ
    let o : ℕ := modeOrder (some ⟨r,χ,z⟩)
    have ho : (o:ℂ) = (analyticOrderNatAt (regularizedL χ) z:ℂ) := by simp [o,modeOrder,NeZero.ne r]
    have hPf : globalProfile X (some ⟨r,χ,z⟩) t =
        -(o:ℂ)*weightedTaperTransform X (2*X-1) (fun j=>scaledWeight (X:ℝ) j) (2*Real.pi*t) z := by
      simp only [globalProfile,dite_eq_left (NeZero.ne r),ho]
    have hSf : smoothGlobalProfile X (some ⟨r,χ,z⟩) t =
        -(o:ℂ)*smoothTransform (X:ℝ) (2*(X:ℝ)) (2*Real.pi*t) (scaledWeight (X:ℝ)) z := by
      simp [smoothGlobalProfile,spectralCoefficient,spectralPoint,o]
    have hbound : (2*(X:ℝ))^z.re * (E/(X:ℝ)^2) ≤ (2*E)*(X:ℝ)^(z.re-1) := calc
      _ ≤ (2*((X:ℝ)^(z.re-1)*(X:ℝ)))*(E/(X:ℝ)^2) :=
        mul_le_mul_of_nonneg_right (two_scale_re_le hx hβ') (by positivity)
      _ = (2*E)*(X:ℝ)^(z.re-1)/(X:ℝ) := by field_simp [hx.ne']
      _ ≤ _ := div_le_self (by positivity) hx1
    rw [hPf,hSf,← mul_sub,norm_mul,norm_neg,Complex.norm_natCast,modeMass_eq_spectral_power hp hi]
    change (o:ℝ)*‖_‖ ≤ K*(1+(X:ℝ)*|t|)*((o:ℝ)*(X:ℝ)^(z.re-1))
    calc
      _ ≤ (o:ℝ)*((2*E)*(X:ℝ)^(z.re-1)) :=
        mul_le_mul_of_nonneg_left (hg.trans hbound) (Nat.cast_nonneg _)
      _ ≤ (o:ℝ)*((K*(1+(X:ℝ)*|t|))*(X:ℝ)^(z.re-1)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact hK₃.trans (le_mul_of_one_le_right hK (by linarith only [hXT]))
      _ = _ := by ring

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Complex MeasureTheory Set
open GoldbachPolynomialMinor205 (wave)

set_option maxHeartbeats 1500000 in
/-- Replacing both profiles in a finite signed pair costs the squared arc scale. -/
theorem norm_pairIntegral_sub_le {ι : Type*} {X R K ai aj : ℝ} {m : ℕ}
    (hX : 1 ≤ X) (hR : 0 ≤ R) (hR1 : R ≤ 1) (hK : 0 ≤ K) (hi : 0 ≤ ai) (hj : 0 ≤ aj)
    (f g : ι → ℝ → ℂ) (i j : ι)
    (hfi : Continuous (f i)) (hfj : Continuous (f j)) (hgi : Continuous (g i)) (hgj : Continuous (g j))
    (hgiB : ∀ t, ‖g i t‖ ≤ 2*X*ai) (hgjB : ∀ t, ‖g j t‖ ≤ 2*X*aj)
    (hdi : ∀ t, ‖f i t-g i t‖ ≤ K*(1+X*|t|)*ai)
    (hdj : ∀ t, ‖f j t-g j t‖ ≤ K*(1+X*|t|)*aj) :
    ‖pairIntegral R m f i j-pairIntegral R m g i j‖ ≤
      2*K*(4+2*K)*(1+X*R)^2*ai*aj := by
  let S := Icc (-R) R
  let w (t : ℝ) := wave (-(m:ℝ)*t)
  let e (t : ℝ) := f i t*f j t*w t-g i t*g j t*w t
  let U := K*(1+X*R)*X*(4+2*K)*ai*aj
  have hW : Continuous w := by unfold w wave; fun_prop
  have hfi' : IntegrableOn (fun t => f i t*f j t*w t) S := ((hfi.mul hfj).mul hW).integrableOn_Icc
  have hgi' : IntegrableOn (fun t => g i t*g j t*w t) S := ((hgi.mul hgj).mul hW).integrableOn_Icc
  have hU (t : ℝ) (ht : t ∈ S) : ‖e t‖ ≤ U := by
    have htR := abs_le.mpr ht
    have hAX : 1+X*R ≤ 2*X := by nlinarith only [mul_le_mul_of_nonneg_left hR1 (zero_le_one.trans hX),hX]
    have hdi' : ‖f i t-g i t‖ ≤ K*(1+X*R)*ai := by
      exact (hdi t).trans (by gcongr)
    have hdj' : ‖f j t-g j t‖ ≤ K*(1+X*R)*aj := by
      exact (hdj t).trans (by gcongr)
    have hfj' : ‖f j t‖ ≤ (2+2*K)*X*aj := calc
      _ = ‖(f j t-g j t)+g j t‖ := by congr 1; ring
      _ ≤ ‖f j t-g j t‖+‖g j t‖ := norm_add_le _ _
      _ ≤ K*(1+X*R)*aj+2*X*aj := add_le_add hdj' (hgjB t)
      _ ≤ (2+2*K)*X*aj := by
        have hh : K*(1+X*R)*aj ≤ K*(2*X)*aj := by gcongr
        linarith only [hh,show K*(2*X)*aj+2*X*aj=(2+2*K)*X*aj by ring]
    have he : e t = (((f i t-g i t)*f j t) + g i t*(f j t-g j t))*w t := by
      dsimp [e]
      ring
    have hwn : ‖w t‖ = 1 := by unfold w wave; exact Complex.norm_exp_ofReal_mul_I _
    rw [he,norm_mul,hwn,mul_one]
    calc
      _ ≤ ‖(f i t-g i t)*f j t‖+‖g i t*(f j t-g j t)‖ := norm_add_le _ _
      _ ≤ (K*(1+X*R)*ai)*((2+2*K)*X*aj)+(2*X*ai)*(K*(1+X*R)*aj) := by
        simp only [norm_mul]
        exact add_le_add (mul_le_mul hdi' hfj' (norm_nonneg _) (by positivity))
          (mul_le_mul (hgiB t) hdj' (norm_nonneg _) (by positivity))
      _ = _ := by unfold U; ring
  have hU' : ∀ᵐ t ∂volume.restrict S, ‖e t‖ ≤ U := by
    filter_upwards [ae_restrict_mem (measurableSet_Icc : MeasurableSet S)] with t ht
    exact hU t ht
  have hIntegral : ‖∫ t in S,e t‖ ≤ 2*R*U := by
    have hconst : IntegrableOn (fun _ : ℝ => U) S := integrableOn_const measure_Icc_lt_top.ne
    refine (norm_integral_le_of_norm_le hconst hU').trans_eq ?_
    rw [setIntegral_const,Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith),smul_eq_mul]
    ring
  unfold pairIntegral
  change ‖(∫ t in S, f i t*f j t*w t)-(∫ t in S,g i t*g j t*w t)‖ ≤ _
  rw [← integral_sub hfi' hgi']
  refine hIntegral.trans ?_
  have hRR : X*R ≤ 1+X*R := by linarith
  calc
    _ = 2*K*(4+2*K)*(1+X*R)*(X*R)*ai*aj := by unfold U; ring
    _ ≤ 2*K*(4+2*K)*(1+X*R)*(1+X*R)*ai*aj := by gcongr
    _ = _ := by ring

end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset MeasureTheory GoldbachWeightedMajorResidual
open GoldbachPolynomialMinor205 (wave)
open GoldbachWeightedException (cutoff)
open Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc (unitMean)
open Conjectures.Goldbach.TwistedGoldbachSingularSeries (gaussCoefficient)
open scoped Classical

noncomputable section

def globalPairCoefficient (m q : ℕ) (i j : GlobalMode) : ℂ :=
  if hq : q ≠ 0 then
    let _ : NeZero q := ⟨hq⟩
    if globalLevel i ∣ q ∧ globalLevel j ∣ q then
      gaussCoefficient (modeCharacter q (globalLift q i))⁻¹ (modeCharacter q (globalLift q j))⁻¹ m
    else 0
  else 0

def shortSignedCoefficient (X m : ℕ) : ℂ :=
  ∑ q ∈ Icc 1 (cutoff X), ∑ a ∈ (range q).filter (fun a => a.Coprime q),
    ∫ β in Set.Icc (-arcRadius X q) (arcRadius X q),
      (unitMean q a*discreteModel X β-shortNearArcCorrection X q a β)^2*
        wave (-(m:ℝ)*((a:ℝ)/q+β))

set_option maxHeartbeats 2400000 in
theorem signedCoefficient_eq_global_pair_sum {X : ℕ} (hX : 2 ≤ X) (m : ℕ) :
    shortSignedCoefficient X m =
      ∑ i ∈ globalModesAt X, ∑ j ∈ globalModesAt X,
        ∑ q ∈ Icc 1 (cutoff X), globalPairCoefficient m q i j *
          pairIntegral (arcRadius X q) m (globalProfile X) i j := by
  let G := globalModesAt X
  let Q := Icc 1 (cutoff X)
  let F (q : ℕ) (i j : GlobalMode) := globalPairCoefficient m q i j *
    pairIntegral (arcRadius X q) m (globalProfile X) i j
  have hq (q : ℕ) (hqQ : q ∈ Q) :
      (∑ a ∈ (range q).filter (fun a => a.Coprime q),
        ∫ β in Set.Icc (-arcRadius X q) (arcRadius X q),
          (unitMean q a*discreteModel X β-shortNearArcCorrection X q a β)^2 *
            wave (-(m:ℝ)*((a:ℝ)/q+β))) = ∑ i ∈ G, ∑ j ∈ G, F q i j := by
    obtain ⟨h1,hP⟩ := mem_Icc.mp hqQ
    have hq0 := Nat.zero_lt_one.trans_le h1
    let _ : NeZero q := ⟨hq0.ne'⟩
    let S := G.filter (fun i => globalLevel i ∣ q)
    have hinj : Set.InjOn (globalLift q) (S : Set GlobalMode) := globalLift_injective
    rw [short_signedFiber_eq_gauss_pair_sum hX, ← globalModes_lift_exact hP]
    change (∑ i ∈ S.image (globalLift q), ∑ j ∈ S.image (globalLift q), _) = _
    rw [sum_image hinj]
    have hf (i : GlobalMode) (hi : i ∈ S) :
        (∑ j ∈ S.image (globalLift q),
          gaussCoefficient (modeCharacter q (globalLift q i))⁻¹ (modeCharacter q j)⁻¹ m *
            pairIntegral (arcRadius X q) m (signedProfile X q) (globalLift q i) j) =
        ∑ j ∈ S, F q i j := by
      rw [sum_image hinj]
      refine sum_congr rfl fun j hj => ?_
      obtain ⟨hGi,hDi⟩ := mem_filter.mp hi
      obtain ⟨hGj,hDj⟩ := mem_filter.mp hj
      simp only [F,globalPairCoefficient,dite_eq_left hq0.ne',ite_eq_left (show globalLevel i ∣ q ∧
        globalLevel j ∣ q from ⟨hDi,hDj⟩)]
      unfold pairIntegral
      simp only [signedProfile_lift_eq_global hGi hDi, signedProfile_lift_eq_global hGj hDj]
    calc
      _ = ∑ i ∈ S, ∑ j ∈ S, F q i j := sum_congr rfl hf
      _ = _ := by
        change (∑ i ∈ G.filter (fun i => globalLevel i ∣ q), ∑ j ∈ S, F q i j) = _
        rw [sum_filter]
        refine sum_congr rfl fun i hi => ?_
        by_cases hI : globalLevel i ∣ q
        · rw [ite_eq_left hI]
          change (∑ j ∈ G.filter (fun j => globalLevel j ∣ q), F q i j) = _
          rw [sum_filter]
          refine sum_congr rfl fun j hj => ?_
          by_cases hJ : globalLevel j ∣ q
          · rw [ite_eq_left hJ]
          · simp [hJ,F,globalPairCoefficient]
        · rw [ite_eq_right hI]
          symm
          apply sum_eq_zero
          intro j hj
          simp [hI,F,globalPairCoefficient]
  calc
    _ = ∑ q ∈ Q, ∑ i ∈ G, ∑ j ∈ G, F q i j := by
      unfold shortSignedCoefficient
      exact sum_congr rfl hq
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      rw [sum_comm]

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset DirichletCharacter
open Conjectures.Goldbach.TwistedGoldbachSingularSeries
open scoped Classical BigOperators

noncomputable section

def globalSourceCharacter (i : GlobalMode) : DirichletCharacter ℂ (globalLevel i) :=
  match i with
  | none => 1
  | some ⟨_,χ,_⟩ => χ

def globalPairConductor (i j : GlobalMode) : ℕ :=
  (((globalSourceCharacter i)⁻¹).mul (globalSourceCharacter j)⁻¹).conductor

def globalOrdinarySingularSeries (m : ℕ) : ℝ :=
  (∑' q : ℕ, coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m q).re

theorem globalLevel_pos {X : ℕ} {i : GlobalMode} (hi : i ∈ globalModesAt X) :
    0 < globalLevel i := by
  rcases i with _ | ⟨r,χ,z⟩
  · exact Nat.zero_lt_one
  · exact (mem_globalModesAt_zero χ z).mp hi |>.1

theorem globalSourceCharacter_isPrimitive {X : ℕ} {i : GlobalMode}
    (hi : i ∈ globalModesAt X) : (globalSourceCharacter i).IsPrimitive := by
  rcases i with _ | ⟨r,χ,z⟩
  · exact isPrimitive_one_level_one
  · exact ((mem_globalModesAt_zero χ z).mp hi).2.2.1

theorem modeCharacter_globalLift {q : ℕ} {i : GlobalMode} (h : globalLevel i ∣ q) :
    modeCharacter q (globalLift q i) = changeLevel h (globalSourceCharacter i) := by
  rcases i with _ | ⟨r,χ,z⟩
  · simp [modeCharacter,globalLift,globalSourceCharacter]
  · have hd : r ∣ q := h
    change modeCharacter q (globalLift q (some ⟨r,χ,z⟩)) = changeLevel hd χ
    simp only [modeCharacter,globalLift,dite_eq_left hd]

/-- The source coefficients in the global signed expansion use the inverse
characters because the additive amplitudes are conjugated. -/
theorem globalPairCoefficient_eq_coefficient (m q : ℕ) (i j : GlobalMode) :
    globalPairCoefficient m q i j =
      coefficient (globalSourceCharacter i)⁻¹ (globalSourceCharacter j)⁻¹ m q := by
  by_cases hq : q=0
  · simp [globalPairCoefficient,coefficient,hq]
  · let : NeZero q := ⟨hq⟩
    by_cases h : globalLevel i ∣ q ∧ globalLevel j ∣ q
    · rw [coefficient_of_dvd _ _ _ h.1 h.2]
      simp only [globalPairCoefficient,dite_eq_left hq,ite_eq_left h,
        modeCharacter_globalLift h.1,modeCharacter_globalLift h.2,map_inv]
    · simp [globalPairCoefficient,coefficient,hq,h]

theorem globalOrdinarySingularSeries_eq (m : ℕ) :
    globalOrdinarySingularSeries m = (∑' q : ℕ, globalPairCoefficient m q none none).re := by
  simp only [globalOrdinarySingularSeries,globalPairCoefficient_eq_coefficient]
  change _ = (∑' q : ℕ, coefficient ((1:DirichletCharacter ℂ 1)⁻¹)
    ((1:DirichletCharacter ℂ 1)⁻¹) m q).re
  simp only [inv_one]

/-- The absolute mass of every finite denominator selection is uniformly
bounded by the ordinary singular series for positive even targets. -/
theorem globalPairCoefficient_absolute_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X m : ℕ}, 0 < m → Even m → ∀ {i j : GlobalMode},
        i ∈ globalModesAt X → j ∈ globalModesAt X →
        ∀ D : Finset ℕ, (∑ q ∈ D, ‖globalPairCoefficient m q i j‖) ≤
          C*globalOrdinarySingularSeries m := by
  obtain ⟨C,hC,h⟩ := finite_absolute_product_conductor_le_ordinary_signed
    (show (0:ℝ)<1/2 by norm_num)
  refine ⟨C,hC,?_⟩
  intro X m hm he i j hi hj D
  let : NeZero (globalLevel i) := ⟨(globalLevel_pos hi).ne'⟩
  let : NeZero (globalLevel j) := ⟨(globalLevel_pos hj).ne'⟩
  have h' := h (globalSourceCharacter i)⁻¹ (globalSourceCharacter j)⁻¹
    (globalSourceCharacter_isPrimitive hi).inv (globalSourceCharacter_isPrimitive hj).inv m hm he D
  simpa only [globalPairCoefficient_eq_coefficient,globalOrdinarySingularSeries,
    sub_self,Real.rpow_zero,mul_one] using h'

theorem globalPairCoefficient_off_support {η : ℝ} (hη : 0 < η) :
    ∃ K H : ℕ, 0 < K ∧ 0 < H ∧
      ∀ {X m : ℕ}, 0 < m → Even m → ∀ {i j : GlobalMode},
        i ∈ globalModesAt X → j ∈ globalModesAt X →
        ¬ (globalPairConductor i j≤K ∧ (globalLevel i).lcm (globalLevel j)∣H*m) →
        ∀ D : Finset ℕ, (∑ q ∈ D, ‖globalPairCoefficient m q i j‖) ≤
          η*globalOrdinarySingularSeries m := by
  obtain ⟨K,H,hK,hH,h⟩ := finite_absolute_off_bounded_divisibility_support hη
  refine ⟨K,H,hK,hH,?_⟩
  intro X m hm he i j hi hj hbad D
  let : NeZero (globalLevel i) := ⟨(globalLevel_pos hi).ne'⟩
  let : NeZero (globalLevel j) := ⟨(globalLevel_pos hj).ne'⟩
  have h' := h (globalSourceCharacter i)⁻¹ (globalSourceCharacter j)⁻¹
    (globalSourceCharacter_isPrimitive hi).inv (globalSourceCharacter_isPrimitive hj).inv
    m hm he hbad D
  simpa only [globalPairCoefficient_eq_coefficient,globalOrdinarySingularSeries] using h'

/-- The first denominator alone gives a positive, target-independent lower
bound for the signed ordinary series at all positive even targets. -/
theorem globalOrdinarySingularSeries_pos_uniform :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 0 < m → Even m → c < globalOrdinarySingularSeries m := by
  obtain ⟨A,hA,h⟩ := ordinary_absolute_total_le_signed
  refine ⟨1/(2*A),by positivity,?_⟩
  intro m hm he
  have hOne : coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m 1 = 1 := by
    rw [ordinaryCoefficient_eq_majorCoefficient]
    exact Conjectures.Goldbach.MajorFixed144_aux.GoldbachMajorArc.coefficient_one m
  have hfirst : (1:ℝ) ≤ ∑' q : ℕ,
      ‖coefficient (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m q‖ := by
    simpa only [sum_singleton,hOne,norm_one] using
      (summable_coefficients (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) m hm).sum_le_tsum
        {1} (fun _ _ => norm_nonneg _)
  have hS : 1/A ≤ globalOrdinarySingularSeries m :=
    (div_le_iff₀ hA).2 (by simpa only [globalOrdinarySingularSeries,mul_comm] using hfirst.trans (h m hm he))
  exact (one_div_lt_one_div_of_lt hA (by linarith)).trans_le hS

/-- Either primitive source level and the product conductor together are
multiples of the least common multiple of both source levels. -/
theorem primitive_levels_lcm_dvd_conductor_mul {r s : ℕ} [NeZero r] [NeZero s]
    (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s)
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) :
    r.lcm s ∣ (α.mul β).conductor*r ∧ r.lcm s ∣ (α.mul β).conductor*s := by
  let L := r.lcm s
  let : NeZero L := ⟨Nat.lcm_ne_zero (NeZero.ne r) (NeZero.ne s)⟩
  let A := changeLevel (Nat.dvd_lcm_left r s) α
  let B := changeLevel (Nat.dvd_lcm_right r s) β
  let c := (α.mul β).conductor
  have ha : A.conductor=r := (conductor_changeLevel α (Nat.dvd_lcm_left r s)).trans hα
  have hb : B.conductor=s := (conductor_changeLevel β (Nat.dvd_lcm_right r s)).trans hβ
  have hc : (A*B).conductor=c := rfl
  have hrd : r ∣ c.lcm s := by
    have h := conductor_mul_dvd_lcm_conductor (A*B) B⁻¹
    rwa [show A*B*B⁻¹=A by simp [mul_assoc],conductor_inv,ha,hb,hc] at h
  have hsd : s ∣ c.lcm r := by
    have h := conductor_mul_dvd_lcm_conductor (A*B) A⁻¹
    rwa [show A*B*A⁻¹=B by simp [mul_comm,mul_left_comm],conductor_inv,ha,hb,hc] at h
  exact ⟨Nat.lcm_dvd (dvd_mul_left _ _) (hsd.trans (Nat.lcm_dvd_mul c r)),
    Nat.lcm_dvd (hrd.trans (Nat.lcm_dvd_mul c s)) (dvd_mul_left _ _)⟩

theorem globalPairConductor_pos {X : ℕ} {i j : GlobalMode}
    (hi : i ∈ globalModesAt X) (hj : j ∈ globalModesAt X) : 0 < globalPairConductor i j := by
  apply Nat.pos_of_ne_zero
  intro h
  exact Nat.lcm_ne_zero (globalLevel_pos hi).ne' (globalLevel_pos hj).ne'
    (conductor_eq_zero_iff_level_eq_zero.mp h)

theorem globalPair_lcm_le_of_conductor_le {X K : ℕ} {i j : GlobalMode}
    (hi : i ∈ globalModesAt X) (hj : j ∈ globalModesAt X)
    (hK : globalPairConductor i j ≤ K) :
    (globalLevel i).lcm (globalLevel j) ≤ K*globalLevel i ∧
      (globalLevel i).lcm (globalLevel j) ≤ K*globalLevel j := by
  let : NeZero (globalLevel i) := ⟨(globalLevel_pos hi).ne'⟩
  let : NeZero (globalLevel j) := ⟨(globalLevel_pos hj).ne'⟩
  obtain ⟨hr,hs⟩ := primitive_levels_lcm_dvd_conductor_mul (globalSourceCharacter i)⁻¹
    (globalSourceCharacter j)⁻¹ (globalSourceCharacter_isPrimitive hi).inv
    (globalSourceCharacter_isPrimitive hj).inv
  have hc := globalPairConductor_pos hi hj
  exact ⟨(Nat.le_of_dvd (Nat.mul_pos hc (globalLevel_pos hi)) hr).trans (Nat.mul_le_mul_right _ hK),
    (Nat.le_of_dvd (Nat.mul_pos hc (globalLevel_pos hj)) hs).trans (Nat.mul_le_mul_right _ hK)⟩

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset

noncomputable section

def pairTail {ι : Type*} (S : Finset ι) (good : ι → Prop) [DecidablePred good] :
    Finset (ι × ι) :=
  (S ×ˢ S).filter (fun p => ¬(good p.1 ∧ good p.2))

/-- Remove all pairs involving an omitted mode, using a first-power mass bound. -/
theorem norm_pairTail_le {ι κ : Type*} (S : Finset ι) (Q : Finset κ) (good : ι → Prop)
    [DecidablePred good] (a : ι → ℝ) (A B : κ → ι → ι → ℂ) {C H : ℝ}
    (ha : ∀ i ∈ S, 0 ≤ a i) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hA : ∀ i ∈ S, ∀ j ∈ S, (∑ q ∈ Q, ‖A q i j‖) ≤ H)
    (hB : ∀ q ∈ Q, ∀ i ∈ S, ∀ j ∈ S, ‖B q i j‖ ≤ C*a i*a j) :
    ‖∑ p ∈ pairTail S good, ∑ q ∈ Q, A q p.1 p.2*B q p.1 p.2‖ ≤
      2*C*H*(∑ i ∈ S, a i)*(∑ i ∈ S.filter (fun i => ¬good i), a i) := by
  classical
  let R := S.filter (fun i => ¬good i)
  let D := pairTail S good
  let L := R ×ˢ S
  let M := S ×ˢ R
  let f (p : ι×ι) := a p.1*a p.2
  have hD : D ⊆ L∪M := by
    intro p hp
    obtain ⟨hpS,hpG⟩ := mem_filter.mp hp
    obtain ⟨hi,hj⟩ := mem_product.mp hpS
    push Not at hpG
    simp only [L,M,R,mem_union,mem_product,mem_filter]
    by_cases h : good p.1
    · exact Or.inr ⟨hi,hj,hpG h⟩
    · exact Or.inl ⟨⟨hi,h⟩,hj⟩
  have hN : ∀ p ∈ L ∪ M, 0 ≤ f p := by
    intro p hp
    obtain hp | hp := mem_union.mp hp
    · obtain ⟨hi,hj⟩ := mem_product.mp hp
      exact mul_nonneg (ha _ (mem_filter.mp hi).1) (ha _ hj)
    · obtain ⟨hi,hj⟩ := mem_product.mp hp
      exact mul_nonneg (ha _ hi) (ha _ (mem_filter.mp hj).1)
  have hsum (p : ι×ι) (hp : p ∈ D) :
      ‖∑ q ∈ Q, A q p.1 p.2 * B q p.1 p.2‖ ≤ C*H*f p := by
    obtain ⟨hi,hj⟩ := mem_product.mp (mem_filter.mp hp).1
    have hn : 0 ≤ C*a p.1*a p.2 := mul_nonneg (mul_nonneg hC (ha _ hi)) (ha _ hj)
    calc
      _ ≤ ∑ q ∈ Q, ‖A q p.1 p.2*B q p.1 p.2‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Q, ‖A q p.1 p.2‖ * (C*a p.1*a p.2) := by
        apply sum_le_sum
        intro q hq
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB q hq _ hi _ hj) (norm_nonneg _)
      _ ≤ C*H*f p := by
        rw [← sum_mul]
        exact (mul_le_mul_of_nonneg_right (hA _ hi _ hj) hn).trans_eq (by dsimp [f]; ring)
  have hUnion : ∑ p ∈ L∪M, f p ≤ (∑ p ∈ L, f p)+(∑ p ∈ M, f p) := by
    have h := sum_union_inter (f := f) (s₁ := L) (s₂ := M)
    have hI : 0 ≤ ∑ p ∈ L∩M, f p :=
      sum_nonneg (fun p hp => hN p (mem_union.mpr (Or.inl (mem_inter.mp hp).1)))
    linarith only [h,hI]
  have hL : ∑ p ∈ L, f p = (∑ i ∈ R, a i)*(∑ i ∈ S, a i) := by
    dsimp only [L]
    rw [sum_product,sum_mul]
    simp only [f,mul_sum]
  have hM : ∑ p ∈ M, f p = (∑ i ∈ S, a i)*(∑ i ∈ R, a i) := by
    dsimp only [M]
    rw [sum_product,sum_mul]
    simp only [f,mul_sum]
  calc
    _ ≤ ∑ p ∈ D, ‖∑ q ∈ Q, A q p.1 p.2 * B q p.1 p.2‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ D, C*H*f p := sum_le_sum hsum
    _ = C*H*(∑ p ∈ D, f p) := by rw [mul_sum]
    _ ≤ C*H*((∑ p ∈ L, f p)+(∑ p ∈ M, f p)) :=
      mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg hD
        (fun p hp _ => hN p hp)).trans hUnion) (mul_nonneg hC hH)
    _ = _ := by rw [hL,hM]; change _ = 2*C*H*(∑ i ∈ S, a i)*(∑ i ∈ R, a i); ring

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset Filter Complex MeasureTheory Goldbach GoldbachTwistedMellin
open GoldbachSmoothMellin GoldbachSmoothWindow GoldbachWeightedMajorResidual
open GoldbachPolynomialMinor205 (wave)
open GoldbachWeightedException (cutoff)
open scoped FourierTransform Classical

theorem continuous_globalProfile {X : ℕ} {i : GlobalMode} (hX : 2 ≤ X)
    (hi : i ∈ globalModesAt X) : Continuous (globalProfile X i) := by
  let q := globalLevel i
  let _ : NeZero q := ⟨(globalLevel_pos hi).ne'⟩
  rw [← signedProfile_lift_eq_global (q:=q) hi (dvd_refl q)]
  exact continuous_signedProfile hX _

theorem continuous_smoothGlobalProfile {X : ℕ} (hX : 0 < X) (i : GlobalMode) :
    Continuous (smoothGlobalProfile X i) := by
  have hx : (0:ℝ) < X := by exact_mod_cast hX
  let f := smoothDensity X (spectralPoint i)
  have hf : Integrable f :=
    (smoothDensity_smooth hx (spectralPoint i)).continuous.integrable_of_hasCompactSupport
      (smoothDensity_compact hx (spectralPoint i))
  have h : (𝓕⁻ f) = fun t : ℝ => (𝓕 f) (-t) :=
    funext (Real.fourierInv_eq_fourier_neg f)
  have hc : Continuous (𝓕⁻ f) := h ▸
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf).comp continuous_neg
  have ht : smoothGlobalProfile X i = fun t => spectralCoefficient i * (𝓕⁻ f) t := by
    funext t
    simp only [smoothGlobalProfile,f,inverse_fourier_smoothDensity hx]
  rw [ht]
  exact hc.const_mul _

theorem smooth_pairIntegral_eq {X m : ℕ} {R : ℝ} (i j : GlobalMode) :
    pairIntegral R m (smoothGlobalProfile X) i j =
      (spectralCoefficient i*spectralCoefficient j)*
        ∫ t in Set.Icc (-R) R,
          smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) (spectralPoint i) *
          smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) (spectralPoint j) *
          wave (-(m:ℝ)*t) := by
  unfold pairIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [smoothGlobalProfile]
  ring

theorem norm_smooth_pairIntegral_le {X m : ℕ} (hX : 0 < X) {i j : GlobalMode}
    (hi : i ∈ globalModesAt X) (hj : j ∈ globalModesAt X) (R : ℝ) :
    ‖pairIntegral R m (smoothGlobalProfile X) i j‖ ≤
      (X:ℝ)*modeMass X i*modeMass X j := by
  have hx : (0:ℝ) < X := by exact_mod_cast hX
  rw [smooth_pairIntegral_eq,norm_mul,norm_mul,norm_spectralCoefficient,norm_spectralCoefficient,
    modeMass_eq_spectral_power hX hi,modeMass_eq_spectral_power hX hj]
  refine (mul_le_mul_of_nonneg_left (arch_pair_window_le hx (spectralPoint_re_bounds hi).2
    (spectralPoint_re_bounds hj).2 m R) (by positivity)).trans_eq ?_
  ring

theorem norm_weighted_pair_difference {ι κ : Type*} (S : Finset ι) (Q : Finset κ)
    (a : ι → ℝ) (A B : κ → ι → ι → ℂ) {C H : ℝ}
    (ha : ∀ i ∈ S, 0 ≤ a i) (hC : 0 ≤ C)
    (hA : ∀ i ∈ S, ∀ j ∈ S, (∑ q ∈ Q, ‖A q i j‖) ≤ H)
    (hB : ∀ q ∈ Q, ∀ i ∈ S, ∀ j ∈ S, ‖B q i j‖ ≤ C*a i*a j) :
    ‖∑ i ∈ S, ∑ j ∈ S, ∑ q ∈ Q, A q i j*B q i j‖ ≤
      C*H*(∑ i ∈ S, a i)^2 := by
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ∑ q ∈ Q, ‖A q i j*B q i j‖ :=
      (norm_sum_le _ _).trans (sum_le_sum (fun i _ =>
        (norm_sum_le _ _).trans (sum_le_sum (fun j _ => norm_sum_le _ _))))
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, C*H*a i*a j := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      calc
        _ ≤ ∑ q ∈ Q, ‖A q i j‖*(C*a i*a j) := by
          apply sum_le_sum
          intro q hq
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hB q hq i hi j hj) (norm_nonneg _)
        _ = (∑ q ∈ Q, ‖A q i j‖)*(C*a i*a j) := by rw [sum_mul]
        _ ≤ H*(C*a i*a j) := mul_le_mul_of_nonneg_right (hA i hi j hj)
          (mul_nonneg (mul_nonneg hC (ha i hi)) (ha j hj))
        _ = _ := by ring
    _ = _ := by simp_rw [← mul_sum,← sum_mul,← mul_sum]; ring

theorem arcRadius_mul_scale_le {X q : ℕ} (hX : 0 < X) (hq : 1 ≤ q) :
    (X:ℝ)*arcRadius X q ≤ (cutoff X:ℝ) := by
  have hx : (0:ℝ) < X := by exact_mod_cast hX
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hd : 0 < (q:ℝ)*(4*(X:ℝ)) := mul_pos (zero_lt_one.trans_le hq') (by positivity)
  unfold arcRadius
  push_cast
  rw [← mul_div_assoc,div_le_iff₀ hd]
  have hb : (X:ℝ) ≤ (q:ℝ)*(4*(X:ℝ)) := by nlinarith [mul_le_mul_of_nonneg_right hq' hx.le]
  exact (mul_comm (X:ℝ) (cutoff X:ℝ)).le.trans
    (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))

noncomputable def shortSmoothCoefficient (X m : ℕ) : ℂ :=
  ∑ i ∈ globalModesAt X, ∑ j ∈ globalModesAt X, ∑ q ∈ Icc 1 (cutoff X),
    globalPairCoefficient m q i j*pairIntegral (arcRadius X q) m (smoothGlobalProfile X) i j

set_option maxHeartbeats 2000000 in
theorem norm_shortSignedCoefficient_sub_smooth_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ m : ℕ, 0 < m → Even m →
        ‖shortSignedCoefficient X m-shortSmoothCoefficient X m‖ ≤
          C*globalOrdinarySingularSeries m*(1+(cutoff X:ℝ))^2 := by
  obtain ⟨A,hA,hmass⟩ := short_global_mass_and_tail
  obtain ⟨K,hK,hd⟩ := actual_to_smooth_profile_error
  obtain ⟨H,hH,ha⟩ := globalPairCoefficient_absolute_le
  obtain ⟨c,hc, hsing⟩ := globalOrdinarySingularSeries_pos_uniform
  refine ⟨2*K*(4+2*K)*H*A^2,by positivity,?_⟩
  filter_upwards [hmass,eventually_ge_atTop (2^200:ℕ)] with X hmass hX m hm he
  have hp : 0 < X := by omega
  have hx : (0:ℝ) < X := by exact_mod_cast hp
  have h32 : 32 ≤ X := by omega
  have hP := (cutoff_scale hX).2.2
  let B (q : ℕ) (i j : GlobalMode) :=
    pairIntegral (arcRadius X q) m (globalProfile X) i j -
      pairIntegral (arcRadius X q) m (smoothGlobalProfile X) i j
  rw [signedCoefficient_eq_global_pair_sum (by omega),shortSmoothCoefficient]
  simp_rw [← sum_sub_distrib,← mul_sub]
  change ‖∑ i ∈ globalModesAt X, ∑ j ∈ globalModesAt X, ∑ q ∈ Icc 1 (cutoff X),
    globalPairCoefficient m q i j*B q i j‖ ≤ _
  have hB (q : ℕ) (hq : q ∈ Icc 1 (cutoff X)) (i : GlobalMode) (hi : i ∈ globalModesAt X)
      (j : GlobalMode) (hj : j ∈ globalModesAt X) :
      ‖B q i j‖ ≤ (2*K*(4+2*K)*(1+(cutoff X:ℝ))^2)*modeMass X i*modeMass X j := by
    have hq₁ := (mem_Icc.mp hq).1
    have hb := arcRadius_mul_scale_le hp hq₁
    have hR : 0 ≤ arcRadius X q := by unfold arcRadius; positivity
    have hR' : arcRadius X q ≤ 1 := by
      apply le_of_not_gt
      intro hh
      have hPt : (cutoff X:ℝ) ≤ X := by exact_mod_cast hP
      have hLt := mul_lt_mul_of_pos_left hh hx
      linarith only [hPt,hLt,hb]
    have h := norm_pairIntegral_sub_le (X:=(X:ℝ)) (R:=arcRadius X q) (m:=m)
      (by exact_mod_cast hp) hR hR' hK (modeMass_nonneg X i) (modeMass_nonneg X j)
      (globalProfile X) (smoothGlobalProfile X) i j
      (continuous_globalProfile (by omega) hi) (continuous_globalProfile (by omega) hj)
      (continuous_smoothGlobalProfile hp i) (continuous_smoothGlobalProfile hp j)
      (norm_smooth_global_profile_le hp hi) (norm_smooth_global_profile_le hp hj)
      (hd X h32 i hi) (hd X h32 j hj)
    refine h.trans ?_
    have hai := modeMass_nonneg X i
    have haj := modeMass_nonneg X j
    gcongr
  have h := norm_weighted_pair_difference (globalModesAt X) (Icc 1 (cutoff X))
    (modeMass X) (globalPairCoefficient m) B (fun i _ => modeMass_nonneg X i)
    (show 0 ≤ 2*K*(4+2*K)*(1+(cutoff X:ℝ))^2 by positivity)
    (fun i hi j hj => ha hm he hi hj _) hB
  refine h.trans ?_
  have hM : 0 ≤ ∑ i ∈ globalModesAt X, modeMass X i := sum_nonneg (fun i _ => modeMass_nonneg X i)
  have hS : 0 ≤ globalOrdinarySingularSeries m := (hc.trans (hsing m hm he)).le
  calc
    _ ≤ (2*K*(4+2*K)*(1+(cutoff X:ℝ))^2)*(H*globalOrdinarySingularSeries m)*A^2 := by
      gcongr
      exact hmass.1
    _ = _ := by ring

end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset Set
open scoped Classical

/-- A finite set of transition scales leaves a multiplicative interval between
successive candidates. -/
theorem exists_separated_scale (S : Finset ℝ) {U B : ℝ} (hU : 0 < U) (hB : 1 < B) :
    ∃ j : ℕ, j ≤ S.card ∧
      ∀ s ∈ S, s < U*B^(3*j) ∨ U*B^(3*j+2) < s := by
  classical
  let I := range (S.card+1)
  by_contra! h
  have hex (j : ℕ) (hj : j ∈ I) : ∃ s ∈ S, s ∈ Set.Icc (U*B^(3*j)) (U*B^(3*j+2)) := by
    obtain ⟨s,hs,h₁,h₂⟩ := h j (Nat.le_of_lt_succ (mem_range.mp hj))
    exact ⟨s,hs,h₁,h₂⟩
  let f (j : ℕ) : ℝ := if h : j ∈ I then (hex j h).choose else 0
  have hm (j : ℕ) (hj : j ∈ I) :
      f j ∈ S ∧ f j ∈ Set.Icc (U*B^(3*j)) (U*B^(3*j+2)) := by
    dsimp only [f]
    rw [dite_eq_left hj]
    exact (hex j hj).choose_spec
  have hdis (i j : ℕ) (hij : i < j) : U*B^(3*i+2) < U*B^(3*j) :=
    mul_lt_mul_of_pos_left (pow_lt_pow_right₀ hB (by omega)) hU
  have hinj : Set.InjOn f I := by
    intro i hi j hj he
    rcases lt_trichotomy i j with hij | h | hji
    · exact False.elim ((not_lt_of_ge ((hm j hj).2.1.trans
        (he ▸ (hm i hi).2.2))) (hdis i j hij))
    · exact h
    · exact False.elim ((not_lt_of_ge ((hm i hi).2.1.trans
        (he.symm ▸ (hm j hj).2.2))) (hdis j i hji))
  have hh := card_le_card_of_injOn f (fun j hj => (hm j hj).1) hinj
  simp only [I,card_range,Nat.not_succ_le_self] at hh

theorem exists_separated_center (S : Finset ℝ) {U B : ℝ} (hU : 0 < U) (hB : 1 < B) :
    ∃ P : ℝ, U ≤ P ∧ P ≤ U*B^(3*S.card+1) ∧
      ∀ s ∈ S, s < P/B ∨ P*B < s := by
  obtain ⟨j,hj,hjS⟩ := exists_separated_scale S hU hB
  let P := U*B^(3*j+1)
  have hp : 0 < B := zero_lt_one.trans hB
  refine ⟨P,le_mul_of_one_le_right hU.le (one_le_pow₀ hB.le), ?_,?_⟩
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB.le (by omega)) hU.le
  · intro s hs
    have hleft : P/B = U*B^(3*j) := by
      unfold P
      rw [pow_succ, ← mul_assoc, mul_div_cancel_right₀ _ hp.ne']
    have hright : P*B = U*B^(3*j+2) := by
      unfold P
      rw [show 3*j+2=3*j+1+1 by omega]
      simp only [pow_succ]
      ring
    rw [hleft,hright]
    exact hjS s hs

end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Filter Finset Topology
open scoped Classical

private theorem floor_cutoff_bounds {x C : ℝ} (hx : (2:ℝ)^200 ≤ x)
    (hC : x^(203/1000:ℝ) ≤ C) (hC' : C ≤ x^(41/200:ℝ)) :
    x^(203/1000:ℝ) ≤ 2*(⌊C⌋₊:ℝ) ∧
      x^(1/5:ℝ) ≤ (⌊C⌋₊:ℝ) ∧ (⌊C⌋₊:ℝ) ≤ x^(41/200:ℝ) ∧
      C/2 ≤ (⌊C⌋₊:ℝ) ∧ (⌊C⌋₊:ℝ) ≤ C := by
  have hx₁ : 1 < x := (by norm_num : (1:ℝ) < 2^200).trans_le hx
  have hx₀ := zero_lt_one.trans hx₁
  have hpow (a : ℝ) (ha : 0 ≤ a) : (2:ℝ)^(((200:ℕ):ℝ)*a) ≤ x^a := by
    rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
    exact Real.rpow_le_rpow (by positivity) hx ha
  have h₄ : (4:ℝ) ≤ x^(1/5:ℝ) := by
    apply le_trans _ (hpow (1/5) (by norm_num))
    rw [show ((200:ℕ):ℝ)*(1/5)=((40:ℕ):ℝ) by norm_num,Real.rpow_natCast]
    norm_num
  have hshift : (5/4:ℝ) ≤ x^(3/1000:ℝ) := calc
    _ ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    _ = (2:ℝ)^((200:ℝ)*(1/400)) := by rw [Real.sqrt_eq_rpow]; norm_num
    _ ≤ x^(1/400:ℝ) := hpow _ (by norm_num)
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx₁.le (by norm_num)
  have hgap : x^(1/5:ℝ)+1 ≤ x^(203/1000:ℝ) := calc
    _ ≤ x^(1/5:ℝ)*(5/4) := by linarith only [h₄]
    _ ≤ x^(1/5:ℝ)*x^(3/1000:ℝ) := mul_le_mul_of_nonneg_left hshift (by positivity)
    _ = _ := by rw [← Real.rpow_add hx₀]; norm_num
  have hCe : 2 ≤ C := by linarith only [h₄,hgap,hC]
  have hfloor := Nat.lt_floor_add_one C
  have hfloor' := Nat.floor_le (show 0 ≤ C by linarith only [hCe])
  have hhalf : C/2 ≤ (⌊C⌋₊:ℝ) := by linarith only [hfloor,hCe]
  refine ⟨hC.trans ?_,?_,hfloor'.trans hC',hhalf,hfloor'⟩
  · linarith only [hhalf]
  · linarith only [hgap,hC,hfloor]

/-- A finite, uniformly bounded set of transition scales leaves an integer
cutoff of the prescribed size with a power-sized multiplicative gap. -/
theorem exists_adaptive_integer_cutoff (S : ℕ → Finset ℝ) (N : ℕ)
    (hN : ∀ᶠ X : ℕ in atTop, (S X).card ≤ N) :
    ∃ (η : ℝ) (P : ℕ → ℕ), 0 < η ∧
      (∀ X : ℕ, 2^200 ≤ 4*X →
        ((4*X:ℕ):ℝ)^(203/1000:ℝ) ≤ 2*(P X:ℝ) ∧
          ((4*X:ℕ):ℝ)^(1/5:ℝ) ≤ (P X:ℝ) ∧
            (P X:ℝ) ≤ ((4*X:ℕ):ℝ)^(41/200:ℝ)) ∧
      ∀ᶠ X : ℕ in atTop, ∀ t ∈ S X,
        t < (P X:ℝ)/(X:ℝ)^η ∨ (P X:ℝ)*(X:ℝ)^η < t := by
  let A (X : ℕ) := ((4*X:ℕ):ℝ)
  let κ : ℝ := (1/500)/((3*N+1:ℕ):ℝ)
  let η : ℝ := κ/2
  have hden : 0 < ((3*N+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos (3*N)
  have hκ : 0 < κ := div_pos (by norm_num) hden
  have hη : 0 < η := half_pos hκ
  have hA (X : ℕ) (hX : 2^200 ≤ 4*X) : (2:ℝ)^200 ≤ A X := by
    dsimp only [A]
    exact_mod_cast hX
  have hA₁ (X : ℕ) (hX : 2^200 ≤ 4*X) : 1 < A X :=
    (by norm_num : (1:ℝ) < 2^200).trans_le (hA X hX)
  have hCenter (X : ℕ) (hX : 2^200 ≤ 4*X) (hcard : (S X).card ≤ N) :
      ∃ C : ℝ, (A X)^(203/1000:ℝ) ≤ C ∧ C ≤ (A X)^(41/200:ℝ) ∧
        ∀ t ∈ S X, t < C/(A X)^κ ∨ C*(A X)^κ < t := by
    have hX₀ : 0 < A X := zero_lt_one.trans (hA₁ X hX)
    obtain ⟨C,hC₁,hC₂,hSep⟩ := exists_separated_center (S X)
      (Real.rpow_pos_of_pos hX₀ (203/1000)) (Real.one_lt_rpow (hA₁ X hX) hκ)
    refine ⟨C,hC₁,hC₂.trans ?_,hSep⟩
    have hpow : κ*((3*(S X).card+1:ℕ):ℝ) ≤ 1/500 := calc
      _ ≤ κ*((3*N+1:ℕ):ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hκ.le
        exact_mod_cast (show 3*(S X).card+1 ≤ 3*N+1 by omega)
      _ = _ := by dsimp only [κ]; field_simp
    have hB : ((A X)^κ)^(3*(S X).card+1) ≤ (A X)^(1/500:ℝ) := by
      rw [← Real.rpow_natCast ((A X)^κ),← Real.rpow_mul hX₀.le]
      exact Real.rpow_le_rpow_of_exponent_le (hA₁ X hX).le hpow
    calc
      _ ≤ (A X)^(203/1000:ℝ)*(A X)^(1/500:ℝ) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by rw [← Real.rpow_add hX₀]; norm_num
  let C (X : ℕ) : ℝ :=
    if h : 2^200 ≤ 4*X ∧ (S X).card ≤ N then (hCenter X h.1 h.2).choose
    else (A X)^(41/200:ℝ)
  let P (X : ℕ) : ℕ := ⌊C X⌋₊
  have hBounds (X : ℕ) (hX : 2^200 ≤ 4*X) :
      (A X)^(203/1000:ℝ) ≤ C X ∧ C X ≤ (A X)^(41/200:ℝ) := by
    dsimp only [C]
    split_ifs with h
    · exact ⟨(hCenter X h.1 h.2).choose_spec.1,(hCenter X h.1 h.2).choose_spec.2.1⟩
    · exact ⟨Real.rpow_le_rpow_of_exponent_le (hA₁ X hX).le (by norm_num),le_rfl⟩
  have hFloor (X : ℕ) (hX : 2^200 ≤ 4*X) :=
    floor_cutoff_bounds (hA X hX) (hBounds X hX).1 (hBounds X hX).2
  refine ⟨η,P,hη,fun X hX => ⟨(hFloor X hX).1,(hFloor X hX).2.1,(hFloor X hX).2.2.1⟩,?_⟩
  have hlim : Tendsto (fun X : ℕ => (X:ℝ)^η) atTop atTop := by
    change Tendsto ((fun x : ℝ => x^η) ∘ (fun X : ℕ => (X:ℝ))) atTop atTop
    exact (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  have hExp : ∀ᶠ X : ℕ in atTop, 2 ≤ (X:ℝ)^η := (tendsto_atTop.1 hlim) 2
  filter_upwards [hN,eventually_ge_atTop (2^200:ℕ),hExp] with X hcard hX hE
  have hX' : 2^200 ≤ 4*X := by omega
  have hG : 2^200 ≤ 4*X ∧ (S X).card ≤ N := ⟨hX',hcard⟩
  have hX₀ : 0 < (X:ℝ) := by
    exact_mod_cast (show 0 < X from (by norm_num : 0 < (2^200:ℕ)).trans_le hX)
  have hXη : 0 < (X:ℝ)^η := Real.rpow_pos_of_pos hX₀ η
  have hXC : (X:ℝ) ≤ A X := by
    dsimp only [A]
    exact_mod_cast (show X ≤ 4*X by omega)
  have hB₂ : 2*(X:ℝ)^η ≤ (A X)^κ := calc
    _ ≤ (X:ℝ)^η*(X:ℝ)^η := mul_le_mul_of_nonneg_right hE hXη.le
    _ = (X:ℝ)^κ := by
      rw [← Real.rpow_add hX₀,show η+η=κ by dsimp [η]; ring]
    _ ≤ _ := Real.rpow_le_rpow hX₀.le hXC hκ.le
  have hC₀ : 0 < C X := (by positivity : 0 < (A X)^(203/1000:ℝ)).trans_le (hBounds X hX').1
  have hSep : ∀ t ∈ S X, t < (C X)/(A X)^κ ∨ (C X)*(A X)^κ < t := by
    dsimp only [C]
    rw [dite_eq_left hG]
    exact (hCenter X hG.1 hG.2).choose_spec.2.2
  have hleft : (C X)/(A X)^κ ≤ (P X:ℝ)/(X:ℝ)^η := calc
    _ ≤ (C X)/(2*(X:ℝ)^η) :=
      div_le_div_of_nonneg_left hC₀.le (by positivity) hB₂
    _ = ((C X)/2)/(X:ℝ)^η := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (hFloor X hX').2.2.2.1 hXη.le
  have hright : (P X:ℝ)*(X:ℝ)^η ≤ (C X)*(A X)^κ := by
    apply mul_le_mul (hFloor X hX').2.2.2.2 _ hXη.le hC₀.le
    linarith only [hB₂,hXη.le]
  intro t ht
  exact (hSep t ht).imp (fun h => h.trans_le hleft) (fun h => hright.trans_lt h)

end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset Filter Complex Goldbach GoldbachTwistedMellin DirichletCharacter
open GoldbachWeightedMajorResidual GoldbachSpectralGeometry GoldbachLowZeroGapEnergy
open GoldbachWeightedException (cutoff)
open scoped Classical

noncomputable section

def shortZerosAtCutoff (X P r : ℕ) (χ : DirichletCharacter ℂ r) : Finset ℂ :=
  if hr : r ≠ 0 then
    let _ : NeZero r := ⟨hr⟩
    (exceptionalZeros χ (heightCut (X:ℝ))).filter
      (fun z => |z.im| < shortHeight (X:ℝ) (P:ℝ) r ∧ 1-farGap (X:ℝ) < z.re)
  else ∅

def globalModesAtCutoff (X P : ℕ) : Finset GlobalMode :=
  ((Icc 1 P).sigma (fun r =>
    (((Finset.univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive)).sigma
      (shortZerosAtCutoff X P r)).image (fun p => (p.1,p.2)))).insertNone

private theorem globalShortZeros_eq_atCutoff (X r : ℕ) (χ : DirichletCharacter ℂ r) :
    globalShortZeros X r χ = shortZerosAtCutoff X (cutoff X) r χ := by
  by_cases hr : r ≠ 0
  · ext z
    simp only [globalShortZeros,shortZerosAtCutoff,dite_eq_left hr,Finset.mem_filter,shortNearZero]
  · simp [globalShortZeros,shortZerosAtCutoff,hr]

theorem globalModesAt_eq_atCutoff (X : ℕ) : globalModesAt X = globalModesAtCutoff X (cutoff X) := by
  unfold globalModesAt globalModesAtCutoff
  have h : ∀ r, globalShortZeros X r = shortZerosAtCutoff X (cutoff X) r :=
    fun r => funext (globalShortZeros_eq_atCutoff X r)
  simp_rw [h]

theorem shortZerosAtCutoff_subset {X P Q r : ℕ} (h : P ≤ Q) (χ : DirichletCharacter ℂ r) :
    shortZerosAtCutoff X P r χ ⊆ shortZerosAtCutoff X Q r χ := by
  by_cases hr : r ≠ 0
  · intro z hz
    simp only [shortZerosAtCutoff,dite_eq_left hr,mem_filter] at hz ⊢
    have hHeight : shortHeight (X:ℝ) (P:ℝ) r ≤ shortHeight (X:ℝ) (Q:ℝ) r := by
      unfold shortHeight
      gcongr
    exact ⟨hz.1,hz.2.1.trans_le hHeight,hz.2.2⟩
  · simp [shortZerosAtCutoff,hr]

theorem globalModesAtCutoff_subset {X P Q : ℕ} (h : P ≤ Q) :
    globalModesAtCutoff X P ⊆ globalModesAtCutoff X Q := by
  intro i hi
  rcases i with _ | ⟨r,χ,z⟩
  · simp [globalModesAtCutoff]
  simp only [globalModesAtCutoff,some_mem_insertNone,mem_sigma,mem_Icc,mem_image,
    mem_filter,mem_univ,true_and] at hi ⊢
  obtain ⟨⟨hr,hP⟩,⟨⟨ψ,w⟩,⟨hψ,hw⟩,he⟩⟩ := hi
  exact ⟨⟨hr,hP.trans h⟩,⟨⟨ψ,w⟩,⟨hψ,shortZerosAtCutoff_subset h ψ hw⟩,he⟩⟩

def modeTransitionScale : GlobalMode → ℝ
  | none => 1
  | some ⟨r,_,z⟩ => (r:ℝ)*(1+|z.im|)

/-- Pass from the nominal cap to all the subsets chosen with an adaptive cutoff. -/
theorem exists_adaptive_mode_cutoff {N : ℕ} (L : ℝ)
    (hN : ∀ᶠ X : ℕ in atTop,
      ((globalModesAtCutoff X ⌊((4*X:ℕ):ℝ)^(41/200:ℝ)⌋₊).filter
        (fun i => modeGap X i ≤ L)).card ≤ N) :
    ∃ (η : ℝ) (P : ℕ → ℕ), 0 < η ∧
      (∀ X : ℕ, 2^200 ≤ 4*X →
        ((4*X:ℕ):ℝ)^(203/1000:ℝ) ≤ 2*(P X:ℝ) ∧
          ((4*X:ℕ):ℝ)^(1/5:ℝ) ≤ (P X:ℝ) ∧
            (P X:ℝ) ≤ ((4*X:ℕ):ℝ)^(41/200:ℝ)) ∧
      ∀ᶠ X : ℕ in atTop, ∀ i ∈ globalModesAtCutoff X (P X), modeGap X i ≤ L →
        modeTransitionScale i < (P X:ℝ)/(X:ℝ)^η ∨
          (P X:ℝ)*(X:ℝ)^η < modeTransitionScale i := by
  let Q (X : ℕ) : ℕ := ⌊((4*X:ℕ):ℝ)^(41/200:ℝ)⌋₊
  let S (X : ℕ) : Finset ℝ := ((globalModesAtCutoff X (Q X)).filter
    (fun i => modeGap X i ≤ L)).image modeTransitionScale
  have hS : ∀ᶠ X : ℕ in atTop, (S X).card ≤ N :=
    hN.mono (fun X h => Finset.card_image_le.trans h)
  obtain ⟨η,P,hη,hP,hSeparation⟩ := exists_adaptive_integer_cutoff S N hS
  refine ⟨η,P,hη,hP,?_⟩
  filter_upwards [hSeparation,eventually_ge_atTop (2^200:ℕ)] with X hsep hX i hi hcap
  have hP' : P X ≤ Q X := Nat.le_floor (hP X (by omega)).2.2
  exact hsep (modeTransitionScale i) (mem_image.mpr
    ⟨i,mem_filter.mpr ⟨globalModesAtCutoff_subset hP' hi,hcap⟩,rfl⟩)

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset Filter Complex GoldbachWeightedMajorResidual
open GoldbachWeightedException (cutoff)
open scoped Classical

noncomputable section

def cappedGlobalModes (X : ℕ) (L : ℝ) : Finset GlobalMode :=
  (globalModesAt X).filter (fun i => modeGap X i ≤ L)

def cappedSmoothCoefficient (X m : ℕ) (L : ℝ) : ℂ :=
  ∑ i ∈ cappedGlobalModes X L, ∑ j ∈ cappedGlobalModes X L, ∑ q ∈ Icc 1 (cutoff X),
    globalPairCoefficient m q i j*pairIntegral (arcRadius X q) m (smoothGlobalProfile X) i j

theorem eventually_capped_mode_card_bounded (L : ℝ) :
    ∃ N : ℕ, ∀ᶠ X : ℕ in atTop, (cappedGlobalModes X L).card ≤ N := by
  obtain ⟨A,_,hA⟩ := short_global_mass_and_tail
  refine ⟨⌈A*Real.exp L⌉₊,hA.mono ?_⟩
  intro X hX
  exact_mod_cast (capped_mode_card_le hX.1 L).trans (Nat.le_ceil (A*Real.exp L))

private theorem shortSmooth_sub_capped_eq_tail (X m : ℕ) (L : ℝ) :
    shortSmoothCoefficient X m-cappedSmoothCoefficient X m L =
      ∑ p ∈ pairTail (globalModesAt X) (fun i => modeGap X i ≤ L),
        ∑ q ∈ Icc 1 (cutoff X),
          globalPairCoefficient m q p.1 p.2*pairIntegral (arcRadius X q) m (smoothGlobalProfile X) p.1 p.2 := by
  let S := globalModesAt X
  let F (p : GlobalMode × GlobalMode) :=
    ∑ q ∈ Icc 1 (cutoff X),
      globalPairCoefficient m q p.1 p.2*pairIntegral (arcRadius X q) m (smoothGlobalProfile X) p.1 p.2
  let g (i : GlobalMode) := modeGap X i ≤ L
  have hS : cappedGlobalModes X L = S.filter g := rfl
  unfold shortSmoothCoefficient cappedSmoothCoefficient pairTail
  change (∑ i ∈ S, ∑ j ∈ S,F (i,j)) -
    (∑ i ∈ cappedGlobalModes X L, ∑ j ∈ cappedGlobalModes X L,F (i,j)) =
      ∑ p ∈ (S ×ˢ S).filter (fun p => ¬(g p.1 ∧ g p.2)), F p
  rw [← sum_product,← sum_product,hS,← filter_product g g]
  apply sub_eq_iff_eq_add.mpr
  simpa only [add_comm] using (sum_filter_add_sum_filter_not (s:=S ×ˢ S) (fun p => g p.1 ∧ g p.2) F).symm

theorem norm_shortSmooth_sub_capped_le_mass {X m : ℕ}
    (hX : 0 < X) (L : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hC : ∀ i ∈ globalModesAt X, ∀ j ∈ globalModesAt X,
      (∑ d ∈ Icc 1 (cutoff X), ‖globalPairCoefficient m d i j‖) ≤ B) :
    ‖shortSmoothCoefficient X m-cappedSmoothCoefficient X m L‖ ≤
      2*(X:ℝ)*B*(∑ i ∈ globalModesAt X,modeMass X i)*
        (∑ i ∈ (globalModesAt X).filter (fun i => ¬(modeGap X i ≤ L)),modeMass X i) := by
  rw [shortSmooth_sub_capped_eq_tail]
  exact norm_pairTail_le (globalModesAt X) (Icc 1 (cutoff X)) (fun i => modeGap X i ≤ L)
    (modeMass X) (globalPairCoefficient m)
    (fun q i j => pairIntegral (arcRadius X q) m (smoothGlobalProfile X) i j)
    (fun i _=>modeMass_nonneg X i) (Nat.cast_nonneg X) hB hC
    (fun q _ i hi j hj => norm_smooth_pairIntegral_le (m:=m) hX hi hj (arcRadius X q))

def goodArithmeticPair (K H m : ℕ) (i j : GlobalMode) : Prop :=
  globalPairConductor i j ≤ K ∧ (globalLevel i).lcm (globalLevel j) ∣ H*m

def supportedSmoothCoefficient (X m : ℕ) (L : ℝ) (K H : ℕ) : ℂ :=
  ∑ p ∈ ((cappedGlobalModes X L) ×ˢ (cappedGlobalModes X L)).filter
    (fun p => goodArithmeticPair K H m p.1 p.2),
      ∑ q ∈ Icc 1 (cutoff X), globalPairCoefficient m q p.1 p.2*
        pairIntegral (arcRadius X q) m (smoothGlobalProfile X) p.1 p.2

set_option maxHeartbeats 1900000 in
theorem eventually_norm_capped_sub_supported_le {ε : ℝ} (hε : 0 < ε) (L : ℝ) :
    ∃ K H : ℕ, 0 < K ∧ 0 < H ∧ ∀ᶠ X : ℕ in atTop, ∀ m : ℕ, 0 < m → Even m →
      ‖cappedSmoothCoefficient X m L-supportedSmoothCoefficient X m L K H‖ ≤
        ε*(X:ℝ)*globalOrdinarySingularSeries m := by
  obtain ⟨A,hA,hM⟩ := short_global_mass_and_tail
  obtain ⟨c,hc,hS⟩ := globalOrdinarySingularSeries_pos_uniform
  let η := ε/A^2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K,H,hK,hH,hC⟩ := globalPairCoefficient_off_support hη
  refine ⟨K,H,hK,hH,?_⟩
  filter_upwards [hM,eventually_ge_atTop (1:ℕ)] with X hX hX1 m hm hEven
  let S := cappedGlobalModes X L
  let Q := Icc 1 (cutoff X)
  let g (p : GlobalMode × GlobalMode) := goodArithmeticPair K H m p.1 p.2
  let F (p : GlobalMode × GlobalMode) := ∑ q ∈ Q, globalPairCoefficient m q p.1 p.2*
    pairIntegral (arcRadius X q) m (smoothGlobalProfile X) p.1 p.2
  let M (i : GlobalMode) := modeMass X i
  have hp : 0 < X := hX1
  have hSing : 0 ≤ globalOrdinarySingularSeries m := (hc.trans (hS m hm hEven)).le
  have heq : cappedSmoothCoefficient X m L-supportedSmoothCoefficient X m L K H =
      ∑ p ∈ (S ×ˢ S).filter (fun p => ¬g p),F p := by
    unfold cappedSmoothCoefficient supportedSmoothCoefficient
    change (∑ i ∈ S,∑ j ∈ S,F (i,j)) - (∑ p ∈ (S ×ˢ S).filter g,F p) = _
    rw [← sum_product]
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using (sum_filter_add_sum_filter_not (s:=S ×ˢ S) g F).symm
  have hPt (p : GlobalMode × GlobalMode) (hmem : p ∈ (S ×ˢ S).filter (fun p => ¬g p)) :
      ‖F p‖ ≤ η*(X:ℝ)*globalOrdinarySingularSeries m*(M p.1*M p.2) := by
    obtain ⟨hpS,hgood⟩ := mem_filter.mp hmem
    obtain ⟨hi,hj⟩ := mem_product.mp hpS
    have hi' := (mem_filter.mp hi).1
    have hj' := (mem_filter.mp hj).1
    have hb := hC hm hEven hi' hj' hgood Q
    unfold F
    calc
      _ ≤ ∑ q ∈ Q, ‖globalPairCoefficient m q p.1 p.2 *
          pairIntegral (arcRadius X q) m (smoothGlobalProfile X) p.1 p.2‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Q, ‖globalPairCoefficient m q p.1 p.2‖ * ((X:ℝ)*M p.1*M p.2) := by
        apply sum_le_sum
        intro q _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (norm_smooth_pairIntegral_le (m:=m) hp hi' hj' (arcRadius X q)) (norm_nonneg _)
      _ = (∑ q ∈ Q, ‖globalPairCoefficient m q p.1 p.2‖)*((X:ℝ)*M p.1*M p.2) := by rw [sum_mul]
      _ ≤ (η*globalOrdinarySingularSeries m)*((X:ℝ)*M p.1*M p.2) :=
        mul_le_mul_of_nonneg_right hb (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (modeMass_nonneg _ _)) (modeMass_nonneg _ _))
      _ = _ := by ring
  rw [heq]
  have hM' : 0 ≤ ∑ i ∈ S,M i := sum_nonneg (fun i _ => modeMass_nonneg _ _)
  have hM'' : ∑ i ∈ S,M i ≤ A :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => modeMass_nonneg _ _)).trans hX.1
  calc
    _ ≤ ∑ p ∈ (S ×ˢ S).filter (fun p => ¬g p), ‖F p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ (S ×ˢ S).filter (fun p => ¬g p),η*(X:ℝ)*globalOrdinarySingularSeries m*(M p.1*M p.2) := sum_le_sum hPt
    _ ≤ ∑ p ∈ S ×ˢ S,η*(X:ℝ)*globalOrdinarySingularSeries m*(M p.1*M p.2) := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro p _ _
      have h₁ := modeMass_nonneg X p.1
      have h₂ := modeMass_nonneg X p.2
      positivity
    _ = η*(X:ℝ)*globalOrdinarySingularSeries m*(∑ i ∈ S,M i)^2 := by
      rw [← mul_sum,sum_product]
      simp_rw [← mul_sum,← sum_mul]
      ring
    _ ≤ η*(X:ℝ)*globalOrdinarySingularSeries m*A^2 := by gcongr
    _ = _ := by dsimp only [η]; field_simp [hA.ne']

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset Complex Goldbach GoldbachTwistedMellin GoldbachWeightedMajorResidual Filter
open scoped Topology

theorem eventually_bounded_modes_have_large_level (K : ℕ) {L T : ℝ} (_hL : 0 ≤ L) (_hT : 0 ≤ T) :
    ∀ᶠ X : ℕ in atTop, ∀ i ∈ globalModesAt X, i ≠ none →
      modeGap X i ≤ L → |(spectralPoint i).im| ≤ T → K < globalLevel i := by
  classical
  have hf : ∀ᶠ X : ℕ in atTop, ∀ r ∈ Finset.range (K+1), ∀ hr : 0 < r,
      ∀ χ : DirichletCharacter ℂ r,
        ∀ z ∈ @exceptionalZeros r ⟨hr.ne'⟩ χ T, L < (1-z.re)*Real.log (X:ℝ) := by
    apply (eventually_all_finset _).mpr
    intro r hr
    by_cases hpos : 0 < r
    · let _ : NeZero r := ⟨hpos.ne'⟩
      suffices ∀ᶠ X : ℕ in atTop, ∀ χ : DirichletCharacter ℂ r,
          ∀ z ∈ exceptionalZeros χ T, L < (1-z.re)*Real.log (X:ℝ) by
        exact this.mono (fun X h _ => h)
      have hh : ∀ᶠ X : ℕ in atTop, ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)),
          ∀ z ∈ exceptionalZeros χ T, L < (1-z.re)*Real.log (X:ℝ) := by
        apply (eventually_all_finset _).mpr
        intro χ _
        apply (eventually_all_finset _).mpr
        intro z hz
        have hz' := ((mem_exceptionalZeros χ T z).mp hz).2.2
        have hp : 0 < 1-z.re := sub_pos.mpr
          (lt_of_not_ge (fun h => GoldbachZeroFree.regularizedL_ne_zero_ge_one χ h hz'))
        have hLog : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
          Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
        exact (hLog.eventually_gt_atTop (L/(1-z.re))).mono
          (fun X h => by rw [mul_comm]; exact (div_lt_iff₀ hp).mp h)
      exact hh.mono (fun X h χ => h χ (mem_univ χ))
    · exact Eventually.of_forall (fun _ h => False.elim (hpos h))
  filter_upwards [hf] with X hX i hi hn hGap hHeight
  rcases i with _ | ⟨r,χ,z⟩
  · exact absurd rfl hn
  change K < r
  by_contra! hK
  obtain ⟨hr,_,_,hmem⟩ := (mem_globalModesAt_zero χ z).mp hi
  let _ : NeZero r := ⟨(Nat.zero_lt_one.trans_le hr).ne'⟩
  have hmem' : z ∈ (exceptionalZeros χ (heightCut (X:ℝ))).filter (shortNearZero X r) := by
    simpa only [globalShortZeros,dite_eq_left (NeZero.ne r)] using hmem
  have hZ := ((mem_exceptionalZeros χ (heightCut (X:ℝ)) z).mp (mem_filter.mp hmem').1)
  have hT' : |z.im| ≤ T := hHeight
  have hzT := (mem_exceptionalZeros χ T z).mpr ⟨hZ.1,hT',hZ.2.2⟩
  have hh := hX r (Finset.mem_range.mpr (by omega)) (Nat.zero_lt_one.trans_le hr) χ z hzT
  exact (not_lt_of_ge hGap) hh

end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Filter Topology

noncomputable def adaptiveArcRadius (P X d : ℕ) : ℝ :=
  (P:ℝ)/((d:ℝ)*((4*X:ℕ):ℝ))

theorem adaptiveArcRadius_eq_arcRadius (X d : ℕ) :
    adaptiveArcRadius (GoldbachWeightedException.cutoff X) X d =
      GoldbachWeightedMajorResidual.arcRadius X d := rfl

theorem mul_adaptiveArcRadius {P X d : ℕ} (hX : 0 < X) (hd : 0 < d) :
    (X:ℝ)*adaptiveArcRadius P X d = (P:ℝ)/(4*(d:ℝ)) := by
  have hx : (0:ℝ)<X := by exact_mod_cast hX
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  unfold adaptiveArcRadius
  push_cast
  field_simp [hx.ne',hd'.ne']

private theorem rpow_half_sq (x : ℝ) (hx : 0 ≤ x) (η : ℝ) :
    (x^(η/2))^2 = x^η := by
  rw [← Real.rpow_natCast (x^(η/2)) 2,← Real.rpow_mul hx]
  rw [show (η/2)*((2:ℕ):ℝ)=η by push_cast; ring]

/-- A transition scale below the cutoff by the power gap has a small
ordinate on all retained denominators through the Rankin cutoff. -/
theorem adaptiveArcRadius_low {η γ : ℝ} {K P X r L d : ℕ}
    (hX : 0 < X) (hK : 0 < K) (hr : 0 < r) (hd : 0 < d)
    (hL : L ≤ K*r) (hB : 4*(K:ℝ) ≤ (X:ℝ)^(η/2))
    (hdL : (d:ℝ) ≤ (L:ℝ)*(X:ℝ)^(η/2))
    (hscale : (r:ℝ)*(1+|γ|) < (P:ℝ)/(X:ℝ)^η) :
    |γ| ≤ Real.pi*((X:ℝ)*adaptiveArcRadius P X d) ∧
      (X:ℝ)^(η/2)/(4*(K:ℝ)) ≤ (X:ℝ)*adaptiveArcRadius P X d := by
  rw [mul_adaptiveArcRadius hX hd]
  let A := (X:ℝ)^η
  let B := (X:ℝ)^(η/2)
  have hx : (0:ℝ)<X := by exact_mod_cast hX
  have hk : (0:ℝ)<K := by exact_mod_cast hK
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hA : 0 < A := Real.rpow_pos_of_pos hx _
  have hB' : 0 < B := Real.rpow_pos_of_pos hx _
  have hBA : B^2 = A := rpow_half_sq _ hx.le η
  have hdR : (d:ℝ) ≤ (K:ℝ)*(r:ℝ)*B := hdL.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast hL) hB'.le)
  have hden : 4*(d:ℝ) ≤ (r:ℝ)*A := calc
    _ ≤ 4*((K:ℝ)*(r:ℝ)*B) := mul_le_mul_of_nonneg_left hdR (by norm_num)
    _ = (4*(K:ℝ))*(r:ℝ)*B := by ring
    _ ≤ B*(r:ℝ)*B := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB hr'.le) hB'.le
    _ = (r:ℝ)*A := by rw [← hBA]; ring
  have hmul : ((r:ℝ)*(1+|γ|))*A < P := (lt_div_iff₀ hA).1 hscale
  have hPA : (r:ℝ)*A < P := calc
    _ ≤ ((r:ℝ)*(1+|γ|))*A := by nlinarith [mul_nonneg hr'.le (mul_nonneg hA.le (abs_nonneg γ))]
    _ < _ := hmul
  have hR : 0 ≤ (P:ℝ)/(4*(d:ℝ)) := by positivity
  have hγ : |γ| < (P:ℝ)/(4*(d:ℝ)) := by
    apply (lt_div_iff₀ (by positivity : 0 < 4*(d:ℝ))).2
    calc
      _ ≤ |γ| *((r:ℝ)*A) := mul_le_mul_of_nonneg_left hden (abs_nonneg _)
      _ ≤ ((r:ℝ)*(1+|γ|))*A := by nlinarith [mul_nonneg hr'.le hA.le]
      _ < _ := hmul
  refine ⟨hγ.le.trans (le_mul_of_one_le_left hR (by linarith [Real.pi_gt_three])),?_⟩
  apply (le_div_iff₀ (by positivity : 0 < 4*(d:ℝ))).2
  calc
    _ ≤ (B/(4*(K:ℝ)))*(4*((K:ℝ)*(r:ℝ)*B)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdR (by norm_num)) (by positivity)
    _ = (r:ℝ)*B^2 := by field_simp [hk.ne'] <;> ring
    _ ≤ _ := by rw [hBA]; exact hPA.le

/-- At the upper transition scale the ordinate dominates both the power
scale and the radius at every positive multiple of the source level. -/
theorem adaptiveArcRadius_high {η γ : ℝ} {P X r d : ℕ}
    (hX : 0 < X) (hr : 0 < r) (hd : 0 < d) (hrP : r ≤ P) (hrd : r ∣ d)
    (hA : 2 ≤ (X:ℝ)^η)
    (hscale : (P:ℝ)*(X:ℝ)^η < (r:ℝ)*(1+|γ|)) :
    (X:ℝ)^η/2 < |γ| ∧
      2*(X:ℝ)^η*((X:ℝ)*adaptiveArcRadius P X d) < |γ| := by
  rw [mul_adaptiveArcRadius hX hd]
  let A := (X:ℝ)^η
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hrP' : (r:ℝ) ≤ P := by exact_mod_cast hrP
  have hrd' : (r:ℝ) ≤ d := by exact_mod_cast Nat.le_of_dvd hd hrd
  have hA' : 0 ≤ A := zero_le_two.trans hA
  have hsmall : (r:ℝ)*A < (r:ℝ)*(1+|γ|) :=
    (mul_le_mul_of_nonneg_right hrP' hA').trans_lt hscale
  have hsmall' : A < 1+|γ| := (mul_lt_mul_iff_of_pos_left hr').1 hsmall
  have hγ : 1 ≤ |γ| := by linarith only [hA,hsmall']
  have hmain : (P:ℝ)*A < (2*(r:ℝ))*|γ| := by
    exact hscale.trans_le ((mul_le_mul_of_nonneg_left
      (show 1+|γ| ≤ 2*|γ| by linarith only [hγ]) hr'.le).trans_eq (by ring))
  refine ⟨by linarith only [hA,hsmall'],?_⟩
  calc
    _ = ((P:ℝ)*A)/(2*(d:ℝ)) := by field_simp [hd'.ne'] <;> ring
    _ ≤ ((P:ℝ)*A)/(2*(r:ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hrd' (by norm_num))
    _ < _ := (div_lt_iff₀ (by positivity)).2 (by convert hmain using 1 <;> ring)

private theorem eventually_nat_rpow_ge {η : ℝ} (hη : 0 < η) (C : ℝ) :
    ∀ᶠ X : ℕ in atTop, C ≤ (X:ℝ)^η := by
  have hlim : Tendsto (fun X : ℕ => (X:ℝ)^η) atTop atTop := by
    change Tendsto ((fun x : ℝ => x^η) ∘ (fun X : ℕ => (X:ℝ))) atTop atTop
    exact (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  exact (tendsto_atTop.1 hlim) C

theorem eventually_adaptiveArcRadius_low {η : ℝ} (hη : 0 < η) {K : ℕ} (hK : 0 < K) :
    ∀ᶠ X : ℕ in atTop, ∀ {P r L d : ℕ} {γ : ℝ}, 0 < r → 0 < d →
      L ≤ K*r → (d:ℝ) ≤ (L:ℝ)*(X:ℝ)^(η/2) →
      (r:ℝ)*(1+|γ|) < (P:ℝ)/(X:ℝ)^η →
      |γ| ≤ Real.pi*((X:ℝ)*adaptiveArcRadius P X d) ∧
        (X:ℝ)^(η/2)/(4*(K:ℝ)) ≤ (X:ℝ)*adaptiveArcRadius P X d := by
  filter_upwards [eventually_ge_atTop (1:ℕ),eventually_nat_rpow_ge (half_pos hη) (4*(K:ℝ))]
    with X hX hB
  intro P r L d γ hr hd hL hdL hscale
  exact adaptiveArcRadius_low hX hK hr hd hL hB hdL hscale

/-- The low-radius estimate for either source of a global pair with bounded
product conductor. -/
theorem eventually_globalPair_adaptiveArcRadius_low {η : ℝ} (hη : 0 < η) {K : ℕ} (hK : 0 < K) :
    ∀ᶠ X : ℕ in atTop, ∀ {P d r : ℕ} {i j : GlobalMode} {γ : ℝ},
      i ∈ globalModesAt X → j ∈ globalModesAt X → globalPairConductor i j ≤ K →
      (r=globalLevel i ∨ r=globalLevel j) → 0 < d →
      (d:ℝ) ≤ ((globalLevel i).lcm (globalLevel j):ℝ)*(X:ℝ)^(η/2) →
      (r:ℝ)*(1+|γ|) < (P:ℝ)/(X:ℝ)^η →
      |γ| ≤ Real.pi*((X:ℝ)*adaptiveArcRadius P X d) ∧
        (X:ℝ)^(η/2)/(4*(K:ℝ)) ≤ (X:ℝ)*adaptiveArcRadius P X d := by
  filter_upwards [eventually_adaptiveArcRadius_low hη hK] with X hX
  intro P d r i j γ hi hj hc hr hd hdL hscale
  obtain ⟨hLi,hLj⟩ := globalPair_lcm_le_of_conductor_le hi hj hc
  rcases hr with rfl|rfl
  · exact hX (globalLevel_pos hi) hd hLi hdL hscale
  · exact hX (globalLevel_pos hj) hd hLj hdL hscale

end GoldbachSignedPairs


end

section

namespace GoldbachSignedPairs

open Finset Filter Topology DirichletCharacter
open Conjectures.Goldbach.TwistedGoldbachSingularSeries
open scoped Classical BigOperators

theorem summable_norm_globalPairCoefficient {X m : ℕ} {i j : GlobalMode}
    (hi : i ∈ globalModesAt X) (hj : j ∈ globalModesAt X) (hm : 0 < m) :
    Summable (fun d : ℕ => ‖globalPairCoefficient m d i j‖) := by
  let : NeZero (globalLevel i) := ⟨(globalLevel_pos hi).ne'⟩
  let : NeZero (globalLevel j) := ⟨(globalLevel_pos hj).ne'⟩
  simpa only [globalPairCoefficient_eq_coefficient] using
    summable_coefficients (globalSourceCharacter i)⁻¹ (globalSourceCharacter j)⁻¹ m hm

/-- Global pair coefficients beyond their common level times the adaptive
power scale have a uniform power saving relative to the signed main series. -/
theorem globalPairCoefficient_absolute_tail_finite {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X m : ℕ}, 0 < m → m ≤ 4*X → Even m → ∀ {i j : GlobalMode},
        i ∈ globalModesAt X → j ∈ globalModesAt X → ∀ D : Finset ℕ,
        let L := (globalLevel i).lcm (globalLevel j)
        (∑ d ∈ D.filter (fun d : ℕ => (L:ℝ)*(X:ℝ)^(η/2) < (d:ℝ)),
          ‖globalPairCoefficient m d i j‖) ≤
          C*globalOrdinarySingularSeries m*(X:ℝ)^(-(η/16)) := by
  let ε := η/16
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨B,hB,hMain⟩ := fixed_pair_absolute_tail_finite hε
  obtain ⟨A,hA,hOrd⟩ := globalPairCoefficient_absolute_le
  refine ⟨B*A*(4:ℝ)^ε,by positivity,?_⟩
  intro X m hm hmX he i j hi hj D
  let L := (globalLevel i).lcm (globalLevel j)
  let T := (L:ℝ)*(X:ℝ)^(η/2)
  have hX : 0 < (X:ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hmR : (m:ℝ) ≤ 4*(X:ℝ) := by exact_mod_cast hmX
  have hL : 0 < (L:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero (globalLevel_pos hi).ne' (globalLevel_pos hj).ne')
  have hT : 0 < T := mul_pos hL (Real.rpow_pos_of_pos hX _)
  let : NeZero (globalLevel i) := ⟨(globalLevel_pos hi).ne'⟩
  let : NeZero (globalLevel j) := ⟨(globalLevel_pos hj).ne'⟩
  have habs : ‖globalPairCoefficient m L i j‖ ≤ A*globalOrdinarySingularSeries m := by
    simpa only [sum_singleton] using hOrd hm he hi hj {L}
  have hS : 0 ≤ globalOrdinarySingularSeries m :=
    nonneg_of_mul_nonneg_right ((norm_nonneg _).trans habs) hA
  have htail := hMain (globalSourceCharacter i)⁻¹ (globalSourceCharacter j)⁻¹
    (globalSourceCharacter_isPrimitive hi).inv (globalSourceCharacter_isPrimitive hj).inv m hm T hT D
  have htail' :
      (∑ d ∈ D.filter (fun d : ℕ => T < (d:ℝ)), ‖globalPairCoefficient m d i j‖) ≤
        (‖globalPairCoefficient m L i j‖*(L:ℝ)^(1/4:ℝ))*(B*(m:ℝ)^ε*T^(-1/4:ℝ)) := by
    simpa only [globalPairCoefficient_eq_coefficient] using htail
  have hscale : (L:ℝ)^(1/4:ℝ)*T^(-1/4:ℝ) = (X:ℝ)^(-(η/8)) := by
    dsimp only [T]
    rw [Real.mul_rpow hL.le (by positivity),← Real.rpow_mul hX.le,← mul_assoc,
      ← Real.rpow_add hL,show (1/4:ℝ)+(-1/4)=0 by norm_num,Real.rpow_zero,one_mul]
    rw [show (η/2)*(-1/4)=-(η/8) by ring]
  change (∑ d ∈ D.filter (fun d : ℕ => T < (d:ℝ)), ‖globalPairCoefficient m d i j‖) ≤ _
  calc
    _ ≤ (‖globalPairCoefficient m L i j‖*(L:ℝ)^(1/4:ℝ))*(B*(m:ℝ)^ε*T^(-1/4:ℝ)) := htail'
    _ = (B*‖globalPairCoefficient m L i j‖)*((m:ℝ)^ε*(X:ℝ)^(-(η/8))) := by
      rw [← hscale]
      ring
    _ ≤ (B*(A*globalOrdinarySingularSeries m))*((m:ℝ)^ε*(X:ℝ)^(-(η/8))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs hB.le) (by positivity)
    _ ≤ (B*(A*globalOrdinarySingularSeries m))*((4*(X:ℝ))^ε*(X:ℝ)^(-(η/8))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (Nat.cast_nonneg m) hmR hε.le) (by positivity)) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4) hX.le]
      calc
        _ = (B*A*(4:ℝ)^ε)*globalOrdinarySingularSeries m*((X:ℝ)^ε*(X:ℝ)^(-(η/8))) := by ring
        _ = _ := by
          rw [← Real.rpow_add hX,show ε+(-(η/8))=-(η/16) by dsimp [ε]; ring]

/-- The same global tail estimate holds for the infinite sum and any
additional restriction on denominators. -/
theorem globalPairCoefficient_absolute_tail {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X m : ℕ}, 0 < m → m ≤ 4*X → Even m → ∀ {i j : GlobalMode},
        i ∈ globalModesAt X → j ∈ globalModesAt X → ∀ keep : ℕ → Prop,
        let L := (globalLevel i).lcm (globalLevel j)
        (∑' d : ℕ, if (L:ℝ)*(X:ℝ)^(η/2) < (d:ℝ) ∧ keep d
          then ‖globalPairCoefficient m d i j‖ else 0) ≤
          C*globalOrdinarySingularSeries m*(X:ℝ)^(-(η/16)) := by
  obtain ⟨C,hC,h⟩ := globalPairCoefficient_absolute_tail_finite hη
  refine ⟨C,hC,?_⟩
  intro X m hm hmX he i j hi hj keep
  let L := (globalLevel i).lcm (globalLevel j)
  let T := (L:ℝ)*(X:ℝ)^(η/2)
  let f (d : ℕ) := if T < (d:ℝ) ∧ keep d then ‖globalPairCoefficient m d i j‖ else 0
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) (summable_norm_globalPairCoefficient hi hj hm)
    · dsimp [f]
      split_ifs <;> positivity
    · dsimp [f]
      split_ifs <;> first | exact le_rfl | exact norm_nonneg _
  apply le_of_tendsto hf.hasSum
  filter_upwards with D
  rw [show (∑ d ∈ D, f d) = ∑ d ∈ (D.filter keep).filter (fun d : ℕ => T < (d:ℝ)),
    ‖globalPairCoefficient m d i j‖ by simp only [filter_filter,sum_filter,f,and_comm]]
  exact h hm hmX he hi hj (D.filter keep)

end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Set

noncomputable section

def convolutionPhase (m γ τ x : ℝ) : ℝ := γ*Real.log x + τ*Real.log (m-x)

def convolutionPhaseDeriv (m γ τ x : ℝ) : ℝ := γ/x-τ/(m-x)

def convolutionPhaseSecond (m γ τ x : ℝ) : ℝ := -γ/x^2-τ/(m-x)^2

theorem convolutionPhase_hasDerivAt {m γ τ x : ℝ} (hx : 0 < x) (hy : 0 < m-x) :
    HasDerivAt (convolutionPhase m γ τ) (convolutionPhaseDeriv m γ τ x) x := by
  have hm := (hasDerivAt_const x m).sub (hasDerivAt_id x)
  have h := ((Real.hasDerivAt_log hx.ne').const_mul γ).add
    (((Real.hasDerivAt_log hy.ne').comp x hm).const_mul τ)
  convert h using 1 <;> try rfl
  simp [convolutionPhaseDeriv, div_eq_mul_inv]
  ring

theorem convolutionPhaseDeriv_hasDerivAt {m γ τ x : ℝ} (hx : 0 < x) (hy : 0 < m-x) :
    HasDerivAt (convolutionPhaseDeriv m γ τ) (convolutionPhaseSecond m γ τ x) x := by
  have hm := (hasDerivAt_const x m).sub (hasDerivAt_id x)
  have h := ((hasDerivAt_const x γ).div (hasDerivAt_id x) hx.ne').sub
    ((hasDerivAt_const x τ).div hm hy.ne')
  convert h using 1 <;> try rfl
  simp [convolutionPhaseSecond]

theorem convolutionPhaseSecond_continuousOn {m γ τ : ℝ} {S : Set ℝ}
    (hx : ∀ x ∈ S, 0 < x) (hy : ∀ x ∈ S, 0 < m-x) :
    ContinuousOn (convolutionPhaseSecond m γ τ) S := by
  unfold convolutionPhaseSecond
  apply ContinuousOn.sub
  · exact continuousOn_const.div
      (show ContinuousOn (fun t : ℝ => t^2) S from continuousOn_id.pow 2)
      (fun x h => pow_ne_zero 2 (hx x h).ne')
  · exact continuousOn_const.div (show ContinuousOn (fun t : ℝ => (m-t)^2) S from
      (continuousOn_const.sub continuousOn_id).pow 2)
      (fun x h => pow_ne_zero 2 (hy x h).ne')

theorem convolutionPhaseSecond_abs_le {X m γ τ x : ℝ} (hX : 0 < X)
    (hx : X ≤ x) (hy : X ≤ m-x) :
    |convolutionPhaseSecond m γ τ x| ≤ (|γ|+|τ|)/X^2 := by
  have h1 : |(-γ)/x^2| ≤ |γ|/X^2 := by
    rw [abs_div, abs_neg, abs_of_nonneg (sq_nonneg x)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hX)
      (pow_le_pow_left₀ hX.le hx 2)
  have h2 : |τ/(m-x)^2| ≤ |τ|/X^2 := by
    rw [abs_div, abs_of_nonneg (sq_nonneg (m-x))]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hX)
      (pow_le_pow_left₀ hX.le hy 2)
  have htr : |convolutionPhaseSecond m γ τ x| ≤ |(-γ)/x^2|+|τ/(m-x)^2| := by
    simpa only [convolutionPhaseSecond,sub_eq_add_neg,abs_neg] using
      (abs_add_le ((-γ)/x^2) (-(τ/(m-x)^2)))
  exact htr.trans ((add_le_add h1 h2).trans_eq (add_div _ _ _).symm)

private theorem abs_sub_div_of_opposite {γ τ x y : ℝ} (hγ : 0 ≤ γ) (hτ : τ ≤ 0)
    (hx : 0 < x) (hy : 0 < y) : |γ/x-τ/y| = |γ|/x+|τ|/y := by
  rw [abs_of_nonneg (sub_nonneg.mpr ((div_nonpos_of_nonpos_of_nonneg hτ hy.le).trans
    (div_nonneg hγ hx.le))),abs_of_nonneg hγ,abs_of_nonpos hτ,neg_div,sub_eq_add_neg]

/-- Both choices of signs obey the same derivative floor away from one interval. -/
theorem convolutionPhase_stationary_gap {X m γ τ H : ℝ} (hX : 0 < X)
    (hH : 1 ≤ H) (hCube : H^3 = |γ|+|τ|) :
    ∃ c : ℝ, ∀ x ∈ Icc X (2*X), m-x ∈ Icc X (2*X) →
      X/H ≤ |x-c| → H^2/(4*X) ≤ |convolutionPhaseDeriv m γ τ x| := by
  let M := |γ|+|τ|
  change H^3 = M at hCube
  have hH₀ : 0 < H := zero_lt_one.trans_le hH
  have hM : 0 < M := by rw [← hCube]; positivity
  by_cases hs : |γ+τ| = M
  · let c := γ*m/(γ+τ)
    have hsum : γ+τ ≠ 0 := abs_pos.mp (hs ▸ hM)
    refine ⟨c,?_⟩
    intro x hx hy hd
    have hx₀ := hX.trans_le hx.1
    have hy₀ := hX.trans_le hy.1
    have hxy : x*(m-x) ≤ 4*X^2 := by
      calc
        _ ≤ (2*X)*(2*X) := mul_le_mul hx.2 hy.2 hy₀.le (by positivity)
        _ = _ := by ring
    have hEq : convolutionPhaseDeriv m γ τ x = (γ+τ)*(c-x)/(x*(m-x)) := by
      unfold convolutionPhaseDeriv c
      field_simp [hsum,hx₀.ne',hy₀.ne']
      ring
    rw [hEq,abs_div,abs_mul,abs_of_pos (mul_pos hx₀ hy₀),abs_sub_comm c x,hs]
    calc
      _ = M*(X/H)/(4*X^2) := by rw [← hCube]; field_simp [hX.ne',hH₀.ne']
      _ ≤ _ := div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hd hM.le)
        (mul_pos hx₀ hy₀) hxy
  · refine ⟨0,?_⟩
    intro x hx hy _
    have hx₀ := hX.trans_le hx.1
    have hy₀ := hX.trans_le hy.1
    have he : |convolutionPhaseDeriv m γ τ x| = |γ|/x+|τ|/(m-x) := by
      unfold convolutionPhaseDeriv
      by_cases hγ : 0 ≤ γ
      · by_cases hτ : 0 ≤ τ
        · exact (hs (by simp only [M,abs_of_nonneg hγ,abs_of_nonneg hτ,
            abs_of_nonneg (add_nonneg hγ hτ)])).elim
        · exact abs_sub_div_of_opposite hγ (le_of_not_ge hτ) hx₀ hy₀
      · by_cases hτ : 0 ≤ τ
        · rw [abs_sub_comm,add_comm]
          exact abs_sub_div_of_opposite hτ (le_of_not_ge hγ) hy₀ hx₀
        · have hγ' := le_of_not_ge hγ
          have hτ' := le_of_not_ge hτ
          exact (hs (by
            dsimp only [M]
            rw [abs_of_nonpos hγ',abs_of_nonpos hτ',abs_of_nonpos (add_nonpos hγ' hτ')]
            ring)).elim
    rw [he]
    have hh : H^2 ≤ H^3 := by
      nlinarith only [mul_nonneg (sq_nonneg H) (sub_nonneg.mpr hH)]
    calc
      _ ≤ H^3/(4*X) := div_le_div_of_nonneg_right hh (by positivity)
      _ ≤ M/(2*X) := by
        rw [hCube]
        exact div_le_div_of_nonneg_left hM.le (by positivity) (by linarith)
      _ = |γ|/(2*X)+|τ|/(2*X) := add_div _ _ _
      _ ≤ _ := add_le_add (div_le_div_of_nonneg_left (abs_nonneg _) hx₀ hx.2)
        (div_le_div_of_nonneg_left (abs_nonneg _) hy₀ hy.2)

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Complex MeasureTheory Set
open scoped Interval

set_option maxHeartbeats 1500000 in
/-- One integration by parts for an oscillatory integral away from stationary points. -/
theorem norm_oscillatory_integral_le
    {a b A B C D : ℝ} (hab : a ≤ b) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 < D)
    (f df : ℝ → ℂ) (p dp ddp : ℝ → ℝ)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (df x) x) (hdf : ContinuousOn df (Icc a b))
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (dp x) x)
    (hdp : ∀ x ∈ Icc a b, HasDerivAt dp (ddp x) x) (hddp : ContinuousOn ddp (Icc a b))
    (hfB : ∀ x ∈ Icc a b, ‖f x‖ ≤ A) (hdfB : ∀ x ∈ Icc a b, ‖df x‖ ≤ B)
    (hpB : ∀ x ∈ Icc a b, D ≤ |dp x|) (hppB : ∀ x ∈ Icc a b, |ddp x| ≤ C) :
    ‖∫ x in a..b, f x*Complex.exp ((p x:ℂ)*I)‖ ≤
      2*A/D+(b-a)*(B/D+A*C/D^2) := by
  let E (x : ℝ) := Complex.exp ((p x:ℂ)*I)
  let v (x : ℝ) := (dp x:ℂ)*I
  let dv (x : ℝ) := (ddp x:ℂ)*I
  let Q (x : ℝ) := f x/v x
  let dQ (x : ℝ) := df x/v x-f x*dv x/(v x)^2
  let I₁ (x : ℝ) := f x*E x
  let I₂ (x : ℝ) := dQ x*E x
  have hEn (x : ℝ) : ‖E x‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hvn (x : ℝ) : ‖v x‖ = |dp x| := by simp [v,Real.norm_eq_abs]
  have hdvn (x : ℝ) : ‖dv x‖ = |ddp x| := by simp [dv,Real.norm_eq_abs]
  have hv0 (x : ℝ) (hx : x ∈ Icc a b) : v x ≠ 0 := by
    apply norm_pos_iff.mp
    rw [hvn]
    exact hD.trans_le (hpB x hx)
  have hvc : ContinuousOn v (Icc a b) := by
    apply (continuous_ofReal.comp_continuousOn ?_).mul continuousOn_const
    exact fun x hx => (hdp x hx).continuousAt.continuousWithinAt
  have hdvc : ContinuousOn dv (Icc a b) :=
    (continuous_ofReal.comp_continuousOn hddp).mul continuousOn_const
  have hfc : ContinuousOn f (Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hEc : ContinuousOn E (Icc a b) := by
    apply Complex.continuous_exp.comp_continuousOn
    apply (continuous_ofReal.comp_continuousOn ?_).mul continuousOn_const
    exact fun x hx => (hp x hx).continuousAt.continuousWithinAt
  have hI₁c : ContinuousOn I₁ (Icc a b) := hfc.mul hEc
  have hI₂c : ContinuousOn I₂ (Icc a b) := by
    apply ContinuousOn.mul _ hEc
    exact (hdf.div hvc hv0).sub ((hfc.mul hdvc).div (hvc.pow 2) (fun x hx => pow_ne_zero _ (hv0 x hx)))
  have hDer (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt (fun t => Q t*E t) (I₁ x+I₂ x) x := by
    have hV : HasDerivAt v (dv x) x := ((hdp x hx).ofReal_comp).mul_const _
    have hE : HasDerivAt E (E x*v x) x := (((hp x hx).ofReal_comp).mul_const I).cexp
    have hQ : HasDerivAt Q (dQ x) x := by
      convert (hf x hx).div hV (hv0 x hx) using 1
      unfold dQ
      field_simp [hv0 x hx]
    convert hQ.mul hE using 1
    dsimp [Q,I₁,I₂]
    field_simp [hv0 x hx]
    ring
  have hI₁ : IntervalIntegrable I₁ volume a b := hI₁c.intervalIntegrable_of_Icc hab
  have hI₂ : IntervalIntegrable I₂ volume a b := hI₂c.intervalIntegrable_of_Icc hab
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hDer x ((uIcc_of_le hab) ▸ hx)) (hI₁.add hI₂)
  rw [intervalIntegral.integral_add hI₁ hI₂] at hFTC
  have hFTC' : (∫ x in a..b, I₁ x) = Q b*E b-Q a*E a-(∫ x in a..b, I₂ x) := by
    linear_combination hFTC
  have hQ (x : ℝ) (hx : x ∈ Icc a b) : ‖Q x*E x‖ ≤ A/D := by
    dsimp only [Q]
    rw [norm_mul,hEn,mul_one,norm_div,hvn]
    exact div_le_div₀ hA (hfB x hx) hD (hpB x hx)
  have hSub (x : ℝ) (hx : x ∈ uIoc a b) : ‖I₂ x‖ ≤ B/D+A*C/D^2 := by
    have hx' := uIoc_subset_uIcc hx
    rw [uIcc_of_le hab] at hx'
    change ‖dQ x*E x‖ ≤ _
    dsimp only [dQ]
    rw [norm_mul,hEn,mul_one]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_div,hvn]
      exact div_le_div₀ hB (hdfB x hx') hD (hpB x hx')
    · rw [norm_div,norm_mul,norm_pow,hvn,hdvn]
      refine div_le_div₀ (by positivity) ?_ (sq_pos_of_pos hD)
        (pow_le_pow_left₀ hD.le (hpB x hx') 2)
      exact mul_le_mul (hfB x hx') (hppB x hx') (abs_nonneg _) hA
  have hIn := intervalIntegral.norm_integral_le_of_norm_le_const hSub
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hIn
  change ‖∫ x in a..b,I₁ x‖ ≤ _
  rw [hFTC']
  calc
    _ ≤ ‖Q b*E b-Q a*E a‖ + ‖∫ x in a..b,I₂ x‖ := norm_sub_le _ _
    _ ≤ (A/D+A/D)+(B/D+A*C/D^2)*(b-a) :=
      (add_le_add) ((norm_sub_le _ _).trans (add_le_add (hQ b ⟨hab,le_rfl⟩) (hQ a ⟨le_rfl,hab⟩))) hIn
    _ = _ := by ring

end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

private def clipped (a b x : ℝ) : ℝ := max a (min b x)

private theorem clipped_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    clipped a b x ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

private theorem clipped_sub_le (a b : ℝ) {u v : ℝ} (huv : u ≤ v) :
    clipped a b v - clipped a b u ≤ v-u := by
  unfold clipped
  apply sub_le_iff_le_add.mpr
  have hmin : min b v ≤ min b u+(v-u) := by
    by_cases h : u ≤ b
    · rw [min_eq_right h]
      linarith only [min_le_right b v]
    · rw [min_eq_left (le_of_not_ge h)]
      linarith only [min_le_left b v,huv]
  apply max_le
  · linarith only [le_max_left a (min b u),huv]
  · linarith only [hmin,le_max_right a (min b u)]

set_option maxHeartbeats 850000 in
/-- Integration by parts on either side of a clipped stationary neighborhood. -/
theorem norm_oscillatory_integral_le_with_gap
    {a b A B C D R c : ℝ} (hab : a ≤ b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hD : 0 < D) (hR : 0 ≤ R)
    (f df : ℝ → ℂ) (p dp ddp : ℝ → ℝ)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (df x) x) (hdf : ContinuousOn df (Icc a b))
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (dp x) x)
    (hdp : ∀ x ∈ Icc a b, HasDerivAt dp (ddp x) x) (hddp : ContinuousOn ddp (Icc a b))
    (hfB : ∀ x ∈ Icc a b, ‖f x‖ ≤ A) (hdfB : ∀ x ∈ Icc a b, ‖df x‖ ≤ B)
    (hpB : ∀ x ∈ Icc a b, R ≤ |x-c| → D ≤ |dp x|)
    (hppB : ∀ x ∈ Icc a b, |ddp x| ≤ C) :
    ‖∫ x in a..b, f x*Complex.exp ((p x:ℂ)*I)‖ ≤
      2*(2*A/D+(b-a)*(B/D+A*C/D^2))+2*R*A := by
  let l := clipped a b (c-R)
  let r := clipped a b (c+R)
  let G (x : ℝ) := f x*Complex.exp ((p x:ℂ)*I)
  let K := 2*A/D+(b-a)*(B/D+A*C/D^2)
  have hL : l ∈ Icc a b := clipped_mem hab _
  have hR' : r ∈ Icc a b := clipped_mem hab _
  have hlr' : c-R ≤ c+R := by linarith only [hR]
  have hlr : l ≤ r := by
    dsimp only [l,r,clipped]
    gcongr
  have hwidth : r-l ≤ 2*R := by
    have hh := clipped_sub_le a b hlr'
    change r-l ≤ (c+R)-(c-R) at hh
    linarith only [hh]
  have hK : 0 ≤ K := by dsimp only [K]; positivity [sub_nonneg.mpr hab]
  have hG : ContinuousOn G (Icc a b) := by
    apply ContinuousOn.mul
    · exact fun x hx => (hf x hx).continuousAt.continuousWithinAt
    · apply Complex.continuous_exp.comp_continuousOn
      apply (Complex.continuous_ofReal.comp_continuousOn ?_).mul continuousOn_const
      exact fun x hx => (hp x hx).continuousAt.continuousWithinAt
  have hInt {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
      IntervalIntegrable G volume u v :=
    (hG.mono (Icc_subset_Icc hu hv)).intervalIntegrable_of_Icc huv
  have hAway {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b)
      (hFar : ∀ x ∈ Icc u v, R ≤ |x-c|) :
      ‖∫ x in u..v, G x‖ ≤ K := by
    let hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc hu hv
    refine (norm_oscillatory_integral_le huv hA hB hC hD f df p dp ddp
      (fun x hx => hf x (hsub hx)) (hdf.mono hsub) (fun x hx => hp x (hsub hx))
      (fun x hx => hdp x (hsub hx)) (hddp.mono hsub)
      (fun x hx => hfB x (hsub hx)) (fun x hx => hdfB x (hsub hx))
      (fun x hx => hpB x (hsub hx) (hFar x hx)) (fun x hx => hppB x (hsub hx))).trans ?_
    dsimp only [K]
    gcongr
  have hLeft : ‖∫ x in a..l,G x‖ ≤ K := by
    rcases hL.1.eq_or_lt with he | hlt
    · rw [← he,intervalIntegral.integral_same,norm_zero]
      exact hK
    · apply hAway le_rfl hL.1 hL.2
      intro x hx
      have hL' : a < min b (c-R) := (lt_max_iff.mp hlt).resolve_left (lt_irrefl _)
      have h₀ : l ≤ c-R := by
        change max a (min b (c-R)) ≤ c-R
        rw [max_eq_right hL'.le]
        exact min_le_right _ _
      exact (show R ≤ -(x-c) by linarith only [hx.2,h₀]).trans (neg_le_abs _)
  have hRight : ‖∫ x in r..b,G x‖ ≤ K := by
    rcases hR'.2.eq_or_lt with he | hlt
    · rw [he,intervalIntegral.integral_same,norm_zero]
      exact hK
    · apply hAway hR'.1 hR'.2 le_rfl
      intro x hx
      have hh : min b (c+R) < b := (max_lt_iff.mp hlt).2
      have hv : c+R < b := (min_lt_iff.mp hh).resolve_left (lt_irrefl _)
      have h₀ : c+R ≤ r := by
        change c+R ≤ max a (min b (c+R))
        rw [min_eq_right hv.le]
        exact le_max_right _ _
      exact (show R ≤ x-c by linarith only [hx.1,h₀]).trans (le_abs_self _)
  have hMid : ‖∫ x in l..r,G x‖ ≤ 2*R*A := by
    have hw (x : ℝ) (hx : x ∈ uIoc l r) : ‖G x‖ ≤ A := by
      have hx' := uIoc_subset_uIcc hx
      rw [uIcc_of_le hlr] at hx'
      simpa only [G,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one] using
        hfB x (Icc_subset_Icc hL.1 hR'.2 hx')
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hw).trans ?_
    rw [abs_of_nonneg (sub_nonneg.mpr hlr),mul_comm A]
    exact mul_le_mul_of_nonneg_right hwidth hA
  have hSplit : (∫ x in a..b,G x) =
      (∫ x in a..l,G x)+(∫ x in l..r,G x)+(∫ x in r..b,G x) := by
    symm
    rw [intervalIntegral.integral_add_adjacent_intervals (hInt le_rfl hL.1 hL.2)
      (hInt hL.1 hlr hR'.2), intervalIntegral.integral_add_adjacent_intervals
      (hInt le_rfl hR'.1 hR'.2) (hInt hR'.1 hR'.2 le_rfl)]
  change ‖∫ x in a..b,G x‖ ≤ 2*K+2*R*A
  rw [hSplit]
  refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl) |>.trans ?_
  linarith only [hLeft,hMid,hRight]

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Complex MeasureTheory Set GoldbachSmoothMellin GoldbachSmoothWindow GoldbachTwistedMellin
open scoped ContDiff Interval

theorem density_rpow_phase {x : ℝ} (hx : 0 < x) (β : ℝ) (s : ℂ) :
    density β s x = ((x^(s.re-1):ℝ):ℂ) * Complex.exp (((s.im*Real.log x+β*x:ℝ):ℂ)*I) := by
  have hsub : s-1 = ((s.re-1:ℝ):ℂ)+((s.im:ℝ):ℂ)*I := by
    apply Complex.ext <;> simp [Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im]
  rw [density,phase,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le,hsub,Real.rpow_def_of_pos hx,Complex.ofReal_exp,
    ← Complex.exp_add,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem scaledWeight_deriv_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {X : ℝ}, 0 < X → ∀ t, ‖deriv (scaledWeight X) t‖ ≤ K/X := by
  obtain ⟨K,hK,hW⟩ := weight_derivative_bound 1
  refine ⟨K,hK,?_⟩
  intro X hX t
  have h := scaledWeight_derivative 1 X t
  simp only [iteratedDeriv_succ,iteratedDeriv_zero,pow_one] at h
  rw [h,norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hX.le)]
  calc
    _ ≤ X⁻¹*K := mul_le_mul_of_nonneg_left (by
      simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hW (t/X)) (inv_nonneg.mpr hX.le)
    _ = _ := by ring

set_option maxHeartbeats 1800000 in
theorem smooth_high_frequency_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X β : ℝ}, 0 < X → β ≠ 0 → ∀ (s : ℂ), 0 ≤ s.re → s.re ≤ 1 →
      2*|s.im| ≤ X*|β| →
      ‖smoothTransform X (2*X) β (scaledWeight X) s‖ ≤ C*X^(s.re-1)/|β| := by
  obtain ⟨K,hK,hW⟩ := scaledWeight_deriv_bound
  refine ⟨2*K+8,by positivity,?_⟩
  intro X β hX hβ s hs0 hs1 hfreq
  let r := s.re-1
  let A := X^r
  let f (x : ℝ) : ℂ := ((scaledWeight X x*x^r:ℝ):ℂ)
  let df (x : ℝ) : ℂ :=
    ((deriv (scaledWeight X) x*x^r+scaledWeight X x*(r*x^(r-1)):ℝ):ℂ)
  let p (x : ℝ) := s.im*Real.log x+β*x
  let dp (x : ℝ) := s.im/x+β
  let ddp (x : ℝ) := -s.im/x^2
  let D := |β|/2
  let E := |s.im|/X^2
  let B := (K+1)*A/X
  have hX2 : X ≤ 2*X := by linarith
  have hD : 0 < D := div_pos (abs_pos.mpr hβ) (by norm_num)
  have hA : 0 ≤ A := Real.rpow_nonneg hX.le _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hWc : ContDiff ℝ 1 (scaledWeight X) := weight_smooth.comp (contDiff_id.div_const X)
  have hPos (x : ℝ) (hx : x ∈ Icc X (2*X)) : 0 < x := hX.trans_le hx.1
  have hf (x : ℝ) (hx : x ∈ Icc X (2*X)) : HasDerivAt f (df x) x := by
    have h := Real.hasDerivAt_rpow_const (p:=r) (Or.inl (hPos x hx).ne')
    simpa [f,df,add_comm,mul_comm] using
      (((hWc.differentiable_one x).hasDerivAt).mul h).ofReal_comp
  have hPow (e : ℝ) : ContinuousOn (fun x : ℝ => x^e) (Icc X (2*X)) :=
    fun x hx => (Real.continuousAt_rpow_const _ _ (Or.inl (hPos x hx).ne')).continuousWithinAt
  have hdf : ContinuousOn df (Icc X (2*X)) := by
    apply continuous_ofReal.comp_continuousOn
    exact ((hWc.continuous_deriv le_rfl).continuousOn.mul (hPow r)).add
      (hWc.continuous.continuousOn.mul (continuousOn_const.mul (hPow (r-1))))
  have hp (x : ℝ) (hx : x ∈ Icc X (2*X)) : HasDerivAt p (dp x) x := by
    have h := ((Real.hasDerivAt_log (hPos x hx).ne').const_mul s.im).add
      ((hasDerivAt_id x).const_mul β)
    have he : dp x = s.im*x⁻¹+β := by unfold dp; rw [div_eq_mul_inv]
    rw [he]
    convert h using 1
    funext t
    simp [p]
    ring
  have hdp (x : ℝ) (hx : x ∈ Icc X (2*X)) : HasDerivAt dp (ddp x) x := by
    have h := (((hasDerivAt_const x s.im).div (hasDerivAt_id x) (hPos x hx).ne')).add_const β
    simpa [dp,ddp,neg_div] using h
  have hddp : ContinuousOn ddp (Icc X (2*X)) := by
    change ContinuousOn (fun t : ℝ => -s.im/t^2) (Icc X (2*X))
    exact continuousOn_const.div (show ContinuousOn (fun t : ℝ => t^2) (Icc X (2*X)) from
      continuousOn_id.pow 2) (fun x hx => pow_ne_zero 2 (hPos x hx).ne')
  have hr : r ≤ 0 := sub_nonpos.mpr hs1
  have hrn : |r| ≤ 1 := by rw [abs_of_nonpos hr]; dsimp [r]; linarith
  have hPx (x : ℝ) (hx : x ∈ Icc X (2*X)) : x^r ≤ A :=
    Real.rpow_le_rpow_of_nonpos hX hx.1 hr
  have hfb (x : ℝ) (hx : x ∈ Icc X (2*X)) : ‖f x‖ ≤ A := by
    have hx0 := hPos x hx
    have hw := weight_range (x/X)
    dsimp only [f]
    rw [norm_real,Real.norm_eq_abs,abs_mul,scaledWeight,abs_of_nonneg hw.1,
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) hw.2).trans (hPx x hx)
  have hdfb (x : ℝ) (hx : x ∈ Icc X (2*X)) : ‖df x‖ ≤ B := by
    have hx0 := hPos x hx
    have hp₁ := hPx x hx
    have hp₂ : x^(r-1) ≤ A/X := by
      rw [Real.rpow_sub hx0,Real.rpow_one]
      exact div_le_div₀ (by positivity) hp₁ hX hx.1
    have hw := weight_range (x/X)
    have hh : ‖scaledWeight X x‖ ≤ 1 := by
      rw [scaledWeight,Real.norm_of_nonneg hw.1]
      exact hw.2
    dsimp [df]
    rw [norm_real]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul,Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have h₁ := mul_le_mul (hW hX x) hp₁ (Real.rpow_nonneg hx0.le _) (div_nonneg hK hX.le)
    have h₂ := mul_le_mul hh (mul_le_mul hrn hp₂ (Real.rpow_nonneg hx0.le _) zero_le_one)
      (by positivity : 0≤‖r‖*x^(r-1)) zero_le_one
    rw [Real.norm_eq_abs] at h₁ h₂
    dsimp [B]
    linarith only [h₁,h₂,
      show K/X*A+1*(1*(A/X))=(K+1)*A/X by ring]
  have hdpb (x : ℝ) (hx : x ∈ Icc X (2*X)) : D ≤ |dp x| := by
    have hx0 := hPos x hx
    have hq : |s.im/x| ≤ |β|/2 := by
      rw [abs_div,abs_of_pos hx0]
      exact (div_le_div_of_nonneg_left (abs_nonneg _) hX hx.1).trans
        ((div_le_iff₀ hX).mpr (by linarith only [hfreq]))
    have htriangle := abs_sub_abs_le_abs_sub β (-(s.im/x))
    rw [abs_neg,sub_neg_eq_add] at htriangle
    change |β|/2≤|s.im/x+β|
    rw [add_comm]
    linarith only [hq,htriangle]
  have hddpb (x : ℝ) (hx : x ∈ Icc X (2*X)) : |ddp x| ≤ E := by
    have hx0 := hPos x hx
    simp only [ddp,abs_div,abs_neg,abs_of_nonneg (sq_nonneg x)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hX) (pow_le_pow_left₀ hX.le hx.1 2)
  have hnorm := norm_oscillatory_integral_le hX2 hA hB hE hD f df p dp ddp
    hf hdf hp hdp hddp hfb hdfb hdpb hddpb
  have harch : smoothTransform X (2*X) β (scaledWeight X) s =
      ∫ y in X..(2*X),f y*Complex.exp ((p y:ℂ)*I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hX2] at hy
    change (scaledWeight X y:ℂ) * density β s y = f y*Complex.exp ((p y:ℂ)*I)
    rw [density_rpow_phase (hPos y hy)]
    dsimp [f,p,r]
    rw [Complex.ofReal_mul,mul_assoc]
  rw [harch]
  refine hnorm.trans ?_
  have hβp := abs_pos.mpr hβ
  have hE' : E ≤ |β|/(2*X) := by
    unfold E
    apply (div_le_iff₀ (sq_pos_of_pos hX)).mpr
    convert (show |s.im| ≤ X*|β|/2 by linarith only [hfreq]) using 1
    field_simp [hX.ne']
  calc
    _ ≤ 2*A/D+(2*X-X)*(B/D+A*(|β|/(2*X))/D^2) := by gcongr
    _ = _ := by dsimp [D,B,r,A]; field_simp [hX.ne',hβp.ne']; ring

end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Complex MeasureTheory Set GoldbachSmoothWindow GoldbachTwistedMellin
open scoped ContDiff Interval

noncomputable section

private def smoothAmplitude (X r x : ℝ) : ℝ := scaledWeight X x*x^r

private def smoothAmplitudeDerivative (X r x : ℝ) : ℝ :=
  deriv (scaledWeight X) x*x^r + scaledWeight X x*(r*x^(r-1))

private theorem smoothAmplitude_hasDerivAt (X r : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (smoothAmplitude X r) (smoothAmplitudeDerivative X r x) x := by
  have hW : ContDiff ℝ 1 (scaledWeight X) := weight_smooth.comp (contDiff_id.div_const X)
  have hw := (hW.differentiable_one x).hasDerivAt
  have hp := Real.hasDerivAt_rpow_const (p:=r) (Or.inl hx.ne')
  convert hw.mul hp using 1 <;> rfl

private theorem smoothAmplitude_continuousOn (X r : ℝ) :
    ContinuousOn (smoothAmplitude X r) (Ioi 0) := by
  have hW : ContDiff ℝ 1 (scaledWeight X) := weight_smooth.comp (contDiff_id.div_const X)
  apply hW.continuous.continuousOn.mul
  exact fun x hx => (Real.continuousAt_rpow_const x r
    (Or.inl (show 0 < x from hx).ne')).continuousWithinAt

private theorem smoothAmplitudeDerivative_continuousOn (X r : ℝ) :
    ContinuousOn (smoothAmplitudeDerivative X r) (Ioi 0) := by
  have hW : ContDiff ℝ 1 (scaledWeight X) := weight_smooth.comp (contDiff_id.div_const X)
  have hp (d : ℝ) : ContinuousOn (fun x : ℝ => x^d) (Ioi 0) :=
    fun x hx => (Real.continuousAt_rpow_const x d
      (Or.inl (show 0 < x from hx).ne')).continuousWithinAt
  exact ((hW.continuous_deriv le_rfl).continuousOn.mul (hp r)).add
    (hW.continuous.continuousOn.mul (continuousOn_const.mul (hp (r-1))))

private theorem smoothAmplitude_norm_le {X r x : ℝ} (hX : 0 < X) (hx : X ≤ x) (hr : r ≤ 0) :
    ‖smoothAmplitude X r x‖ ≤ X^r := by
  have hx₀ := hX.trans_le hx
  have hw := weight_range (x/X)
  rw [smoothAmplitude,norm_mul,scaledWeight,Real.norm_of_nonneg hw.1,
    Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _)]
  exact (mul_le_of_le_one_left (Real.rpow_nonneg hx₀.le _) hw.2).trans
    (Real.rpow_le_rpow_of_nonpos hX hx hr)

private theorem smoothAmplitudeDerivative_norm_le {X r x K : ℝ} (hX : 0 < X)
    (hx : X ≤ x) (hr₀ : -1 ≤ r) (hr₁ : r ≤ 0) (hK : 0 ≤ K)
    (hW : ‖deriv (scaledWeight X) x‖ ≤ K/X) :
    ‖smoothAmplitudeDerivative X r x‖ ≤ (K+1)*X^r/X := by
  have hx₀ := hX.trans_le hx
  have hpow : x^r ≤ X^r := Real.rpow_le_rpow_of_nonpos hX hx hr₁
  have hpow' : x^(r-1) ≤ X^r/X := by
    rw [Real.rpow_sub hx₀,Real.rpow_one]
    exact div_le_div₀ (by positivity) hpow hX hx
  have hw := weight_range (x/X)
  have hweight : ‖scaledWeight X x‖ ≤ 1 := by
    rw [scaledWeight,Real.norm_of_nonneg hw.1]
    exact hw.2
  have hr : ‖r‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonpos hr₁]; linarith only [hr₀]
  unfold smoothAmplitudeDerivative
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul,Real.norm_of_nonneg (Real.rpow_nonneg hx₀.le _)]
  have h₁ := mul_le_mul hW hpow (Real.rpow_nonneg hx₀.le _) (div_nonneg hK hX.le)
  have h₂ := mul_le_mul hweight (mul_le_mul hr hpow' (Real.rpow_nonneg hx₀.le _) zero_le_one)
    (by positivity : 0 ≤ ‖r‖*x^(r-1)) zero_le_one
  calc
    _ ≤ K/X*X^r + 1*(1*(X^r/X)) := add_le_add h₁ h₂
    _ = _ := by ring

private theorem smoothDensity_amplitude_phase {X x : ℝ} (hx : 0 < x) (s : ℂ) :
    smoothDensity X s x =
      (smoothAmplitude X (s.re-1) x : ℂ)*Complex.exp (((s.im*Real.log x:ℝ):ℂ)*I) := by
  have hp : (x:ℂ)^(s-1) =
      ((x^(s.re-1):ℝ):ℂ)*Complex.exp (((s.im*Real.log x:ℝ):ℂ)*I) := by
    simpa [density,phase] using density_rpow_phase hx 0 s
  rw [smoothDensity,hp,← mul_assoc,smoothAmplitude]
  simp only [Complex.ofReal_mul]

private theorem convolution_integrand_phase {X m x : ℝ} (hx : 0 < x) (hy : 0 < m-x) (s z : ℂ) :
    smoothDensity X s x*smoothDensity X z (m-x) =
      ((smoothAmplitude X (s.re-1) x*smoothAmplitude X (z.re-1) (m-x):ℝ):ℂ)*
        Complex.exp ((convolutionPhase m s.im z.im x:ℂ)*I) := by
  rw [smoothDensity_amplitude_phase hx, smoothDensity_amplitude_phase hy, mul_mul_mul_comm,
    ← Complex.ofReal_mul, ← Complex.exp_add, convolutionPhase,Complex.ofReal_add, add_mul]

private theorem convolution_IBP_constants {X H A B l : ℝ}
    (hX : 0 < X) (hH : 1 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hl : l ≤ X) :
    let D := H^2/(4*X)
    2*(2*A/D+l*((B*A/X)/D+A*(H^3/X^2)/D^2))+2*(X/H)*A ≤ (50+8*B)*X*A/H := by
  let D := H^2/(4*X)
  have hH₀ := zero_lt_one.trans_le hH
  have hD : 0 < D := by dsimp only [D]; positivity
  have hP : 0 ≤ (B*A/X)/D+A*(H^3/X^2)/D^2 := by positivity
  have hHH : H ≤ H^2 := by nlinarith only [mul_nonneg hH₀.le (sub_nonneg.mpr hH)]
  change 2*(2*A/D+l*((B*A/X)/D+A*(H^3/X^2)/D^2))+2*(X/H)*A ≤ _
  calc
    _ ≤ 2*(2*A/D+X*((B*A/X)/D+A*(H^3/X^2)/D^2))+2*(X/H)*A := by
      have hh := mul_le_mul_of_nonneg_right hl hP
      linarith only [hh]
    _ = (16+8*B)*X*A/H^2+34*X*A/H := by
      dsimp only [D]
      field_simp [hX.ne', hH₀.ne']
      ring
    _ ≤ (16+8*B)*X*A/H+34*X*A/H := by
      exact add_le_add (div_le_div_of_nonneg_left
        (show 0 ≤ (16+8*B)*X*A by positivity) hH₀ hHH) le_rfl
    _ = _ := by ring

set_option maxHeartbeats 1200000 in
/-- Compact smooth Mellin densities decorrelate when the sum of their heights is large. -/
theorem norm_smoothDensity_convolution_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {X m : ℝ}, 0 < X → (5/2:ℝ)*X ≤ m → m ≤ (7/2:ℝ)*X →
      ∀ s z : ℂ, 0 ≤ s.re → s.re ≤ 1 → 0 ≤ z.re → z.re ≤ 1 → 1 ≤ |s.im|+|z.im| →
      ‖∫ x : ℝ, smoothDensity X s x*smoothDensity X z (m-x)‖ ≤
        C*X*X^(s.re-1)*X^(z.re-1)*(|s.im|+|z.im|)^(-1/3 : ℝ) := by
  obtain ⟨K,hK,hW⟩ := scaledWeight_deriv_bound
  let B := 2*(K+1)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨50+8*B,by positivity,?_⟩
  intro X m hX hm₁ hm₂ s z hs₀ hs₁ hz₀ hz₁ hM
  let rs := s.re-1
  let rz := z.re-1
  let M := |s.im|+|z.im|
  let H := M^(1/3 : ℝ)
  let A := X^rs*X^rz
  let D := H^2/(4*X)
  let a := max X (m-2*X)
  let b := min (2*X) (m-X)
  let f (x : ℝ) : ℂ := ((smoothAmplitude X rs x*smoothAmplitude X rz (m-x):ℝ):ℂ)
  let df (x : ℝ) : ℂ := ((smoothAmplitudeDerivative X rs x*smoothAmplitude X rz (m-x)-
    smoothAmplitude X rs x*smoothAmplitudeDerivative X rz (m-x):ℝ):ℂ)
  let p := convolutionPhase m s.im z.im
  let dp := convolutionPhaseDeriv m s.im z.im
  let ddp := convolutionPhaseSecond m s.im z.im
  have hH : 1 ≤ H := Real.one_le_rpow hM (by norm_num)
  have hH₀ := zero_lt_one.trans_le hH
  have hCube : H^3 = M := by
    dsimp only [H]
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hM),
      show (1/3:ℝ)*(3:ℕ) = 1 by norm_num,Real.rpow_one]
  have hD : 0 < D := by dsimp only [D]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hab : a ≤ b := by
    dsimp only [a,b]
    apply max_le <;> apply le_min <;> linarith only [hX,hm₁,hm₂]
  have hlen : b-a ≤ X := by
    linarith only [show X ≤ a from le_max_left _ _, show b ≤ 2*X from min_le_left _ _]
  have hxI (x : ℝ) (hx : x ∈ Icc a b) : x ∈ Icc X (2*X) :=
    ⟨(le_max_left _ _).trans hx.1,hx.2.trans (min_le_left _ _)⟩
  have hyI (x : ℝ) (hx : x ∈ Icc a b) : m-x ∈ Icc X (2*X) := by
    constructor
    · linarith only [hx.2.trans (show b ≤ m-X from min_le_right _ _)]
    · linarith only [(show m-2*X ≤ a from le_max_right _ _).trans hx.1]
  have hx₀ (x : ℝ) (hx : x ∈ Icc a b) : 0 < x := hX.trans_le (hxI x hx).1
  have hy₀ (x : ℝ) (hx : x ∈ Icc a b) : 0 < m-x := hX.trans_le (hyI x hx).1
  have hf (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt f (df x) x := by
    have hh := smoothAmplitude_hasDerivAt X rs (hx₀ x hx)
    have hh' := (smoothAmplitude_hasDerivAt X rz (hy₀ x hx)).comp x
      ((hasDerivAt_const x m).sub (hasDerivAt_id x))
    convert (hh.mul hh').ofReal_comp using 1 <;> try rfl
    simp [df,sub_eq_add_neg]
  have hdf : ContinuousOn df (Icc a b) := by
    have hleft : Icc a b ⊆ Ioi 0 := fun x hx => hx₀ x hx
    have hmap : MapsTo (fun x : ℝ => m-x) (Icc a b) (Ioi 0) := fun x hx => hy₀ x hx
    have hcont : ContinuousOn (fun x : ℝ => m-x) (Icc a b) :=
      continuousOn_const.sub continuousOn_id
    apply Complex.continuous_ofReal.comp_continuousOn
    exact (((smoothAmplitudeDerivative_continuousOn X rs).mono hleft).mul
      ((smoothAmplitude_continuousOn X rz).comp hcont hmap)).sub
      (((smoothAmplitude_continuousOn X rs).mono hleft).mul
        ((smoothAmplitudeDerivative_continuousOn X rz).comp hcont hmap))
  have hbound (x : ℝ) (hx : x ∈ Icc a b) : ‖f x‖ ≤ A := by
    change ‖((smoothAmplitude X rs x*smoothAmplitude X rz (m-x):ℝ):ℂ)‖ ≤ A
    rw [norm_real,norm_mul]
    exact mul_le_mul (smoothAmplitude_norm_le hX (hxI x hx).1 (sub_nonpos.mpr hs₁))
      (smoothAmplitude_norm_le hX (hyI x hx).1 (sub_nonpos.mpr hz₁))
      (norm_nonneg _) (Real.rpow_nonneg hX.le _)
  have hdbound (x : ℝ) (hx : x ∈ Icc a b) : ‖df x‖ ≤ B*A/X := by
    dsimp only [df]
    rw [norm_real]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul,norm_mul]
    have hr : -1 ≤ rs := by dsimp [rs]; linarith only [hs₀]
    have hr' : -1 ≤ rz := by dsimp [rz]; linarith only [hz₀]
    have h₁ := smoothAmplitudeDerivative_norm_le hX (hxI x hx).1 hr
      (sub_nonpos.mpr hs₁) hK (hW hX x)
    have h₂ := smoothAmplitudeDerivative_norm_le hX (hyI x hx).1 hr'
      (sub_nonpos.mpr hz₁) hK (hW hX (m-x))
    have h₃ := smoothAmplitude_norm_le hX (hxI x hx).1 (sub_nonpos.mpr hs₁)
    have h₄ := smoothAmplitude_norm_le hX (hyI x hx).1 (sub_nonpos.mpr hz₁)
    calc
      _ ≤ ((K+1)*X^rs/X)*X^rz+X^rs*((K+1)*X^rz/X) := add_le_add
        (mul_le_mul h₁ h₄ (norm_nonneg _) (by positivity))
        (mul_le_mul h₃ h₂ (norm_nonneg _) (by positivity))
      _ = _ := by dsimp only [A,B]; ring
  obtain ⟨c,hgap⟩ := convolutionPhase_stationary_gap (X:=X) (m:=m)
    (γ:=s.im) (τ:=z.im) hX hH hCube
  have hnorm := norm_oscillatory_integral_le_with_gap (R:=X/H) (c:=c) hab hA
    (show 0 ≤ B*A/X by positivity) (show 0 ≤ H^3/X^2 by positivity) hD (by positivity)
    f df p dp ddp hf hdf (fun x hx => convolutionPhase_hasDerivAt (hx₀ x hx) (hy₀ x hx))
    (fun x hx => convolutionPhaseDeriv_hasDerivAt (hx₀ x hx) (hy₀ x hx))
    (convolutionPhaseSecond_continuousOn hx₀ hy₀) hbound hdbound
    (fun x hx => hgap x (hxI x hx) (hyI x hx)) (fun x hx => by
      rw [hCube]
      exact convolutionPhaseSecond_abs_le hX (hxI x hx).1 (hyI x hx).1)
  have harch : (∫ x : ℝ, smoothDensity X s x*smoothDensity X z (m-x)) =
      ∫ x in a..b, f x*Complex.exp ((p x:ℂ)*I) := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    calc
      _ = ∫ x in Icc a b, smoothDensity X s x*smoothDensity X z (m-x) := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        by_cases hx' : x ∈ Icc X (2*X)
        · have hy' : m-x ∉ Icc X (2*X) := by
            intro hy
            apply hx
            exact ⟨max_le hx'.1 (by linarith only [hy.2]), le_min hx'.2 (by linarith only [hy.1])⟩
          rw [smoothDensity_zero_outside hX z hy',mul_zero]
        · rw [smoothDensity_zero_outside hX s hx',zero_mul]
      _ = _ := setIntegral_congr_fun measurableSet_Icc
        (fun x hx => convolution_integrand_phase (hx₀ x hx) (hy₀ x hx) s z)
  rw [harch]
  refine hnorm.trans ((convolution_IBP_constants hX hH hA hB hlen).trans_eq ?_)
  have hInv : H⁻¹ = M^(-1/3 : ℝ) := by
    rw [show (-1/3:ℝ) = -(1/3:ℝ) by ring,Real.rpow_neg (zero_le_one.trans hM)]
  change (50+8*B)*X*A/H = (50+8*B)*X*X^rs*X^rz*M^(-1/3 : ℝ)
  rw [← hInv,div_eq_mul_inv]
  dsimp only [A]
  ring

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset DirichletCharacter
open scoped Classical

noncomputable section


theorem conductorClass_eq_of_small_ratio {q K : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q)
    (h : (χ/ψ).conductor ≤ K) : conductorClass K χ = conductorClass K ψ :=
  (conductorClass_eq_iff χ ψ).mpr
    (Nat.dvd_factorial (Nat.pos_of_ne_zero (χ/ψ).conductor_ne_zero) h)

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset DirichletCharacter
open scoped Classical

noncomputable section

theorem conductorClass_inv {q K : ℕ} (χ : DirichletCharacter ℂ q) :
    conductorClass K χ⁻¹ = (conductorClass K χ)⁻¹ :=
  QuotientGroup.mk_inv (boundedConductorSubgroup q K) χ

theorem conductorClass_eq_inv_of_small_product {q K : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (h : (χ*ψ).conductor ≤ K) :
    conductorClass K χ = (conductorClass K ψ)⁻¹ := by
  rw [← conductorClass_inv]
  apply conductorClass_eq_of_small_ratio
  simpa only [div_inv_eq_mul] using h

/-- Products of small conductor only pair inverse quotient classes. The sum
of all their cross-products is bounded by the sum of squared class masses. -/
theorem small_product_pair_mass_le {ι : Type*} {q K : ℕ} [NeZero q]
    (S : Finset ι) (χ : ι → DirichletCharacter ℂ q) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) :
    (∑ i ∈ S, ∑ j ∈ S.filter (fun j => (χ i*χ j).conductor ≤ K), a i*a j) ≤
      ∑ k ∈ S.image (fun i => conductorClass K (χ i)),
        (∑ i ∈ S.filter (fun i => conductorClass K (χ i)=k), a i)^2 := by
  classical
  let Γ := (DirichletCharacter ℂ q) ⧸ boundedConductorSubgroup q K
  let _ : Fintype Γ := Fintype.ofFinite Γ
  let k (i : ι) : Γ := conductorClass K (χ i)
  let W := S.image k
  let H (r : Γ) := ∑ i ∈ S.filter (fun i => k i=r), a i
  have hm : (S : Set ι).MapsTo k W := fun i hi => mem_image_of_mem _ hi
  have hsub (i : ι) :
      S.filter (fun j => (χ i*χ j).conductor ≤ K) ⊆ S.filter (fun j => k j=(k i)⁻¹) := by
    intro j hj
    obtain ⟨hj',hr⟩ := mem_filter.mp hj
    rw [mul_comm] at hr
    exact mem_filter.mpr ⟨hj',conductorClass_eq_inv_of_small_product (χ j) (χ i) hr⟩
  have hzero (r : Γ) (hr : r ∉ W) : H r = 0 := by
    dsimp only [H]
    apply sum_eq_zero
    intro i hi
    obtain ⟨hi,hki⟩ := mem_filter.mp hi
    exact (hr (hki ▸ hm hi)).elim
  have hswap : (∑ r : Γ, (H r⁻¹)^2) = ∑ r : Γ, (H r)^2 :=
    Equiv.sum_comp (Equiv.inv Γ) (fun r => (H r)^2)
  calc
    _ ≤ ∑ i ∈ S, a i*H ((k i)⁻¹) := by
      apply sum_le_sum
      intro i hi
      rw [mul_sum]
      exact sum_le_sum_of_subset_of_nonneg (hsub i) (fun j hj _ =>
        mul_nonneg (ha i hi) (ha _ (mem_filter.mp hj).1))
    _ = ∑ r ∈ W, ∑ i ∈ S.filter (fun i => k i=r), a i*H ((k i)⁻¹) :=
      (sum_fiberwise_of_maps_to hm _).symm
    _ = ∑ r ∈ W, H r*H r⁻¹ := by
      apply sum_congr rfl
      intro r hr
      calc
        _ = ∑ i ∈ S.filter (fun i => k i=r), a i*H r⁻¹ := by
          apply sum_congr rfl
          intro i hi
          rw [(mem_filter.mp hi).2]
        _ = _ := by rw [← sum_mul]
    _ = ∑ r : Γ, H r*H r⁻¹ := by
      apply sum_subset (subset_univ _)
      intro r _ hr
      rw [hzero r hr, zero_mul]
    _ ≤ ∑ r : Γ, ((H r)^2+(H r⁻¹)^2)/2 := by
      apply sum_le_sum
      intro r _
      nlinarith only [sq_nonneg (H r-H r⁻¹)]
    _ = ∑ r : Γ, (H r)^2 := by rw [← sum_div, sum_add_distrib, hswap]; ring
    _ = ∑ r ∈ W, (H r)^2 := by
      symm
      apply sum_subset (subset_univ _)
      intro r _ hr
      rw [hzero r hr, zero_pow (by decide : (2:ℕ) ≠ 0)]

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset
open scoped Classical

noncomputable section

def divisorClass {ι : Type*} (S : Finset ι) (r : ι → ℕ) (C m : ℕ) : Finset ι :=
  S.filter (fun i => r i ∣ C*m)

def classModulus {ι : Type*} (S : Finset ι) (r : ι → ℕ) (C m : ℕ) : ℕ :=
  (divisorClass S r C m).lcm r

theorem classModulus_dvd {ι : Type*} (S : Finset ι) (r : ι → ℕ) (C m : ℕ) :
    classModulus S r C m ∣ C*m :=
  lcm_dvd (fun _ hi => (mem_filter.mp hi).2)

private theorem divisor_target_card_le {C B q : ℕ} (hC : 0 < C) (hq : 0 < q) :
    (((range (B+1)).filter (fun m => q ∣ C*m)).card : ℝ) ≤ (C:ℝ)*B/q+1 := by
  let S := (range (B+1)).filter (fun m => q ∣ C*m)
  let d (m : ℕ) := C*m/q
  have hmap : (S : Set ℕ).MapsTo d (range (C*B/q+1)) := by
    intro m hm
    have hb : m ≤ B := Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hm).1)
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.mul_le_mul_left C hb)))
  have hinj : Set.InjOn d S := by
    intro m hm n hn he
    have h := congrArg (fun u : ℕ => u*q) he
    dsimp only [d] at h
    rw [Nat.div_mul_cancel (mem_filter.mp hm).2,Nat.div_mul_cancel (mem_filter.mp hn).2] at h
    exact Nat.eq_of_mul_eq_mul_left hC h
  have hcard := Finset.card_le_card_of_injOn d hmap hinj
  rw [card_range] at hcard
  have hR : (0:ℝ) < q := by exact_mod_cast hq
  have hdiv : ((C*B/q:ℕ):ℝ) ≤ (C:ℝ)*B/q :=
    (le_div_iff₀ hR).mpr (by exact_mod_cast Nat.div_mul_le_self (C*B) q)
  exact (show (S.card:ℝ) ≤ ((C*B/q:ℕ):ℝ)+1 by exact_mod_cast hcard).trans (add_le_add hdiv le_rfl)

/-- All divisor classes with a large common modulus contribute only the corresponding
number of multiples per class. -/
theorem large_classModulus_card_le {ι : Type*} (S : Finset ι) (r : ι → ℕ) {C B : ℕ}
    (hC : 0 < C) {T : ℝ} (hT : 0 < T) :
    (((range (B+1)).filter (fun m => T < (classModulus S r C m:ℝ))).card : ℝ) ≤
      (2:ℝ)^S.card*((C:ℝ)*B/T+1) := by
  let Z := (range (B+1)).filter (fun m => T < (classModulus S r C m:ℝ))
  let W := S.powerset
  let key := divisorClass S r C
  have hmap : (Z : Set ℕ).MapsTo key W := by
    intro m _
    exact mem_powerset.mpr (filter_subset _ _)
  have hBound (A : Finset ι) (hA : A ∈ W) :
      ((Z.filter (fun m => key m=A)).card:ℝ) ≤ (C:ℝ)*B/T+1 := by
    let q := A.lcm r
    by_cases hq : T < (q:ℝ)
    · have hq0 : 0 < q := by exact_mod_cast hT.trans hq
      have hsub : Z.filter (fun m => key m=A) ⊆
          (range (B+1)).filter (fun m => q ∣ C*m) := by
        intro m hm
        obtain ⟨hmZ,hEq⟩ := mem_filter.mp hm
        have hmem := (mem_filter.mp hmZ).1
        have hd := classModulus_dvd S r C m
        change (key m).lcm r ∣ C*m at hd
        rw [hEq] at hd
        exact mem_filter.mpr ⟨hmem,hd⟩
      have hcard : ((Z.filter (fun m => key m=A)).card:ℝ) ≤
          (((range (B+1)).filter (fun m => q ∣ C*m)).card:ℝ) := by exact_mod_cast card_le_card hsub
      exact hcard.trans ((divisor_target_card_le hC hq0).trans
        (add_le_add (div_le_div_of_nonneg_left (by positivity) hT hq.le) le_rfl))
    · have hEmpty : Z.filter (fun m => key m=A) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro m hm
        obtain ⟨hmZ,hEq⟩ := mem_filter.mp hm
        have hM : T < (((key m).lcm r:ℕ):ℝ) := (mem_filter.mp hmZ).2
        rw [hEq] at hM
        exact hq hM
      rw [hEmpty,card_empty,Nat.cast_zero]
      positivity
  change (Z.card:ℝ) ≤ _
  calc
    _ = ∑ m ∈ Z,(1:ℝ) := by simp [nsmul_eq_mul]
    _ = ∑ A ∈ W, ∑ m ∈ Z.filter (fun m => key m=A),(1:ℝ) :=
      (sum_fiberwise_of_maps_to hmap _).symm
    _ = ∑ A ∈ W, ((Z.filter (fun m => key m=A)).card:ℝ) := by simp [nsmul_eq_mul]
    _ ≤ ∑ _A ∈ W,((C:ℝ)*B/T+1) := sum_le_sum hBound
    _ = _ := by simp [W,nsmul_eq_mul,card_powerset]; ring

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Complex MeasureTheory Set GoldbachSmoothWindow GoldbachSmoothMellin
open GoldbachPolynomialMinor205 (wave)

noncomputable section

def principalConvolution (X m : ℝ) : ℝ :=
  ∫ x : ℝ, scaledWeight X x * scaledWeight X (m-x)

private theorem scaledWeight_zero_outside {X : ℝ} (hX : 0 < X) {t : ℝ}
    (ht : t ∉ Icc X (2*X)) : scaledWeight X t = 0 := by
  apply weight_zero
  have ht' : t < X ∨ 2*X < t := by simpa only [mem_Icc,not_and_or,not_le] using ht
  rcases ht' with h | h
  · exact Or.inl ((div_le_iff₀ hX).mpr (by linarith))
  · exact Or.inr ((le_div_iff₀ hX).mpr (by linarith))

private theorem weight_product_integrable {X : ℝ} (hX : 0 < X) (m : ℝ) :
    Integrable (fun t => scaledWeight X t * scaledWeight X (m-t)) := by
  have hC : Continuous (scaledWeight X) :=
    (weight_smooth (n:=1)).continuous.comp (continuous_id.div_const X)
  apply (hC.mul (hC.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=X) (b:=2*X))
  intro t ht
  by_contra h
  exact ht (by simp [scaledWeight_zero_outside hX h])

theorem principal_convolution_floor {X m : ℝ} (hX : 0 < X)
    (hm : m ∈ Icc (5*X/2) (7*X/2)) :
    X/4 ≤ principalConvolution X m := by
  let a : ℝ := max (9*X/8) (m-15*X/8)
  let b : ℝ := min (15*X/8) (m-9*X/8)
  have hlen : X/4 ≤ b-a := by
    have hL := hm.1
    have hR := hm.2
    simp only [a,b,max_def,min_def]
    split_ifs <;> linarith
  have hprod (t : ℝ) : 0 ≤ scaledWeight X t*scaledWeight X (m-t) :=
    mul_nonneg (weight_range _).1 (weight_range _).1
  have h1 (t : ℝ) (ht : t ∈ Icc a b) :
      scaledWeight X t*scaledWeight X (m-t) = 1 := by
    have htt : 9*X/8≤t ∧ t≤15*X/8 := ⟨(le_max_left _ _).trans ht.1, ht.2.trans (min_le_left _ _)⟩
    have hss : 9 * X / 8 ≤ (m - t) ∧ (m - t) ≤ 15 * X / 8 := by
      have hA := (le_max_right (9*X/8) (m-15*X/8)).trans ht.1
      have hB := ht.2.trans (min_le_right (15*X/8) (m-9*X/8))
      exact ⟨by linarith only [hB],by linarith only [hA]⟩
    have hw (y : ℝ) (hy : 9*X/8≤y ∧ y≤15*X/8) : scaledWeight X y=1 := by
      apply weight_one
      exact ⟨(le_div_iff₀ hX).mpr (by linarith only [hy.1]),
        (div_le_iff₀ hX).mpr (by linarith only [hy.2])⟩
    rw [hw _ htt,hw _ hss,mul_one]
  have hI := weight_product_integrable hX m
  have hIcc : (∫ t in Icc a b, scaledWeight X t*scaledWeight X (m-t)) =
      b-a := by
    rw [setIntegral_congr_fun measurableSet_Icc h1,setIntegral_const,Measure.real,Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith only [hlen,hX]),smul_eq_mul,mul_one]
  calc
    _ ≤ b-a := hlen
    _ = ∫ t in Icc a b, scaledWeight X t*scaledWeight X (m-t) := hIcc.symm
    _ ≤ _ := integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall hprod) hI

theorem norm_full_arch_pair_le_principal {X : ℝ} (hX : 0 < X) {s z : ℂ}
    (hs : s.re ≤ 1) (hz : z.re ≤ 1) (m : ℝ) :
    ‖∫ t : ℝ, smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) s *
      smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) z * wave (-m*t)‖ ≤
      principalConvolution X m*X^(s.re-1)*X^(z.re-1) := by
  let w (t : ℝ) := scaledWeight X t*scaledWeight X (m-t)
  let A : ℝ := X^(s.re-1)*X^(z.re-1)
  have hw := weight_product_integrable hX m
  have hwA : Integrable (fun t => w t*A) := hw.mul_const A
  rw [arch_pair_full_eq hX]
  have hBound : ∀ᵐ x ∂(volume : Measure ℝ), ‖smoothDensity X s x * smoothDensity X z (m-x)‖ ≤ w x*A := by
    filter_upwards with x
    by_cases hx : x ∈ Icc X (2*X)
    · by_cases hy : m-x ∈ Icc X (2*X)
      · have hx0 := hX.trans_le hx.1
        have hy0 := hX.trans_le hy.1
        have hA₁ := Real.rpow_le_rpow_of_nonpos hX hx.1 (sub_nonpos.mpr hs)
        have hA₂ := Real.rpow_le_rpow_of_nonpos hX hy.1 (sub_nonpos.mpr hz)
        unfold smoothDensity
        simp only [norm_mul,Complex.norm_real,norm_cpow_eq_rpow_re_of_pos hx0,
          norm_cpow_eq_rpow_re_of_pos hy0,Complex.sub_re,Complex.one_re]
        have hW₁ : 0 ≤ scaledWeight X x := (weight_range (x/X)).1
        have hW₂ : 0 ≤ scaledWeight X (m-x) := (weight_range ((m-x)/X)).1
        rw [Real.norm_of_nonneg hW₁,Real.norm_of_nonneg hW₂]
        change scaledWeight X x * x^(s.re-1) * (scaledWeight X (m-x)*(m-x)^(z.re-1)) ≤ w x*A
        have hm : 0 ≤ w x := mul_nonneg (weight_range _).1 (weight_range _).1
        calc
          _ = w x*(x^(s.re-1)*(m-x)^(z.re-1)) := by unfold w; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (mul_le_mul hA₁ hA₂ (Real.rpow_nonneg hy0.le _) (Real.rpow_nonneg hX.le _)) hm
      · simp [smoothDensity_zero_outside hX z hy,w,scaledWeight_zero_outside hX hy]
    · simp [smoothDensity_zero_outside hX s hx,w,scaledWeight_zero_outside hX hx]
  calc
    _ ≤ ∫ x : ℝ, w x*A := norm_integral_le_of_norm_le hwA hBound
    _ = _ := by rw [integral_mul_const]; unfold principalConvolution A; ring

theorem full_arch_pair_pole_eq {X : ℝ} (hX : 0 < X) (m : ℝ) :
    (∫ t : ℝ, (smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) 1)^2 * wave (-m*t)) =
    (principalConvolution X m:ℂ) := by
  simp_rw [pow_two]
  rw [arch_pair_full_eq hX,principalConvolution]
  simp only [smoothDensity,sub_self,Complex.cpow_zero,mul_one,← Complex.ofReal_mul,integral_complex_ofReal]

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Complex MeasureTheory Set GoldbachSmoothMellin GoldbachSmoothWindow
open GoldbachPolynomialMinor205 (wave)
open scoped FourierTransform

private theorem norm_right_tail_le {R A : ℝ} (hR : 0 < R) (f : ℝ → ℂ)
    (h : ∀ t > R, ‖f t‖ ≤ A/|t|^2) :
    ‖∫ t in Ioi R,f t‖ ≤ A/R := by
  let g (t : ℝ) := A*t^(-2:ℝ)
  have hg : IntegrableOn g (Ioi R) := (integrableOn_Ioi_rpow_of_lt (by norm_num) hR).const_mul A
  have hPt : ∀ᵐ t ∂volume.restrict (Ioi R), ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htR : R<t := ht
    have hp : 0<t := hR.trans htR
    simpa only [g,abs_of_pos hp,Real.rpow_neg hp.le,Real.rpow_ofNat,div_eq_mul_inv] using h t htR
  refine (norm_integral_le_of_norm_le hg hPt).trans_eq ?_
  unfold g
  rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) hR]
  rw [show (-2:ℝ)+1 = -1 by norm_num,Real.rpow_neg_one]
  ring

theorem norm_integral_sub_center_le {R A : ℝ} (hR : 0 < R) {f : ℝ → ℂ} (hf : Integrable f)
    (h : ∀ t, R < |t| → ‖f t‖ ≤ A/|t|^2) :
    ‖(∫ t : ℝ,f t)-(∫ t in Icc (-R) R,f t)‖ ≤ 2*A/R := by
  have hs : (Icc (-R) R : Set ℝ)ᶜ = Iio (-R) ∪ Ioi R := by
    ext x
    simp only [mem_compl_iff,mem_Icc,not_and_or,not_le,mem_union,mem_Iio,mem_Ioi]
  rw [← setIntegral_compl measurableSet_Icc hf,hs]
  have hdis : Disjoint (Iio (-R)) (Ioi R) := by
    apply disjoint_left.mpr
    intro x hx hy
    have hx' : x< -R := hx
    have hy' : R<x := hy
    linarith
  rw [setIntegral_union hdis measurableSet_Ioi hf.integrableOn hf.integrableOn]
  have hp := norm_right_tail_le hR f (fun t ht =>
    h t (by rwa [abs_of_pos (hR.trans ht)]))
  have hn := norm_right_tail_le (A:=A) hR (fun t => f (-t)) (fun t ht => by
    simpa only [abs_neg] using h (-t) (by rwa [abs_neg,abs_of_pos (hR.trans ht)]))
  have hn' : ‖∫ t in Iio (-R),f t‖ ≤ A/R := by
    rw [integral_comp_neg_Ioi,integral_Iic_eq_integral_Iio] at hn
    exact hn
  exact (norm_add_le _ _).trans ((add_le_add hn' hp).trans_eq (by ring))

set_option maxHeartbeats 1800000 in
private theorem inverse_pair_integrable {f g : ℝ → ℂ} (hf : Integrable f)
    (hg : Integrable g) (hG : Integrable (𝓕 g)) (m : ℝ) :
    Integrable (fun t => (𝓕⁻ f) t*(𝓕⁻ g) t*wave (-m*t)) := by
  let F : ℝ → ℂ := 𝓕⁻ f
  let G : ℝ → ℂ := 𝓕⁻ g
  let e (t : ℝ) : ℂ := wave (-m*t)
  let H (t : ℝ) : ℂ := F t*G t*e t
  change Integrable H
  have hg' : Integrable G := by
    change Integrable (𝓕⁻ g)
    rw [show (𝓕⁻ g) = fun t => (𝓕 g) (-t) from funext (Real.fourierInv_eq_fourier_neg g)]
    exact hG.comp_neg
  have hC (k : ℝ → ℂ) (h : Integrable k) : Continuous (𝓕⁻ k) := by
    rw [show (𝓕⁻ k) = fun t => (𝓕 k) (-t) from funext (Real.fourierInv_eq_fourier_neg k)]
    exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ h).comp continuous_neg
  have he : Continuous e := by unfold e wave; fun_prop
  have hFc : Continuous F := hC f hf
  have hGc : Continuous G := hC g hg
  have hHc : Continuous H := (hFc.mul hGc).mul he
  let M : ℝ := ∫ t : ℝ, ‖f t‖
  have hM : Integrable (fun t : ℝ => M*‖G t‖) := hg'.norm.const_mul M
  refine MeasureTheory.Integrable.mono' hM hHc.aestronglyMeasurable ?_
  filter_upwards with t
  have hx : ‖e t‖ = 1 := by unfold e wave; exact Complex.norm_exp_ofReal_mul_I _
  have ht : ‖F t‖ ≤ M := by
    change ‖(𝓕⁻ f) t‖ ≤ _
    rw [Real.fourierInv_eq_fourier_neg]
    exact Real.norm_fourier_le_integral_norm f (-t)
  change ‖F t*G t*e t‖ ≤ M*‖G t‖
  simp only [norm_mul,hx,mul_one]
  exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)

set_option maxHeartbeats 1600000 in
theorem smooth_arc_to_full_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X R : ℝ}, 0 < X → 0 < R → ∀ (s z : ℂ), 0 ≤ s.re → s.re ≤ 1 →
      0 ≤ z.re → z.re ≤ 1 → |s.im| ≤ Real.pi*X*R → |z.im| ≤ Real.pi*X*R →
      ∀ (m : ℝ),
      let F (t : ℝ) := smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) s *
        smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) z * wave (-m*t)
      ‖(∫ t : ℝ,F t)-(∫ t in Icc (-R) R,F t)‖ ≤ C*X^(s.re-1)*X^(z.re-1)/R := by
  obtain ⟨K,hK,hKbound⟩ := smooth_high_frequency_bound
  refine ⟨2*K^2,by positivity,?_⟩
  intro X R hX hR s z hs hs' hz hz' hsi hzi m F
  have hFS : Integrable F := by
    have hf : Integrable (smoothDensity X s) := (smoothDensity_smooth hX s).continuous.integrable_of_hasCompactSupport
      (smoothDensity_compact hX s)
    have hg : Integrable (smoothDensity X z) := (smoothDensity_smooth hX z).continuous.integrable_of_hasCompactSupport
      (smoothDensity_compact hX z)
    have h := inverse_pair_integrable hf hg (integrable_fourier_smoothDensity hX z) m
    simp_rw [inverse_fourier_smoothDensity hX] at h
    exact h
  let A := K^2*X^(s.re-1)*X^(z.re-1)
  have hPt (t : ℝ) (ht : R < |t|) : ‖F t‖ ≤ A/|t|^2 := by
    have hπ : 0 < 2*Real.pi := by positivity
    have ht0 := hR.trans ht
    have hβ (u : ℂ) (hu : |u.im|≤Real.pi*X*R) : 2*|u.im|≤X*|2*Real.pi*t| := by
      rw [abs_mul,abs_of_pos hπ]
      nlinarith only [hu,mul_le_mul_of_nonneg_left ht.le (show 0≤Real.pi*X by positivity)]
    have hb (u : ℂ) (hu0 : 0≤u.re) (hu1 : u.re≤1) (hu : |u.im|≤Real.pi*X*R) :
        ‖smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) u‖ ≤ K*X^(u.re-1)/|t| := by
      have htne : t≠0 := abs_pos.mp ht0
      have h := hKbound hX (mul_ne_zero hπ.ne' htne) u hu0 hu1 (hβ u hu)
      rw [abs_mul,abs_of_pos hπ] at h
      refine h.trans (div_le_div_of_nonneg_left (by positivity) ht0 ?_)
      exact le_mul_of_one_le_left ht0.le (by linarith only [Real.pi_gt_three])
    have hW : ‖wave (-m*t)‖ = 1 := by unfold wave; exact Complex.norm_exp_ofReal_mul_I _
    dsimp only [F]
    simp only [norm_mul,hW,mul_one]
    refine (mul_le_mul (hb s hs hs' hsi) (hb z hz hz' hzi) (norm_nonneg _) (by positivity)).trans_eq ?_
    unfold A
    ring
  exact (norm_integral_sub_center_le hR hFS hPt).trans_eq (by unfold A; ring)

end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Complex MeasureTheory Set GoldbachSmoothMellin GoldbachSmoothWindow GoldbachTwistedMellin
open GoldbachPolynomialMinor205 (wave)
open scoped ContDiff Interval

set_option maxHeartbeats 1400000 in
/-- An ordinate dominating the angular contribution gives one inverse power of height. -/
theorem smooth_high_ordinate_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {X κ : ℝ}, 0 < X → ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 →
      0 < |s.im| → 4*X*|κ| ≤ |s.im| →
      ‖smoothTransform X (2*X) κ (scaledWeight X) s‖ ≤ C*X^s.re/|s.im| := by
  obtain ⟨K,hK,hW⟩ := scaledWeight_deriv_bound
  refine ⟨4*K+28,by positivity,?_⟩
  intro X κ hX s hs0 hs1 hγ hfreq
  let r := s.re-1
  let A := X^r
  let f (x : ℝ) : ℂ := ((scaledWeight X x*x^r:ℝ):ℂ)
  let df (x : ℝ) : ℂ :=
    ((deriv (scaledWeight X) x*x^r+scaledWeight X x*(r*x^(r-1)):ℝ):ℂ)
  let p (x : ℝ) := s.im*Real.log x+κ*x
  let dp (x : ℝ) := s.im/x+κ
  let ddp (x : ℝ) := -s.im/x^2
  let D := |s.im|/(4*X)
  let E := |s.im|/X^2
  let B := (K+1)*A/X
  have hX2 : X ≤ 2*X := by linarith
  have hD : 0 < D := div_pos hγ (by positivity)
  have hA : 0 ≤ A := Real.rpow_nonneg hX.le _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hWc : ContDiff ℝ 1 (scaledWeight X) := weight_smooth.comp (contDiff_id.div_const X)
  have hPos (x : ℝ) (hx : x ∈ Icc X (2*X)) : 0 < x := hX.trans_le hx.1
  have hf (x : ℝ) (hx : x ∈ Icc X (2*X)) : HasDerivAt f (df x) x := by
    have h := Real.hasDerivAt_rpow_const (p:=r) (Or.inl (hPos x hx).ne')
    simpa [f,df,add_comm,mul_comm] using
      (((hWc.differentiable_one x).hasDerivAt).mul h).ofReal_comp
  have hPow (e : ℝ) : ContinuousOn (fun x : ℝ => x^e) (Icc X (2*X)) :=
    fun x hx => (Real.continuousAt_rpow_const _ _ (Or.inl (hPos x hx).ne')).continuousWithinAt
  have hdf : ContinuousOn df (Icc X (2*X)) := by
    apply continuous_ofReal.comp_continuousOn
    exact ((hWc.continuous_deriv le_rfl).continuousOn.mul (hPow r)).add
      (hWc.continuous.continuousOn.mul (continuousOn_const.mul (hPow (r-1))))
  have hp (x : ℝ) (hx : x ∈ Icc X (2*X)) : HasDerivAt p (dp x) x := by
    have h := ((Real.hasDerivAt_log (hPos x hx).ne').const_mul s.im).add
      ((hasDerivAt_id x).const_mul κ)
    have he : dp x = s.im*x⁻¹+κ := by unfold dp; rw [div_eq_mul_inv]
    rw [he]
    convert h using 1
    funext t
    simp [p]
    ring
  have hdp (x : ℝ) (hx : x ∈ Icc X (2*X)) : HasDerivAt dp (ddp x) x := by
    have h := (((hasDerivAt_const x s.im).div (hasDerivAt_id x) (hPos x hx).ne')).add_const κ
    simpa [dp,ddp,neg_div] using h
  have hddp : ContinuousOn ddp (Icc X (2*X)) := by
    change ContinuousOn (fun t : ℝ => -s.im/t^2) (Icc X (2*X))
    exact continuousOn_const.div (show ContinuousOn (fun t : ℝ => t^2) (Icc X (2*X)) from
      continuousOn_id.pow 2) (fun x hx => pow_ne_zero 2 (hPos x hx).ne')
  have hr : r ≤ 0 := sub_nonpos.mpr hs1
  have hrn : |r| ≤ 1 := by rw [abs_of_nonpos hr]; dsimp [r]; linarith
  have hPx (x : ℝ) (hx : x ∈ Icc X (2*X)) : x^r ≤ A :=
    Real.rpow_le_rpow_of_nonpos hX hx.1 hr
  have hfb (x : ℝ) (hx : x ∈ Icc X (2*X)) : ‖f x‖ ≤ A := by
    have hx0 := hPos x hx
    have hw := weight_range (x/X)
    dsimp only [f]
    rw [norm_real,Real.norm_eq_abs,abs_mul,scaledWeight,abs_of_nonneg hw.1,
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) hw.2).trans (hPx x hx)
  have hdfb (x : ℝ) (hx : x ∈ Icc X (2*X)) : ‖df x‖ ≤ B := by
    have hx0 := hPos x hx
    have hp₁ := hPx x hx
    have hp₂ : x^(r-1) ≤ A/X := by
      rw [Real.rpow_sub hx0,Real.rpow_one]
      exact div_le_div₀ (by positivity) hp₁ hX hx.1
    have hw := weight_range (x/X)
    have hh : ‖scaledWeight X x‖ ≤ 1 := by
      rw [scaledWeight,Real.norm_of_nonneg hw.1]
      exact hw.2
    dsimp [df]
    rw [norm_real]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul,Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have h₁ := mul_le_mul (hW hX x) hp₁ (Real.rpow_nonneg hx0.le _) (div_nonneg hK hX.le)
    have h₂ := mul_le_mul hh (mul_le_mul hrn hp₂ (Real.rpow_nonneg hx0.le _) zero_le_one)
      (by positivity : 0≤‖r‖*x^(r-1)) zero_le_one
    rw [Real.norm_eq_abs] at h₁ h₂
    dsimp [B]
    linarith only [h₁,h₂,
      show K/X*A+1*(1*(A/X))=(K+1)*A/X by ring]
  have hdpb (x : ℝ) (hx : x ∈ Icc X (2*X)) : D ≤ |dp x| := by
    have hq : |s.im|/(2*X) ≤ |s.im/x| := by
      rw [abs_div,abs_of_pos (hPos x hx)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (hPos x hx) hx.2
    have hκ : |κ| ≤ D := (le_div_iff₀ (by positivity : 0 < 4*X)).mpr
      (by nlinarith only [hfreq])
    have hd : |s.im|/(2*X) = 2*D := by
      dsimp only [D]
      field_simp [hX.ne']
      ring
    have htriangle := abs_sub_abs_le_abs_sub (s.im/x) (-κ)
    rw [abs_neg,sub_neg_eq_add] at htriangle
    change D ≤ |s.im/x+κ|
    linarith only [hq,hκ,hd,htriangle]
  have hddpb (x : ℝ) (hx : x ∈ Icc X (2*X)) : |ddp x| ≤ E := by
    have hx0 := hPos x hx
    simp only [ddp,abs_div,abs_neg,abs_of_nonneg (sq_nonneg x)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hX) (pow_le_pow_left₀ hX.le hx.1 2)
  have hnorm := norm_oscillatory_integral_le hX2 hA hB hE hD f df p dp ddp
    hf hdf hp hdp hddp hfb hdfb hdpb hddpb
  have harch : smoothTransform X (2*X) κ (scaledWeight X) s =
      ∫ y in X..(2*X),f y*Complex.exp ((p y:ℂ)*I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hX2] at hy
    change (scaledWeight X y:ℂ) * density κ s y = f y*Complex.exp ((p y:ℂ)*I)
    rw [density_rpow_phase (hPos y hy)]
    dsimp [f,p,r]
    rw [Complex.ofReal_mul,mul_assoc]
  rw [harch]
  refine hnorm.trans ?_
  have hscale : X*A = X^s.re := by
    dsimp only [A,r]
    nth_rewrite 1 [← Real.rpow_one X]
    rw [← Real.rpow_add hX]
    congr 1
    ring
  calc
    _ = (4*K+28)*(X*A)/|s.im| := by
      dsimp only [D,E,B]
      field_simp [hX.ne',hγ.ne']
      ring
    _ ≤ _ := by rw [hscale]

private theorem smooth_transform_unit_norm_le {X : ℝ} (hX : 0 < X) {s : ℂ}
    (hs : s.re ≤ 1) (κ : ℝ) :
    ‖smoothTransform X (2*X) κ (scaledWeight X) s‖ ≤ X*X^(s.re-1) := by
  have hXX : X ≤ 2*X := by linarith
  unfold smoothTransform
  have hB (t : ℝ) (ht : t ∈ uIoc X (2*X)) :
      ‖(scaledWeight X t : ℂ)*density κ s t‖ ≤ X^(s.re-1) := by
    have ht' := uIoc_subset_uIcc ht
    rw [uIcc_of_le hXX] at ht'
    have ht₀ := hX.trans_le ht'.1
    have hw := weight_range (t/X)
    rw [norm_mul,norm_real,scaledWeight,Real.norm_of_nonneg hw.1,density,norm_mul,norm_phase,
      one_mul,norm_cpow_eq_rpow_re_of_pos ht₀,sub_re,one_re]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg ht₀.le _) hw.2).trans
      (Real.rpow_le_rpow_of_nonpos hX ht'.1 (sub_nonpos.mpr hs))
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hB).trans_eq ?_
  rw [abs_of_nonneg (sub_nonneg.mpr hXX)]
  ring

/-- A short Fourier window suppresses pairs with an ordinate exceeding its angular scale. -/
theorem arch_pair_window_high_ordinate_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {X R : ℝ}, 0 < X → 0 ≤ R → ∀ s z : ℂ,
      0 ≤ s.re → s.re ≤ 1 → z.re ≤ 1 → 8*Real.pi*X*R ≤ |s.im| → ∀ m : ℝ,
      ‖∫ t in Icc (-R) R,
        smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) s *
        smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) z * wave (-m*t)‖ ≤
        C*X*X^(s.re-1)*X^(z.re-1)*(X*R)/|s.im| := by
  obtain ⟨C,hC,hdecay⟩ := smooth_high_ordinate_bound
  refine ⟨2*C,by positivity,?_⟩
  intro X R hX hR s z hs₀ hs₁ hz hγ m
  by_cases he : R=0
  · simp [he]
  have hR₀ := hR.lt_of_ne (Ne.symm he)
  have hγ₀ : 0 < |s.im| := (show 0 < 8*Real.pi*X*R by positivity).trans_le hγ
  let F (u : ℂ) (t : ℝ) := smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) u
  have hF (t : ℝ) (ht : t ∈ Icc (-R) R) : ‖F s t*F z t*wave (-m*t)‖ ≤
      (C*X^s.re/|s.im|)*(X*X^(z.re-1)) := by
    have hfreq : 4*X*|2*Real.pi*t| ≤ |s.im| := by
      rw [abs_mul,abs_of_pos (show 0 < 2*Real.pi by positivity)]
      calc
        _ ≤ 4*X*(2*Real.pi*R) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (abs_le.mpr ht)
            (by positivity)) (by positivity)
        _ = 8*Real.pi*X*R := by ring
        _ ≤ _ := hγ
    have hw : ‖wave (-m*t)‖ = 1 := by unfold wave; exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul,hw,mul_one,norm_mul]
    exact mul_le_mul (hdecay hX s hs₀ hs₁ hγ₀ hfreq)
      (smooth_transform_unit_norm_le hX hz _) (norm_nonneg _) (by positivity)
  change ‖∫ t in Icc (-R) R,F s t*F z t*wave (-m*t)‖ ≤ _
  refine (norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top hF).trans_eq ?_
  rw [Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith only [hR])]
  have hscale : X^s.re = X*X^(s.re-1) := by
    nth_rewrite 2 [← Real.rpow_one X]
    rw [← Real.rpow_add hX]
    congr 1
    ring
  rw [hscale]
  ring

end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Complex MeasureTheory

/-- The higher of two ordinates suppresses the actual smooth pair on a short window. -/
theorem norm_smooth_pairIntegral_high_ordinate_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {X m : ℕ}, 0 < X → ∀ {i j : GlobalMode},
      i ∈ globalModesAt X → j ∈ globalModesAt X → ∀ {R : ℝ}, 0 ≤ R →
      let H := max |(spectralPoint i).im| |(spectralPoint j).im|
      8*Real.pi*(X:ℝ)*R ≤ H →
      ‖pairIntegral R m (smoothGlobalProfile X) i j‖ ≤
        C*(X:ℝ)*modeMass X i*modeMass X j*((X:ℝ)*R)/H := by
  obtain ⟨C,hC,hpair⟩ := arch_pair_window_high_ordinate_le
  refine ⟨C,hC,?_⟩
  intro X m hX i j hi hj R hR
  have hx : (0:ℝ) < X := by exact_mod_cast hX
  have oneSide {u v : GlobalMode} (hu : u ∈ globalModesAt X) (hv : v ∈ globalModesAt X)
      (hh : 8*Real.pi*(X:ℝ)*R ≤ |(spectralPoint u).im|) :
      ‖pairIntegral R m (smoothGlobalProfile X) u v‖ ≤
        C*(X:ℝ)*modeMass X u*modeMass X v*((X:ℝ)*R)/|(spectralPoint u).im| := by
    rw [smooth_pairIntegral_eq,norm_mul,norm_mul,norm_spectralCoefficient,norm_spectralCoefficient,
      modeMass_eq_spectral_power hX hu,modeMass_eq_spectral_power hX hv]
    have h₁ := spectralPoint_re_bounds hu
    have h₂ := spectralPoint_re_bounds hv
    refine (mul_le_mul_of_nonneg_left
      (hpair hx hR (spectralPoint u) (spectralPoint v) h₁.1 h₁.2 h₂.2 hh (m:ℝ))
      (by positivity)).trans_eq ?_
    ring
  dsimp only
  rcases le_total |(spectralPoint i).im| |(spectralPoint j).im| with hij | hji
  · rw [max_eq_right hij]
    intro h
    have hs : pairIntegral R m (smoothGlobalProfile X) i j =
        pairIntegral R m (smoothGlobalProfile X) j i := by
      unfold pairIntegral
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun _ => by ring)
    rw [hs]
    exact (oneSide hj hi h).trans_eq (by ring)
  · rw [max_eq_left hji]
    exact oneSide hi hj

end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Complex MeasureTheory
open GoldbachSmoothMellin GoldbachSmoothWindow
open GoldbachPolynomialMinor205 (wave)

noncomputable section

/-- The full smooth pair is the convolution of the two physical spectral
densities, with the coefficients of the original global modes. -/
def fullGlobalPair (X m : ℕ) (i j : GlobalMode) : ℂ :=
  (spectralCoefficient i*spectralCoefficient j) *
    ∫ x : ℝ, smoothDensity X (spectralPoint i) x *
      smoothDensity X (spectralPoint j) ((m:ℝ)-x)

theorem fullGlobalPair_eq_fourier {X m : ℕ} (hX : 0 < X) (i j : GlobalMode) :
    fullGlobalPair X m i j =
      (spectralCoefficient i*spectralCoefficient j) *
        ∫ t : ℝ, smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) (spectralPoint i) *
          smoothTransform X (2*X) (2*Real.pi*t) (scaledWeight X) (spectralPoint j) *
          wave (-(m:ℝ)*t) := by
  rw [fullGlobalPair,arch_pair_full_eq (by exact_mod_cast hX : (0:ℝ)<X)]

/-- A short window containing the ordinate scales can be extended to the
full pair with error proportional to the reciprocal radius. -/
theorem norm_fullGlobalPair_sub_smooth_pairIntegral_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X m : ℕ} {R : ℝ}, 0 < X → 0 < R →
      ∀ {i j : GlobalMode}, i ∈ globalModesAt X → j ∈ globalModesAt X →
      |(spectralPoint i).im| ≤ Real.pi*((X:ℝ)*R) →
      |(spectralPoint j).im| ≤ Real.pi*((X:ℝ)*R) →
      ‖fullGlobalPair X m i j-pairIntegral R m (smoothGlobalProfile X) i j‖ ≤
        C*((X:ℝ)/((X:ℝ)*R))*modeMass X i*modeMass X j := by
  obtain ⟨C,hC,hTail⟩ := smooth_arc_to_full_error
  refine ⟨C,hC,?_⟩
  intro X m R hX hR i j hi hj hγi hγj
  have hx : (0:ℝ) < X := by exact_mod_cast hX
  obtain ⟨hi₀,hi₁⟩ := spectralPoint_re_bounds hi
  obtain ⟨hj₀,hj₁⟩ := spectralPoint_re_bounds hj
  have ht := hTail hx hR (spectralPoint i) (spectralPoint j) hi₀ hi₁ hj₀ hj₁
    (by simpa only [mul_assoc] using hγi) (by simpa only [mul_assoc] using hγj) (m:ℝ)
  rw [fullGlobalPair_eq_fourier hX,smooth_pairIntegral_eq,← mul_sub,norm_mul,norm_mul,
    norm_spectralCoefficient,norm_spectralCoefficient,modeMass_eq_spectral_power hX hi,
    modeMass_eq_spectral_power hX hj]
  refine (mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq ?_
  field_simp [hx.ne',hR.ne']

theorem fullGlobalPair_none_none {X m : ℕ} (hX : 0 < X) :
    fullGlobalPair X m none none = (principalConvolution X m:ℂ) := by
  rw [fullGlobalPair_eq_fourier hX]
  have hc : spectralCoefficient none = 1 := by simp [spectralCoefficient]
  simpa only [hc,spectralPoint,one_mul,pow_two] using
    full_arch_pair_pole_eq (by exact_mod_cast hX : (0:ℝ)<X) (m:ℝ)

theorem fullGlobalPair_pole_floor {X m : ℕ} (hX : 0 < X)
    (hm₁ : (5/2:ℝ)*(X:ℝ) ≤ (m:ℝ)) (hm₂ : (m:ℝ) ≤ (7/2:ℝ)*(X:ℝ)) :
    (X:ℝ)/4 ≤ (fullGlobalPair X m none none).re := by
  rw [fullGlobalPair_none_none hX,Complex.ofReal_re]
  exact principal_convolution_floor (by exact_mod_cast hX) ⟨by linarith,by linarith⟩

/-- Every full pair is bounded by the pole pair with the appropriate
spectral masses. -/
theorem norm_fullGlobalPair_le_pole {X m : ℕ} (hX : 0 < X)
    {i j : GlobalMode} (hi : i ∈ globalModesAt X) (hj : j ∈ globalModesAt X) :
    ‖fullGlobalPair X m i j‖ ≤
      (fullGlobalPair X m none none).re*modeMass X i*modeMass X j := by
  have hx : (0:ℝ) < X := by exact_mod_cast hX
  rw [fullGlobalPair_none_none hX,Complex.ofReal_re,fullGlobalPair_eq_fourier hX,
    norm_mul,norm_mul,norm_spectralCoefficient,norm_spectralCoefficient,
    modeMass_eq_spectral_power hX hi,modeMass_eq_spectral_power hX hj]
  refine (mul_le_mul_of_nonneg_left
    (norm_full_arch_pair_le_principal hx (spectralPoint_re_bounds hi).2
      (spectralPoint_re_bounds hj).2 (m:ℝ)) (by positivity)).trans_eq ?_
  ring

theorem principal_convolution_le_scale {X m : ℝ} (hX : 0 < X) :
    principalConvolution X m ≤ X := by
  let f (x : ℝ) := scaledWeight X x*scaledWeight X (m-x)
  have hw : Continuous (scaledWeight X) :=
    (weight_smooth (n:=1)).continuous.comp (continuous_id.div_const X)
  have hf : IntegrableOn f (Set.Icc X (2*X)) :=
    (hw.mul (hw.comp (continuous_const.sub continuous_id))).continuousOn.integrableOn_compact
      isCompact_Icc
  have hOne : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Icc X (2*X)) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hsupp : ∀ x, x ∉ Set.Icc X (2*X) → f x = 0 := by
    intro x hx
    have h := congrArg Complex.re (smoothDensity_zero_outside hX (1:ℂ) hx)
    have hw₀ : scaledWeight X x = 0 := by
      simpa only [smoothDensity,sub_self,Complex.cpow_zero,mul_one,Complex.ofReal_re,Complex.zero_re] using h
    simp only [f,hw₀,zero_mul]
  change (∫ x : ℝ,f x) ≤ X
  calc
    _ = ∫ x in Set.Icc X (2*X),f x := (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
    _ ≤ ∫ _ in Set.Icc X (2*X),(1:ℝ) := setIntegral_mono_on hf hOne measurableSet_Icc
      (fun x _ => mul_le_one₀ (weight_range _).2 (weight_range _).1 (weight_range _).2)
    _ = _ := by
      rw [setIntegral_const,Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith),
        smul_eq_mul,mul_one]
      ring

theorem norm_fullGlobalPair_le_mass {X m : ℕ} (hX : 0 < X)
    {i j : GlobalMode} (hi : i ∈ globalModesAt X) (hj : j ∈ globalModesAt X) :
    ‖fullGlobalPair X m i j‖ ≤ (X:ℝ)*modeMass X i*modeMass X j := by
  have hp : (fullGlobalPair X m none none).re ≤ (X:ℝ) := by
    rw [fullGlobalPair_none_none hX,Complex.ofReal_re]
    exact principal_convolution_le_scale (by exact_mod_cast hX)
  exact (norm_fullGlobalPair_le_pole hX hi hj).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (modeMass_nonneg X i))
      (modeMass_nonneg X j))

/-- The full convolution gains a third power of the total ordinate. -/
theorem norm_fullGlobalPair_high_ordinate_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {X m : ℕ}, 0 < X →
      (5/2:ℝ)*(X:ℝ) ≤ (m:ℝ) → (m:ℝ) ≤ (7/2:ℝ)*(X:ℝ) →
      ∀ {i j : GlobalMode}, i ∈ globalModesAt X → j ∈ globalModesAt X →
      let H := |(spectralPoint i).im|+|(spectralPoint j).im|
      1 ≤ H → ‖fullGlobalPair X m i j‖ ≤
        C*(X:ℝ)*modeMass X i*modeMass X j*H^(-1/3:ℝ) := by
  obtain ⟨C,hC,hFull⟩ := norm_smoothDensity_convolution_le
  refine ⟨C,hC,?_⟩
  intro X m hX hm₁ hm₂ i j hi hj
  dsimp only
  intro hH
  have hx : (0:ℝ) < X := by exact_mod_cast hX
  obtain ⟨hi₀,hi₁⟩ := spectralPoint_re_bounds hi
  obtain ⟨hj₀,hj₁⟩ := spectralPoint_re_bounds hj
  rw [fullGlobalPair,norm_mul,norm_mul,norm_spectralCoefficient,norm_spectralCoefficient,
    modeMass_eq_spectral_power hX hi,modeMass_eq_spectral_power hX hj]
  refine (mul_le_mul_of_nonneg_left
    (hFull hx hm₁ hm₂ (spectralPoint i) (spectralPoint j) hi₀ hi₁ hj₀ hj₁ hH)
    (by positivity)).trans_eq ?_
  ring

/-- When an ordinate exceeds half the separating power scale, the full pair
has a negative power saving relative to the pole pair in the central window. -/
theorem norm_fullGlobalPair_high_scale_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {η : ℝ} {X m : ℕ}, 0 < X →
      (5/2:ℝ)*(X:ℝ) ≤ (m:ℝ) → (m:ℝ) ≤ (7/2:ℝ)*(X:ℝ) → 2 ≤ (X:ℝ)^η →
      ∀ {i j : GlobalMode}, i ∈ globalModesAt X → j ∈ globalModesAt X →
      (X:ℝ)^η/2 ≤ max |(spectralPoint i).im| |(spectralPoint j).im| →
      ‖fullGlobalPair X m i j‖ ≤ C*(fullGlobalPair X m none none).re*
        modeMass X i*modeMass X j*(X:ℝ)^(-(η/3)) := by
  obtain ⟨A,hA,hFull⟩ := norm_fullGlobalPair_high_ordinate_le
  refine ⟨4*A*(2:ℝ)^(1/3:ℝ),by positivity,?_⟩
  intro η X m hX hm₁ hm₂ hScale i j hi hj hH
  let H := |(spectralPoint i).im|+|(spectralPoint j).im|
  let M := (X:ℝ)^η/2
  have hM : 1 ≤ M := by dsimp only [M]; linarith
  have hMH : M ≤ H := hH.trans (max_le (by dsimp only [H]; linarith [abs_nonneg (spectralPoint j).im])
    (by dsimp only [H]; linarith [abs_nonneg (spectralPoint i).im]))
  have hX₀ : 0 < (X:ℝ) := by exact_mod_cast hX
  have hPole := fullGlobalPair_pole_floor hX hm₁ hm₂
  have hPole' : (X:ℝ) ≤ 4*(fullGlobalPair X m none none).re := by linarith
  have hHp : H^(-1/3:ℝ) ≤ M^(-1/3:ℝ) :=
    Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hM) hMH (by norm_num)
  have hMp : M^(-1/3:ℝ) = (2:ℝ)^(1/3:ℝ)*(X:ℝ)^(-(η/3)) := by
    dsimp only [M]
    rw [Real.div_rpow (by positivity) (by norm_num),← Real.rpow_mul hX₀.le,
      show η*(-1/3)=-(η/3) by ring,
      show (-1/3:ℝ)=-(1/3) by ring,Real.rpow_neg (by norm_num : (0:ℝ)≤2),
      div_inv_eq_mul,mul_comm]
  calc
    _ ≤ A*(X:ℝ)*modeMass X i*modeMass X j*H^(-1/3:ℝ) :=
      hFull hX hm₁ hm₂ hi hj (hM.trans hMH)
    _ ≤ A*(X:ℝ)*modeMass X i*modeMass X j*M^(-1/3:ℝ) :=
      mul_le_mul_of_nonneg_left hHp (mul_nonneg (mul_nonneg
        (mul_nonneg hA.le (Nat.cast_nonneg X)) (modeMass_nonneg X i)) (modeMass_nonneg X j))
    _ ≤ A*(4*(fullGlobalPair X m none none).re)*modeMass X i*modeMass X j*M^(-1/3:ℝ) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hPole' hA.le) (modeMass_nonneg X i))
        (modeMass_nonneg X j)) (by positivity)
    _ = _ := by rw [hMp]; ring

end
end GoldbachSignedPairs


end

section

namespace GoldbachSignedPairs

open Finset DirichletCharacter Filter Complex Goldbach GoldbachTwistedMellin GoldbachConductorZeros GoldbachWeightedMajorResidual
open GoldbachWeightedException (cutoff)
open scoped Classical

noncomputable section

/-- A source character, lifted to the common modulus used for a target. -/
def liftedSpectralCharacter (q : ℕ) (i : GlobalMode) : DirichletCharacter ℂ q :=
  if h : globalLevel i ∣ q then changeLevel h (globalSourceCharacter i) else 1

theorem liftedSpectralCharacter_conductor {q : ℕ} [NeZero q] {X : ℕ} {i : GlobalMode}
    (hi : i ∈ globalModesAt X) (h : globalLevel i ∣ q) :
    (liftedSpectralCharacter q i).conductor = globalLevel i := by
  simp only [liftedSpectralCharacter,dite_eq_left h,conductor_changeLevel]
  exact globalSourceCharacter_isPrimitive hi

theorem globalPairConductor_eq_lifted {q : ℕ} [NeZero q] {i j : GlobalMode}
    (hi : globalLevel i ∣ q) (hj : globalLevel j ∣ q) :
    globalPairConductor i j = (liftedSpectralCharacter q i*liftedSpectralCharacter q j).conductor := by
  let r := globalLevel i
  let s := globalLevel j
  let L := r.lcm s
  let a := (globalSourceCharacter i)⁻¹
  let b := (globalSourceCharacter j)⁻¹
  have hd : L ∣ q := Nat.lcm_dvd hi hj
  have ha : changeLevel hd (a.mul b) = changeLevel hi a*changeLevel hj b := by
    change changeLevel hd
      (changeLevel (Nat.dvd_lcm_left r s) a*changeLevel (Nat.dvd_lcm_right r s) b) = _
    rw [map_mul, ← changeLevel_trans a (Nat.dvd_lcm_left r s) hd,
      ← changeLevel_trans b (Nat.dvd_lcm_right r s) hd]
  calc
    _ = (a.mul b).conductor := rfl
    _ = (changeLevel hd (a.mul b)).conductor := (conductor_changeLevel _ hd).symm
    _ = _ := by
      rw [ha]
      simp only [liftedSpectralCharacter,dite_eq_left hi,dite_eq_left hj,a,b,map_inv,← mul_inv,
        conductor_inv]

theorem globalPairConductor_none_left {X : ℕ} {i : GlobalMode} (hi : i ∈ globalModesAt X) :
    globalPairConductor none i = globalLevel i := by
  let q := globalLevel i
  let _ : NeZero q := ⟨(globalLevel_pos hi).ne'⟩
  rw [globalPairConductor_eq_lifted (q:=q) (by simp [globalLevel]) (dvd_refl q)]
  have h : liftedSpectralCharacter q none = 1 := by
    unfold liftedSpectralCharacter
    rw [dite_eq_left (show globalLevel none ∣ q from one_dvd q)]
    exact changeLevel_one (one_dvd q)
  rw [h,one_mul]
  exact liftedSpectralCharacter_conductor hi (dvd_refl q)

theorem globalPairConductor_none_right {X : ℕ} {i : GlobalMode} (hi : i ∈ globalModesAt X) :
    globalPairConductor i none = globalLevel i := by
  let q := globalLevel i
  let _ : NeZero q := ⟨(globalLevel_pos hi).ne'⟩
  rw [globalPairConductor_eq_lifted (q:=q) (dvd_refl q) (by simp [globalLevel])]
  have h : liftedSpectralCharacter q none = 1 := by
    unfold liftedSpectralCharacter
    rw [dite_eq_left (show globalLevel none ∣ q from one_dvd q)]
    exact changeLevel_one (one_dvd q)
  rw [h,mul_one]
  exact liftedSpectralCharacter_conductor hi (dvd_refl q)

theorem liftedSpectralCharacter_zero_and_order {q X : ℕ} [NeZero q] {i : GlobalMode}
    (hi : i ∈ globalModesAt X) (hn : i ≠ none) (h : globalLevel i ∣ q) :
    regularizedL (liftedSpectralCharacter q i) (spectralPoint i) = 0 ∧
      analyticOrderNatAt (regularizedL (liftedSpectralCharacter q i)) (spectralPoint i) = modeOrder i := by
  rcases i with _ | ⟨r,χ,z⟩
  · exact (hn rfl).elim
  obtain ⟨hr,_,_,hz⟩ := (mem_globalModesAt_zero χ z).mp hi
  let _ : NeZero r := ⟨(Nat.zero_lt_one.trans_le hr).ne'⟩
  have hf : z ∈ (exceptionalZeros χ (heightCut (X:ℝ))).filter (shortNearZero X r) := by
    simpa only [globalShortZeros,dite_eq_left (NeZero.ne r)] using hz
  obtain ⟨hβ,_,hZ⟩ := ((mem_exceptionalZeros χ _ z).mp (mem_filter.mp hf).1)
  have hp : 0 < z.re := by linarith only [hβ]
  have h1 : z ≠ 1 := fun e => regularizedL_ne_zero_at_one χ (e ▸ hZ)
  have hd : r ∣ q := h
  have hl : liftedSpectralCharacter q (some ⟨r,χ,z⟩) = changeLevel hd χ := by
    simp only [liftedSpectralCharacter,dite_eq_left h,globalSourceCharacter]
    rfl
  rw [hl]
  change regularizedL (changeLevel hd χ) z = 0 ∧
    analyticOrderNatAt (regularizedL (changeLevel hd χ)) z =
      modeOrder (some ⟨r,χ,z⟩)
  exact ⟨(changeLevel_regularized_zero_iff hd χ hp h1).mpr hZ,
    by rw [changeLevel_regularized_order hd χ hp h1]
       simp only [modeOrder,dite_eq_left (NeZero.ne r)]⟩

theorem modeMass_le_conductor_power {X q : ℕ} {i : GlobalMode}
    (hX : 0 < X) (hq : 0 < q) (hi : i ∈ globalModesAt X)
    (hBound : (q:ℝ) ≤ (X:ℝ)^(81/400:ℝ)) :
    modeMass X i ≤ (modeOrder i:ℝ)*(q:ℝ)^((493/100:ℝ)*((spectralPoint i).re-1)) := by
  have hx : (0:ℝ) < X := by exact_mod_cast hX
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hX1 : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hβ : (spectralPoint i).re ≤ 1 := (spectralPoint_re_bounds hi).2
  have hp : (493/100:ℝ)*((spectralPoint i).re-1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sub_nonpos.mpr hβ)
  rw [modeMass_eq_spectral_power hX hi]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    _ ≤ (X:ℝ)^((81/400:ℝ)*((493/100:ℝ)*((spectralPoint i).re-1))) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith only [hβ])
    _ = ((X:ℝ)^(81/400:ℝ))^((493/100:ℝ)*((spectralPoint i).re-1)) :=
      Real.rpow_mul hx.le _ _
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hq' hBound hp

def massSquareByClass (q K X : ℕ) (S : Finset GlobalMode) : ℝ :=
  let key := fun i => conductorClass K (liftedSpectralCharacter q i)
  ∑ c ∈ S.image key,(∑ i ∈ S.filter (fun j => key j=c), modeMass X i)^2

theorem global_small_product_mass_le {q K X : ℕ} [NeZero q]
    (S : Finset GlobalMode) (hDiv : ∀ i ∈ S, globalLevel i ∣ q) :
    (∑ p ∈ (S ×ˢ S).filter (fun p => globalPairConductor p.1 p.2 ≤ K),
      modeMass X p.1*modeMass X p.2) ≤ massSquareByClass q K X S := by
  have hEq : (S ×ˢ S).filter (fun p => globalPairConductor p.1 p.2 ≤ K) =
      (S ×ˢ S).filter (fun p =>
        (liftedSpectralCharacter q p.1*liftedSpectralCharacter q p.2).conductor ≤ K) := by
    apply filter_congr
    intro p hp
    obtain ⟨hi,hj⟩ := mem_product.mp hp
    rw [globalPairConductor_eq_lifted (hDiv _ hi) (hDiv _ hj)]
  have he :
      (∑ p ∈ (S ×ˢ S).filter (fun p =>
        (liftedSpectralCharacter q p.1*liftedSpectralCharacter q p.2).conductor ≤ K),
        modeMass X p.1 * modeMass X p.2) =
      ∑ i ∈ S, ∑ j ∈ S.filter (fun j =>
        (liftedSpectralCharacter q i*liftedSpectralCharacter q j).conductor ≤ K),
        modeMass X i*modeMass X j := by
    rw [sum_filter,sum_product]
    simp only [sum_filter]
  rw [hEq,he]
  exact small_product_pair_mass_le (K:=K) S (liftedSpectralCharacter q)
    (modeMass X) (fun i _ => modeMass_nonneg X i)

theorem level_dvd_classModulus {m C : ℕ} {S : Finset GlobalMode} {i : GlobalMode}
    (hi : i ∈ divisorClass S globalLevel C m) :
    globalLevel i ∣ classModulus S globalLevel C m :=
  Finset.dvd_lcm hi

/-- The common modulus can be required to be at most X^(81/400), with a power
bound on the resulting additional exception count. -/
theorem eventually_classModulus_exception_card_le {C : ℕ} (hC : 0 < C) (L : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ X : ℕ in atTop,
      (((range (4*X+1)).filter (fun m =>
        (X:ℝ)^(81/400:ℝ) < (classModulus (cappedGlobalModes X L) globalLevel C m:ℝ))).card:ℝ)
      ≤ A*(X:ℝ)^(319/400:ℝ) := by
  obtain ⟨N,hN⟩ := eventually_capped_mode_card_bounded L
  refine ⟨(2:ℝ)^N*(4*(C:ℝ)+1),by positivity,?_⟩
  filter_upwards [hN,eventually_ge_atTop (1:ℕ)] with X hNX hX
  have hx1 : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hx0 : (0:ℝ) < X := zero_lt_one.trans_le hx1
  have hT := Real.rpow_pos_of_pos hx0 (81/400:ℝ)
  have hp := large_classModulus_card_le (cappedGlobalModes X L) globalLevel (B:=4*X) hC hT
  refine hp.trans ?_
  have heq : (C:ℝ)*((4*X:ℕ):ℝ)/(X:ℝ)^(81/400:ℝ) =
      (4*(C:ℝ))*(X:ℝ)^(319/400:ℝ) := by
    push_cast
    calc
      _ = (4*(C:ℝ))*((X:ℝ)/(X:ℝ)^(81/400:ℝ)) := by ring
      _ = (4*(C:ℝ))*((X:ℝ)^(1:ℝ)/(X:ℝ)^(81/400:ℝ)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub hx0]; norm_num
  rw [heq]
  have hpow := pow_le_pow_right₀ (show (1:ℝ)≤2 by norm_num) hNX
  have h1 := Real.one_le_rpow hx1 (show (0:ℝ)≤319/400 by norm_num)
  calc
    _ ≤ (2:ℝ)^N*((4*(C:ℝ))*(X:ℝ)^(319/400:ℝ)+1) := by gcongr
    _ ≤ (2:ℝ)^N*((4*(C:ℝ))*(X:ℝ)^(319/400:ℝ)+(X:ℝ)^(319/400:ℝ)) := by gcongr
    _ = _ := by ring

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Complex Finset Filter Topology GoldbachWeightedMajorResidual
open Conjectures.Goldbach.TwistedGoldbachSingularSeries
open GoldbachWeightedException (cutoff)
open scoped Classical

noncomputable section

def globalPairSeries (m : ℕ) (i j : GlobalMode) : ℂ :=
  ∑' d : ℕ, globalPairCoefficient m d i j

def denominatorCap (X : ℕ) (η : ℝ) (i j : GlobalMode) : ℝ :=
  ((globalLevel i).lcm (globalLevel j):ℝ)*(X:ℝ)^(η/2)

def smoothDenominatorSum (X m : ℕ) (i j : GlobalMode) : ℂ :=
  ∑ d ∈ Icc 1 (cutoff X), globalPairCoefficient m d i j*
    pairIntegral (arcRadius X d) m (smoothGlobalProfile X) i j

theorem norm_globalPairSeries_le {X m : ℕ} (hm : 0 < m) {i j : GlobalMode}
    (hi : i ∈ globalModesAt X) (hj : j ∈ globalModesAt X) :
    ‖globalPairSeries m i j‖ ≤ globalOrdinarySingularSeries m := by
  let _ : NeZero (globalLevel i) := ⟨(globalLevel_pos hi).ne'⟩
  let _ : NeZero (globalLevel j) := ⟨(globalLevel_pos hj).ne'⟩
  simp only [globalPairSeries,globalPairCoefficient_eq_coefficient,globalOrdinarySingularSeries]
  exact infinite_domination (globalSourceCharacter_isPrimitive hi).inv
    (globalSourceCharacter_isPrimitive hj).inv m hm

theorem globalPairCoefficient_zero (m : ℕ) (i j : GlobalMode) :
    globalPairCoefficient m 0 i j = 0 := by simp [globalPairCoefficient]

theorem modeTransitionScale_eq (i : GlobalMode) :
    modeTransitionScale i = (globalLevel i:ℝ)*(1+|(spectralPoint i).im|) := by
  rcases i with _ | ⟨r,χ,z⟩
  · simp [modeTransitionScale,globalLevel,spectralPoint]
  · rfl

theorem eventually_denominatorCap_le_cutoff {η : ℝ} (hη : 0 < η) (K : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ i ∈ globalModesAt X, ∀ j ∈ globalModesAt X,
      globalPairConductor i j ≤ K →
      modeTransitionScale i < (cutoff X:ℝ)/(X:ℝ)^η →
      denominatorCap X η i j ≤ (cutoff X:ℝ) := by
  have hLim : Tendsto (fun X : ℕ => (X:ℝ)^(η/2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hη)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hLim.eventually_ge_atTop (K:ℝ),eventually_ge_atTop (1:ℕ)] with X hpow hX i hi j hj hc ht
  have hx : (0:ℝ) < X := by exact_mod_cast (show 0 < X from hX)
  have hr : (0:ℝ) < globalLevel i := by exact_mod_cast globalLevel_pos hi
  have hL : ((globalLevel i).lcm (globalLevel j):ℝ) ≤ (K:ℝ)*(globalLevel i:ℝ) := by
    exact_mod_cast (globalPair_lcm_le_of_conductor_le hi hj hc).1
  have hav := (le_mul_of_one_le_right hr.le (le_add_of_nonneg_right (abs_nonneg (spectralPoint i).im)))
  rw [modeTransitionScale_eq] at ht
  have hlt := (lt_div_iff₀ (Real.rpow_pos_of_pos hx η)).mp (hav.trans_lt ht)
  unfold denominatorCap
  calc
    _ ≤ ((K:ℝ)*(globalLevel i:ℝ))*(X:ℝ)^(η/2) :=
      mul_le_mul_of_nonneg_right hL (by positivity)
    _ ≤ ((X:ℝ)^(η/2)*(globalLevel i:ℝ))*(X:ℝ)^(η/2) := by gcongr
    _ = (globalLevel i:ℝ)*(X:ℝ)^η := by
      rw [mul_comm ((X:ℝ)^(η/2)) _,mul_assoc,← Real.rpow_add hx,add_halves]
    _ ≤ _ := hlt.le

private theorem norm_cap_sum_sub_series_le {η C : ℝ} {X m : ℕ} {i j : GlobalMode}
    (hm : 0 < m) (hi : i ∈ globalModesAt X) (hj : j ∈ globalModesAt X)
    (hC : (∑' d : ℕ, if denominatorCap X η i j < (d:ℝ) then ‖globalPairCoefficient m d i j‖ else 0) ≤ C)
    (hcap : denominatorCap X η i j ≤ (cutoff X:ℝ)) :
    ‖(∑ d ∈ (Icc 1 (cutoff X)).filter (fun d : ℕ => (d:ℝ) ≤ denominatorCap X η i j),
        globalPairCoefficient m d i j) - globalPairSeries m i j‖ ≤ C := by
  let T := denominatorCap X η i j
  let D := (Icc 1 (cutoff X)).filter (fun d : ℕ => (d:ℝ) ≤ T)
  let a (d : ℕ) := globalPairCoefficient m d i j
  have hn : Summable (fun d : ℕ => ‖a d‖) := summable_norm_globalPairCoefficient hi hj hm
  have hf := hn.of_norm
  have hs := hf.sum_add_tsum_compl (s:=D)
  change ‖(∑ d ∈ D,a d)-(∑' d : ℕ,a d)‖ ≤ C
  rw [← hs,sub_add_cancel_left,norm_neg]
  refine (norm_tsum_le_tsum_norm (hn.subtype _)).trans ?_
  rw [tsum_subtype ((↑D : Set ℕ)ᶜ) (fun d : ℕ => ‖a d‖)]
  have heq : Set.indicator (↑D : Set ℕ)ᶜ (fun d => ‖a d‖) =
      fun d : ℕ => if T < (d:ℝ) then ‖a d‖ else 0 := by
    funext d
    by_cases hd : d=0
    · subst d
      simp [a,globalPairCoefficient_zero]
    have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hd
    rw [Set.indicator_apply]
    have hD : d ∈ D ↔ (d:ℝ) ≤ T := by
      simp only [D,mem_filter,mem_Icc,hd1,true_and]
      exact and_iff_right_of_imp (fun h => by exact_mod_cast h.trans hcap)
    have hc : d ∈ (↑D : Set ℕ)ᶜ ↔ T < (d:ℝ) := by
      simp only [Set.mem_compl_iff,Finset.mem_coe,hD,not_le]
    simp only [hc]
  rw [heq]
  exact hC

set_option maxHeartbeats 4800000 in
/-- Each pair below the separated cutoff has the complete singular-series
coefficient and the full physical convolution, up to a uniform power error. -/
theorem eventually_norm_low_smoothDenominatorSum_sub_full_le {η : ℝ} (hη : 0 < η) {K : ℕ}
    (hK : 0 < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop, ∀ m : ℕ, 0 < m → m ≤ 4*X → Even m →
      ∀ i ∈ globalModesAt X, ∀ j ∈ globalModesAt X, globalPairConductor i j ≤ K →
        modeTransitionScale i < (cutoff X:ℝ)/(X:ℝ)^η →
        modeTransitionScale j < (cutoff X:ℝ)/(X:ℝ)^η →
        ‖smoothDenominatorSum X m i j-globalPairSeries m i j*fullGlobalPair X m i j‖ ≤
          C*(X:ℝ)*globalOrdinarySingularSeries m*(X:ℝ)^(-(η/16))*modeMass X i*modeMass X j := by
  obtain ⟨A,hA,hAbs⟩ := globalPairCoefficient_absolute_le
  obtain ⟨B,hB,hTail⟩ := globalPairCoefficient_absolute_tail_finite hη
  obtain ⟨B',hB',hTail'⟩ := globalPairCoefficient_absolute_tail hη
  obtain ⟨E,hE,hErr⟩ := norm_fullGlobalPair_sub_smooth_pairIntegral_le
  obtain ⟨c,hc,hS⟩ := globalOrdinarySingularSeries_pos_uniform
  refine ⟨B+4*(K:ℝ)*E*A+B',by positivity,?_⟩
  filter_upwards [eventually_denominatorCap_le_cutoff hη K,
    eventually_globalPair_adaptiveArcRadius_low hη hK, eventually_ge_atTop (1:ℕ)]
    with X hcap hRadius hX m hm hmX he i hi j hj hcK hLi hLj
  let S := globalOrdinarySingularSeries m
  let T := denominatorCap X η i j
  let Q := Icc 1 (cutoff X)
  let D := Q.filter (fun d : ℕ => (d:ℝ) ≤ T)
  let U := Q.filter (fun d : ℕ => T < (d:ℝ))
  let a (d : ℕ) := globalPairCoefficient m d i j
  let V (d : ℕ) := pairIntegral (arcRadius X d) m (smoothGlobalProfile X) i j
  let W := fullGlobalPair X m i j
  let u := modeMass X i
  let v := modeMass X j
  let b := (X:ℝ)^(-(η/16))
  have hX0 : 0 < X := hX
  have hx : (0:ℝ) < X := by exact_mod_cast hX0
  have hx' : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hu : 0 ≤ u := modeMass_nonneg _ _
  have hv : 0 ≤ v := modeMass_nonneg _ _
  have hS0 : 0 ≤ S := (hc.trans (hS m hm he)).le
  have hA' : (∑ d ∈ D, ‖a d‖) ≤ A*S := hAbs hm he hi hj D
  have hBcap : (∑ d ∈ U, ‖a d‖) ≤ B*S*b := hTail hm hmX he hi hj Q
  have hBseries : ‖(∑ d ∈ D,a d)-globalPairSeries m i j‖ ≤ B'*S*b := by
    apply norm_cap_sum_sub_series_le hm hi hj _ (hcap i hi j hj hcK hLi)
    convert hTail' hm hmX he hi hj (fun _ => True) using 1
    apply tsum_congr
    intro d
    by_cases hd : denominatorCap X η i j < (d:ℝ)
    · have hd' : ((globalLevel i).lcm (globalLevel j):ℝ)*(X:ℝ)^(η/2) < (d:ℝ) := hd
      simp only [hd,hd',true_and,ite_true]
    · have hd' : ¬(((globalLevel i).lcm (globalLevel j):ℝ)*(X:ℝ)^(η/2) < (d:ℝ)) := hd
      simp only [hd,hd',false_and,ite_false]
  have hU : ‖∑ d ∈ U,a d*V d‖ ≤ B*S*b*((X:ℝ)*u*v) := calc
    _ ≤ ∑ d ∈ U, ‖a d*V d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ U, ‖a d‖*((X:ℝ)*u*v) := by
      apply sum_le_sum
      intro d _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_smooth_pairIntegral_le hX0 hi hj _) (norm_nonneg _)
    _ = _ := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hBcap (by positivity)
  have hDpt (d : ℕ) (hd : d ∈ D) : ‖V d-W‖ ≤ (4*(K:ℝ)*E)*(X:ℝ)*b*u*v := by
    have hd0 : 0 < d := (mem_Icc.mp (mem_filter.mp hd).1).1
    have hdT : (d:ℝ) ≤ T := (mem_filter.mp hd).2
    obtain ⟨hγi,hr⟩ := hRadius hi hj hcK (Or.inl rfl) hd0 hdT
      (by simpa only [modeTransitionScale_eq] using hLi)
    obtain ⟨hγj,_⟩ := hRadius hi hj hcK (Or.inr rfl) hd0 hdT
      (by simpa only [modeTransitionScale_eq] using hLj)
    simp only [adaptiveArcRadius_eq_arcRadius] at hγi hγj hr
    have hr0 : 0 < (X:ℝ)*arcRadius X d :=
      (div_pos (Real.rpow_pos_of_pos hx _) (by positivity)).trans_le hr
    have hR : 0 < arcRadius X d := pos_of_mul_pos_right hr0 hx.le
    have hInv : (X:ℝ)/((X:ℝ)*arcRadius X d) ≤ (4*(K:ℝ))*(X:ℝ)*b := calc
      _ ≤ (X:ℝ)/((X:ℝ)^(η/2)/(4*(K:ℝ))) :=
        div_le_div_of_nonneg_left hx.le (by positivity) hr
      _ = (4*(K:ℝ))*(X:ℝ)*(X:ℝ)^(-(η/2)) := by
        rw [div_div_eq_mul_div,div_eq_mul_inv,← Real.rpow_neg hx.le]
        ring
      _ ≤ _ := by
        have ht : (X:ℝ)^ (-(η/2)) ≤ b :=
          Real.rpow_le_rpow_of_exponent_le hx' (by linarith only [hη])
        exact mul_le_mul_of_nonneg_left ht (by positivity)
    rw [norm_sub_rev]
    exact (hErr hX0 hR hi hj hγi hγj).trans (by
      calc
        _ ≤ E*((4*(K:ℝ))*(X:ℝ)*b)*u*v :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hInv hE) hu) hv
        _ = _ := by ring)
  have hD : ‖∑ d ∈ D,a d*(V d-W)‖ ≤ A*S*((4*(K:ℝ)*E)*(X:ℝ)*b*u*v) := calc
    _ ≤ ∑ d ∈ D,‖a d*(V d-W)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ D,‖a d‖*((4*(K:ℝ)*E)*(X:ℝ)*b*u*v) := by
      apply sum_le_sum
      intro d hd
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hDpt d hd) (norm_nonneg _)
    _ = _ := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hA' (by positivity)
  have hW := norm_fullGlobalPair_le_mass (m:=m) hX0 hi hj
  have hDW : ‖((∑ d ∈ D,a d)-globalPairSeries m i j)*W‖ ≤
      B'*S*b*((X:ℝ)*u*v) := by
    rw [norm_mul]
    exact mul_le_mul hBseries hW (norm_nonneg _) (by positivity)
  have hsplit : smoothDenominatorSum X m i j = (∑ d ∈ D,a d*V d)+(∑ d ∈ U,a d*V d) := by
    unfold smoothDenominatorSum
    change (∑ d ∈ Q,a d*V d) = _
    simpa only [D,U,not_le] using
      (sum_filter_add_sum_filter_not (s:=Q) (fun d : ℕ => (d:ℝ)≤T) (fun d => a d*V d)).symm
  have hsplit' : smoothDenominatorSum X m i j-globalPairSeries m i j*W =
      (∑ d ∈ U,a d*V d)+(∑ d ∈ D,a d*(V d-W))+((∑ d ∈ D,a d)-globalPairSeries m i j)*W := by
    rw [hsplit]
    simp_rw [mul_sub,sum_sub_distrib,← sum_mul]
    ring
  rw [hsplit']
  calc
    _ ≤ ‖∑ d ∈ U,a d*V d‖+‖∑ d ∈ D,a d*(V d-W)‖+
        ‖((∑ d ∈ D,a d)-globalPairSeries m i j)*W‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := (add_le_add (add_le_add hU hD) hDW).trans_eq (by ring)


end
end GoldbachSignedPairs


end

section

namespace GoldbachSignedPairs

open Finset Filter Complex DirichletCharacter
open scoped Classical

noncomputable section

def compactFullPairs (X m : ℕ) (L T : ℝ) (K H : ℕ) : Finset (GlobalMode × GlobalMode) :=
  (cappedGlobalModes X L ×ˢ cappedGlobalModes X L).filter (fun p =>
    goodArithmeticPair K H m p.1 p.2 ∧
    |(spectralPoint p.1).im| ≤ T ∧ |(spectralPoint p.2).im| ≤ T)

def compactFullCoefficient (X m : ℕ) (L T : ℝ) (K H : ℕ) : ℂ :=
  ∑ p ∈ compactFullPairs X m L T K H,
    globalPairSeries m p.1 p.2*fullGlobalPair X m p.1 p.2

def compactNonpoleModes (X m : ℕ) (L T : ℝ) (H : ℕ) : Finset GlobalMode :=
  ((divisorClass (cappedGlobalModes X L) globalLevel H m).filter
    (fun i => |(spectralPoint i).im| ≤ T)).erase none

private theorem none_mem_capped {X : ℕ} {L : ℝ} (hL : 0 ≤ L) :
    none ∈ cappedGlobalModes X L :=
  mem_filter.mpr ⟨by simp [globalModesAt], hL⟩

theorem mem_compactNonpoleModes {X m H : ℕ} {L T : ℝ} {i : GlobalMode} :
    i ∈ compactNonpoleModes X m L T H ↔
      i ≠ none ∧ i ∈ cappedGlobalModes X L ∧ globalLevel i ∣ H*m ∧
        |(spectralPoint i).im| ≤ T := by
  simp [compactNonpoleModes,divisorClass,and_assoc]

theorem compactNonpole_level_dvd_class {X m H : ℕ} {L T : ℝ} {i : GlobalMode}
    (hi : i ∈ compactNonpoleModes X m L T H) :
    globalLevel i ∣ classModulus (cappedGlobalModes X L) globalLevel H m := by
  obtain ⟨_,hi',hd,_⟩ := mem_compactNonpoleModes.mp hi
  exact level_dvd_classModulus (mem_filter.mpr ⟨hi',hd⟩)

theorem commonModulus_pos {X m H : ℕ} (hH : 0 < H) (hm : 0 < m) (L : ℝ) :
    0 < classModulus (cappedGlobalModes X L) globalLevel H m :=
  Nat.pos_of_ne_zero (fun h => by
    have hd := classModulus_dvd (cappedGlobalModes X L) globalLevel H m
    rw [h,zero_dvd_iff] at hd
    exact (Nat.mul_pos hH hm).ne' hd)

private theorem eventually_compactFullPairs_eq {K H : ℕ} (hK : 0 < K)
    {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) :
    ∀ᶠ X : ℕ in atTop, ∀ m : ℕ,
      let S := compactNonpoleModes X m L T H
      compactFullPairs X m L T K H =
        insert (none,none) ((S ×ˢ S).filter (fun p => globalPairConductor p.1 p.2 ≤ K)) := by
  filter_upwards [eventually_bounded_modes_have_large_level K hL hT] with X hG m
  let S := compactNonpoleModes X m L T H
  have hnone : none ∈ globalModesAt X := by simp [globalModesAt]
  have h00 : globalPairConductor none none = 1 :=
    globalPairConductor_none_left hnone
  have hPoleIn : (none,none) ∈ compactFullPairs X m L T K H := by
    refine mem_filter.mpr ⟨mem_product.mpr ⟨none_mem_capped hL,none_mem_capped hL⟩,?_⟩
    have hh : (1:ℕ) ≤ K := hK
    refine ⟨⟨h00 ▸ hh,?_⟩,?_,?_⟩
    · change (1:ℕ).lcm 1 ∣ H*m
      simp
    · change |(1:ℂ).im| ≤ T
      simpa only [Complex.one_im,abs_zero] using hT
    · change |(1:ℂ).im| ≤ T
      simpa only [Complex.one_im,abs_zero] using hT
  ext p
  constructor
  · intro hp
    obtain ⟨hpij,⟨hKp,hdiv⟩,hti,htj⟩ := mem_filter.mp hp
    obtain ⟨hi,hj⟩ := mem_product.mp hpij
    obtain ⟨hi',hLi⟩ := mem_filter.mp hi
    obtain ⟨hj',hLj⟩ := mem_filter.mp hj
    by_cases hi0 : p.1 = none
    · by_cases hj0 : p.2 = none
      · exact mem_insert.mpr (Or.inl (Prod.ext hi0 hj0))
      · rw [hi0,globalPairConductor_none_left hj'] at hKp
        exact (not_lt_of_ge hKp (hG _ hj' hj0 hLj htj)).elim
    · by_cases hj0 : p.2 = none
      · rw [hj0,globalPairConductor_none_right hi'] at hKp
        exact (not_lt_of_ge hKp (hG _ hi' hi0 hLi hti)).elim
      · refine mem_insert.mpr (Or.inr (mem_filter.mpr ⟨mem_product.mpr ⟨?_,?_⟩,hKp⟩))
        · exact mem_compactNonpoleModes.mpr ⟨hi0,hi,(Nat.dvd_lcm_left _ _).trans hdiv,hti⟩
        · exact mem_compactNonpoleModes.mpr ⟨hj0,hj,(Nat.dvd_lcm_right _ _).trans hdiv,htj⟩
  · intro hp
    rcases mem_insert.mp hp with h | hp
    · rwa [h]
    obtain ⟨hpij,hKp⟩ := mem_filter.mp hp
    obtain ⟨hi,hj⟩ := mem_product.mp hpij
    obtain ⟨_,hi',hdi,hti⟩ := mem_compactNonpoleModes.mp hi
    obtain ⟨_,hj',hdj,htj⟩ := mem_compactNonpoleModes.mp hj
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hi',hj'⟩,⟨hKp,Nat.lcm_dvd hdi hdj⟩,hti,htj⟩

set_option maxHeartbeats 2200000 in
theorem eventually_compactFullCoefficient_re_lower {K H : ℕ} (hK : 0 < K) (hH : 0 < H)
    {L T θ : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) (hθ : θ ≤ 1) :
    ∀ᶠ X : ℕ in atTop, ∀ m : ℕ, 0 < m → Even m →
      (5/2:ℝ)*(X:ℝ) ≤ (m:ℝ) → (m:ℝ) ≤ (7/2:ℝ)*(X:ℝ) →
      massSquareByClass (classModulus (cappedGlobalModes X L) globalLevel H m) K X
        (compactNonpoleModes X m L T H) ≤ θ →
      (1-θ)*((X:ℝ)/4)*globalOrdinarySingularSeries m ≤ (compactFullCoefficient X m L T K H).re := by
  obtain ⟨c,hc,hS⟩ := globalOrdinarySingularSeries_pos_uniform
  filter_upwards [eventually_compactFullPairs_eq (H:=H) hK hL hT,eventually_ge_atTop (1:ℕ)]
    with X hsplit hX m hm hEven hm₁ hm₂ hMass
  let S := compactNonpoleModes X m L T H
  let q := classModulus (cappedGlobalModes X L) globalLevel H m
  let f (p : GlobalMode × GlobalMode) := globalPairSeries m p.1 p.2*fullGlobalPair X m p.1 p.2
  let D := (S ×ˢ S).filter (fun p => globalPairConductor p.1 p.2 ≤ K)
  let P := (fullGlobalPair X m none none).re
  let U := globalOrdinarySingularSeries m
  let _ : NeZero q := ⟨(commonModulus_pos hH hm L).ne'⟩
  have hX0 : 0 < X := hX
  have hPole := fullGlobalPair_pole_floor hX0 hm₁ hm₂
  have hP : 0 ≤ P := (by positivity : (0:ℝ)≤(X:ℝ)/4).trans hPole
  have hU : 0 ≤ U := (hc.trans (hS m hm hEven)).le
  have hCom : (∑ p ∈ D,modeMass X p.1*modeMass X p.2) ≤ θ :=
    (global_small_product_mass_le (q:=q) (K:=K) (X:=X) S
      (fun _ hi => compactNonpole_level_dvd_class hi)).trans hMass
  have hPoleRe : (f (none,none)).re = U*P := by
    have hIm : (fullGlobalPair X m none none).im = 0 := by
      rw [fullGlobalPair_none_none hX0,Complex.ofReal_im]
    simp only [f,Complex.mul_re,hIm,mul_zero,sub_zero]
    change (globalPairSeries m none none).re*P = _
    exact congrArg (fun y : ℝ => y*P) (globalOrdinarySingularSeries_eq m).symm
  have hPoleNot : (none,none) ∉ D := by
    intro hp
    have hi := (mem_product.mp (mem_filter.mp hp).1).1
    exact (mem_compactNonpoleModes.mp hi).1 rfl
  have hPt (p : GlobalMode × GlobalMode) (hp : p ∈ D) :
      ‖f p‖ ≤ (U*P)*(modeMass X p.1*modeMass X p.2) := by
    obtain ⟨hi,hj⟩ := mem_product.mp (mem_filter.mp hp).1
    have hi' := (mem_filter.mp (mem_compactNonpoleModes.mp hi).2.1).1
    have hj' := (mem_filter.mp (mem_compactNonpoleModes.mp hj).2.1).1
    change ‖globalPairSeries m p.1 p.2 * fullGlobalPair X m p.1 p.2‖ ≤ _
    rw [norm_mul]
    exact (mul_le_mul (norm_globalPairSeries_le hm hi' hj')
      (norm_fullGlobalPair_le_pole hX0 hi' hj') (norm_nonneg _) hU).trans_eq (by ring)
  have hNorm : ‖∑ p ∈ D,f p‖ ≤ U*P*θ := calc
    _ ≤ ∑ p ∈ D,‖f p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ D,(U*P)*(modeMass X p.1*modeMass X p.2) := sum_le_sum hPt
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hCom (mul_nonneg hU hP)
  have hLow : - (U*P*θ) ≤ (∑ p ∈ D,f p).re :=
    (neg_le_neg hNorm).trans (neg_abs_le _ |>.trans' (neg_le_neg (Complex.abs_re_le_norm _)))
  unfold compactFullCoefficient
  change (1-θ)*((X:ℝ)/4)*U ≤ (∑ p ∈ compactFullPairs X m L T K H,f p).re
  rw [hsplit, sum_insert hPoleNot,Complex.add_re,hPoleRe]
  calc
    _ ≤ (1-θ)*P*U := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPole (sub_nonneg.mpr hθ)) hU
    _ ≤ _ := by linarith only [hLow,show (1-θ)*P*U=U*P-U*P*θ by ring]

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

/-- In the high-ordinate branch both the full and truncated smooth pairs
are small relative to the pole on the central target window. -/
theorem norm_fullGlobalPair_sub_smooth_pairIntegral_high_scale_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {η : ℝ}, 0 < η → ∀ {X m : ℕ} {R : ℝ}, 0 < X →
      (5/2:ℝ)*(X:ℝ) ≤ (m:ℝ) → (m:ℝ) ≤ (7/2:ℝ)*(X:ℝ) →
      4*Real.pi ≤ (X:ℝ)^η → 0 ≤ R →
      ∀ {i j : GlobalMode}, i ∈ globalModesAt X → j ∈ globalModesAt X →
      let H := max |(spectralPoint i).im| |(spectralPoint j).im|
      (X:ℝ)^η/2 ≤ H → 2*(X:ℝ)^η*((X:ℝ)*R) ≤ H →
      ‖fullGlobalPair X m i j-pairIntegral R m (smoothGlobalProfile X) i j‖ ≤
        C*(fullGlobalPair X m none none).re*modeMass X i*modeMass X j*(X:ℝ)^(-(η/3)) := by
  obtain ⟨A,hA,hfull⟩ := norm_fullGlobalPair_high_scale_le
  obtain ⟨B,hB,hwindow⟩ := norm_smooth_pairIntegral_high_ordinate_le
  refine ⟨A+4*B,by positivity,?_⟩
  intro η hη X m R hX hm₁ hm₂ hScale hR i j hi hj
  dsimp only
  let H := max |(spectralPoint i).im| |(spectralPoint j).im|
  intro hH hRH
  have hx : (0:ℝ) < X := by exact_mod_cast hX
  have hx₁ : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hηX : (0:ℝ) < (X:ℝ)^η := Real.rpow_pos_of_pos hx _
  have h2 : 2 ≤ (X:ℝ)^η := by linarith only [hScale,Real.pi_gt_three]
  have hH₀ : 0 < H := (half_pos hηX).trans_le hH
  have hXR : 0 ≤ (X:ℝ)*R := mul_nonneg hx.le hR
  have hR₈ : 8*Real.pi*(X:ℝ)*R ≤ H := calc
    _ = (2*(4*Real.pi))*((X:ℝ)*R) := by ring
    _ ≤ (2*(X:ℝ)^η)*((X:ℝ)*R) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hScale (by norm_num)) hXR
    _ ≤ _ := hRH
  have hRatio : ((X:ℝ)*R)/H ≤ (X:ℝ)^(-η) := by
    rw [Real.rpow_neg hx.le,← one_div]
    apply (div_le_div_iff₀ hH₀ hηX).2
    rw [one_mul]
    exact (show ((X:ℝ)*R)*(X:ℝ)^η ≤ 2*(X:ℝ)^η*((X:ℝ)*R) by
      nlinarith only [mul_nonneg hXR hηX.le]).trans hRH
  have hPow : (X:ℝ)^(-η) ≤ (X:ℝ)^(-(η/3)) :=
    Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith)
  have hPole := fullGlobalPair_pole_floor hX hm₁ hm₂
  have hPole' : (X:ℝ) ≤ 4*(fullGlobalPair X m none none).re := by linarith
  have hi₀ := modeMass_nonneg X i
  have hj₀ := modeMass_nonneg X j
  have hWin : ‖pairIntegral R m (smoothGlobalProfile X) i j‖ ≤
      (4*B)*(fullGlobalPair X m none none).re*modeMass X i*modeMass X j*(X:ℝ)^(-(η/3)) := by
    calc
      _ ≤ B*(X:ℝ)*modeMass X i*modeMass X j*((X:ℝ)*R)/H := hwindow hX hi hj hR hR₈
      _ = B*(X:ℝ)*modeMass X i*modeMass X j*(((X:ℝ)*R)/H) := by ring
      _ ≤ B*(X:ℝ)*modeMass X i*modeMass X j*(X:ℝ)^(-(η/3)) := by
        exact mul_le_mul_of_nonneg_left (hRatio.trans hPow)
          (mul_nonneg (mul_nonneg (mul_nonneg hB.le hx.le) hi₀) hj₀)
      _ ≤ B*(4*(fullGlobalPair X m none none).re)*modeMass X i*modeMass X j*(X:ℝ)^(-(η/3)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPole' hB.le) hi₀) hj₀) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ‖fullGlobalPair X m i j‖ + ‖pairIntegral R m (smoothGlobalProfile X) i j‖ := norm_sub_le _ _
    _ ≤ _ := (add_le_add (hfull hX hm₁ hm₂ h2 hi hj hH) hWin).trans_eq (by ring)

end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Complex Finset Filter Topology DirichletCharacter
open GoldbachWeightedMajorResidual GoldbachWeightedException
open Conjectures.Goldbach.TwistedGoldbachSingularSeries
open scoped Classical BigOperators

private theorem transition_scale_eq_level_mul (i : GlobalMode) :
    modeTransitionScale i = (globalLevel i:ℝ)*(1+|(spectralPoint i).im|) := by
  rcases i with _ | ⟨r,χ,z⟩
  · simp [modeTransitionScale,globalLevel,spectralPoint]
  · rfl

private theorem norm_complete_pair_series_le {X m : ℕ} (hm : 0 < m) {i j : GlobalMode}
    (hi : i ∈ globalModesAt X) (hj : j ∈ globalModesAt X) :
    ‖∑' d : ℕ, globalPairCoefficient m d i j‖ ≤ globalOrdinarySingularSeries m := by
  let : NeZero (globalLevel i) := ⟨(globalLevel_pos hi).ne'⟩
  let : NeZero (globalLevel j) := ⟨(globalLevel_pos hj).ne'⟩
  simp only [globalPairCoefficient_eq_coefficient,globalOrdinarySingularSeries]
  exact infinite_domination (globalSourceCharacter_isPrimitive hi).inv
    (globalSourceCharacter_isPrimitive hj).inv m hm

/-- If either mode lies above the adaptive transition gap, the finite
denominator approximation to the full pair has a uniform power error. -/
theorem norm_high_adaptive_denominator_sum_sub_full_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X P m : ℕ}, 0 < X → 4*Real.pi ≤ (X:ℝ)^η →
      0 < m → Even m → (5/2:ℝ)*(X:ℝ) ≤ (m:ℝ) → (m:ℝ) ≤ (7/2:ℝ)*(X:ℝ) →
      ∀ {i j : GlobalMode}, i ∈ globalModesAt X → j ∈ globalModesAt X →
      ((globalLevel i ≤ P ∧ (P:ℝ)*(X:ℝ)^η < modeTransitionScale i) ∨
        (globalLevel j ≤ P ∧ (P:ℝ)*(X:ℝ)^η < modeTransitionScale j)) →
      ‖(∑ d ∈ Icc 1 P, globalPairCoefficient m d i j*
        pairIntegral (adaptiveArcRadius P X d) m (smoothGlobalProfile X) i j) -
        (∑' d : ℕ, globalPairCoefficient m d i j)*fullGlobalPair X m i j‖ ≤
          C*(X:ℝ)*globalOrdinarySingularSeries m*(X:ℝ)^(-(η/3))*modeMass X i*modeMass X j := by
  obtain ⟨A,hA,hAbs⟩ := globalPairCoefficient_absolute_le
  obtain ⟨E,hE,hErr⟩ := norm_fullGlobalPair_sub_smooth_pairIntegral_high_scale_le
  obtain ⟨F,hF,hFull⟩ := norm_fullGlobalPair_high_scale_le
  refine ⟨A*E+(A+1)*F,by positivity,?_⟩
  intro X P m hX hScale hm he hm₁ hm₂ i j hi hj hside
  let Q := Icc 1 P
  let a (d : ℕ) := globalPairCoefficient m d i j
  let V (d : ℕ) := pairIntegral (adaptiveArcRadius P X d) m (smoothGlobalProfile X) i j
  let W := fullGlobalPair X m i j
  let S := globalOrdinarySingularSeries m
  let u := modeMass X i
  let v := modeMass X j
  let b := (X:ℝ)^(-(η/3))
  let H := max |(spectralPoint i).im| |(spectralPoint j).im|
  have hx : (0:ℝ) < X := by exact_mod_cast hX
  have hu : 0 ≤ u := modeMass_nonneg X i
  have hv : 0 ≤ v := modeMass_nonneg X j
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hTwo : 2 ≤ (X:ℝ)^η := by linarith only [hScale,Real.pi_gt_three]
  obtain ⟨k,hk,hkP,hkHigh⟩ : ∃ k : GlobalMode, (k=i ∨ k=j) ∧ globalLevel k≤P ∧
      (P:ℝ)*(X:ℝ)^η < modeTransitionScale k := by
    rcases hside with h | h
    · exact ⟨i,Or.inl rfl,h.1,h.2⟩
    · exact ⟨j,Or.inr rfl,h.1,h.2⟩
  have hk₀ : 0 < globalLevel k := by
    rcases hk with rfl|rfl
    · exact globalLevel_pos hi
    · exact globalLevel_pos hj
  have hgH : |(spectralPoint k).im| ≤ H := by
    rcases hk with rfl|rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  rw [transition_scale_eq_level_mul] at hkHigh
  have hH : (X:ℝ)^η/2 ≤ H :=
    (adaptiveArcRadius_high hX hk₀ hk₀ hkP (dvd_refl _) hTwo hkHigh).1.le.trans hgH
  have hPole : (fullGlobalPair X m none none).re ≤ (X:ℝ) := by
    rw [fullGlobalPair_none_none hX,Complex.ofReal_re]
    exact principal_convolution_le_scale hx
  have hW : ‖W‖ ≤ F*(X:ℝ)*u*v*b := (hFull hX hm₁ hm₂ hTwo hi hj hH).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPole hF.le) hu) hv) hb)
  have hAbsQ : (∑ d ∈ Q,‖a d‖) ≤ A*S := hAbs hm he hi hj Q
  have hSeries : ‖∑' d : ℕ,a d‖ ≤ S := norm_complete_pair_series_le hm hi hj
  have hS : 0 ≤ S := (norm_nonneg _).trans hSeries
  have hPoint (d : ℕ) (hd : d∈Q) (hkd : globalLevel k ∣ d) :
      ‖V d-W‖ ≤ E*(X:ℝ)*u*v*b := by
    have hd₀ : 0 < d := (mem_Icc.mp hd).1
    have hR : 0 ≤ adaptiveArcRadius P X d := by unfold adaptiveArcRadius; positivity
    have hRadius : 2*(X:ℝ)^η*((X:ℝ)*adaptiveArcRadius P X d) ≤ H :=
      (adaptiveArcRadius_high hX hk₀ hd₀ hkP hkd hTwo hkHigh).2.le.trans hgH
    rw [norm_sub_rev]
    refine (hErr hη hX hm₁ hm₂ hScale hR hi hj hH hRadius).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPole hE.le) hu) hv) hb
  have hA' : ‖∑ d ∈ Q,a d*(V d-W)‖ ≤ (A*S)*(E*(X:ℝ)*u*v*b) := calc
    _ ≤ ∑ d ∈ Q,‖a d*(V d-W)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Q,‖a d‖*(E*(X:ℝ)*u*v*b) := by
      apply sum_le_sum
      intro d hd
      rw [norm_mul]
      by_cases hdiv : globalLevel i ∣ d ∧ globalLevel j ∣ d
      · have hkd : globalLevel k ∣ d := by
          rcases hk with rfl|rfl
          · exact hdiv.1
          · exact hdiv.2
        exact mul_le_mul_of_nonneg_left (hPoint d hd hkd) (norm_nonneg _)
      · have hz : a d = 0 := by simp [a,globalPairCoefficient,hdiv]
        simp only [hz,norm_zero,zero_mul,le_refl]
    _ = (∑ d ∈ Q,‖a d‖)*(E*(X:ℝ)*u*v*b) := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hAbsQ (by positivity)
  have hDiff : ‖(∑ d ∈ Q,a d)-(∑' d : ℕ,a d)‖ ≤ (A+1)*S := calc
    _ ≤ ‖∑ d ∈ Q,a d‖+‖∑' d : ℕ,a d‖ := norm_sub_le _ _
    _ ≤ A*S+S := add_le_add ((norm_sum_le _ _).trans hAbsQ) hSeries
    _ = _ := by ring
  have hB' : ‖((∑ d ∈ Q,a d)-(∑' d : ℕ,a d))*W‖ ≤ ((A+1)*S)*(F*(X:ℝ)*u*v*b) := by
    rw [norm_mul]
    exact mul_le_mul hDiff hW (norm_nonneg _) (by positivity)
  change ‖(∑ d ∈ Q,a d*V d)-(∑' d : ℕ,a d)*W‖ ≤ _
  have hSplit : (∑ d ∈ Q,a d*V d)-(∑' d : ℕ,a d)*W =
      (∑ d ∈ Q,a d*(V d-W))+((∑ d ∈ Q,a d)-(∑' d : ℕ,a d))*W := by
    simp_rw [mul_sub,sum_sub_distrib,← sum_mul]
    ring
  rw [hSplit]
  exact (norm_add_le _ _).trans ((add_le_add hA' hB').trans_eq (by ring))

private theorem eventually_high_denominator_rpow_ge {η : ℝ} (hη : 0 < η) (A : ℝ) :
    ∀ᶠ X : ℕ in atTop, A ≤ (X:ℝ)^η := by
  have hLim : Tendsto (fun X : ℕ => (X:ℝ)^η) atTop atTop := by
    change Tendsto ((fun x : ℝ => x^η) ∘ (fun X : ℕ => (X:ℝ))) atTop atTop
    exact (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  exact (tendsto_atTop.1 hLim) A

theorem eventually_norm_high_adaptive_denominator_sum_sub_full_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop, ∀ {P m : ℕ},
      0 < m → Even m → (5/2:ℝ)*(X:ℝ) ≤ (m:ℝ) → (m:ℝ) ≤ (7/2:ℝ)*(X:ℝ) →
      ∀ {i j : GlobalMode}, i ∈ globalModesAt X → j ∈ globalModesAt X →
      ((globalLevel i ≤ P ∧ (P:ℝ)*(X:ℝ)^η < modeTransitionScale i) ∨
        (globalLevel j ≤ P ∧ (P:ℝ)*(X:ℝ)^η < modeTransitionScale j)) →
      ‖(∑ d ∈ Icc 1 P, globalPairCoefficient m d i j*
        pairIntegral (adaptiveArcRadius P X d) m (smoothGlobalProfile X) i j) -
        (∑' d : ℕ, globalPairCoefficient m d i j)*fullGlobalPair X m i j‖ ≤
          C*(X:ℝ)*globalOrdinarySingularSeries m*(X:ℝ)^(-(η/3))*modeMass X i*modeMass X j := by
  obtain ⟨C,hC,h⟩ := norm_high_adaptive_denominator_sum_sub_full_le hη
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ),eventually_high_denominator_rpow_ge hη (4*Real.pi)] with X hX hScale
  exact h hX hScale

/-- The high-transition error for the nominal denominator cutoff. The
left side unfolds to the nominal smooth denominator sum minus the full pair. -/
theorem eventually_norm_high_nominal_denominator_sum_sub_full_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop, ∀ {m : ℕ},
      0 < m → Even m → (5/2:ℝ)*(X:ℝ) ≤ (m:ℝ) → (m:ℝ) ≤ (7/2:ℝ)*(X:ℝ) →
      ∀ {i j : GlobalMode}, i ∈ globalModesAt X → j ∈ globalModesAt X →
      ((cutoff X:ℝ)*(X:ℝ)^η < modeTransitionScale i ∨
        (cutoff X:ℝ)*(X:ℝ)^η < modeTransitionScale j) →
      ‖(∑ d ∈ Icc 1 (cutoff X), globalPairCoefficient m d i j*
        pairIntegral (arcRadius X d) m (smoothGlobalProfile X) i j) -
        (∑' d : ℕ, globalPairCoefficient m d i j)*fullGlobalPair X m i j‖ ≤
          C*(X:ℝ)*globalOrdinarySingularSeries m*(X:ℝ)^(-(η/3))*modeMass X i*modeMass X j := by
  obtain ⟨C,hC,h⟩ := eventually_norm_high_adaptive_denominator_sum_sub_full_le hη
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_ge_atTop (2^200:ℕ)] with X hX hScale
  intro m hm he hm₁ hm₂ i j hi hj hside
  have hLevel {k : GlobalMode} (hk : k ∈ globalModesAt X) : globalLevel k ≤ cutoff X := by
    rcases k with _ | ⟨r,χ,z⟩
    · exact (cutoff_scale hScale).1
    · exact ((mem_globalModesAt_zero χ z).mp hk).2.1
  have hSide' :
      ((globalLevel i ≤ cutoff X ∧ (cutoff X:ℝ)*(X:ℝ)^η < modeTransitionScale i) ∨
        (globalLevel j ≤ cutoff X ∧ (cutoff X:ℝ)*(X:ℝ)^η < modeTransitionScale j)) :=
    hside.imp (fun h => ⟨hLevel hi,h⟩) (fun h => ⟨hLevel hj,h⟩)
  simpa only [adaptiveArcRadius_eq_arcRadius] using hX hm he hm₁ hm₂ hi hj hSide'

end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Filter Finset Complex
open GoldbachWeightedException (cutoff)
open scoped Classical

noncomputable section

def supportedFullPairs (X m : ℕ) (L : ℝ) (K H : ℕ) : Finset (GlobalMode × GlobalMode) :=
  (cappedGlobalModes X L ×ˢ cappedGlobalModes X L).filter
    (fun p => goodArithmeticPair K H m p.1 p.2)

def supportedFullCoefficient (X m : ℕ) (L : ℝ) (K H : ℕ) : ℂ :=
  ∑ p ∈ supportedFullPairs X m L K H,
    globalPairSeries m p.1 p.2*fullGlobalPair X m p.1 p.2

private theorem norm_subproduct_sum_le {ι : Type*} {G : Finset ι} {D : Finset (ι × ι)}
    {C : ℝ} (hC : 0 ≤ C) (hD : D ⊆ G ×ˢ G) (a : ι → ℝ) (f : ι × ι → ℂ)
    (ha : ∀ i ∈ G, 0 ≤ a i) (hf : ∀ p ∈ D, ‖f p‖ ≤ C*(a p.1*a p.2)) :
    ‖∑ p ∈ D,f p‖ ≤ C*(∑ i ∈ G,a i)^2 := by
  calc
    _ ≤ ∑ p ∈ D,‖f p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ D,C*(a p.1*a p.2) := sum_le_sum hf
    _ ≤ ∑ p ∈ G ×ˢ G,C*(a p.1*a p.2) := by
      apply sum_le_sum_of_subset_of_nonneg hD
      intro p hp _
      obtain ⟨hi,hj⟩ := mem_product.mp hp
      exact mul_nonneg hC (mul_nonneg (ha _ hi) (ha _ hj))
    _ = _ := by
      rw [← mul_sum,sum_product]
      simp_rw [← mul_sum,← sum_mul]
      ring

/-- The spectral separation needed to extend the major arc windows. -/
def SeparatedSpectralCutoff (η L : ℝ) : Prop :=
  ∀ᶠ X : ℕ in atTop, ∀ i ∈ cappedGlobalModes X L,
    modeTransitionScale i < (cutoff X:ℝ)/(X:ℝ)^η ∨
      (cutoff X:ℝ)*(X:ℝ)^η < modeTransitionScale i

set_option maxHeartbeats 2600000 in
theorem eventually_norm_supportedSmooth_sub_full_le {η : ℝ} (hη : 0 < η)
    {L : ℝ} (hSep : SeparatedSpectralCutoff η L) {K H : ℕ} (hK : 0 < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop, ∀ m : ℕ, 0 < m → m ≤ 4*X → Even m →
      (5/2:ℝ)*(X:ℝ) ≤ (m:ℝ) → (m:ℝ) ≤ (7/2:ℝ)*(X:ℝ) →
        ‖supportedSmoothCoefficient X m L K H-supportedFullCoefficient X m L K H‖ ≤
          C*(X:ℝ)*globalOrdinarySingularSeries m*(X:ℝ)^(-(η/16)) := by
  obtain ⟨A,hA,hMass⟩ := short_global_mass_and_tail
  obtain ⟨B,hB,hLow⟩ := eventually_norm_low_smoothDenominatorSum_sub_full_le hη hK
  obtain ⟨D,hD,hHigh⟩ := eventually_norm_high_nominal_denominator_sum_sub_full_le hη
  obtain ⟨v,hv,hSing⟩ := globalOrdinarySingularSeries_pos_uniform
  refine ⟨(B+D)*A^2,by positivity,?_⟩
  unfold SeparatedSpectralCutoff at hSep
  filter_upwards [hSep,hMass,hLow,hHigh,eventually_ge_atTop (1:ℕ)]
    with X hSep hMass hLow hHigh hX m hm hmX he hm₁ hm₂
  let F := supportedFullPairs X m L K H
  let e (p : GlobalMode × GlobalMode) :=
    smoothDenominatorSum X m p.1 p.2-globalPairSeries m p.1 p.2*fullGlobalPair X m p.1 p.2
  let S := globalOrdinarySingularSeries m
  let M (i : GlobalMode) := modeMass X i
  let w := (X:ℝ)^(-(η/16))
  have hS : 0 ≤ S := (hv.trans (hSing m hm he)).le
  have hX' : (1:ℝ) ≤ X := by exact_mod_cast hX
  have heq : supportedSmoothCoefficient X m L K H-supportedFullCoefficient X m L K H =
      ∑ p ∈ F,e p := by
    let A (p : GlobalMode × GlobalMode) := smoothDenominatorSum X m p.1 p.2
    let B (p : GlobalMode × GlobalMode) :=
      globalPairSeries m p.1 p.2*fullGlobalPair X m p.1 p.2
    change (∑ p ∈ F,A p)-(∑ p ∈ F,B p) = (∑ p ∈ F,(A p-B p))
    exact (sum_sub_distrib A B).symm
  rw [heq]
  have hSub : F ⊆ globalModesAt X ×ˢ globalModesAt X := by
    intro p hp
    obtain ⟨hi,hj⟩ := mem_product.mp (mem_filter.mp hp).1
    exact mem_product.mpr ⟨(mem_filter.mp hi).1,(mem_filter.mp hj).1⟩
  refine (norm_subproduct_sum_le (C:=(B+D)*(X:ℝ)*S*w) (by positivity)
    hSub M e (fun i _ => modeMass_nonneg _ _) ?_).trans ?_
  · intro p hp
    obtain ⟨hpij,hGood⟩ := mem_filter.mp hp
    obtain ⟨hi,hj⟩ := mem_product.mp hpij
    have hi' := (mem_filter.mp hi).1
    have hj' := (mem_filter.mp hj).1
    have hai : 0 ≤ M p.1 := modeMass_nonneg _ _
    have haj : 0 ≤ M p.2 := modeMass_nonneg _ _
    have hH (hh : (cutoff X:ℝ)*(X:ℝ)^η < modeTransitionScale p.1 ∨
        (cutoff X:ℝ)*(X:ℝ)^η < modeTransitionScale p.2) :
        ‖e p‖ ≤ D*(X:ℝ)*S*(X:ℝ)^(-(η/3))*M p.1*M p.2 := by
      exact hHigh (m:=m) hm he hm₁ hm₂ hi' hj' hh
    have hH' (hh : (cutoff X:ℝ)*(X:ℝ)^η < modeTransitionScale p.1 ∨
        (cutoff X:ℝ)*(X:ℝ)^η < modeTransitionScale p.2) :
        ‖e p‖ ≤ (B+D)*(X:ℝ)*S*w*(M p.1*M p.2) := (hH hh).trans (by
      have hw : (X:ℝ)^(-(η/3)) ≤ w :=
        Real.rpow_le_rpow_of_exponent_le hX' (by linarith only [hη])
      have hb : D ≤ B+D := le_add_of_nonneg_left hB
      calc
        _ ≤ (B+D)*(X:ℝ)*S*w*M p.1*M p.2 := by gcongr
        _ = _ := by ring)
    rcases hSep p.1 hi with hLi|hHi
    · rcases hSep p.2 hj with hLj|hHj
      · exact (hLow m hm hmX he _ hi' _ hj' hGood.1 hLi hLj).trans (by
          have hBase : B ≤ B+D := le_add_of_nonneg_right hD.le
          calc
            _ ≤ (B+D)*(X:ℝ)*S*w*M p.1*M p.2 := by gcongr
            _ = _ := by ring)
      · exact hH' (Or.inr hHj)
    · exact hH' (Or.inl hHi)
  · have hMass0 : 0 ≤ ∑ i ∈ globalModesAt X,M i := sum_nonneg (fun i _ => modeMass_nonneg _ _)
    calc
      _ ≤ (B+D)*(X:ℝ)*S*w*A^2 := by gcongr; exact hMass.1
      _ = _ := by ring

set_option maxHeartbeats 2300000 in
theorem eventually_norm_supportedFull_sub_compact_le {ε : ℝ} (hε : 0 < ε)
    (L : ℝ) (K H : ℕ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ᶠ X : ℕ in atTop, ∀ m : ℕ, 0 < m →
      (5/2:ℝ)*(X:ℝ) ≤ (m:ℝ) → (m:ℝ) ≤ (7/2:ℝ)*(X:ℝ) →
      ‖supportedFullCoefficient X m L K H-compactFullCoefficient X m L T K H‖ ≤
        ε*(X:ℝ)*globalOrdinarySingularSeries m := by
  obtain ⟨A,hA,hMass⟩ := short_global_mass_and_tail
  obtain ⟨C,hC,hHeight⟩ := norm_fullGlobalPair_high_ordinate_le
  let U := max 1 (C*A^2/ε)
  let T := U^3
  have hU : 1 ≤ U := le_max_left _ _
  have hU0 := zero_lt_one.trans_le hU
  have hT : 1 ≤ T := one_le_pow₀ hU
  have hFactor : C*T^(-1/3:ℝ)*A^2 ≤ ε := by
    have h := (div_le_iff₀ hε).mp (le_max_right (1:ℝ) (C*A^2/ε))
    dsimp only [T]
    rw [← Real.rpow_natCast,← Real.rpow_mul hU0.le,
      show ((3:ℕ):ℝ)*(-1/3:ℝ) = -1 by norm_num,Real.rpow_neg_one]
    calc
      _ = (C*A^2)/U := by ring
      _ ≤ _ := (div_le_iff₀ hU0).mpr (by linarith only [h])
  refine ⟨T,hT,?_⟩
  filter_upwards [hMass,eventually_ge_atTop (1:ℕ)] with X hMass hX m hm hm₁ hm₂
  let F := supportedFullPairs X m L K H
  let g (p : GlobalMode × GlobalMode) := |(spectralPoint p.1).im| ≤ T ∧ |(spectralPoint p.2).im| ≤ T
  let a (p : GlobalMode × GlobalMode) :=
    globalPairSeries m p.1 p.2*fullGlobalPair X m p.1 p.2
  let S := globalOrdinarySingularSeries m
  let M (i : GlobalMode) := modeMass X i
  have hS : 0 ≤ S := (norm_nonneg _).trans (norm_globalPairSeries_le hm
    (i:=none) (j:=none) (X:=X) (by simp [globalModesAt]) (by simp [globalModesAt]))
  have hX0 : 0 < X := hX
  have heq : supportedFullCoefficient X m L K H-compactFullCoefficient X m L T K H =
      ∑ p ∈ F.filter (fun p => ¬g p),a p := by
    have he : compactFullPairs X m L T K H = F.filter g := by
      ext p
      simp [compactFullPairs,supportedFullPairs,F,g,and_assoc]
    rw [supportedFullCoefficient,compactFullCoefficient,he]
    change (∑ p ∈ F,a p)-(∑ p ∈ F.filter g,a p) = _
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using (sum_filter_add_sum_filter_not (s:=F) g a).symm
  rw [heq]
  have hSub : F.filter (fun p => ¬g p) ⊆ globalModesAt X ×ˢ globalModesAt X := by
    intro p hp
    obtain ⟨hF,_⟩ := mem_filter.mp hp
    obtain ⟨hi,hj⟩ := mem_product.mp (mem_filter.mp hF).1
    exact mem_product.mpr ⟨(mem_filter.mp hi).1,(mem_filter.mp hj).1⟩
  refine (norm_subproduct_sum_le (C:=(C*T^(-1/3:ℝ))*(X:ℝ)*S) (by positivity)
    hSub M a (fun i _ => modeMass_nonneg _ _) ?_).trans ?_
  · intro p hp
    obtain ⟨hi,hj⟩ := mem_product.mp (hSub hp)
    let M' := |(spectralPoint p.1).im|+|(spectralPoint p.2).im|
    have hT' : T ≤ M' := by
      have h := (mem_filter.mp hp).2
      change ¬ (|(spectralPoint p.1).im| ≤ T ∧ |(spectralPoint p.2).im| ≤ T) at h
      rcases not_and_or.mp h with h|h
      · exact (lt_of_not_ge h).le.trans (le_add_of_nonneg_right (abs_nonneg _))
      · exact (lt_of_not_ge h).le.trans (le_add_of_nonneg_left (abs_nonneg _))
    have hDecay : M'^(-1/3:ℝ) ≤ T^(-1/3:ℝ) :=
      Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hT) hT' (by norm_num)
    have hMassI : 0 ≤ M p.1 := modeMass_nonneg _ _
    have hMassJ : 0 ≤ M p.2 := modeMass_nonneg _ _
    change ‖globalPairSeries m p.1 p.2 * fullGlobalPair X m p.1 p.2‖ ≤ _
    rw [norm_mul]
    refine (mul_le_mul (norm_globalPairSeries_le hm hi hj)
      (hHeight hX0 hm₁ hm₂ hi hj (hT.trans hT')) (norm_nonneg _) hS).trans ?_
    calc
      _ ≤ S*(C*(X:ℝ)*M p.1*M p.2*T^(-1/3:ℝ)) := by gcongr
      _ = _ := by ring
  · have hMass0 : 0 ≤ ∑ i ∈ globalModesAt X,M i := sum_nonneg (fun i _ => modeMass_nonneg _ _)
    calc
      _ ≤ (C*T^(-1/3:ℝ))*(X:ℝ)*S*A^2 := by gcongr; exact hMass.1
      _ = (C*T^(-1/3:ℝ)*A^2)*((X:ℝ)*S) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right hFactor (by positivity)).trans_eq (by ring)

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset GoldbachWeightedMajorResidual Filter Topology
open GoldbachWeightedException (cutoff)

theorem eventually_const_mul_neg_power_le {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (C : ℝ) :
    ∀ᶠ X : ℕ in atTop, C*(X:ℝ)^(-δ) ≤ ε := by
  have hLim : Tendsto (fun X : ℕ => (X:ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [hLim.eventually_ge_atTop (C/ε),eventually_ge_atTop (1:ℕ)] with X hX hX1
  have hx : (0:ℝ) < X := by exact_mod_cast (show 0<X from hX1)
  rw [Real.rpow_neg hx.le,← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hx _)).mpr
  exact ((div_le_iff₀ hε).mp hX).trans_eq (mul_comm _ _)

set_option maxHeartbeats 1500000 in
theorem eventually_norm_shortSigned_sub_smooth_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ m : ℕ, 0 < m → Even m →
      ‖shortSignedCoefficient X m-shortSmoothCoefficient X m‖ ≤
        ε*(X:ℝ)*globalOrdinarySingularSeries m := by
  obtain ⟨C,hC,h⟩ := norm_shortSignedCoefficient_sub_smooth_le
  obtain ⟨c,hc,hS⟩ := globalOrdinarySingularSeries_pos_uniform
  have h := h
  filter_upwards [h,eventually_ge_atTop (2^200:ℕ),
    eventually_const_mul_neg_power_le (show (0:ℝ)<59/100 by norm_num) hε (25*C)]
    with X hErr hX hSmall m hm he
  have hx : (0:ℝ) < X := by exact_mod_cast (show 0<X by omega)
  have hx1 : (1:ℝ) ≤ X := by exact_mod_cast (show 1≤X by omega)
  have hS0 : 0 ≤ globalOrdinarySingularSeries m := (hc.trans (hS m hm he)).le
  have hP := (cutoff_scale hX).2.1
  have hPower : (1+(cutoff X:ℝ))^2 ≤ 25*(X:ℝ)^(41/100:ℝ) := calc
    _ ≤ (5*(X:ℝ)^(41/200:ℝ))^2 := by
      apply pow_le_pow_left₀ (by positivity) _ 2
      have h1 := Real.one_le_rpow hx1 (show (0:ℝ)≤41/200 by norm_num)
      linarith only [hP,h1]
    _ = _ := by
      rw [mul_pow,← Real.rpow_mul_natCast hx.le]
      norm_num
  have hId : (X:ℝ)^(41/100:ℝ) = (X:ℝ)^(-(59/100:ℝ))*(X:ℝ) := by
    calc
      _ = (X:ℝ)^(-(59/100:ℝ)+1) := by congr 1; norm_num
      _ = _ := by rw [Real.rpow_add hx,Real.rpow_one]
  calc
    _ ≤ C*globalOrdinarySingularSeries m*(1+(cutoff X:ℝ))^2 := hErr m hm he
    _ ≤ C*globalOrdinarySingularSeries m*(25*(X:ℝ)^(41/100:ℝ)) :=
      mul_le_mul_of_nonneg_left hPower (mul_nonneg hC hS0)
    _ = (25*C*(X:ℝ)^(-(59/100:ℝ)))*((X:ℝ)*globalOrdinarySingularSeries m) := by rw [hId]; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right hSmall (mul_nonneg hx.le hS0)).trans_eq (by ring)

end GoldbachSignedPairs

end


section

namespace GoldbachSignedPairs

open Finset Filter Complex Goldbach GoldbachTwistedMellin DirichletCharacter GoldbachWeightedMajorResidual
open scoped Classical

noncomputable section


private theorem mem_modulusZeros {q : ℕ} [NeZero q] {L T : ℝ}
    {p : DirichletCharacter ℂ q × ℂ} :
    p ∈ modulusZeros q L T ↔ p.1≠1 ∧ p.2 ∈ exceptionalZeros p.1 T ∧
      (1-p.2.re)*Real.log (q:ℝ) ≤ L := by
  rcases p with ⟨χ,z⟩
  simp only [modulusZeros,mem_image,mem_sigma,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨⟨ψ,w⟩,⟨hψ,hz,hGap⟩,he⟩
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨hψ,hz,hGap⟩
  · rintro ⟨hχ,hz,hGap⟩
    exact ⟨⟨χ,z⟩,⟨hχ,hz,hGap⟩,rfl⟩

private theorem global_mode_lift_nonpole {q : ℕ} {i : GlobalMode} (hn : i ≠ none)
    (hd : globalLevel i ∣ q) :
    globalLift q i = some ⟨liftedSpectralCharacter q i,spectralPoint i⟩ := by
  rcases i with _ | ⟨r,χ,z⟩
  · exact (hn rfl).elim
  have hd' : r ∣ q := hd
  simp only [globalLift,dite_eq_left hd,dite_eq_left hd',liftedSpectralCharacter,globalSourceCharacter,spectralPoint]
  rfl

/-- The actual capped modes embed into the zeros at their common modulus with
the correct multiplicities and no loss in the class weights. -/
theorem class_mass_le_modulus_class_mass {q X m K H : ℕ} [NeZero q]
    {L T : ℝ} (hX : 0 < X) (hMod : q = classModulus (cappedGlobalModes X L) globalLevel H m)
    (hQ : (q:ℝ) ≤ (X:ℝ)^(81/400:ℝ))
    (hLarge : ∀ i ∈ compactNonpoleModes X m L T H, 1 < globalLevel i) :
    massSquareByClass q K X (compactNonpoleModes X m L T H) ≤
      modulusClassMassSquare q K L T := by
  let S := compactNonpoleModes X m L T H
  let D := modulusZeros q L T
  let f (i : GlobalMode) := (liftedSpectralCharacter q i,spectralPoint i)
  let key (i : GlobalMode) := conductorClass K (liftedSpectralCharacter q i)
  let k (p : DirichletCharacter ℂ q × ℂ) := conductorClass K p.1
  have hDiv (i : GlobalMode) (hi : i ∈ S) : globalLevel i ∣ q :=
    hMod.symm ▸ compactNonpole_level_dvd_class hi
  have hData (i : GlobalMode) (hi : i ∈ S) := mem_compactNonpoleModes.mp hi
  have hG (i : GlobalMode) (hi : i ∈ S) : i ∈ globalModesAt X :=
    (mem_filter.mp (hData i hi).2.1).1
  let hmap : Set.MapsTo f (S:Set GlobalMode) D := by
    intro i hi
    have hm : i ∈ S := hi
    obtain ⟨hn,hi',_,ht⟩ := hData i hm
    have hs := hG i hm
    obtain ⟨hz,hO⟩ := liftedSpectralCharacter_zero_and_order hs hn (hDiv i hm)
    have hχ : liftedSpectralCharacter q i ≠ 1 := by
      intro h1
      have hh := liftedSpectralCharacter_conductor hs (hDiv i hm)
      rw [h1,conductor_one] at hh
      exact (ne_of_gt (hLarge i hm)) hh.symm
    have hβ : 1/2 < (spectralPoint i).re := by
      rcases i with _ | ⟨r,χ,z⟩
      · exact (hn rfl).elim
      obtain ⟨hr,_,_,hMem⟩ := (mem_globalModesAt_zero χ z).mp hs
      let _ : NeZero r := ⟨(Nat.zero_lt_one.trans_le hr).ne'⟩
      have hMem' : z ∈ (exceptionalZeros χ (heightCut (X:ℝ))).filter (shortNearZero X r) := by
        simpa only [globalShortZeros,dite_eq_left (NeZero.ne r)] using hMem
      exact ((mem_exceptionalZeros _ _ _).mp (mem_filter.mp hMem').1).1
    have hqX : (q:ℝ) ≤ X := hQ.trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hX : (1:ℝ)≤X) (by norm_num : (81/400:ℝ)≤1))
    have hq0 : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
    have hGap := mul_le_mul_of_nonneg_left (Real.log_le_log hq0 hqX)
      (sub_nonneg.mpr (spectralPoint_re_bounds hs).2)
    have hCap := (mem_filter.mp hi').2
    have hEq : (1-(spectralPoint i).re)*Real.log (X:ℝ) = modeGap X i := by
      cases i <;> simp [spectralPoint,modeGap]
    rw [hEq] at hGap
    exact mem_modulusZeros.mpr ⟨hχ,(mem_exceptionalZeros _ _ _).mpr ⟨hβ,ht,hz⟩,hGap.trans hCap⟩
  have hinj : Set.InjOn f (S:Set GlobalMode) := by
    intro i hi j hj he
    have hiS : i ∈ S := hi
    have hjS : j ∈ S := hj
    have hiD := hDiv i hiS
    have hjD := hDiv j hjS
    have hiG := hG i hiS
    have hjG := hG j hjS
    have hEq : globalLift q i = globalLift q j := by
      rw [global_mode_lift_nonpole (hData i hiS).1 hiD,
        global_mode_lift_nonpole (hData j hjS).1 hjD]
      exact congrArg (fun p : DirichletCharacter ℂ q × ℂ => (some ⟨p.1,p.2⟩ : Mode q)) he
    exact globalLift_injective (mem_filter.mpr ⟨hiG,hiD⟩) (mem_filter.mpr ⟨hjG,hjD⟩) hEq
  have hEqMass : massSquareByClass q K X S = classMassSq S key (modeMass X) := by
    unfold massSquareByClass classMassSq
    dsimp only [key]
    apply sum_congr
    · ext c
      simp only [mem_image]
    · intro c _
      congr 1
      apply sum_congr
      · ext j
        simp only [mem_filter]
      · intro j _
        rfl
  change massSquareByClass q K X S ≤ classMassSq D k (modulusModeMass q)
  rw [hEqMass]
  refine classMassSq_le_of_injection hmap hinj (fun _ _ => rfl)
    (fun i _ => modeMass_nonneg X i) (fun _ _ => by unfold modulusModeMass; positivity) ?_
  intro i hi
  have hOrder := (liftedSpectralCharacter_zero_and_order (hG i hi) (hData i hi).1 (hDiv i hi)).2
  change modeMass X i ≤ (analyticOrderNatAt (regularizedL (liftedSpectralCharacter q i))
    (spectralPoint i):ℝ)*(q:ℝ)^((493/100:ℝ)*((spectralPoint i).re-1))
  rw [hOrder]
  exact modeMass_le_conductor_power hX (NeZero.pos q) (hG i hi) hQ

theorem eventually_compact_class_mass_bound {θ : ℝ} (hθ : 0 ≤ θ) (hBound : FixedModulusClassBound θ)
    {K H : ℕ} (hH : 0 < H) {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) :
    ∀ᶠ X : ℕ in atTop, ∀ m : ℕ, 0 < m →
      (classModulus (cappedGlobalModes X L) globalLevel H m:ℝ) ≤ (X:ℝ)^(81/400:ℝ) →
      massSquareByClass (classModulus (cappedGlobalModes X L) globalLevel H m) K X
        (compactNonpoleModes X m L T H) ≤ θ := by
  obtain ⟨q₀,hq₀⟩ := hBound K L T
  filter_upwards [eventually_bounded_modes_have_large_level (max q₀ 1) hL hT,
    eventually_ge_atTop (1:ℕ)] with X hX hX1 m hm hModBound
  let S := compactNonpoleModes X m L T H
  let q := classModulus (cappedGlobalModes X L) globalLevel H m
  have hq : 0 < q := commonModulus_pos hH hm L
  let _ : NeZero q := ⟨hq.ne'⟩
  have hLarge (i : GlobalMode) (hi : i ∈ S) : max q₀ 1 < globalLevel i := by
    obtain ⟨hn,hi',_,ht⟩ := mem_compactNonpoleModes.mp hi
    exact hX _ (mem_filter.mp hi').1 hn (mem_filter.mp hi').2 ht
  by_cases hS : S.Nonempty
  · obtain ⟨i,hi⟩ := hS
    have hd : globalLevel i ∣ q := compactNonpole_level_dvd_class hi
    have hq' : q₀ ≤ q := (le_max_left _ _).trans ((hLarge _ hi).le.trans (Nat.le_of_dvd hq hd))
    exact (class_mass_le_modulus_class_mass (X:=X) (q:=q) (K:=K) hX1 rfl
      hModBound (fun i hi => (le_max_right _ _).trans_lt (hLarge i hi))).trans (hq₀ q hq' _)
  · have hEmpty : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    change massSquareByClass q K X S ≤ θ
    simp only [hEmpty,massSquareByClass,image_empty,sum_empty]
    exact hθ

end
end GoldbachSignedPairs

end

section

namespace GoldbachSignedPairs

open Finset Filter Complex GoldbachWeightedMajorResidual
open scoped Classical

private theorem norm_sub_triangle (a b c : ℂ) : ‖a-c‖ ≤ ‖a-b‖+‖b-c‖ := by
  rw [show a-c = (a-b)+(b-c) by ring]
  exact norm_add_le _ _

set_option maxHeartbeats 3500000 in
theorem signed_floor_from_fixed_modulus_bound {θ η L : ℝ} (hθ : 0 ≤ θ) (hθ₁ : θ < 1)
    (hSharp : FixedModulusClassBound θ) (hη : 0 < η) (hL : 0 ≤ L)
    (hSep : SeparatedSpectralCutoff η L)
    (hCapped : ∀ᶠ X : ℕ in atTop, ∀ m : ℕ, 0 < m → Even m →
      ‖shortSmoothCoefficient X m-cappedSmoothCoefficient X m L‖ ≤
        ((1-θ)/40)*(X:ℝ)*globalOrdinarySingularSeries m) :
    ∃ (B : ℕ → Finset ℕ) (D c : ℝ), 0 ≤ D ∧ 0 < c ∧
      (∀ᶠ X : ℕ in atTop, ((B X).card:ℝ) ≤ D*(X:ℝ)^(319/400:ℝ)) ∧
      (∀ᶠ X : ℕ in atTop, ∀ m ∈ GoldbachCenterWindows.centralWindow X, Even m →
        m ∉ B X → c*(X:ℝ) ≤ (shortSignedCoefficient X m).re) := by
  let ε := (1-θ)/40
  have hε : 0 < ε := div_pos (sub_pos.mpr hθ₁) (by norm_num)
  obtain ⟨K,H,hK,hH,hSupport⟩ := eventually_norm_capped_sub_supported_le hε L
  obtain ⟨A,hA,hFull⟩ := eventually_norm_supportedSmooth_sub_full_le hη hSep (H:=H) hK
  obtain ⟨T,hT,hCompact⟩ := eventually_norm_supportedFull_sub_compact_le hε L K H
  obtain ⟨D,hD,hExc⟩ := eventually_classModulus_exception_card_le hH L
  obtain ⟨s,hs,hSing⟩ := globalOrdinarySingularSeries_pos_uniform
  have hSharp' := eventually_compact_class_mass_bound (K:=K) hθ hSharp hH hL
    (zero_le_one.trans hT)
  let B (X : ℕ) := (range (4*X+1)).filter (fun m =>
    (X:ℝ)^(81/400:ℝ) < (classModulus (cappedGlobalModes X L) globalLevel H m:ℝ))
  refine ⟨B,D,((1-θ)/8)*s,hD,mul_pos (by linarith only [hθ₁]) hs,hExc,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ),eventually_norm_shortSigned_sub_smooth_le hε,
    hCapped,hSupport,hFull,hCompact,hSharp',
    eventually_const_mul_neg_power_le (div_pos hη (by norm_num : (0:ℝ)<16)) hε A,
    eventually_compactFullCoefficient_re_lower hK hH hL (zero_le_one.trans hT) hθ₁.le]
    with X hX hsmooth hcap hsupp hfull hcompact hsharp hSmall hP m hm he hB
  obtain ⟨hm₁,hm₂⟩ := GoldbachCenterWindows.mem_centralWindow.mp hm
  have hm0 : 0 < m := by omega
  have hmX : m ≤ 4*X := by omega
  have hx : (0:ℝ) < X := by exact_mod_cast (show 0<X from hX)
  have hLeft : (5/2:ℝ)*(X:ℝ) ≤ (m:ℝ) := by
    have h' : (5:ℝ)*(X:ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast hm₁
    linarith only [h']
  have hRight : (m:ℝ) ≤ (7/2:ℝ)*(X:ℝ) := by
    have h' : (2:ℝ)*(m:ℝ) ≤ 7*(X:ℝ) := by exact_mod_cast hm₂
    linarith only [h']
  let S := globalOrdinarySingularSeries m
  have hS : 0 ≤ S := (hs.trans (hSing m hm0 he)).le
  have hMod : (classModulus (cappedGlobalModes X L) globalLevel H m:ℝ) ≤
      (X:ℝ)^(81/400:ℝ) := by
    by_contra! h
    exact hB (mem_filter.mpr ⟨mem_range.mpr (by omega),h⟩)
  have a₁ := hsmooth m hm0 he
  have a₂ := hcap m hm0 he
  have a₃ := hsupp m hm0 he
  have a₄ : ‖supportedSmoothCoefficient X m L K H-supportedFullCoefficient X m L K H‖ ≤
      ε*(X:ℝ)*S := (hfull m hm0 hmX he hLeft hRight).trans (by
    change A*(X:ℝ)*S*(X:ℝ)^(-(η/16)) ≤ ε*(X:ℝ)*S
    calc
      _ = (A*(X:ℝ)^(-(η/16)))*((X:ℝ)*S) := by ring
      _ ≤ ε*((X:ℝ)*S) := mul_le_mul_of_nonneg_right hSmall (mul_nonneg hx.le hS)
      _ = _ := by ring)
  have a₅ := hcompact m hm0 hLeft hRight
  have hErr : ‖shortSignedCoefficient X m-compactFullCoefficient X m L T K H‖ ≤
      5*ε*(X:ℝ)*S := by
    calc
      _ ≤ ‖shortSignedCoefficient X m-shortSmoothCoefficient X m‖+
        ‖shortSmoothCoefficient X m-cappedSmoothCoefficient X m L‖+
        ‖cappedSmoothCoefficient X m L-supportedSmoothCoefficient X m L K H‖+
        ‖supportedSmoothCoefficient X m L K H-supportedFullCoefficient X m L K H‖+
        ‖supportedFullCoefficient X m L K H-compactFullCoefficient X m L T K H‖ := by
          have h₁ := norm_sub_triangle (shortSignedCoefficient X m) (supportedFullCoefficient X m L K H)
            (compactFullCoefficient X m L T K H)
          have h₂ := norm_sub_triangle (shortSignedCoefficient X m) (supportedSmoothCoefficient X m L K H)
            (supportedFullCoefficient X m L K H)
          have h₃ := norm_sub_triangle (shortSignedCoefficient X m) (cappedSmoothCoefficient X m L)
            (supportedSmoothCoefficient X m L K H)
          have h₄ := norm_sub_triangle (shortSignedCoefficient X m) (shortSmoothCoefficient X m)
            (cappedSmoothCoefficient X m L)
          linarith only [h₁,h₂,h₃,h₄]
      _ ≤ _ := by linarith only [a₁,a₂,a₃,a₄,a₅,
        show (1-θ)/40*(X:ℝ)*S = ε*(X:ℝ)*S by rfl]
  have hRe : (compactFullCoefficient X m L T K H).re-5*ε*(X:ℝ)*S ≤ (shortSignedCoefficient X m).re := by
    have hh := (neg_le_neg (Complex.abs_re_le_norm
      (shortSignedCoefficient X m-compactFullCoefficient X m L T K H))).trans
      (neg_abs_le (shortSignedCoefficient X m-compactFullCoefficient X m L T K H).re)
    rw [Complex.sub_re] at hh
    linarith only [hErr,hh]
  have hFloor := hP m hm0 he hLeft hRight (hsharp m hm0 hMod)
  calc
    _ ≤ ((1-θ)/8)*(X:ℝ)*S := by
      have hs' := (hSing m hm0 he).le
      have hfac : 0 ≤ ((1-θ)/8)*(X:ℝ) :=
        mul_nonneg (div_nonneg (sub_nonneg.mpr hθ₁.le) (by norm_num)) hx.le
      calc
        _ = ((1-θ)/8)*(X:ℝ)*s := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hs' hfac
    _ ≤ _ := by
      have hr : ((1-θ)/8)*(X:ℝ)*S = (1-θ)*((X:ℝ)/4)*S-5*ε*(X:ℝ)*S := by
        dsimp only [ε]; ring
      linarith only [hFloor,hRe,hr]

end GoldbachSignedPairs

end

section
namespace GoldbachSignedPairs

open Finset Filter
open GoldbachWeightedException (cutoff)
open scoped Classical

private theorem nominalCutoff_bounds (X : ℕ) (hX : 2^200 ≤ 4*X) :
    let x := ((4*X:ℕ):ℝ)
    let P := ⌊x^(41/200:ℝ)⌋₊
    x^(203/1000:ℝ) ≤ 2*(P:ℝ) ∧ x^(1/5:ℝ) ≤ (P:ℝ) ∧
      (P:ℝ) ≤ x^(41/200:ℝ) := by
  dsimp only
  have hx : (2:ℝ)^200 ≤ ((4*X:ℕ):ℝ) := by exact_mod_cast hX
  have hx₁ : 1 ≤ ((4*X:ℕ):ℝ) := (by norm_num : (1:ℝ) ≤ 2^200).trans hx
  have hC : ((4*X:ℕ):ℝ)^(203/1000:ℝ) ≤ ((4*X:ℕ):ℝ)^(41/200:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num)
  obtain ⟨h₁,h₂,h₃,_⟩ := floor_cutoff_bounds hx hC le_rfl
  exact ⟨h₁,h₂,h₃⟩

noncomputable abbrev nominalCutoff : GoldbachMajorCutoff where
  value X := ⌊((4*X:ℕ):ℝ)^(41/200:ℝ)⌋₊
  lower X hX := (nominalCutoff_bounds X hX).1
  principalLower X hX := (nominalCutoff_bounds X hX).2.1
  upper X hX := (nominalCutoff_bounds X hX).2.2

theorem cutoff_value_le_nominal (C : GoldbachMajorCutoff) {X : ℕ} (hX : 2^200 ≤ 4*X) :
    C.value X ≤ nominalCutoff.value X :=
  Nat.le_floor (C.upper X hX)

/-- The nominal spectrum controls all its smaller-cutoff spectra with the
same mass and tail constants. -/
theorem eventually_nominal_mode_mass_and_tail :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ X : ℕ in atTop, ∀ P : ℕ, P ≤ nominalCutoff.value X →
      (∑ i ∈ globalModesAtCutoff X P,modeMass X i) ≤ A ∧
      ∀ L : ℝ, 0 ≤ L →
        (∑ i ∈ (globalModesAtCutoff X P).filter (fun i => L ≤ modeGap X i),modeMass X i) ≤
          A*Real.exp (-((77/12500:ℝ)*L)) := by
  obtain ⟨A,hA,h⟩ := @short_global_mass_and_tail nominalCutoff
  refine ⟨A,hA,?_⟩
  filter_upwards [h] with X hX P hP
  have hmodes : @globalModesAt nominalCutoff X = globalModesAtCutoff X (nominalCutoff.value X) :=
    @globalModesAt_eq_atCutoff nominalCutoff X
  have hsub := globalModesAtCutoff_subset (X:=X) hP
  refine ⟨?_,?_⟩
  · have hSum := congrArg (fun G : Finset GlobalMode => ∑ i ∈ G, modeMass X i) hmodes
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => modeMass_nonneg X i)).trans
      (hSum.ge.trans hX.1)
  · intro L hL
    have hs :
        (globalModesAtCutoff X P).filter (fun i => L ≤ modeGap X i) ⊆
          (globalModesAtCutoff X (nominalCutoff.value X)).filter (fun i => L ≤ modeGap X i) := by
      intro i hi
      obtain ⟨h₁,h₂⟩ := mem_filter.mp hi
      exact mem_filter.mpr ⟨hsub h₁,h₂⟩
    have hSum := congrArg (fun G : Finset GlobalMode =>
      ∑ i ∈ G.filter (fun i => L ≤ modeGap X i), modeMass X i) hmodes
    exact (sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => modeMass_nonneg X i)).trans
      (hSum.ge.trans (hX.2 L hL))

/-- The spectral mass and tail bounds are uniform over all admissible
cutoff instances, so the gap cap can be fixed before selecting one. -/
theorem eventually_all_majorCutoffs_mode_mass_and_tail :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ X : ℕ in atTop, ∀ C : GoldbachMajorCutoff,
      (∑ i ∈ @globalModesAt C X,modeMass X i) ≤ A ∧
      ∀ L : ℝ, 0 ≤ L →
        (∑ i ∈ (@globalModesAt C X).filter (fun i => L ≤ modeGap X i),modeMass X i) ≤
          A*Real.exp (-((77/12500:ℝ)*L)) := by
  obtain ⟨A,hA,h⟩ := eventually_nominal_mode_mass_and_tail
  refine ⟨A,hA,?_⟩
  filter_upwards [h,eventually_ge_atTop (2^200:ℕ)] with X hX hLarge C
  have hC := hX (C.value X) (cutoff_value_le_nominal C (by omega))
  have hg : @globalModesAt C X = globalModesAtCutoff X (C.value X) := @globalModesAt_eq_atCutoff C X
  refine ⟨?_,?_⟩
  · exact (congrArg (fun G : Finset GlobalMode => ∑ i ∈ G, modeMass X i) hg).le.trans hC.1
  · intro L hL
    exact (congrArg (fun G : Finset GlobalMode =>
      ∑ i ∈ G.filter (fun i => L ≤ modeGap X i), modeMass X i) hg).le.trans (hC.2 L hL)

theorem eventually_nominal_capped_mode_card_bounded (L : ℝ) :
    ∃ N : ℕ, ∀ᶠ X : ℕ in atTop,
      ((globalModesAtCutoff X (nominalCutoff.value X)).filter (fun i => modeGap X i ≤ L)).card ≤ N := by
  obtain ⟨A,_,h⟩ := @short_global_mass_and_tail nominalCutoff
  refine ⟨⌈A*Real.exp L⌉₊,?_⟩
  filter_upwards [h] with X hX
  have hcard :
      ((@globalModesAt nominalCutoff X).filter (fun i => modeGap X i ≤ L)).card ≤ ⌈A*Real.exp L⌉₊ := by
    exact_mod_cast (@capped_mode_card_le nominalCutoff X A hX.1 L).trans (Nat.le_ceil (A*Real.exp L))
  have hg : @globalModesAt nominalCutoff X = globalModesAtCutoff X (nominalCutoff.value X) :=
    @globalModesAt_eq_atCutoff nominalCutoff X
  exact (congrArg (fun G : Finset GlobalMode => (G.filter (fun i => modeGap X i ≤ L)).card)
    hg).ge.trans hcard

/-- After fixing the spectral cap, choose a cutoff instance which separates
the modes of that same capped spectrum. -/
theorem exists_majorCutoff_separated (L : ℝ) :
    ∃ (C : GoldbachMajorCutoff) (η : ℝ), 0 < η ∧ @SeparatedSpectralCutoff C η L := by
  obtain ⟨N,hN⟩ := eventually_nominal_capped_mode_card_bounded L
  obtain ⟨η,P,hη,hP,hSep⟩ := exists_adaptive_mode_cutoff L hN
  let C : GoldbachMajorCutoff :=
    ⟨P,fun X hX => (hP X hX).1,fun X hX => (hP X hX).2.1,fun X hX => (hP X hX).2.2⟩
  refine ⟨C,η,hη,?_⟩
  change ∀ᶠ X : ℕ in atTop, ∀ i ∈ @cappedGlobalModes C X L,
    modeTransitionScale i < (P X:ℝ)/(X:ℝ)^η ∨ (P X:ℝ)*(X:ℝ)^η < modeTransitionScale i
  filter_upwards [hSep] with X hX i hi
  have hg : @globalModesAt C X = globalModesAtCutoff X (P X) := @globalModesAt_eq_atCutoff C X
  have hmem : i ∈ @globalModesAt C X ∧ modeGap X i ≤ L := mem_filter.mp hi
  have hPmem := (congrArg (fun G : Finset GlobalMode => i ∈ G) hg).mp hmem.1
  exact hX i hPmem hmem.2

end GoldbachSignedPairs
end

section
namespace GoldbachSignedPairs

open Finset Filter Complex GoldbachWeightedMajorResidual
open GoldbachWeightedException (cutoff)
open scoped Classical

private theorem eventually_cutoff_mode_subset_nominal :
    ∀ᶠ X : ℕ in atTop, ∀ C : GoldbachMajorCutoff,
      @globalModesAt C X ⊆ @globalModesAt nominalCutoff X := by
  filter_upwards [eventually_ge_atTop (2^200:ℕ)] with X hX C
  rw [@globalModesAt_eq_atCutoff C X,@globalModesAt_eq_atCutoff nominalCutoff X]
  exact globalModesAtCutoff_subset (cutoff_value_le_nominal C (by omega))

theorem exists_uniform_gap_cap {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ X : ℕ in atTop, ∀ C : GoldbachMajorCutoff,
      ∀ m : ℕ, 0 < m → Even m →
        ‖@shortSmoothCoefficient C X m-@cappedSmoothCoefficient C X m L‖ ≤
          ε*(X:ℝ)*globalOrdinarySingularSeries m := by
  obtain ⟨A,hA,hMass⟩ := eventually_all_majorCutoffs_mode_mass_and_tail
  obtain ⟨H,hH,hAbs⟩ := @globalPairCoefficient_absolute_le nominalCutoff
  obtain ⟨c,hc,hS⟩ := globalOrdinarySingularSeries_pos_uniform
  let v := ε/(2*H*A^2)
  have hv : 0 < v := by dsimp [v]; positivity
  let b : ℝ := 77/12500
  have hb : 0 < b := by norm_num [b]
  let L := max 0 (-Real.log v/b)
  have hL : 0 ≤ L := le_max_left _ _
  have he : Real.exp (-(b*L)) ≤ v := by
    rw [← Real.exp_log hv]
    apply Real.exp_le_exp.mpr
    have h : -Real.log v/b ≤ L := le_max_right _ _
    have h' := (div_le_iff₀ hb).mp h
    linarith only [h']
  refine ⟨L,hL,?_⟩
  filter_upwards [hMass,eventually_cutoff_mode_subset_nominal,eventually_ge_atTop (1:ℕ)]
    with X hMass hSub hX C m hm hEven
  letI : GoldbachMajorCutoff := C
  have hX0 : 0 < X := hX
  have hs : 0 ≤ globalOrdinarySingularSeries m := (hc.trans (hS m hm hEven)).le
  have hMassBound := hMass C
  have hTail : (∑ i ∈ (globalModesAt X).filter (fun i => ¬(modeGap X i ≤ L)),modeMass X i)
      ≤ A*Real.exp (-(b*L)) := by
    refine (sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => modeMass_nonneg X i)).trans
      (hMassBound.2 L hL)
    intro i hi
    obtain ⟨hi,ht⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hi,(lt_of_not_ge ht).le⟩
  refine (norm_shortSmooth_sub_capped_le_mass (m:=m) hX0 L (mul_nonneg hH.le hs)
    (fun i hi j hj => hAbs hm hEven (hSub C hi) (hSub C hj) _)).trans ?_
  have hTail0 : 0 ≤ ∑ i ∈ (globalModesAt X).filter (fun i => ¬(modeGap X i ≤ L)),modeMass X i :=
    sum_nonneg (fun i _ => modeMass_nonneg X i)
  calc
    _ ≤ 2*(X:ℝ)*(H*globalOrdinarySingularSeries m)*A*(A*Real.exp (-(b*L))) := by
      gcongr
      exact hMassBound.1
    _ ≤ 2*(X:ℝ)*(H*globalOrdinarySingularSeries m)*A*(A*v) := by gcongr
    _ = _ := by dsimp [v]; field_simp [hH.ne',hA.ne']

/-- The class moment bound needed for the positive signed major arc term. -/
theorem binary_shift_exception_union_of_class_bound {θ : ℝ}
    (hθ : 0 ≤ θ) (hθ₁ : θ < 1) (hSharp : FixedModulusClassBound θ) :
    let G := fun m : ℕ => ((Finset.range (m+1)).filter
      (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card
    ∃ X₀ : ℕ, ∀ X ≥ X₀,
      let L := Nat.log 2 X / 2
      let E := (Finset.Ico X (2*X)).filter (fun n => Even n ∧
        0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e)=0)).card)
      E.card^5 ≤ X^4 := by
  have hε : 0 < (1-θ)/40 := div_pos (sub_pos.mpr hθ₁) (by norm_num)
  obtain ⟨L,hL,hLBound⟩ := exists_uniform_gap_cap hε
  obtain ⟨C,η,hη,hSep⟩ := exists_majorCutoff_separated L
  letI : GoldbachMajorCutoff := C
  have hCap := hLBound.mono (fun X h => h C)
  obtain ⟨B,D,c,hD,hc,hCount,hFloor⟩ :=
    signed_floor_from_fixed_modulus_bound hθ hθ₁ hSharp hη hL hSep hCap
  change ∃ N : ℕ, ∀ X ≥ N, (GoldbachPolynomialMinor205.failedShifts X).card^5 ≤ X^4
  exact failed_shifts_of_short_floor_outside B hD hc hCount (by
    simpa only [shortSignedCoefficient,signedModelCoefficient,GoldbachWeightedMajorResidual.localModel,
      GoldbachWeightedMajorResidual.localPhase,GoldbachWeightedMajorResidual.domain] using hFloor)

end GoldbachSignedPairs

end
end


section
/-!
Adapted from the test-function and Laplace-transform proofs in Eric Naslund's
`enaslund/linniks-constant-3.99`, revision ecdbe3e3e08ad499d2c749ff417cc461f57334c5,
Apache-2.0. Covers Heath-Brown's parabolic test, without the analytic estimates
assumed in the source project's graded near-density theorem.
-/


/-- A concrete cutoff instance for baseline declarations whose source was
checked under a global cutoff variable. -/
private theorem portable_nominal_cutoff_bounds (X : ℕ) (hX : 2^200≤4*X) :
    let x := (((4*X:ℕ):ℝ))
    let y := x^(41/200:ℝ)
    x^(203/1000:ℝ)≤2*(⌊y⌋₊:ℝ) ∧ x^(1/5:ℝ)≤(⌊y⌋₊:ℝ) ∧ (⌊y⌋₊:ℝ)≤y := by
  intro x y
  have hXr : (2:ℝ)^200≤x := by
    change (2:ℝ)^200≤((4*X:ℕ):ℝ)
    exact_mod_cast hX
  have hx1 : 1≤x := (show (1:ℝ)≤(2:ℝ)^200 by norm_num).trans hXr
  have hx0 : 0<x := zero_lt_one.trans_le hx1
  have ha := Real.rpow_le_rpow (by norm_num : (0:ℝ)≤(2:ℝ)^200) hXr
    (by norm_num : (0:ℝ)≤1/200)
  rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2)] at ha
  norm_num at ha
  have hm : 2*x^(1/5:ℝ)≤y := calc
    _ ≤ x^(1/200:ℝ)*x^(1/5:ℝ) := mul_le_mul_of_nonneg_right ha (by positivity)
    _ = y := by rw [←Real.rpow_add hx0]; norm_num [y]
  have hy0 : 0≤y := Real.rpow_nonneg hx0.le _
  have h1 : 1≤x^(1/5:ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hfloor : y < (⌊y⌋₊:ℝ)+1 := Nat.lt_floor_add_one y
  have hpow : x^(203/1000:ℝ)≤y := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  refine ⟨hpow.trans ?_,?_,Nat.floor_le hy0⟩
  · linarith only [hfloor,hm,h1]
  · linarith only [hfloor,hm,h1]

noncomputable local instance : GoldbachMajorCutoff where
  value X := ⌊((4*X:ℕ):ℝ)^(41/200:ℝ)⌋₊
  lower X hX := (portable_nominal_cutoff_bounds X hX).1
  principalLower X hX := (portable_nominal_cutoff_bounds X hX).2.1
  upper X hX := (portable_nominal_cutoff_bounds X hX).2.2

theorem Conjectures.Goldbach.BinaryShiftExceptionUnion :
    let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∃ X₀ : ℕ, ∀ X ≥ X₀, let L := Nat.log 2 X / 2; let E := (Finset.Ico X (2*X)).filter (fun n => Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e)=0)).card); E.card^5 ≤ X^4 := by
  obtain ⟨θ, hθ, hθ₁, hClass⟩ :=
    GoldbachSignedPairs.fixedModulusClassBound_via_public_square
  exact GoldbachSignedPairs.binary_shift_exception_union_of_class_bound hθ hθ₁ hClass
