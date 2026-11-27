import Mathlib

open MeasureTheory Finset
open scoped Interval
namespace Goldbach.LacunarySpectrum
noncomputable section

def orbit (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n+1 => fun t => g t + orbit g n (2*t)

theorem orbit_cont {g : ℝ → ℝ} (hg : Continuous g) (n : ℕ) : Continuous (orbit g n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact hg.add (ih.comp (continuous_const.mul continuous_id))

theorem orbit_period {g : ℝ → ℝ} (hg : ∀ t, g (t+1) = g t) (n : ℕ) (t : ℝ) :
    orbit g n (t+1) = orbit g n t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [orbit,hg,show 2*(t+1)=2*t+1+1 by ring,ih]

/-- Average over the two preimages of the doubling map. -/
theorem halves (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in (0:ℝ)..1, f t) =
      (1/2:ℝ)*(∫ t in (0:ℝ)..1, f ((1/2)*t) + f ((1/2)*t + 1/2)) := by
  have h1 := intervalIntegral.integral_comp_mul_left (a:=(0:ℝ)) (b:=1) f (by norm_num : (1/2:ℝ) ≠ 0)
  have h2 := intervalIntegral.integral_comp_mul_add (a:=(0:ℝ)) (b:=1) f (by norm_num : (1/2:ℝ) ≠ 0) (1/2)
  rw [intervalIntegral.integral_add (by exact (hf.comp (continuous_const.mul continuous_id)).intervalIntegrable ..)
    (by exact (hf.comp ((continuous_const.mul continuous_id).add continuous_const)).intervalIntegrable ..)]
  rw [h1,h2]
  norm_num
  have h := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable (0:ℝ) (1/2)) (hf.intervalIntegrable (1/2) (1:ℝ))
  linarith only [h]

/-- Pairing the inverse branches cancels the odd part of each exponential. -/
theorem exp_moment {g : ℝ → ℝ} (hg : Continuous g) (hs : ∀ t, g (t+1/2) = -g t)
    (hb : ∀ t, |g t| ≤ 1) (n : ℕ) :
    (∫ t in (0:ℝ)..1, Real.exp (orbit g n t / 2)) ≤ Real.exp ((n:ℝ)/8) := by
  have per (t : ℝ) : g (t+1)=g t := by rw [show t+1=t+1/2+1/2 by ring,hs,hs,neg_neg]
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    let f := fun t => Real.exp (orbit g (n+1) t / 2)
    have hf : Continuous f := Real.continuous_exp.comp ((orbit_cont hg _).div_const _)
    have pair (t : ℝ) : f ((1/2)*t) + f ((1/2)*t+1/2) ≤
        2*Real.exp (1/8)*Real.exp (orbit g n t/2) := by
      simp only [f,orbit,hs,show 2*((1/2)*t)=t by ring,
        show 2*((1/2)*t+1/2)=t+1 by ring,orbit_period per,add_div,Real.exp_add,neg_div]
      have hsq := (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (hb ((1/2)*t))
      rw [sq_abs] at hsq
      have hcos := (Real.cosh_le_exp_half_sq (g ((1/2)*t)/2)).trans (Real.exp_le_exp.mpr (by nlinarith only [hsq] : (g ((1/2)*t)/2)^2/2 ≤ 1/8))
      rw [Real.cosh_eq] at hcos
      nlinarith only [mul_le_mul_of_nonneg_right hcos (Real.exp_pos (orbit g n t/2)).le]
    change (∫ t in (0:ℝ)..1, f t) ≤ _
    rw [halves f hf]
    have him := intervalIntegral.integral_mono_on (μ:=volume) (a:=(0:ℝ)) (b:=1) (by norm_num)
      (by exact ((hf.comp (continuous_const.mul continuous_id)).add
        (hf.comp ((continuous_const.mul continuous_id).add continuous_const))).intervalIntegrable ..)
      (by apply Continuous.intervalIntegrable; exact continuous_const.mul (Real.continuous_exp.comp ((orbit_cont hg n).div_const 2)))
      (fun t _ => pair t)
    rw [intervalIntegral.integral_const_mul] at him
    have hprod := mul_le_mul_of_nonneg_left ih (Real.exp_pos (1/8)).le
    rw [Nat.cast_succ,show ((n:ℝ)+1)/8 = 1/8 + n/8 by ring,Real.exp_add]
    linarith only [him,hprod]

def phase (t : ℝ) : ℂ := Complex.exp ((2*Real.pi*t : ℝ)*Complex.I)

theorem phase_cont : Continuous phase := by unfold phase; fun_prop

theorem phase_half (t : ℝ) : phase (t+1/2) = -phase t := by
  unfold phase
  rw [show 2*Real.pi*(t+1/2)=2*Real.pi*t+Real.pi by ring, Complex.ofReal_add]
  rw [add_mul, Complex.exp_add,Complex.exp_pi_mul_I,mul_neg_one]

def spectrum (n : ℕ) (t : ℝ) : ℂ := ∑ j ∈ range n, phase ((2:ℝ)^j*t)

theorem spectrum_cont (n : ℕ) : Continuous (spectrum n) := by
  unfold spectrum
  exact continuous_finsetSum _ (fun j _ => phase_cont.comp (continuous_const.mul continuous_id))

theorem projection (p : ℂ →L[ℝ] ℝ) (n : ℕ) (t : ℝ) :
    p (spectrum n t) = orbit (fun x => p (phase x)) n t := by
  induction n generalizing t with
  | zero => simp [orbit,spectrum]
  | succ n ih =>
    change p (spectrum (n+1) t) = p (phase t) + orbit _ n (2*t)
    rw [← ih]
    simp only [spectrum, sum_range_succ',pow_zero,one_mul,map_add,pow_succ,mul_assoc]
    apply add_comm

theorem moment (p : ℂ →L[ℝ] ℝ) (hp : ∀ z, |p z| ≤ ‖z‖) (n : ℕ) :
    (∫ t in (0:ℝ)..1, Real.exp (p (spectrum n (2*t))/2)) ≤ Real.exp ((n:ℝ)/8) := by
  let g := fun x => p (phase x)
  have hs (t : ℝ) : g (t+1/2) = -g t := by simp only [g,phase_half,map_neg]
  have hper (t : ℝ) : g (t+1)=g t := by rw [show t+1=t+1/2+1/2 by ring,hs,hs,neg_neg]
  have hb (t : ℝ) : |g t| ≤ 1 := (hp _).trans_eq (Complex.norm_exp_ofReal_mul_I _)
  have hg : Continuous g := p.continuous.comp phase_cont
  let f := fun t => Real.exp (orbit g n t / 2)
  have hf : Continuous f := Real.continuous_exp.comp ((orbit_cont hg n).div_const 2)
  simp_rw [projection]
  change (∫ t in (0:ℝ)..1, f (2*t)) ≤ _
  rw [halves (fun t => f (2*t)) (hf.comp (continuous_const.mul continuous_id))]
  have fp (t : ℝ) : f (t+1)=f t := by simp only [f,orbit_period hper]
  simp only [show ∀ t : ℝ, 2*(1/2*t)=t by intro t; ring,
    show ∀ t : ℝ, 2*(1/2*t+1/2)=t+1 by intro t; ring,
    fp]
  rw [intervalIntegral.integral_add (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)]
  linarith only [show (∫ t in (0:ℝ)..1, f t) ≤ Real.exp ((n:ℝ)/8) from exp_moment hg hs hb n]

/-- At least one signed coordinate detects a large complex sum. -/
theorem large (n : ℕ) :
    (∫ t in (0:ℝ)..1, if (9:ℝ)*n ≤ 10*‖spectrum n (2*t)‖ then (1:ℝ) else 0)
    ≤ 4*Real.exp (-(1/10:ℝ)*n) := by
  let S := fun t : ℝ => spectrum n (2*t)
  have hS : Continuous S := (spectrum_cont n).comp (continuous_const.mul continuous_id)
  let E := fun (p : ℂ →L[ℝ] ℝ) (t : ℝ) => Real.exp (p (S t)/2)
  let R := Complex.reCLM
  let I := Complex.imCLM
  let A := fun t => if (9:ℝ)*n ≤ 10*‖S t‖ then (1:ℝ) else 0
  let w := Real.exp (9*(n:ℝ)/40)
  have ec (p : ℂ →L[ℝ] ℝ) : Continuous (E p) :=
    Real.continuous_exp.comp ((p.continuous.comp hS).div_const 2)
  have ei (p : ℂ →L[ℝ] ℝ) : IntervalIntegrable (E p) volume 0 1 := (ec p).intervalIntegrable ..
  have hr (z : ℂ) : |R z| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hi (z : ℂ) : |I z| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hn (p : ℂ →L[ℝ] ℝ) (h : ∀ z, |p z| ≤ ‖z‖) (z : ℂ) : |(-p) z| ≤ ‖z‖ := by
    simpa only [neg_apply,abs_neg] using h z
  have ha : IntervalIntegrable A volume 0 1 := by
    apply (intervalIntegrable_const (c:=(1:ℝ))).mono_fun'
    · exact (measurable_const.ite (measurableSet_le measurable_const
        (measurable_const.mul hS.norm.measurable)) measurable_const).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t => by dsimp [A]; split <;> norm_num)
  have pt (t : ℝ) : w*A t ≤ E R t + E (-R) t + E I t + E (-I) t := by
    dsimp only [A]
    split_ifs with h
    · rw [mul_one]
      have hx := Complex.norm_le_abs_re_add_abs_im (S t)
      have hc : 9*(n:ℝ)/40 ≤ (S t).re/2 ∨ 9*(n:ℝ)/40 ≤ -(S t).re/2 ∨
          9*(n:ℝ)/40 ≤ (S t).im/2 ∨ 9*(n:ℝ)/40 ≤ -(S t).im/2 := by
        by_contra! hh
        obtain ⟨h₁,h₂,h₃,h₄⟩ := hh
        have a : |(S t).re| < 9*n/20 := abs_lt.mpr ⟨by linarith only [h₂], by linarith only [h₁]⟩
        have b : |(S t).im| < 9*n/20 := abs_lt.mpr ⟨by linarith only [h₄], by linarith only [h₃]⟩
        linarith only [h,hx,a,b]
      change w ≤ Real.exp ((S t).re/2) + Real.exp (-(S t).re/2) +
        Real.exp ((S t).im/2) + Real.exp (-(S t).im/2)
      dsimp only [w]
      rcases hc with h | h | h | h <;> linarith only [Real.exp_le_exp.mpr h,
        Real.exp_pos ((S t).re/2),Real.exp_pos (-(S t).re/2),
        Real.exp_pos ((S t).im/2),Real.exp_pos (-(S t).im/2)]
    · simp only [mul_zero,E]
      positivity
  have hint := intervalIntegral.integral_mono_on (μ:=volume) (a:=(0:ℝ)) (b:=1) (by norm_num)
      (ha.const_mul w) ((((ei R).add (ei (-R))).add (ei I)).add (ei (-I))) (fun t _ => pt t)
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
    (((ei R).add (ei (-R))).add (ei I)) (ei (-I)),
    intervalIntegral.integral_add ((ei R).add (ei (-R))) (ei I),
    intervalIntegral.integral_add (ei R) (ei (-R))] at hint
  have htot : w * (∫ t in (0:ℝ)..1, A t) ≤ 4*Real.exp ((n:ℝ)/8) := by
    linarith only [hint,show (∫ t in (0:ℝ)..1, E R t) ≤ _ from moment R hr n,
      show (∫ t in (0:ℝ)..1, E (-R) t) ≤ _ from moment (-R) (hn R hr) n,
      show (∫ t in (0:ℝ)..1, E I t) ≤ _ from moment I hi n,
      show (∫ t in (0:ℝ)..1, E (-I) t) ≤ _ from moment (-I) (hn I hi) n]
  change (∫ t in (0:ℝ)..1, A t) ≤ _
  apply le_of_mul_le_mul_left (a:=w) _ (Real.exp_pos _)
  convert htot using 1
  dsimp only [w]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

end
end Goldbach.LacunarySpectrum

open Goldbach.LacunarySpectrum in
theorem Conjectures.Goldbach.BinaryShiftLargeSpectrum :
    let T := fun (L : ℕ) (t : ℝ) => ∑ j ∈ Finset.range L, Complex.exp (((2*Real.pi*(2:ℝ)^(j+1)*t:ℝ):ℂ)*Complex.I); ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ L : ℕ, intervalIntegral (fun t => if (9:ℝ)*(L:ℝ) ≤ 10*‖T L t‖ then (1:ℝ) else 0) (0:ℝ) 1 MeasureTheory.volume ≤ C*Real.exp (-c*(L:ℝ)) := by
  intro T
  refine ⟨1/10,4,by norm_num,by norm_num,?_⟩
  intro n
  have ht (t : ℝ) : T n t = spectrum n (2*t) := by
    apply Finset.sum_congr rfl
    intro j _
    unfold phase
    rw [show 2*Real.pi*(2:ℝ)^(j+1)*t = 2*Real.pi*((2:ℝ)^j*(2*t)) by rw [pow_succ]; ring]
  simpa only [ht] using large n
