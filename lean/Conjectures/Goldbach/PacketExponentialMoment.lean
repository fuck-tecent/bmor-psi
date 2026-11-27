import Mathlib

open MeasureTheory Finset
open scoped Interval

namespace Conjectures.Goldbach.PacketExponentialMoment_aux
noncomputable section

def orb (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n+1 => fun t => g t + orb g n (2*t)

theorem orb_cont {g : ℝ → ℝ} (hg : Continuous g) (n : ℕ) : Continuous (orb g n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact hg.add (ih.comp (continuous_const.mul continuous_id))

theorem orb_period {g : ℝ → ℝ} (hg : ∀ t, g (t+1) = g t) (n : ℕ) (t : ℝ) :
    orb g n (t+1) = orb g n t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [orb, hg, show 2*(t+1)=2*t+1+1 by ring, ih]

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

def g0 (u : ℝ) : ℝ := Real.cos (2*Real.pi*u)

theorem g0_cont : Continuous g0 := by unfold g0; fun_prop

theorem g0_period (t : ℝ) : g0 (t+1) = g0 t := by
  unfold g0
  rw [show 2*Real.pi*(t+1) = 2*Real.pi*t + 2*Real.pi by ring, Real.cos_add_two_pi]

theorem orb_g0_eq (m : ℕ) (v : ℝ) :
    orb g0 m v = ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^j*v) := by
  induction m generalizing v with
  | zero => simp [orb]
  | succ m ih =>
      show orb g0 (m+1) v = ∑ j ∈ Finset.range (m+1), Real.cos (2*Real.pi*(2:ℝ)^j*v)
      have horb : orb g0 (m+1) v = g0 v + orb g0 m (2*v) := by simp only [orb]
      rw [horb, Finset.sum_range_succ', ih (2*v)]
      have h1 : g0 v = Real.cos (2*Real.pi*(2:ℝ)^(0:ℕ)*v) := by simp [g0]
      have h2 : ∀ k ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^k*(2*v))
          = Real.cos (2*Real.pi*(2:ℝ)^(k+1)*v) := by
        intro k _
        have hk : 2*Real.pi*(2:ℝ)^k*(2*v) = 2*Real.pi*(2:ℝ)^(k+1)*v := by
          rw [pow_succ]; ring
        rw [hk]
      have h3 : (∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^j*(2*v)))
          = ∑ k ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(k+1)*v) := Finset.sum_congr rfl h2
      rw [h1, h3]
      ring

theorem doubling (h : ℝ → ℝ) (hh : Continuous h) (hper : ∀ t, h (t+1) = h t) :
    (∫ t in (0:ℝ)..1, h (2*t)) = ∫ t in (0:ℝ)..1, h t := by
  have h2c : Continuous (fun t : ℝ => (2:ℝ)*t) := continuous_const.mul continuous_id
  rw [halves (fun t => h (2*t)) (hh.comp h2c)]
  simp only [show ∀ t : ℝ, 2*((1/2)*t)=t by intro t; ring,
    show ∀ t : ℝ, 2*((1/2)*t+1/2)=t+1 by intro t; ring, hper]
  rw [intervalIntegral.integral_add (hh.intervalIntegrable ..) (hh.intervalIntegrable ..)]
  ring

theorem moment_bound (m : ℕ) (s : ℝ) :
    (∫ t in (0:ℝ)..1, Real.exp (s * orb g0 m t)) ≤ (Real.cosh s)^m := by
  induction m with
  | zero =>
      have h0 : (∫ t in (0:ℝ)..1, Real.exp (s * orb g0 0 t)) = 1 := by
        have hc : (fun t => Real.exp (s * orb g0 0 t)) = fun _ => (1:ℝ) := by
          funext t; simp [orb]
        rw [hc, intervalIntegral.integral_const]
        norm_num [smul_eq_mul]
      have h1 : (1:ℝ) ≤ (Real.cosh s)^(0:ℕ) := by
        rw [pow_zero]
      exact h0.le.trans h1
  | succ m ih =>
      have hf : Continuous (fun t => Real.exp (s * orb g0 (m+1) t)) :=
        Real.continuous_exp.comp (continuous_const.mul (orb_cont g0_cont (m+1)))
      have hc1 : Continuous (fun t : ℝ => (1/2:ℝ)*t) := continuous_const.mul continuous_id
      have hc2 : Continuous (fun t : ℝ => (1/2:ℝ)*t + 1/2) := hc1.add continuous_const
      have hf2 : Continuous (fun t => Real.exp (s * orb g0 (m+1) ((1/2)*t))
            + Real.exp (s * orb g0 (m+1) ((1/2)*t + 1/2))) :=
        (hf.comp hc1).add (hf.comp hc2)
      have hg2 : Continuous (fun t => 2 * Real.cosh s * Real.exp (s * orb g0 m t)) :=
        continuous_const.mul (Real.continuous_exp.comp
          (continuous_const.mul (orb_cont g0_cont m)))
      have pair (t : ℝ) : Real.exp (s * orb g0 (m+1) ((1/2)*t))
            + Real.exp (s * orb g0 (m+1) ((1/2)*t + 1/2))
          ≤ 2 * Real.cosh s * Real.exp (s * orb g0 m t) := by
        have hg1 : g0 ((1/2)*t) = Real.cos (Real.pi * t) := by
          unfold g0
          rw [show 2*Real.pi*((1/2)*t) = Real.pi*t by ring]
        have hg3 : g0 ((1/2)*t + 1/2) = -(Real.cos (Real.pi * t)) := by
          unfold g0
          rw [show 2*Real.pi*((1/2)*t + 1/2) = Real.pi*t + Real.pi by ring, Real.cos_add_pi]
        have ho1 : orb g0 m (2*((1/2)*t)) = orb g0 m t := by
          rw [show 2*((1/2)*t) = t by ring]
        have ho2 : orb g0 m (2*((1/2)*t + 1/2)) = orb g0 m t := by
          rw [show 2*((1/2)*t + 1/2) = t + 1 by ring, orb_period g0_period m t]
        have e1 : orb g0 (m+1) ((1/2)*t) = Real.cos (Real.pi*t) + orb g0 m t := by
          have h : orb g0 (m+1) ((1/2)*t) = g0 ((1/2)*t) + orb g0 m (2*((1/2)*t)) := by
            simp only [orb]
          rw [h, hg1, ho1]
        have e2 : orb g0 (m+1) ((1/2)*t + 1/2)
            = -(Real.cos (Real.pi*t)) + orb g0 m t := by
          have h : orb g0 (m+1) ((1/2)*t + 1/2)
              = g0 ((1/2)*t + 1/2) + orb g0 m (2*((1/2)*t + 1/2)) := by
            simp only [orb]
          rw [h, hg3, ho2]
        rw [e1, e2]
        have hsum : Real.exp (s * (Real.cos (Real.pi*t) + orb g0 m t))
              + Real.exp (s * (-(Real.cos (Real.pi*t)) + orb g0 m t))
            = (Real.exp (s * Real.cos (Real.pi*t)) + Real.exp (-(s * Real.cos (Real.pi*t))))
              * Real.exp (s * orb g0 m t) := by
          simp only [mul_add, Real.exp_add, mul_neg]
          ring
        rw [hsum]
        have hcc : Real.exp (s * Real.cos (Real.pi*t)) + Real.exp (-(s * Real.cos (Real.pi*t)))
            = 2 * Real.cosh (s * Real.cos (Real.pi*t)) := by
          rw [Real.cosh_eq]; ring
        have hcos : Real.cosh (s * Real.cos (Real.pi*t)) ≤ Real.cosh s := by
          rw [Real.cosh_le_cosh, abs_mul]
          calc |s| * |Real.cos (Real.pi*t)| ≤ |s| * 1 :=
                  mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg s)
            _ = |s| := by ring
        rw [hcc]
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      have hX : (∫ t in (0:ℝ)..1, (Real.exp (s * orb g0 (m+1) ((1/2)*t))
            + Real.exp (s * orb g0 (m+1) ((1/2)*t + 1/2))))
          ≤ 2 * Real.cosh s * (∫ t in (0:ℝ)..1, Real.exp (s * orb g0 m t)) := by
        have him := intervalIntegral.integral_mono_on (μ:=volume) (a:=(0:ℝ)) (b:=1) (by norm_num)
          (hf2.intervalIntegrable 0 1) (hg2.intervalIntegrable 0 1) (fun t _ => pair t)
        rw [intervalIntegral.integral_const_mul] at him
        exact him
      have hhalf : (∫ t in (0:ℝ)..1, Real.exp (s * orb g0 (m+1) t))
          = (1/2:ℝ) * (∫ t in (0:ℝ)..1, (Real.exp (s * orb g0 (m+1) ((1/2)*t))
            + Real.exp (s * orb g0 (m+1) ((1/2)*t + 1/2)))) :=
        halves (fun t => Real.exp (s * orb g0 (m+1) t)) hf
      calc (∫ t in (0:ℝ)..1, Real.exp (s * orb g0 (m+1) t))
          = (1/2:ℝ) * (∫ t in (0:ℝ)..1, (Real.exp (s * orb g0 (m+1) ((1/2)*t))
              + Real.exp (s * orb g0 (m+1) ((1/2)*t + 1/2)))) := hhalf
        _ ≤ (1/2:ℝ) * (2 * Real.cosh s * (∫ t in (0:ℝ)..1, Real.exp (s * orb g0 m t))) :=
            mul_le_mul_of_nonneg_left hX (by norm_num)
        _ = Real.cosh s * (∫ t in (0:ℝ)..1, Real.exp (s * orb g0 m t)) := by ring
        _ ≤ Real.cosh s * (Real.cosh s)^m :=
            mul_le_mul_of_nonneg_left ih (Real.cosh_pos s).le
        _ = (Real.cosh s)^(m+1) := by rw [pow_succ]; ring

end
end Conjectures.Goldbach.PacketExponentialMoment_aux

open Conjectures.Goldbach.PacketExponentialMoment_aux in
theorem Conjectures.Goldbach.PacketExponentialMoment :
    let T := fun (m : ℕ) (t : ℝ) => ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t); ∀ (m : ℕ) (s : ℝ), intervalIntegral (fun t => Real.exp (s*T m t)) (0:ℝ) 1 MeasureTheory.volume ≤ (Real.cosh s)^m := by
  intro T m s
  have hT (t : ℝ) : T m t = orb g0 m (2*t) := by
    rw [orb_g0_eq]
    show (∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))
        = ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^j*(2*t))
    have h2 : ∀ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)
        = Real.cos (2*Real.pi*(2:ℝ)^j*(2*t)) := by
      intro j _
      have hj : 2*Real.pi*(2:ℝ)^(j+1)*t = 2*Real.pi*(2:ℝ)^j*(2*t) := by
        rw [pow_succ]; ring
      rw [hj]
    exact Finset.sum_congr rfl h2
  have hh : Continuous (fun u => Real.exp (s * orb g0 m u)) :=
    Real.continuous_exp.comp (continuous_const.mul (orb_cont g0_cont m))
  have hper (t : ℝ) : (fun u => Real.exp (s * orb g0 m u)) (t+1)
      = (fun u => Real.exp (s * orb g0 m u)) t := by
    show Real.exp (s * orb g0 m (t+1)) = Real.exp (s * orb g0 m t)
    rw [orb_period g0_period m t]
  have hdoub : (∫ t in (0:ℝ)..1, Real.exp (s * orb g0 m (2*t)))
      = ∫ t in (0:ℝ)..1, Real.exp (s * orb g0 m t) := doubling _ hh hper
  calc intervalIntegral (fun t => Real.exp (s*T m t)) (0:ℝ) 1 MeasureTheory.volume
      = ∫ t in (0:ℝ)..1, Real.exp (s * orb g0 m (2*t)) := by simp only [hT]
    _ = ∫ t in (0:ℝ)..1, Real.exp (s * orb g0 m t) := hdoub
    _ ≤ (Real.cosh s)^m := moment_bound m s
