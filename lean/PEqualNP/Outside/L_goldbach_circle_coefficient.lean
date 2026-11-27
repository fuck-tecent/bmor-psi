import Mathlib

/-- The frequency-one additive character `t ↦ exp (2 π i t)`. -/
noncomputable def gbPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

namespace PEqualNP.Outside

theorem L_goldbach_circle_coefficient :
    ∀ (n : ℕ) (w : ℕ → ℝ), let phase : ℝ → ℂ := fun t => Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I); let S : ℝ → ℂ := fun t => Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * phase ((k : ℝ) * t)); let f : ℝ → ℂ := fun t => (S t) ^ 2 * phase (-(n : ℝ) * t); intervalIntegral f (0 : ℝ) 1 MeasureTheory.volume = ((Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) : ℝ) : ℂ) := by
  intro n w
  dsimp only
  change intervalIntegral (fun t : ℝ => (Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * gbPhase ((k : ℝ) * t))) ^ 2 * gbPhase (-(n : ℝ) * t)) (0 : ℝ) 1 MeasureTheory.volume = ((Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) : ℝ) : ℂ)
  have hphase_mul : ∀ x y : ℝ, gbPhase (x + y) = gbPhase x * gbPhase y := by
    intro x y
    unfold gbPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphase_cont : Continuous gbPhase := by
    unfold gbPhase
    fun_prop
  have hphase_exp : ∀ m : ℤ, Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I) = 1 := by
    intro m
    have h : 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hphase_one : ∀ m : ℤ, gbPhase (m : ℝ) = 1 := by
    intro m
    unfold gbPhase
    have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) = 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, hphase_exp m]
  have horth : ∀ m : ℤ, (∫ t in (0 : ℝ)..1, gbPhase ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
    intro m
    have hrewrite : (∫ t in (0 : ℝ)..1, gbPhase ((m : ℝ) * t)) = ∫ t in (0 : ℝ)..1, Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      unfold gbPhase
      congr 1
      push_cast
      ring
    rw [hrewrite]
    by_cases hm : m = 0
    · subst hm
      simp
    · have hmr : (m : ℝ) ≠ 0 := by
        intro hzero
        exact hm (by exact_mod_cast hzero)
      have h1 : (2 * Real.pi * (m : ℝ)) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmr
      have hc : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
        have h2 : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
          simpa [Complex.ofReal_eq_zero] using h1
        exact mul_ne_zero h2 Complex.I_ne_zero
      have hval : Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ)) * Complex.I) = 1 := by
        have hone := hphase_one m
        simpa only [gbPhase] using hone
      rw [integral_exp_mul_complex hc]
      simp [hphase_exp m, hm]
  have hint_single : ∀ (c : ℂ) (a : ℝ), IntervalIntegrable (fun t : ℝ => c * gbPhase (a * t)) MeasureTheory.volume (0 : ℝ) 1 := by
    intro c a
    exact (continuous_const.mul (hphase_cont.comp (by fun_prop))).intervalIntegrable (0 : ℝ) 1
  have hint : ∀ k : ℕ, IntervalIntegrable (fun t : ℝ => Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * gbPhase (((k : ℝ) + (j : ℝ) - (n : ℝ)) * t))) MeasureTheory.volume (0 : ℝ) 1 := by
    intro k
    exact (continuous_finsetSum _ (fun j _ => continuous_const.mul (hphase_cont.comp (by fun_prop)))).intervalIntegrable (0 : ℝ) 1
  have hpoint : ∀ t : ℝ, (Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * gbPhase ((k : ℝ) * t))) ^ 2 * gbPhase (-(n : ℝ) * t) = Finset.sum (Finset.range (n + 1)) (fun k => Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * gbPhase (((k : ℝ) + (j : ℝ) - (n : ℝ)) * t))) := by
    intro t
    rw [pow_two, Finset.sum_mul_sum, Finset.sum_mul]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have h1 : gbPhase ((k : ℝ) * t) * gbPhase ((j : ℝ) * t) = gbPhase (((k : ℝ) + (j : ℝ)) * t) := by
      rw [← hphase_mul]
      congr 1
      ring
    have h2 : gbPhase (((k : ℝ) + (j : ℝ)) * t) * gbPhase (-(n : ℝ) * t) = gbPhase (((k : ℝ) + (j : ℝ) - (n : ℝ)) * t) := by
      rw [← hphase_mul]
      congr 1
      ring
    calc ((w k : ℂ) * gbPhase ((k : ℝ) * t)) * ((w j : ℂ) * gbPhase ((j : ℝ) * t)) * gbPhase (-(n : ℝ) * t)
        = ((w k : ℂ) * (w j : ℂ)) * (gbPhase ((k : ℝ) * t) * gbPhase ((j : ℝ) * t)) * gbPhase (-(n : ℝ) * t) := by ring
      _ = ((w k : ℂ) * (w j : ℂ)) * (gbPhase (((k : ℝ) + (j : ℝ)) * t) * gbPhase (-(n : ℝ) * t)) := by
        rw [h1]; ring
      _ = ((w k : ℂ) * (w j : ℂ)) * gbPhase (((k : ℝ) + (j : ℝ) - (n : ℝ)) * t) := by
        rw [h2]
  have hcollapse : (Finset.sum (Finset.range (n + 1)) (fun k => Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * (if ((k : ℤ) + (j : ℤ) - (n : ℤ)) = 0 then 1 else 0)))) = ((Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) : ℝ) : ℂ) := by
    have hcast : (Finset.sum (Finset.range (n + 1)) (fun p => (w p : ℂ) * (w (n - p) : ℂ))) = ((Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) : ℝ) : ℂ) := by
      simp only [Complex.ofReal_sum (Finset.range (n + 1)) (fun p => w p * w (n - p)), Complex.ofReal_mul]
    rw [← hcast]
    have hinner : ∀ k ∈ Finset.range (n + 1), (Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * (if ((k : ℤ) + (j : ℤ) - (n : ℤ)) = 0 then 1 else 0))) = (w k : ℂ) * (w (n - k) : ℂ) := by
      intro k hk
      have hle : k ≤ n := by
        have := Finset.mem_range.mp hk
        omega
      have hmem : n - k ∈ Finset.range (n + 1) := by
        simp only [Finset.mem_range]
        omega
      have hzero : ∀ j ∈ Finset.range (n + 1), j ≠ n - k → ((w k : ℂ) * (w j : ℂ)) * (if ((k : ℤ) + (j : ℤ) - (n : ℤ)) = 0 then 1 else 0) = 0 := by
        intro j hj hne
        have hjle : j ≤ n := by
          have := Finset.mem_range.mp hj
          omega
        have h2 : ((k : ℤ) + (j : ℤ) - (n : ℤ)) ≠ 0 := by
          intro hz
          have hsum : k + j = n := by omega
          exact hne (by omega)
        simp [h2]
      have hval : ((w k : ℂ) * (w (n - k) : ℂ)) * (if ((k : ℤ) + ((n - k : ℕ) : ℤ) - (n : ℤ)) = 0 then 1 else 0) = (w k : ℂ) * (w (n - k) : ℂ) := by
        have h1 : ((k : ℤ) + ((n - k : ℕ) : ℤ) - (n : ℤ)) = 0 := by omega
        simp [h1]
      calc (Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * (if ((k : ℤ) + (j : ℤ) - (n : ℤ)) = 0 then 1 else 0)))
          = ((w k : ℂ) * (w (n - k) : ℂ)) * (if ((k : ℤ) + ((n - k : ℕ) : ℤ) - (n : ℤ)) = 0 then 1 else 0) := Finset.sum_eq_single_of_mem (n - k) hmem hzero
        _ = (w k : ℂ) * (w (n - k) : ℂ) := hval
    refine Finset.sum_congr rfl (fun k hk => ?_)
    exact hinner k hk
  have hmain : (∫ t in (0 : ℝ)..1, Finset.sum (Finset.range (n + 1)) (fun k => Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * gbPhase (((k : ℝ) + (j : ℝ) - (n : ℝ)) * t)))) = ((Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_finsetSum (fun k _ => hint k)]
    have hstep : ∀ k ∈ Finset.range (n + 1), (∫ t in (0 : ℝ)..1, Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * gbPhase (((k : ℝ) + (j : ℝ) - (n : ℝ)) * t))) = Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * (if ((k : ℤ) + (j : ℤ) - (n : ℤ)) = 0 then 1 else 0)) := by
      intro k _
      rw [intervalIntegral.integral_finsetSum (fun j _ => hint_single ((w k : ℂ) * (w j : ℂ)) (((k : ℝ) + (j : ℝ) - (n : ℝ))))]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hm : ((k : ℝ) + (j : ℝ) - (n : ℝ)) = ((((k : ℤ) + (j : ℤ) - (n : ℤ)) : ℤ) : ℝ) := by
        push_cast
        ring
      rw [hm, horth]
    calc Finset.sum (Finset.range (n + 1)) (fun k => (∫ t in (0 : ℝ)..1, Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * gbPhase (((k : ℝ) + (j : ℝ) - (n : ℝ)) * t))))
        = Finset.sum (Finset.range (n + 1)) (fun k => Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * (if ((k : ℤ) + (j : ℤ) - (n : ℤ)) = 0 then 1 else 0))) := Finset.sum_congr rfl hstep
      _ = ((Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) : ℝ) : ℂ) := hcollapse
  rw [show (∫ t in (0 : ℝ)..1, (Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * gbPhase ((k : ℝ) * t))) ^ 2 * gbPhase (-(n : ℝ) * t)) = (∫ t in (0 : ℝ)..1, Finset.sum (Finset.range (n + 1)) (fun k => Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * gbPhase (((k : ℝ) + (j : ℝ) - (n : ℝ)) * t)))) from intervalIntegral.integral_congr (fun t _ => hpoint t)]
  exact hmain

end PEqualNP.Outside
