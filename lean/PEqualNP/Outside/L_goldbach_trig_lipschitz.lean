import Mathlib

theorem PEqualNP.Outside.L_goldbach_trig_lipschitz :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); ∀ n w s t, ‖S n w s-S n w t‖ ≤ 2*Real.pi*|s-t| * Finset.sum (Finset.range (n+1)) (fun k => (k:ℝ)*|w k|) := by
  intro E S n w s t
  have chord (a b : ℝ) :
      ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
    have split : (a : ℂ) * Complex.I =
        Complex.I * ((a - b : ℝ) : ℂ) + (b : ℂ) * Complex.I := by
      push_cast
      ring
    rw [split, Complex.exp_add, ← sub_one_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le
  change ‖(∑ k ∈ Finset.range (n+1), (w k : ℂ) * E (k * s)) -
      ∑ k ∈ Finset.range (n+1), (w k : ℂ) * E (k * t)‖ ≤ _
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |w k| * ‖E (k * s) - E (k * t)‖ ≤
        |w k| * |2 * Real.pi * (k * s) - 2 * Real.pi * (k * t)| :=
      mul_le_mul_of_nonneg_left (chord _ _) (abs_nonneg _)
    _ = _ := by
      rw [show 2 * Real.pi * ((k : ℝ) * s) - 2 * Real.pi * ((k : ℝ) * t) =
          (2 * Real.pi * k) * (s-t) by ring, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * k)]
      ring
