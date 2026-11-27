import Mathlib

theorem PEqualNP.Outside.L_goldbach_trig_sup_bound :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); ∀ n w t, ‖S n w t‖ ≤ Finset.sum (Finset.range (n+1)) (fun k => |w k|) := by
  dsimp only
  intro n w t
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro k _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one]
