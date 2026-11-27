import Mathlib

theorem PEqualNP.Outside.L_goldbach_even_shift_phase_filter :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ (H : ℕ) (t : ℝ), 0<H → Real.sin (2*Real.pi*t) ≠ 0 → ‖(∑ j ∈ Finset.range H, E (-2*(j:ℝ)*t))/(H:ℂ)‖ ≤ min 1 (1/((H:ℝ)*|Real.sin (2*Real.pi*t)|)) := by
  intro _ E H t hH hsin
  let z := Complex.exp (Complex.I * ((-4*Real.pi*t : ℝ):ℂ))
  have hz : ‖z‖ = 1 := by
    simpa [z,mul_comm] using Complex.norm_exp_ofReal_mul_I (-4*Real.pi*t)
  have phase (j : ℕ) : E (-2*(j:ℝ)*t) = z^j := by
    dsimp only [E,z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have chord : ‖z-1‖ = 2*|Real.sin (2*Real.pi*t)| := by
    rw [show z = Complex.exp (Complex.I*((-4*Real.pi*t:ℝ):ℂ)) from rfl,
      Complex.norm_exp_I_mul_ofReal_sub_one]
    have arg : (-4*Real.pi*t)/2 = -(2*Real.pi*t) := by ring
    rw [arg,Real.sin_neg,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),abs_neg]
  let G := ∑ j ∈ Finset.range H, z^j
  have hG : ‖G‖ ≤ H := by
    calc
      _ ≤ ∑ j ∈ Finset.range H, ‖z^j‖ := norm_sum_le _ _
      _ = _ := by simp [norm_pow,hz]
  have geom : ‖G‖ * (2*|Real.sin (2*Real.pi*t)|) ≤ 2 := by
    rw [← chord, ← norm_mul, show G*(z-1)=z^H-1 from geom_sum_mul z H]
    calc
      _ ≤ ‖z^H‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = _ := by simp [norm_pow,hz]; norm_num
  have hpos : (0:ℝ) < H := by exact_mod_cast hH
  have hsinpos : 0 < |Real.sin (2*Real.pi*t)| := abs_pos.mpr hsin
  simp_rw [phase]
  change ‖G/(H:ℂ)‖ ≤ min 1 (1/((H:ℝ)*|Real.sin (2*Real.pi*t)|))
  rw [norm_div,Complex.norm_natCast]
  apply le_min
  · exact (div_le_one hpos).2 hG
  · apply (div_le_div_iff₀ hpos (mul_pos hpos hsinpos)).2
    nlinarith
