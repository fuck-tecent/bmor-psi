import Mathlib

/-!
新路线 · 特征与分母扩窗 · CW-8005 · 为截断显式公式的单个零点给出双端点增量界

所用的恒等式与估计：对正实数 x 与复指数 ρ，有 x ^ ρ = exp((log x) · ρ)；沿实轴从 log u 到 log v
对 exp(t · ρ) 用中值不等式（导数的模长不超过 exp(Re ρ · log v) · ‖ρ‖），得对数窗界
‖v ^ ρ − u ^ ρ‖ ≤ v ^ Re ρ · ‖ρ‖ · log(v / u)；再用三角不等式与 u ^ Re ρ ≤ v ^ Re ρ 得
端点界 ‖v ^ ρ − u ^ ρ‖ ≤ 2 · v ^ Re ρ。两界各除以 ‖ρ‖ 后取较小者。

量词：对全体实数 u、v 与复数 ρ 成立；假设 1 ≤ u ≤ v、Re ρ ≥ 0、ρ ≠ 0。
-/

theorem PEqualNP.Outside.L_goldbach_primitive_zero_window_increment :
    ∀ (u v : ℝ) (ρ : ℂ), 1 ≤ u → u ≤ v → 0 ≤ ρ.re → ρ ≠ 0 → ‖((v:ℂ)^ρ-(u:ℂ)^ρ)/ρ‖ ≤ (v:ℝ)^ρ.re * min (Real.log (v/u)) (2/‖ρ‖) := by
  intro u v ρ hu hv hre hρ
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hv0 : 0 < v := lt_of_lt_of_le hu0 hv
  -- 正底数的复幂写成指数：此后两端点之差就是 exp(t · ρ) 在 log u、log v 两点取值之差
  have hcpow : ∀ x : ℝ, 0 < x → (x : ℂ) ^ ρ = Complex.exp (((Real.log x : ℝ) : ℂ) * ρ) := by
    intro x hx
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.ofReal_log hx.le,
      mul_comm]
  -- 正实数的复幂的模长只看指数的实部：端点界里用它
  have hnorm : ∀ (x : ℝ) (w : ℂ), 0 < x → ‖(x : ℂ) ^ w‖ = x ^ w.re := by
    intro x w hx
    rw [Complex.norm_cpow_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.norm_real,
      Complex.arg_ofReal_of_nonneg hx.le]
    simp only [Real.norm_eq_abs, abs_of_pos hx, zero_mul, Real.exp_zero, div_one]
  -- 沿实轴求导：exp(t · ρ) 对 t 的导数是 exp(t · ρ) · ρ
  have hderiv : ∀ t : ℝ, HasDerivAt (fun x : ℝ => Complex.exp ((x : ℂ) * ρ))
      (Complex.exp ((t : ℂ) * ρ) * ρ) t := by
    intro t
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) * ρ) ρ t := (hasDerivAt_mul_const ρ).comp_ofReal
    exact h1.cexp
  -- Re ρ ≥ 0 时导数的模长在窗内随 t 递增，右端点处最大，所以常数可以整窗通用
  have hdbound : ∀ t ∈ Set.Ico (Real.log u) (Real.log v),
      ‖Complex.exp ((t : ℂ) * ρ) * ρ‖ ≤ Real.exp (Real.log v * ρ.re) * ‖ρ‖ := by
    intro t ht
    rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.2.le hre)) (norm_nonneg _)
  -- 对数窗界：中值不等式比较的是右端点与左端点，右端点取 log v
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f' := fun t => Complex.exp ((t : ℂ) * ρ) * ρ) (C := Real.exp (Real.log v * ρ.re) * ‖ρ‖)
    (a := Real.log u) (b := Real.log v)
    (fun t _ => (hderiv t).hasDerivWithinAt) hdbound (Real.log v)
    ⟨Real.log_le_log hu0 hv, le_refl _⟩
  rw [hcpow v hv0, hcpow u hu0]
  rw [Real.rpow_def_of_pos hv0 ρ.re, Real.log_div hv0.ne' hu0.ne']
  -- 对数窗界除以 ‖ρ‖：对应 min 的第一支
  have hw : ‖(Complex.exp (((Real.log v : ℝ) : ℂ) * ρ) - Complex.exp (((Real.log u : ℝ) : ℂ) * ρ)) / ρ‖
      ≤ Real.exp (Real.log v * ρ.re) * (Real.log v - Real.log u) := by
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hρ)]
    calc ‖Complex.exp (((Real.log v : ℝ) : ℂ) * ρ) - Complex.exp (((Real.log u : ℝ) : ℂ) * ρ)‖
        ≤ Real.exp (Real.log v * ρ.re) * ‖ρ‖ * (Real.log v - Real.log u) := hmvt
      _ ≤ (Real.exp (Real.log v * ρ.re) * (Real.log v - Real.log u)) * ‖ρ‖ := le_of_eq (by ring)
  -- 端点界：窗很宽时对数窗界变差，改用两个端点各自的模长；对应 min 的第二支
  have he : ‖(Complex.exp (((Real.log v : ℝ) : ℂ) * ρ) - Complex.exp (((Real.log u : ℝ) : ℂ) * ρ)) / ρ‖
      ≤ Real.exp (Real.log v * ρ.re) * (2 / ‖ρ‖) := by
    calc ‖(Complex.exp (((Real.log v : ℝ) : ℂ) * ρ) - Complex.exp (((Real.log u : ℝ) : ℂ) * ρ)) / ρ‖
        ≤ (‖Complex.exp (((Real.log v : ℝ) : ℂ) * ρ)‖ + ‖Complex.exp (((Real.log u : ℝ) : ℂ) * ρ)‖) / ‖ρ‖ := by
          rw [norm_div, div_le_div_iff_of_pos_right (norm_pos_iff.mpr hρ)]
          exact norm_sub_le _ _
      _ = ((v : ℝ) ^ ρ.re + (u : ℝ) ^ ρ.re) / ‖ρ‖ := by
          rw [← hcpow v hv0, ← hcpow u hu0, hnorm v ρ hv0, hnorm u ρ hu0]
      _ ≤ ((v : ℝ) ^ ρ.re + (v : ℝ) ^ ρ.re) / ‖ρ‖ :=
        div_le_div_of_nonneg_right (add_le_add (le_refl _) (Real.rpow_le_rpow hu0.le hv hre)) (norm_nonneg _)
      _ = Real.exp (Real.log v * ρ.re) * (2 / ‖ρ‖) := by
          rw [Real.rpow_def_of_pos hv0 ρ.re]
          ring
  rcases le_total (Real.log v - Real.log u) (2 / ‖ρ‖) with h | h
  · rw [min_eq_left h]
    exact hw
  · rw [min_eq_right h]
    exact he
