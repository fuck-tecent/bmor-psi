import Mathlib

theorem PEqualNP.Outside.L_goldbach_power_error_sublinear :
    ∀ C e : ℝ, 0<e → ∃ N : ℕ, ∀ n : ℕ, N≤n → C*Real.sqrt (n:ℝ)*(Real.log (n:ℝ))^3 ≤ e*(n:ℝ) := by
  intro C e he
  have hsmall : ∀ᶠ x : ℝ in Filter.atTop,
      C * Real.sqrt x * (Real.log x) ^ 3 ≤ e * x := by
    filter_upwards [
      ((isLittleO_log_rpow_rpow_atTop ((3 : ℕ) : ℝ)
        (show 0 < (1 / 2 : ℝ) by norm_num)).const_mul_left (C / e)).eventuallyLE,
      Filter.eventually_ge_atTop (0 : ℝ)] with x hx hx0
    have hbound : (C / e) * (Real.log x) ^ 3 ≤ Real.sqrt x := by
      rw [Real.sqrt_eq_rpow]
      exact (le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 (1 / 2)),
          Real.rpow_natCast] using hx)
    calc
      C * Real.sqrt x * (Real.log x) ^ 3 =
          ((C / e) * (Real.log x) ^ 3) * (e * Real.sqrt x) := by
        field_simp [he.ne']
      _ ≤ Real.sqrt x * (e * Real.sqrt x) :=
        mul_le_mul_of_nonneg_right hbound (mul_nonneg he.le (Real.sqrt_nonneg x))
      _ = e * x := by
        calc
          Real.sqrt x * (e * Real.sqrt x) = e * (Real.sqrt x * Real.sqrt x) := by ring
          _ = e * x := by rw [Real.mul_self_sqrt hx0]
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hsmall
  obtain ⟨N, hN⟩ := exists_nat_ge X
  refine ⟨N, ?_⟩
  intro n hn
  exact hX (n : ℝ) (hN.trans (by exact_mod_cast hn))
