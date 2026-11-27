import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_explicit_formula_truncation :
    ∀ (q : ℕ) (u : ℝ), 1≤q → 4≤u → let T := Real.sqrt u; 2≤T ∧ T≤u ∧ u*Real.log ((q : ℝ)*u*T)^2/T ≤ 4*Real.sqrt u*Real.log ((q : ℝ)*u)^2 := by
  intro q u hq hu
  dsimp only
  have hu0 : (0:ℝ) < u := by linarith
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hsq : (Real.sqrt u)^2 = u := Real.sq_sqrt hu0.le
  have hTnn : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  have hTpos : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hqu0 : (0:ℝ) < (q:ℝ)*u := by nlinarith
  have hqu1 : (1:ℝ) ≤ (q:ℝ)*u := by nlinarith
  have hqu_ge : u ≤ (q:ℝ)*u := by nlinarith
  have hlogq : 0 ≤ Real.log ((q:ℝ)*u) := Real.log_nonneg hqu1
  have hsplit : Real.log ((q:ℝ)*u*Real.sqrt u) = Real.log ((q:ℝ)*u) + Real.log u / 2 := by
    rw [Real.log_mul (ne_of_gt hqu0) (ne_of_gt hTpos), Real.log_sqrt hu0.le]
  have hle : Real.log u ≤ 2 * Real.log ((q:ℝ)*u) := by
    have h1 : u ≤ ((q:ℝ)*u)^2 := by
      calc u = u * 1 := by ring
        _ ≤ ((q:ℝ)*u) * ((q:ℝ)*u) :=
            mul_le_mul hqu_ge hqu1 (by norm_num) hqu0.le
        _ = ((q:ℝ)*u)^2 := by ring
    calc Real.log u ≤ Real.log (((q:ℝ)*u)^2) := Real.log_le_log hu0 h1
      _ = 2 * Real.log ((q:ℝ)*u) := by rw [Real.log_pow]; norm_num
  have hmain : Real.log ((q:ℝ)*u*Real.sqrt u)^2 ≤ 4 * Real.log ((q:ℝ)*u)^2 := by
    rw [hsplit]
    have hL1nn : 0 ≤ Real.log ((q:ℝ)*u) + Real.log u / 2 := by
      have hx : (1:ℝ) ≤ (q:ℝ)*u*Real.sqrt u := by nlinarith
      linarith [Real.log_nonneg hx]
    have h2 : Real.log ((q:ℝ)*u) + Real.log u / 2 ≤ 2 * Real.log ((q:ℝ)*u) := by linarith
    have h2' : (Real.log ((q:ℝ)*u) + Real.log u / 2)^2 ≤ (2 * Real.log ((q:ℝ)*u))^2 :=
      pow_le_pow_left₀ hL1nn h2 2
    nlinarith [h2']
  have hTA : u * Real.log ((q:ℝ)*u*Real.sqrt u)^2 / Real.sqrt u
      = Real.sqrt u * Real.log ((q:ℝ)*u*Real.sqrt u)^2 := by
    rw [div_eq_iff hTpos.ne']
    calc u * Real.log ((q:ℝ)*u*Real.sqrt u)^2
        = (Real.sqrt u)^2 * Real.log ((q:ℝ)*u*Real.sqrt u)^2 := by rw [Real.sq_sqrt hu0.le]
      _ = Real.sqrt u * Real.log ((q:ℝ)*u*Real.sqrt u)^2 * Real.sqrt u := by ring
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  calc u * Real.log ((q:ℝ)*u*Real.sqrt u)^2 / Real.sqrt u
      = Real.sqrt u * Real.log ((q:ℝ)*u*Real.sqrt u)^2 := hTA
    _ ≤ Real.sqrt u * (4 * Real.log ((q:ℝ)*u)^2) :=
        mul_le_mul_of_nonneg_left hmain hTnn
    _ = 4 * Real.sqrt u * Real.log ((q:ℝ)*u)^2 := by ring
