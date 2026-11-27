import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_dyadic_log_absorption :
    let budget := fun x : ℕ => (x : ℝ) * Real.log (x : ℝ); ∀ ε : ℝ, 0<ε → ∃ X : ℕ, ∀ x ≥ X, Real.log (((2*x)^2+1 : ℕ) : ℝ) ≤ ε*budget x := by
  dsimp only
  intro ε hε
  have hlog : Filter.Tendsto (fun x : ℕ => Real.log (x:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ x : ℕ in Filter.atTop, 6 ≤ ε * Real.log (x:ℝ) :=
    (hlog.const_mul_atTop hε).eventually_ge_atTop 6
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max X 1, ?_⟩
  intro x hx
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have h6 : 6 ≤ ε * Real.log (x:ℝ) := hX x hxX
  have hxpos : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx1
  have hx1R : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx1
  have hN : (((2*x)^2+1 : ℕ) : ℝ) ≤ (3*(x:ℝ))^2 := by
    push_cast
    nlinarith
  have hpos : (0:ℝ) < (((2*x)^2+1 : ℕ) : ℝ) := by positivity
  have hstep1 : Real.log (((2*x)^2+1 : ℕ) : ℝ) ≤ Real.log ((3*(x:ℝ))^2) :=
    Real.log_le_log hpos hN
  have hstep2 : Real.log ((3*(x:ℝ))^2) = 2 * Real.log (3*(x:ℝ)) := by
    rw [Real.log_pow]
    norm_num
  have hstep3 : Real.log (3*(x:ℝ)) ≤ 3*(x:ℝ) := Real.log_le_self (by positivity)
  have hfin : 6*(x:ℝ) ≤ ε*((x:ℝ)*Real.log (x:ℝ)) := by nlinarith
  linarith
