import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_rh_zero_line :
    RiemannHypothesis → ∀ (ρ : ℂ) (u : ℝ), 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 → 1 ≤ u → ‖(u : ℂ) ^ ρ / ρ‖ = Real.sqrt u / ‖ρ‖ := by
  intro H ρ u h1 h2 h3 h4
  have hnotneg : ¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hcast : ((n : ℂ) + 1) = ((n : ℝ) + 1 : ℂ) := by push_cast; ring
    have hre : ρ.re = -2 * ((n : ℝ) + 1) := by
      rw [hn, hcast]
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hne1 : ρ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at h2
    exact absurd h2 (lt_irrefl 1)
  have hre : ρ.re = 1 / 2 := H ρ h3 hnotneg hne1
  rw [Complex.norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < u), hre, Real.sqrt_eq_rpow]
