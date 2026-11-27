import Mathlib

theorem PEqualNP.Outside.L_goldbach_signed_phase :
    ∀ (u S M : ℂ) (E : ℝ), ‖u‖=1 → ‖S-M‖≤E → (u*M^2).re-E*(2*‖M‖+E)≤(u*S^2).re := by
  intro u S M E hu h
  have hE : 0 ≤ E := le_trans (norm_nonneg _) h
  have hfac : S ^ 2 - M ^ 2 = (S - M) * (S + M) := by ring
  have hsum : ‖S + M‖ ≤ E + 2 * ‖M‖ := by
    have h1 : S + M = (S - M) + M + M := by ring
    calc ‖S + M‖ = ‖(S - M) + M + M‖ := by rw [h1]
      _ ≤ ‖(S - M) + M‖ + ‖M‖ := norm_add_le _ _
      _ ≤ (‖S - M‖ + ‖M‖) + ‖M‖ := by linarith [norm_add_le (S - M) M]
      _ ≤ E + 2 * ‖M‖ := by linarith
  have hsq : ‖S ^ 2 - M ^ 2‖ ≤ E * (2 * ‖M‖ + E) := by
    calc ‖S ^ 2 - M ^ 2‖ = ‖S - M‖ * ‖S + M‖ := by rw [hfac, norm_mul]
      _ ≤ E * (E + 2 * ‖M‖) := mul_le_mul h hsum (norm_nonneg _) hE
      _ = E * (2 * ‖M‖ + E) := by ring
  have hnorm : ‖u * (S ^ 2 - M ^ 2)‖ ≤ E * (2 * ‖M‖ + E) := by
    rw [norm_mul, hu, one_mul]
    exact hsq
  have hlow : -(E * (2 * ‖M‖ + E)) ≤ (u * (S ^ 2 - M ^ 2)).re := by
    have h1 : -((u * (S ^ 2 - M ^ 2)).re) ≤ ‖u * (S ^ 2 - M ^ 2)‖ := by
      have h2 := Complex.re_le_norm (-(u * (S ^ 2 - M ^ 2)))
      simpa using h2
    linarith
  have hsplit : (u * S ^ 2).re = (u * M ^ 2).re + (u * (S ^ 2 - M ^ 2)).re := by
    have h2 : u * S ^ 2 = u * M ^ 2 + u * (S ^ 2 - M ^ 2) := by ring
    rw [h2, Complex.add_re]
  linarith
