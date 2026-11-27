import Mathlib

theorem PEqualNP.Outside.L_goldbach_strip_geometry_zeta_floor :
    RiemannHypothesis → ∀ s : ℂ, 0<s.re → s.re<1 → riemannZeta s=0 → 1/2≤‖s‖ := by
  intro hRH s h1 h2 hz
  have hre : s.re = 1/2 := by
    refine hRH s hz ?_ ?_
    · rintro ⟨n, hn⟩
      have hz2 : s.re = -2 * ((n:ℝ) + 1) := by
        rw [hn]
        push_cast
        simp
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      nlinarith
    · intro h
      rw [h] at h2
      norm_num at h2
  calc (1/2:ℝ) = |s.re| := by rw [hre]; norm_num
    _ ≤ ‖s‖ := Complex.abs_re_le_norm s
