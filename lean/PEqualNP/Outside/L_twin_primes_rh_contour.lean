import Mathlib
theorem PEqualNP.Outside.L_twin_primes_rh_contour : RiemannHypothesis → ∀ s : ℂ, 9/16 ≤ s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  intro rh s hs hs1 hz
  have htriv : ¬ ∃ n : ℕ, s = -2 * ((n:ℂ)+1) := by
    rintro ⟨n, hn⟩
    have hr := congrArg Complex.re hn
    simp only [Complex.mul_re, Complex.neg_re, Complex.natCast_re, Complex.one_re, Complex.add_re, Complex.natCast_im, Complex.one_im, Complex.add_im] at hr
    norm_num at hr
    have hnon : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hsne : s ≠ 1 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  have hhalf := rh s hz htriv hsne
  linarith


