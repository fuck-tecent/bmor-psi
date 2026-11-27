import Mathlib
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_quadratic_primes_levent_dirichlet_zero_line :
    (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (Z : Finset ℂ) (m : ℂ → ℕ) (u : ℝ), 1 ≤ u → (∀ s ∈ Z, 0 < s.re ∧ s.re < 1 ∧ χ.LFunction s = 0) → ‖∑ s ∈ Z, (m s : ℂ) * (u : ℂ)^s / s‖ ≤ Real.sqrt u * ∑ s ∈ Z, (m s : ℝ) / ‖s‖ := by
  intro H q _ χ Z m u h1 hZ
  have hu : (0:ℝ) < u := by linarith
  have key : ∀ s ∈ Z, ‖(m s : ℂ) * (u : ℂ)^s / s‖ = (m s : ℝ) / ‖s‖ * Real.sqrt u := by
    intro s hs
    obtain ⟨h0, h1', h2'⟩ := hZ s hs
    have hre : s.re = 1/2 := H q χ s h0 h1' h2'
    rw [Complex.norm_div, Complex.norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, hre,
      Real.sqrt_eq_rpow, Complex.norm_natCast]
    ring
  calc ‖∑ s ∈ Z, (m s : ℂ) * (u : ℂ)^s / s‖ ≤ ∑ s ∈ Z, ‖(m s : ℂ) * (u : ℂ)^s / s‖ := norm_sum_le _ _
    _ = ∑ s ∈ Z, (m s : ℝ) / ‖s‖ * Real.sqrt u := Finset.sum_congr rfl key
    _ = (∑ s ∈ Z, (m s : ℝ) / ‖s‖) * Real.sqrt u := by rw [Finset.sum_mul]
    _ = Real.sqrt u * ∑ s ∈ Z, (m s : ℝ) / ‖s‖ := by ring
