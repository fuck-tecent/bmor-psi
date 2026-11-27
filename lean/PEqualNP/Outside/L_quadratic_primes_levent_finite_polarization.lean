import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_finite_polarization :
    ∀ (S : Finset ℕ) (u v : ℕ → ℂ),
      (∑ k ∈ S, ‖u k + v k‖ ^ 2) - (∑ k ∈ S, ‖u k - v k‖ ^ 2) =
        4 * ∑ k ∈ S, (u k * star (v k)).re := by
  intro S u v
  classical
  have hinner (a b : ℂ) : RCLike.re (inner ℂ a b) = (a * star b).re := by
    calc
      RCLike.re (inner ℂ a b) = RCLike.re (inner ℂ b a) := inner_re_symm a b
      _ = (a * star b).re := by
        rw [RCLike.inner_apply]
        rfl
  have hpoint (a b : ℂ) :
      ‖a + b‖ ^ 2 - ‖a - b‖ ^ 2 = 4 * (a * star b).re := by
    rw [norm_add_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ), hinner]
    ring
  rw [← Finset.sum_sub_distrib]
  simp_rw [hpoint]
  rw [← Finset.mul_sum]