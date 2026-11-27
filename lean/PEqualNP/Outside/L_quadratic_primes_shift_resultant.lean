import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_shift_resultant :
    ∀ n h d:ℤ,d∣n^2+1 → d∣(n+h)^2+1 → d∣h^2*(h^2+4) := by
  intro n h d h1 h2
  have hC : d ∣ 2*n*h + h^2 := by
    have hs : (n+h)^2+1 - (n^2+1) = 2*n*h + h^2 := by ring
    rw [← hs]
    exact dvd_sub h2 h1
  have hkey : h^2*(h^2+4) = (2*n*h+h^2)*(2*h^2-(2*n*h+h^2)) + 4*h^2*(n^2+1) := by ring
  rw [hkey]
  refine dvd_add ?_ ?_
  · exact dvd_mul_of_dvd_left hC _
  · exact dvd_mul_of_dvd_right h1 _
