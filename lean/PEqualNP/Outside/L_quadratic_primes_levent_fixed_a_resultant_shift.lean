import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_fixed_a_resultant_shift :
    ∀ a n h d : ℤ, d ∣ n^2+a → d ∣ (n+h)^2+a → d ∣ h^2*(h^2+4*a) := by
  intro a n h d h1 h2
  have hBA : d ∣ ((n+h)^2+a) - (n^2+a) := dvd_sub h2 h1
  have key : h^2*(h^2+4*a)
      = 4*h^2*(n^2+a) - (((n+h)^2+a) - (n^2+a))^2
        + 2*h^2*(((n+h)^2+a) - (n^2+a)) := by ring
  rw [key]
  apply dvd_add
  · apply dvd_sub
    · exact dvd_mul_of_dvd_right h1 _
    · rw [pow_two]; exact dvd_mul_of_dvd_left hBA _
  · exact dvd_mul_of_dvd_right hBA _
