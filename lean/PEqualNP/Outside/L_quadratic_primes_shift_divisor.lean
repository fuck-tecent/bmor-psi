import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_shift_divisor :
    ∀ n h d:ℕ,d∣n^2+1 → d∣(n+h)^2+1 → d∣h*(2*n+h) := by
  intro n h d h1 h2
  have h1z : (d:ℤ) ∣ (n:ℤ)^2 + 1 := by exact_mod_cast h1
  have h2z : (d:ℤ) ∣ ((n:ℤ) + (h:ℤ))^2 + 1 := by exact_mod_cast h2
  have h3 : (d:ℤ) ∣ (h:ℤ) * (2*(n:ℤ) + (h:ℤ)) := by
    have hsplit : ((n:ℤ) + (h:ℤ))^2 + 1 - ((n:ℤ)^2 + 1) = (h:ℤ) * (2*(n:ℤ) + (h:ℤ)) := by ring
    rw [← hsplit]
    exact dvd_sub h2z h1z
  exact_mod_cast h3
