import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_divisor_coprime :
    ∀ (n p : ℕ), p ∣ n ^ 2 + 1 → p ∣ n → p = 1 := by
  intro n p h1 h2
  have h2' : p ∣ n ^ 2 := by simpa [pow_two] using dvd_mul_of_dvd_left h2 n
  have h3 : p ∣ (n ^ 2 + 1) - n ^ 2 := Nat.dvd_sub h1 h2'
  have h4 : (n ^ 2 + 1) - n ^ 2 = 1 := by omega
  rw [h4] at h3
  exact Nat.dvd_one.mp h3
