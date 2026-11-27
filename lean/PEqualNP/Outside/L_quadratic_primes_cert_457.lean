import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_457 :
    ∀ n:ℕ, 457∣n^2+1 ↔ n %457=109 ∨ n %457=348 := by
  intro n
  have key : ∀ m, m < 457 → (457 ∣ m^2+1 ↔ m = 109 ∨ m = 348) := by decide +kernel
  have hmod : (n % 457)^2+1 ≡ n^2+1 [MOD 457] := ((Nat.mod_modEq n 457).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 457) (Nat.mod_lt n (by norm_num))
