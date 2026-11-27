import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_193 :
    ∀ n:ℕ, 193∣n^2+1 ↔ n %193=81 ∨ n %193=112 := by
  intro n
  have key : ∀ m, m < 193 → (193 ∣ m^2+1 ↔ m = 81 ∨ m = 112) := by decide +kernel
  have hmod : (n % 193)^2+1 ≡ n^2+1 [MOD 193] := ((Nat.mod_modEq n 193).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 193) (Nat.mod_lt n (by norm_num))
