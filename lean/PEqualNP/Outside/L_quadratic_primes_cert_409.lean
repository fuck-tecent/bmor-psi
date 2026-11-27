import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_409 :
    ∀ n:ℕ, 409∣n^2+1 ↔ n %409=143 ∨ n %409=266 := by
  intro n
  have key : ∀ m, m < 409 → (409 ∣ m^2+1 ↔ m = 143 ∨ m = 266) := by decide +kernel
  have hmod : (n % 409)^2+1 ≡ n^2+1 [MOD 409] := ((Nat.mod_modEq n 409).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 409) (Nat.mod_lt n (by norm_num))
