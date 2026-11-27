import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_373 :
    ∀ n:ℕ, 373∣n^2+1 ↔ n %373=104 ∨ n %373=269 := by
  intro n
  have key : ∀ m, m < 373 → (373 ∣ m^2+1 ↔ m = 104 ∨ m = 269) := by decide +kernel
  have hmod : (n % 373)^2+1 ≡ n^2+1 [MOD 373] := ((Nat.mod_modEq n 373).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 373) (Nat.mod_lt n (by norm_num))
