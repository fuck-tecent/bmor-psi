import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_389 :
    ∀ n:ℕ, 389∣n^2+1 ↔ n %389=115 ∨ n %389=274 := by
  intro n
  have key : ∀ m, m < 389 → (389 ∣ m^2+1 ↔ m = 115 ∨ m = 274) := by decide +kernel
  have hmod : (n % 389)^2+1 ≡ n^2+1 [MOD 389] := ((Nat.mod_modEq n 389).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 389) (Nat.mod_lt n (by norm_num))
