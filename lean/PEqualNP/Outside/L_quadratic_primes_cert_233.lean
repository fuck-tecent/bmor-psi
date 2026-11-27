import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_233 :
    ∀ n:ℕ, 233∣n^2+1 ↔ n %233=89 ∨ n %233=144 := by
  intro n
  have key : ∀ m, m < 233 → (233 ∣ m^2+1 ↔ m = 89 ∨ m = 144) := by decide +kernel
  have hmod : (n % 233)^2+1 ≡ n^2+1 [MOD 233] := ((Nat.mod_modEq n 233).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 233) (Nat.mod_lt n (by norm_num))
