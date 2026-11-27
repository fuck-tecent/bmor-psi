import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_313 :
    ∀ n:ℕ, 313∣n^2+1 ↔ n %313=25 ∨ n %313=288 := by
  intro n
  have key : ∀ m, m < 313 → (313 ∣ m^2+1 ↔ m = 25 ∨ m = 288) := by decide +kernel
  have hmod : (n % 313)^2+1 ≡ n^2+1 [MOD 313] := ((Nat.mod_modEq n 313).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 313) (Nat.mod_lt n (by norm_num))
