import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_433 :
    ∀ n:ℕ, 433∣n^2+1 ↔ n %433=179 ∨ n %433=254 := by
  intro n
  have key : ∀ m, m < 433 → (433 ∣ m^2+1 ↔ m = 179 ∨ m = 254) := by decide +kernel
  have hmod : (n % 433)^2+1 ≡ n^2+1 [MOD 433] := ((Nat.mod_modEq n 433).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 433) (Nat.mod_lt n (by norm_num))
