import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_317 :
    ∀ n:ℕ, 317∣n^2+1 ↔ n %317=114 ∨ n %317=203 := by
  intro n
  have key : ∀ m, m < 317 → (317 ∣ m^2+1 ↔ m = 114 ∨ m = 203) := by decide +kernel
  have hmod : (n % 317)^2+1 ≡ n^2+1 [MOD 317] := ((Nat.mod_modEq n 317).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 317) (Nat.mod_lt n (by norm_num))
