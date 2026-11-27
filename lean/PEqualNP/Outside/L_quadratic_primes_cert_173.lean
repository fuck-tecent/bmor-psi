import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_173 :
    ∀ n:ℕ, 173∣n^2+1 ↔ n %173=80 ∨ n %173=93 := by
  intro n
  have key : ∀ m, m < 173 → (173 ∣ m^2+1 ↔ m = 80 ∨ m = 93) := by decide +kernel
  have hmod : (n % 173)^2+1 ≡ n^2+1 [MOD 173] := ((Nat.mod_modEq n 173).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 173) (Nat.mod_lt n (by norm_num))
