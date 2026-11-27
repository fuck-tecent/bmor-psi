import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_977 :
    ∀ n:ℕ, 977∣n^2+1 ↔ n %977=252 ∨ n %977=725 := by
  intro n
  have key : ∀ m, m < 977 → (977 ∣ m^2+1 ↔ m = 252 ∨ m = 725) := by decide +kernel
  have hmod : (n % 977)^2+1 ≡ n^2+1 [MOD 977] := ((Nat.mod_modEq n 977).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 977) (Nat.mod_lt n (by norm_num))
