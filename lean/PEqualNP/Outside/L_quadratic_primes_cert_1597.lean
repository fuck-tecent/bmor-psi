import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1597 :
    ∀ n:ℕ, 1597∣n^2+1 ↔ n %1597=610 ∨ n %1597=987 := by
  intro n
  have key : ∀ m, m < 1597 → (1597 ∣ m^2+1 ↔ m = 610 ∨ m = 987) := by decide +kernel
  have hmod : (n % 1597)^2+1 ≡ n^2+1 [MOD 1597] := ((Nat.mod_modEq n 1597).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 1597) (Nat.mod_lt n (by norm_num))
