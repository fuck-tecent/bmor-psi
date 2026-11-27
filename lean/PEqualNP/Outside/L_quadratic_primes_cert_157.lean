import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_157 :
    ∀ n:ℕ, 157∣n^2+1 ↔ n %157=28 ∨ n %157=129 := by
  intro n
  have key : ∀ m, m < 157 → (157 ∣ m^2+1 ↔ m = 28 ∨ m = 129) := by decide +kernel
  have hmod : (n % 157)^2+1 ≡ n^2+1 [MOD 157] := ((Nat.mod_modEq n 157).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 157) (Nat.mod_lt n (by norm_num))
