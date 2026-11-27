import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_241 :
    ∀ n:ℕ, 241∣n^2+1 ↔ n %241=64 ∨ n %241=177 := by
  intro n
  have key : ∀ m, m < 241 → (241 ∣ m^2+1 ↔ m = 64 ∨ m = 177) := by decide +kernel
  have hmod : (n % 241)^2+1 ≡ n^2+1 [MOD 241] := ((Nat.mod_modEq n 241).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 241) (Nat.mod_lt n (by norm_num))
