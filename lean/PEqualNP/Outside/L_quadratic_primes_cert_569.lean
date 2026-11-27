import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_569 :
    ∀ n:ℕ, 569∣n^2+1 ↔ n %569=86 ∨ n %569=483 := by
  intro n
  have key : ∀ m, m < 569 → (569 ∣ m^2+1 ↔ m = 86 ∨ m = 483) := by decide +kernel
  have hmod : (n % 569)^2+1 ≡ n^2+1 [MOD 569] := ((Nat.mod_modEq n 569).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 569) (Nat.mod_lt n (by norm_num))
