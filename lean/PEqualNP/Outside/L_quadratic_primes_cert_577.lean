import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_577 :
    ∀ n:ℕ, 577∣n^2+1 ↔ n %577=24 ∨ n %577=553 := by
  intro n
  have key : ∀ m, m < 577 → (577 ∣ m^2+1 ↔ m = 24 ∨ m = 553) := by decide +kernel
  have hmod : (n % 577)^2+1 ≡ n^2+1 [MOD 577] := ((Nat.mod_modEq n 577).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 577) (Nat.mod_lt n (by norm_num))
