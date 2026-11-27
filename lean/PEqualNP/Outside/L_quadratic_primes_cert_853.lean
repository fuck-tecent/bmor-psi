import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_853 :
    ∀ n:ℕ, 853∣n^2+1 ↔ n %853=333 ∨ n %853=520 := by
  intro n
  have key : ∀ m, m < 853 → (853 ∣ m^2+1 ↔ m = 333 ∨ m = 520) := by decide +kernel
  have hmod : (n % 853)^2+1 ≡ n^2+1 [MOD 853] := ((Nat.mod_modEq n 853).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 853) (Nat.mod_lt n (by norm_num))
