import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1493 :
    ∀ n:ℕ, 1493∣n^2+1 ↔ n %1493=432 ∨ n %1493=1061 := by
  intro n
  have key : ∀ m, m < 1493 → (1493 ∣ m^2+1 ↔ m = 432 ∨ m = 1061) := by decide +kernel
  have hmod : (n % 1493)^2+1 ≡ n^2+1 [MOD 1493] := ((Nat.mod_modEq n 1493).pow 2).add_right 1
  rw [← hmod.dvd_iff dvd_rfl]
  exact key (n % 1493) (Nat.mod_lt n (by norm_num))
