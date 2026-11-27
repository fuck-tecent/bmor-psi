import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_1409 :
    ∀ n : ℕ, 1409 ∣ n ^ 2 + 1 ↔ n % 1409 = 452 ∨ n % 1409 = 957 := by
  intro n
  have hident : (n + 452) * (n + 957) = (n ^ 2 + 1) + 1409 * (n + 307) := by ring
  have hprime : Nat.Prime 1409 := by norm_num
  constructor
  · intro hdvd
    have hprod : 1409 ∣ (n + 452) * (n + 957) := by
      rw [hident]
      exact dvd_add hdvd (dvd_mul_right 1409 (n + 307))
    rcases hprime.dvd_mul.mp hprod with ⟨k, hk⟩ | ⟨k, hk⟩
    · right
      have hn : n = 957 + 1409 * (k - 1) := by omega
      rw [hn, Nat.add_mul_mod_self_left]
    · left
      have hn : n = 452 + 1409 * (k - 1) := by omega
      rw [hn, Nat.add_mul_mod_self_left]
  · intro hmod
    have hdiv := Nat.div_add_mod n 1409
    have hprod : 1409 ∣ (n + 452) * (n + 957) := by
      rcases hmod with h | h
      · rw [h] at hdiv
        exact dvd_mul_of_dvd_right ⟨n / 1409 + 1, by linarith⟩ (n + 452)
      · rw [h] at hdiv
        exact dvd_mul_of_dvd_left ⟨n / 1409 + 1, by linarith⟩ (n + 957)
    rcases hprod with ⟨m, hm⟩
    have hlin : (n ^ 2 + 1) + 1409 * (n + 307) = 1409 * m := hident.symm.trans hm
    have hle : n + 307 ≤ m := by nlinarith
    refine ⟨m - (n + 307), ?_⟩
    zify [hle] at hlin ⊢
    linarith
