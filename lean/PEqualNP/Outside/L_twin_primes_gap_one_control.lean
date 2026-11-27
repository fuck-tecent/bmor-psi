import Mathlib

theorem PEqualNP.Outside.L_twin_primes_gap_one_control :
    ∀ n : ℕ, ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+1) ≠ 0 → (∃ k : ℕ, n = 2^k) ∨ (∃ k : ℕ, n+1 = 2^k) := by
  intro n hn
  have h1 : ArithmeticFunction.vonMangoldt n ≠ 0 := left_ne_zero_of_mul hn
  have h2 : ArithmeticFunction.vonMangoldt (n+1) ≠ 0 := right_ne_zero_of_mul hn
  rw [ArithmeticFunction.vonMangoldt_ne_zero_iff, isPrimePow_nat_iff] at h1 h2
  obtain ⟨p, k, hp, hk, rfl⟩ := h1
  obtain ⟨q, l, hq, hl, hql⟩ := h2
  rcases Nat.even_or_odd (p ^ k) with he | ho
  · left
    have h3 : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow he.two_dvd
    have h4 : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h3
    exact ⟨k, by rw [← h4]⟩
  · right
    have h5 : Even (q ^ l) := by rw [hql]; exact Odd.add_one ho
    have h3 : 2 ∣ q := Nat.prime_two.dvd_of_dvd_pow h5.two_dvd
    have h4 : 2 = q := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h3
    exact ⟨l, by rw [← hql, ← h4]⟩
