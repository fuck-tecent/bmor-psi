import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_dyadic_witness_transfer :
    (∀ X : ℕ, ∃ x n p : ℕ, X < x ∧ x ≤ n ∧ n ≤ 2 * x ∧ Nat.Prime p ∧ p ∣ n ^ 2 + 1 ∧ x ^ 13231 < p ^ 10000) → ∀ B : ℕ, ∃ n p : ℕ, B < n ∧ Nat.Prime p ∧ p ∣ n ^ 2 + 1 ∧ n ^ 1323 < p ^ 1000 := by
  intro H B
  obtain ⟨x, n, p, hXx, hxn, hnx, hp, hdvd, hpow⟩ := H (2 ^ 13230 * (B + 1))
  have hXbig : 2 ^ 13230 ≤ 2 ^ 13230 * (B + 1) :=
    Nat.le_mul_of_pos_right (2 ^ 13230) (by omega)
  have hBx : B < 2 ^ 13230 * (B + 1) := by
    have h1 : B + 1 ≤ 2 ^ 13230 * (B + 1) :=
      Nat.le_mul_of_pos_left (B + 1) (by positivity)
    omega
  have h2x : 2 ^ 13230 < x := lt_of_le_of_lt hXbig hXx
  have hxpos : 0 < x := lt_trans (by positivity) h2x
  refine ⟨n, p, ?_, hp, hdvd, ?_⟩
  · omega
  · have hx1000 : 2 ^ 13230000 < x ^ 1000 := by
      have h := Nat.pow_lt_pow_left h2x (by norm_num : (1000 : ℕ) ≠ 0)
      calc 2 ^ 13230000 = (2 ^ 13230) ^ 1000 := by rw [← Nat.pow_mul]
        _ < x ^ 1000 := h
    have hstep1 : n ^ 13230000 ≤ 2 ^ 13230000 * x ^ 13230000 := by
      calc n ^ 13230000 ≤ (2 * x) ^ 13230000 := Nat.pow_le_pow_left hnx 13230000
        _ = 2 ^ 13230000 * x ^ 13230000 := Nat.mul_pow 2 x 13230000
    have hstep2 : 2 ^ 13230000 * x ^ 13230000 < x ^ 13231000 := by
      have hxpos' : 0 < x ^ 13230000 := pow_pos hxpos 13230000
      calc 2 ^ 13230000 * x ^ 13230000 < x ^ 1000 * x ^ 13230000 :=
            Nat.mul_lt_mul_of_pos_right hx1000 hxpos'
        _ = x ^ 13231000 := by rw [← pow_add]
    have hstep3 : x ^ 13231000 < p ^ 10000000 := by
      have h := Nat.pow_lt_pow_left hpow (by norm_num : (1000 : ℕ) ≠ 0)
      calc x ^ 13231000 = (x ^ 13231) ^ 1000 := by rw [← Nat.pow_mul]
        _ < (p ^ 10000) ^ 1000 := h
        _ = p ^ 10000000 := by rw [← Nat.pow_mul]
    have hkey : n ^ 13230000 < p ^ 10000000 :=
      lt_trans (lt_of_le_of_lt hstep1 hstep2) hstep3
    have hkey' : (n ^ 1323) ^ 10000 < (p ^ 1000) ^ 10000 := by
      calc (n ^ 1323) ^ 10000 = n ^ 13230000 := by rw [← Nat.pow_mul]
        _ < p ^ 10000000 := hkey
        _ = (p ^ 1000) ^ 10000 := by rw [← Nat.pow_mul]
    exact (Nat.pow_lt_pow_iff_left (by norm_num : (10000 : ℕ) ≠ 0)).mp hkey'
