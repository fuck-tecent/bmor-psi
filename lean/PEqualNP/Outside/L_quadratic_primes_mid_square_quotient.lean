import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_mid_square_quotient :
    ∀ x n p:ℕ,x<n → n≤2*x → x<p → Nat.Prime p → p^2∣n^2+1 → n^2+1=2*p^2 ∨ n^2+1=3*p^2 := by
  intro x n p hxn hnx hxp _ hd
  obtain ⟨q, hq⟩ := hd
  have hn : 0 < n := by omega
  have hs : n + 1 ≤ 2 * p := by omega
  have hu : n ^ 2 + 1 < 4 * p ^ 2 := by
    nlinarith only [Nat.pow_le_pow_left hs 2, hn]
  have hq4 : q < 4 := by
    by_contra! h
    have hc := Nat.mul_le_mul_left (p ^ 2) h
    nlinarith only [hc, hq, hu]
  have hq0 : q ≠ 0 := by
    intro hz
    subst q
    simp at hq
  have hq1 : q ≠ 1 := by
    intro ho
    subst q
    simp only [Nat.mul_one] at hq
    by_cases h : p ≤ n
    · have hs' := Nat.pow_le_pow_left h 2
      omega
    · have hh : n + 1 ≤ p := by omega
      nlinarith only [Nat.pow_le_pow_left hh 2, hn, hq]
  have hc : q = 2 ∨ q = 3 := by omega
  rcases hc with rfl | rfl
  · exact Or.inl (by simpa [Nat.mul_comm] using hq)
  · exact Or.inr (by simpa [Nat.mul_comm] using hq)
