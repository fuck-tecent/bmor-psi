import Mathlib

theorem Conjectures.QuadraticPrimes.BlockExponentFirstIncrementTransfer :
    ∀ x n p : ℕ, x≤n → n≤2*x → 2^132301 < x^9 → x^13231 < p^10000 → n^132301 < p^100000 := by
  intro x n p _ hnx hx hp
  have hxpos : 0 < x := by
    rcases Nat.eq_zero_or_pos x with rfl | h
    · simp at hx
    · exact h
  calc
    n ^ 132301 ≤ (2 * x) ^ 132301 := Nat.pow_le_pow_left hnx 132301
    _ = 2 ^ 132301 * x ^ 132301 := Nat.mul_pow 2 x 132301
    _ < x ^ 9 * x ^ 132301 :=
      Nat.mul_lt_mul_of_pos_right hx (pow_pos hxpos 132301)
    _ = x ^ (9 + 132301) := (Nat.pow_add x 9 132301).symm
    _ = x ^ 132310 := by rfl
    _ = x ^ (13231 * 10) := rfl
    _ = (x ^ 13231) ^ 10 := Nat.pow_mul x 13231 10
    _ < (p ^ 10000) ^ 10 := Nat.pow_lt_pow_left hp (by norm_num)
    _ = p ^ (10000 * 10) := (Nat.pow_mul p 10000 10).symm
    _ = p ^ 100000 := by rfl
