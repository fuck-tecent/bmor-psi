import Mathlib

theorem PEqualNP.Outside.L_goldbach_dyadic_conductor_ratio :
    ∀ k j : ℕ, j+2≤k → (Nat.totient (2^k/2^j):ℝ)/(Nat.totient (2^k):ℝ) = 1/(2:ℝ)^j := by
  intro k j hjk
  have hjk' : j ≤ k := by omega
  have hkj : 0 < k - j := by omega
  have hk0 : 0 < k := by omega
  have hdiv : 2 ^ k / 2 ^ j = 2 ^ (k - j) := Nat.pow_div hjk' (by norm_num)
  have ht1 : Nat.totient (2 ^ (k - j)) = 2 ^ (k - j - 1) := by
    rw [Nat.totient_prime_pow (by norm_num : Nat.Prime 2) hkj]
    norm_num
  have ht2 : Nat.totient (2 ^ k) = 2 ^ (k - 1) := by
    rw [Nat.totient_prime_pow (by norm_num : Nat.Prime 2) hk0]
    norm_num
  rw [hdiv, ht1, ht2]
  push_cast
  have hkminus : k - 1 = (k - j - 1) + j := by omega
  rw [hkminus, pow_add]
  have hA : (2:ℝ) ^ (k - j - 1) ≠ 0 := by positivity
  have hB : (2:ℝ) ^ j ≠ 0 := by positivity
  field_simp
