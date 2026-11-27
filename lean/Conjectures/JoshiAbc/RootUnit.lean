import Mathlib

theorem Conjectures.JoshiAbc.RootUnit :
  ∀ (p l : ℕ) [Fact p.Prime] (z : ZMod p), p ≠ 2 → Odd l → z^l=1 → z+z⁻¹ ≠ 0 := by
  intro p l hp z hp2 hl hzl hsum
  rcases hl with ⟨k, rfl⟩
  have hz : z ≠ 0 := by
    rintro rfl
    have he : 2 * k + 1 ≠ 0 := by omega
    rw [zero_pow he] at hzl
    exact zero_ne_one hzl
  have hz2 : z ^ 2 = -1 := by
    have h1 : z * (z + z⁻¹) = 0 := by rw [hsum, mul_zero]
    rw [mul_add, mul_inv_cancel₀ hz] at h1
    linear_combination h1
  have h1 : (1 : ZMod p) = -1 := by
    calc
      (1 : ZMod p) = (z ^ (2 * k + 1)) ^ 2 := by rw [hzl, one_pow]
      _ = (z ^ 2) ^ (2 * k + 1) := by rw [← pow_mul, Nat.mul_comm (2 * k + 1) 2, pow_mul]
      _ = (-1) ^ (2 * k + 1) := by rw [hz2]
      _ = ((-1 : ZMod p) ^ 2) ^ k * (-1) := by rw [pow_succ, pow_mul]
      _ = -1 := by
        have hsq : (-1 : ZMod p) ^ 2 = 1 := by ring
        rw [hsq, one_pow, one_mul]
  have h2 : (2 : ZMod p) = 0 := by linear_combination h1
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2)
  have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
  have hge : 2 ≤ p := hp.out.two_le
  omega
