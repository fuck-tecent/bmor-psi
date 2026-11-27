import Mathlib

namespace Conjectures.Goldbach.Rfc11DyadicCover_aux

theorem two_pow_597_split : (2:ℕ)^597 = ((2:ℕ)^199)^3 := by
  rw [← Nat.pow_mul (2:ℕ) 199 3]

theorem ten_pow_180_split : (10:ℕ)^180 = ((10:ℕ)^60)^3 := by
  rw [← Nat.pow_mul (10:ℕ) 60 3]

theorem two_pow_598_split : (2:ℕ)^598 = (2:ℕ)^256 * (2:ℕ)^256 * (2:ℕ)^86 := by
  rw [← Nat.pow_add (2:ℕ) 256 256, ← Nat.pow_add (2:ℕ) 512 86]

theorem two_pow_1049_split :
    (2:ℕ)^1049 = (2:ℕ)^256 * (2:ℕ)^256 * (2:ℕ)^256 * (2:ℕ)^256 * (2:ℕ)^25 := by
  rw [← Nat.pow_add (2:ℕ) 256 256, ← Nat.pow_add (2:ℕ) 512 256, ← Nat.pow_add (2:ℕ) 768 256,
    ← Nat.pow_add (2:ℕ) 1024 25]

theorem two_pow_1050_split :
    (2:ℕ)^1050 = (2:ℕ)^256 * (2:ℕ)^256 * (2:ℕ)^256 * (2:ℕ)^256 * (2:ℕ)^26 := by
  rw [← Nat.pow_add (2:ℕ) 256 256, ← Nat.pow_add (2:ℕ) 512 256, ← Nat.pow_add (2:ℕ) 768 256,
    ← Nat.pow_add (2:ℕ) 1024 26]

theorem ten_pow_316_split : (10:ℕ)^316 = (10:ℕ)^256 * (10:ℕ)^60 := by
  rw [← Nat.pow_add (10:ℕ) 256 60]

end Conjectures.Goldbach.Rfc11DyadicCover_aux

theorem Conjectures.Goldbach.Rfc11DyadicCover :
    (2:ℕ)^597 < 10^180 ∧ (10:ℕ)^180 < 2^598 ∧ (2:ℕ)^1049 < 10^316 ∧ (10:ℕ)^316 < 2^1050 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Conjectures.Goldbach.Rfc11DyadicCover_aux.two_pow_597_split,
      Conjectures.Goldbach.Rfc11DyadicCover_aux.ten_pow_180_split]
    norm_num
  · rw [Conjectures.Goldbach.Rfc11DyadicCover_aux.two_pow_598_split]
    norm_num
  · rw [Conjectures.Goldbach.Rfc11DyadicCover_aux.two_pow_1049_split,
      Conjectures.Goldbach.Rfc11DyadicCover_aux.ten_pow_316_split]
    norm_num
  · rw [Conjectures.Goldbach.Rfc11DyadicCover_aux.two_pow_1050_split,
      Conjectures.Goldbach.Rfc11DyadicCover_aux.ten_pow_316_split]
    norm_num
