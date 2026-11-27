import Mathlib

theorem Conjectures.JoshiAbc.FreyHeight :
  let h := fun (a b : ℕ) => Real.log ((a:ℝ)+b); ∀ a b : ℕ, 0 < a → 0 < b → 2*h a b + Real.log 12 ≤ Real.log (16*((a:ℝ)^2+a*b+(b:ℝ)^2)) := by
  intro h a b ha hb
  dsimp only [h]
  have ha' : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr ha
  have hb' : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  have h1 : 2 * Real.log ((a : ℝ) + b) = Real.log (((a : ℝ) + b) ^ 2) := by
    rw [Real.log_pow, Nat.cast_ofNat]
  rw [h1, ← Real.log_mul]
  · apply Real.log_le_log
    · positivity
    · nlinarith [sq_nonneg ((a : ℝ) - b)]
  · positivity
  · positivity