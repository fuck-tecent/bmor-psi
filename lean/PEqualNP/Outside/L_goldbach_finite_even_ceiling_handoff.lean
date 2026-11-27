import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_even_ceiling_handoff :
    ∀ (X : ℝ) (n : ℕ), 0 ≤ X → Even n → X ≤ n → 2*⌈X/2⌉₊ ≤ n := by
  intro X n _hX hev hXn
  obtain ⟨k, hk⟩ := hev
  have hcast : (n : ℝ) = 2 * (k : ℝ) := by
    rw [hk]
    push_cast
    ring
  have hXk : X / 2 ≤ (k : ℝ) := by linarith
  have hc : ⌈X / 2⌉₊ ≤ k := Nat.ceil_le.mpr hXk
  have h2 : 2 * ⌈X / 2⌉₊ ≤ 2 * k := Nat.mul_le_mul_left 2 hc
  omega
