import Mathlib

/-- Shifting both sides of the residue-invariance lemma for `n ^ 2 + 1` by the same `c` keeps the
congruence: representatives that agree modulo `m` still agree after squaring and adding `1 + c`. -/
theorem Conjectures.QuadraticPrimes.ShiftedResidueInvariance :
    ∀ (m a b c : ℕ), a % m = b % m → (a ^ 2 + (1 + c)) % m = (b ^ 2 + (1 + c)) % m := by
  intro m a b c h
  have hm : Nat.ModEq m a b := h
  exact Nat.ModEq.add_right (1 + c) (Nat.ModEq.pow 2 hm)
