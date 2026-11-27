import Mathlib

theorem PEqualNP.Outside.L_goldbach_power_base_bound :
    ∀ p j X : ℕ, 2≤p → 2≤j → p^j≤X → p≤Nat.sqrt X := by
  intro p j X hp hj hX
  apply Nat.le_sqrt'.2
  calc
    p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right (by omega) hj
    _ ≤ X := hX
