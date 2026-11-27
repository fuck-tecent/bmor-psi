import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_repeated_residue_direction_positive :
    ∀ (p x y u v s t : ℤ), 0 < p → (((x+p*u)-x)*(t-y) = ((y+p*v)-y)*(s-x) ↔ u*(t-y) = v*(s-x)) := by
  intro p x y u v s t hp
  have hx : (x + p * u) - x = p * u := by ring
  have hy : (y + p * v) - y = p * v := by ring
  rw [hx, hy]
  constructor
  · intro h
    have h' : p * (u * (t - y)) = p * (v * (s - x)) := by
      calc p * (u * (t - y)) = p * u * (t - y) := by ring
        _ = p * v * (s - x) := h
        _ = p * (v * (s - x)) := by ring
    exact mul_left_cancel₀ hp.ne' h'
  · intro h
    calc p * u * (t - y) = p * (u * (t - y)) := by ring
      _ = p * (v * (s - x)) := by rw [h]
      _ = p * v * (s - x) := by ring
