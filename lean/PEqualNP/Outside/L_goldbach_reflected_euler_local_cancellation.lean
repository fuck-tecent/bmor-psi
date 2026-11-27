import Mathlib

/-!
# First-order cancellation in a reflected-divisor Euler factor

Clearing the denominators `p - 1`, `p` and `p - u` turns the identity into the polynomial identity
`p * (p - 1 - u) * ((p - 1) * (p - u)) = ((p - 1) * (p - u) - u) * ((p - 1) * (p - u)) / ...`, which `ring` checks; the hypotheses `1 < p` and `u ≠ p` are exactly what makes the denominators nonzero.
-/

theorem PEqualNP.Outside.L_goldbach_reflected_euler_local_cancellation :
    ∀ p u : ℝ, 1 < p → u ≠ p → (1-u/(p-1))/(1-u/p) = 1-u/((p-1)*(p-u)) := by
  intro p u hp hu
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hpu : p - u ≠ 0 := by
    intro h
    apply hu
    linarith
  have h1 : 1 - u/p ≠ 0 := by
    intro h
    apply hu
    have hq : u/p = 1 := by linarith
    rw [div_eq_iff hp0] at hq
    linarith
  field_simp
  ring
