import Mathlib

theorem PEqualNP.Outside.L_goldbach_euler_loss_pair_correction :
    ∀ z w : ℂ, (1-z)*(1-w)-(1-z-w)=z*w := by
  intro z w
  ring
