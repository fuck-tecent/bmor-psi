import Mathlib

theorem PEqualNP.Outside.L_log_rank_product_four_corners :
    ∀ u v s t a : ℤ, u ≠ v → s ≠ t → ¬ ((u+s=a ∨ u+s=a+1) ∧ (u+t=a ∨ u+t=a+1) ∧ (v+s=a ∨ v+s=a+1) ∧ (v+t=a ∨ v+t=a+1)) := by
  intro u v s t a huv hst h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4 <;>
    omega
