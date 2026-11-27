import Mathlib

theorem PEqualNP.Outside.L_goldbach_factor_line_fiber_determinant :
    ∀ (a b N r₀ s₀ g i j : ℤ), 0 < g → g ∣ a → g ∣ b → a*r₀+b*s₀=N → (r₀+(b/g)*i)*(s₀-(a/g)*j)-(r₀+(b/g)*j)*(s₀-(a/g)*i)=-(N/g)*(j-i) := by
  intro a b N r₀ s₀ g i j hg hga hgb hN
  have hg0 : g ≠ 0 := ne_of_gt hg
  rcases hga with ⟨ka, rfl⟩
  rcases hgb with ⟨kb, rfl⟩
  subst hN
  have hsum : g * ka * r₀ + g * kb * s₀ = g * (ka * r₀ + kb * s₀) := by ring
  rw [hsum, Int.mul_ediv_cancel_left _ hg0, Int.mul_ediv_cancel_left _ hg0,
    Int.mul_ediv_cancel_left _ hg0]
  ring
