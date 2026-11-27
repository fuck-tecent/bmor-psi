import Mathlib

theorem Conjectures.QuadraticPrimes.SieveGaussianFiber :
    ∀ a b c₀ d₀ c d : ℤ, a*d₀+b*c₀=1 →
  (a*d+b*c=1 ↔ ∃ t : ℤ, c=c₀+a*t ∧ d=d₀-b*t) ∧
  (∀ t : ℤ, a*(c₀+a*t)-b*(d₀-b*t) = (a*c₀-b*d₀)+(a^2+b^2)*t) ∧
  (2*(a*c₀-b*d₀))^2 - 4*(a^2+b^2)*(c₀^2+d₀^2) = -4 := by
  intro a b c₀ d₀ c d h
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hcd
      have h0 : a * (d - d₀) + b * (c - c₀) = 0 := by linarith
      refine ⟨(c - c₀) * d₀ - (d - d₀) * c₀, ?_, ?_⟩
      · have key : a * ((c - c₀) * d₀ - (d - d₀) * c₀) = c - c₀ := by
          linear_combination (c - c₀) * h - c₀ * h0
        linarith
      · have key : b * ((c - c₀) * d₀ - (d - d₀) * c₀) = -(d - d₀) := by
          linear_combination (-(d - d₀)) * h + d₀ * h0
        linarith
    · rintro ⟨t, rfl, rfl⟩
      linear_combination h
  · intro t
    ring
  · have hid : (a*c₀ - b*d₀)^2 + (a*d₀ + b*c₀)^2 = (a^2+b^2)*(c₀^2+d₀^2) := by ring
    linear_combination 4 * hid - 4 * (a*d₀ + b*c₀ + 1) * h
