import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

def E (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

lemma E_add (x y : ℝ) : E x * E y = E (x + y) := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Arc integral: translating the arc to the origin factors out the central
phase. -/
lemma integral_E_arc (h : ℤ) (c ρ : ℝ) :
    (∫ t in (c - ρ)..(c + ρ), E ((h:ℝ)*t))
      = E ((h:ℝ)*c) * ∫ β in (-ρ)..ρ, E ((h:ℝ)*β) := by
  have h1 : (∫ t in (c - ρ)..(c + ρ), E ((h:ℝ)*t))
      = ∫ β in (-ρ)..ρ, E ((h:ℝ)*(c + β)) := by
    have := intervalIntegral.integral_comp_add_left
      (f := fun t : ℝ => E ((h:ℝ)*t)) (a := -ρ) (b := ρ) (d := c)
    rw [this]
    congr 1
  rw [h1]
  have h2 : ∀ β : ℝ, E ((h:ℝ)*(c + β)) = E ((h:ℝ)*c) * E ((h:ℝ)*β) := by
    intro β
    rw [show (h:ℝ)*(c + β) = (h:ℝ)*c + (h:ℝ)*β by ring, ← E_add]
  simp_rw [h2]
  rw [intervalIntegral.integral_const_mul]

end B1B1
