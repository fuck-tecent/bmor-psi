import Mathlib
import PEqualNP.Outside.L_goldbach_arc_major_floor

theorem Conjectures.Cuts.Task806407a84ed180a3d42158cd :
    (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * x2) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), ↑(x4 x6) * x2 (↑x6 * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - ↑x8 / ↑x7| ≤ ↑(x4 x5) / (↑x7 * ↑x5)}; have x6 : ℕ → ℝ → ℂ := fun (x6 : ℕ) (x7 : ℝ) => x3 x6 x1 x7 ^ (2 : ℕ) * x2 (-↑x6 * x7); have x7 : ℕ → ℂ := fun (x7 : ℕ) => ∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x7).indicator (x6 x7) x8; ∃ (x8 : ℝ) (x9 : ℕ), (0 : ℝ) < x8 ∧ ∀ (x10 : ℕ), x9 ≤ x10 → Even x10 → x8 * ↑x10 ≤ (x7 x10).re) := by
  exact PEqualNP.Outside.L_goldbach_arc_major_floor
