import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem L_goldbach_cert_95 :
    ∀ a:ℕ, Nat.Coprime a 95 → (∑ b ∈ (Finset.range 95).filter (fun b => Nat.Coprime b 95), Complex.exp (((2*Real.pi*(a:ℝ)*b/95:ℝ):ℂ)*Complex.I))/(72:ℂ)=(1:ℂ)/72 := by
  intro a ha
  let θ : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / 95)
  let z := Complex.exp θ
  have hz : IsPrimitiveRoot z 95 :=
    Complex.isPrimitiveRoot_exp_of_coprime a 95 (by decide) ha
  have phase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 95 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    calc
      Complex.exp _ = Complex.exp ((b : ℂ) * θ) := by
        apply congrArg Complex.exp
        dsimp only [θ]
        push_cast
        ring
      _ = z ^ b := Complex.exp_nat_mul θ b
  have h₁₉ : IsPrimitiveRoot (z ^ 5) 19 :=
    IsPrimitiveRoot.pow (a := 5) (b := 19) (by decide) hz (by decide)
  have h₅ : IsPrimitiveRoot (z ^ 19) 5 :=
    IsPrimitiveRoot.pow (a := 19) (b := 5) (by decide) hz (by decide)
  have residues : (Finset.range 95).filter (fun b => Nat.Coprime b 95) =
      ({1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 13, 14, 16, 17, 18, 21, 22, 23,
        24, 26, 27, 28, 29, 31, 32, 33, 34, 36, 37, 39, 41, 42, 43, 44, 46, 47,
        48, 49, 51, 52, 53, 54, 56, 58, 59, 61, 62, 63, 64, 66, 67, 68, 69, 71,
        72, 73, 74, 77, 78, 79, 81, 82, 83, 84, 86, 87, 88, 89, 91, 92, 93, 94} :
        Finset ℕ) := by decide
  -- Remove multiples of 5 and 19, restoring their common multiple 0.
  have sum_units : (∑ b ∈ (Finset.range 95).filter (fun b => Nat.Coprime b 95), z ^ b) =
      (∑ j ∈ Finset.range 95, z ^ j) - (∑ j ∈ Finset.range 19, (z ^ 5) ^ j) -
        (∑ j ∈ Finset.range 5, (z ^ 19) ^ j) + 1 := by
    rw [residues]
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton,
      Finset.sum_range_succ, Finset.sum_range_zero] <;> ring
  simp_rw [phase]
  rw [sum_units, hz.geom_sum_eq_zero (by decide), h₁₉.geom_sum_eq_zero (by decide),
    h₅.geom_sum_eq_zero (by decide)]
  simp

end PEqualNP.Outside
