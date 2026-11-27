import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

set_option maxHeartbeats 1000000 in
theorem L_goldbach_cert_42 :
    ∀ a:ℕ, Nat.Coprime a 42 → (∑ b ∈ (Finset.range 42).filter (fun b => Nat.Coprime b 42), Complex.exp (((2*Real.pi*(a:ℝ)*b/42:ℝ):ℂ)*Complex.I))/(12:ℂ)=(-1:ℂ)/12 := by
  intro a ha
  let θ : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / 42)
  let z := Complex.exp θ
  have hz : IsPrimitiveRoot z 42 :=
    Complex.isPrimitiveRoot_exp_of_coprime a 42 (by decide) ha
  have phase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 42 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    calc
      Complex.exp _ = Complex.exp ((b : ℂ) * θ) := by
        apply congrArg Complex.exp
        dsimp only [θ]
        push_cast
        ring
      _ = z ^ b := Complex.exp_nat_mul θ b
  have h₂ : IsPrimitiveRoot (z ^ 21) 2 :=
    IsPrimitiveRoot.pow (a := 21) (b := 2) (by decide) hz (by decide)
  have h₃ : IsPrimitiveRoot (z ^ 14) 3 :=
    IsPrimitiveRoot.pow (a := 14) (b := 3) (by decide) hz (by decide)
  have h₇ : IsPrimitiveRoot (z ^ 6) 7 :=
    IsPrimitiveRoot.pow (a := 6) (b := 7) (by decide) hz (by decide)
  have h₂₁ : IsPrimitiveRoot (z ^ 2) 21 :=
    IsPrimitiveRoot.pow (a := 2) (b := 21) (by decide) hz (by decide)
  have residues : (Finset.range 42).filter (fun b => Nat.Coprime b 42) =
      ({1, 5, 11, 13, 17, 19, 23, 25, 29, 31, 37, 41} : Finset ℕ) := by
    decide
  -- Include the odd residues, remove the odd multiples of 3 and 7, and restore 21.
  have sum_units : (∑ b ∈ (Finset.range 42).filter (fun b => Nat.Coprime b 42), z ^ b) =
      z * (∑ j ∈ Finset.range 21, (z ^ 2) ^ j) -
      z ^ 3 * (∑ j ∈ Finset.range 7, (z ^ 6) ^ j) -
      z ^ 7 * (∑ j ∈ Finset.range 3, (z ^ 14) ^ j) + z ^ 21 := by
    rw [residues]
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton,
      Finset.sum_range_succ, Finset.sum_range_zero] <;> ring
  simp_rw [phase]
  rw [sum_units, h₂₁.geom_sum_eq_zero (by decide), h₇.geom_sum_eq_zero (by decide),
    h₃.geom_sum_eq_zero (by decide)]
  simp [h₂.eq_neg_one_of_two_right]

end PEqualNP.Outside
