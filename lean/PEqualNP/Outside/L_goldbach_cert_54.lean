import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

set_option maxHeartbeats 1000000 in
theorem L_goldbach_cert_54 :
    ∀ a:ℕ, Nat.Coprime a 54 → (∑ b ∈ (Finset.range 54).filter (fun b => Nat.Coprime b 54), Complex.exp (((2*Real.pi*(a:ℝ)*b/54:ℝ):ℂ)*Complex.I))/(18:ℂ)=(0:ℂ)/18 := by
  intro a ha
  let θ : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / 54)
  let z := Complex.exp θ
  have hz : IsPrimitiveRoot z 54 :=
    Complex.isPrimitiveRoot_exp_of_coprime a 54 (by decide) ha
  have phase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 54 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    calc
      Complex.exp _ = Complex.exp ((b : ℂ) * θ) := by
        apply congrArg Complex.exp
        dsimp only [θ]
        push_cast
        ring
      _ = z ^ b := Complex.exp_nat_mul θ b
  have h₉ : IsPrimitiveRoot (z ^ 6) 9 :=
    IsPrimitiveRoot.pow (a := 6) (b := 9) (by decide) hz (by decide)
  have residues : (Finset.range 54).filter (fun b => Nat.Coprime b 54) =
      ({1, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35, 37, 41, 43, 47, 49, 53} : Finset ℕ) := by
    decide
  -- The units are the two progressions 6j + 1 and 6j + 5.
  have sum_units : (∑ b ∈ (Finset.range 54).filter (fun b => Nat.Coprime b 54), z ^ b) =
      (z + z ^ 5) * (∑ j ∈ Finset.range 9, (z ^ 6) ^ j) := by
    rw [residues]
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton,
      Finset.sum_range_succ, Finset.sum_range_zero] <;> ring
  simp_rw [phase]
  rw [sum_units, h₉.geom_sum_eq_zero (by decide)]
  simp

end PEqualNP.Outside
