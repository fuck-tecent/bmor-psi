import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

open scoped BigOperators

/-- Root-of-unity cancellation for every frequency coprime to eighty-four. -/
theorem PEqualNP.Outside.L_goldbach_cert_84 :
    ∀ a:ℕ, Nat.Coprime a 84 → (∑ b ∈ (Finset.range 84).filter (fun b => Nat.Coprime b 84), Complex.exp (((2*Real.pi*(a:ℝ)*b/84:ℝ):ℂ)*Complex.I))/(24:ℂ)=(0:ℂ)/24 := by
  intro a ha
  have ha2 : Nat.Coprime a 2 :=
    Nat.Coprime.of_dvd_right (by decide : 2 ∣ 84) ha
  have hodd : Odd a := Nat.coprime_two_right.mp ha2
  let z : ℂ := Complex.exp (((2 * Real.pi * (a : ℝ) / 84 : ℝ) : ℂ) * Complex.I)
  have hexp (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 84 : ℝ) : ℂ) * Complex.I) =
        z ^ b := by
    dsimp only [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz42 : z ^ 42 = -1 := by
    calc
      z ^ 42 = Complex.exp ((a : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
        dsimp only [z]
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ = (-1 : ℂ) ^ a := by
        rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
      _ = -1 := hodd.neg_one_pow
  have hU : (Finset.range 84).filter (fun b => Nat.Coprime b 84) =
      ({1, 5, 11, 13, 17, 19, 23, 25, 29, 31, 37, 41,
        43, 47, 53, 55, 59, 61, 65, 67, 71, 73, 79, 83} : Finset ℕ) := by
    decide
  have hpoly :
      (∑ b ∈ ({1, 5, 11, 13, 17, 19, 23, 25, 29, 31, 37, 41,
        43, 47, 53, 55, 59, 61, 65, 67, 71, 73, 79, 83} : Finset ℕ), z ^ b) =
      (z + z ^ 5 + z ^ 11 + z ^ 13 + z ^ 17 + z ^ 19 +
        z ^ 23 + z ^ 25 + z ^ 29 + z ^ 31 + z ^ 37 + z ^ 41) *
        (1 + z ^ 42) := by
    norm_num <;> ring
  simp_rw [hexp]
  rw [hU, hpoly, hz42]
  simp
