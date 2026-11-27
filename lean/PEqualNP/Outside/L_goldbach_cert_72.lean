import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

open scoped BigOperators

/-- Root-of-unity cancellation for every frequency coprime to seventy-two. -/
theorem PEqualNP.Outside.L_goldbach_cert_72 :
    ∀ a:ℕ, Nat.Coprime a 72 → (∑ b ∈ (Finset.range 72).filter (fun b => Nat.Coprime b 72), Complex.exp (((2*Real.pi*(a:ℝ)*b/72:ℝ):ℂ)*Complex.I))/(24:ℂ)=(0:ℂ)/24 := by
  intro a ha
  have ha2 : Nat.Coprime a 2 :=
    Nat.Coprime.of_dvd_right (by decide : 2 ∣ 72) ha
  have hodd : Odd a := Nat.coprime_two_right.mp ha2
  let z : ℂ := Complex.exp (((2 * Real.pi * (a : ℝ) / 72 : ℝ) : ℂ) * Complex.I)
  have hexp (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 72 : ℝ) : ℂ) * Complex.I) =
        z ^ b := by
    dsimp only [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz36 : z ^ 36 = -1 := by
    calc
      z ^ 36 = Complex.exp ((a : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
        dsimp only [z]
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ = (-1 : ℂ) ^ a := by
        rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
      _ = -1 := hodd.neg_one_pow
  have hU : (Finset.range 72).filter (fun b => Nat.Coprime b 72) =
      ({1, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35,
        37, 41, 43, 47, 49, 53, 55, 59, 61, 65, 67, 71} : Finset ℕ) := by
    decide
  have hpoly :
      (∑ b ∈ ({1, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35,
        37, 41, 43, 47, 49, 53, 55, 59, 61, 65, 67, 71} : Finset ℕ), z ^ b) =
      (z + z ^ 5 + z ^ 7 + z ^ 11 + z ^ 13 + z ^ 17 +
        z ^ 19 + z ^ 23 + z ^ 25 + z ^ 29 + z ^ 31 + z ^ 35) *
        (1 + z ^ 36) := by
    norm_num <;> ring
  simp_rw [hexp]
  rw [hU, hpoly, hz36]
  simp
