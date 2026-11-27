import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

open scoped BigOperators

/-- Root-of-unity cancellation for every frequency coprime to one hundred twenty. -/
theorem PEqualNP.Outside.L_goldbach_cert_120 :
    ∀ a:ℕ, Nat.Coprime a 120 → (∑ b ∈ (Finset.range 120).filter (fun b => Nat.Coprime b 120), Complex.exp (((2*Real.pi*(a:ℝ)*b/120:ℝ):ℂ)*Complex.I))/(32:ℂ)=(0:ℂ)/32 := by
  intro a ha
  have ha2 : Nat.Coprime a 2 :=
    Nat.Coprime.of_dvd_right (by decide : 2 ∣ 120) ha
  have hodd : Odd a := Nat.coprime_two_right.mp ha2
  let z : ℂ := Complex.exp (((2 * Real.pi * (a : ℝ) / 120 : ℝ) : ℂ) * Complex.I)
  have hexp (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 120 : ℝ) : ℂ) * Complex.I) =
        z ^ b := by
    dsimp only [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz60 : z ^ 60 = -1 := by
    calc
      z ^ 60 = Complex.exp ((a : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
        dsimp only [z]
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ = (-1 : ℂ) ^ a := by
        rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
      _ = -1 := hodd.neg_one_pow
  have hU : (Finset.range 120).filter (fun b => Nat.Coprime b 120) =
      ({1, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 49, 53, 59,
        61, 67, 71, 73, 77, 79, 83, 89, 91, 97, 101, 103, 107, 109, 113, 119} : Finset ℕ) := by
    decide
  have hpoly :
      (∑ b ∈ ({1, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 49, 53, 59,
        61, 67, 71, 73, 77, 79, 83, 89, 91, 97, 101, 103, 107, 109, 113, 119} : Finset ℕ),
        z ^ b) =
      (z + z ^ 7 + z ^ 11 + z ^ 13 + z ^ 17 + z ^ 19 + z ^ 23 + z ^ 29 +
        z ^ 31 + z ^ 37 + z ^ 41 + z ^ 43 + z ^ 47 + z ^ 49 + z ^ 53 + z ^ 59) *
        (1 + z ^ 60) := by
    norm_num <;> ring
  simp_rw [hexp]
  rw [hU, hpoly, hz60]
  simp
