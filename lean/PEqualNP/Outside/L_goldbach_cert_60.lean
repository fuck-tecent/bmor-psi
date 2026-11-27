import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

open scoped BigOperators

/-- Root-of-unity cancellation for every frequency coprime to sixty. -/
theorem PEqualNP.Outside.L_goldbach_cert_60 :
    ∀ a:ℕ, Nat.Coprime a 60 → (∑ b ∈ (Finset.range 60).filter (fun b => Nat.Coprime b 60), Complex.exp (((2*Real.pi*(a:ℝ)*b/60:ℝ):ℂ)*Complex.I))/(16:ℂ)=(0:ℂ)/16 := by
  intro a ha
  have ha2 : Nat.Coprime a 2 :=
    Nat.Coprime.of_dvd_right (by decide : 2 ∣ 60) ha
  have hodd : Odd a := Nat.coprime_two_right.mp ha2
  let z : ℂ := Complex.exp (((2 * Real.pi * (a : ℝ) / 60 : ℝ) : ℂ) * Complex.I)
  have hexp (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 60 : ℝ) : ℂ) * Complex.I) =
        z ^ b := by
    dsimp only [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz30 : z ^ 30 = -1 := by
    calc
      z ^ 30 = Complex.exp ((a : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
        dsimp only [z]
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ = (-1 : ℂ) ^ a := by
        rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
      _ = -1 := hodd.neg_one_pow
  have hU : (Finset.range 60).filter (fun b => Nat.Coprime b 60) =
      ({1, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 49, 53, 59} : Finset ℕ) := by
    decide
  have hpoly :
      (∑ b ∈ ({1, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 49, 53, 59} : Finset ℕ),
        z ^ b) =
      (z + z ^ 7 + z ^ 11 + z ^ 13 + z ^ 17 + z ^ 19 + z ^ 23 + z ^ 29) *
        (1 + z ^ 30) := by
    norm_num <;> ring
  simp_rw [hexp]
  rw [hU, hpoly, hz30]
  simp
