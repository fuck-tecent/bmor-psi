import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

open scoped BigOperators

/-- Root-of-unity cancellation for every frequency coprime to twenty. -/
theorem PEqualNP.Outside.L_goldbach_cert_20 :
    ∀ a:ℕ, Nat.Coprime a 20 → (∑ b ∈ (Finset.range 20).filter (fun b => Nat.Coprime b 20), Complex.exp (((2*Real.pi*(a:ℝ)*b/20:ℝ):ℂ)*Complex.I))/(8:ℂ)=(0:ℂ)/8 := by
  intro a ha
  have ha2 : Nat.Coprime a 2 :=
    Nat.Coprime.of_dvd_right (by decide : 2 ∣ 20) ha
  have hodd : Odd a := Nat.coprime_two_right.mp ha2
  let z : ℂ := Complex.exp (((2 * Real.pi * (a : ℝ) / 20 : ℝ) : ℂ) * Complex.I)
  have hexp (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 20 : ℝ) : ℂ) * Complex.I) =
        z ^ b := by
    dsimp only [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz10 : z ^ 10 = -1 := by
    calc
      z ^ 10 = Complex.exp ((a : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
        dsimp only [z]
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ = (-1 : ℂ) ^ a := by
        rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
      _ = -1 := hodd.neg_one_pow
  have hU : (Finset.range 20).filter (fun b => Nat.Coprime b 20) =
      ({1, 3, 7, 9, 11, 13, 17, 19} : Finset ℕ) := by
    decide
  have hpoly : (∑ b ∈ ({1, 3, 7, 9, 11, 13, 17, 19} : Finset ℕ), z ^ b) =
      (z + z ^ 3 + z ^ 7 + z ^ 9) * (1 + z ^ 10) := by
    norm_num <;> ring
  simp_rw [hexp]
  rw [hU, hpoly, hz10]
  simp
