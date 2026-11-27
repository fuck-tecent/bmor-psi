import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

theorem PEqualNP.Outside.L_goldbach_ram_period :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ q h, 0<q → ram q (h+q)=ram q h := by
  dsimp only
  intro q h hq
  apply Finset.sum_congr rfl
  intro a _
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hshift : ((h + q : ℕ) : ℝ) * a / q = (h : ℝ) * a / q + a := by
    rw [Nat.cast_add, add_mul, add_div, mul_div_cancel_left₀ _ hq']
  rw [hshift, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]
  have hphase : ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I =
      (a : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [hphase, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
