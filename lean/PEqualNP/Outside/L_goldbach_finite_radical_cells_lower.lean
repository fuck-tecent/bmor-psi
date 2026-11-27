import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.GCD.Basic

theorem PEqualNP.Outside.L_goldbach_finite_radical_cells_lower :
    ∀ n d : ℕ, Nat.gcd n 105 = d → d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 7 ∨ d = 15 ∨ d = 21 ∨ d = 35 ∨ d = 105 := by
  intro n d hd
  have hdiv : d ∣ 105 := hd ▸ Nat.gcd_dvd_right n 105
  have hbound : d ≤ 105 := Nat.le_of_dvd (by decide) hdiv
  interval_cases d <;> first | (norm_num at hdiv; done) | decide
