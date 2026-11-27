import Mathlib

theorem PEqualNP.Outside.L_goldbach_minor_type_two_tail_divisor_majorant :
    ∀ U R : ℕ, |∑ d ∈ R.divisors.filter (fun d => U < d), (ArithmeticFunction.moebius d:ℝ)| ≤ (R.divisors.card:ℝ) := by
  intro U R
  calc
    _ ≤ ∑ d ∈ R.divisors.filter (fun d => U < d), |(ArithmeticFunction.moebius d:ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ R.divisors.filter (fun d => U < d), (1:ℝ) := Finset.sum_le_sum fun d _ => by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=d))
    _ ≤ _ := by simpa using (show (((R.divisors.filter (fun d => U < d)).card:ℝ) ≤ (R.divisors.card:ℝ)) by exact_mod_cast Finset.card_filter_le _ _)
