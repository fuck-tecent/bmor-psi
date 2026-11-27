import Mathlib

noncomputable section

theorem Conjectures.Goldbach.FrontierType2B1B1TauSupport :
  let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) * ArithmeticFunction.vonMangoldt (m / a); ∀ n m : ℕ, m ≤ (U n)^2 → τ₁ n m = 0 := by
  dsimp only
  intro n m hm
  apply Finset.sum_eq_zero
  intro a ha
  have hd := (Finset.mem_filter.mp ha).1
  have hh := (Finset.mem_filter.mp ha).2
  have hdiv : a ∣ m := (Nat.mem_divisors.mp hd).1
  have heq := Nat.mul_div_cancel' hdiv
  nlinarith
