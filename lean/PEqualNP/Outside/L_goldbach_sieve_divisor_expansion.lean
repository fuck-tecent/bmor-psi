import Mathlib

theorem PEqualNP.Outside.L_goldbach_sieve_divisor_expansion :
    let S := fun n : ℕ => ∏ p ∈ n.primeFactors.filter (fun p => 2<p), (1+1/((p:ℝ)-2)); ∀ n : ℕ, (S n)^2 = ∑ t ∈ (n.primeFactors.filter (fun p => 2<p)).powerset, ∏ p ∈ t, ((1+1/((p:ℝ)-2))^2-1) := by
  dsimp only
  intro n
  rw [← Finset.prod_pow, ← Finset.prod_one_add]
  apply Finset.prod_congr rfl
  intro p _
  ring
