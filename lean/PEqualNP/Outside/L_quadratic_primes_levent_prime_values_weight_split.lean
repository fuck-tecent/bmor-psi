import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_prime_values_weight_split :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let lam := fun x : ℕ => ∑ n ∈ block x, ArithmeticFunction.vonMangoldt (n^2+1); let pp := fun x : ℕ => ∑ n ∈ (block x).filter (fun n => ¬ Nat.Prime (n^2+1)), ArithmeticFunction.vonMangoldt (n^2+1); let primeMass := fun x : ℕ => ∑ n ∈ (block x).filter (fun n => Nat.Prime (n^2+1)), Real.log ((n^2+1 : ℕ) : ℝ); ∀ x : ℕ, lam x = primeMass x + pp x := by
  intro block lam pp primeMass x
  change (∑ n ∈ block x, ArithmeticFunction.vonMangoldt (n^2+1)) =
    (∑ n ∈ (block x).filter (fun n => Nat.Prime (n^2+1)), Real.log ((n^2+1 : ℕ) : ℝ)) +
    (∑ n ∈ (block x).filter (fun n => ¬ Nat.Prime (n^2+1)), ArithmeticFunction.vonMangoldt (n^2+1))
  have hs := Finset.sum_filter_add_sum_filter_not (block x)
    (fun n => Nat.Prime (n^2+1)) (fun n => ArithmeticFunction.vonMangoldt (n^2+1))
  have hp : (∑ n ∈ (block x).filter (fun n => Nat.Prime (n^2+1)), ArithmeticFunction.vonMangoldt (n^2+1)) =
      ∑ n ∈ (block x).filter (fun n => Nat.Prime (n^2+1)), Real.log ((n^2+1 : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2
  rw [hp] at hs
  exact hs.symm
