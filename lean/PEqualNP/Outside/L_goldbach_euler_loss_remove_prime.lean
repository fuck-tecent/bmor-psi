import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_euler_loss_remove_prime :
    ∀ (S : Finset ℕ) (z : ℕ → ℂ) (p : ℕ), p∈S → (∏ i ∈ S,(1-z i))-(∏ i ∈ S.erase p,(1-z i)) = -z p*(∏ i ∈ S.erase p,(1-z i)) := by
  intro S z p hp
  rw [← Finset.mul_prod_erase S (fun i => 1 - z i) hp]
  ring
