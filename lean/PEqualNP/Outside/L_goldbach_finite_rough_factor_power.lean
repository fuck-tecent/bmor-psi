import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_rough_factor_power :
    ∀ s y : ℕ, 2 ≤ s → 2 ≤ y → (∀ p, Nat.Prime p → p ∣ s → y ≤ p) → y^(s.primeFactorsList.length) ≤ s := by
  intro s y hs _ hrough
  calc
    y ^ s.primeFactorsList.length ≤ s.primeFactorsList.prod := by
      apply List.pow_length_le_prod
      intro p hp
      exact hrough p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)
    _ = s := Nat.prod_primeFactorsList (by omega)
