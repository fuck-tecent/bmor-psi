import Mathlib

/-- Adding a full modulus to the target preserves the admissible residues. -/
theorem PEqualNP.Outside.L_goldbach_unit_period :
    let U := fun q n : ℕ => (Finset.range q).filter
      (fun a => Nat.Coprime a q ∧ Nat.Coprime (n + q - a) q)
    ∀ q n, U q (n + q) = U q n := by
  intro U q n
  ext a
  by_cases ha : a < q
  · have shift : n + q + q - a = (n + q - a) + q := by omega
    simp only [U, Finset.mem_filter, shift, Nat.coprime_add_self_left]
  · simp [U, ha]
