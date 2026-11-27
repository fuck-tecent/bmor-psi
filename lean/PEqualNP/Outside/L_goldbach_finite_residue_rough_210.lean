import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

set_option maxHeartbeats 2000000 in
theorem L_goldbach_finite_residue_rough_210 :
    ∀ a : ℕ, a < 210 → Even a → ∃ p ∈ ({3,5,7,11,19} : Finset ℕ), Nat.Coprime ((a+210-p)%210) 210 := by
  intro a ha he
  obtain ⟨k, rfl⟩ := he
  have hk : k < 105 := by omega
  interval_cases k <;> decide

end PEqualNP.Outside
