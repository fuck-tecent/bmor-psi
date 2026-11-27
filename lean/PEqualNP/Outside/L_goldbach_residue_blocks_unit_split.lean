import Mathlib

namespace PEqualNP.Outside

open scoped BigOperators

theorem L_goldbach_residue_blocks_unit_split :
    ∀ (q X : ℕ) (w : ℕ → ℂ), (∑ k ∈ Finset.range X,w k)=(∑ k ∈ (Finset.range X).filter (fun k => Nat.Coprime k q),w k)+(∑ k ∈ (Finset.range X).filter (fun k => ¬ Nat.Coprime k q),w k) := by
  intro q X w
  exact (Finset.sum_filter_add_sum_filter_not (Finset.range X)
    (fun k => Nat.Coprime k q) w).symm

end PEqualNP.Outside