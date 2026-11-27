import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_residue_blocks_factor_phase :
    ∀ (q X : ℕ) (w u : ℕ → ℂ), 0 < q →
      (∑ k ∈ Finset.range X, w k * u (k % q)) =
        ∑ a ∈ Finset.range q, u a *
          (∑ k ∈ (Finset.range X).filter (fun k => k % q = a), w k) := by
  intro q X w u hq
  have hmod : ∀ k ∈ Finset.range X, k % q ∈ Finset.range q :=
    fun k _ => Finset.mem_range.mpr (Nat.mod_lt k hq)
  rw [← Finset.sum_fiberwise_of_maps_to hmod (fun k => w k * u (k % q))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [(Finset.mem_filter.mp hk).2, mul_comm]
