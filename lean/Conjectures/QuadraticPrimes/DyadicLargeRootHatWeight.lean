import Mathlib

namespace Conjectures.QuadraticPrimes

/-- Count of the integer scales captured by the moving window: the integers `x` with
`Y ≤ x < 2Y`, `x < n` and `n ≤ 2x` form the half-open interval
`[max Y ((n+1)/2), min (2Y) n)`, whose cardinality in `ℕ` is
`min (2Y) n - max Y ((n+1)/2)` (truncated subtraction covers the empty case). -/
theorem DyadicLargeRootHatWeight :
    ∀ Y n : ℕ, ((Finset.Ico Y (2*Y)).filter fun x => x<n ∧ n≤2*x).card = min (2*Y) n - max Y ((n+1)/2) := by
  intro Y n
  have hset : (Finset.Ico Y (2*Y)).filter (fun x => x < n ∧ n ≤ 2*x) =
      Finset.Ico (max Y ((n+1)/2)) (min (2*Y) n) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [hset, Nat.card_Ico]

end Conjectures.QuadraticPrimes
