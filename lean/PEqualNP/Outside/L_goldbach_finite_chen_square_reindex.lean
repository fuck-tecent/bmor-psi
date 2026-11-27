import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_finite_chen_square_reindex :
    let P := fun n : ℕ => (Finset.range (n+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (Nat.sqrt (n-p)) ∧ (Nat.sqrt (n-p))^2=n-p); ∀ (n : ℕ) (v : ℕ → ℝ), (∑ p ∈ P n, v p) = ∑ a ∈ (Finset.Icc 2 (Nat.sqrt n)).filter (fun a => Nat.Prime a ∧ Nat.Prime (n-a^2)), v (n-a^2) := by
  dsimp only
  intro n v
  -- On each filtered set the subtraction is exact, giving the two inverse maps.
  refine Finset.sum_bij' (fun p _ => Nat.sqrt (n - p)) (fun a _ => n - a ^ 2)
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hpRange, hpPrime, haPrime, haSq⟩ := Finset.mem_filter.mp hp
    have hpLe : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hpRange)
    have hBack : n - (Nat.sqrt (n - p)) ^ 2 = p := by omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨haPrime.two_le, Nat.sqrt_le_sqrt (Nat.sub_le n p)⟩,
        haPrime, by simpa only [hBack] using hpPrime⟩
  · intro a ha
    obtain ⟨haRange, haPrime, hpPrime⟩ := Finset.mem_filter.mp ha
    have haSqLe : a ^ 2 ≤ n := Nat.le_sqrt'.mp (Finset.mem_Icc.mp haRange).2
    have hBack : n - (n - a ^ 2) = a ^ 2 := by omega
    rw [Finset.mem_filter, hBack, Nat.sqrt_eq']
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _)), hpPrime, haPrime, rfl⟩
  · intro p hp
    obtain ⟨hpRange, _, _, haSq⟩ := Finset.mem_filter.mp hp
    have hpLe : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hpRange)
    omega
  · intro a ha
    have haSqLe : a ^ 2 ≤ n := Nat.le_sqrt'.mp (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
    have hBack : n - (n - a ^ 2) = a ^ 2 := by omega
    rw [hBack, Nat.sqrt_eq']
  · intro p hp
    obtain ⟨hpRange, _, _, haSq⟩ := Finset.mem_filter.mp hp
    have hpLe : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hpRange)
    exact congrArg v (by omega)
