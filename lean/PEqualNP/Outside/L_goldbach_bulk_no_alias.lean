import Mathlib

theorem PEqualNP.Outside.L_goldbach_bulk_no_alias :
    ∀ (x n : ℕ) (w : ℕ → ℝ), n≤2*x → (∑ p ∈ Finset.range (x+1), ∑ q ∈ Finset.range (x+1), if (p+q)%(2*x+1)=n then w p*w q else 0) = ∑ p ∈ (Finset.range (x+1)).filter (fun p => p≤n ∧ n-p≤x), w p*w (n-p) := by
  intro x n w _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hpBound := Finset.mem_range.mp hp
  have nowrap (q : ℕ) (hq : q ∈ Finset.range (x + 1)) :
      (p + q) % (2 * x + 1) = p + q := by
    have hqBound := Finset.mem_range.mp hq
    exact Nat.mod_eq_of_lt (by omega)
  by_cases h : p ≤ n ∧ n - p ≤ x
  · have hmem : n - p ∈ Finset.range (x + 1) := Finset.mem_range.mpr (by omega)
    rw [ite_eq_left h, Finset.sum_eq_single_of_mem (n - p) hmem]
    · rw [nowrap _ hmem, ite_eq_left (by omega)]
    · intro q hq hne
      rw [nowrap _ hq, ite_eq_right (by omega)]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro q hq
    have hqBound := Finset.mem_range.mp hq
    rw [nowrap _ hq, ite_eq_right (by omega)]
