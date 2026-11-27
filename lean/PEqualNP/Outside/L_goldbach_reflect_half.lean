import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Basic.Real.Basic

theorem PEqualNP.Outside.L_goldbach_reflect_half :
    ∀ (n : ℕ) (w : ℕ → ℝ), (∑ k ∈ Finset.range (n+1), w k*w (n-k)) = 2*(∑ k ∈ (Finset.range (n+1)).filter (fun k => 2*k<n), w k*w (n-k)) + (if Even n then (w (n/2))^2 else 0) := by
  intro n w
  let left (k : ℕ) : ℝ := if 2 * k < n then w k * w (n - k) else 0
  let mid (k : ℕ) : ℝ := if 2 * k = n then (w k) ^ 2 else 0
  have split (k : ℕ) (hk : k ≤ n) :
      w k * w (n - k) = left k + left (n - k) + mid k := by
    have hrev : n - (n - k) = k := by omega
    rcases lt_trichotomy (2 * k) n with h | h | h
    · have hr : ¬ 2 * (n - k) < n := by omega
      simp [left, mid, h, hr, h.ne]
    · have heq : n - k = k := by omega
      simp [left, mid, heq, h, pow_two]
    · have hr : 2 * (n - k) < n := by omega
      simp [left, mid, hr, hrev, h.not_gt, h.ne']
      exact mul_comm _ _
  have midpoint : (∑ k ∈ Finset.range (n + 1), mid k) =
      (if Even n then (w (n / 2)) ^ 2 else 0) := by
    by_cases he : Even n
    · rw [ite_eq_left he]
      have hmod := Nat.even_iff.mp he
      have hmem : n / 2 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      have hmid (k : ℕ) : mid k = if k = n / 2 then (w k) ^ 2 else 0 := by
        have hiff : 2 * k = n ↔ k = n / 2 := by omega
        simp only [mid, hiff]
      simp [hmid, hmem]
    · rw [ite_eq_right he]
      apply Finset.sum_eq_zero
      intro k _
      have hne : 2 * k ≠ n := by
        intro h
        exact he ⟨k, by omega⟩
      simp [mid, hne]
  calc
    _ = ∑ k ∈ Finset.range (n + 1), (left k + left (n - k) + mid k) := by
      exact Finset.sum_congr rfl fun k hk => split k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [show (∑ k ∈ Finset.range (n + 1), left (n - k)) =
          ∑ k ∈ Finset.range (n + 1), left k from Finset.sum_range_reflect left (n + 1)]
      rw [midpoint, two_mul, Finset.sum_filter]
