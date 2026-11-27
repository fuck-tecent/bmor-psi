import Mathlib

theorem PEqualNP.Outside.L_goldbach_replacement_lone_linf :
    let conv := fun (u v : ℕ → ℝ) (n : ℕ) =>
      Finset.sum (Finset.range (n + 1)) (fun k => u k * v (n - k))
    ∀ (u v : ℕ → ℝ) (n : ℕ) (M : ℝ),
      (∀ k ≤ n, |u k| ≤ M ∧ |v k| ≤ M) →
      |conv u u n - conv v v n| ≤
        2 * M * Finset.sum (Finset.range (n + 1)) (fun k => |u k - v k|) := by
  dsimp only
  intro u v n M h
  let d : ℕ → ℝ := fun k => |u k - v k|
  have hreflect :
      (∑ k ∈ Finset.range (n + 1), d (n - k)) =
        ∑ k ∈ Finset.range (n + 1), d k := by
    simpa using Finset.sum_range_reflect d (n + 1)
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), |u k * u (n - k) - v k * v (n - k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), (M * d k + M * d (n - k)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hnk := Nat.sub_le n k
      calc
        _ = |(u k - v k) * u (n - k) + v k * (u (n - k) - v (n - k))| := by
          congr 1
          ring
        _ ≤ |(u k - v k) * u (n - k)| + |v k * (u (n - k) - v (n - k))| :=
          abs_add_le _ _
        _ ≤ M * d k + M * d (n - k) := by
          simp only [abs_mul, d]
          rw [mul_comm |u k - v k|]
          exact add_le_add
            (mul_le_mul_of_nonneg_right (h _ hnk).1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right (h _ hkn).2 (abs_nonneg _))
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hreflect]
      change _ = 2 * M * ∑ k ∈ Finset.range (n + 1), d k
      ring
