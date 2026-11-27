import Mathlib

theorem PEqualNP.Outside.L_goldbach_abel_total_variation :
    ∀ (N : ℕ) (A g : ℕ → ℂ) (e : ℝ), A 0=0 → (∀ k≤N, ‖A k‖≤e) → ‖Finset.sum (Finset.range N) (fun k => (A (k+1)-A k)*g k)‖ ≤ e*(‖g N‖+Finset.sum (Finset.range N) (fun k => ‖g (k+1)-g k‖)) := by
  intro N A g e hzero hbound
  let correction (k : ℕ) := A (k + 1) * (g (k + 1) - g k)
  have abel (n : ℕ) :
      ∑ k ∈ Finset.range n, (A (k + 1) - A k) * g k =
        A n * g n - ∑ k ∈ Finset.range n, correction k := by
    induction n with
    | zero => simp [hzero]
    | succ n ih =>
      simp only [Finset.sum_range_succ, ih, correction]
      ring
  have hvar : ‖∑ k ∈ Finset.range N, correction k‖ ≤
      e * ∑ k ∈ Finset.range N, ‖g (k + 1) - g k‖ := by
    calc
      ‖∑ k ∈ Finset.range N, correction k‖ ≤
          ∑ k ∈ Finset.range N, ‖correction k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range N, e * ‖g (k + 1) - g k‖ := by
        apply Finset.sum_le_sum
        intro k hk
        have hkN : k + 1 ≤ N := Finset.mem_range.mp hk
        simpa only [correction, norm_mul] using
          mul_le_mul_of_nonneg_right (hbound (k + 1) hkN) (norm_nonneg (g (k + 1) - g k))
      _ = _ := by rw [Finset.mul_sum]
  rw [abel N, mul_add]
  refine (norm_sub_le _ _).trans (add_le_add ?_ hvar)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound N le_rfl) (norm_nonneg (g N))
