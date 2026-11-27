import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_pair_errors_minor_margin :
    let C := fun (a b : ℕ → ℝ) (n : ℕ) => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)
    ∀ a e n (B D : ℝ), -B ≤ C a e n → -D ≤ C e e n →
      2 * B + D < C a a n → 0 < C (fun k => a k + e k) (fun k => a k + e k) n := by
  dsimp only
  intro a e n B D hcross herr hmain
  have hswap :
      (∑ k ∈ Finset.range (n + 1), e k * a (n - k)) =
        ∑ k ∈ Finset.range (n + 1), a k * e (n - k) := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1), a (n - k) * e (n - (n - k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        have h : n - (n - k) = k := by omega
        rw [h, mul_comm]
      _ = _ := by
        simpa using (Finset.sum_range_reflect (fun k => a k * e (n - k)) (n + 1))
  have hexpand :
      (∑ k ∈ Finset.range (n + 1), (a k + e k) * (a (n - k) + e (n - k))) =
        (∑ k ∈ Finset.range (n + 1), a k * a (n - k)) +
          (∑ k ∈ Finset.range (n + 1), a k * e (n - k)) +
          (∑ k ∈ Finset.range (n + 1), e k * a (n - k)) +
          (∑ k ∈ Finset.range (n + 1), e k * e (n - k)) := by
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hexpand, hswap]
  linarith
