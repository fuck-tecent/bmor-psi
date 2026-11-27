import Mathlib

open Finset

theorem PEqualNP.Outside.L_goldbach_sampled_window_variation :
    ∀ (f : ℝ → ℝ) (L : ℝ), 0≤L → (∀ u ∈ Set.Icc (0:ℝ) 1, ∀ v ∈ Set.Icc (0:ℝ) 1, |f u-f v|≤L*|u-v|) → ∀ n : ℕ, 0<n → (∑ k ∈ Finset.range n, |f (((k+1:ℕ):ℝ)/n)-f ((k:ℝ)/n)|) ≤ L := by
  intro f L _ hL n hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ ∑ k ∈ range n, L*(1/(n:ℝ)) := by
      apply sum_le_sum
      intro k hk
      have hk' := mem_range.mp hk
      have inGrid (i : ℕ) (hi : i ≤ n) : (i:ℝ)/n ∈ Set.Icc (0:ℝ) 1 := by
        exact ⟨by positivity, (div_le_one hn').mpr (by exact_mod_cast hi)⟩
      apply (hL _ (inGrid (k+1) (by omega)) _ (inGrid k (by omega))).trans_eq
      rw [← sub_div, Nat.cast_add, Nat.cast_one, add_sub_cancel_left,
        abs_of_nonneg (by positivity : 0 ≤ 1/(n:ℝ))]
    _ = L := by simp; field_simp
