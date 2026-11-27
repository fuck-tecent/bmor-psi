import Mathlib

theorem Conjectures.Goldbach.PrimeModFourPartition :
    ∀ (f : ℕ → ℝ), (∀ k : ℕ, ¬ k.Prime → f k = 0) → ∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), f k) = (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % 4 = 1), f k) + (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % 4 = 3), f k) + (if 2 ≤ n then f 2 else 0) := by
  intro f hf n
  have hpt : ∀ k : ℕ, f k =
      (if k % 4 = 1 then f k else 0) + (if k % 4 = 3 then f k else 0)
        + (if k = 2 then f k else 0) := by
    intro k
    by_cases hk : k.Prime
    · rcases hk.eq_two_or_odd with h2 | hodd
      · subst h2
        norm_num
      · have hres := Nat.odd_mod_four_iff.mp hodd
        rcases hres with h1 | h3
        · rw [if_pos h1, if_neg (by rw [h1]; norm_num),
            if_neg (by rintro rfl; norm_num at hodd)]
          ring
        · rw [if_neg (by rw [h3]; norm_num), if_pos h3,
            if_neg (by rintro rfl; norm_num at h3)]
          ring
    · have hf0 : f k = 0 := hf k hk
      simp [hf0]
  have hlast : (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k = 2), f k)
      = if 2 ≤ n then f 2 else 0 := by
    by_cases h2n : 2 ≤ n
    · have hmem : (2 : ℕ) ∈ Finset.range (n + 1) := by
        simp [Finset.mem_range]
        omega
      rw [Finset.filter_eq' (Finset.range (n + 1)) 2, if_pos hmem,
        Finset.sum_singleton, if_pos h2n]
    · have hmem : (2 : ℕ) ∉ Finset.range (n + 1) := by
        simp [Finset.mem_range]
        omega
      rw [Finset.filter_eq' (Finset.range (n + 1)) 2, if_neg hmem, if_neg h2n]
      simp
  have hsum : (∑ k ∈ Finset.range (n + 1), f k)
      = ∑ k ∈ Finset.range (n + 1),
          ((if k % 4 = 1 then f k else 0) + (if k % 4 = 3 then f k else 0)
            + (if k = 2 then f k else 0)) := by
    exact Finset.sum_congr rfl (fun k _ => hpt k)
  rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.sum_filter]
  rw [hlast]
