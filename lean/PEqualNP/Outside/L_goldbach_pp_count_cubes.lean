import Mathlib

theorem PEqualNP.Outside.L_goldbach_pp_count_cubes :
    ∀ n : ℕ, let s := (Finset.range (n+1)).filter (fun p => p.Prime ∧ p^3≤n); s.card^3 ≤ n := by
  intro n
  let s := (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ^ 3 ≤ n)
  change s.card ^ 3 ≤ n
  by_cases hs : s.Nonempty
  · let M := s.max' hs
    have hM : M ∈ s := s.max'_mem hs
    have hbound : M ^ 3 ≤ n := (Finset.mem_filter.mp hM).2.2
    have hsub : s ⊆ Finset.Ioc 0 M := by
      intro p hp
      exact Finset.mem_Ioc.mpr ⟨(Finset.mem_filter.mp hp).2.1.pos, s.le_max' p hp⟩
    have hcard : s.card ≤ M := by simpa using Finset.card_le_card hsub
    exact (Nat.pow_le_pow_left hcard 3).trans hbound
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
