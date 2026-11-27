import Mathlib

theorem Conjectures.Goldbach.Type2CornerWideArcsClosed :
    let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; ∀ n : ℕ, IsClosed (wideArcs n) := by

  intro Q₁ Q H wideArcs n
  have hset : wideArcs n =
      ⋃ q ∈ Finset.Icc 1 (Q₁ n),
        ⋃ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
          Set.Icc ((a : ℝ) / (q : ℝ) - (H n : ℝ) / ((q : ℝ) * (n : ℝ)))
            ((a : ℝ) / (q : ℝ) + (H n : ℝ) / ((q : ℝ) * (n : ℝ))) := by
    ext t
    dsimp only [wideArcs]
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Icc, Finset.mem_Icc, Finset.mem_range,
      Finset.mem_filter, exists_prop, Nat.lt_succ_iff]
    constructor
    · rintro ⟨q, a, h1, h2, h3, hc, habs⟩
      refine ⟨q, ⟨h1, h2⟩, a, ⟨h3, hc⟩, ?_⟩
      rw [abs_le] at habs
      exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
    · rintro ⟨q, ⟨h1, h2⟩, a, ⟨h3, hc⟩, ht1, ht2⟩
      refine ⟨q, a, h1, h2, h3, hc, ?_⟩
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
  rw [hset]
  exact isClosed_biUnion_finset (fun q hq => isClosed_biUnion_finset (fun a ha => isClosed_Icc))
