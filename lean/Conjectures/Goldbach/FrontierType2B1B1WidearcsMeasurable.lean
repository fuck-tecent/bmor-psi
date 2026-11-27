import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.FrontierType2B1B1WidearcsMeasurable :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2
    let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
    let H := fun n : ℕ => 256 * Q₁ n * Q n
    let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}
    ∀ n, MeasurableSet (wideArcs n) := by
  intro Q Q₁ H wideArcs n
  have hset : wideArcs n = ⋃ q : ℕ, ⋃ a : ℕ,
      {t : ℝ | 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧
        |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))} := by
    ext t
    simp only [wideArcs, Set.mem_iUnion, Set.mem_setOf_eq]
  rw [hset]
  refine MeasurableSet.iUnion (fun q => MeasurableSet.iUnion (fun a => ?_))
  by_cases h : 1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q
  · have heq : {t : ℝ | 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧
        |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}
        = Set.Icc ((a:ℝ)/(q:ℝ) - (H n:ℝ)/((q:ℝ)*(n:ℝ)))
            ((a:ℝ)/(q:ℝ) + (H n:ℝ)/((q:ℝ)*(n:ℝ))) := by
      ext t
      constructor
      · intro ht
        obtain ⟨-, -, -, -, habs⟩ := ht
        obtain ⟨h1, h2⟩ := abs_le.mp habs
        exact ⟨by linarith, by linarith⟩
      · intro ht
        rw [Set.mem_Icc] at ht
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2,
          abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
    rw [heq]
    exact measurableSet_Icc
  · have heq : {t : ℝ | 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧
        |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))} = ∅ := by
      ext t
      constructor
      · intro ht
        exact h ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩
      · intro ht
        exact absurd ht (by simp)
    rw [heq]
    exact MeasurableSet.empty
