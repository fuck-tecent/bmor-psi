import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

noncomputable section

theorem L_goldbach_frontier_type2_b1_b1_widearcs_measurable :
    (let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2;
     let Q₁ := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊;
     let H := fun n : ℕ => 256 * Q₁ n * Q n;
     let wideArcs := fun n : ℕ =>
       {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q ∧
         |t - (a : ℝ) / (q : ℝ)| ≤ (H n : ℝ) / ((q : ℝ) * (n : ℝ))};
     ∀ n, MeasurableSet (wideArcs n)) := by
  dsimp only
  intro n
  have h : {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊) ∧ a ≤ q ∧
        Nat.Coprime a q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤
          ((256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) /
            ((q : ℝ) * (n : ℝ))} =
      ⋃ q : ℕ, ⋃ a : ℕ,
        {t : ℝ | 1 ≤ q ∧ q ≤ (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊) ∧ a ≤ q ∧
          Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤
            ((256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) /
              ((q : ℝ) * (n : ℝ))} := by
    ext t
    simp
  rw [h]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro a
  by_cases hq : 1 ≤ q ∧ q ≤ (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊) ∧ a ≤ q ∧ Nat.Coprime a q
  · have hq1 := hq.1
    have hq2 := hq.2.1
    have hq3 := hq.2.2.1
    have hq4 := hq.2.2.2
    have hset : {t : ℝ | 1 ≤ q ∧ q ≤ (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊) ∧ a ≤ q ∧
          Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤
            ((256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) /
              ((q : ℝ) * (n : ℝ))} =
        {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤
            ((256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) /
              ((q : ℝ) * (n : ℝ))} := by
      ext t
      constructor
      · intro ht
        exact ht.2.2.2.2
      · intro ht
        exact ⟨hq1, hq2, hq3, hq4, ht⟩
    rw [hset]
    have hIcc : {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤
          ((256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) /
            ((q : ℝ) * (n : ℝ))} =
        Set.Icc
          ((a : ℝ) / (q : ℝ) -
            ((256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) /
              ((q : ℝ) * (n : ℝ)))
          ((a : ℝ) / (q : ℝ) +
            ((256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) /
              ((q : ℝ) * (n : ℝ))) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · intro ht
        have h1 := (abs_le.mp ht).1
        have h2 := (abs_le.mp ht).2
        constructor <;> linarith
      · intro ht
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
    rw [hIcc]
    exact measurableSet_Icc
  · have hset : {t : ℝ | 1 ≤ q ∧ q ≤ (⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊) ∧ a ≤ q ∧
        Nat.Coprime a q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤
          ((256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) /
            ((q : ℝ) * (n : ℝ))} = ∅ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
      tauto
    rw [hset]
    exact MeasurableSet.empty

end

end PEqualNP.Outside
