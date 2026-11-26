import Mathlib

set_option autoImplicit false

namespace PEqualNP.Outside

noncomputable section

/-- The Bombieri–Vinogradov distribution-level statement with denominator range
`q ≤ floor (X ^ θ)`. `θ = 1/2` is the classical theorem; `θ = 3/5` is the
catalogue's open frontier target. -/
def BVLevel (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ (C : ℝ) (X₀ : ℕ), 0 < C ∧
    ∀ X : ℕ, X₀ ≤ X → ∃ B : ℕ → ℝ,
      (∀ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ θ⌋₊, ∀ a : ℕ, Nat.Coprime a q →
        |(∑ k ∈ (Finset.Icc 1 X).filter (fun k => k % q = a % q),
            ArithmeticFunction.vonMangoldt k) -
          (X : ℝ) / (Nat.totient q : ℝ)| ≤ B q) ∧
      (∑ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ θ⌋₊, B q) ≤
        C * (X : ℝ) / (Real.log (X : ℝ)) ^ A

theorem bv_three_fifths_target_iff :
    BVLevel (3 / 5 : ℝ) ↔
      (∀ A : ℝ, 0 < A → ∃ (C : ℝ) (X₀ : ℕ), 0 < C ∧
        ∀ X : ℕ, X₀ ≤ X → ∃ B : ℕ → ℝ,
          (∀ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ (3 / 5 : ℝ)⌋₊, ∀ a : ℕ, Nat.Coprime a q →
            |(∑ k ∈ (Finset.Icc 1 X).filter (fun k => k % q = a % q),
                ArithmeticFunction.vonMangoldt k) -
              (X : ℝ) / (Nat.totient q : ℝ)| ≤ B q) ∧
          (∑ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ (3 / 5 : ℝ)⌋₊, B q) ≤
            C * (X : ℝ) / (Real.log (X : ℝ)) ^ A) := Iff.rfl

end

end PEqualNP.Outside

/-- The classical Bombieri–Vinogradov level-1/2 statement, stated but not proved here. -/
example : Prop := PEqualNP.Outside.BVLevel (1 / 2 : ℝ)
