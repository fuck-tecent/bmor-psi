import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

def Qs (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2
def Qcut (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
def Hwide (n : ℕ) : ℕ := 256 * Qcut n * Qs n
def wideArcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qcut n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a:ℝ)/(q:ℝ)| ≤ (Hwide n:ℝ)/((q:ℝ)*(n:ℝ))}

/-- Membership in the wide arcs, in the arc-family form used by the integral
expansion. -/
lemma mem_wideArcs_iff (n : ℕ) (t : ℝ) :
    t ∈ wideArcs n ↔
      ∃ q ∈ Finset.Icc 1 (Qcut n),
        ∃ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
          |t - (a:ℝ)/(q:ℝ)| ≤ (Hwide n:ℝ)/((q:ℝ)*(n:ℝ)) := by
  simp only [wideArcs, Set.mem_setOf_eq, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨q, a, hq1, hqQ, haq, hcop, hle⟩
    exact ⟨q, ⟨hq1, hqQ⟩, a, ⟨by omega, hcop⟩, hle⟩
  · rintro ⟨q, ⟨hq1, hqQ⟩, a, ⟨haq, hcop⟩, hle⟩
    exact ⟨q, a, hq1, hqQ, by omega, hcop, hle⟩

end B1B1
