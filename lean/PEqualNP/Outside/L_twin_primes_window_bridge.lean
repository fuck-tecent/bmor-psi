import Mathlib
theorem PEqualNP.Outside.L_twin_primes_window_bridge : (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let E := fun (X : ℕ) => ((w X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum v / (X : ℝ); let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → E X ≤ C * e X) → (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let M := fun (X : ℕ) => (w X).sum v / (X : ℝ); let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X) → (∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧ (p+2).Prime) := by
  dsimp only
  rintro ⟨C, hC, hE⟩ hM B
  obtain ⟨X, hX, hlarge⟩ := hM C (max B 2)
  have hB : B < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hX2 : 2 ≤ X := le_trans (le_max_right _ _) (le_of_lt hX)
  have hbound := hE X hX2
  let w := (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)
  let v := fun n : ℕ => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)
  change C * (Real.log (2+(X:ℝ))^3 / Real.sqrt X) < w.sum v / (X:ℝ) at hlarge
  change (w.filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum v / (X:ℝ) ≤ C * (Real.log (2+(X:ℝ))^3 / Real.sqrt X) at hbound
  by_contra h
  have hfilter : w.filter (fun n => ¬ (n.Prime ∧ (n+2).Prime)) = w := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro hn
      refine ⟨hn, ?_⟩
      intro hp
      have hnX : X < n := (Finset.mem_filter.mp hn).2.1
      exact h ⟨n, lt_trans hB hnX, hp.1, hp.2⟩
  rw [hfilter] at hbound
  linarith

