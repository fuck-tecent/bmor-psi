import Mathlib

theorem PEqualNP.Outside.L_twin_primes_window_extraction :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X);
    let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2);
    let M := fun (X : ℕ) => (w X).sum v / (X : ℝ);
    let E := fun (X : ℕ) => ((w X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum v / (X : ℝ);
    ∀ X : ℕ, 0 < X → E X < M X → ∃ n ∈ w X, n.Prime ∧ (n+2).Prime := by
  intro w v M E X _ hsurplus
  by_contra hnone
  have hall : (w X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime)) = w X :=
    Finset.filter_eq_self.mpr fun n hn hpair => hnone ⟨n, hn, hpair⟩
  have heq : E X = M X := by
    dsimp only [E, M]
    rw [hall]
  exact (ne_of_lt hsurplus) heq
