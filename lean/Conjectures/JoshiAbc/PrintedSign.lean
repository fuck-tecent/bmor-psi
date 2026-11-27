import Mathlib

theorem Conjectures.JoshiAbc.PrintedSign :
    ∀ (n : ℕ) (a : Fin (n+1) → ℝ) (m V : ℝ), 0 < m → (∀ i, 0 < a i ∧ a i < 1) → -|V|/m < -∑ i, Real.log (a i) := by
  intro n a m V hm ha
  have hsum : (∑ i, Real.log (a i)) < 0 := by
    simpa using
      (Finset.sum_neg (s := (Finset.univ : Finset (Fin (n + 1))))
        (fun i _ => Real.log_neg (ha i).1 (ha i).2) Finset.univ_nonempty)
  have hleft : -|V| / m ≤ 0 := by
    have hdiv : 0 ≤ |V| / m := div_nonneg (abs_nonneg V) hm.le
    calc
      -|V| / m = -(|V| / m) := by ring
      _ ≤ 0 := neg_nonpos.mpr hdiv
  linarith
