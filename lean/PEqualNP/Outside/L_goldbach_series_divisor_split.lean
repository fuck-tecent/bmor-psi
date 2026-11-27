import Mathlib

theorem PEqualNP.Outside.L_goldbach_series_divisor_split : let fac := fun p n : ℕ => if p ∣ n then (p:ℝ)/((p:ℝ)-1) else 1-1/((p:ℝ)-1)^2; let P := fun Q : ℕ => (Finset.range (Q+1)).filter (fun p => Nat.Prime p ∧ 2<p); ∀ Q n, Finset.prod (P Q) (fun p => fac p n) = Finset.prod (P Q) (fun p => 1-1/((p:ℝ)-1)^2) * Finset.prod ((P Q).filter (fun p => p ∣ n)) (fun p => ((p:ℝ)-1)/((p:ℝ)-2)) := by
  dsimp only
  intro Q n
  rw [Finset.prod_filter (fun p : ℕ => p ∣ n), ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have h : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.2
  by_cases hd : p ∣ n
  · simp only [hd, ite_true]
    field_simp [show (p:ℝ)-1 ≠ 0 by linarith, show (p:ℝ)-2 ≠ 0 by linarith]
    ring
  · simp [hd]
