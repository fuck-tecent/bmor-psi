import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_mid_compatible :
    let w := fun (n p : ℕ) => (((n^2+1).factorization p : ℕ) : ℝ) * Real.log (p:ℝ);
    let middle := fun (x : ℕ) => Finset.sum (Finset.Ioc x (2*x)) (fun n => Finset.sum ((n^2+1).primeFactors.filter (fun p => x < p ∧ p^100000 ≤ n^132301)) (w n));
    let band := fun (x:ℕ) (first:Bool) => Finset.sum (Finset.Ioc x (2*x)) (fun n => Finset.sum ((n^2+1).primeFactors.filter (fun p => x<p ∧ p^100000≤n^132301 ∧ (if first then p^20≤n^23 else n^23<p^20))) (w n));
    ∀ a b:ℝ,a+b<1 → (∃ X:ℕ,∀ x≥X,band x true≤a*x*Real.log (x:ℝ)) → (∀ B:ℕ,∃ x>B,band x false≤b*x*Real.log (x:ℝ)) → ∃ d : ℝ, 0 < d ∧ ∀ B : ℕ, ∃ x : ℕ, B < x ∧ middle x ≤ (1-d)*(x:ℝ)*Real.log (x:ℝ) := by
  classical
  dsimp only
  intro a b hab hlo hhi
  obtain ⟨X, hX⟩ := hlo
  refine ⟨1 - (a + b), sub_pos.mpr hab, ?_⟩
  intro B
  obtain ⟨x, hx, hu⟩ := hhi (max B X)
  have hl := hX x (le_trans (le_max_right B X) hx.le)
  refine ⟨x, lt_of_le_of_lt (le_max_left B X) hx, ?_⟩
  have hcoeff : (1 - (1 - (a + b))) * (x : ℝ) * Real.log (x : ℝ) =
      a * (x : ℝ) * Real.log (x : ℝ) + b * (x : ℝ) * Real.log (x : ℝ) := by ring
  rw [hcoeff]
  refine le_trans (le_of_eq ?_) (add_le_add hl hu)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rcases le_or_gt (p ^ 20) (n ^ 23) with h | h
  · simp [h, not_lt_of_ge h]
  · simp [h, not_le_of_gt h]
