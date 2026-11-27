import Mathlib

theorem PEqualNP.Outside.L_goldbach_exception_main_deficit : let reps := fun n : ℕ => (Finset.range (n+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n-p)); let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let conv := fun (u v : ℕ → ℝ) (n : ℕ) => Finset.sum (Finset.range (n+1)) (fun k => u k*v (n-k)); let D := fun X : ℕ => (Finset.Ico X (2*X)).filter (fun n => 4 ≤ n ∧ Even n); let bad := fun X : ℕ => (D X).filter (fun n => (reps n).card=0); ∀ (X : ℕ) (m : ℕ → ℝ) (c : ℝ), (∀ n ∈ D X, c*(X:ℝ) ≤ m n) → ∀ n ∈ bad X, c*(X:ℝ) ≤ |conv w w n-m n| := by
  dsimp only
  intro X m c hmodel n hn
  have hnd := (Finset.mem_filter.mp hn).1
  have he := Finset.card_eq_zero.mp (Finset.mem_filter.mp hn).2
  have hsum : (∑ k ∈ Finset.range (n + 1),
      (if Nat.Prime k then Real.log (k : ℝ) else 0) *
        (if Nat.Prime (n - k) then Real.log ((n - k : ℕ) : ℝ) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hp : Nat.Prime k
    · have hq : ¬ Nat.Prime (n - k) := by
        intro hq
        have hmem : k ∈ (Finset.range (n + 1)).filter
            (fun p => Nat.Prime p ∧ Nat.Prime (n - p)) := Finset.mem_filter.mpr ⟨hk, hp, hq⟩
        simp [he] at hmem
      simp [hq]
    · simp [hp]
  rw [hsum, zero_sub, abs_neg]
  exact (hmodel n hnd).trans (le_abs_self _)
