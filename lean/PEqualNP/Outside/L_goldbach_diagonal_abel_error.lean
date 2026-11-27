import Mathlib

theorem PEqualNP.Outside.L_goldbach_diagonal_abel_error :
    let p := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let θ := fun n : ℕ => ∑ k ∈ Finset.range (n+1), p k; let g := fun (φ : ℝ → ℝ) (n k : ℕ) => Real.log (k:ℝ)*(φ ((k:ℝ)/n))^2; ∀ (φ : ℝ → ℝ) (n : ℕ), 1≤n → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → (∑ k ∈ Finset.Icc 1 n, (p k-1)*g φ n k) = - ∑ k ∈ Finset.range n, (θ k-(k:ℝ))*(g φ n (k+1)-g φ n k) := by
  intro p θ g φ n hn hφ
  have step (m : ℕ) : θ (m+1) = θ m + p (m+1) := Finset.sum_range_succ _ _
  have abel (m : ℕ) :
      (∑ k ∈ Finset.Icc 1 m, (p k-1) * g φ n k) =
        (θ m - (m:ℝ)) * g φ n m -
          ∑ k ∈ Finset.range m, (θ k - (k:ℝ)) * (g φ n (k+1) - g φ n k) := by
    induction m with
    | zero => simp [θ, p]
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih, step]
      push_cast
      ring
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hlast : g φ n n = 0 := by
    simp [g, hn0, hφ 1 (Or.inr (by norm_num))]
  simpa only [hlast, mul_zero, zero_sub] using abel n
