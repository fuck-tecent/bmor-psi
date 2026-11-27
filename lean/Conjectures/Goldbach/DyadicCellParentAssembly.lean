import Mathlib

noncomputable section

theorem Conjectures.Goldbach.DyadicCellParentAssembly :
  (let w := fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0; ∃ K : ℕ, ∀ k ≥ K, let n : ℕ := 2^k; let H : ℕ := 2^(k-k/4); ∀ x : ℕ, n ≤ 3*x → 3*x ≤ 2*n → (H:ℝ)/2 ≤ ∑ t ∈ Finset.range H, w (x+t)) → (let w := fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0; ∀ k : ℕ, 12 ≤ k → let n : ℕ := 2^k; let H : ℕ := 2^(k-k/4); let B : ℕ := 2^(k/4-3); let p := fun j t : ℕ => n/2+j*H+t; let a := fun j t : ℕ => w (p j t); let b := fun j t : ℕ => w (n-p j t); (∀ x : ℕ, n ≤ 3*x → 3*x ≤ 2*n → (H:ℝ)/2 ≤ ∑ t ∈ Finset.range H, w (x+t)) → (n:ℝ)/32 + (∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a j s-a j t)*(b j s-b j t)) / (2*(H:ℝ))) ≤ (∑ p ∈ (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n), w p * w (n-p))) → (let w := fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0; ∃ K : ℕ, ∀ k ≥ K, let n : ℕ := 2^k; let H : ℕ := 2^(k-k/4); let B : ℕ := 2^(k/4-3); let p := fun j t : ℕ => n/2+j*H+t; let a := fun j t : ℕ => w (p j t); let b := fun j t : ℕ => w (n-p j t); -(n:ℝ)/64 ≤ (∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a j s-a j t)*(b j s-b j t)) / (2*(H:ℝ)))) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0; ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, let n : ℕ := 2^k; c*(n : ℝ) ≤ ∑ p ∈ (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n), w p * w (n-p)) := by
  dsimp only
  rintro ⟨K₁,h₁⟩ h₂ ⟨K₃,h₃⟩
  refine ⟨1/64, by norm_num, max 12 (max K₁ K₃), ?_⟩
  intro k hk
  have hk12 : 12 ≤ k := le_trans (le_max_left _ _) hk
  have hk1 : K₁ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk3 : K₃ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have h := h₂ k hk12 (h₁ k hk1)
  have h' := h₃ k hk3
  linarith
