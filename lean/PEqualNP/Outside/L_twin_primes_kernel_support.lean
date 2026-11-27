import Mathlib
theorem PEqualNP.Outside.L_twin_primes_kernel_support : ∀ K : ℝ → ℝ, (∀ v, 1/20 ≤ |v| → K v = 0) → (∀ v, |v| < 1/20 → 0 < K v) → let H := fun (v : ℝ) => K v / 2 - K (v-1/5)/4 - K (v+1/5)/4; (∀ v, 1/4 ≤ |v| → H v = 0) ∧ (∀ v, |v| < 1/20 → 0 < H v) := by
  intro K hs hp
  dsimp only
  constructor
  · intro v hv
    have hv0 : K v = 0 := hs v (by linarith)
    have hv' : v ≤ -(1/4:ℝ) ∨ (1/4:ℝ) ≤ v := by
      rcases (le_abs).mp hv with h | h
      · exact Or.inr h
      · left; linarith
    have hvm : K (v-1/5)=0 := hs _ (by
      rcases hv' with h | h
      · rw [abs_of_nonpos (by linarith : v-1/5 ≤ 0)]; linarith
      · rw [abs_of_nonneg (by linarith : 0 ≤ v-1/5)]; linarith)
    have hvp : K (v+1/5)=0 := hs _ (by
      rcases hv' with h | h
      · rw [abs_of_nonpos (by linarith : v+1/5 ≤ 0)]; linarith
      · rw [abs_of_nonneg (by linarith : 0 ≤ v+1/5)]; linarith)
    norm_num at hvm hvp ⊢
    rw [hv0, hvm, hvp]
    norm_num
  · intro v hv
    have hvp := hp v hv
    have hvm : K (v-1/5)=0 := hs _ (by
      have h := abs_lt.mp hv
      rw [abs_of_nonpos (by linarith : v-1/5 ≤ 0)]
      linarith)
    have hvp2 : K (v+1/5)=0 := hs _ (by
      have h := abs_lt.mp hv
      rw [abs_of_nonneg (by linarith : 0 ≤ v+1/5)]
      linarith)
    rw [hvm, hvp2]
    linarith




