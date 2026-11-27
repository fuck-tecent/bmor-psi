import Mathlib

theorem Conjectures.Goldbach.AntispikeSharedCoefficientError :
    ∀ (n : ℕ) (a w : ℕ → ℝ) (δ T : ℝ), 0 ≤ δ → let s := Finset.Icc n (2 * n); ((∀ c : ℕ → ℝ, (∑ m ∈ s, (c m - a m) ^ 2) ≤ δ ^ 2 → (∑ m ∈ s, w m * c m) - c n ≤ T) ↔ (∑ m ∈ s, w m * a m) - a n + δ * Real.sqrt (1 - 2 * w n + ∑ m ∈ s, (w m) ^ 2) ≤ T) := by
  dsimp only
  intro n a w δ T hδ
  set s : Finset ℕ := Finset.Icc n (2 * n) with hs
  have hnn : n ∈ s := by
    rw [hs]
    simp only [Finset.mem_Icc]
    omega
  set v : ℕ → ℝ := fun m => w m - if m = n then 1 else 0 with hv
  have hvc : ∀ c : ℕ → ℝ, (∑ m ∈ s, v m * c m) = (∑ m ∈ s, w m * c m) - c n := by
    intro c
    have hexp : ∀ m : ℕ, (w m - (if m = n then 1 else 0)) * c m
        = w m * c m - (if m = n then 1 else 0) * c m := by
      intro m
      rw [sub_mul]
    simp only [hv, hexp]
    rw [Finset.sum_sub_distrib]
    congr 1
    have h2 : (∑ m ∈ s, (if m = n then 1 else 0) * c m) = (∑ m ∈ s, if m = n then c m else 0) := by
      apply Finset.sum_congr rfl
      intro m _
      by_cases hm : m = n
      · simp [hm]
      · simp [hm]
    rw [h2, Finset.sum_ite_eq' s n (fun m => c m), if_pos hnn]
  have hvv : (∑ m ∈ s, (v m) ^ 2) = 1 - 2 * w n + ∑ m ∈ s, (w m) ^ 2 := by
    have hexp : ∀ m : ℕ, (v m) ^ 2
        = (w m) ^ 2 - 2 * (if m = n then w m else 0) + (if m = n then 1 else 0) := by
      intro m
      simp only [hv]
      by_cases hm : m = n
      · simp [hm]
        ring
      · simp [hm]
    have h1 : (∑ m ∈ s, (if m = n then w m else 0)) = w n := by
      rw [Finset.sum_ite_eq' s n (fun m => w m), if_pos hnn]
    have h2 : (∑ m ∈ s, (if m = n then (1 : ℝ) else 0)) = 1 := by
      rw [Finset.sum_ite_eq' s n (fun _ => (1 : ℝ)), if_pos hnn]
    have h3 : (∑ m ∈ s, 2 * (if m = n then w m else 0)) = 2 * w n := by
      rw [← Finset.mul_sum, h1]
    simp only [hexp]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h3, h2]
    ring
  have key : (∀ c : ℕ → ℝ, (∑ m ∈ s, (c m - a m) ^ 2) ≤ δ ^ 2 → (∑ m ∈ s, v m * c m) ≤ T) ↔
      (∑ m ∈ s, v m * a m) + δ * Real.sqrt (∑ m ∈ s, (v m) ^ 2) ≤ T := by
    set B : ℝ := Real.sqrt (∑ m ∈ s, (v m) ^ 2) with hB
    have hB2 : B ^ 2 = ∑ m ∈ s, (v m) ^ 2 := by
      rw [hB]
      exact Real.sq_sqrt (Finset.sum_nonneg (fun m _ => sq_nonneg _))
    have hBnn : 0 ≤ B := by
      rw [hB]
      exact Real.sqrt_nonneg _
    have hzero : (∑ m ∈ s, (a m - a m) ^ 2) ≤ δ ^ 2 := by
      simpa using sq_nonneg δ
    constructor
    · intro H
      by_cases hdel : δ = 0
      · have hT := H a hzero
        simpa [hdel] using hT
      · have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hdel)
        by_cases hBz : B = 0
        · have hsum0 : (∑ m ∈ s, (v m) ^ 2) = 0 := by
            rw [← hB2, hBz]
            ring
          have hv0sq : ∀ m ∈ s, (v m) ^ 2 = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => sq_nonneg _)).mp hsum0
          have hv0 : ∀ m ∈ s, v m = 0 := by
            intro m hm
            have h := hv0sq m hm
            exact sq_eq_zero_iff.mp h
          have hva : (∑ m ∈ s, v m * a m) = 0 := by
            apply Finset.sum_eq_zero
            intro m hm
            rw [hv0 m hm]
            ring
          have hTa : (0 : ℝ) ≤ T := by
            have hT := H a hzero
            rwa [hva] at hT
          rw [hva, hBz]
          simpa using hTa
        · set c : ℕ → ℝ := fun m => a m + δ * v m / B with hc
          have hcsub : ∀ m : ℕ, c m - a m = δ * v m / B := by
            intro m
            simp [hc]
          have hEq : (∑ m ∈ s, (c m - a m) ^ 2) = δ ^ 2 := by
            calc (∑ m ∈ s, (c m - a m) ^ 2)
                = ∑ m ∈ s, (δ * v m / B) ^ 2 := by
                  apply Finset.sum_congr rfl
                  intro m _
                  rw [hcsub m]
              _ = (δ / B) ^ 2 * ∑ m ∈ s, (v m) ^ 2 := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro m _
                  field_simp [hBz]
              _ = (δ / B) ^ 2 * B ^ 2 := by
                  rw [← hB2]
              _ = δ ^ 2 := by
                  field_simp [hBz]
          have hball : (∑ m ∈ s, (c m - a m) ^ 2) ≤ δ ^ 2 := le_of_eq hEq
          have hHc := H c hball
          have hexp2 : ∀ m : ℕ, v m * c m = v m * a m + δ / B * (v m) ^ 2 := by
            intro m
            simp only [hc]
            field_simp [hBz]
          have hvc_eq : (∑ m ∈ s, v m * c m) = (∑ m ∈ s, v m * a m) + δ * B := by
            calc (∑ m ∈ s, v m * c m)
                = ∑ m ∈ s, (v m * a m + δ / B * (v m) ^ 2) := by
                  apply Finset.sum_congr rfl
                  intro m _
                  exact hexp2 m
              _ = (∑ m ∈ s, v m * a m) + ∑ m ∈ s, δ / B * (v m) ^ 2 := by
                  rw [Finset.sum_add_distrib]
              _ = (∑ m ∈ s, v m * a m) + δ / B * (∑ m ∈ s, (v m) ^ 2) := by
                  rw [Finset.mul_sum]
              _ = (∑ m ∈ s, v m * a m) + δ / B * B ^ 2 := by
                  rw [← hB2]
              _ = (∑ m ∈ s, v m * a m) + δ * B := by
                  field_simp [hBz]
          rw [hvc_eq] at hHc
          exact hHc
    · intro HR c hcbal
      have hCS : (∑ m ∈ s, v m * (c m - a m)) ^ 2
          ≤ (∑ m ∈ s, (v m) ^ 2) * (∑ m ∈ s, (c m - a m) ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq s v (fun m => c m - a m)
      have hBd : (∑ m ∈ s, v m * (c m - a m)) ≤ B * δ := by
        have hsq : (∑ m ∈ s, v m * (c m - a m)) ^ 2 ≤ (B * δ) ^ 2 := by
          calc (∑ m ∈ s, v m * (c m - a m)) ^ 2
              ≤ (∑ m ∈ s, (v m) ^ 2) * (∑ m ∈ s, (c m - a m) ^ 2) := hCS
            _ = B ^ 2 * (∑ m ∈ s, (c m - a m) ^ 2) := by
                rw [hB2]
            _ ≤ B ^ 2 * δ ^ 2 := by
                apply mul_le_mul_of_nonneg_left hcbal
                positivity
            _ = (B * δ) ^ 2 := by
                ring
        have habs := (sq_le_sq.mp hsq)
        have hBdnn : 0 ≤ B * δ := mul_nonneg hBnn hδ
        rw [abs_of_nonneg hBdnn] at habs
        exact le_trans (le_abs_self _) habs
      have hsplit : (∑ m ∈ s, v m * c m)
          = (∑ m ∈ s, v m * a m) + (∑ m ∈ s, v m * (c m - a m)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro m _
        ring
      rw [hsplit]
      linarith
  have A : (∀ c : ℕ → ℝ, (∑ m ∈ s, (c m - a m) ^ 2) ≤ δ ^ 2 → (∑ m ∈ s, w m * c m) - c n ≤ T) ↔
      (∀ c : ℕ → ℝ, (∑ m ∈ s, (c m - a m) ^ 2) ≤ δ ^ 2 → (∑ m ∈ s, v m * c m) ≤ T) := by
    constructor
    · intro H c hc
      rw [hvc c]
      exact H c hc
    · intro H c hc
      rw [← hvc c]
      exact H c hc
  have B' : ((∑ m ∈ s, w m * a m) - a n + δ * Real.sqrt (1 - 2 * w n + ∑ m ∈ s, (w m) ^ 2) ≤ T) ↔
      ((∑ m ∈ s, v m * a m) + δ * Real.sqrt (∑ m ∈ s, (v m) ^ 2) ≤ T) := by
    rw [← hvc a, ← hvv]
  rw [A, B']
  exact key
