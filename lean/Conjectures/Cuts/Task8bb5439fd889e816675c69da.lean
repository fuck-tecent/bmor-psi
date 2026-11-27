import Mathlib

theorem Conjectures.Cuts.Task8bb5439fd889e816675c69da :
    ∀ (x1 : ℕ),   (200 : ℕ) ≤ x1 →     ∀ (x3 : ℕ),       x1 < x3 →         x3 ≤ (2 : ℕ) * x1 →           ∃ x6 < (201 : ℕ),             have x7 : ℕ := Min.min ((2 : ℕ) * x1) (x1 + x1 / (100 : ℕ) * x6);             x7 < x3 ∧ (50 : ℕ) * x3 < (51 : ℕ) * x7 := by
  intro X hX n hXn hn
  let d := X/100
  let s := n-X-1
  let k := s/d
  have hd : 0 < d := by dsimp [d]; omega
  have hk : k < 201 := (Nat.div_lt_iff_lt_mul hd).mpr (by dsimp [s,d]; omega)
  have hLower : d*k ≤ s := by
    simpa only [k, Nat.mul_comm] using Nat.div_mul_le_self s d
  have hUpper : s < d*k+d := by
    have h : s < (k+1)*d :=
      (Nat.div_lt_iff_lt_mul hd).mp (by dsimp [k]; omega)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm k d] at h
    exact h
  have hShift : s+X+1 = n := by dsimp [s]; omega
  have hHundred : 100*d ≤ X := by
    simpa only [d, Nat.mul_comm] using Nat.div_mul_le_self X 100
  have hYn : X+d*k < n := by omega
  have hYCut : X+d*k ≤ 2*X := hYn.le.trans hn
  refine ⟨k, hk, ?_⟩
  change min (2*X) (X+d*k) < n ∧ 50*n < 51*min (2*X) (X+d*k)
  rw [min_eq_right hYCut]
  exact ⟨hYn, by omega⟩
