import Mathlib

theorem PEqualNP.Outside.L_goldbach_mellin_tail_binning :
    let Z := fun (m k : ℕ) (γ : Fin m → ℝ) => Finset.univ.filter (fun j => (k:ℝ) ≤ |γ j| ∧ |γ j| < (k+1:ℕ)); ∀ (m H B : ℕ) (γ : Fin m → ℝ) (f : Fin m → ℝ), (∀ i, |γ i| < (B+1:ℕ)) → (∑ i ∈ Finset.univ.filter (fun i => (H:ℝ)≤|γ i|), f i) = ∑ k ∈ Finset.Icc H B, ∑ i ∈ Z m k γ, f i := by
  intro Z m H B γ f hB
  let S := Finset.univ.filter (fun i : Fin m => (H:ℝ) ≤ |γ i|)
  let bin (i : Fin m) := ⌊|γ i|⌋₊
  have maps (i : Fin m) (hi : i ∈ S) : bin i ∈ Finset.Icc H B := by
    have lower : (H:ℝ) ≤ |γ i| := (Finset.mem_filter.mp hi).2
    have upper : bin i < B+1 := (Nat.floor_lt (abs_nonneg (γ i))).mpr (hB i)
    exact Finset.mem_Icc.mpr ⟨Nat.le_floor lower, by omega⟩
  change (∑ i ∈ S, f i) = _
  rw [← Finset.sum_fiberwise_of_maps_to maps f]
  apply Finset.sum_congr rfl
  intro k hk
  have hHk : (H:ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have fiber : S.filter (fun i => bin i = k) = Z m k γ := by
    ext i
    simp only [S, Z, Finset.mem_filter, Finset.mem_univ, true_and,
      bin, Nat.floor_eq_iff (abs_nonneg (γ i)), Nat.cast_add, Nat.cast_one]
    exact ⟨And.right, fun h => ⟨hHk.trans h.1, h⟩⟩
  rw [fiber]
