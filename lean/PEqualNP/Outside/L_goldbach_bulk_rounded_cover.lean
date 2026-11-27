import Mathlib

theorem PEqualNP.Outside.L_goldbach_bulk_rounded_cover :
    let J := fun x : ℕ => (Finset.range (2*x+1)).filter (fun n => Even n ∧ 13*x≤12*n ∧ 4*n≤5*x); ∃ S : Finset ℚ, (∀ r∈S, 0<r) ∧ ∃ X : ℕ, ∀ x≥X, ∀ n∈Finset.Icc x (2*x), Even n → ∃ r∈S, n∈J ⌊(r:ℝ)*(x:ℝ)⌋₊ := by
  dsimp only
  let S := (Finset.Icc 18 36).image (fun k : ℕ => (k : ℚ) / 20)
  refine ⟨S, ?_, 20, ?_⟩
  · intro r hr
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
    have hk' := (Finset.mem_Icc.mp hk).1
    positivity
  · intro x hx n hn heven
    obtain ⟨hxn, hnx⟩ := Finset.mem_Icc.mp hn
    have hxpos : 0 < x := by omega
    let k := 18 * n / x
    have hklo : 18 ≤ k := (Nat.le_div_iff_mul_le hxpos).2 (by omega)
    have hkhi : k < 37 := (Nat.div_lt_iff_lt_mul hxpos).2 (by omega)
    refine ⟨(k : ℚ) / 20, Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hklo, by omega⟩, rfl⟩, ?_⟩
    have hfloor : ⌊(((k : ℚ) / 20 : ℚ) : ℝ) * (x : ℝ)⌋₊ = k * x / 20 := by
      push_cast
      rw [div_mul_eq_mul_div, ← Nat.cast_mul]
      exact Nat.floor_div_eq_div (K := ℝ) (k * x) 20
    have hle : k * x ≤ 18 * n := Nat.div_mul_le_self _ _
    have hlt : 18 * n < k * x + x := by
      have h := (Nat.div_lt_iff_lt_mul hxpos).1 (Nat.lt_succ_self k)
      simpa [Nat.succ_mul] using h
    rw [hfloor, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, heven, by omega, by omega⟩
