import Mathlib

private theorem sum_units_81 (z : ℂ) (hz : IsPrimitiveRoot z 81) :
    (∑ b ∈ (Finset.range 81).filter (fun b => Nat.Coprime b 81), z ^ b) = 0 := by
  have nonunit (b : ℕ) : ¬ Nat.Coprime b 81 ↔ 3 ∣ b := by
    rw [show 81 = 3 ^ 4 by decide, Nat.coprime_pow_right_iff (by decide : 0 < 4),
      Nat.coprime_comm, (by decide : Nat.Prime 3).coprime_iff_not_dvd, not_not]
  -- The nonunits form a complete geometric sum at the primitive 27th root z³.
  have hnon : (∑ b ∈ (Finset.range 81).filter (fun b => ¬ Nat.Coprime b 81), z ^ b) =
      ∑ j ∈ Finset.range 27, (z ^ 3) ^ j := by
    symm
    apply Finset.sum_bij (fun j _ => 3 * j)
    · intro j hj
      have hj' := Finset.mem_range.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), (nonunit _).mpr ⟨j, rfl⟩⟩
    · intro i _ j _ hij
      omega
    · intro b hb
      obtain ⟨hbound, hnu⟩ := Finset.mem_filter.mp hb
      obtain ⟨j, rfl⟩ := (nonunit b).mp hnu
      have hj := Finset.mem_range.mp hbound
      exact ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
    · intro j _
      exact (pow_mul z 3 j).symm
  have hcube : IsPrimitiveRoot (z ^ 3) 27 := IsPrimitiveRoot.pow (by decide) hz (by decide)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range 81)
    (fun b => Nat.Coprime b 81) (fun b => z ^ b)
  simpa only [hnon, hcube.geom_sum_eq_zero (by decide), add_zero,
    hz.geom_sum_eq_zero (by decide)] using hsplit

theorem PEqualNP.Outside.L_goldbach_cert_81 :
    ∀ a:ℕ, Nat.Coprime a 81 → (∑ b ∈ (Finset.range 81).filter (fun b => Nat.Coprime b 81), Complex.exp (((2*Real.pi*(a:ℝ)*b/81:ℝ):ℂ)*Complex.I))/(54:ℂ)=(0:ℂ)/54 := by
  intro a ha
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 81)
  have hz : IsPrimitiveRoot (Complex.exp θ) 81 :=
    Complex.isPrimitiveRoot_exp_of_coprime a 81 (by decide) ha
  apply congrArg (fun s : ℂ => s / 54)
  calc
    _ = ∑ b ∈ (Finset.range 81).filter (fun b => Nat.Coprime b 81), (Complex.exp θ) ^ b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← Complex.exp_nat_mul]
      congr 1
      dsimp [θ]
      push_cast
      ring
    _ = 0 := sum_units_81 _ hz
