import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_143 :
    ∀ a:ℕ, Nat.Coprime a 143 → (∑ b ∈ (Finset.range 143).filter (fun b => Nat.Coprime b 143), Complex.exp (((2*Real.pi*(a:ℝ)*b/143:ℝ):ℂ)*Complex.I))/(120:ℂ)=(1:ℂ)/120 := by
  intro a ha
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 143)
  let z := Complex.exp θ
  have hroot : IsPrimitiveRoot z 143 := by
    simpa [z, θ] using Complex.isPrimitiveRoot_exp_of_coprime a 143 (by decide) ha
  have hphase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 143 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    dsimp [z]
    rw [← Complex.exp_nat_mul]
    apply congrArg Complex.exp
    push_cast
    dsimp [θ]
    ring
  -- Multiplication by p indexes all multiples of p in the original range.
  have multiples (p q : ℕ) (hp : 0 < p) :
      (∑ b ∈ Finset.range (p * q), if p ∣ b then z ^ b else 0) =
        ∑ k ∈ Finset.range q, (z ^ p) ^ k := by
    rw [← Finset.sum_filter]
    symm
    apply Finset.sum_nbij' (p * ·) (· / p)
    · intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        ((Nat.mul_lt_mul_left hp).mpr (Finset.mem_range.mp hk)), Nat.dvd_mul_right p k⟩
    · intro b hb
      apply Finset.mem_range.mpr ∘ (Nat.div_lt_iff_lt_mul hp).mpr
      simpa [Nat.mul_comm] using Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    · exact fun k _ => Nat.mul_div_cancel_left k hp
    · exact fun b hb => Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2
    · exact fun k _ => (pow_mul z p k).symm
  have hunits (b : ℕ) : Nat.Coprime b 143 ↔ ¬ 11 ∣ b ∧ ¬ 13 ∣ b := by
    change b.Coprime (11 * 13) ↔ _
    rw [Nat.coprime_mul_iff_right, (@Nat.coprime_comm b 11), (@Nat.coprime_comm b 13),
      (by decide : Nat.Prime 11).coprime_iff_not_dvd, (by decide : Nat.Prime 13).coprime_iff_not_dvd]
  have hboth (b : ℕ) : 143 ∣ b ↔ 11 ∣ b ∧ 13 ∣ b := by
    exact ⟨fun h => ⟨dvd_trans (by decide : 11 ∣ 143) h, dvd_trans (by decide : 13 ∣ 143) h⟩,
      fun ⟨h, k⟩ => (by decide : Nat.Coprime 11 13).mul_dvd_of_dvd_of_dvd h k⟩
  have inclusion (b : ℕ) : (if b.Coprime 143 then z ^ b else 0) =
      z ^ b - (if 11 ∣ b then z ^ b else 0) - (if 13 ∣ b then z ^ b else 0) +
        (if 143 ∣ b then z ^ b else 0) := by
    simp_rw [hunits, hboth]
    by_cases h : 11 ∣ b <;> by_cases k : 13 ∣ b <;> simp [h, k]
  have root13 : IsPrimitiveRoot (z ^ 11) 13 := IsPrimitiveRoot.pow (by decide) hroot rfl
  have root11 : IsPrimitiveRoot (z ^ 13) 11 := IsPrimitiveRoot.pow (by decide) hroot rfl
  apply congrArg (fun s : ℂ => s / 120)
  simp_rw [hphase]
  rw [Finset.sum_filter]
  simp_rw [inclusion]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    hroot.geom_sum_eq_zero (by decide), multiples 11 13 (by decide),
    multiples 13 11 (by decide), multiples 143 1 (by decide),
    root13.geom_sum_eq_zero (by decide), root11.geom_sum_eq_zero (by decide)]
  simp
