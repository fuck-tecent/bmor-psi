import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_102 :
    ∀ a:ℕ, Nat.Coprime a 102 → (∑ b ∈ (Finset.range 102).filter (fun b => Nat.Coprime b 102), Complex.exp (((2*Real.pi*(a:ℝ)*b/102:ℝ):ℂ)*Complex.I))/(32:ℂ)=(-1:ℂ)/32 := by
  intro a ha
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 102)
  let z := Complex.exp θ
  have hroot : IsPrimitiveRoot z 102 := by
    simpa [z, θ] using Complex.isPrimitiveRoot_exp_of_coprime a 102 (by decide) ha
  have hphase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 102 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    dsimp [z]
    rw [← Complex.exp_nat_mul]
    apply congrArg Complex.exp
    push_cast
    dsimp [θ]
    ring
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
  have units (b : ℕ) : b.Coprime 102 ↔ ¬ 2 ∣ b ∧ ¬ 3 ∣ b ∧ ¬ 17 ∣ b := by
    change b.Coprime (2 * 3 * 17) ↔ _
    simp only [Nat.coprime_mul_iff_right,
      (@Nat.coprime_comm b 2),
      (@Nat.coprime_comm b 3),
      (@Nat.coprime_comm b 17),
      (by decide : Nat.Prime 2).coprime_iff_not_dvd,
      (by decide : Nat.Prime 3).coprime_iff_not_dvd,
      (by decide : Nat.Prime 17).coprime_iff_not_dvd,
      and_assoc]
  have dvd6 (b : ℕ) : 6 ∣ b ↔ 2 ∣ b ∧ 3 ∣ b :=
    ⟨fun h => ⟨dvd_trans (by decide : 2 ∣ 6) h, dvd_trans (by decide : 3 ∣ 6) h⟩,
      fun ⟨h, k⟩ => (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h k⟩
  have dvd34 (b : ℕ) : 34 ∣ b ↔ 2 ∣ b ∧ 17 ∣ b :=
    ⟨fun h => ⟨dvd_trans (by decide : 2 ∣ 34) h, dvd_trans (by decide : 17 ∣ 34) h⟩,
      fun ⟨h, k⟩ => (by decide : Nat.Coprime 2 17).mul_dvd_of_dvd_of_dvd h k⟩
  have dvd51 (b : ℕ) : 51 ∣ b ↔ 3 ∣ b ∧ 17 ∣ b :=
    ⟨fun h => ⟨dvd_trans (by decide : 3 ∣ 51) h, dvd_trans (by decide : 17 ∣ 51) h⟩,
      fun ⟨h, k⟩ => (by decide : Nat.Coprime 3 17).mul_dvd_of_dvd_of_dvd h k⟩
  have dvd102 (b : ℕ) : 102 ∣ b ↔ 6 ∣ b ∧ 17 ∣ b :=
    ⟨fun h => ⟨dvd_trans (by decide : 6 ∣ 102) h, dvd_trans (by decide : 17 ∣ 102) h⟩,
      fun ⟨h, k⟩ => (by decide : Nat.Coprime 6 17).mul_dvd_of_dvd_of_dvd h k⟩
  have inclusion (b : ℕ) : (if b.Coprime 102 then z ^ b else 0) =
      z ^ b -
        (if 2 ∣ b then z ^ b else 0) -
        (if 3 ∣ b then z ^ b else 0) -
        (if 17 ∣ b then z ^ b else 0) +
        (if 6 ∣ b then z ^ b else 0) +
        (if 34 ∣ b then z ^ b else 0) +
        (if 51 ∣ b then z ^ b else 0) -
        (if 102 ∣ b then z ^ b else 0) := by
    simp only [units, dvd102, dvd51, dvd34, dvd6]
    by_cases h2 : 2 ∣ b <;> by_cases h3 : 3 ∣ b <;> by_cases h17 : 17 ∣ b <;> simp [h2, h3, h17]
  have sum2 : (∑ b ∈ Finset.range 102, if 2 ∣ b then z ^ b else 0) = 0 := by
    rw [multiples 2 51 (by decide)]
    exact (IsPrimitiveRoot.pow (by decide : 0 < 102) hroot (by decide : 102 = 2 * 51)).geom_sum_eq_zero (by decide)
  have sum3 : (∑ b ∈ Finset.range 102, if 3 ∣ b then z ^ b else 0) = 0 := by
    rw [multiples 3 34 (by decide)]
    exact (IsPrimitiveRoot.pow (by decide : 0 < 102) hroot (by decide : 102 = 3 * 34)).geom_sum_eq_zero (by decide)
  have sum17 : (∑ b ∈ Finset.range 102, if 17 ∣ b then z ^ b else 0) = 0 := by
    rw [multiples 17 6 (by decide)]
    exact (IsPrimitiveRoot.pow (by decide : 0 < 102) hroot (by decide : 102 = 17 * 6)).geom_sum_eq_zero (by decide)
  have sum6 : (∑ b ∈ Finset.range 102, if 6 ∣ b then z ^ b else 0) = 0 := by
    rw [multiples 6 17 (by decide)]
    exact (IsPrimitiveRoot.pow (by decide : 0 < 102) hroot (by decide : 102 = 6 * 17)).geom_sum_eq_zero (by decide)
  have sum34 : (∑ b ∈ Finset.range 102, if 34 ∣ b then z ^ b else 0) = 0 := by
    rw [multiples 34 3 (by decide)]
    exact (IsPrimitiveRoot.pow (by decide : 0 < 102) hroot (by decide : 102 = 34 * 3)).geom_sum_eq_zero (by decide)
  have sum51 : (∑ b ∈ Finset.range 102, if 51 ∣ b then z ^ b else 0) = 0 := by
    rw [multiples 51 2 (by decide)]
    exact (IsPrimitiveRoot.pow (by decide : 0 < 102) hroot (by decide : 102 = 51 * 2)).geom_sum_eq_zero (by decide)
  have sum102 : (∑ b ∈ Finset.range 102, if 102 ∣ b then z ^ b else 0) = 1 := by
    rw [multiples 102 1 (by decide)]
    simp
  apply congrArg (fun s : ℂ => s / 32)
  simp_rw [hphase]
  rw [Finset.sum_filter]
  simp_rw [inclusion]
  norm_num only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    hroot.geom_sum_eq_zero (by decide), sum2, sum3, sum17, sum6, sum34, sum51, sum102]
