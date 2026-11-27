import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_133 :
    ∀ a:ℕ, Nat.Coprime a 133 → (∑ b ∈ (Finset.range 133).filter (fun b => Nat.Coprime b 133), Complex.exp (((2*Real.pi*(a:ℝ)*b/133:ℝ):ℂ)*Complex.I))/(108:ℂ)=(1:ℂ)/108 := by
  intro a ha
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 133)
  let z := Complex.exp θ
  have hroot : IsPrimitiveRoot z 133 := by
    simpa [z, θ] using Complex.isPrimitiveRoot_exp_of_coprime a 133 (by decide) ha
  have hphase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 133 : ℝ) : ℂ) * Complex.I) = z ^ b := by
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
  have hunits (b : ℕ) : Nat.Coprime b 133 ↔ ¬ 7 ∣ b ∧ ¬ 19 ∣ b := by
    change b.Coprime (7 * 19) ↔ _
    rw [Nat.coprime_mul_iff_right, (@Nat.coprime_comm b 7), (@Nat.coprime_comm b 19),
      (by decide : Nat.Prime 7).coprime_iff_not_dvd, (by decide : Nat.Prime 19).coprime_iff_not_dvd]
  have hboth (b : ℕ) : 133 ∣ b ↔ 7 ∣ b ∧ 19 ∣ b := by
    exact ⟨fun h => ⟨dvd_trans (by decide : 7 ∣ 133) h, dvd_trans (by decide : 19 ∣ 133) h⟩,
      fun ⟨h, k⟩ => (by decide : Nat.Coprime 7 19).mul_dvd_of_dvd_of_dvd h k⟩
  have inclusion (b : ℕ) : (if b.Coprime 133 then z ^ b else 0) =
      z ^ b - (if 7 ∣ b then z ^ b else 0) - (if 19 ∣ b then z ^ b else 0) +
        (if 133 ∣ b then z ^ b else 0) := by
    simp_rw [hunits, hboth]
    by_cases h : 7 ∣ b <;> by_cases k : 19 ∣ b <;> simp [h, k]
  have root19 : IsPrimitiveRoot (z ^ 7) 19 := IsPrimitiveRoot.pow (by decide) hroot rfl
  have root7 : IsPrimitiveRoot (z ^ 19) 7 := IsPrimitiveRoot.pow (by decide) hroot rfl
  apply congrArg (fun s : ℂ => s / 108)
  simp_rw [hphase]
  rw [Finset.sum_filter]
  simp_rw [inclusion]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    hroot.geom_sum_eq_zero (by decide), multiples 7 19 (by decide),
    multiples 19 7 (by decide), multiples 133 1 (by decide),
    root19.geom_sum_eq_zero (by decide), root7.geom_sum_eq_zero (by decide)]
  simp
