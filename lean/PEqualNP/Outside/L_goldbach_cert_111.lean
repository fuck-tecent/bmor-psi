import Mathlib

private theorem sum_multiples (z : ℂ) (d m : ℕ) (hd : 0 < d) :
    (∑ b ∈ Finset.range (d * m), if d ∣ b then z ^ b else 0) =
      ∑ j ∈ Finset.range m, (z ^ d) ^ j := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun j _ => d * j)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      ((Nat.mul_lt_mul_left hd).mpr (Finset.mem_range.mp hj)), ⟨j, rfl⟩⟩
  · intro i _ j _ hij
    exact Nat.eq_of_mul_eq_mul_left hd hij
  · intro b hb
    obtain ⟨hbound, ⟨j, rfl⟩⟩ := Finset.mem_filter.mp hb
    exact ⟨j, Finset.mem_range.mpr ((Nat.mul_lt_mul_left hd).mp (Finset.mem_range.mp hbound)), rfl⟩
  · intro j _
    exact (pow_mul z d j).symm

private theorem unit_weight (z : ℂ) (p q b : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p.Coprime q) :
    (if b.Coprime (p * q) then z ^ b else 0) = z ^ b - (if p ∣ b then z ^ b else 0) -
      (if q ∣ b then z ^ b else 0) + (if p * q ∣ b then z ^ b else 0) := by
  have hunit : b.Coprime (p * q) ↔ ¬ p ∣ b ∧ ¬ q ∣ b := by
    rw [Nat.coprime_mul_iff_right, (Nat.coprime_comm : b.Coprime p ↔ _),
      (Nat.coprime_comm : b.Coprime q ↔ _), hp.coprime_iff_not_dvd, hq.coprime_iff_not_dvd]
  have hboth : p * q ∣ b ↔ p ∣ b ∧ q ∣ b := by
    exact ⟨fun h => ⟨dvd_trans (dvd_mul_right p q) h, dvd_trans (dvd_mul_left q p) h⟩,
      fun ⟨h₁, h₂⟩ => hpq.mul_dvd_of_dvd_of_dvd h₁ h₂⟩
  by_cases h₁ : p ∣ b <;> by_cases h₂ : q ∣ b <;> simp [hunit, hboth, h₁, h₂]

-- The complete sum and the sums on multiples of p and q vanish. Their intersection
-- consists only of zero, which contributes 1 to the inclusion-exclusion formula.
private theorem sum_units_semiprime (z : ℂ) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p.Coprime q) (hz : IsPrimitiveRoot z (p * q)) :
    (∑ b ∈ (Finset.range (p * q)).filter (fun b => b.Coprime (p * q)), z ^ b) = 1 := by
  have hpos := Nat.mul_pos hp.pos hq.pos
  have hzp : IsPrimitiveRoot (z ^ p) q := IsPrimitiveRoot.pow hpos hz rfl
  have hzq : IsPrimitiveRoot (z ^ q) p := IsPrimitiveRoot.pow hpos hz (Nat.mul_comm p q)
  have hqsum := sum_multiples z q p hq.pos
  rw [Nat.mul_comm q p] at hqsum
  have hboth := sum_multiples z (p * q) 1 hpos
  simp only [Nat.mul_one, Finset.sum_range_one, pow_zero] at hboth
  have hlarge : 1 < p * q := by nlinarith [hp.one_lt, hq.one_lt]
  simp_rw [Finset.sum_filter, unit_weight z p q _ hp hq hpq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_multiples z p q hp.pos, hqsum, hboth, hz.geom_sum_eq_zero hlarge,
    hzp.geom_sum_eq_zero hq.one_lt, hzq.geom_sum_eq_zero hp.one_lt]
  simp

theorem PEqualNP.Outside.L_goldbach_cert_111 :
    ∀ a:ℕ, Nat.Coprime a 111 → (∑ b ∈ (Finset.range 111).filter (fun b => Nat.Coprime b 111), Complex.exp (((2*Real.pi*(a:ℝ)*b/111:ℝ):ℂ)*Complex.I))/(72:ℂ)=(1:ℂ)/72 := by
  intro a ha
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / 111)
  have hz : IsPrimitiveRoot (Complex.exp θ) 111 :=
    Complex.isPrimitiveRoot_exp_of_coprime a 111 (by decide) ha
  apply congrArg (fun s : ℂ => s / 72)
  calc
    _ = ∑ b ∈ (Finset.range 111).filter (fun b => Nat.Coprime b 111), (Complex.exp θ) ^ b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← Complex.exp_nat_mul]
      congr 1
      dsimp [θ]
      push_cast
      ring
    _ = 1 := sum_units_semiprime _ 3 37 (by decide) (by decide) (by decide) hz
