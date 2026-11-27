import Mathlib

theorem PEqualNP.Outside.L_goldbach_divisor_indicator_covariance :
    let X := fun (p t : ℕ) => (p:ℝ)*(if p ∣ t then 1 else 0)-1; ∀ (N p q : ℕ), 0 < N → Nat.Prime p → Nat.Prime q → p ∣ N → q ∣ N → ((∑ t ∈ Finset.range N, X p t * X q t)/(N:ℝ)) = if p=q then (p:ℝ)-1 else 0 := by
  intro X N p q hN hp hq hpN hqN
  have cnt : ∀ d : ℕ, 0 < d → d ∣ N →
      (d:ℝ) * (∑ t ∈ Finset.range N, (if d ∣ t then (1:ℝ) else 0)) = N := by
    rintro d hd ⟨m, rfl⟩
    have himg : (Finset.range (d * m)).filter (fun t => d ∣ t)
        = (Finset.range m).image (fun k => d * k) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨ht, k, rfl⟩
        exact ⟨k, lt_of_mul_lt_mul_left ht (Nat.zero_le d), rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨Nat.mul_lt_mul_of_pos_left hk hd, dvd_mul_right _ _⟩
    rw [← Finset.sum_filter, himg, Finset.sum_const,
      Finset.card_image_of_injective _ (mul_right_injective₀ hd.ne'), Finset.card_range]
    simp
  have hN' : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have expand : ∑ t ∈ Finset.range N, X p t * X q t
      = (p:ℝ) * q * (∑ t ∈ Finset.range N, (if p ∣ t ∧ q ∣ t then (1:ℝ) else 0))
        - (p:ℝ) * (∑ t ∈ Finset.range N, (if p ∣ t then (1:ℝ) else 0))
        - (q:ℝ) * (∑ t ∈ Finset.range N, (if q ∣ t then (1:ℝ) else 0))
        + ∑ t ∈ Finset.range N, (1:ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    simp only [X]
    by_cases h1 : p ∣ t <;> by_cases h2 : q ∣ t <;> simp [h1, h2] <;> ring
  have hone : ∑ t ∈ Finset.range N, (1:ℝ) = N := by simp
  rw [expand, hone]
  have hcp := cnt p hp.pos hpN
  have hcq := cnt q hq.pos hqN
  by_cases hpq : p = q
  · subst hpq
    simp only [and_self, ite_true]
    rw [div_eq_iff hN']
    linear_combination ((p:ℝ) - 2) * hcp
  · simp only [hpq, ite_false]
    have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    have hiff : ∀ t : ℕ, (p ∣ t ∧ q ∣ t) ↔ p * q ∣ t := fun t =>
      ⟨fun h => hco.mul_dvd_of_dvd_of_dvd h.1 h.2,
       fun h => ⟨(dvd_mul_right p q).trans h, (dvd_mul_left q p).trans h⟩⟩
    simp only [hiff]
    have hcpq := cnt (p * q) (Nat.mul_pos hp.pos hq.pos) (hco.mul_dvd_of_dvd_of_dvd hpN hqN)
    push_cast at hcpq
    rw [div_eq_zero_iff]
    left
    linear_combination hcpq - hcp - hcq
