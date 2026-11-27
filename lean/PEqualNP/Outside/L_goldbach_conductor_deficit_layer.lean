import Mathlib

theorem PEqualNP.Outside.L_goldbach_conductor_deficit_layer :
    ∀ (n : ℕ) [NeZero n], 2<n → ∀ χ : DirichletCharacter ℂ n, Real.log ((n:ℝ)/(χ.conductor:ℝ)) = ∑ p ∈ n.primeFactors, (Real.log (p:ℝ)) * (((Finset.Icc 1 (n.factorization p)).filter (fun j => χ.conductor ∣ n/p^j)).card : ℝ) := by
  intro n _ _ χ
  let m := n / χ.conductor
  have hd := χ.conductor_dvd_level
  have hn : n ≠ 0 := NeZero.ne n
  have hprod : m * χ.conductor = n := Nat.div_mul_cancel hd
  have hm : m ≠ 0 := by
    intro h
    exact hn (by simpa [h] using hprod.symm)
  have hmn : m ∣ n := ⟨χ.conductor, hprod.symm⟩
  have hle : m.factorization ≤ n.factorization := (Nat.factorization_le_iff_dvd hm hn).mpr hmn
  have layers (p : ℕ) (hp : p ∈ n.primeFactors) :
      (Finset.Icc 1 (n.factorization p)).filter (fun j => χ.conductor ∣ n/p^j) =
        Finset.Icc 1 (m.factorization p) := by
    have prime := Nat.prime_of_mem_primeFactors hp
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have layer (hj : j ≤ n.factorization p) :
        χ.conductor ∣ n/p^j ↔ j ≤ m.factorization p := by
      have hpow := (prime.pow_dvd_iff_le_factorization hn).mpr hj
      rw [← prime.pow_dvd_iff_le_factorization hm, Nat.dvd_div_iff_mul_dvd hpow]
      dsimp only [m]
      rw [Nat.dvd_div_iff_mul_dvd hd, mul_comm]
    constructor
    · rintro ⟨⟨hpos, hj⟩, h⟩
      exact ⟨hpos, (layer hj).mp h⟩
    · rintro ⟨hpos, hj⟩
      have hjn := hj.trans (hle p)
      exact ⟨⟨hpos, hjn⟩, (layer hjn).mpr hj⟩
  have hdreal : (χ.conductor : ℝ) ≠ 0 := by exact_mod_cast χ.conductor_ne_zero
  rw [← Nat.cast_div hd hdreal, Real.log_nat_eq_sum_factorization]
  change (∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * Real.log p) = _
  calc
    _ = ∑ p ∈ n.primeFactors, (m.factorization p : ℝ) * Real.log p := by
      apply Finset.sum_subset (Nat.primeFactors_mono hmn hn)
      intro p _ hnot
      have hzero : m.factorization p = 0 := Finsupp.notMem_support_iff.mp hnot
      simp [hzero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [layers p hp, Nat.card_Icc]
      simp [mul_comm]
