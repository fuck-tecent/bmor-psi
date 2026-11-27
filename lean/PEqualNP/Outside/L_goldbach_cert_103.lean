import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_103 :
    ∀ a:ℕ, Nat.Coprime a 103 → (∑ b ∈ (Finset.range 103).filter (fun b => Nat.Coprime b 103), Complex.exp (((2*Real.pi*(a:ℝ)*b/103:ℝ):ℂ)*Complex.I))/(102:ℂ)=(-1:ℂ)/102 := by
  have prime_ramanujan_sum (p a : ℕ) (hp : p.Prime) (ha : a.Coprime p) :
      (∑ b ∈ (Finset.range p).filter (fun b => Nat.Coprime b p),
        Complex.exp (((2 * Real.pi * (a : ℝ) * b / p : ℝ) : ℂ) * Complex.I)) = -1 := by
    let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / p)
    have hroot : IsPrimitiveRoot (Complex.exp θ) p :=
      Complex.isPrimitiveRoot_exp_of_coprime a p hp.ne_zero ha
    have hphase (b : ℕ) : Complex.exp (((2 * Real.pi * (a : ℝ) * b / p : ℝ) : ℂ) * Complex.I) =
        Complex.exp θ ^ b := by
      rw [← Complex.exp_nat_mul]
      congr 1
      dsimp [θ]
      push_cast
      ring
    have hunits : (Finset.range p).filter (fun b => Nat.Coprime b p) = (Finset.range p).erase 0 := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
      constructor
      · rintro ⟨hb, hbp⟩
        exact ⟨fun h => (hp.coprime_iff_not_dvd.mp hbp.symm) (h ▸ dvd_zero p), hb⟩
      · rintro ⟨hb0, hb⟩
        exact ⟨hb, (Nat.coprime_of_lt_prime hb0 hb hp).symm⟩
    simp_rw [hphase]
    rw [hunits, eq_neg_iff_add_eq_zero, ← pow_zero (Complex.exp θ),
      Finset.sum_erase_add _ _ (Finset.mem_range.mpr hp.pos)]
    exact hroot.geom_sum_eq_zero hp.one_lt
  intro a ha
  apply congrArg (fun z : ℂ => z / 102)
  simpa only [Nat.cast_ofNat] using prime_ramanujan_sum 103 a (by norm_num) ha
