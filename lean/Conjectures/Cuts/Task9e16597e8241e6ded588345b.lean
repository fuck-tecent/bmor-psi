import Mathlib

private theorem sum_quadratic_phase_eq_zero {p t : ℕ} (hp : p.Prime) (h : ¬p ∣ t) :
    (∑ k ∈ Finset.range p, Real.cos (2 * Real.pi * (k:ℝ) * (t:ℝ) / (p:ℝ))) = 0 := by
  let z := Complex.exp (2 * (Real.pi:ℂ) * Complex.I * ((t:ℂ)/(p:ℂ)))
  have hCop : t.Coprime p := (hp.coprime_iff_not_dvd.mpr h).symm
  have hRoot : IsPrimitiveRoot z p := Complex.isPrimitiveRoot_exp_of_coprime t p hp.ne_zero hCop
  have hPow (k : ℕ) :
      (z^k).re = Real.cos (2 * Real.pi * (k:ℝ) * (t:ℝ) / (p:ℝ)) := by
    have he : z ^ k =
        Complex.exp ((((2 * Real.pi * (k:ℝ) * (t:ℝ) / (p:ℝ)) : ℝ) : ℂ) * Complex.I) := by
      dsimp [z]
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [he, Complex.exp_ofReal_mul_I_re]
  calc
    (∑ k ∈ Finset.range p, Real.cos (2 * Real.pi * (k:ℝ) * (t:ℝ) / (p:ℝ))) =
        ∑ k ∈ Finset.range p, (z^k).re :=
      Finset.sum_congr rfl fun k _ => (hPow k).symm
    _ = (∑ k ∈ Finset.range p, z^k).re := by simp
    _ = 0 := by rw [hRoot.geom_sum_eq_zero hp.one_lt]; simp

theorem Conjectures.Cuts.Task9e16597e8241e6ded588345b :
    (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.filter Nat.Prime (Finset.Ioc x1 ((2 : ℕ) * x1)); have x2 : ℕ → Finset ℕ := fun (x2 : ℕ) => {x3 ∈ Finset.range ((2 : ℕ) * x2) | x3 ^ (2 : ℕ) + (1 : ℕ) < (2 : ℕ) * x2}; have x3 : ℕ → ℝ := fun (x3 : ℕ) => ↑(x1 x3).card * ↑(x2 x3).card; have x4 : ℕ → ℝ := fun (x4 : ℕ) => ∑ x5 ∈ x1 x4, ∑ x6 ∈ x2 x4, ∑ x7 ∈ (Finset.range x5).erase (0 : ℕ), Real.cos ((2 : ℝ) * Real.pi * ↑x7 * ↑(x6 ^ (2 : ℕ) + (1 : ℕ)) / ↑x5); ∀ (x5 : ℕ), (2 : ℕ) ≤ x5 → (0 : ℝ) < x3 x5 ∧ ((0 : ℝ) < x3 x5 + x4 x5 → ∃ (x8 : ℕ) (x9 : ℕ), x5 < x9 ∧ Nat.Prime x9 ∧ x8 ^ (2 : ℕ) + (1 : ℕ) = x9)) := by
  classical
  dsimp only
  intro X hx
  let P := (Finset.Ioc X (2*X)).filter Nat.Prime
  let S := (Finset.range (2*X)).filter (fun n => n^2+1 < 2*X)
  let f (p n k : ℕ) : ℝ := Real.cos (2 * Real.pi * (k:ℝ) * ((n^2+1 : ℕ):ℝ) / (p:ℝ))
  let d : ℝ := (P.card:ℝ) * S.card
  let e : ℝ := ∑ p ∈ P, ∑ n ∈ S, ∑ k ∈ (Finset.range p).erase 0, f p n k
  change 0 < d ∧ (0 < d + e → ∃ n p : ℕ, X < p ∧ Nat.Prime p ∧ n^2+1=p)
  have hP : P.Nonempty := by
    obtain ⟨p,hp,hxp,hpx⟩ := Nat.exists_prime_lt_and_le_two_mul X (by omega)
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hxp,hpx⟩,hp⟩⟩
  have hS : S.Nonempty := by
    refine ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩⟩
    simp only [zero_pow (by decide : 2≠0),zero_add]; omega
  have hD : 0 < d := mul_pos (by exact_mod_cast hP.card_pos) (by exact_mod_cast hS.card_pos)
  refine ⟨hD,?_⟩
  intro hPos
  by_contra hNo
  have hMode (p : ℕ) (hpP : p ∈ P) (n : ℕ) (hnS : n ∈ S) :
      ∑ k ∈ (Finset.range p).erase 0, f p n k = -1 := by
    obtain ⟨hpx,hp⟩ := Finset.mem_filter.mp hpP
    have hXp := (Finset.mem_Ioc.mp hpx).1
    have hnBound := (Finset.mem_filter.mp hnS).2
    have hDvd : ¬p ∣ n^2+1 := by
      rintro ⟨a,ha⟩
      have hpPos := hp.pos
      have ha0 : a ≠ 0 := by rintro rfl; simp at ha
      have ha2 : a < 2 := by
        by_contra! hGe
        have hmul := Nat.mul_le_mul_left p hGe
        omega
      have ha1 : a=1 := by omega
      exact hNo ⟨n,p,hXp,hp,by simpa [ha1] using ha⟩
    have hAll : ∑ k ∈ Finset.range p, f p n k = 0 := sum_quadratic_phase_eq_zero hp hDvd
    have hZero : f p n 0 = 1 := by simp [f]
    have hSplit := Finset.sum_erase_add (Finset.range p) (f p n) (Finset.mem_range.mpr hp.pos)
    linarith
  have hNeg : e = -d := by
    calc
      e = ∑ p ∈ P, ∑ _n ∈ S, (-1 : ℝ) := by
        apply Finset.sum_congr rfl; intro p hpP
        apply Finset.sum_congr rfl; intro n hnS
        exact hMode p hpP n hnS
      _ = -d := by simp [d, nsmul_eq_mul]
  linarith
