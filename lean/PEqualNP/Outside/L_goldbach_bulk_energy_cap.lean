import Mathlib

theorem PEqualNP.Outside.L_goldbach_bulk_energy_cap :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0;
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * E ((k : ℝ) * t));
    let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2;
    let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))};
    let low := fun (n k : ℕ) => if k ^ 3 ≤ n then w k else 0;
    let high := fun (n k : ℕ) => w k - low n k;
    let I := fun (n : ℕ) (a b : ℕ → ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u * S n b u * E (-(n : ℝ) * u)) t) (0 : ℝ) 1 MeasureTheory.volume;
    ∀ n : ℕ, 2 ≤ n → intervalIntegral (fun t => ‖S n (high n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume ≤ ((n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2 := by
  intro w E S _Q _arcs low high _I n hn
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hstar_E : ∀ x : ℝ, star (E x) = Complex.exp (-(((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) := by
    intro x
    dsimp only [E]
    change (starRingEnd ℂ) (Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-(((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have hE_mul_star : ∀ (j k : ℕ) (t : ℝ),
      E ((j : ℝ) * t) * star (E ((k : ℝ) * t)) =
      Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
    intro j k t
    rw [hstar_E]
    dsimp only [E]
    rw [← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast,
      Int.cast_sub, Int.cast_natCast]
    ring
  have hint_exp : ∀ m : ℤ,
      intervalIntegral (fun t : ℝ => Complex.exp ((m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
        (0 : ℝ) 1 MeasureTheory.volume = if m = 0 then 1 else 0 := by
    intro m
    by_cases hm : m = 0
    · subst hm
      simp
    · simp only [hm, ↓reduceIte]
      set c : ℂ := (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      have hc : c ≠ 0 := by
        dsimp only [c]
        have hm0 : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm
        have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        exact mul_ne_zero hm0 (mul_ne_zero (mul_ne_zero two_ne_zero hpi0) Complex.I_ne_zero)
      have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ)) / c) (Complex.exp (c * (t : ℂ))) t := by
        intro t _
        have h1 : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c t := by
          have := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c
          simpa using this
        have h2 : HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ))) (Complex.exp (c * (t : ℂ)) * c) t :=
          h1.cexp
        have h3 := h2.div_const c
        simpa [mul_div_cancel_right₀ _ hc] using h3
      have hcont : Continuous (fun t : ℝ => Complex.exp (c * (t : ℂ))) := by fun_prop
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
      have hexp1 : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
        rw [Complex.ofReal_one, mul_one]
        exact Complex.exp_int_mul_two_pi_mul_I m
      have hexp0 : Complex.exp (c * ((0 : ℝ) : ℂ)) = 1 := by
        rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      rw [hexp1, hexp0, sub_self]
  have hpoint : ∀ t : ℝ,
      ((‖S n (high n) t‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        ((high n j : ℂ) * (high n k : ℂ)) *
          Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
    intro t
    have hns : ((‖S n (high n) t‖ ^ 2 : ℝ) : ℂ) = S n (high n) t * star (S n (high n) t) := by
      have := Complex.mul_conj (S n (high n) t)
      rw [Complex.normSq_eq_norm_sq] at this
      exact this.symm
    rw [hns]
    dsimp only [S]
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.star_def]
    rw [show (high n j : ℂ) * E ((j : ℝ) * t) * ((high n k : ℂ) * star (E ((k : ℝ) * t))) =
      ((high n j : ℂ) * (high n k : ℂ)) * (E ((j : ℝ) * t) * star (E ((k : ℝ) * t))) by ring]
    rw [hE_mul_star j k t]
  have hparseval_complex :
      ((intervalIntegral (fun t => ‖S n (high n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume : ℝ) : ℂ) =
      ∑ k ∈ Finset.range (n + 1), ((high n k : ℂ) * (high n k : ℂ)) := by
    rw [← intervalIntegral.integral_ofReal]
    calc
      intervalIntegral (fun t => ((‖S n (high n) t‖ ^ 2 : ℝ) : ℂ)) (0 : ℝ) 1 MeasureTheory.volume
        = intervalIntegral
            (fun t => ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
              ((high n j : ℂ) * (high n k : ℂ)) *
                Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
            (0 : ℝ) 1 MeasureTheory.volume := intervalIntegral.integral_congr fun t _ => hpoint t
      _ = ∑ j ∈ Finset.range (n + 1),
            intervalIntegral
              (fun t => ∑ k ∈ Finset.range (n + 1),
                ((high n j : ℂ) * (high n k : ℂ)) *
                  Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
              (0 : ℝ) 1 MeasureTheory.volume := by
          refine intervalIntegral.integral_finsetSum fun j _ => ?_
          exact Continuous.intervalIntegrable (by fun_prop) 0 1
      _ = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            intervalIntegral
              (fun t => ((high n j : ℂ) * (high n k : ℂ)) *
                Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
              (0 : ℝ) 1 MeasureTheory.volume := by
          refine Finset.sum_congr rfl fun j _ => ?_
          refine intervalIntegral.integral_finsetSum fun k _ => ?_
          exact Continuous.intervalIntegrable (by fun_prop) 0 1
      _ = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            ((high n j : ℂ) * (high n k : ℂ)) * (if ((j : ℤ) - (k : ℤ)) = 0 then (1 : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          rw [intervalIntegral.integral_const_mul, hint_exp ((j : ℤ) - (k : ℤ))]
      _ = ∑ j ∈ Finset.range (n + 1), ((high n j : ℂ) * (high n j : ℂ)) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.sum_eq_single j]
          · simp
          · intro k _ hkj
            have hne : (j : ℤ) - (k : ℤ) ≠ 0 := by omega
            simp [hne]
          · intro hj'
            exact (hj' hj).elim
  have hparseval :
      intervalIntegral (fun t => ‖S n (high n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume =
      ∑ k ∈ Finset.range (n + 1), (high n k) ^ 2 := by
    have hre := congrArg Complex.re hparseval_complex
    rw [Complex.ofReal_re] at hre
    rw [hre, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re, sq]
  have hhigh_bound : ∀ k ∈ Finset.range (n + 1), (high n k) ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h0 : 0 ≤ high n k := by
      dsimp only [high, low]
      by_cases h1 : k ^ 3 ≤ n
      · simp [h1]
      · simp only [h1, ↓reduceIte, sub_zero, w]
        split_ifs with hp
        · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
        · exact le_rfl
    have hle : high n k ≤ Real.log (n : ℝ) := by
      dsimp only [high, low]
      by_cases h1 : k ^ 3 ≤ n
      · simp [h1, hlog_nonneg]
      · simp only [h1, ↓reduceIte, sub_zero, w]
        split_ifs with hp
        · exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hkn)
        · exact hlog_nonneg
    exact pow_le_pow_left₀ h0 hle 2
  calc
    intervalIntegral (fun t => ‖S n (high n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume
      = ∑ k ∈ Finset.range (n + 1), (high n k) ^ 2 := hparseval
    _ ≤ ∑ _k ∈ Finset.range (n + 1), (Real.log (n : ℝ)) ^ 2 := Finset.sum_le_sum hhigh_bound
    _ = ((n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
