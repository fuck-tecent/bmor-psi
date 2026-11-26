import rational
import vaughan

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction zeta Moebius

namespace PEqualNP.Outside.Vaughan

noncomputable section

/-- Type-I bound for the second Vaughan term.  After the divisor
reindexing, the inner sum over `l` is a log-weighted exponential sum with
frequency `d * t`, so the weighted Abel bound gives the reciprocal-sine
estimate below. -/
theorem norm_expSum_low_mu_mul_log_le (n U : ℕ) (t : ℝ)
    (hsin : ∀ d ∈ Finset.Icc 1 U,
      Real.sin (Real.pi * ((d : ℝ) * t)) ≠ 0) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) t‖ ≤
      ∑ d ∈ Finset.Icc 1 U,
        2 * Real.log (n : ℝ) / |Real.sin (Real.pi * ((d : ℝ) * t))| := by
  rw [expSum_low_mu_mul_log_eq]
  refine (norm_type1_bilinear_log_le n U
    (fun d => (μ : ArithmeticFunction ℝ) d) t hsin).trans ?_
  apply Finset.sum_le_sum
  intro d hd
  have hs : 0 < |Real.sin (Real.pi * ((d : ℝ) * t))| := abs_pos.mpr (hsin d hd)
  have hμ : |(μ : ArithmeticFunction ℝ) d| ≤ 1 := by
    have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
      ArithmeticFunction.abs_moebius_le_one
    have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast h
    simpa using h'
  have hlog : Real.log ((n / d : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
    rcases Nat.eq_zero_or_pos (n / d) with h0 | hpos
    · rw [h0]
      simpa using Real.log_natCast_nonneg n
    · exact Real.log_le_log (by exact_mod_cast hpos)
        (by exact_mod_cast Nat.div_le_self n d)
  calc
    |(μ : ArithmeticFunction ℝ) d| *
        (2 * Real.log ((n / d : ℕ) : ℝ) /
          |Real.sin (Real.pi * ((d : ℝ) * t))|)
        ≤ 1 * (2 * Real.log ((n / d : ℕ) : ℝ) /
          |Real.sin (Real.pi * ((d : ℝ) * t))|) := by
      apply mul_le_mul_of_nonneg_right hμ
      exact div_nonneg
        (mul_nonneg (by norm_num) (Real.log_natCast_nonneg (n / d)))
        (abs_nonneg _)
    _ = 2 * Real.log ((n / d : ℕ) : ℝ) /
          |Real.sin (Real.pi * ((d : ℝ) * t))| := one_mul _
    _ ≤ 2 * Real.log (n : ℝ) /
          |Real.sin (Real.pi * ((d : ℝ) * t))| := by
      rw [div_le_div_iff_of_pos_right hs]
      exact mul_le_mul_of_nonneg_left hlog (by norm_num)

/-- Conditional major-arc form: if all the frequencies `d * t` stay at
distance `1/q` from the integers (in the sine sense), then the second Vaughan
term is at most `2 U q log n`. -/
theorem norm_expSum_low_mu_mul_log_le_of_sine_separation (n U q : ℕ) (t : ℝ)
    (hq : 0 < q)
    (hsin : ∀ d ∈ Finset.Icc 1 U,
      (1:ℝ)/(q:ℝ) ≤ |Real.sin (Real.pi * ((d:ℝ) * t))|) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) t‖ ≤
      2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hqne : (q:ℝ) ≠ 0 := hqR.ne'
  refine (norm_expSum_low_mu_mul_log_le n U t ?_).trans ?_
  · intro d hd
    have hpos : (0:ℝ) < |Real.sin (Real.pi * ((d:ℝ) * t))| :=
      lt_of_lt_of_le (one_div_pos.mpr hqR) (hsin d hd)
    exact abs_pos.mp hpos
  · have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
    calc
      ∑ d ∈ Finset.Icc 1 U, 2 * Real.log (n:ℝ) /
          |Real.sin (Real.pi * ((d:ℝ) * t))|
          ≤ ∑ _d ∈ Finset.Icc 1 U, 2 * Real.log (n:ℝ) / (1/(q:ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hlog)
          (one_div_pos.mpr hqR) (hsin d hd)
      _ = 2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc]
        have hcard : U + 1 - 1 = U := by omega
        rw [hcard, nsmul_eq_mul]
        field_simp

/-- Unconditional major-arc Type-I bound: for `t = a/q + β` with
`gcd(a,q) = 1`, `U < q` and `|β| <= 1/(16 q U)`, the second Vaughan term is
bounded by `2 U q log n`. -/
theorem norm_expSum_low_mu_mul_log_le_majorArc (n q U a : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hU1 : 1 ≤ U) (hUq : U < q)
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * (U:ℝ))) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
        ((a:ℝ)/(q:ℝ) + β)‖ ≤
      2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) := by
  exact norm_expSum_low_mu_mul_log_le_of_sine_separation n U q
    ((a:ℝ)/(q:ℝ) + β) hq
    (abs_sin_pi_mul_majorArc_ge q U a β hq hcop hU1 hUq hβ)

/- Major-arc estimate for the third Vaughan term: when `q > U^2` and the
perturbation is below `1/(16 q U^2)`, every product `d * e` stays below `q`,
so the inner geometric sums contribute a factor `q` each. -/
set_option maxHeartbeats 1000000 in
theorem norm_expSum_low_mu_lowLambda_zeta_le_majorArc (n q U a : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hU1 : 1 ≤ U) (hUq : U * U < q)
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ))) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
        (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ ≤
      2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by
  rw [expSum_low_mu_lowLambda_zeta_eq n U ((a:ℝ)/(q:ℝ) + β)]
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hqne : (q:ℝ) ≠ 0 := hqR.ne'
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hsine : ∀ k ∈ Finset.Icc 1 (U * U),
      (1:ℝ)/(q:ℝ) ≤ |Real.sin (Real.pi * ((k:ℝ) * ((a:ℝ)/(q:ℝ) + β)))| :=
    abs_sin_pi_mul_majorArc_ge q (U * U) a β hq hcop
      (Nat.mul_pos (by omega : 0 < U) (by omega : 0 < U)) hUq hβ
  calc
    ‖∑ d ∈ Finset.Icc 1 (min U n), ((μ : ArithmeticFunction ℝ) d : ℂ) *
        ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e : ℂ) *
            ∑ m ∈ Finset.Icc 1 (n / (d * e)),
              E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖
        ≤ ∑ d ∈ Finset.Icc 1 (min U n), ‖((μ : ArithmeticFunction ℝ) d : ℂ) *
            ∑ e ∈ Finset.Icc 1 (min U (n / d)),
              ((Λ : ArithmeticFunction ℝ) e : ℂ) *
                ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                  E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ :=
      norm_sum_le _ _
    _ = ∑ d ∈ Finset.Icc 1 (min U n), |(μ : ArithmeticFunction ℝ) d| *
          ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ := by
      apply Finset.sum_congr rfl
      intro d _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ d ∈ Finset.Icc 1 (min U n), |(μ : ArithmeticFunction ℝ) d| *
          ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            |(Λ : ArithmeticFunction ℝ) e| *
              ‖∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ := by
      apply Finset.sum_le_sum
      intro d _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖
            ≤ ∑ e ∈ Finset.Icc 1 (min U (n / d)),
                ‖((Λ : ArithmeticFunction ℝ) e : ℂ) *
                  ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                    E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ :=
          norm_sum_le _ _
        _ = ∑ e ∈ Finset.Icc 1 (min U (n / d)),
              |(Λ : ArithmeticFunction ℝ) e| *
                ‖∑ m ∈ Finset.Icc 1 (n / (d * e)),
                  E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ := by
          apply Finset.sum_congr rfl
          intro e _
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ d ∈ Finset.Icc 1 (min U n), ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          (Real.log (n:ℝ) * (2 * (q:ℝ))) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.mp hd
      obtain ⟨he1, he2⟩ := Finset.mem_Icc.mp he
      have hdU : d ≤ U := by omega
      have heU : e ≤ U := by omega
      have hen : e ≤ n := by
        have h : e ≤ n / d := le_trans he2 (min_le_right _ _)
        have := Nat.div_le_self n d
        omega
      have hμd : |(μ : ArithmeticFunction ℝ) d| ≤ 1 := by
        have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
          ArithmeticFunction.abs_moebius_le_one
        have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
          exact_mod_cast h
        simpa using h'
      have hΛe : |(Λ : ArithmeticFunction ℝ) e| ≤ Real.log (n:ℝ) := by
        rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have hepos : 0 < e := by omega
        exact (ArithmeticFunction.vonMangoldt_le_log).trans
          (Real.log_le_log (by exact_mod_cast hepos) (by exact_mod_cast hen))
      have hk_mem : d * e ∈ Finset.Icc 1 (U * U) :=
        Finset.mem_Icc.mpr ⟨Nat.mul_pos (by omega) (by omega), Nat.mul_le_mul hdU heU⟩
      have hsin_ge := hsine (d * e) hk_mem
      have hsin_ne : Real.sin (Real.pi * (((d * e : ℕ) : ℝ) *
          ((a:ℝ)/(q:ℝ) + β))) ≠ 0 :=
        abs_pos.mp (lt_of_lt_of_le (one_div_pos.mpr hqR) hsin_ge)
      have hphase : (∑ m ∈ Finset.Icc 1 (n / (d * e)),
            E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))) =
          ∑ m ∈ Finset.Icc 1 (n / (d * e)),
            E ((m : ℝ) * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))) := by
        apply Finset.sum_congr rfl
        intro m _
        have harg : ((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β) =
            (m : ℝ) * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)) := by
          push_cast
          ring
        rw [harg]
      rw [hphase]
      have hinner : ‖∑ m ∈ Finset.Icc 1 (n / (d * e)),
            E ((m : ℝ) * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)))‖ ≤ 2 * (q:ℝ) := by
        refine (norm_geometric_sum_Icc_le_two (n / (d * e))
          (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)) hsin_ne).trans ?_
        have hs' : (1:ℝ) ≤ |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) *
            ((a:ℝ)/(q:ℝ) + β)))| * (q:ℝ) := (div_le_iff₀ hqR).mp hsin_ge
        have hspos : 0 < |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) *
            ((a:ℝ)/(q:ℝ) + β)))| := lt_of_lt_of_le (one_div_pos.mpr hqR) hsin_ge
        have hunit : (1:ℝ) / |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) *
            ((a:ℝ)/(q:ℝ) + β)))| ≤ (q:ℝ) := by
          rw [div_le_iff₀ hspos]
          simpa [mul_comm] using hs'
        calc
          (2:ℝ) / |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) *
              ((a:ℝ)/(q:ℝ) + β)))| =
              2 * (1 / |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) *
                ((a:ℝ)/(q:ℝ) + β)))|) := by ring
          _ ≤ 2 * (q:ℝ) := mul_le_mul_of_nonneg_left hunit (by norm_num)
      calc
        |(μ : ArithmeticFunction ℝ) d| *
            (|(Λ : ArithmeticFunction ℝ) e| *
              ‖∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E ((m : ℝ) * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)))‖)
            ≤ 1 * (Real.log (n:ℝ) * (2 * (q:ℝ))) := by
          refine mul_le_mul hμd ?_ ?_ (by norm_num)
          · exact mul_le_mul hΛe hinner (norm_nonneg _) hlog
          · exact mul_nonneg (abs_nonneg _) (norm_nonneg _)
        _ = Real.log (n:ℝ) * (2 * (q:ℝ)) := one_mul _
    _ ≤ ∑ d ∈ Finset.Icc 1 (min U n), ∑ e ∈ Finset.Icc 1 U,
          (Real.log (n:ℝ) * (2 * (q:ℝ))) := by
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp he).1, by
          have := (Finset.mem_Icc.mp he).2
          omega⟩
      · intro e _ _
        exact mul_nonneg hlog (by positivity)
    _ = ∑ d ∈ Finset.Icc 1 (min U n),
          (U:ℝ) * (Real.log (n:ℝ) * (2 * (q:ℝ))) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_const, Nat.card_Icc]
      have hcard : U + 1 - 1 = U := by omega
      rw [hcard, nsmul_eq_mul]
    _ = ((min U n : ℕ) : ℝ) * ((U:ℝ) * (Real.log (n:ℝ) * (2 * (q:ℝ)))) := by
      rw [Finset.sum_const, Nat.card_Icc]
      have hcard : min U n + 1 - 1 = min U n := by omega
      rw [hcard, nsmul_eq_mul]
    _ ≤ 2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by
      have hmin : ((min U n : ℕ) : ℝ) ≤ (U:ℝ) := by exact_mod_cast min_le_left U n
      have hC : 0 ≤ Real.log (n:ℝ) * (2 * (q:ℝ)) :=
        mul_nonneg hlog (by positivity)
      have hUC : 0 ≤ (U:ℝ) * (Real.log (n:ℝ) * (2 * (q:ℝ))) :=
        mul_nonneg (by positivity) hC
      calc
        ((min U n : ℕ) : ℝ) * ((U:ℝ) * (Real.log (n:ℝ) * (2 * (q:ℝ))))
            ≤ (U:ℝ) * ((U:ℝ) * (Real.log (n:ℝ) * (2 * (q:ℝ)))) :=
          mul_le_mul_of_nonneg_right hmin hUC
        _ = 2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by ring

end

end PEqualNP.Outside.Vaughan
