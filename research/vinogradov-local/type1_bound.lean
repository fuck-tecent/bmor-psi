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

lemma norm_log_weighted_geometric_sum_Icc_le_trivial (N : ℕ) (t : ℝ) :
    ‖∑ l ∈ Finset.Icc 1 N, (Real.log l : ℂ) * E ((l : ℝ) * t)‖ ≤
      (N : ℝ) * Real.log (N : ℝ) := by
  have normE : ∀ x : ℝ, ‖E x‖ = 1 := by
    intro x
    dsimp only [E]
    simpa only [mul_comm] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
  have h1 : ‖∑ l ∈ Finset.Icc 1 N, (Real.log l : ℂ) * E ((l : ℝ) * t)‖ ≤
      ∑ l ∈ Finset.Icc 1 N, Real.log l := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro l _
    rw [norm_mul, normE, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_natCast_nonneg l)]
  have h2 : ∑ l ∈ Finset.Icc 1 N, Real.log l ≤
      ∑ _l ∈ Finset.Icc 1 N, Real.log (N : ℝ) := by
    apply Finset.sum_le_sum
    intro l hl
    obtain ⟨hl1, hlN⟩ := Finset.mem_Icc.mp hl
    exact Real.log_le_log (by exact_mod_cast hl1) (by exact_mod_cast hlN)
  have h3 : ∑ _l ∈ Finset.Icc 1 N, Real.log (N : ℝ) =
      (N : ℝ) * Real.log (N : ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    norm_num
  exact h1.trans (h2.trans_eq h3)

/-- The log-weighted geometric sum in the classical reciprocal-distance
form, with the zero-distance case capped by `N`. -/
lemma norm_log_weighted_geometric_sum_Icc_le_recip (n N : ℕ) (t : ℝ) (hNn : N ≤ n) :
    ‖∑ l ∈ Finset.Icc 1 N, (Real.log l : ℂ) * E ((l : ℝ) * t)‖ ≤
      Real.log (n : ℝ) * typeIDistRecip N t := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hlogN : Real.log (N : ℝ) ≤ Real.log (n : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0]
      simpa using hlog
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hNn)
  have htriv := norm_log_weighted_geometric_sum_Icc_le_trivial N t
  have htriv' : ‖∑ l ∈ Finset.Icc 1 N, (Real.log l : ℂ) * E ((l : ℝ) * t)‖ ≤
      (N : ℝ) * Real.log (n : ℝ) := by
    refine htriv.trans ?_
    exact mul_le_mul_of_nonneg_left hlogN (by positivity)
  rw [typeIDistRecip]
  by_cases hdist : typeIDist t = 0
  · rw [if_pos hdist]
    simpa [mul_comm] using htriv'
  · rw [if_neg hdist]
    have hpos : 0 < typeIDist t :=
      lt_of_le_of_ne (typeIDist_nonneg t) (Ne.symm hdist)
    have hsin_lower := abs_sin_pi_mul_ge_two_mul_typeIDist t
    have hsin_ne : Real.sin (Real.pi * t) ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hsin_lower
      nlinarith
    have hdistb := norm_log_weighted_geometric_sum_Icc_le N t hsin_ne
    have hone : (1 : ℝ) / |Real.sin (Real.pi * t)| ≤ 1 / (2 * typeIDist t) :=
      one_div_le_one_div_of_le (by positivity) hsin_lower
    have hdist' : ‖∑ l ∈ Finset.Icc 1 N, (Real.log l : ℂ) * E ((l : ℝ) * t)‖ ≤
        (1 / typeIDist t) * Real.log (n : ℝ) := by
      calc
        ‖∑ l ∈ Finset.Icc 1 N, (Real.log l : ℂ) * E ((l : ℝ) * t)‖
            ≤ 2 * Real.log (N : ℝ) / |Real.sin (Real.pi * t)| := hdistb
        _ = 2 * Real.log (N : ℝ) * (1 / |Real.sin (Real.pi * t)|) := by ring
        _ ≤ 2 * Real.log (n : ℝ) * (1 / (2 * typeIDist t)) := by
          apply mul_le_mul ?_ hone (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hlogN (by norm_num)
        _ = (1 / typeIDist t) * Real.log (n : ℝ) := by ring
    by_cases hmin : (N : ℝ) ≤ 1 / typeIDist t
    · rw [min_eq_left hmin]
      simpa [mul_comm] using htriv'
    · rw [min_eq_right (le_of_not_ge hmin)]
      simpa [mul_comm] using hdist'

/-- Geometric sum in reciprocal-distance form, with the zero-distance case
capped by the length. -/
lemma norm_geometric_sum_Icc_le_recip (N : ℕ) (t : ℝ) :
    ‖∑ m ∈ Finset.Icc 1 N, E ((m : ℝ) * t)‖ ≤ typeIDistRecip N t := by
  have normE : ∀ x : ℝ, ‖E x‖ = 1 := by
    intro x
    dsimp only [E]
    simpa only [mul_comm] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
  rw [typeIDistRecip]
  by_cases hdist : typeIDist t = 0
  · rw [if_pos hdist]
    calc
      ‖∑ m ∈ Finset.Icc 1 N, E ((m : ℝ) * t)‖ ≤
          ∑ _m ∈ Finset.Icc 1 N, (1 : ℝ) := by
        refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro m _
        rw [normE]
      _ = (N : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        norm_num
  · rw [if_neg hdist]
    have hdistb := norm_geometric_sum_Icc_le_dist N t hdist
    by_cases hmin : (N : ℝ) ≤ 1 / typeIDist t
    · rw [min_eq_left hmin]
      calc
        ‖∑ m ∈ Finset.Icc 1 N, E ((m : ℝ) * t)‖ ≤
            ∑ _m ∈ Finset.Icc 1 N, (1 : ℝ) := by
          refine (norm_sum_le _ _).trans ?_
          apply Finset.sum_le_sum
          intro m _
          rw [normE]
        _ = (N : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          norm_num
    · rw [min_eq_right (le_of_not_ge hmin)]
      exact hdistb

/-- The harmonic sum is at most `1 + log K`. -/

lemma typeI_small_q_coeff_sum_le (n q U : ℕ) (hq : 0 < q) (hUn : U ≤ n) :
    ∑ d ∈ Finset.Icc 1 U,
        (if (q : ℕ) ∣ d then ((n / d : ℕ) : ℝ) * Real.log (n : ℝ)
          else 2 * (q : ℝ) * Real.log (n : ℝ)) ≤
      2 * (U : ℝ) * (q : ℝ) * Real.log (n : ℝ) +
        2 * (n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ) := by
  classical
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set s : Finset ℕ := Finset.Icc 1 U with hs
  rw [Finset.sum_ite]
  have hnon : ∑ d ∈ s.filter (fun d => ¬ (q : ℕ) ∣ d),
      2 * (q : ℝ) * Real.log (n : ℝ) ≤
        2 * (U : ℝ) * (q : ℝ) * Real.log (n : ℝ) := by
    calc
      ∑ d ∈ s.filter (fun d => ¬ (q : ℕ) ∣ d),
          2 * (q : ℝ) * Real.log (n : ℝ)
          ≤ ∑ _d ∈ s, 2 * (q : ℝ) * Real.log (n : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro d _ _
        positivity
      _ = 2 * (U : ℝ) * (q : ℝ) * Real.log (n : ℝ) := by
        rw [Finset.sum_const, hs, Nat.card_Icc, nsmul_eq_mul]
        norm_num
        ring
  have hmult : ∑ d ∈ s.filter (fun d => (q : ℕ) ∣ d),
      ((n / d : ℕ) : ℝ) * Real.log (n : ℝ) ≤
        (n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ) := by
    set t : Finset ℕ := Finset.Icc 1 (U / q) with ht
    have hbij : ∑ d ∈ s.filter (fun d => (q : ℕ) ∣ d),
        ((n / d : ℕ) : ℝ) = ∑ k ∈ t, ((n / q / k : ℕ) : ℝ) := by
      refine Finset.sum_nbij' (fun d => d / q) (fun k => q * k) ?_ ?_ ?_ ?_ ?_
      · intro d hd
        simp only [hs, Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨hd1, hdU⟩, hqd⟩ := hd
        simp only [ht, Finset.mem_Icc]
        constructor
        · exact Nat.div_pos (Nat.le_of_dvd (by omega) hqd) hq
        · exact Nat.div_le_div_right hdU
      · intro k hk
        simp only [ht, Finset.mem_Icc] at hk
        simp only [hs, Finset.mem_filter, Finset.mem_Icc]
        have hkU : q * k ≤ U := by
          rw [Nat.mul_comm]
          exact (Nat.le_div_iff_mul_le hq).mp hk.2
        exact ⟨⟨Nat.succ_le_of_lt (Nat.mul_pos hq (by omega)), hkU⟩, ⟨k, rfl⟩⟩
      · intro d hd
        simp only [hs, Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨hd1, _⟩, hqd⟩ := hd
        exact Nat.mul_div_cancel' hqd
      · intro k _
        rw [Nat.mul_comm q k, Nat.mul_div_cancel _ hq]
      · intro d hd
        simp only [hs, Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨hd1, _⟩, hqd⟩ := hd
        have hdq : d = q * (d / q) := (Nat.mul_div_cancel' hqd).symm
        conv_lhs => rw [hdq]
        rw [Nat.div_div_eq_div_mul]
    calc
      ∑ d ∈ s.filter (fun d => (q : ℕ) ∣ d), ((n / d : ℕ) : ℝ) * Real.log (n : ℝ)
          = (∑ d ∈ s.filter (fun d => (q : ℕ) ∣ d), ((n / d : ℕ) : ℝ)) *
              Real.log (n : ℝ) := by rw [Finset.sum_mul]
      _ = (∑ k ∈ t, ((n / q / k : ℕ) : ℝ)) * Real.log (n : ℝ) := by rw [hbij]
      _ ≤ ((∑ k ∈ t, (n : ℝ) / q / (k : ℝ))) * Real.log (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        apply Finset.sum_le_sum
        intro k hk
        calc ((n / q / k : ℕ) : ℝ) ≤ ((n / q : ℕ) : ℝ) / (k : ℝ) := Nat.cast_div_le
          _ ≤ (n : ℝ) / q / (k : ℝ) := by
              exact div_le_div_of_nonneg_right Nat.cast_div_le (by positivity)
      _ = ((n : ℝ) / q * (∑ k ∈ t, (1 : ℝ) / (k : ℝ))) * Real.log (n : ℝ) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ ((n : ℝ) / q * (1 + Real.log ((U / q : ℕ) : ℝ))) * Real.log (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_inv_Icc_le_one_add_log (U / q)
      _ ≤ ((n : ℝ) / q * (1 + Real.log (n : ℝ))) * Real.log (n : ℝ) := by
        have hUq : U / q ≤ U := Nat.div_le_self _ _
        have hlog_le : Real.log ((U / q : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
          rcases Nat.eq_zero_or_pos (U / q) with h0 | hpos
          · rw [h0]; simpa using hlog
          · exact Real.log_le_log (by exact_mod_cast hpos)
              (by exact_mod_cast le_trans hUq hUn)
        have h1 : 1 + Real.log ((U / q : ℕ) : ℝ) ≤ 1 + Real.log (n : ℝ) := by linarith
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) le_rfl hlog (by positivity)
      _ = (n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ) := by ring
  have htot := add_le_add hmult hnon
  calc
    ∑ d ∈ s.filter (fun d => (q : ℕ) ∣ d), ((n / d : ℕ) : ℝ) * Real.log (n : ℝ) +
        ∑ d ∈ s.filter (fun d => ¬ (q : ℕ) ∣ d), 2 * (q : ℝ) * Real.log (n : ℝ)
        ≤ (n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ) +
          2 * (U : ℝ) * (q : ℝ) * Real.log (n : ℝ) := htot
    _ = 2 * (U : ℝ) * (q : ℝ) * Real.log (n : ℝ) +
        (n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ) := by ring
    _ ≤ 2 * (U : ℝ) * (q : ℝ) * Real.log (n : ℝ) +
        2 * (n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ) := by
      have hnq : 0 ≤ (n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ) :=
        div_nonneg (mul_nonneg (mul_nonneg (by positivity) hlog) (by linarith)) hqR.le
      have hX : (n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ) ≤
          2 * (n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ) := by
        calc (n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ)
            ≤ 2 * ((n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ)) :=
              le_mul_of_one_le_left hnq (by norm_num)
          _ = 2 * (n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ) := by ring
      exact add_le_add_right hX _


/-- Type-I second term on a major arc, uniformly in `q` (in particular for the
small-denominator range `q <= U`, where multiples of `q` must be treated
trivially). -/
theorem norm_expSum_low_mu_mul_log_le_majorArc_small_q (n q U a : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hU1 : 1 ≤ U) (hUn : U ≤ n)
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * (U:ℝ))) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
        ((a:ℝ)/(q:ℝ) + β)‖ ≤
      2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) +
        2 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ) := by
  rw [expSum_low_mu_mul_log_eq n U ((a:ℝ)/(q:ℝ) + β)]
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have harg : ∀ d l : ℕ, ((d * l : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β) =
      (l : ℝ) * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)) := by
    intro d l
    push_cast
    ring
  have hstep : ‖∑ d ∈ Finset.Icc 1 U, ((μ : ArithmeticFunction ℝ) d : ℂ) *
        ∑ l ∈ Finset.Icc 1 (n / d),
          (ArithmeticFunction.log l : ℂ) *
            E (((d * l : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ ≤
      ∑ d ∈ Finset.Icc 1 U,
        (if (q : ℕ) ∣ d then ((n / d : ℕ) : ℝ) * Real.log (n : ℝ)
          else 2 * (q : ℝ) * Real.log (n : ℝ)) := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro d hd
    obtain ⟨hd1, hdU⟩ := Finset.mem_Icc.mp hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hμd : |(μ : ArithmeticFunction ℝ) d| ≤ 1 := by
      have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
        ArithmeticFunction.abs_moebius_le_one
      have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast h
      simpa using h'
    have hmain : ‖∑ l ∈ Finset.Icc 1 (n / d),
          (ArithmeticFunction.log l : ℂ) *
            E (((d * l : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ ≤
        (if (q : ℕ) ∣ d then ((n / d : ℕ) : ℝ) * Real.log (n : ℝ)
          else 2 * (q : ℝ) * Real.log (n : ℝ)) := by
      by_cases hdiv : (q : ℕ) ∣ d
      · rw [if_pos hdiv]
        simp_rw [harg d]
        refine (norm_log_weighted_geometric_sum_Icc_le_trivial (n / d)
          ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β))).trans ?_
        have hlogN : Real.log (((n / d : ℕ)) : ℝ) ≤ Real.log (n : ℝ) := by
          rcases Nat.eq_zero_or_pos (n / d) with h0 | hpos
          · rw [h0]
            simpa using hlog
          · exact Real.log_le_log (by exact_mod_cast hpos)
              (by exact_mod_cast Nat.div_le_self n d)
        exact mul_le_mul_of_nonneg_left hlogN (by positivity)
      · rw [if_neg hdiv]
        have hsine := abs_sin_pi_mul_majorArc_ge_pointwise q U a d β hq hcop hU1 hd1 hdU hdiv hβ
        have hspos : (0:ℝ) <
            |Real.sin (Real.pi * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)))| :=
          lt_of_lt_of_le (by positivity : (0:ℝ) < 1/(q:ℝ)) hsine
        have hsin_ne : Real.sin (Real.pi * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β))) ≠ 0 :=
          abs_pos.mp hspos
        simp_rw [harg d]
        refine (norm_log_weighted_geometric_sum_Icc_le (n / d)
          ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)) hsin_ne).trans ?_
        have hs' : (1:ℝ) ≤
            |Real.sin (Real.pi * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)))| * (q:ℝ) :=
          (div_le_iff₀ hqR).mp hsine
        have hunit : (1:ℝ) /
            |Real.sin (Real.pi * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)))| ≤ (q:ℝ) := by
          rw [div_le_iff₀ hspos]
          simpa [mul_comm] using hs'
        have hlogN : Real.log (((n / d : ℕ)) : ℝ) ≤ Real.log (n : ℝ) := by
          rcases Nat.eq_zero_or_pos (n / d) with h0 | hpos
          · rw [h0]
            simpa using hlog
          · exact Real.log_le_log (by exact_mod_cast hpos)
              (by exact_mod_cast Nat.div_le_self n d)
        calc
          2 * Real.log (((n / d : ℕ)) : ℝ) /
              |Real.sin (Real.pi * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)))|
              ≤ 2 * Real.log (n : ℝ) /
                |Real.sin (Real.pi * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)))| := by
            apply div_le_div_of_nonneg_right _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left hlogN (by norm_num)
          _ = 2 * Real.log (n : ℝ) * (1 /
                |Real.sin (Real.pi * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)))|) := by
            rw [div_eq_mul_one_div]
          _ ≤ 2 * Real.log (n : ℝ) * (q:ℝ) :=
            mul_le_mul_of_nonneg_left hunit (by positivity)
          _ = 2 * (q:ℝ) * Real.log (n : ℝ) := by ring
    calc
      |(μ : ArithmeticFunction ℝ) d| * ‖∑ l ∈ Finset.Icc 1 (n / d),
          (ArithmeticFunction.log l : ℂ) *
            E (((d * l : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖
          ≤ 1 * ‖∑ l ∈ Finset.Icc 1 (n / d),
              (ArithmeticFunction.log l : ℂ) *
                E (((d * l : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ :=
            mul_le_mul_of_nonneg_right hμd (norm_nonneg _)
      _ = ‖∑ l ∈ Finset.Icc 1 (n / d),
            (ArithmeticFunction.log l : ℂ) *
              E (((d * l : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ := one_mul _
      _ ≤ (if (q : ℕ) ∣ d then ((n / d : ℕ) : ℝ) * Real.log (n : ℝ)
            else 2 * (q : ℝ) * Real.log (n : ℝ)) := hmain
  exact hstep.trans (typeI_small_q_coeff_sum_le n q U hq hUn)

/-- Coefficient sum for the truncated second Type-I term. -/
lemma typeI_trunc_coeff_sum_le (n q U M : ℕ) (hq : 0 < q) (hUn : U ≤ n)
    (hM1 : 1 ≤ M) (hMU : M ≤ U) :
    (∑ d ∈ Finset.Icc 1 U,
        (if (q : ℕ) ∣ d then ((n / d : ℕ) : ℝ) * Real.log (n : ℝ)
          else if d ≤ M then 2 * (q : ℝ) * Real.log (n : ℝ)
          else ((n / d : ℕ) : ℝ) * Real.log (n : ℝ)))
      ≤ 2 * (q : ℝ) * (M : ℝ) * Real.log (n : ℝ) +
          (n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ) +
          (n : ℝ) * Real.log (n : ℝ) * (Real.log (U : ℝ) - Real.log (M : ℝ)) := by
  classical
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set s : Finset ℕ := Finset.Icc 1 U with hs
  set X : ℕ → ℝ := fun d => ((n / d : ℕ) : ℝ) * Real.log (n : ℝ) with hXdef
  set Y : ℝ := 2 * (q : ℝ) * Real.log (n : ℝ) with hYdef
  have hXnon : ∀ d, 0 ≤ X d := fun d => by positivity
  have hYnon : 0 ≤ Y := by positivity
  -- Multiples of `q` contribute the reciprocal tail.
  have hmult : (∑ d ∈ s, (if (q : ℕ) ∣ d then X d else 0)) ≤
      (n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ) := by
    rw [← Finset.sum_filter]
    set t : Finset ℕ := Finset.Icc 1 (U / q) with ht
    have hbij : ∑ d ∈ s.filter (fun d => (q : ℕ) ∣ d),
        ((n / d : ℕ) : ℝ) = ∑ k ∈ t, ((n / q / k : ℕ) : ℝ) := by
      refine Finset.sum_nbij' (fun d => d / q) (fun k => q * k) ?_ ?_ ?_ ?_ ?_
      · intro d hd
        simp only [hs, Finset.mem_filter, Finset.mem_Icc] at hd ⊢
        obtain ⟨⟨hd1, hdU⟩, hqd⟩ := hd
        simp only [ht, Finset.mem_Icc]
        constructor
        · exact Nat.div_pos (Nat.le_of_dvd (by omega) hqd) hq
        · exact Nat.div_le_div_right hdU
      · intro k hk
        simp only [ht, Finset.mem_Icc] at hk
        simp only [hs, Finset.mem_filter, Finset.mem_Icc]
        have hkU : q * k ≤ U := by
          rw [Nat.mul_comm]
          exact (Nat.le_div_iff_mul_le hq).mp hk.2
        exact ⟨⟨Nat.succ_le_of_lt (Nat.mul_pos hq (by omega)), hkU⟩, ⟨k, rfl⟩⟩
      · intro d hd
        simp only [hs, Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨hd1, _⟩, hqd⟩ := hd
        exact Nat.mul_div_cancel' hqd
      · intro k _
        rw [Nat.mul_comm q k, Nat.mul_div_cancel _ hq]
      · intro d hd
        simp only [hs, Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨hd1, _⟩, hqd⟩ := hd
        have hdq : d = q * (d / q) := (Nat.mul_div_cancel' hqd).symm
        conv_lhs => rw [hdq]
        rw [Nat.div_div_eq_div_mul]
    calc
      ∑ d ∈ s.filter (fun d => (q : ℕ) ∣ d), X d
          = (∑ d ∈ s.filter (fun d => (q : ℕ) ∣ d), ((n / d : ℕ) : ℝ)) *
              Real.log (n : ℝ) := by
        rw [hXdef]
        rw [Finset.sum_mul]
      _ = (∑ k ∈ t, ((n / q / k : ℕ) : ℝ)) * Real.log (n : ℝ) := by rw [hbij]
      _ ≤ ((∑ k ∈ t, (n : ℝ) / (q : ℝ) / (k : ℝ))) * Real.log (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        apply Finset.sum_le_sum
        intro k hk
        calc ((n / q / k : ℕ) : ℝ) ≤ ((n / q : ℕ) : ℝ) / (k : ℝ) := Nat.cast_div_le
          _ ≤ (n : ℝ) / (q : ℝ) / (k : ℝ) :=
              div_le_div_of_nonneg_right Nat.cast_div_le (by positivity)
      _ = ((n : ℝ) / (q : ℝ) * (∑ k ∈ t, (1 : ℝ) / (k : ℝ))) * Real.log (n : ℝ) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ ((n : ℝ) / (q : ℝ) * (1 + Real.log ((U / q : ℕ) : ℝ))) *
            Real.log (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_inv_Icc_le_one_add_log (U / q)
      _ ≤ ((n : ℝ) / (q : ℝ) * (1 + Real.log (n : ℝ))) * Real.log (n : ℝ) := by
        have hUq : U / q ≤ U := Nat.div_le_self _ _
        have hlog_le : Real.log ((U / q : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
          rcases Nat.eq_zero_or_pos (U / q) with h0 | hpos
          · rw [h0]; simpa using hlog
          · exact Real.log_le_log (by exact_mod_cast hpos)
              (by exact_mod_cast le_trans hUq hUn)
        have h1 : 1 + Real.log ((U / q : ℕ) : ℝ) ≤ 1 + Real.log (n : ℝ) := by linarith
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) le_rfl hlog (by positivity)
      _ = (n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ) := by ring
  -- Pairs `d ≤ M` contribute `2 q log n` each.
  have hsmall : (∑ d ∈ s, (if d ≤ M then Y else 0)) ≤ 2 * (q : ℝ) * (M : ℝ) *
      Real.log (n : ℝ) := by
    rw [← Finset.sum_filter]
    have hsub : s.filter (fun d => d ≤ M) ⊆ Finset.Icc 1 M := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      exact Finset.mem_Icc.mpr ⟨hd.1.1, hd.2⟩
    calc
      ∑ d ∈ s.filter (fun d => d ≤ M), Y
          ≤ ∑ _d ∈ Finset.Icc 1 M, Y := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro d _ _
        exact hYnon
      _ = (M : ℝ) * Y := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        norm_num
      _ = 2 * (q : ℝ) * (M : ℝ) * Real.log (n : ℝ) := by rw [hYdef]; ring
  -- Pairs `d > M` contribute the reciprocal tail.
  have htail : (∑ d ∈ s, (if M < d then X d else 0)) ≤
      (n : ℝ) * Real.log (n : ℝ) * (Real.log (U : ℝ) - Real.log (M : ℝ)) := by
    rw [← Finset.sum_filter]
    have hset : s.filter (fun d => M < d) = Finset.Icc (M + 1) U := by
      ext d
      simp only [hs, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨-, hdU⟩, hd⟩
        exact ⟨hd, hdU⟩
      · rintro ⟨hd, hdU⟩
        exact ⟨⟨Nat.le_trans (Nat.le_add_left 1 M) hd, hdU⟩, hd⟩
    rw [hset]
    calc
      ∑ d ∈ Finset.Icc (M + 1) U, X d
          ≤ ∑ d ∈ Finset.Icc (M + 1) U,
              (n : ℝ) * Real.log (n : ℝ) * (1 / (d : ℝ)) := by
        apply Finset.sum_le_sum
        intro d _
        calc ((n / d : ℕ) : ℝ) * Real.log (n : ℝ)
            ≤ ((n : ℝ) / (d : ℝ)) * Real.log (n : ℝ) :=
              mul_le_mul_of_nonneg_right Nat.cast_div_le hlog
          _ = (n : ℝ) * Real.log (n : ℝ) * (1 / (d : ℝ)) := by ring
      _ = (n : ℝ) * Real.log (n : ℝ) *
            ∑ d ∈ Finset.Icc (M + 1) U, (1 / (d : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ (n : ℝ) * Real.log (n : ℝ) *
            (Real.log (U : ℝ) - Real.log (M : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (sum_inv_Icc_succ_le_log M U hM1 hMU)
        positivity
  have hf : ∀ d : ℕ, (if (q : ℕ) ∣ d then X d
        else if d ≤ M then Y else X d)
      ≤ (if (q : ℕ) ∣ d then X d else 0) + (if d ≤ M then Y else 0) +
        (if M < d then X d else 0) := by
    intro d
    by_cases hq' : (q : ℕ) ∣ d
    · by_cases hdM : d ≤ M
      · simp only [if_pos hq', if_pos hdM, if_neg (not_lt.mpr hdM)]
        linarith [hYnon]
      · have hlt : M < d := Nat.lt_of_not_le hdM
        simp only [if_pos hq', if_neg hdM, if_pos hlt]
        linarith [hXnon d]
    · by_cases hdM : d ≤ M
      · simp only [if_neg hq', if_pos hdM, if_neg (not_lt.mpr hdM)]
        linarith
      · have hlt : M < d := Nat.lt_of_not_le hdM
        simp only [if_neg hq', if_neg hdM, if_pos hlt]
        linarith
  calc
    (∑ d ∈ Finset.Icc 1 U,
        (if (q : ℕ) ∣ d then X d
          else if d ≤ M then Y else X d))
        ≤ ∑ d ∈ s, ((if (q : ℕ) ∣ d then X d else 0) + (if d ≤ M then Y else 0) +
            (if M < d then X d else 0)) := by
      rw [hs]
      exact Finset.sum_le_sum (fun d _ => hf d)
    _ = (∑ d ∈ s, (if (q : ℕ) ∣ d then X d else 0)) +
          (∑ d ∈ s, (if d ≤ M then Y else 0)) +
          (∑ d ∈ s, (if M < d then X d else 0)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ 2 * (q : ℝ) * (M : ℝ) * Real.log (n : ℝ) +
          (n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ) +
          (n : ℝ) * Real.log (n : ℝ) * (Real.log (U : ℝ) - Real.log (M : ℝ)) := by
      linarith [hmult, hsmall, htail]

/-- Type-I second term with threshold `M`: for `d ≤ M` the sine separation
gives `2q log n`, and the range `d > M` is estimated trivially. -/
theorem norm_expSum_low_mu_mul_log_le_truncated (n q U M a : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hU1 : 1 ≤ U) (hUn : U ≤ n)
    (hM1 : 1 ≤ M) (hMU : M ≤ U)
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * (M:ℝ))) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
        ((a:ℝ)/(q:ℝ) + β)‖ ≤
      2 * (q : ℝ) * (M : ℝ) * Real.log (n : ℝ) +
          (n : ℝ) * Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) / (q : ℝ) +
          (n : ℝ) * Real.log (n : ℝ) * (Real.log (U : ℝ) - Real.log (M : ℝ)) := by
  rw [expSum_low_mu_mul_log_eq n U ((a:ℝ)/(q:ℝ) + β)]
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have harg : ∀ d l : ℕ, ((d * l : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β) =
      (l : ℝ) * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)) := by
    intro d l
    push_cast
    ring
  have hstep : ‖∑ d ∈ Finset.Icc 1 U, ((μ : ArithmeticFunction ℝ) d : ℂ) *
        ∑ l ∈ Finset.Icc 1 (n / d),
          (ArithmeticFunction.log l : ℂ) *
            E (((d * l : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ ≤
      ∑ d ∈ Finset.Icc 1 U,
        (if (q : ℕ) ∣ d then ((n / d : ℕ) : ℝ) * Real.log (n : ℝ)
          else if d ≤ M then 2 * (q : ℝ) * Real.log (n : ℝ)
          else ((n / d : ℕ) : ℝ) * Real.log (n : ℝ)) := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro d hd
    obtain ⟨hd1, hdU⟩ := Finset.mem_Icc.mp hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hμd : |(μ : ArithmeticFunction ℝ) d| ≤ 1 := by
      have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
        ArithmeticFunction.abs_moebius_le_one
      have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast h
      simpa using h'
    have hmain : ‖∑ l ∈ Finset.Icc 1 (n / d),
          (ArithmeticFunction.log l : ℂ) *
            E (((d * l : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ ≤
        (if (q : ℕ) ∣ d then ((n / d : ℕ) : ℝ) * Real.log (n : ℝ)
          else if d ≤ M then 2 * (q : ℝ) * Real.log (n : ℝ)
          else ((n / d : ℕ) : ℝ) * Real.log (n : ℝ)) := by
      by_cases hdiv : (q : ℕ) ∣ d
      · rw [if_pos hdiv]
        simp_rw [harg d]
        refine (norm_log_weighted_geometric_sum_Icc_le_trivial (n / d)
          ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β))).trans ?_
        have hlogN : Real.log (((n / d : ℕ)) : ℝ) ≤ Real.log (n : ℝ) := by
          rcases Nat.eq_zero_or_pos (n / d) with h0 | hpos
          · rw [h0]
            simpa using hlog
          · exact Real.log_le_log (by exact_mod_cast hpos)
              (by exact_mod_cast Nat.div_le_self n d)
        exact mul_le_mul_of_nonneg_left hlogN (by positivity)
      · rw [if_neg hdiv]
        by_cases hdM : d ≤ M
        · rw [if_pos hdM]
          have hsine := abs_sin_pi_mul_majorArc_ge_pointwise q M a d β
            hq hcop hM1 hd1 hdM hdiv hβ
          have hspos : (0:ℝ) <
              |Real.sin (Real.pi * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)))| :=
            lt_of_lt_of_le (by positivity : (0:ℝ) < 1/(q:ℝ)) hsine
          have hsin_ne : Real.sin (Real.pi * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β))) ≠ 0 :=
            abs_pos.mp hspos
          simp_rw [harg d]
          refine (norm_log_weighted_geometric_sum_Icc_le (n / d)
            ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)) hsin_ne).trans ?_
          have hs' : (1:ℝ) ≤
              |Real.sin (Real.pi * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)))| * (q:ℝ) :=
            (div_le_iff₀ hqR).mp hsine
          have hunit : (1:ℝ) /
              |Real.sin (Real.pi * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)))| ≤ (q:ℝ) := by
            rw [div_le_iff₀ hspos]
            simpa [mul_comm] using hs'
          have hlogN : Real.log (((n / d : ℕ)) : ℝ) ≤ Real.log (n : ℝ) := by
            rcases Nat.eq_zero_or_pos (n / d) with h0 | hpos
            · rw [h0]
              simpa using hlog
            · exact Real.log_le_log (by exact_mod_cast hpos)
                (by exact_mod_cast Nat.div_le_self n d)
          calc
            2 * Real.log (((n / d : ℕ)) : ℝ) /
                |Real.sin (Real.pi * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)))|
                ≤ 2 * Real.log (n : ℝ) /
                  |Real.sin (Real.pi * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)))| := by
              apply div_le_div_of_nonneg_right _ (abs_nonneg _)
              exact mul_le_mul_of_nonneg_left hlogN (by norm_num)
            _ = 2 * Real.log (n : ℝ) * (1 /
                  |Real.sin (Real.pi * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)))|) := by
              rw [div_eq_mul_one_div]
            _ ≤ 2 * Real.log (n : ℝ) * (q:ℝ) :=
              mul_le_mul_of_nonneg_left hunit (by positivity)
            _ = 2 * (q:ℝ) * Real.log (n : ℝ) := by ring
        · rw [if_neg hdM]
          simp_rw [harg d]
          refine (norm_log_weighted_geometric_sum_Icc_le_trivial (n / d)
            ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β))).trans ?_
          have hlogN : Real.log (((n / d : ℕ)) : ℝ) ≤ Real.log (n : ℝ) := by
            rcases Nat.eq_zero_or_pos (n / d) with h0 | hpos
            · rw [h0]
              simpa using hlog
            · exact Real.log_le_log (by exact_mod_cast hpos)
                (by exact_mod_cast Nat.div_le_self n d)
          exact mul_le_mul_of_nonneg_left hlogN (by positivity)
    calc
      |(μ : ArithmeticFunction ℝ) d| * ‖∑ l ∈ Finset.Icc 1 (n / d),
          (ArithmeticFunction.log l : ℂ) *
            E (((d * l : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖
          ≤ 1 * ‖∑ l ∈ Finset.Icc 1 (n / d),
              (ArithmeticFunction.log l : ℂ) *
                E (((d * l : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ :=
            mul_le_mul_of_nonneg_right hμd (norm_nonneg _)
      _ = ‖∑ l ∈ Finset.Icc 1 (n / d),
            (ArithmeticFunction.log l : ℂ) *
              E (((d * l : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ := one_mul _
      _ ≤ (if (q : ℕ) ∣ d then ((n / d : ℕ) : ℝ) * Real.log (n : ℝ)
          else if d ≤ M then 2 * (q : ℝ) * Real.log (n : ℝ)
          else ((n / d : ℕ) : ℝ) * Real.log (n : ℝ)) := hmain
  exact hstep.trans (typeI_trunc_coeff_sum_le n q U M hq hUn hM1 hMU)


lemma double_sum_vonMangoldt_div_le (U q : ℕ) (hq : 0 < q) :
    ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        (if (q : ℕ) ∣ d * e then ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)
          else 0) ≤
      Real.log (((U * U : ℕ)) : ℝ) *
        ((1 / (q : ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))) := by
  classical
  set s : Finset (ℕ × ℕ) := (Finset.Icc 1 U) ×ˢ (Finset.Icc 1 U) with hs
  set F : ℕ × ℕ → ℝ := fun p =>
    if (q : ℕ) ∣ p.1 * p.2 then ((Λ : ArithmeticFunction ℝ) p.2) / ((p.1 * p.2 : ℕ) : ℝ)
      else 0 with hF
  have hprod : ∑ p ∈ s, F p =
      ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        (if (q : ℕ) ∣ d * e then ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)
          else 0) := by
    rw [hs, Finset.sum_product]
  rw [← hprod]
  have hmaps : ∀ p ∈ s, p.1 * p.2 ∈ Finset.Icc 1 (U * U) := by
    intro p hp
    rw [hs, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    obtain ⟨⟨hp11, hp1U⟩, ⟨hp21, hp2U⟩⟩ := hp
    rw [Finset.mem_Icc]
    exact ⟨Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega)),
      Nat.mul_le_mul hp1U hp2U⟩
  have hfib := Finset.sum_fiberwise_of_maps_to (s := s) (t := Finset.Icc 1 (U * U))
    (g := fun p : ℕ × ℕ => p.1 * p.2) hmaps F
  rw [← hfib]
  have hantidiag : ∀ k : ℕ, ∑ p ∈ k.divisorsAntidiagonal,
      ((Λ : ArithmeticFunction ℝ) p.2) = Real.log (k : ℝ) := by
    intro k
    rw [Nat.sum_divisorsAntidiagonal' (fun a b => (Λ : ArithmeticFunction ℝ) b)]
    have h := ArithmeticFunction.vonMangoldt_sum (n := k)
    rw [← h]
  have hfiber : ∀ k ∈ Finset.Icc 1 (U * U),
      ∑ p ∈ s.filter (fun p => p.1 * p.2 = k), F p ≤
        if (q : ℕ) ∣ k then Real.log (k : ℝ) / (k : ℝ) else 0 := by
    intro k hk
    obtain ⟨hk1, hkU⟩ := Finset.mem_Icc.mp hk
    have hkne : k ≠ 0 := by omega
    by_cases hqk : (q : ℕ) ∣ k
    · rw [if_pos hqk]
      calc
        ∑ p ∈ s.filter (fun p => p.1 * p.2 = k), F p
            ≤ ∑ p ∈ s.filter (fun p => p.1 * p.2 = k),
                ((Λ : ArithmeticFunction ℝ) p.2) / (k : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          rw [Finset.mem_filter] at hp
          obtain ⟨hps, hpk⟩ := hp
          simp only [hF]
          rw [if_pos (by rw [hpk]; exact hqk), hpk]
        _ ≤ ∑ p ∈ k.divisorsAntidiagonal,
              ((Λ : ArithmeticFunction ℝ) p.2) / (k : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rw [Finset.mem_filter] at hp
            rw [Nat.mem_divisorsAntidiagonal]
            exact ⟨hp.2, hkne⟩
          · intro p _ _
            positivity
        _ = (∑ p ∈ k.divisorsAntidiagonal,
              ((Λ : ArithmeticFunction ℝ) p.2)) / (k : ℝ) := by
          rw [Finset.sum_div]
        _ = Real.log (k : ℝ) / (k : ℝ) := by rw [hantidiag]
    · rw [if_neg hqk]
      apply Finset.sum_nonpos
      intro p hp
      rw [Finset.mem_filter] at hp
      simp only [hF]
      rw [if_neg (by rw [hp.2]; exact hqk)]
  calc
    ∑ k ∈ Finset.Icc 1 (U * U),
        ∑ p ∈ s.filter (fun p => p.1 * p.2 = k), F p
        ≤ ∑ k ∈ Finset.Icc 1 (U * U),
            (if (q : ℕ) ∣ k then Real.log (k : ℝ) / (k : ℝ) else 0) :=
      Finset.sum_le_sum hfiber
    _ ≤ ∑ k ∈ Finset.Icc 1 (U * U),
          (if (q : ℕ) ∣ k then Real.log ((U * U : ℕ) : ℝ) / (k : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hqk : (q : ℕ) ∣ k
      · rw [if_pos hqk, if_pos hqk]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hk1 : 0 < k := by
          have := (Finset.mem_Icc.mp hk).1
          omega
        exact Real.log_le_log (by exact_mod_cast hk1)
          (by exact_mod_cast (Finset.mem_Icc.mp hk).2)
      · rw [if_neg hqk, if_neg hqk]
    _ = Real.log ((U * U : ℕ) : ℝ) *
          ∑ k ∈ Finset.Icc 1 (U * U), (if (q : ℕ) ∣ k then 1 / (k : ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : (q : ℕ) ∣ k
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h]; ring
    _ = Real.log ((U * U : ℕ) : ℝ) *
          ∑ k ∈ (Finset.Icc 1 (U * U)).filter (fun k => (q : ℕ) ∣ k), 1 / (k : ℝ) := by
      rw [Finset.sum_filter]
    _ ≤ Real.log ((U * U : ℕ) : ℝ) *
          ((1 / (q : ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg (U * U))
      exact sum_inv_filter_le (U * U) q hq


/-- Count of pairs `d,e ≤ U` with `d * e ≤ M`, weighted by `log n`. -/
lemma sum_card_mul_le (M U : ℕ) :
    (∑ d ∈ Finset.Icc 1 U,
        (((Finset.Icc 1 U).filter (fun e => d * e ≤ M)).card : ℝ))
      ≤ (M : ℝ) * (1 + Real.log (U : ℝ)) := by
  classical
  have hstep : (∑ d ∈ Finset.Icc 1 U,
        (((Finset.Icc 1 U).filter (fun e => d * e ≤ M)).card : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 U, ((M / d : ℕ) : ℝ) := by
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdpos : 0 < d := by omega
    have hsub : (Finset.Icc 1 U).filter (fun e => d * e ≤ M) ⊆
        Finset.Icc 1 (M / d) := by
      intro e he
      rw [Finset.mem_filter, Finset.mem_Icc] at he
      obtain ⟨⟨he1, _heU⟩, hde⟩ := he
      rw [Finset.mem_Icc]
      exact ⟨he1, (Nat.le_div_iff_mul_le hdpos).mpr (by simpa [Nat.mul_comm] using hde)⟩
    calc
      (((Finset.Icc 1 U).filter (fun e => d * e ≤ M)).card : ℝ)
          ≤ ((Finset.Icc 1 (M / d)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ = ((M / d : ℕ) : ℝ) := by
        rw [Nat.card_Icc]
        norm_num
  calc
    (∑ d ∈ Finset.Icc 1 U,
        (((Finset.Icc 1 U).filter (fun e => d * e ≤ M)).card : ℝ))
        ≤ ∑ d ∈ Finset.Icc 1 U, ((M / d : ℕ) : ℝ) := hstep
    _ ≤ ∑ d ∈ Finset.Icc 1 U, (M : ℝ) / (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      exact Nat.cast_div_le
    _ = (M : ℝ) * ∑ d ∈ Finset.Icc 1 U, (1 : ℝ) / (d : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ ≤ (M : ℝ) * (1 + Real.log (U : ℝ)) := by
      apply mul_le_mul_of_nonneg_left (sum_inv_Icc_le_one_add_log U) (by positivity)

/-- Total reciprocal von Mangoldt sum over `d,e ≤ U`. -/
lemma sum_div_vonMangoldt_le (n U : ℕ) (hUn : U ≤ n) :
    ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)
      ≤ Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) ^ 2 := by
  classical
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hlogU : Real.log (U : ℝ) ≤ Real.log (n : ℝ) := by
    rcases Nat.eq_zero_or_pos U with h0 | hpos
    · rw [h0]
      simpa using hlog
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hUn)
  have hfac : (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)) =
      (∑ d ∈ Finset.Icc 1 U, (1 : ℝ) / (d : ℝ)) *
        (∑ e ∈ Finset.Icc 1 U,
          ((Λ : ArithmeticFunction ℝ) e) / (e : ℝ)) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro e _
    push_cast
    field_simp
  rw [hfac]
  have hd : (∑ d ∈ Finset.Icc 1 U, (1 : ℝ) / (d : ℝ)) ≤
      1 + Real.log (U : ℝ) := sum_inv_Icc_le_one_add_log U
  have hd' : (∑ d ∈ Finset.Icc 1 U, (1 : ℝ) / (d : ℝ)) ≤
      1 + Real.log (n : ℝ) := by linarith
  have he : (∑ e ∈ Finset.Icc 1 U,
        ((Λ : ArithmeticFunction ℝ) e) / (e : ℝ)) ≤
      Real.log (n : ℝ) * (1 + Real.log (U : ℝ)) := by
    calc
      (∑ e ∈ Finset.Icc 1 U,
          ((Λ : ArithmeticFunction ℝ) e) / (e : ℝ))
          ≤ ∑ e ∈ Finset.Icc 1 U, Real.log (n : ℝ) * (1 / (e : ℝ)) := by
        apply Finset.sum_le_sum
        intro e he'
        obtain ⟨he1, heU⟩ := Finset.mem_Icc.mp he'
        have hΛ : ((Λ : ArithmeticFunction ℝ) e) ≤ Real.log (n : ℝ) := by
          exact (ArithmeticFunction.vonMangoldt_le_log).trans
            (Real.log_le_log (by exact_mod_cast he1)
              (by exact_mod_cast le_trans heU hUn))
        have hepos : 0 < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
        rw [show ((Λ : ArithmeticFunction ℝ) e) / (e : ℝ) =
            ((Λ : ArithmeticFunction ℝ) e) * (1 / (e : ℝ)) by ring]
        exact mul_le_mul_of_nonneg_right hΛ (by positivity)
      _ = Real.log (n : ℝ) * ∑ e ∈ Finset.Icc 1 U, (1 : ℝ) / (e : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ Real.log (n : ℝ) * (1 + Real.log (U : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_inv_Icc_le_one_add_log U) hlog
  have he' : (∑ e ∈ Finset.Icc 1 U,
        ((Λ : ArithmeticFunction ℝ) e) / (e : ℝ)) ≤
      Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) := by
    exact he.trans (mul_le_mul_of_nonneg_left (by linarith) hlog)
  have hdnon : 0 ≤ ∑ d ∈ Finset.Icc 1 U, (1 : ℝ) / (d : ℝ) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have henon : 0 ≤ ∑ e ∈ Finset.Icc 1 U,
      ((Λ : ArithmeticFunction ℝ) e) / (e : ℝ) :=
    Finset.sum_nonneg (fun _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
  calc
    (∑ d ∈ Finset.Icc 1 U, (1 : ℝ) / (d : ℝ)) *
        (∑ e ∈ Finset.Icc 1 U,
          ((Λ : ArithmeticFunction ℝ) e) / (e : ℝ))
        ≤ (1 + Real.log (n : ℝ)) *
            (Real.log (n : ℝ) * (1 + Real.log (n : ℝ))) :=
      mul_le_mul hd' he' henon (by positivity)
    _ = Real.log (n : ℝ) * (1 + Real.log (n : ℝ)) ^ 2 := by ring


/-- Tail harmonic bound with the natural-number threshold `M / U`:
`∑_{d = M/U + 1}^{U} 1/d ≤ 1 + log(U²/M)` for `U ≤ M ≤ U²`. -/
lemma sum_inv_Icc_div_succ_le (M U : ℕ) (hM1 : 1 ≤ M) (hU1 : 1 ≤ U)
    (hMU : M ≤ U * U) :
    ∑ d ∈ Finset.Icc (M / U + 1) U, (1 : ℝ) / (d : ℝ)
      ≤ 1 + Real.log (((U:ℝ) * (U:ℝ)) / (M:ℝ)) := by
  classical
  have hUpos : (0:ℝ) < (U:ℝ) := by exact_mod_cast (by omega : 1 ≤ U)
  have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
  rcases Nat.eq_zero_or_pos (M / U) with h0 | hK
  · -- `M / U = 0`, so `M < U` and the range is `{1, ..., U}`
    have hMlt : M < U := by
      by_contra h
      have hUM : U ≤ M := by omega
      have : 1 ≤ M / U := Nat.one_le_div_iff (by omega : 0 < U) |>.mpr hUM
      omega
    have hIcc : Finset.Icc (M / U + 1) U = Finset.Icc 1 U := by rw [h0]
    rw [hIcc]
    have hsum := sum_inv_Icc_le_one_add_log U
    have hlogU : Real.log (U:ℝ) ≤ Real.log (((U:ℝ) * (U:ℝ)) / (M:ℝ)) := by
      apply Real.log_le_log (by positivity)
      rw [le_div_iff₀ hMpos]
      have hMle : (M:ℝ) ≤ (U:ℝ) := by exact_mod_cast le_of_lt hMlt
      nlinarith
    linarith
  · -- `1 ≤ M / U`
    have hkU : M / U ≤ U := Nat.div_le_of_le_mul hMU
    have hsum := sum_inv_Icc_succ_le_log (M / U) U hK hkU
    have hMle : (M:ℝ) ≤ (U:ℝ) * ((M / U : ℕ):ℝ) + (U:ℝ) := by
      have hmod : M % U < U := Nat.mod_lt M (by omega)
      have hdecomp : M = U * (M / U) + M % U := (Nat.div_add_mod M U).symm
      have hle : M ≤ U * (M / U) + U := by
        calc M = U * (M / U) + M % U := hdecomp
          _ ≤ U * (M / U) + U := Nat.add_le_add_left (le_of_lt hmod) _
      calc (M:ℝ) ≤ ((U * (M / U) + U : ℕ) : ℝ) := by exact_mod_cast hle
        _ = (U:ℝ) * ((M / U : ℕ):ℝ) + (U:ℝ) := by push_cast; ring
    have hlogeq : Real.log ((U:ℝ) / ((M / U : ℕ):ℝ)) =
        Real.log ((U:ℝ) / (((M / U : ℕ):ℝ) + 1)) +
          Real.log ((((M / U : ℕ):ℝ) + 1) / ((M / U : ℕ):ℝ)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    have h2 : Real.log ((U:ℝ) / (((M / U : ℕ):ℝ) + 1)) ≤
        Real.log (((U:ℝ) * (U:ℝ)) / (M:ℝ)) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by positivity) hMpos]
      nlinarith [hMle, hUpos]
    have h3 : Real.log ((((M / U : ℕ):ℝ) + 1) / ((M / U : ℕ):ℝ)) ≤ 1 := by
      have hkp : (0:ℝ) < ((M / U : ℕ):ℝ) := by exact_mod_cast hK
      have h := Real.log_le_sub_one_of_pos
        (show (0:ℝ) < (((M / U : ℕ):ℝ) + 1) / ((M / U : ℕ):ℝ) by positivity)
      have hsimp : (((M / U : ℕ):ℝ) + 1) / ((M / U : ℕ):ℝ) - 1 =
          1 / ((M / U : ℕ):ℝ) := by
        field_simp
        ring
      rw [hsimp] at h
      refine h.trans ?_
      rw [div_le_one hkp]
      exact_mod_cast hK
    have hlogU : Real.log (U:ℝ) - Real.log ((M / U : ℕ):ℝ) =
        Real.log ((U:ℝ) / ((M / U : ℕ):ℝ)) := by
      rw [Real.log_div (ne_of_gt hUpos) (by positivity)]
    calc
      ∑ d ∈ Finset.Icc (M / U + 1) U, (1 : ℝ) / (d : ℝ)
          ≤ Real.log (U:ℝ) - Real.log ((M / U : ℕ):ℝ) := hsum
      _ = Real.log ((U:ℝ) / ((M / U : ℕ):ℝ)) := hlogU
      _ = Real.log ((U:ℝ) / (((M / U : ℕ):ℝ) + 1)) +
            Real.log ((((M / U : ℕ):ℝ) + 1) / ((M / U : ℕ):ℝ)) := hlogeq
      _ ≤ Real.log (((U:ℝ) * (U:ℝ)) / (M:ℝ)) + 1 := add_le_add h2 h3
      _ = 1 + Real.log (((U:ℝ) * (U:ℝ)) / (M:ℝ)) := by ring

/-- Tail reciprocal von Mangoldt sum over the pair region `d * e > M`. -/
lemma sum_div_vonMangoldt_tail_le (n U M : ℕ) (hUn : U ≤ n)
    (hU1 : 1 ≤ U) (hM1 : 1 ≤ M) (hMU : M ≤ U * U) :
    (∑ d ∈ Finset.Icc 1 U,
        ∑ e ∈ (Finset.Icc 1 U).filter (fun e => M < d * e),
          ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ))
      ≤ Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) *
          (1 + Real.log (((U:ℝ) * (U:ℝ)) / (M:ℝ))) := by
  classical
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hlogU : 0 ≤ Real.log (U:ℝ) := Real.log_natCast_nonneg U
  have hUpos : (0:ℝ) < (U:ℝ) := by exact_mod_cast (by omega : 0 < U)
  -- Step 1: strip the von Mangoldt weight, `Λ e ≤ log n`.
  have hstep : (∑ d ∈ Finset.Icc 1 U,
        ∑ e ∈ (Finset.Icc 1 U).filter (fun e => M < d * e),
          ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ))
      ≤ Real.log (n:ℝ) * ∑ d ∈ Finset.Icc 1 U,
        ∑ e ∈ (Finset.Icc 1 U).filter (fun e => M < d * e),
          (1 : ℝ) / (d:ℝ) * (1 / (e:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    obtain ⟨he1, heU⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp he).1
    have hepos : (0:ℝ) < (e:ℝ) := by exact_mod_cast (by omega : 0 < e)
    have hΛ : ((Λ : ArithmeticFunction ℝ) e) ≤ Real.log (n:ℝ) := by
      exact (ArithmeticFunction.vonMangoldt_le_log).trans
        (Real.log_le_log (by exact_mod_cast (by omega : 0 < e))
          (by exact_mod_cast le_trans heU hUn))
    rw [show ((d * e : ℕ) : ℝ) = (d:ℝ) * (e:ℝ) by push_cast; ring]
    have hdpos : (0:ℝ) < (d:ℝ) := by
      obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
      exact_mod_cast (by omega : 0 < d)
    rw [show (1 : ℝ) / (d:ℝ) * (1 / (e:ℝ)) = 1 / ((d:ℝ) * (e:ℝ)) by
      field_simp [ne_of_gt hdpos, ne_of_gt hepos]]
    rw [show Real.log (n:ℝ) * (1 / ((d:ℝ) * (e:ℝ))) =
        Real.log (n:ℝ) / ((d:ℝ) * (e:ℝ)) by ring]
    exact div_le_div_of_nonneg_right hΛ (by positivity)
  -- Step 2: only `d ≥ M/U + 1` contributes.
  have hzero : ∀ d ∈ Finset.Icc 1 U, d ≤ M / U →
      (∑ e ∈ (Finset.Icc 1 U).filter (fun e => M < d * e),
        (1 : ℝ) / (d:ℝ) * (1 / (e:ℝ))) = 0 := by
    intro d hd hdM
    obtain ⟨hd1, hdU⟩ := Finset.mem_Icc.mp hd
    have hemp : (Finset.Icc 1 U).filter (fun e => M < d * e) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro e he
      obtain ⟨he1, heU⟩ := Finset.mem_Icc.mp he
      have hde : d * e ≤ M := by
        have h1 : d * e ≤ (M / U) * U := Nat.mul_le_mul hdM heU
        have h2 : (M / U) * U ≤ M := by
          have := Nat.div_mul_le_self M U
          simpa [Nat.mul_comm] using this
        omega
      exact not_lt.mpr hde
    rw [hemp, Finset.sum_empty]
  have hfilter : (∑ d ∈ Finset.Icc 1 U,
        ∑ e ∈ (Finset.Icc 1 U).filter (fun e => M < d * e),
          (1 : ℝ) / (d:ℝ) * (1 / (e:ℝ)))
      = ∑ d ∈ (Finset.Icc 1 U).filter (fun d => M / U + 1 ≤ d),
        ∑ e ∈ (Finset.Icc 1 U).filter (fun e => M < d * e),
          (1 : ℝ) / (d:ℝ) * (1 / (e:ℝ)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hcase : M / U + 1 ≤ d
    · rw [if_pos hcase]
    · rw [if_neg hcase, hzero d hd (Nat.le_of_lt_succ (Nat.lt_of_not_le hcase))]
  -- Step 3: bound by the product of the two harmonic tails.
  have hprod : (∑ d ∈ (Finset.Icc 1 U).filter (fun d => M / U + 1 ≤ d),
        ∑ e ∈ (Finset.Icc 1 U).filter (fun e => M < d * e),
          (1 : ℝ) / (d:ℝ) * (1 / (e:ℝ)))
      ≤ (1 + Real.log (U:ℝ)) *
          ∑ d ∈ Finset.Icc (M / U + 1) U, (1:ℝ) / (d:ℝ) := by
    have hset : (Finset.Icc 1 U).filter (fun d => M / U + 1 ≤ d) =
        Finset.Icc (M / U + 1) U := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨_, hdU⟩, hd⟩
        exact ⟨hd, hdU⟩
      · rintro ⟨hd, hdU⟩
        exact ⟨⟨Nat.le_trans (Nat.le_add_left 1 (M / U)) hd, hdU⟩, hd⟩
    rw [hset]
    calc
      ∑ d ∈ Finset.Icc (M / U + 1) U,
          ∑ e ∈ (Finset.Icc 1 U).filter (fun e => M < d * e),
            (1 : ℝ) / (d:ℝ) * (1 / (e:ℝ))
          = ∑ d ∈ Finset.Icc (M / U + 1) U,
              (1 : ℝ) / (d:ℝ) *
                ∑ e ∈ (Finset.Icc 1 U).filter (fun e => M < d * e),
                  (1 / (e:ℝ)) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.mul_sum]
      _ ≤ ∑ d ∈ Finset.Icc (M / U + 1) U,
              (1 : ℝ) / (d:ℝ) * (1 + Real.log (U:ℝ)) := by
        apply Finset.sum_le_sum
        intro d _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          ∑ e ∈ (Finset.Icc 1 U).filter (fun e => M < d * e), (1 / (e:ℝ))
              ≤ ∑ e ∈ Finset.Icc 1 U, (1 / (e:ℝ)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro e _ _
            positivity
          _ = ∑ e ∈ Finset.Icc 1 U, (1:ℝ) / (e:ℝ) := rfl
          _ ≤ 1 + Real.log (U:ℝ) := sum_inv_Icc_le_one_add_log U
      _ = (1 + Real.log (U:ℝ)) *
            ∑ d ∈ Finset.Icc (M / U + 1) U, (1:ℝ) / (d:ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
  calc
    (∑ d ∈ Finset.Icc 1 U,
        ∑ e ∈ (Finset.Icc 1 U).filter (fun e => M < d * e),
          ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ))
        ≤ Real.log (n:ℝ) * ∑ d ∈ Finset.Icc 1 U,
            ∑ e ∈ (Finset.Icc 1 U).filter (fun e => M < d * e),
              (1 : ℝ) / (d:ℝ) * (1 / (e:ℝ)) := hstep
    _ = Real.log (n:ℝ) * (∑ d ∈ (Finset.Icc 1 U).filter (fun d => M / U + 1 ≤ d),
          ∑ e ∈ (Finset.Icc 1 U).filter (fun e => M < d * e),
            (1 : ℝ) / (d:ℝ) * (1 / (e:ℝ))) := by rw [hfilter]
    _ ≤ Real.log (n:ℝ) * ((1 + Real.log (U:ℝ)) *
          ∑ d ∈ Finset.Icc (M / U + 1) U, (1:ℝ) / (d:ℝ)) := by
      apply mul_le_mul_of_nonneg_left hprod hlog
    _ ≤ Real.log (n:ℝ) * ((1 + Real.log (U:ℝ)) *
          (1 + Real.log (((U:ℝ) * (U:ℝ)) / (M:ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ hlog
      apply mul_le_mul_of_nonneg_left (sum_inv_Icc_div_succ_le M U hM1 hU1 hMU)
        (by positivity)
    _ = Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) *
          (1 + Real.log (((U:ℝ) * (U:ℝ)) / (M:ℝ))) := by ring


/-- When `U² < q`, no product `d * e` with `d, e ≤ U` is divisible by `q`,
so the `q`-multiples correction in the third Type-I term vanishes. -/
lemma double_sum_vonMangoldt_div_eq_zero (U q : ℕ) (h : U * U < q) :
    (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        (if (q : ℕ) ∣ d * e then
          ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ) else 0)) = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro e he
  obtain ⟨hd1, hdU⟩ := Finset.mem_Icc.mp hd
  obtain ⟨he1, heU⟩ := Finset.mem_Icc.mp he
  have hde : d * e ≤ U * U := Nat.mul_le_mul hdU heU
  have hlt : d * e < q := lt_of_le_of_lt hde h
  rw [if_neg]
  intro hdvd
  have hpos : 0 < d * e := Nat.mul_pos (by omega) (by omega)
  have := Nat.le_of_dvd hpos hdvd
  omega

/-- Quantitative Farey-shift separation in terms of the residue of `d a` mod `q`:
for `d < q` and `d |β| ≤ 1/(2q)`,
`typeIDist (d (a/q + β)) ≥ r_d/(2q)` with `r_d = min ((d a) mod q) (q - (d a) mod q)`. -/
lemma typeIDist_mul_farey_shift_ge_residue (q a d : ℕ) (β : ℝ) (hq : 0 < q)
    (hcop : Nat.Coprime a q) (hd1 : 1 ≤ d) (hdq : d < q)
    (hβ : (d:ℝ) * |β| ≤ 1 / (2 * (q:ℝ))) :
    ((min ((d * a) % q) (q - (d * a) % q) : ℕ) : ℝ) / (2 * (q:ℝ))
      ≤ typeIDist ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)) := by
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hxne : (d * a) % q ≠ 0 := by
    intro h0
    have hdvd : q ∣ d * a := Nat.dvd_of_mod_eq_zero h0
    have hqd : q ∣ d := hcop.symm.dvd_of_dvd_mul_right hdvd
    have := Nat.le_of_dvd (by omega) hqd
    omega
  have hx1 : 1 ≤ (d * a) % q := Nat.one_le_iff_ne_zero.mpr hxne
  have hxq : (d * a) % q < q := Nat.mod_lt _ hq
  have hqr1 : 1 ≤ q - (d * a) % q := by omega
  have hr1 : 1 ≤ min ((d * a) % q) (q - (d * a) % q) := le_min hx1 hqr1
  have hrat : ((min ((d * a) % q) (q - (d * a) % q) : ℕ) : ℝ) / (q:ℝ)
      ≤ typeIDist (((d * a : ℕ) : ℝ)/(q:ℝ)) :=
    typeIDist_natCast_div_ge_mod q (d * a) hq
  have hsplit : (d:ℝ) * ((a:ℝ)/(q:ℝ) + β) =
      ((d * a : ℕ) : ℝ)/(q:ℝ) + (d:ℝ) * β := by
    push_cast
    ring
  have habs : |(d:ℝ) * β| = (d:ℝ) * |β| := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
  have htri : typeIDist (((d * a : ℕ) : ℝ)/(q:ℝ)) ≤
      typeIDist (((d * a : ℕ) : ℝ)/(q:ℝ) + (d:ℝ) * β) + |(d:ℝ) * β| := by
    have h := typeIDist_add_le (((d * a : ℕ) : ℝ)/(q:ℝ) + (d:ℝ) * β) (-((d:ℝ) * β))
    have heq : ((d * a : ℕ) : ℝ)/(q:ℝ) + (d:ℝ) * β + (-((d:ℝ) * β)) =
        ((d * a : ℕ) : ℝ)/(q:ℝ) := by ring
    rw [heq] at h
    simpa [abs_neg] using h
  rw [habs] at htri
  have hstep : ((min ((d * a) % q) (q - (d * a) % q) : ℕ) : ℝ) / (2 * (q:ℝ)) ≤
      ((min ((d * a) % q) (q - (d * a) % q) : ℕ) : ℝ) / (q:ℝ) - 1/(2 * (q:ℝ)) := by
    have hr1R : (1:ℝ) ≤ ((min ((d * a) % q) (q - (d * a) % q) : ℕ) : ℝ) := by
      exact_mod_cast hr1
    have hqne : (q:ℝ) ≠ 0 := ne_of_gt hqpos
    field_simp
    linarith
  rw [hsplit]
  linarith [hrat, htri, hβ, hstep]

/-- The residue map `d ↦ (d * a) mod q` is injective on `[1, U]` when `2U ≤ q`
and `gcd (a, q) = 1`. -/
lemma residue_inj {q a : ℕ} (hq : 0 < q) (hcop : Nat.Coprime a q)
    {d1 d2 : ℕ} (hd1 : d1 < q) (hd2 : d2 < q)
    (h : (d1 * a) % q = (d2 * a) % q) : d1 = d2 := by
  have hmod : Nat.ModEq q (d1 * a) (d2 * a) := h
  have hdvd : (q:ℤ) ∣ ((d1:ℤ) - (d2:ℤ)) * (a:ℤ) := by
    have h1 : (q:ℤ) ∣ ((d2 * a : ℕ) : ℤ) - ((d1 * a : ℕ) : ℤ) :=
      Nat.modEq_iff_dvd.mp hmod
    have heq : ((d2 * a : ℕ) : ℤ) - ((d1 * a : ℕ) : ℤ) =
        -(((d1:ℤ) - (d2:ℤ)) * (a:ℤ)) := by
      push_cast
      ring
    rw [heq] at h1
    exact dvd_neg.mp h1
  have hcopZ : IsCoprime (q:ℤ) (a:ℤ) := hcop.symm.isCoprime
  have hdvd2 : (q:ℤ) ∣ (d1:ℤ) - (d2:ℤ) := hcopZ.dvd_of_dvd_mul_right hdvd
  rcases le_total d2 d1 with hle | hle
  · have hnat : q ∣ d1 - d2 := by
      have h' : (q:ℤ) ∣ ((d1 - d2 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hle]
        exact hdvd2
      exact_mod_cast h'
    by_contra hne
    have hpos : 0 < d1 - d2 := by omega
    have := Nat.le_of_dvd hpos hnat
    omega
  · have hneg : (q:ℤ) ∣ ((d2 - d1 : ℕ) : ℤ) := by
      have heq : ((d2 - d1 : ℕ) : ℤ) = -((d1:ℤ) - (d2:ℤ)) := by
        rw [Nat.cast_sub hle]
        ring
      rw [heq]
      exact dvd_neg.mpr hdvd2
    have hnat : q ∣ d2 - d1 := by exact_mod_cast hneg
    by_contra hne
    have hpos : 0 < d2 - d1 := by omega
    have := Nat.le_of_dvd hpos hnat
    omega

/-- Harmonic bound for reciprocal residues: if `2U ≤ q`, then
`∑_{d ≤ U} 1/min ((d a) mod q) (q - (d a) mod q) ≤ 2 (1 + log q)`. -/
lemma sum_inv_residue_le (q a U : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hUq : 2 * U ≤ q) :
    (∑ d ∈ Finset.Icc 1 U,
        (1:ℝ)/(((min ((d * a) % q) (q - (d * a) % q) : ℕ)) : ℝ))
      ≤ 2 * (1 + Real.log (q:ℝ)) := by
  classical
  rcases Nat.eq_zero_or_pos U with hU0 | hU1
  · subst hU0
    rw [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.sum_empty]
    have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    have hlogq : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg hq1
    linarith
  have hUq' : U < q := by omega
  -- Pointwise bound by the two reciprocal distances.
  have hxne : ∀ d ∈ Finset.Icc 1 U, (d * a) % q ≠ 0 := by
    intro d hd h0
    obtain ⟨hd1, hdU⟩ := Finset.mem_Icc.mp hd
    have hdvd : q ∣ d * a := Nat.dvd_of_mod_eq_zero h0
    have hqd : q ∣ d := hcop.symm.dvd_of_dvd_mul_right hdvd
    have := Nat.le_of_dvd (by omega) hqd
    omega
  have hpoint : ∀ d ∈ Finset.Icc 1 U,
      (1:ℝ)/(((min ((d * a) % q) (q - (d * a) % q) : ℕ)) : ℝ)
        ≤ 1/((((d * a) % q : ℕ)) : ℝ) + 1/(((q - (d * a) % q : ℕ)) : ℝ) := by
    intro d hd
    obtain ⟨hd1, hdU⟩ := Finset.mem_Icc.mp hd
    have hx1 : 1 ≤ (d * a) % q := Nat.one_le_iff_ne_zero.mpr (hxne d hd)
    have hxq : (d * a) % q < q := Nat.mod_lt _ hq
    have hqr1 : 1 ≤ q - (d * a) % q := by omega
    have hxpos : (0:ℝ) < (((d * a) % q : ℕ)) := by exact_mod_cast (by omega : 0 < (d*a)%q)
    have hypos : (0:ℝ) < (((q - (d * a) % q : ℕ))) := by exact_mod_cast (by omega)
    rcases le_total ((d*a)%q) (q - (d*a)%q) with hle | hle
    · have hmin : min ((d * a) % q) (q - (d * a) % q) = (d * a) % q :=
        min_eq_left hle
      rw [hmin]
      exact le_add_of_nonneg_right (by positivity)
    · have hmin : min ((d * a) % q) (q - (d * a) % q) = q - (d * a) % q :=
        min_eq_right hle
      rw [hmin]
      exact le_add_of_nonneg_left (by positivity)
  -- The two harmonic sums.
  have hinj : ∀ d1 ∈ Finset.Icc 1 U, ∀ d2 ∈ Finset.Icc 1 U,
      (d1 * a) % q = (d2 * a) % q → d1 = d2 := by
    intro d1 hd1 d2 hd2 h
    have h1 : d1 < q := lt_of_le_of_lt (Finset.mem_Icc.mp hd1).2 hUq'
    have h2 : d2 < q := lt_of_le_of_lt (Finset.mem_Icc.mp hd2).2 hUq'
    exact residue_inj hq hcop h1 h2 h
  have hsum1 : (∑ d ∈ Finset.Icc 1 U, (1:ℝ)/((((d * a) % q : ℕ)) : ℝ))
      ≤ 1 + Real.log (q:ℝ) := by
    have himg : (∑ d ∈ Finset.Icc 1 U, (1:ℝ)/((((d * a) % q : ℕ)) : ℝ))
        = ∑ k ∈ (Finset.Icc 1 U).image (fun d => (d * a) % q), (1:ℝ)/((k:ℕ):ℝ) := by
      rw [Finset.sum_image]
      intro x hx y hy hxy
      exact hinj x hx y hy hxy
    rw [himg]
    have hsub : (Finset.Icc 1 U).image (fun d => (d * a) % q) ⊆ Finset.Icc 1 q := by
      intro k hk
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (hxne d hd),
        le_of_lt (Nat.mod_lt _ hq)⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => by positivity)).trans (sum_inv_Icc_le_one_add_log q)
  have hsum2 : (∑ d ∈ Finset.Icc 1 U, (1:ℝ)/((((q - (d * a) % q : ℕ))) : ℝ))
      ≤ 1 + Real.log (q:ℝ) := by
    have himg : (∑ d ∈ Finset.Icc 1 U, (1:ℝ)/((((q - (d * a) % q : ℕ))) : ℝ))
        = ∑ k ∈ (Finset.Icc 1 U).image (fun d => q - (d * a) % q),
            (1:ℝ)/((k:ℕ):ℝ) := by
      rw [Finset.sum_image]
      intro x hx y hy hxy
      apply hinj x hx y hy
      have hxq : (x * a) % q < q := Nat.mod_lt _ hq
      have hyq : (y * a) % q < q := Nat.mod_lt _ hq
      exact (tsub_right_inj (le_of_lt hxq) (le_of_lt hyq)).mp hxy
    rw [himg]
    have hsub : (Finset.Icc 1 U).image (fun d => q - (d * a) % q) ⊆ Finset.Icc 1 q := by
      intro k hk
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hk
      have hxq : (d * a) % q < q := Nat.mod_lt _ hq
      have hx1 : 1 ≤ (d * a) % q := Nat.one_le_iff_ne_zero.mpr (hxne d hd)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => by positivity)).trans (sum_inv_Icc_le_one_add_log q)
  calc (∑ d ∈ Finset.Icc 1 U,
        (1:ℝ)/(((min ((d * a) % q) (q - (d * a) % q) : ℕ)) : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 U,
          (1/((((d * a) % q : ℕ)) : ℝ) + 1/(((q - (d * a) % q : ℕ)) : ℝ)) :=
        Finset.sum_le_sum hpoint
    _ = (∑ d ∈ Finset.Icc 1 U, (1:ℝ)/((((d * a) % q : ℕ)) : ℝ)) +
          (∑ d ∈ Finset.Icc 1 U, (1:ℝ)/((((q - (d * a) % q : ℕ))) : ℝ)) := by
        rw [Finset.sum_add_distrib]
    _ ≤ 2 * (1 + Real.log (q:ℝ)) := by linarith [hsum1, hsum2]


/-- Trivial (no oscillation) bound for the second Type-I term. -/
lemma norm_expSum_low_mu_mul_log_le_trivial (n U : ℕ) (t : ℝ) (hUn : U ≤ n) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log) t‖ ≤
      (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) := by
  rw [expSum_low_mu_mul_log_eq n U t]
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hstep : ‖∑ d ∈ Finset.Icc 1 U, ((μ : ArithmeticFunction ℝ) d : ℂ) *
        ∑ l ∈ Finset.Icc 1 (n / d),
          (ArithmeticFunction.log l : ℂ) * E (((d * l : ℕ) : ℝ) * t)‖ ≤
      ∑ d ∈ Finset.Icc 1 U, (n:ℝ) / (d:ℝ) * Real.log (n:ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro d hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hμ : |(μ : ArithmeticFunction ℝ) d| ≤ 1 := by
      have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
        ArithmeticFunction.abs_moebius_le_one
      have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast h
      simpa using h'
    have hphase : (∑ l ∈ Finset.Icc 1 (n / d),
          (ArithmeticFunction.log l : ℂ) * E (((d * l : ℕ) : ℝ) * t)) =
        ∑ l ∈ Finset.Icc 1 (n / d),
          (ArithmeticFunction.log l : ℂ) * E ((l : ℝ) * ((d : ℝ) * t)) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [show (((d * l : ℕ) : ℝ) * t) = (l : ℝ) * ((d : ℝ) * t) by
        push_cast
        ring]
    rw [hphase]
    calc
      |(μ : ArithmeticFunction ℝ) d| *
          ‖∑ l ∈ Finset.Icc 1 (n / d),
            (ArithmeticFunction.log l : ℂ) * E ((l : ℝ) * ((d : ℝ) * t))‖
          ≤ 1 * ‖∑ l ∈ Finset.Icc 1 (n / d),
              (ArithmeticFunction.log l : ℂ) * E ((l : ℝ) * ((d : ℝ) * t))‖ :=
            mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
      _ = ‖∑ l ∈ Finset.Icc 1 (n / d),
            (ArithmeticFunction.log l : ℂ) * E ((l : ℝ) * ((d : ℝ) * t))‖ := one_mul _
      _ ≤ ((n / d : ℕ) : ℝ) * Real.log ((n / d : ℕ) : ℝ) :=
        norm_log_weighted_geometric_sum_Icc_le_trivial (n / d) ((d : ℝ) * t)
      _ ≤ ((n / d : ℕ) : ℝ) * Real.log (n : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rcases Nat.eq_zero_or_pos (n / d) with h0 | hpos
        · rw [h0]
          simpa using hlog
        · exact Real.log_le_log (by exact_mod_cast hpos)
            (by exact_mod_cast Nat.div_le_self n d)
      _ ≤ ((n:ℝ) / (d:ℝ)) * Real.log (n:ℝ) :=
        mul_le_mul_of_nonneg_right Nat.cast_div_le hlog
  have hsum : (∑ d ∈ Finset.Icc 1 U, (n:ℝ) / (d:ℝ) * Real.log (n:ℝ))
      = (n:ℝ) * Real.log (n:ℝ) *
          ∑ d ∈ Finset.Icc 1 U, (1 : ℝ) / (d:ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hlogU : Real.log (U:ℝ) ≤ Real.log (n:ℝ) := by
    rcases Nat.eq_zero_or_pos U with h0 | hpos
    · rw [h0]
      simpa using hlog
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hUn)
  calc
    ‖∑ d ∈ Finset.Icc 1 U, ((μ : ArithmeticFunction ℝ) d : ℂ) *
        ∑ l ∈ Finset.Icc 1 (n / d),
          (ArithmeticFunction.log l : ℂ) * E (((d * l : ℕ) : ℝ) * t)‖
        ≤ ∑ d ∈ Finset.Icc 1 U, (n:ℝ) / (d:ℝ) * Real.log (n:ℝ) := hstep
    _ = (n:ℝ) * Real.log (n:ℝ) *
          ∑ d ∈ Finset.Icc 1 U, (1 : ℝ) / (d:ℝ) := hsum
    _ ≤ (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) := by
      apply mul_le_mul_of_nonneg_left (sum_inv_Icc_le_one_add_log U) (by positivity)
    _ ≤ (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith


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

set_option maxHeartbeats 1600000 in
/-- Type-I third term on a major arc, uniformly in `q`, including the
small-denominator range `q <= U^2`. -/
theorem norm_expSum_low_mu_lowLambda_zeta_le_majorArc_small_q (n q U a : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hU1 : 1 ≤ U) (hUn : U ≤ n)
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ))) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
        (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ ≤
      2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) +
        4 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ) := by
  rw [expSum_low_mu_lowLambda_zeta_eq n U ((a:ℝ)/(q:ℝ) + β)]
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hUnR : (U:ℝ) ≤ (n:ℝ) := by exact_mod_cast hUn
  have harg : ∀ d e m : ℕ,
      ((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β) =
        (m : ℝ) * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)) := by
    intro d e m
    push_cast
    ring
  have hmul : ∀ d : ℕ, 1 ≤ d → d ≤ U → 1 ≤ d * d := by
    intro d hd1 _
    exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  have hstep : ‖∑ d ∈ Finset.Icc 1 (min U n), ((μ : ArithmeticFunction ℝ) d : ℂ) *
        ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e : ℂ) *
            ∑ m ∈ Finset.Icc 1 (n / (d * e)),
              E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ ≤
      ∑ d ∈ Finset.Icc 1 (min U n), ∑ e ∈ Finset.Icc 1 (min U (n / d)),
        ((Λ : ArithmeticFunction ℝ) e) *
          (if (q : ℕ) ∣ d * e then ((n / (d * e) : ℕ) : ℝ) else 2 * (q:ℝ)) := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro d hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hμ : |(μ : ArithmeticFunction ℝ) d| ≤ 1 := by
      have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
        ArithmeticFunction.abs_moebius_le_one
      have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast h
      simpa using h'
    calc
      |(μ : ArithmeticFunction ℝ) d| *
          ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖
          ≤ 1 * ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
              ((Λ : ArithmeticFunction ℝ) e : ℂ) *
                ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                  E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ :=
            mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
      _ = ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ := one_mul _
      _ ≤ ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e) *
              (if (q : ℕ) ∣ d * e then ((n / (d * e) : ℕ) : ℝ) else 2 * (q:ℝ)) := by
        refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro e he
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have hinner : ‖∑ m ∈ Finset.Icc 1 (n / (d * e)),
              E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ ≤
            (if (q : ℕ) ∣ d * e then ((n / (d * e) : ℕ) : ℝ) else 2 * (q:ℝ)) := by
          by_cases hde : (q : ℕ) ∣ d * e
          · rw [if_pos hde]
            calc
              ‖∑ m ∈ Finset.Icc 1 (n / (d * e)),
                  E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖
                  ≤ ∑ m ∈ Finset.Icc 1 (n / (d * e)), (1 : ℝ) := by
                refine (norm_sum_le _ _).trans ?_
                apply Finset.sum_le_sum
                intro m _
                have hE : ‖E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ = 1 := by
                  dsimp only [E]
                  simpa only [mul_comm] using Complex.norm_exp_ofReal_mul_I
                    (2 * Real.pi * (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)))
                rw [hE]
              _ = ((n / (d * e) : ℕ) : ℝ) := by
                rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
                norm_num
          · rw [if_neg hde]
            obtain ⟨hd1, hdU'⟩ := Finset.mem_Icc.mp hd
            obtain ⟨he1, heU'⟩ := Finset.mem_Icc.mp he
            have hdU : d ≤ U := le_trans hdU' (min_le_left _ _)
            have heU : e ≤ U := le_trans heU' (min_le_left _ _)
            have hkU : d * e ≤ U * U := Nat.mul_le_mul hdU heU
            have hk1 : 1 ≤ d * e := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
            have hsine := abs_sin_pi_mul_majorArc_ge_pointwise q (U * U) a (d * e) β
              hq hcop (Nat.mul_pos (by omega : 0 < U) (by omega : 0 < U)) hk1 hkU hde hβ
            have hspos : (0:ℝ) <
                |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)))| :=
              lt_of_lt_of_le (by positivity : (0:ℝ) < 1/(q:ℝ)) hsine
            have hsin_ne : Real.sin (Real.pi * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))) ≠ 0 :=
              abs_pos.mp hspos
            simp_rw [harg d e]
            refine (norm_geometric_sum_Icc_le_two (n / (d * e))
              (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)) hsin_ne).trans ?_
            have hs' : (1:ℝ) ≤
                |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)))| * (q:ℝ) :=
              (div_le_iff₀ hqR).mp hsine
            have hunit : (1:ℝ) /
                |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)))| ≤ (q:ℝ) := by
              rw [div_le_iff₀ hspos]
              simpa [mul_comm] using hs'
            calc
              (2:ℝ) /
                  |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)))|
                  = 2 * (1 /
                      |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)))|) := by
                rw [div_eq_mul_one_div]
              _ ≤ 2 * (q:ℝ) := mul_le_mul_of_nonneg_left hunit (by norm_num)
        exact mul_le_mul_of_nonneg_left hinner ArithmeticFunction.vonMangoldt_nonneg
  have hext : ∑ d ∈ Finset.Icc 1 (min U n), ∑ e ∈ Finset.Icc 1 (min U (n / d)),
        ((Λ : ArithmeticFunction ℝ) e) *
          (if (q : ℕ) ∣ d * e then ((n / (d * e) : ℕ) : ℝ) else 2 * (q:ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        ((Λ : ArithmeticFunction ℝ) e) *
          (if (q : ℕ) ∣ d * e then ((n / (d * e) : ℕ) : ℝ) else 2 * (q:ℝ)) := by
    have houter : ∑ d ∈ Finset.Icc 1 (min U n),
          ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e) *
              (if (q : ℕ) ∣ d * e then ((n / (d * e) : ℕ) : ℝ) else 2 * (q:ℝ))
        ≤ ∑ d ∈ Finset.Icc 1 U,
          ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e) *
              (if (q : ℕ) ∣ d * e then ((n / (d * e) : ℕ) : ℝ) else 2 * (q:ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
          le_trans (Finset.mem_Icc.mp hd).2 (min_le_left _ _)⟩
      · intro d _ _
        apply Finset.sum_nonneg
        intro e _
        apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        by_cases hde : (q : ℕ) ∣ d * e
        · rw [if_pos hde]; positivity
        · rw [if_neg hde]; positivity
    refine houter.trans ?_
    apply Finset.sum_le_sum
    intro d _
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp he).1,
        le_trans (Finset.mem_Icc.mp he).2 (min_le_left _ _)⟩
    · intro e _ _
      apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      by_cases hde : (q : ℕ) ∣ d * e
      · rw [if_pos hde]; positivity
      · rw [if_neg hde]; positivity
  have hΛsum : ∑ e ∈ Finset.Icc 1 U, ((Λ : ArithmeticFunction ℝ) e) ≤
      (U:ℝ) * Real.log (n:ℝ) := by
    calc
      ∑ e ∈ Finset.Icc 1 U, ((Λ : ArithmeticFunction ℝ) e)
          ≤ ∑ _e ∈ Finset.Icc 1 U, Real.log (n:ℝ) := by
        apply Finset.sum_le_sum
        intro e he
        obtain ⟨he1, heU⟩ := Finset.mem_Icc.mp he
        exact (ArithmeticFunction.vonMangoldt_le_log).trans
          (Real.log_le_log (by exact_mod_cast he1)
            (by exact_mod_cast le_trans heU hUn))
      _ = (U:ℝ) * Real.log (n:ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        norm_num
  have hnd : ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        (if (q : ℕ) ∣ d * e then 0 else ((Λ : ArithmeticFunction ℝ) e) * (2 * (q:ℝ)))
      ≤ 2 * (U:ℝ) * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) := by
    have hcomm : ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          ((Λ : ArithmeticFunction ℝ) e) * (2 * (q:ℝ)) =
        ∑ e ∈ Finset.Icc 1 U, ∑ _d ∈ Finset.Icc 1 U,
          ((Λ : ArithmeticFunction ℝ) e) * (2 * (q:ℝ)) := Finset.sum_comm
    calc
      ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          (if (q : ℕ) ∣ d * e then 0 else ((Λ : ArithmeticFunction ℝ) e) * (2 * (q:ℝ)))
          ≤ ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
              ((Λ : ArithmeticFunction ℝ) e) * (2 * (q:ℝ)) := by
        apply Finset.sum_le_sum
        intro d _
        apply Finset.sum_le_sum
        intro e _
        by_cases hde : (q : ℕ) ∣ d * e
        · rw [if_pos hde]
          exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
        · rw [if_neg hde]
      _ = ∑ e ∈ Finset.Icc 1 U, ∑ _d ∈ Finset.Icc 1 U,
              ((Λ : ArithmeticFunction ℝ) e) * (2 * (q:ℝ)) := hcomm
      _ = ∑ e ∈ Finset.Icc 1 U, ((U:ℝ) * (((Λ : ArithmeticFunction ℝ) e) * (2 * (q:ℝ)))) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        norm_num
      _ = (U:ℝ) * (2 * (q:ℝ)) * ∑ e ∈ Finset.Icc 1 U, ((Λ : ArithmeticFunction ℝ) e) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ ≤ (U:ℝ) * (2 * (q:ℝ)) * ((U:ℝ) * Real.log (n:ℝ)) := by
        apply mul_le_mul_of_nonneg_left hΛsum
        positivity
      _ = 2 * (U:ℝ) * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) := by ring
  have hlogU2 : Real.log (((U * U : ℕ)) : ℝ) ≤ 2 * Real.log (n:ℝ) := by
    have hU2n2 : ((U * U : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul hUn hUn
    by_cases hn0 : n = 0
    · have hU0 : U = 0 := by omega
      simp [hU0, hn0]
    · have hpos : 0 < ((U * U : ℕ) : ℝ) := by
        have hU0 : 0 < U := by omega
        have : 0 < U * U := Nat.mul_pos hU0 hU0
        exact_mod_cast this
      calc
        Real.log (((U * U : ℕ)) : ℝ) ≤ Real.log (((n * n : ℕ)) : ℝ) :=
          Real.log_le_log hpos hU2n2
        _ = 2 * Real.log (n:ℝ) := by
          rw [show ((n * n : ℕ) : ℝ) = (n:ℝ) * (n:ℝ) by push_cast; ring,
            Real.log_mul (by exact_mod_cast hn0) (by exact_mod_cast hn0)]
          ring
  have hdiv : ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        (if (q : ℕ) ∣ d * e then ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ)
          else 0)
      ≤ 4 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ) := by
    have hfac : ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          (if (q : ℕ) ∣ d * e then ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ)
            else 0)
        ≤ (n:ℝ) * ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
            (if (q : ℕ) ∣ d * e then ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)
              else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e he
      by_cases hde : (q : ℕ) ∣ d * e
      · rw [if_pos hde, if_pos hde]
        have hde1 : 1 ≤ d * e := by
          obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
          obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
          exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
        have hdeR : (0:ℝ) < ((d * e : ℕ) : ℝ) := by exact_mod_cast hde1
        calc
          ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ)
              ≤ ((Λ : ArithmeticFunction ℝ) e) * ((n:ℝ) / ((d * e : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left Nat.cast_div_le ArithmeticFunction.vonMangoldt_nonneg
          _ = (n:ℝ) * (((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)) := by ring
      · rw [if_neg hde, if_neg hde]
        simp
    have hbase := double_sum_vonMangoldt_div_le U q hq
    have hlogU2q : Real.log ((((U * U) / q : ℕ)) : ℝ) ≤ Real.log (((U * U : ℕ)) : ℝ) := by
      by_cases h0 : (U * U) / q = 0
      · rw [h0]
        simpa using Real.log_natCast_nonneg (U * U)
      · apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h0)
        exact_mod_cast Nat.div_le_self (U * U) q
    have hlogU2q' : Real.log ((((U * U) / q : ℕ)) : ℝ) ≤ 2 * Real.log (n:ℝ) :=
      hlogU2q.trans hlogU2
    calc
      ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          (if (q : ℕ) ∣ d * e then ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ)
            else 0)
          ≤ (n:ℝ) * ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
              (if (q : ℕ) ∣ d * e then ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)
                else 0) := hfac
      _ ≤ (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
            ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left hbase
        positivity
      _ ≤ (n:ℝ) * ((2 * Real.log (n:ℝ)) *
            ((1 / (q:ℝ)) * (1 + 2 * Real.log (n:ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hA2 : 0 ≤ 2 * Real.log (n:ℝ) := by positivity
        have hB : 0 ≤ (1/(q:ℝ)) * (1 + Real.log ((((U*U)/q:ℕ)):ℝ)) :=
          mul_nonneg (by positivity)
            (by linarith [Real.log_natCast_nonneg ((U*U)/q)])
        have hC : (1/(q:ℝ)) * (1 + Real.log ((((U*U)/q:ℕ)):ℝ)) ≤
            (1/(q:ℝ)) * (1 + 2 * Real.log (n:ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith [hlogU2q']) (by positivity)
        exact mul_le_mul hlogU2 hC hB hA2
      _ = 2 * (n:ℝ) * Real.log (n:ℝ) * (1 + 2 * Real.log (n:ℝ)) / (q:ℝ) := by ring
      _ ≤ 4 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ) := by
        have hcoef : 0 ≤ 2 * (n:ℝ) * Real.log (n:ℝ) := by positivity
        apply div_le_div_of_nonneg_right _ hqR.le
        calc
          2 * (n:ℝ) * Real.log (n:ℝ) * (1 + 2 * Real.log (n:ℝ))
              ≤ 2 * (n:ℝ) * Real.log (n:ℝ) * (2 * (1 + Real.log (n:ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ hcoef
            linarith
          _ = 4 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) := by ring
  have hsplit : ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        ((Λ : ArithmeticFunction ℝ) e) *
          (if (q : ℕ) ∣ d * e then ((n / (d * e) : ℕ) : ℝ) else 2 * (q:ℝ))
      = (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          (if (q : ℕ) ∣ d * e then ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ)
            else 0))
        + ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          (if (q : ℕ) ∣ d * e then 0 else ((Λ : ArithmeticFunction ℝ) e) * (2 * (q:ℝ))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hde : (q : ℕ) ∣ d * e
    · rw [if_pos hde, if_pos hde, if_pos hde]; ring
    · rw [if_neg hde, if_neg hde, if_neg hde]; ring
  calc
    ‖∑ d ∈ Finset.Icc 1 (min U n), ((μ : ArithmeticFunction ℝ) d : ℂ) *
        ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e : ℂ) *
            ∑ m ∈ Finset.Icc 1 (n / (d * e)),
              E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖
        ≤ ∑ d ∈ Finset.Icc 1 (min U n), ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e) *
            (if (q : ℕ) ∣ d * e then ((n / (d * e) : ℕ) : ℝ) else 2 * (q:ℝ)) := hstep
    _ ≤ ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          ((Λ : ArithmeticFunction ℝ) e) *
            (if (q : ℕ) ∣ d * e then ((n / (d * e) : ℕ) : ℝ) else 2 * (q:ℝ)) := hext
    _ = _ := hsplit
    _ ≤ 2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) +
        4 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ) := by
      linarith [hnd, hdiv]

set_option maxHeartbeats 1600000 in
/-- Third Type-I term in reciprocal-distance form, unconditional. -/
lemma norm_expSum_low_mu_lowLambda_zeta_le_recip (n U : ℕ) (t : ℝ) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
        (ζ : ArithmeticFunction ℝ)) t‖ ≤
      ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        ((Λ : ArithmeticFunction ℝ) e) *
          typeIDistRecip (n / (d * e)) (((d * e : ℕ) : ℝ) * t) := by
  rw [expSum_low_mu_lowLambda_zeta_eq n U t]
  have hstep : ‖∑ d ∈ Finset.Icc 1 (min U n), ((μ : ArithmeticFunction ℝ) d : ℂ) *
        ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e : ℂ) *
            ∑ m ∈ Finset.Icc 1 (n / (d * e)),
              E (((d * e * m : ℕ) : ℝ) * t)‖ ≤
      ∑ d ∈ Finset.Icc 1 (min U n),
        ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e) *
            typeIDistRecip (n / (d * e)) (((d * e : ℕ) : ℝ) * t) := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro d hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hμ : |(μ : ArithmeticFunction ℝ) d| ≤ 1 := by
      have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
        ArithmeticFunction.abs_moebius_le_one
      have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast h
      simpa using h'
    calc
      |(μ : ArithmeticFunction ℝ) d| *
          ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * t)‖
          ≤ 1 * ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
              ((Λ : ArithmeticFunction ℝ) e : ℂ) *
                ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                  E (((d * e * m : ℕ) : ℝ) * t)‖ :=
            mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
      _ = ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * t)‖ := one_mul _
      _ ≤ ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e) *
              typeIDistRecip (n / (d * e)) (((d * e : ℕ) : ℝ) * t) := by
        refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro e he
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have hinner : ‖∑ m ∈ Finset.Icc 1 (n / (d * e)),
              E (((d * e * m : ℕ) : ℝ) * t)‖ ≤
            typeIDistRecip (n / (d * e)) (((d * e : ℕ) : ℝ) * t) := by
          have harg' : ∀ m : ℕ, ((d : ℝ) * (e : ℝ) * (m : ℝ)) * t =
              (m : ℝ) * ((d : ℝ) * (e : ℝ) * t) := by
            intro m
            ring
          simpa [harg'] using
            norm_geometric_sum_Icc_le_recip (n / (d * e))
              (((d * e : ℕ) : ℝ) * t)
        exact mul_le_mul_of_nonneg_left hinner ArithmeticFunction.vonMangoldt_nonneg
  have hext : ∑ d ∈ Finset.Icc 1 (min U n),
        ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e) *
            typeIDistRecip (n / (d * e)) (((d * e : ℕ) : ℝ) * t)
      ≤ ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        ((Λ : ArithmeticFunction ℝ) e) *
          typeIDistRecip (n / (d * e)) (((d * e : ℕ) : ℝ) * t) := by
    have houter : ∑ d ∈ Finset.Icc 1 (min U n),
          ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e) *
              typeIDistRecip (n / (d * e)) (((d * e : ℕ) : ℝ) * t)
        ≤ ∑ d ∈ Finset.Icc 1 U,
          ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e) *
              typeIDistRecip (n / (d * e)) (((d * e : ℕ) : ℝ) * t) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
          le_trans (Finset.mem_Icc.mp hd).2 (min_le_left _ _)⟩
      · intro d _ _
        apply Finset.sum_nonneg
        intro e _
        apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        exact typeIDistRecip_nonneg _ _
    refine houter.trans ?_
    apply Finset.sum_le_sum
    intro d _
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp he).1,
        le_trans (Finset.mem_Icc.mp he).2 (min_le_left _ _)⟩
    · intro e _ _
      apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      exact typeIDistRecip_nonneg _ _
  exact hstep.trans hext


/-- Third-term inner sum below a product threshold `M`: if `de ≤ M`,
`q ∤ de`, and `|β| ≤ 1/(16 q M)`, the geometric sum is at most `2q`. -/
lemma norm_third_inner_le_of_product_le (n q M a d e : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hde1 : 1 ≤ d * e) (hdeM : d * e ≤ M)
    (hndvd : ¬ q ∣ d * e)
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * (M:ℝ))) :
    ‖∑ m ∈ Finset.Icc 1 (n / (d * e)),
        E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ ≤ 2 * (q:ℝ) := by
  classical
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hM1 : 1 ≤ M := le_trans hde1 hdeM
  have hsine := abs_sin_pi_mul_majorArc_ge_pointwise q M a (d * e) β
    hq hcop hM1 hde1 hdeM hndvd hβ
  have hspos : (0:ℝ) <
      |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)))| :=
    lt_of_lt_of_le (by positivity : (0:ℝ) < 1/(q:ℝ)) hsine
  have hsin_ne : Real.sin (Real.pi * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))) ≠ 0 :=
    abs_pos.mp hspos
  have harg : ∀ m : ℕ, ((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β) =
      (m : ℝ) * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)) := by
    intro m
    push_cast
    ring
  simp_rw [harg]
  refine (norm_geometric_sum_Icc_le_two (n / (d * e))
    (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)) hsin_ne).trans ?_
  have hs' : (1:ℝ) ≤
      |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)))| * (q:ℝ) :=
    (div_le_iff₀ hqR).mp hsine
  have hunit : (1:ℝ) /
      |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)))| ≤ (q:ℝ) := by
    rw [div_le_iff₀ hspos]
    simpa [mul_comm] using hs'
  calc
    (2:ℝ) /
        |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)))|
        = 2 * (1 /
            |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)))|) := by
      rw [div_eq_mul_one_div]
    _ ≤ 2 * (q:ℝ) := mul_le_mul_of_nonneg_left hunit (by norm_num)


/-- Trivial bound for the third-term inner geometric sum. -/
lemma norm_third_inner_le_trivial (n d e : ℕ) (t : ℝ) :
    ‖∑ m ∈ Finset.Icc 1 (n / (d * e)),
        E (((d * e * m : ℕ) : ℝ) * t)‖ ≤ ((n / (d * e) : ℕ) : ℝ) := by
  have normE : ∀ x : ℝ, ‖E x‖ = 1 := by
    intro x
    dsimp only [E]
    simpa only [mul_comm] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑ m ∈ Finset.Icc 1 (n / (d * e)),
        ‖E (((d * e * m : ℕ) : ℝ) * t)‖
        ≤ ∑ _m ∈ Finset.Icc 1 (n / (d * e)), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m _
      rw [normE]
    _ = ((n / (d * e) : ℕ) : ℝ) := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      norm_num

/-- The per-`(d,e)` truncated inner bound: threshold sine bound, then the
trivial bounds. -/
noncomputable def typeIThirdInnerBound (n q M d e : ℕ) : ℝ :=
  (if d * e ≤ M then 2 * (q:ℝ) else 0) +
    ((n / (d * e) : ℕ) : ℝ) +
    (if (q : ℕ) ∣ d * e then ((n / (d * e) : ℕ) : ℝ) else 0)

lemma norm_third_inner_le_truncated (n q M a d e : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hde1 : 1 ≤ d * e)
    (hβM : |β| ≤ 1 / (16 * (q:ℝ) * (M:ℝ))) :
    ‖∑ m ∈ Finset.Icc 1 (n / (d * e)),
        E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ ≤
      typeIThirdInnerBound n q M d e := by
  classical
  by_cases hM : d * e ≤ M
  · by_cases hqde : (q : ℕ) ∣ d * e
    · have htriv := norm_third_inner_le_trivial n d e ((a:ℝ)/(q:ℝ) + β)
      have hq0 : (0:ℝ) ≤ 2 * (q:ℝ) := by positivity
      have hn0 : (0:ℝ) ≤ ((n / (d * e) : ℕ) : ℝ) := by positivity
      simp only [typeIThirdInnerBound, if_pos hM, if_pos hqde]
      linarith
    · have hthr := norm_third_inner_le_of_product_le n q M a d e β
        hq hcop hde1 hM hqde hβM
      have hn0 : (0:ℝ) ≤ ((n / (d * e) : ℕ) : ℝ) := by positivity
      simp only [typeIThirdInnerBound, if_pos hM, if_neg hqde]
      linarith
  · have htriv := norm_third_inner_le_trivial n d e ((a:ℝ)/(q:ℝ) + β)
    have hn0 : (0:ℝ) ≤ ((n / (d * e) : ℕ) : ℝ) := by positivity
    by_cases hqde : (q : ℕ) ∣ d * e
    · simp only [typeIThirdInnerBound, if_neg hM, if_pos hqde]
      linarith
    · simp only [typeIThirdInnerBound, if_neg hM, if_neg hqde]
      linarith


lemma typeIThirdInnerBound_nonneg (n q M d e : ℕ) :
    0 ≤ typeIThirdInnerBound n q M d e := by
  rw [typeIThirdInnerBound]
  apply add_nonneg
  · apply add_nonneg
    · by_cases h : d * e ≤ M
      · rw [if_pos h]; positivity
      · rw [if_neg h]
    · positivity
  · by_cases h : (q : ℕ) ∣ d * e
    · rw [if_pos h]; positivity
    · rw [if_neg h]

set_option maxHeartbeats 1600000 in
/-- Truncated third Type-I term: the sine separation is used only for
`de ≤ M`; the remaining terms are estimated trivially. -/
lemma norm_expSum_low_mu_lowLambda_zeta_le_truncated (n q U M a : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hU1 : 1 ≤ U) (hUn : U ≤ n)
    (hβM : |β| ≤ 1 / (16 * (q:ℝ) * (M:ℝ))) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
        (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ ≤
      2 * (q:ℝ) * (M:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ))
      + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ^ 2
      + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
          ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ)))) := by
  classical
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hstep : ‖∑ d ∈ Finset.Icc 1 (min U n), ((μ : ArithmeticFunction ℝ) d : ℂ) *
        ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e : ℂ) *
            ∑ m ∈ Finset.Icc 1 (n / (d * e)),
              E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ ≤
      ∑ d ∈ Finset.Icc 1 (min U n),
        ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e) * typeIThirdInnerBound n q M d e := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro d hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hμ : |(μ : ArithmeticFunction ℝ) d| ≤ 1 := by
      have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
        ArithmeticFunction.abs_moebius_le_one
      have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast h
      simpa using h'
    calc
      |(μ : ArithmeticFunction ℝ) d| *
          ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖
          ≤ 1 * ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
              ((Λ : ArithmeticFunction ℝ) e : ℂ) *
                ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                  E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ :=
            mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
      _ = ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ := one_mul _
      _ ≤ ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e) * typeIThirdInnerBound n q M d e := by
        refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro e he
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
        obtain ⟨hd1, _hdU⟩ := Finset.mem_Icc.mp hd
        obtain ⟨he1, _heU⟩ := Finset.mem_Icc.mp he
        have hde1 : 1 ≤ d * e :=
          Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
        exact norm_third_inner_le_truncated n q M a d e β hq hcop hde1 hβM
  have hext : ∑ d ∈ Finset.Icc 1 (min U n),
        ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e) * typeIThirdInnerBound n q M d e
      ≤ ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        ((Λ : ArithmeticFunction ℝ) e) * typeIThirdInnerBound n q M d e := by
    have houter : ∑ d ∈ Finset.Icc 1 (min U n),
          ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e) * typeIThirdInnerBound n q M d e
        ≤ ∑ d ∈ Finset.Icc 1 U,
          ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e) * typeIThirdInnerBound n q M d e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
          le_trans (Finset.mem_Icc.mp hd).2 (min_le_left _ _)⟩
      · intro d _ _
        apply Finset.sum_nonneg
        intro e _
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (typeIThirdInnerBound_nonneg n q M d e)
    refine houter.trans ?_
    apply Finset.sum_le_sum
    intro d _
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp he).1,
        le_trans (Finset.mem_Icc.mp he).2 (min_le_left _ _)⟩
    · intro e _ _
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (typeIThirdInnerBound_nonneg n q M d e)
  set Acoef : ℝ := ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
    (if d * e ≤ M then (Λ : ArithmeticFunction ℝ) e else 0)
  set Tcoef : ℝ := ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
    ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)
  set Bcoef : ℝ := ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
    (if (q : ℕ) ∣ d * e then ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ) else 0)
  have hpoint : ∀ d e : ℕ,
      ((Λ : ArithmeticFunction ℝ) e) * typeIThirdInnerBound n q M d e ≤
        2 * (q:ℝ) * (if d * e ≤ M then (Λ : ArithmeticFunction ℝ) e else 0)
        + (n:ℝ) * (((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ))
        + (n:ℝ) * (if (q : ℕ) ∣ d * e then
            ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ) else 0) := by
    intro d e
    have hnle : ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ) ≤
        (n:ℝ) * (((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)) := by
      have hdiv : ((n / (d * e) : ℕ) : ℝ) ≤ (n:ℝ) / ((d * e : ℕ) : ℝ) :=
        Nat.cast_div_le
      calc
        ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ)
            ≤ ((Λ : ArithmeticFunction ℝ) e) * ((n:ℝ) / ((d * e : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hdiv ArithmeticFunction.vonMangoldt_nonneg
        _ = (n:ℝ) * (((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)) := by ring
    have hnle' : ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ) ≤
        (n:ℝ) * (((Λ : ArithmeticFunction ℝ) e) / ((d:ℝ) * (e:ℝ))) := by
      simpa [Nat.cast_mul] using hnle
    rw [typeIThirdInnerBound]
    by_cases hM : d * e ≤ M <;> by_cases hqde : (q : ℕ) ∣ d * e <;>
      simp [hM, hqde] <;> nlinarith [hnle']
  have hsplit : ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        ((Λ : ArithmeticFunction ℝ) e) * typeIThirdInnerBound n q M d e
      ≤ 2 * (q:ℝ) * Acoef + (n:ℝ) * Tcoef + (n:ℝ) * Bcoef := by
    calc
      ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          ((Λ : ArithmeticFunction ℝ) e) * typeIThirdInnerBound n q M d e
          ≤ ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
              (2 * (q:ℝ) * (if d * e ≤ M then (Λ : ArithmeticFunction ℝ) e else 0)
                + (n:ℝ) * (((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ))
                + (n:ℝ) * (if (q : ℕ) ∣ d * e then
                    ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ) else 0)) := by
        apply Finset.sum_le_sum
        intro d _
        apply Finset.sum_le_sum
        intro e _
        exact hpoint d e
      _ = 2 * (q:ℝ) * Acoef + (n:ℝ) * Tcoef + (n:ℝ) * Bcoef := by
        simp only [Acoef, Tcoef, Bcoef, Finset.sum_add_distrib, Finset.mul_sum]
  have hA : Acoef ≤ Real.log (n:ℝ) * ((M:ℝ) * (1 + Real.log (U:ℝ))) := by
    have hterm : (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          (if d * e ≤ M then (Λ : ArithmeticFunction ℝ) e else 0))
        ≤ Real.log (n:ℝ) *
            (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
              (if d * e ≤ M then (1:ℝ) else 0)) := by
      calc
        (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
            (if d * e ≤ M then (Λ : ArithmeticFunction ℝ) e else 0))
            ≤ ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
                Real.log (n:ℝ) * (if d * e ≤ M then (1:ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro d _
          apply Finset.sum_le_sum
          intro e he
          by_cases h : d * e ≤ M
          · rw [if_pos h, if_pos h]
            have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
            have heU : e ≤ U := (Finset.mem_Icc.mp he).2
            have hΛ : ((Λ : ArithmeticFunction ℝ) e) ≤ Real.log (n:ℝ) :=
              (ArithmeticFunction.vonMangoldt_le_log).trans
                (Real.log_le_log (by exact_mod_cast he1)
                  (by exact_mod_cast le_trans heU hUn))
            simpa using hΛ
          · rw [if_neg h, if_neg h]
            simp
        _ = Real.log (n:ℝ) *
            (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
              (if d * e ≤ M then (1:ℝ) else 0)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          rw [Finset.mul_sum]
    have hcount : (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          (if d * e ≤ M then (1:ℝ) else 0))
        = ∑ d ∈ Finset.Icc 1 U,
            ((((Finset.Icc 1 U).filter (fun e => d * e ≤ M)).card : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_boole]
    rw [hcount] at hterm
    refine hterm.trans ?_
    apply mul_le_mul_of_nonneg_left _ hlog
    exact sum_card_mul_le M U
  have hT : Tcoef ≤ Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ^ 2 :=
    sum_div_vonMangoldt_le n U hUn
  have hB : Bcoef ≤ Real.log (((U * U : ℕ)) : ℝ) *
      ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))) :=
    double_sum_vonMangoldt_div_le U q hq
  have hlogU : Real.log (U:ℝ) ≤ Real.log (n:ℝ) := by
    rcases Nat.eq_zero_or_pos U with h0 | hpos
    · rw [h0]; simpa using hlog
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hUn)
  have hA' : Acoef ≤ Real.log (n:ℝ) * ((M:ℝ) * (1 + Real.log (n:ℝ))) := by
    refine hA.trans ?_
    apply mul_le_mul_of_nonneg_left _ hlog
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  calc
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
        (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖
        ≤ ∑ d ∈ Finset.Icc 1 (min U n),
            ∑ e ∈ Finset.Icc 1 (min U (n / d)),
              ((Λ : ArithmeticFunction ℝ) e) * typeIThirdInnerBound n q M d e := by
          rw [expSum_low_mu_lowLambda_zeta_eq n U ((a:ℝ)/(q:ℝ) + β)]
          exact hstep
    _ ≤ ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          ((Λ : ArithmeticFunction ℝ) e) * typeIThirdInnerBound n q M d e := hext
    _ ≤ 2 * (q:ℝ) * Acoef + (n:ℝ) * Tcoef + (n:ℝ) * Bcoef := hsplit
    _ ≤ 2 * (q:ℝ) * (Real.log (n:ℝ) * ((M:ℝ) * (1 + Real.log (n:ℝ))))
          + (n:ℝ) * (Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ^ 2)
          + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
              ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ)))) := by
      apply add_le_add
      · apply add_le_add
        · apply mul_le_mul_of_nonneg_left hA' (by positivity)
        · apply mul_le_mul_of_nonneg_left hT (by positivity)
      · apply mul_le_mul_of_nonneg_left hB (by positivity)
    _ = 2 * (q:ℝ) * (M:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ))
          + (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ^ 2
          + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
              ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ)))) := by ring


set_option maxHeartbeats 1600000 in
/-- Trivial (no oscillation) bound for the third Type-I term. -/
lemma norm_expSum_low_mu_lowLambda_zeta_le_trivial (n U : ℕ) (t : ℝ) (hUn : U ≤ n) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
        (ζ : ArithmeticFunction ℝ)) t‖ ≤
      (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ^ 2 := by
  classical
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hstep : ‖∑ d ∈ Finset.Icc 1 (min U n), ((μ : ArithmeticFunction ℝ) d : ℂ) *
        ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e : ℂ) *
            ∑ m ∈ Finset.Icc 1 (n / (d * e)),
              E (((d * e * m : ℕ) : ℝ) * t)‖ ≤
      ∑ d ∈ Finset.Icc 1 (min U n),
        ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro d hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hμ : |(μ : ArithmeticFunction ℝ) d| ≤ 1 := by
      have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
        ArithmeticFunction.abs_moebius_le_one
      have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast h
      simpa using h'
    calc
      |(μ : ArithmeticFunction ℝ) d| *
          ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * t)‖
          ≤ 1 * ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
              ((Λ : ArithmeticFunction ℝ) e : ℂ) *
                ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                  E (((d * e * m : ℕ) : ℝ) * t)‖ :=
            mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
      _ = ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * t)‖ := one_mul _
      _ ≤ ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ) := by
        refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro e _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact mul_le_mul_of_nonneg_left (norm_third_inner_le_trivial n d e t)
          ArithmeticFunction.vonMangoldt_nonneg
  have hext : ∑ d ∈ Finset.Icc 1 (min U n),
        ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ) := by
    have houter : ∑ d ∈ Finset.Icc 1 (min U n),
          ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ)
        ≤ ∑ d ∈ Finset.Icc 1 U,
          ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
          le_trans (Finset.mem_Icc.mp hd).2 (min_le_left _ _)⟩
      · intro d _ _
        apply Finset.sum_nonneg
        intro e _
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    refine houter.trans ?_
    apply Finset.sum_le_sum
    intro d _
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp he).1,
        le_trans (Finset.mem_Icc.mp he).2 (min_le_left _ _)⟩
    · intro e _ _
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hbound : ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ)
      ≤ (n:ℝ) * (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)) := by
    calc
      ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ)
          ≤ ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
              (n:ℝ) * (((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro d _
        apply Finset.sum_le_sum
        intro e _
        have hdiv : ((n / (d * e) : ℕ) : ℝ) ≤ (n:ℝ) / ((d * e : ℕ) : ℝ) :=
          Nat.cast_div_le
        calc
          ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ)
              ≤ ((Λ : ArithmeticFunction ℝ) e) * ((n:ℝ) / ((d * e : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hdiv ArithmeticFunction.vonMangoldt_nonneg
          _ = (n:ℝ) * (((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)) := by ring
      _ = (n:ℝ) * (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.mul_sum]
  have hT := sum_div_vonMangoldt_le n U hUn
  calc
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
        (ζ : ArithmeticFunction ℝ)) t‖
        ≤ ∑ d ∈ Finset.Icc 1 (min U n),
            ∑ e ∈ Finset.Icc 1 (min U (n / d)),
              ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ) := by
          rw [expSum_low_mu_lowLambda_zeta_eq n U t]
          exact hstep
    _ ≤ ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ) := hext
    _ ≤ (n:ℝ) * (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)) := hbound
    _ ≤ (n:ℝ) * (Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ = (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) ^ 2 := by ring


set_option maxHeartbeats 1600000 in
/-- Weighted count of the pairs `d * e ≤ M`: the sum of `Λ e` over the pairs
below the threshold is at most `log n · M (1 + log U)`. -/
lemma sum_vonMangoldt_filter_mul_le (n U M : ℕ) (hUn : U ≤ n) :
    (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        (if d * e ≤ M then ((Λ : ArithmeticFunction ℝ) e) else 0))
      ≤ Real.log (n:ℝ) * ((M:ℝ) * (1 + Real.log (U:ℝ))) := by
  classical
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hterm : (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        (if d * e ≤ M then ((Λ : ArithmeticFunction ℝ) e) else 0))
      ≤ Real.log (n:ℝ) *
          (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
            (if d * e ≤ M then (1:ℝ) else 0)) := by
    calc
      (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          (if d * e ≤ M then ((Λ : ArithmeticFunction ℝ) e) else 0))
          ≤ ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
              Real.log (n:ℝ) * (if d * e ≤ M then (1:ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro d _
        apply Finset.sum_le_sum
        intro e he
        by_cases h : d * e ≤ M
        · rw [if_pos h, if_pos h]
          have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
          have heU : e ≤ U := (Finset.mem_Icc.mp he).2
          have hΛ : ((Λ : ArithmeticFunction ℝ) e) ≤ Real.log (n:ℝ) :=
            (ArithmeticFunction.vonMangoldt_le_log).trans
              (Real.log_le_log (by exact_mod_cast he1)
                (by exact_mod_cast le_trans heU hUn))
          simpa using hΛ
        · rw [if_neg h, if_neg h]
          simp
      _ = Real.log (n:ℝ) *
          (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
            (if d * e ≤ M then (1:ℝ) else 0)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.mul_sum]
  have hcount : (∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        (if d * e ≤ M then (1:ℝ) else 0))
      = ∑ d ∈ Finset.Icc 1 U,
          ((((Finset.Icc 1 U).filter (fun e => d * e ≤ M)).card : ℝ)) := by
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_boole]
  rw [hcount] at hterm
  refine hterm.trans ?_
  apply mul_le_mul_of_nonneg_left _ hlog
  exact sum_card_mul_le M U

/-- Per-`(d,e)` truncated inner bound with the trivial tail beyond `M`. -/
noncomputable def typeIThirdInnerBoundTail (n q M d e : ℕ) : ℝ :=
  if d * e ≤ M then
    (if (q : ℕ) ∣ d * e then ((n / (d * e) : ℕ) : ℝ) else 2 * (q:ℝ))
  else ((n / (d * e) : ℕ) : ℝ)

lemma norm_third_inner_le_truncatedTail (n q M a d e : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hde1 : 1 ≤ d * e)
    (hβM : |β| ≤ 1 / (16 * (q:ℝ) * (M:ℝ))) :
    ‖∑ m ∈ Finset.Icc 1 (n / (d * e)),
        E (((d * e * m : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))‖ ≤
      typeIThirdInnerBoundTail n q M d e := by
  classical
  by_cases hM : d * e ≤ M
  · by_cases hqde : (q : ℕ) ∣ d * e
    · rw [typeIThirdInnerBoundTail, if_pos hM, if_pos hqde]
      exact norm_third_inner_le_trivial n d e ((a:ℝ)/(q:ℝ) + β)
    · rw [typeIThirdInnerBoundTail, if_pos hM, if_neg hqde]
      exact norm_third_inner_le_of_product_le n q M a d e β hq hcop hde1 hM hqde hβM
  · rw [typeIThirdInnerBoundTail, if_neg hM]
    exact norm_third_inner_le_trivial n d e ((a:ℝ)/(q:ℝ) + β)

lemma typeIThirdInnerBoundTail_nonneg (n q M d e : ℕ) :
    0 ≤ typeIThirdInnerBoundTail n q M d e := by
  rw [typeIThirdInnerBoundTail]
  by_cases h : d * e ≤ M
  · rw [if_pos h]
    by_cases hq : (q : ℕ) ∣ d * e
    · rw [if_pos hq]; positivity
    · rw [if_neg hq]; positivity
  · rw [if_neg h]; positivity

set_option maxHeartbeats 1600000 in
/-- Reindexed third Type-I term, with an abstract per-pair bound. -/
lemma norm_expSum_low_mu_lowLambda_zeta_le_of_bound (n U : ℕ) (t : ℝ)
    (f : ℕ → ℕ → ℝ)
    (hpoint : ∀ d e : ℕ, 1 ≤ d * e →
      ‖∑ m ∈ Finset.Icc 1 (n / (d * e)),
        E (((d * e * m : ℕ) : ℝ) * t)‖ ≤ f d e)
    (hnonneg : ∀ d e : ℕ, 0 ≤ f d e) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
        (ζ : ArithmeticFunction ℝ)) t‖ ≤
      ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        ((Λ : ArithmeticFunction ℝ) e) * f d e := by
  classical
  have hstep : ‖∑ d ∈ Finset.Icc 1 (min U n), ((μ : ArithmeticFunction ℝ) d : ℂ) *
        ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e : ℂ) *
            ∑ m ∈ Finset.Icc 1 (n / (d * e)),
              E (((d * e * m : ℕ) : ℝ) * t)‖ ≤
      ∑ d ∈ Finset.Icc 1 (min U n),
        ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e) * f d e := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro d hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hμ : |(μ : ArithmeticFunction ℝ) d| ≤ 1 := by
      have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
        ArithmeticFunction.abs_moebius_le_one
      have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast h
      simpa using h'
    calc
      |(μ : ArithmeticFunction ℝ) d| *
          ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * t)‖
          ≤ 1 * ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
              ((Λ : ArithmeticFunction ℝ) e : ℂ) *
                ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                  E (((d * e * m : ℕ) : ℝ) * t)‖ :=
            mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
      _ = ‖∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * t)‖ := one_mul _
      _ ≤ ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e) * f d e := by
        refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro e he
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
        obtain ⟨hd1, _hdU⟩ := Finset.mem_Icc.mp hd
        obtain ⟨he1, _heU⟩ := Finset.mem_Icc.mp he
        have hde1 : 1 ≤ d * e :=
          Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
        exact hpoint d e hde1
  have hext : ∑ d ∈ Finset.Icc 1 (min U n),
        ∑ e ∈ Finset.Icc 1 (min U (n / d)),
          ((Λ : ArithmeticFunction ℝ) e) * f d e
      ≤ ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        ((Λ : ArithmeticFunction ℝ) e) * f d e := by
    have houter : ∑ d ∈ Finset.Icc 1 (min U n),
          ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e) * f d e
        ≤ ∑ d ∈ Finset.Icc 1 U,
          ∑ e ∈ Finset.Icc 1 (min U (n / d)),
            ((Λ : ArithmeticFunction ℝ) e) * f d e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
          le_trans (Finset.mem_Icc.mp hd).2 (min_le_left _ _)⟩
      · intro d _ _
        apply Finset.sum_nonneg
        intro e _
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hnonneg d e)
    refine houter.trans ?_
    apply Finset.sum_le_sum
    intro d _
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp he).1,
        le_trans (Finset.mem_Icc.mp he).2 (min_le_left _ _)⟩
    · intro e _ _
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hnonneg d e)
  calc
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
        (ζ : ArithmeticFunction ℝ)) t‖
        ≤ ∑ d ∈ Finset.Icc 1 (min U n),
            ∑ e ∈ Finset.Icc 1 (min U (n / d)),
              ((Λ : ArithmeticFunction ℝ) e) * f d e := by
          rw [expSum_low_mu_lowLambda_zeta_eq n U t]
          exact hstep
    _ ≤ ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          ((Λ : ArithmeticFunction ℝ) e) * f d e := hext

set_option maxHeartbeats 1600000 in
/-- Truncated third Type-I term with the tail gain: the sine separation is
used only for `de ≤ M`, while the tail `de > M` is estimated by the
reciprocal von Mangoldt tail sum. -/
lemma norm_expSum_low_mu_lowLambda_zeta_le_truncated_tail (n q U M a : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hU1 : 1 ≤ U) (hUn : U ≤ n)
    (hM1 : 1 ≤ M) (hMU : M ≤ U * U)
    (hβM : |β| ≤ 1 / (16 * (q:ℝ) * (M:ℝ))) :
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
        (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ ≤
      2 * (q:ℝ) * (Real.log (n:ℝ) * ((M:ℝ) * (1 + Real.log (U:ℝ))))
      + (n:ℝ) * (Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) *
          (1 + Real.log (((U:ℝ) * (U:ℝ)) / (M:ℝ))))
      + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
          ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ)))) := by
  classical
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hUpos : (0:ℝ) < (U:ℝ) := by exact_mod_cast (by omega : 0 < U)
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  set A2 : ℝ := ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
    (if d * e ≤ M then ((Λ : ArithmeticFunction ℝ) e) else 0)
  set T2 : ℝ := ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
    (if M < d * e then ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ) else 0)
  set B2 : ℝ := ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
    (if (q : ℕ) ∣ d * e then ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ) else 0)
  have hbase := norm_expSum_low_mu_lowLambda_zeta_le_of_bound n U
    ((a:ℝ)/(q:ℝ) + β) (typeIThirdInnerBoundTail n q M)
    (fun d e hde1 => norm_third_inner_le_truncatedTail n q M a d e β
      hq hcop hde1 hβM)
    (fun d e => typeIThirdInnerBoundTail_nonneg n q M d e)
  have hterm : ∀ d e : ℕ,
      ((Λ : ArithmeticFunction ℝ) e) * typeIThirdInnerBoundTail n q M d e ≤
        2 * (q:ℝ) * (if d * e ≤ M then ((Λ : ArithmeticFunction ℝ) e) else 0)
        + (n:ℝ) * (if M < d * e then
            ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ) else 0)
        + (n:ℝ) * (if (q : ℕ) ∣ d * e then
            ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ) else 0) := by
    intro d e
    have hndiv : ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ) ≤
        (n:ℝ) * (((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)) := by
      calc
        ((Λ : ArithmeticFunction ℝ) e) * ((n / (d * e) : ℕ) : ℝ)
            ≤ ((Λ : ArithmeticFunction ℝ) e) * ((n:ℝ) / ((d * e : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left Nat.cast_div_le ArithmeticFunction.vonMangoldt_nonneg
        _ = (n:ℝ) * (((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)) := by ring
    have hΛ0 : (0:ℝ) ≤ ((Λ : ArithmeticFunction ℝ) e) := ArithmeticFunction.vonMangoldt_nonneg
    rw [typeIThirdInnerBoundTail]
    by_cases hM : d * e ≤ M
    · by_cases hqde : (q : ℕ) ∣ d * e
      · simp only [if_pos hM, if_pos hqde, if_neg (not_lt.mpr hM)]
        have h1 : 0 ≤ 2 * (q:ℝ) * ((Λ : ArithmeticFunction ℝ) e) :=
          mul_nonneg (by positivity) hΛ0
        have h2 : 0 ≤ (n:ℝ) * (((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)) :=
          mul_nonneg (by positivity) (div_nonneg hΛ0 (by positivity))
        linarith
      · simp only [if_pos hM, if_neg hqde, if_neg (not_lt.mpr hM)]
        linarith
    · have hlt : M < d * e := Nat.lt_of_not_le hM
      by_cases hqde : (q : ℕ) ∣ d * e
      · simp only [if_neg hM, if_pos hlt, if_pos hqde]
        have h2 : 0 ≤ (n:ℝ) * (((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ)) :=
          mul_nonneg (by positivity) (div_nonneg hΛ0 (by positivity))
        linarith
      · simp only [if_neg hM, if_pos hlt, if_neg hqde]
        linarith
  have hsplit : ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
        ((Λ : ArithmeticFunction ℝ) e) * typeIThirdInnerBoundTail n q M d e
      ≤ 2 * (q:ℝ) * A2 + (n:ℝ) * T2 + (n:ℝ) * B2 := by
    calc
      ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
          ((Λ : ArithmeticFunction ℝ) e) * typeIThirdInnerBoundTail n q M d e
          ≤ ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
              (2 * (q:ℝ) * (if d * e ≤ M then
                  ((Λ : ArithmeticFunction ℝ) e) else 0)
                + (n:ℝ) * (if M < d * e then
                    ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ) else 0)
                + (n:ℝ) * (if (q : ℕ) ∣ d * e then
                    ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ) else 0)) := by
        apply Finset.sum_le_sum
        intro d _
        apply Finset.sum_le_sum
        intro e _
        exact hterm d e
      _ = 2 * (q:ℝ) * A2 + (n:ℝ) * T2 + (n:ℝ) * B2 := by
        simp only [A2, T2, B2, Finset.sum_add_distrib, Finset.mul_sum]
  have hA2 : A2 ≤ Real.log (n:ℝ) * ((M:ℝ) * (1 + Real.log (U:ℝ))) :=
    sum_vonMangoldt_filter_mul_le n U M hUn
  have hT2 : T2 ≤ Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) *
      (1 + Real.log (((U:ℝ) * (U:ℝ)) / (M:ℝ))) := by
    have hT2' : T2 = ∑ d ∈ Finset.Icc 1 U,
        ∑ e ∈ (Finset.Icc 1 U).filter (fun e => M < d * e),
          ((Λ : ArithmeticFunction ℝ) e) / ((d * e : ℕ) : ℝ) := by
      simp only [T2]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_filter]
    rw [hT2']
    exact sum_div_vonMangoldt_tail_le n U M hUn hU1 hM1 hMU
  have hB2 : B2 ≤ Real.log (((U * U : ℕ)) : ℝ) *
      ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ))) :=
    double_sum_vonMangoldt_div_le U q hq
  calc
    ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
        (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖
        ≤ ∑ d ∈ Finset.Icc 1 U, ∑ e ∈ Finset.Icc 1 U,
            ((Λ : ArithmeticFunction ℝ) e) * typeIThirdInnerBoundTail n q M d e := hbase
    _ ≤ 2 * (q:ℝ) * A2 + (n:ℝ) * T2 + (n:ℝ) * B2 := hsplit
    _ ≤ 2 * (q:ℝ) * (Real.log (n:ℝ) * ((M:ℝ) * (1 + Real.log (U:ℝ))))
          + (n:ℝ) * (Real.log (n:ℝ) * (1 + Real.log (U:ℝ)) *
              (1 + Real.log (((U:ℝ) * (U:ℝ)) / (M:ℝ))))
          + (n:ℝ) * (Real.log (((U * U : ℕ)) : ℝ) *
              ((1 / (q:ℝ)) * (1 + Real.log ((((U * U) / q : ℕ)) : ℝ)))) := by
      apply add_le_add
      · apply add_le_add
        · apply mul_le_mul_of_nonneg_left hA2 (by positivity)
        · apply mul_le_mul_of_nonneg_left hT2 (by positivity)
      · apply mul_le_mul_of_nonneg_left hB2 (by positivity)


/- Milestone: on a major arc with `q > U^2`, the entire Type-I part of the
Vaughan decomposition is bounded by `6 U^2 q log n`.  Only the Type-II
bilinear term is left. -/
set_option maxHeartbeats 1000000 in
theorem norm_expSum_vaughan_typeI_le_majorArc (n q U a : ℕ) (β : ℝ)
    (hn : 1 ≤ n) (hUn : U ≤ n) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hU1 : 1 ≤ U) (hUq : U * U < q)
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ))) :
    ‖expSum n Λ ((a:ℝ)/(q:ℝ) + β) -
        expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
          high U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ ≤
      6 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hU1R : (1:ℝ) ≤ (U:ℝ) := by exact_mod_cast hU1
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hcast : ((U * U : ℕ) : ℝ) = (U:ℝ) * (U:ℝ) := by push_cast; ring
  have hβ2 : |β| ≤ 1 / (16 * (q:ℝ) * (U:ℝ)) := by
    have hUU : (U:ℝ) ≤ (U:ℝ) * (U:ℝ) := by nlinarith
    have hdenpos : (0:ℝ) < 16 * (q:ℝ) * (U:ℝ) := by positivity
    have hdenle : 16 * (q:ℝ) * (U:ℝ) ≤ 16 * (q:ℝ) * ((U:ℝ)*(U:ℝ)) := by
      nlinarith
    rw [hcast] at hβ
    exact hβ.trans (one_div_le_one_div_of_le hdenpos hdenle)
  have hUqU : U < q := by
    have hUle : U ≤ U * U := Nat.le_mul_of_pos_right U (by omega)
    exact lt_of_le_of_lt hUle hUq
  have hdecomp : expSum n Λ ((a:ℝ)/(q:ℝ) + β) -
      expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
        high U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) =
      expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) +
        expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
          ((a:ℝ)/(q:ℝ) + β) -
        expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) := by
    rw [expSum_vaughan n U]
    ring
  rw [hdecomp]
  have h1 := norm_expSum_low_vonMangoldt_le n U hn hUn ((a:ℝ)/(q:ℝ) + β)
  have h2 := norm_expSum_low_mu_mul_log_le_majorArc n q U a β hq hcop hU1 hUqU hβ2
  have h3 := norm_expSum_low_mu_lowLambda_zeta_le_majorArc n q U a β hq hcop hU1 hUq hβ
  calc
    ‖expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) +
        expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
          ((a:ℝ)/(q:ℝ) + β) -
        expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖
        ≤ ‖expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) +
            expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
              ((a:ℝ)/(q:ℝ) + β)‖ +
          ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
            (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ :=
      norm_sub_le _ _
    _ ≤ (‖expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ +
          ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
            ((a:ℝ)/(q:ℝ) + β)‖) +
        ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (((U:ℝ) + 1) * Real.log (n:ℝ) + 2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ)) +
          2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by
      apply add_le_add
      · exact add_le_add h1 h2
      · exact h3
    _ ≤ 6 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by
      have hQ1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
      have hUU : (U:ℝ) ≤ (U:ℝ) * (U:ℝ) := by nlinarith
      have hA1 : ((U:ℝ) + 1) * Real.log (n:ℝ) ≤
          2 * (U:ℝ) * Real.log (n:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hlog
        linarith
      have hA2 : 2 * (U:ℝ) * Real.log (n:ℝ) ≤
          2 * ((U:ℝ) * (U:ℝ)) * Real.log (n:ℝ) := by
        calc
          2 * (U:ℝ) * Real.log (n:ℝ) =
              2 * Real.log (n:ℝ) * (U:ℝ) := by ring
          _ ≤ 2 * Real.log (n:ℝ) * ((U:ℝ) * (U:ℝ)) :=
            mul_le_mul_of_nonneg_left hUU (by positivity)
          _ = 2 * ((U:ℝ) * (U:ℝ)) * Real.log (n:ℝ) := by ring
      have hA3 : 2 * ((U:ℝ) * (U:ℝ)) * Real.log (n:ℝ) ≤
          2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by
        calc
          2 * ((U:ℝ) * (U:ℝ)) * Real.log (n:ℝ) =
              (2 * ((U:ℝ) * (U:ℝ)) * Real.log (n:ℝ)) * 1 := by ring
          _ ≤ (2 * ((U:ℝ) * (U:ℝ)) * Real.log (n:ℝ)) * (q:ℝ) :=
            mul_le_mul_of_nonneg_left hQ1 (by positivity)
          _ = 2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by ring
      have hB : 2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) ≤
          2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by
        calc
          2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) =
              (2 * (q:ℝ) * Real.log (n:ℝ)) * (U:ℝ) := by ring
          _ ≤ (2 * (q:ℝ) * Real.log (n:ℝ)) * ((U:ℝ) * (U:ℝ)) :=
            mul_le_mul_of_nonneg_left hUU (by positivity)
          _ = 2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by ring
      calc
        ((U:ℝ) + 1) * Real.log (n:ℝ) + 2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) +
            2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ)
            ≤ 2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) +
                2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) +
              2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by
          apply add_le_add
          · exact add_le_add (hA1.trans (hA2.trans hA3)) hB
          · exact le_rfl
        _ = 6 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) := by ring

set_option maxHeartbeats 1000000 in
/-- Combined Type-I bound on a major arc, uniformly in `q`: it also covers
the small-denominator range `q <= U^2`, where multiples of `q` must be
estimated trivially. -/
theorem norm_expSum_vaughan_typeI_le_majorArc_small_q (n q U a : ℕ) (β : ℝ)
    (hn : 1 ≤ n) (hUn : U ≤ n) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hU1 : 1 ≤ U)
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * ((U * U : ℕ) : ℝ))) :
    ‖expSum n Λ ((a:ℝ)/(q:ℝ) + β) -
        expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
          high U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ ≤
      6 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) +
        6 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hU1R : (1:ℝ) ≤ (U:ℝ) := by exact_mod_cast hU1
  have hUnR : (U:ℝ) ≤ (n:ℝ) := by exact_mod_cast hUn
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hcast : ((U * U : ℕ) : ℝ) = (U:ℝ) * (U:ℝ) := by push_cast; ring
  have hβ2 : |β| ≤ 1 / (16 * (q:ℝ) * (U:ℝ)) := by
    have hUU : (U:ℝ) ≤ (U:ℝ) * (U:ℝ) := by nlinarith
    have hdenpos : (0:ℝ) < 16 * (q:ℝ) * (U:ℝ) := by positivity
    have hdenle : 16 * (q:ℝ) * (U:ℝ) ≤ 16 * (q:ℝ) * ((U:ℝ)*(U:ℝ)) := by
      nlinarith
    rw [hcast] at hβ
    exact hβ.trans (one_div_le_one_div_of_le hdenpos hdenle)
  have hdecomp : expSum n Λ ((a:ℝ)/(q:ℝ) + β) -
      expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
        high U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) =
      expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) +
        expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
          ((a:ℝ)/(q:ℝ) + β) -
        expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) := by
    rw [expSum_vaughan n U]
    ring
  rw [hdecomp]
  have h1 := norm_expSum_low_vonMangoldt_le n U hn hUn ((a:ℝ)/(q:ℝ) + β)
  have h2 := norm_expSum_low_mu_mul_log_le_majorArc_small_q n q U a β
    hq hcop hU1 hUn hβ2
  have h3 := norm_expSum_low_mu_lowLambda_zeta_le_majorArc_small_q n q U a β
    hq hcop hU1 hUn hβ
  calc
    ‖expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) +
        expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
          ((a:ℝ)/(q:ℝ) + β) -
        expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖
        ≤ ‖expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β) +
            expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
              ((a:ℝ)/(q:ℝ) + β)‖ +
          ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
            (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ :=
      norm_sub_le _ _
    _ ≤ (‖expSum n (low U (Λ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ +
          ‖expSum n (low U (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log)
            ((a:ℝ)/(q:ℝ) + β)‖) +
        ‖expSum n (low U (μ : ArithmeticFunction ℝ) * low U (Λ : ArithmeticFunction ℝ) *
          (ζ : ArithmeticFunction ℝ)) ((a:ℝ)/(q:ℝ) + β)‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (((U:ℝ) + 1) * Real.log (n:ℝ) +
          (2 * (U:ℝ) * (q:ℝ) * Real.log (n:ℝ) +
            2 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ))) +
          (2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) +
            4 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ)) := by
      apply add_le_add
      · exact add_le_add h1 h2
      · exact h3
    _ ≤ 6 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * Real.log (n:ℝ) +
        6 * (n:ℝ) * Real.log (n:ℝ) * (1 + Real.log (n:ℝ)) / (q:ℝ) := by
      set L := Real.log (n:ℝ) with hL
      have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
      have hmain : ((U:ℝ) + 1) * L + 2 * (U:ℝ) * (q:ℝ) * L +
          2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * L ≤
            6 * (((U:ℝ) * (U:ℝ)) * (q:ℝ)) * L := by
        have h1' : ((U:ℝ) + 1) * L ≤ 2 * (U:ℝ) * (U:ℝ) * (q:ℝ) * L := by
          apply mul_le_mul_of_nonneg_right _ hlog
          nlinarith
        have h2' : 2 * (U:ℝ) * (q:ℝ) * L ≤ 2 * (U:ℝ) * (U:ℝ) * (q:ℝ) * L := by
          apply mul_le_mul_of_nonneg_right _ hlog
          have hUU : (U:ℝ) ≤ (U:ℝ) * (U:ℝ) := by nlinarith
          have hUq : (U:ℝ) * (q:ℝ) ≤ (U:ℝ) * (U:ℝ) * (q:ℝ) := by
            calc (U:ℝ) * (q:ℝ) ≤ ((U:ℝ) * (U:ℝ)) * (q:ℝ) :=
              mul_le_mul_of_nonneg_right hUU hqR.le
              _ = (U:ℝ) * (U:ℝ) * (q:ℝ) := by ring
          linarith
        nlinarith
      calc
        ((U:ℝ) + 1) * L +
            (2 * (U:ℝ) * (q:ℝ) * L + 2 * (n:ℝ) * L * (1 + L) / (q:ℝ)) +
            (2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * L +
              4 * (n:ℝ) * L * (1 + L) / (q:ℝ))
            = (((U:ℝ) + 1) * L + 2 * (U:ℝ) * (q:ℝ) * L +
                2 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * L) +
              6 * ((n:ℝ) * L * (1 + L) / (q:ℝ)) := by ring
        _ ≤ 6 * (((U:ℝ) * (U:ℝ)) * (q:ℝ)) * L +
              6 * ((n:ℝ) * L * (1 + L) / (q:ℝ)) := by linarith [hmain]
        _ = 6 * ((U:ℝ) * (U:ℝ)) * (q:ℝ) * L +
              6 * (n:ℝ) * L * (1 + L) / (q:ℝ) := by ring

/-- Geometric bound for the innermost Type-II sum at frequency `d * e * t`. -/
lemma norm_typeII_m_sum_le (n d e : ℕ) (t : ℝ)
    (hsin : Real.sin (Real.pi * (((d * e : ℕ) : ℝ) * t)) ≠ 0) :
    ‖∑ m ∈ Finset.Icc 1 (n / (d * e)), E (((d * e * m : ℕ) : ℝ) * t)‖ ≤
      2 / |Real.sin (Real.pi * (((d * e : ℕ) : ℝ) * t))| := by
  have hphase : (∑ m ∈ Finset.Icc 1 (n / (d * e)), E (((d * e * m : ℕ) : ℝ) * t)) =
      ∑ m ∈ Finset.Icc 1 (n / (d * e)), E ((m : ℝ) * (((d * e : ℕ) : ℝ) * t)) := by
    apply Finset.sum_congr rfl
    intro m _
    congr 1
    push_cast
    ring
  rw [hphase]
  exact norm_geometric_sum_Icc_le_two (n / (d * e)) (((d * e : ℕ) : ℝ) * t) hsin

lemma norm_sum_mul_sq_le_sum_mul_sum_sq {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (F : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ‖∑ i ∈ s, (w i : ℂ) * F i‖ ^ 2 ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ‖F i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, (w i : ℂ) * F i‖ ≤ ∑ i ∈ s, w i * ‖F i‖ := by
    calc
      ‖∑ i ∈ s, (w i : ℂ) * F i‖ ≤ ∑ i ∈ s, ‖(w i : ℂ) * F i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, w i * ‖F i‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
  have h2 : (∑ i ∈ s, w i * ‖F i‖) ^ 2 ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ‖F i‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * ‖F i‖)
    have hleft : (∑ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i) * ‖F i‖)) =
        ∑ i ∈ s, w i * ‖F i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
    have hr1 : (∑ i ∈ s, (Real.sqrt (w i)) ^ 2) = ∑ i ∈ s, w i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.sq_sqrt (hw i hi)]
    have hr2 : (∑ i ∈ s, (Real.sqrt (w i) * ‖F i‖) ^ 2) =
        ∑ i ∈ s, w i * ‖F i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_pow, Real.sq_sqrt (hw i hi)]
    rw [hleft, hr1, hr2] at h
    exact h
  calc
    ‖∑ i ∈ s, (w i : ℂ) * F i‖ ^ 2 ≤ (∑ i ∈ s, w i * ‖F i‖) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2


/-- Summing the weighted Cauchy–Schwarz over the outer `d` block. -/
lemma sum_norm_mul_sq_le_sum_weight_mul_energy {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (w : ι → ℝ) (G : κ → ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∑ d ∈ t, ‖∑ e ∈ s, (w e : ℂ) * G d e‖ ^ 2 ≤
      (∑ e ∈ s, w e) * ∑ e ∈ s, w e * ∑ d ∈ t, ‖G d e‖ ^ 2 := by
  have hpoint : ∀ d ∈ t, ‖∑ e ∈ s, (w e : ℂ) * G d e‖ ^ 2 ≤
      (∑ e ∈ s, w e) * ∑ e ∈ s, w e * ‖G d e‖ ^ 2 :=
    fun d _ => norm_sum_mul_sq_le_sum_mul_sum_sq s w (fun e => G d e) hw
  calc
    ∑ d ∈ t, ‖∑ e ∈ s, (w e : ℂ) * G d e‖ ^ 2
        ≤ ∑ d ∈ t, (∑ e ∈ s, w e) * ∑ e ∈ s, w e * ‖G d e‖ ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = (∑ e ∈ s, w e) * ∑ d ∈ t, ∑ e ∈ s, w e * ‖G d e‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ = (∑ e ∈ s, w e) * ∑ e ∈ s, w e * ∑ d ∈ t, ‖G d e‖ ^ 2 := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.mul_sum]

/-- The inner `(e, m)` sum of the Type-II term at a fixed outer `d`. -/
noncomputable def typeIIInner (n U : ℕ) (t : ℝ) (d : ℕ) : ℂ :=
  ∑ e ∈ Finset.Icc (U + 1) (n / d), ((Λ : ArithmeticFunction ℝ) e : ℂ) *
    ∑ m ∈ Finset.Icc 1 (n / (d * e)), E (((d * e * m : ℕ) : ℝ) * t)

lemma E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_E (x : ℝ) : ‖E x‖ = 1 := by
  dsimp only [E]
  simpa only [mul_comm] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

/-- Shifting all phases by a common unit does not change the sum's norm. -/
lemma norm_sum_shift {M : ℕ} (c : Fin M → ℂ) (θ shift : ℝ) :
    ‖∑ n : Fin M, c n * E ((n : ℝ) * θ + shift)‖ =
      ‖∑ n : Fin M, c n * E ((n : ℝ) * θ)‖ := by
  have h : (∑ n : Fin M, c n * E ((n : ℝ) * θ + shift))
      = (∑ n : Fin M, c n * E ((n : ℝ) * θ)) * E shift := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    rw [E_add]
    ring
  rw [h, norm_mul, norm_E, mul_one]

lemma star_E (x : ℝ) : (starRingEnd ℂ) (E x) = E (-x) := by
  unfold E
  rw [← Complex.exp_conj]
  congr 1
  simp [map_ofNat, map_mul]

lemma dispersion_identity (N D : ℕ) (hD : 0 < D) (c : ℕ → ℂ) (t : ℝ) :
    ((∑ d ∈ Finset.Icc D (N / D),
        ‖∑ l ∈ Finset.Icc 1 (N / d), c l * E (((d * l : ℕ) : ℝ) * t)‖ ^ 2 : ℝ) : ℂ)
      = ∑ l1 ∈ Finset.Icc 1 (N / D), ∑ l2 ∈ Finset.Icc 1 (N / D),
          c l1 * star (c l2) *
            ∑ d ∈ Finset.Icc D (min (N / D) (N / max l1 l2)),
              E (((d : ℝ) * ((l1 : ℝ) - (l2 : ℝ))) * t) := by
  classical
  have hstep : ((∑ d ∈ Finset.Icc D (N / D),
        ‖∑ l ∈ Finset.Icc 1 (N / d), c l * E (((d * l : ℕ) : ℝ) * t)‖ ^ 2 : ℝ) : ℂ)
      = ∑ d ∈ Finset.Icc D (N / D),
          ∑ l1 ∈ Finset.Icc 1 (N / d),
            ∑ l2 ∈ Finset.Icc 1 (N / d),
              c l1 * star (c l2) * E (((d : ℝ) * ((l1 : ℝ) - (l2 : ℝ))) * t) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l1 hl1
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l2 hl2
    rw [map_mul, star_E]
    have hphase : E (((d * l1 : ℕ) : ℝ) * t) * E (-(((d * l2 : ℕ) : ℝ) * t)) =
        E (((d : ℝ) * ((l1 : ℝ) - (l2 : ℝ))) * t) := by
      rw [← E_add]
      congr 1
      push_cast
      ring
    calc
      c l1 * E (((d * l1 : ℕ) : ℝ) * t) *
          ((starRingEnd ℂ) (c l2) * E (-(((d * l2 : ℕ) : ℝ) * t)))
          = c l1 * (starRingEnd ℂ) (c l2) *
              (E (((d * l1 : ℕ) : ℝ) * t) * E (-(((d * l2 : ℕ) : ℝ) * t))) := by ring
      _ = c l1 * (starRingEnd ℂ) (c l2) *
              E (((d : ℝ) * ((l1 : ℝ) - (l2 : ℝ))) * t) := by rw [hphase]
  rw [hstep]
  simp_rw [Finset.mul_sum]
  have hL : (∑ d ∈ Finset.Icc D (N / D),
          ∑ l1 ∈ Finset.Icc 1 (N / d),
            ∑ l2 ∈ Finset.Icc 1 (N / d),
              c l1 * star (c l2) * E (((d : ℝ) * ((l1 : ℝ) - (l2 : ℝ))) * t))
      = ∑ p ∈ (Finset.Icc D (N / D)).sigma
          (fun d => (Finset.Icc 1 (N / d)).product (Finset.Icc 1 (N / d))),
          c p.2.1 * star (c p.2.2) *
            E (((p.1 : ℝ) * ((p.2.1 : ℝ) - (p.2.2 : ℝ))) * t) := by
    calc
      (∑ d ∈ Finset.Icc D (N / D),
          ∑ l1 ∈ Finset.Icc 1 (N / d),
            ∑ l2 ∈ Finset.Icc 1 (N / d),
              c l1 * star (c l2) * E (((d : ℝ) * ((l1 : ℝ) - (l2 : ℝ))) * t))
          = ∑ d ∈ Finset.Icc D (N / D),
              ∑ p ∈ (Finset.Icc 1 (N / d)).product (Finset.Icc 1 (N / d)),
                c p.1 * star (c p.2) * E (((d : ℝ) * ((p.1 : ℝ) - (p.2 : ℝ))) * t) := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [show (Finset.Icc 1 (N / d)).product (Finset.Icc 1 (N / d)) =
                Finset.Icc 1 (N / d) ×ˢ Finset.Icc 1 (N / d) from rfl]
            rw [Finset.sum_product]
      _ = ∑ p ∈ (Finset.Icc D (N / D)).sigma
            (fun d => (Finset.Icc 1 (N / d)).product (Finset.Icc 1 (N / d))),
            c p.2.1 * star (c p.2.2) *
              E (((p.1 : ℝ) * ((p.2.1 : ℝ) - (p.2.2 : ℝ))) * t) := by
            rw [Finset.sum_sigma']
  rw [hL]
  have hR : (∑ l1 ∈ Finset.Icc 1 (N / D), ∑ l2 ∈ Finset.Icc 1 (N / D),
          ∑ d ∈ Finset.Icc D (min (N / D) (N / max l1 l2)),
            c l1 * star (c l2) * E (((d : ℝ) * ((l1 : ℝ) - (l2 : ℝ))) * t))
      = ∑ q ∈ ((Finset.Icc 1 (N / D)).product (Finset.Icc 1 (N / D))).sigma
          (fun p => Finset.Icc D (min (N / D) (N / max p.1 p.2))),
          c q.1.1 * star (c q.1.2) *
            E (((q.2 : ℝ) * ((q.1.1 : ℝ) - (q.1.2 : ℝ))) * t) := by
    calc
      (∑ l1 ∈ Finset.Icc 1 (N / D), ∑ l2 ∈ Finset.Icc 1 (N / D),
          ∑ d ∈ Finset.Icc D (min (N / D) (N / max l1 l2)),
            c l1 * star (c l2) * E (((d : ℝ) * ((l1 : ℝ) - (l2 : ℝ))) * t))
          = ∑ p ∈ (Finset.Icc 1 (N / D)).product (Finset.Icc 1 (N / D)),
              ∑ d ∈ Finset.Icc D (min (N / D) (N / max p.1 p.2)),
                c p.1 * star (c p.2) * E (((d : ℝ) * ((p.1 : ℝ) - (p.2 : ℝ))) * t) := by
            rw [show (Finset.Icc 1 (N / D)).product (Finset.Icc 1 (N / D)) =
                Finset.Icc 1 (N / D) ×ˢ Finset.Icc 1 (N / D) from rfl]
            rw [Finset.sum_product]
      _ = ∑ q ∈ ((Finset.Icc 1 (N / D)).product (Finset.Icc 1 (N / D))).sigma
            (fun p => Finset.Icc D (min (N / D) (N / max p.1 p.2))),
            c q.1.1 * star (c q.1.2) *
              E (((q.2 : ℝ) * ((q.1.1 : ℝ) - (q.1.2 : ℝ))) * t) := by
            rw [Finset.sum_sigma']
  rw [hR]
  refine Finset.sum_bij (fun p _ => (⟨(p.2.1, p.2.2), p.1⟩ : Σ _ : ℕ × ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hpd, hpl⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hpl1, hpl2⟩ := Finset.mem_product.mp hpl
    obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.mp hpd
    obtain ⟨hl11, hl12⟩ := Finset.mem_Icc.mp hpl1
    obtain ⟨hl21, hl22⟩ := Finset.mem_Icc.mp hpl2
    have hdpos : 0 < p.1 := by omega
    have hl1L : p.2.1 ≤ N / D := by
      exact le_trans hl12 (Nat.div_le_div_left hd1 hD)
    have hl2L : p.2.2 ≤ N / D := by
      exact le_trans hl22 (Nat.div_le_div_left hd1 hD)
    have hmaxpos : 0 < max p.2.1 p.2.2 := by omega
    have hdle : p.1 ≤ min (N / D) (N / max p.2.1 p.2.2) := by
      apply le_min
      · exact hd2
      · rw [Nat.le_div_iff_mul_le hmaxpos, mul_max, Nat.max_le]
        exact ⟨by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hdpos).mp hl12,
          by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hdpos).mp hl22⟩
    exact Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hl11, hl1L⟩, Finset.mem_Icc.mpr ⟨hl21, hl2L⟩⟩,
      Finset.mem_Icc.mpr ⟨hd1, hdle⟩⟩
  · intro p hp p' hp' heq
    simp only [Sigma.mk.injEq, Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have h2' : p.1 = p'.1 := eq_of_heq h2
    have hp2 : p.2 = p'.2 := Prod.ext h1.1 h1.2
    exact Sigma.ext h2' (heq_of_eq hp2)
  · intro q hq
    obtain ⟨hqp, hqd⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hqp
    obtain ⟨hq11, hq12⟩ := Finset.mem_Icc.mp hq1
    obtain ⟨hq21, hq22⟩ := Finset.mem_Icc.mp hq2
    obtain ⟨hqd1, hqd2⟩ := Finset.mem_Icc.mp hqd
    have hqmaxpos : 0 < max q.1.1 q.1.2 := by omega
    have hq1pos : 0 < q.1.1 := by omega
    have hq2pos : 0 < q.1.2 := by omega
    have hqd2' : q.2 ≤ N / max q.1.1 q.1.2 := le_trans hqd2 (min_le_right _ _)
    have hqdD : q.2 ≤ N / D := le_trans hqd2 (min_le_left _ _)
    have hmul : q.2 * max q.1.1 q.1.2 ≤ N :=
      (Nat.le_div_iff_mul_le hqmaxpos).mp hqd2'
    have hdpos : 0 < q.2 := by omega
    refine ⟨⟨q.2, (q.1.1, q.1.2)⟩, ?_, ?_⟩
    · refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hqd1, hqdD⟩, ?_⟩
      refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hq11, ?_⟩,
        Finset.mem_Icc.mpr ⟨hq21, ?_⟩⟩
      · rw [Nat.le_div_iff_mul_le hdpos]
        calc q.1.1 * q.2 = q.2 * q.1.1 := by ring
          _ ≤ q.2 * max q.1.1 q.1.2 := Nat.mul_le_mul_left _ (le_max_left _ _)
          _ ≤ N := hmul
      · rw [Nat.le_div_iff_mul_le hdpos]
        calc q.1.2 * q.2 = q.2 * q.1.2 := by ring
          _ ≤ q.2 * max q.1.1 q.1.2 := Nat.mul_le_mul_left _ (le_max_right _ _)
          _ ≤ N := hmul
    · rfl
  · intro p hp
    obtain ⟨-, hpl⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hpl1, hpl2⟩ := Finset.mem_product.mp hpl
    rfl

/-- Split a multiple of `B` into `K` consecutive blocks of length `B`. -/
lemma sum_range_mul_eq_sum_blocks (f : ℕ → ℝ) (B K : ℕ) :
    ∑ i ∈ Finset.range (K * B), f i =
      ∑ k ∈ Finset.range K, ∑ i ∈ Finset.range B, f (k * B + i) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Split a range into full blocks of length `B` plus a remainder. -/
lemma sum_range_eq_blocks_add_rem (f : ℕ → ℝ) (B M : ℕ) :
    ∑ i ∈ Finset.range M, f i =
      ∑ k ∈ Finset.range (M / B), ∑ i ∈ Finset.range B, f (k * B + i) +
        ∑ i ∈ Finset.range (M % B), f ((M / B) * B + i) := by
  conv_lhs => rw [← Nat.div_add_mod M B]
  rw [Finset.sum_range_add]
  have h1 : (∑ x ∈ Finset.range (B * (M / B)), f x) =
      ∑ k ∈ Finset.range (M / B), ∑ i ∈ Finset.range B, f (k * B + i) := by
    rw [Nat.mul_comm B (M / B), sum_range_mul_eq_sum_blocks]
  rw [h1]
  congr 1
  rw [Nat.mul_comm B (M / B)]

/-- Shift an `Icc` sum to a `range` sum. -/
lemma sum_Icc_eq_sum_range_shift {α : Type*} [AddCommMonoid α]
    (A M : ℕ) (f : ℕ → α) (hAM : A ≤ M) :
    ∑ d ∈ Finset.Icc A M, f d = ∑ x ∈ Finset.range (M + 1 - A), f (A + x) := by
  have hIcc : Finset.Icc A M = Finset.Ico A (M + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]

/-- Short-block energy with an arbitrary offset `jB` in the inner variable. -/
lemma majorArc_block_energy_offset (q D B d0 jB : ℕ) (a : ℕ) (β : ℝ)
    (c : ℕ → ℂ) (hq : 0 < q) (hcop : Nat.Coprime a q) (hDq : D < q)
    (hβ : |β| ≤ 1 / (2 * (q:ℝ) * (D:ℝ))) :
    ∑ d : Fin (D + 1),
      ‖∑ n : Fin (B + 1),
        (if n.val < B then c (jB + n.val) else 0) *
          E (((jB + n.val : ℕ) : ℝ) *
            (((d0 : ℝ) + (d : ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖ ^ 2
      ≤ (B + 1 + 2 * (q:ℝ)) *
          ∑ n : Fin (B + 1),
            ‖(if n.val < B then c (jB + n.val) else 0)‖ ^ 2 := by
  let c' : Fin (B + 1) → ℂ := fun n => if n.val < B then c (jB + n.val) else 0
  have h := majorArc_block_energy q D d0 B a β c' hq hcop hDq hβ
  have hshift : ∀ d : Fin (D + 1),
      ‖∑ n : Fin (B + 1), c' n * E (((jB + n.val : ℕ) : ℝ) *
          (((d0:ℝ) + (d:ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖
      = ‖∑ n : Fin (B + 1), c' n * E ((n.val : ℝ) *
          (((d0:ℝ) + (d:ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖ := by
    intro d
    have harg : ∀ n : Fin (B + 1),
        ((jB + n.val : ℕ) : ℝ) * (((d0:ℝ) + (d:ℝ)) * ((a:ℝ)/(q:ℝ) + β)) =
          (n.val : ℝ) * (((d0:ℝ) + (d:ℝ)) * ((a:ℝ)/(q:ℝ) + β)) +
            (jB : ℝ) * (((d0:ℝ) + (d:ℝ)) * ((a:ℝ)/(q:ℝ) + β)) := by
      intro n
      push_cast
      ring
    simp_rw [harg]
    exact norm_sum_shift c' _ _
  have hLHS : (∑ d : Fin (D + 1),
      ‖∑ n : Fin (B + 1), c' n * E (((jB + n.val : ℕ) : ℝ) *
        (((d0:ℝ) + (d:ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖ ^ 2)
      = ∑ d : Fin (D + 1),
          ‖∑ n : Fin (B + 1), c' n * E ((n.val : ℝ) *
            (((d0:ℝ) + (d:ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro d _
    rw [hshift d]
  change (∑ d : Fin (D + 1),
      ‖∑ n : Fin (B + 1), c' n * E (((jB + n.val : ℕ) : ℝ) *
        (((d0:ℝ) + (d:ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖ ^ 2) ≤
    (B + 1 + 2 * (q:ℝ)) * ∑ n : Fin (B + 1), ‖c' n‖ ^ 2
  rw [hLHS]
  exact h

/-- Coefficient of a dyadic `(e, m)` box after collapsing to `l = e * m`. -/
noncomputable def typeIIBoxCoeff (E0 M0 l : ℕ) : ℂ :=
  ∑ e ∈ (Finset.Icc E0 (2 * E0 - 1)).filter
      (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1),
    ((Λ : ArithmeticFunction ℝ) e : ℂ)

lemma box_e_m_reindex (d E0 M0 : ℕ) (hE0 : 0 < E0) (hM0 : 0 < M0) (t : ℝ) :
    (∑ e ∈ Finset.Icc E0 (2 * E0 - 1),
        ((Λ : ArithmeticFunction ℝ) e : ℂ) *
          ∑ m ∈ Finset.Icc M0 (2 * M0 - 1),
            E (((d * e * m : ℕ) : ℝ) * t)) =
      ∑ l ∈ Finset.Icc (E0 * M0) (4 * E0 * M0 - 1),
        (∑ e ∈ (Finset.Icc E0 (2 * E0 - 1)).filter
            (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1),
          ((Λ : ArithmeticFunction ℝ) e : ℂ)) *
          E (((d * l : ℕ) : ℝ) * t) := by
  classical
  have hL : (∑ e ∈ Finset.Icc E0 (2 * E0 - 1),
        ((Λ : ArithmeticFunction ℝ) e : ℂ) *
          ∑ m ∈ Finset.Icc M0 (2 * M0 - 1),
            E (((d * e * m : ℕ) : ℝ) * t)) =
      ∑ p ∈ (Finset.Icc E0 (2 * E0 - 1)).sigma
          (fun e => Finset.Icc M0 (2 * M0 - 1)),
        ((Λ : ArithmeticFunction ℝ) p.1 : ℂ) *
          E (((d * p.1 * p.2 : ℕ) : ℝ) * t) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_sigma'
      (s := Finset.Icc E0 (2 * E0 - 1))
      (t := fun e => Finset.Icc M0 (2 * M0 - 1))
      (f := fun e m => ((Λ : ArithmeticFunction ℝ) e : ℂ) *
        E (((d * e * m : ℕ) : ℝ) * t))
  have hR : (∑ l ∈ Finset.Icc (E0 * M0) (4 * E0 * M0 - 1),
        (∑ e ∈ (Finset.Icc E0 (2 * E0 - 1)).filter
            (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1),
          ((Λ : ArithmeticFunction ℝ) e : ℂ)) *
          E (((d * l : ℕ) : ℝ) * t)) =
      ∑ q ∈ (Finset.Icc (E0 * M0) (4 * E0 * M0 - 1)).sigma
          (fun l => (Finset.Icc E0 (2 * E0 - 1)).filter
            (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1)),
        ((Λ : ArithmeticFunction ℝ) q.2 : ℂ) *
          E (((d * q.1 : ℕ) : ℝ) * t) := by
    simp only [Finset.sum_mul]
    exact Finset.sum_sigma'
      (s := Finset.Icc (E0 * M0) (4 * E0 * M0 - 1))
      (t := fun l => (Finset.Icc E0 (2 * E0 - 1)).filter
        (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1))
      (f := fun l e => ((Λ : ArithmeticFunction ℝ) e : ℂ) *
        E (((d * l : ℕ) : ℝ) * t))
  rw [hL, hR]
  refine Finset.sum_bij
    (fun p _ => (⟨p.1 * p.2, p.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hpe, hpm⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hpe1, hpe2⟩ := Finset.mem_Icc.mp hpe
    obtain ⟨hpm1, hpm2⟩ := Finset.mem_Icc.mp hpm
    have hppos : 0 < p.1 := by omega
    have hlpos : 0 < p.1 * p.2 := Nat.mul_pos hppos (by omega)
    have hllow : E0 * M0 ≤ p.1 * p.2 := Nat.mul_le_mul hpe1 hpm1
    have hlhigh : p.1 * p.2 ≤ 4 * E0 * M0 - 1 := by
      have h1 : p.1 ≤ 2 * E0 - 1 := hpe2
      have h2 : p.2 ≤ 2 * M0 - 1 := hpm2
      have h3 : p.1 * p.2 ≤ (2 * E0 - 1) * (2 * M0 - 1) := Nat.mul_le_mul h1 h2
      have h4 : (2 * E0 - 1) * (2 * M0 - 1) ≤ 4 * E0 * M0 - 1 := by
        have hlt : (2 * E0 - 1) * (2 * M0 - 1) < 4 * E0 * M0 := by
          have hElt : 2 * E0 - 1 < 2 * E0 := by omega
          have hMpos : 0 < 2 * M0 - 1 := by omega
          calc
            (2 * E0 - 1) * (2 * M0 - 1) < (2 * E0) * (2 * M0 - 1) :=
              Nat.mul_lt_mul_of_pos_right hElt hMpos
            _ ≤ (2 * E0) * (2 * M0) := Nat.mul_le_mul_left _ (by omega)
            _ = 4 * E0 * M0 := by ring
        omega
      omega
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hllow, hlhigh⟩, ?_⟩
    refine Finset.mem_filter.mpr ⟨hpe, ?_, ?_, ?_⟩
    · exact dvd_mul_right p.1 p.2
    · rw [Nat.mul_div_right p.2 hppos]
      exact hpm1
    · rw [Nat.mul_div_right p.2 hppos]
      exact hpm2
  · intro p hp p' hp' heq
    simp only [Sigma.mk.injEq] at heq
    obtain ⟨hprod, he⟩ := heq
    have he' : p.1 = p'.1 := eq_of_heq he
    have hp1pos : 0 < p.1 := by
      have := (Finset.mem_sigma.mp hp).1
      have := (Finset.mem_Icc.mp this).1
      omega
    have hm : p.2 = p'.2 := by
      apply Nat.mul_left_cancel hp1pos
      calc p.1 * p.2 = p'.1 * p'.2 := hprod
        _ = p.1 * p'.2 := by rw [he']
    exact Sigma.ext he' (heq_of_eq hm)
  · intro q hq
    obtain ⟨hql, hqe⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hql1, hql2⟩ := Finset.mem_Icc.mp hql
    obtain ⟨hqe1, hqe2⟩ := Finset.mem_filter.mp hqe
    obtain ⟨hqedvd, hqm1, hqm2⟩ := hqe2
    have hqepos : 0 < q.2 := by
      have := (Finset.mem_Icc.mp hqe1).1
      omega
    have hq1pos : 0 < q.1 := by
      have hE0M0 : 0 < E0 * M0 := Nat.mul_pos hE0 hM0
      omega
    have hmpos : 0 < q.1 / q.2 := Nat.div_pos (Nat.le_of_dvd hq1pos hqedvd) hqepos
    have hmmem : q.1 / q.2 ∈ Finset.Icc M0 (2 * M0 - 1) :=
      Finset.mem_Icc.mpr ⟨hqm1, hqm2⟩
    refine ⟨⟨q.2, q.1 / q.2⟩, ?_, ?_⟩
    · exact Finset.mem_sigma.mpr ⟨hqe1, hmmem⟩
    · show (⟨q.2 * (q.1 / q.2), q.2⟩ : Σ _ : ℕ, ℕ) = q
      rw [Nat.mul_div_cancel' hqedvd]
  · intro p hp
    obtain ⟨-, hpm⟩ := Finset.mem_sigma.mp hp
    show ((Λ : ArithmeticFunction ℝ) p.1 : ℂ) *
        E (((d * p.1 * p.2 : ℕ) : ℝ) * t) =
      ((Λ : ArithmeticFunction ℝ) p.1 : ℂ) *
        E (((d * (p.1 * p.2) : ℕ) : ℝ) * t)
    have h : d * p.1 * p.2 = d * (p.1 * p.2) := by ring
    rw [h]


lemma norm_typeIIBoxCoeff_le (n E0 M0 l : ℕ) (hl0 : 0 < l) (hl : l ≤ n) :
    ‖typeIIBoxCoeff E0 M0 l‖ ≤ Real.log (n : ℝ) := by
  classical
  have hnonneg : 0 ≤ ∑ e ∈ (Finset.Icc E0 (2 * E0 - 1)).filter
      (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1),
        (Λ : ArithmeticFunction ℝ) e :=
    Finset.sum_nonneg (fun e _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hsub : (Finset.Icc E0 (2 * E0 - 1)).filter
      (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1) ⊆ l.divisors := by
    intro e he
    obtain ⟨-, hedvd, -⟩ := Finset.mem_filter.mp he
    exact Nat.mem_divisors.mpr ⟨hedvd, Nat.ne_of_gt hl0⟩
  have hle : ∑ e ∈ (Finset.Icc E0 (2 * E0 - 1)).filter
        (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1),
          (Λ : ArithmeticFunction ℝ) e ≤
      ∑ e ∈ l.divisors, (Λ : ArithmeticFunction ℝ) e :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun e _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hfull : ∑ e ∈ l.divisors, (Λ : ArithmeticFunction ℝ) e = Real.log (l : ℝ) :=
    ArithmeticFunction.vonMangoldt_sum
  have hlog : Real.log (l : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by exact_mod_cast hl0) (by exact_mod_cast hl)
  have hnorm : ‖typeIIBoxCoeff E0 M0 l‖ =
      ∑ e ∈ (Finset.Icc E0 (2 * E0 - 1)).filter
        (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1),
          (Λ : ArithmeticFunction ℝ) e := by
    unfold typeIIBoxCoeff
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [hnorm]
  calc
    ∑ e ∈ (Finset.Icc E0 (2 * E0 - 1)).filter
        (fun e => e ∣ l ∧ M0 ≤ l / e ∧ l / e ≤ 2 * M0 - 1),
          (Λ : ArithmeticFunction ℝ) e
        ≤ ∑ e ∈ l.divisors, (Λ : ArithmeticFunction ℝ) e := hle
    _ = Real.log (l : ℝ) := hfull
    _ ≤ Real.log (n : ℝ) := hlog

lemma sum_normSq_typeIIBoxCoeff_interval_le (n E0 M0 s B : ℕ)
    (hs : 0 < s) (hBn : s + B - 1 ≤ n) :
    ∑ l ∈ Finset.Icc s (s + B - 1), ‖typeIIBoxCoeff E0 M0 l‖ ^ 2 ≤
      (B : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  calc
    ∑ l ∈ Finset.Icc s (s + B - 1), ‖typeIIBoxCoeff E0 M0 l‖ ^ 2
        ≤ ∑ _l ∈ Finset.Icc s (s + B - 1), (Real.log (n : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro l hl
      have hls : s ≤ l := (Finset.mem_Icc.mp hl).1
      have hln : l ≤ n := by
        have := (Finset.mem_Icc.mp hl).2
        omega
      have h := norm_typeIIBoxCoeff_le n E0 M0 l (by omega) hln
      nlinarith [norm_nonneg (typeIIBoxCoeff E0 M0 l), h]
    _ = ((Finset.Icc s (s + B - 1)).card : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (B : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hcard : (Finset.Icc s (s + B - 1)).card ≤ B := by
        rw [Nat.card_Icc]
        omega
      exact_mod_cast hcard

/-- Core fixed-interval block energy: coefficients bounded by `log n` on the
interval `[s, s+B-1]` give energy at most `(B+1+2q) * B * (log n)^2`. -/
lemma majorArc_coeff_interval_energy (n q D d0 s B : ℕ) (a : ℕ) (β : ℝ)
    (c : ℕ → ℂ) (hq : 0 < q) (hcop : Nat.Coprime a q) (hDq : D < q)
    (hβ : |β| ≤ 1 / (2 * (q:ℝ) * (D:ℝ)))
    (hcoeff : ∀ l, s ≤ l → l ≤ s + B - 1 → ‖c l‖ ≤ Real.log (n : ℝ)) :
    ∑ d : Fin (D + 1),
      ‖∑ j : Fin (B + 1), (if j.val < B then c (s + j.val) else 0) *
          E (((s + j.val : ℕ) : ℝ) *
            (((d0 : ℝ) + (d : ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖ ^ 2
      ≤ ((B : ℝ) + 1 + 2 * (q : ℝ)) *
          (((B : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2) := by
  have h := majorArc_block_energy_offset q D B d0 s a β c hq hcop hDq hβ
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hcoeff_sum : (∑ j : Fin (B + 1),
      ‖(if j.val < B then c (s + j.val) else 0)‖ ^ 2) ≤
      (((B : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2) := by
    calc
      ∑ j : Fin (B + 1), ‖(if j.val < B then c (s + j.val) else 0)‖ ^ 2
          ≤ ∑ _n : Fin (B + 1), (Real.log (n : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j.val < B
        · rw [if_pos hj]
          have hsl : s ≤ s + j.val := by omega
          have hsu : s + j.val ≤ s + B - 1 := by omega
          have hc := hcoeff (s + j.val) hsl hsu
          nlinarith [norm_nonneg (c (s + j.val)), hc]
        · rw [if_neg hj]
          have := sq_nonneg (Real.log (n : ℝ))
          simpa using this
      _ = ((B : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
  exact hcoeff_sum

/-- A dyadic box with `8 D E M ≤ n` is fully inside the Type-II region:
every `d < 2D`, `e < 2E`, `m < 2M` satisfies `d * e * m ≤ n`. -/
lemma box_product_le_of_dyadic (n D E M : ℕ) (h : 8 * D * E * M ≤ n) :
    ∀ d e m : ℕ, D ≤ d → d < 2 * D → E ≤ e → e < 2 * E →
      M ≤ m → m < 2 * M → d * e * m ≤ n := by
  intro d e m hd1 hd2 he1 he2 hm1 hm2
  have hd : d ≤ 2 * D := by omega
  have he : e ≤ 2 * E := by omega
  have hm : m ≤ 2 * M := by omega
  have hde : d * e ≤ (2 * D) * (2 * E) := Nat.mul_le_mul hd he
  have hdem : d * e * m ≤ ((2 * D) * (2 * E)) * (2 * M) :=
    Nat.mul_le_mul hde hm
  have hval : ((2 * D) * (2 * E)) * (2 * M) = 8 * D * E * M := by ring
  rw [hval] at hdem
  exact hdem.trans h

/-- Major-arc energy for a fixed dyadic `(e,m)` box. -/
theorem majorArc_box_energy (n q D d0 E0 M0 : ℕ) (a : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q) (hDq : D < q)
    (hβ : |β| ≤ 1 / (2 * (q:ℝ) * (D:ℝ)))
    (hE0 : 0 < E0) (hM0 : 0 < M0) (hboxn : 4 * E0 * M0 - 1 ≤ n) :
    ∑ d : Fin (D + 1),
      ‖∑ e ∈ Finset.Icc E0 (2 * E0 - 1), ((Λ : ArithmeticFunction ℝ) e : ℂ) *
          ∑ m ∈ Finset.Icc M0 (2 * M0 - 1),
            E ((((d0 + d.val : ℕ) * e * m : ℕ) : ℝ) *
              ((a:ℝ)/(q:ℝ) + β))‖ ^ 2
      ≤ (((3 * E0 * M0 : ℕ) : ℝ) + 1 + 2 * (q : ℝ)) *
          ((((3 * E0 * M0 : ℕ) : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2) := by
  classical
  let s : ℕ := E0 * M0
  let B : ℕ := 3 * E0 * M0
  have hBpos : 0 < B := by
    dsimp only [B]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) hE0) hM0
  have hsum_s : s + B - 1 = 4 * E0 * M0 - 1 := by
    dsimp only [s, B]
    have h4 : E0 * M0 + 3 * E0 * M0 = 4 * E0 * M0 := by ring
    rw [h4]
  have hterm : ∀ d : Fin (D + 1),
      ‖∑ e ∈ Finset.Icc E0 (2 * E0 - 1), ((Λ : ArithmeticFunction ℝ) e : ℂ) *
          ∑ m ∈ Finset.Icc M0 (2 * M0 - 1),
            E ((((d0 + d.val : ℕ) * e * m : ℕ) : ℝ) *
              ((a:ℝ)/(q:ℝ) + β))‖
      = ‖∑ j : Fin (B + 1),
          (if j.val < B then typeIIBoxCoeff E0 M0 (s + j.val) else 0) *
            E (((s + j.val : ℕ) : ℝ) *
              (((d0 : ℝ) + (d : ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖ := by
    intro d
    rw [box_e_m_reindex (d0 + d.val) E0 M0 hE0 hM0 ((a:ℝ)/(q:ℝ) + β)]
    let f : ℕ → ℂ := fun l => typeIIBoxCoeff E0 M0 l *
      E ((((d0 + d.val : ℕ) * l : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β))
    change ‖∑ l ∈ Finset.Icc (E0 * M0) (4 * E0 * M0 - 1), f l‖ =
      ‖∑ j : Fin (B + 1),
          (if j.val < B then typeIIBoxCoeff E0 M0 (s + j.val) else 0) *
            E (((s + j.val : ℕ) : ℝ) *
              (((d0 : ℝ) + (d : ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖
    rw [← hsum_s]
    rw [sum_Icc_eq_sum_range_shift s (s + B - 1) f (by omega)]
    have hfin : (∑ j : Fin (B + 1),
        (if j.val < B then typeIIBoxCoeff E0 M0 (s + j.val) else 0) *
          E (((s + j.val : ℕ) : ℝ) *
            (((d0 : ℝ) + (d : ℝ)) * ((a:ℝ)/(q:ℝ) + β))))
        = ∑ x ∈ Finset.range B, typeIIBoxCoeff E0 M0 (s + x) *
          E ((((d0 + d.val : ℕ) * (s + x) : ℕ) : ℝ) * ((a:ℝ)/(q:ℝ) + β)) := by
      rw [Fin.sum_univ_eq_sum_range
        (f := fun k : ℕ => (if k < B then typeIIBoxCoeff E0 M0 (s + k) else 0) *
          E (((s + k : ℕ) : ℝ) *
            (((d0 : ℝ) + (d : ℝ)) * ((a:ℝ)/(q:ℝ) + β))))
        (n := B + 1)]
      rw [Finset.sum_range_succ]
      simp only [Nat.lt_irrefl, if_false, zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro x hx
      have hxB : x < B := Finset.mem_range.mp hx
      rw [if_pos hxB]
      congr 1
      push_cast
      ring
    rw [hfin]
    have hlen : s + B - 1 + 1 - s = B := by omega
    rw [hlen]
  calc
    ∑ d : Fin (D + 1),
        ‖∑ e ∈ Finset.Icc E0 (2 * E0 - 1), ((Λ : ArithmeticFunction ℝ) e : ℂ) *
          ∑ m ∈ Finset.Icc M0 (2 * M0 - 1),
            E ((((d0 + d.val : ℕ) * e * m : ℕ) : ℝ) *
              ((a:ℝ)/(q:ℝ) + β))‖ ^ 2
        = ∑ d : Fin (D + 1),
            ‖∑ j : Fin (B + 1),
              (if j.val < B then typeIIBoxCoeff E0 M0 (s + j.val) else 0) *
                E (((s + j.val : ℕ) : ℝ) *
                  (((d0 : ℝ) + (d : ℝ)) * ((a:ℝ)/(q:ℝ) + β)))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro d _
      rw [hterm d]
    _ ≤ ((B : ℝ) + 1 + 2 * (q : ℝ)) *
          (((B : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2) := by
      apply majorArc_coeff_interval_energy n q D d0 s B a β
        (typeIIBoxCoeff E0 M0) hq hcop hDq hβ
      intro l hsl hlu
      have hl0 : 0 < l := by
        have : 0 < s := by
          dsimp only [s]
          exact Nat.mul_pos hE0 hM0
        omega
      have hln : l ≤ n := by
        have : l ≤ 4 * E0 * M0 - 1 := by
          calc l ≤ s + B - 1 := hlu
            _ = 4 * E0 * M0 - 1 := hsum_s
        omega
      exact norm_typeIIBoxCoeff_le n E0 M0 l hl0 hln
    _ = (((3 * E0 * M0 : ℕ) : ℝ) + 1 + 2 * (q : ℝ)) *
          ((((3 * E0 * M0 : ℕ) : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2) := by
      dsimp only [B]

/-- The truncated divisor convolution `c_U(l) = ∑_{e | l, e > U} Λ(e)`. -/
noncomputable def typeIICoeff (U l : ℕ) : ℂ :=
  ∑ e ∈ l.divisors.filter (fun e => U < e), ((Λ : ArithmeticFunction ℝ) e : ℂ)

/-- Collapsed Fourier form of the Type-II inner sum. -/
noncomputable def typeIIFourier (n U : ℕ) (t : ℝ) (d : ℕ) : ℂ :=
  ∑ l ∈ Finset.Icc 1 (n / d), typeIICoeff U l * E (((d * l : ℕ) : ℝ) * t)

lemma norm_typeIICoeff_le (n U l : ℕ) (hl : l ≤ n) :
    ‖typeIICoeff U l‖ ≤ Real.log (n : ℝ) := by
  classical
  have hnonneg : 0 ≤ ∑ e ∈ l.divisors.filter (fun e => U < e),
      (Λ : ArithmeticFunction ℝ) e :=
    Finset.sum_nonneg (fun e _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hsub : l.divisors.filter (fun e => U < e) ⊆ l.divisors :=
    Finset.filter_subset _ _
  have hle : ∑ e ∈ l.divisors.filter (fun e => U < e),
        (Λ : ArithmeticFunction ℝ) e ≤
      ∑ e ∈ l.divisors, (Λ : ArithmeticFunction ℝ) e :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun e _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hfull : ∑ e ∈ l.divisors, (Λ : ArithmeticFunction ℝ) e = Real.log (l : ℝ) :=
    ArithmeticFunction.vonMangoldt_sum
  have hlog : Real.log (l : ℝ) ≤ Real.log (n : ℝ) := by
    rcases Nat.eq_zero_or_pos l with h0 | hpos
    · subst l
      simpa using Real.log_natCast_nonneg n
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hl)
  have hnorm : ‖typeIICoeff U l‖ =
      ∑ e ∈ l.divisors.filter (fun e => U < e), (Λ : ArithmeticFunction ℝ) e := by
    unfold typeIICoeff
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [hnorm]
  calc
    ∑ e ∈ l.divisors.filter (fun e => U < e), (Λ : ArithmeticFunction ℝ) e
        ≤ ∑ e ∈ l.divisors, (Λ : ArithmeticFunction ℝ) e := hle
    _ = Real.log (l : ℝ) := hfull
    _ ≤ Real.log (n : ℝ) := hlog

lemma sum_normSq_typeIICoeff_le (n U : ℕ) (s : Finset ℕ)
    (hs : ∀ l ∈ s, l ≤ n) :
    ∑ l ∈ s, ‖typeIICoeff U l‖ ^ 2 ≤ (s.card : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  calc
    ∑ l ∈ s, ‖typeIICoeff U l‖ ^ 2 ≤ ∑ l ∈ s, (Real.log (n : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro l hl
      have h := norm_typeIICoeff_le n U l (hs l hl)
      nlinarith [norm_nonneg (typeIICoeff U l), h]
    _ = (s.card : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- A geometric sum over an arbitrary interval, bounded by `2q` when the
frequency is `1/q`-separated from the integers. -/
lemma norm_geometric_Icc_shift_le (A B : ℕ) (θ : ℝ) (q : ℕ) (hq : 0 < q)
    (hsin : (1:ℝ)/(q:ℝ) ≤ |Real.sin (Real.pi * θ)|) :
    ‖∑ d ∈ Finset.Icc A B, E ((d : ℝ) * θ)‖ ≤ 2 * (q : ℝ) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hsin_ne : Real.sin (Real.pi * θ) ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hsin
    have : (0:ℝ) < 1/(q:ℝ) := by positivity
    linarith
  by_cases hAB : A ≤ B
  · rw [sum_Icc_eq_sum_range_shift A B (fun d => E ((d:ℝ) * θ)) hAB]
    have hfactor : (∑ x ∈ Finset.range (B + 1 - A), E (((A + x : ℕ) : ℝ) * θ))
        = E ((A : ℝ) * θ) * ∑ x ∈ Finset.range (B + 1 - A), E ((x : ℝ) * θ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [← E_add]
      congr 1
      push_cast
      ring
    rw [hfactor, norm_mul, norm_E, one_mul]
    have hlen : B + 1 - A = (B - A) + 1 := by omega
    rw [hlen]
    have hgeom := norm_geometric_sum_le (B - A) θ hsin_ne
    have hrec : 1 / |Real.sin (Real.pi * θ)| ≤ (q:ℝ) := by
      rw [div_le_iff₀ (abs_pos.mpr hsin_ne)]
      have h' : (1:ℝ) ≤ |Real.sin (Real.pi * θ)| * (q:ℝ) := by
        rw [← div_le_iff₀ hqR]
        exact hsin
      simpa [mul_comm] using h'
    calc
      ‖∑ x ∈ Finset.range ((B - A) + 1), E ((x : ℝ) * θ)‖
          ≤ 1 / |Real.sin (Real.pi * θ)| := hgeom
      _ ≤ (q:ℝ) := hrec
      _ ≤ 2 * (q:ℝ) := by nlinarith
  · have hempty : Finset.Icc A B = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty]
    simp

/-- Diagonal contribution of the dispersion expansion: bounded by
`n (log n)^2 (1 + log n)`. -/
lemma diagonal_dispersion_le (n U : ℕ) :
    (∑ l ∈ Finset.Icc 1 (n / (U + 1)),
        ‖typeIICoeff U l‖ ^ 2 * ((n / l : ℕ) : ℝ)) ≤
      (n : ℝ) * (Real.log (n : ℝ)) ^ 2 * (1 + Real.log (n : ℝ)) := by
  classical
  let L := n / (U + 1)
  have hcoeff : ∀ l ∈ Finset.Icc 1 L,
      ‖typeIICoeff U l‖ ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
    intro l hl
    obtain ⟨hl1, hlL⟩ := Finset.mem_Icc.mp hl
    have hLn : L ≤ n := Nat.div_le_self n (U + 1)
    have hln : l ≤ n := by omega
    have h0 : 0 < l := by omega
    have h := norm_typeIICoeff_le n U l hln
    nlinarith [norm_nonneg (typeIICoeff U l), h]
  have hharm : (∑ l ∈ Finset.Icc 1 L, (1:ℝ)/(l:ℝ)) = (harmonic L : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    (∑ l ∈ Finset.Icc 1 L, ‖typeIICoeff U l‖ ^ 2 * ((n / l : ℕ) : ℝ))
        ≤ ∑ l ∈ Finset.Icc 1 L, (Real.log (n : ℝ)) ^ 2 * ((n / l : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_right (hcoeff l hl) (by positivity)
    _ ≤ ∑ l ∈ Finset.Icc 1 L, (Real.log (n : ℝ)) ^ 2 * ((n : ℝ)/(l : ℝ)) := by
      apply Finset.sum_le_sum
      intro l hl
      have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
      have hpos : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl1
      have hcast : ((n / l : ℕ) : ℝ) ≤ (n : ℝ)/(l : ℝ) := Nat.cast_div_le
      exact mul_le_mul_of_nonneg_left hcast (by positivity)
    _ = (Real.log (n : ℝ)) ^ 2 * ((n : ℝ) *
          ∑ l ∈ Finset.Icc 1 L, (1:ℝ)/(l:ℝ)) := by
      rw [← Finset.mul_sum]
      congr 1
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = (Real.log (n : ℝ)) ^ 2 * (n : ℝ) *
          ∑ l ∈ Finset.Icc 1 L, (1:ℝ)/(l:ℝ) := by ring
    _ = (Real.log (n : ℝ)) ^ 2 * (n : ℝ) * (harmonic L : ℝ) := by rw [hharm]
    _ ≤ (Real.log (n : ℝ)) ^ 2 * (n : ℝ) * (1 + Real.log (L : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast harmonic_le_one_add_log L
    _ ≤ (Real.log (n : ℝ)) ^ 2 * (n : ℝ) * (1 + Real.log (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hLn : L ≤ n := Nat.div_le_self n (U + 1)
      have hlog : Real.log (L : ℝ) ≤ Real.log (n : ℝ) := by
        rcases Nat.eq_zero_or_pos L with h0 | hpos
        · rw [h0]
          simpa using Real.log_natCast_nonneg n
        · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hLn)
      linarith
    _ = (n : ℝ) * (Real.log (n : ℝ)) ^ 2 * (1 + Real.log (n : ℝ)) := by ring

/-- Pointwise trivial bound for the collapsed Type-II inner sum. -/
lemma norm_typeIIFourier_le (n U d : ℕ) (t : ℝ) :
    ‖typeIIFourier n U t d‖ ≤ ((n / d : ℕ) : ℝ) * Real.log (n : ℝ) := by
  classical
  unfold typeIIFourier
  calc
    ‖∑ l ∈ Finset.Icc 1 (n / d), typeIICoeff U l * E (((d * l : ℕ) : ℝ) * t)‖
        ≤ ∑ l ∈ Finset.Icc 1 (n / d),
            ‖typeIICoeff U l * E (((d * l : ℕ) : ℝ) * t)‖ := norm_sum_le _ _
    _ ≤ ∑ _l ∈ Finset.Icc 1 (n / d), Real.log (n : ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      have hln : l ≤ n := by
        have hln' : l ≤ n / d := (Finset.mem_Icc.mp hl).2
        calc l ≤ n / d := hln'
          _ ≤ n := Nat.div_le_self n d
      have hc := norm_typeIICoeff_le n U l hln
      rw [norm_mul, norm_E, mul_one]
      exact hc
    _ = ((Finset.Icc 1 (n / d)).card : ℝ) * Real.log (n : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n / d : ℕ) : ℝ) * Real.log (n : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hcard : (Finset.Icc 1 (n / d)).card ≤ n / d := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
      exact_mod_cast hcard

/-- The actual diagonal term of the Type-II dispersion expansion is bounded by
`n (log n)^2 (1 + log n)`. -/
lemma diagonal_dispersion_part_le (n U : ℕ) (t : ℝ) :
    ‖∑ l ∈ Finset.Icc 1 (n / (U + 1)),
        typeIICoeff U l * star (typeIICoeff U l) *
          ∑ d ∈ Finset.Icc (U + 1) (min (n / (U + 1)) (n / l)),
            E (((d : ℝ) * ((l : ℝ) - (l : ℝ))) * t)‖ ≤
      (n : ℝ) * (Real.log (n : ℝ)) ^ 2 * (1 + Real.log (n : ℝ)) := by
  classical
  calc
    ‖∑ l ∈ Finset.Icc 1 (n / (U + 1)),
        typeIICoeff U l * star (typeIICoeff U l) *
          ∑ d ∈ Finset.Icc (U + 1) (min (n / (U + 1)) (n / l)),
            E (((d : ℝ) * ((l : ℝ) - (l : ℝ))) * t)‖
        ≤ ∑ l ∈ Finset.Icc 1 (n / (U + 1)),
            ‖typeIICoeff U l * star (typeIICoeff U l) *
              ∑ d ∈ Finset.Icc (U + 1) (min (n / (U + 1)) (n / l)),
                E (((d : ℝ) * ((l : ℝ) - (l : ℝ))) * t)‖ := norm_sum_le _ _
    _ = ∑ l ∈ Finset.Icc 1 (n / (U + 1)),
          ‖typeIICoeff U l‖ ^ 2 *
            (((Finset.Icc (U + 1) (min (n / (U + 1)) (n / l))).card : ℝ)) := by
      apply Finset.sum_congr rfl
      intro l _
      have harg : ∀ d : ℕ, E (((d : ℝ) * ((l : ℝ) - (l : ℝ))) * t) = 1 := by
        intro d
        simp [E]
      simp_rw [harg]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      change ‖typeIICoeff U l * (starRingEnd ℂ) (typeIICoeff U l) *
          ((Finset.Icc (U + 1) (min (n / (U + 1)) (n / l))).card : ℂ)‖ =
        ‖typeIICoeff U l‖ ^ 2 *
          ((Finset.Icc (U + 1) (min (n / (U + 1)) (n / l))).card : ℝ)
      rw [Complex.mul_conj']
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), Complex.norm_natCast]
    _ ≤ ∑ l ∈ Finset.Icc 1 (n / (U + 1)),
          ‖typeIICoeff U l‖ ^ 2 * ((n / l : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hcard : ((Finset.Icc (U + 1) (min (n / (U + 1)) (n / l))).card : ℝ) ≤
          ((n / l : ℕ) : ℝ) := by
        have hcard_nat : (Finset.Icc (U + 1) (min (n / (U + 1)) (n / l))).card ≤ n / l := by
          rw [Nat.card_Icc, Nat.sub_le_iff_le_add]
          have h2 : min (n / (U + 1)) (n / l) ≤ n / l := min_le_right _ _
          omega
        exact_mod_cast hcard_nat
      exact hcard
    _ ≤ (n : ℝ) * (Real.log (n : ℝ)) ^ 2 * (1 + Real.log (n : ℝ)) := by
      simpa using diagonal_dispersion_le n U

/-- Split a double sum into its diagonal and off-diagonal parts. -/
lemma sum_diagonal_add_offdiag {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ι → ℂ) :
    ∑ x ∈ s, ∑ y ∈ s, f x y =
      (∑ x ∈ s, f x x) + ∑ x ∈ s, ∑ y ∈ s.erase x, f x y := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_erase_add _ _ hx]
  ring

/-- Triangle bound for a filtered double sum: if the kernel is at most `C` on
the filtered pairs, the sum is at most `C * (∑‖c‖)²`. -/
lemma norm_filtered_double_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c : ι → ℂ) (G : ι → ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (p : ι → ι → Prop) [DecidableRel p]
    (hG : ∀ x ∈ s, ∀ y ∈ s, p x y → ‖G x y‖ ≤ C) :
    ‖∑ x ∈ s, ∑ y ∈ s.filter (fun y => p x y), c x * star (c y) * G x y‖ ≤
      C * (∑ x ∈ s, ‖c x‖) * (∑ y ∈ s, ‖c y‖) := by
  calc
    ‖∑ x ∈ s, ∑ y ∈ s.filter (fun y => p x y), c x * star (c y) * G x y‖
        ≤ ∑ x ∈ s,
            ‖∑ y ∈ s.filter (fun y => p x y), c x * star (c y) * G x y‖ :=
      norm_sum_le _ _
    _ ≤ ∑ x ∈ s, ∑ y ∈ s.filter (fun y => p x y),
          ‖c x * star (c y) * G x y‖ := by
      apply Finset.sum_le_sum
      intro x _
      exact norm_sum_le _ _
    _ ≤ ∑ x ∈ s, ∑ y ∈ s.filter (fun y => p x y), ‖c x‖ * ‖c y‖ * C := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      have hyp : p x y := (Finset.mem_filter.mp hy).2
      have h := hG x hx y (Finset.mem_filter.mp hy).1 hyp
      rw [norm_mul, norm_mul, norm_star]
      have hc : 0 ≤ ‖c x‖ * ‖c y‖ := by positivity
      exact mul_le_mul_of_nonneg_left h hc
    _ ≤ ∑ x ∈ s, ∑ y ∈ s, ‖c x‖ * ‖c y‖ * C := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro y _ _
      exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hC
    _ = (∑ x ∈ s, ‖c x‖) * (∑ y ∈ s, ‖c y‖) * C := by
      rw [Finset.sum_mul_sum]
      simp only [Finset.sum_mul]
    _ = C * (∑ x ∈ s, ‖c x‖) * (∑ y ∈ s, ‖c y‖) := by ring

/-- Non-resonance condition `q ∤ (l1 - l2)` for a dispersion pair. -/
def typeIINonresonant (q : ℕ) (l1 l2 : ℕ) : Prop :=
  ¬ (q : ℤ) ∣ (l1 : ℤ) - (l2 : ℤ)

/-- Non-resonant part of the dispersion off-diagonal is at most
`2q (∑‖c‖)²`. -/
lemma typeII_nonresonant_energy_le (s : Finset ℕ) (q : ℕ) (c : ℕ → ℂ)
    (G : ℕ → ℕ → ℂ) [DecidableRel (typeIINonresonant q)]
    (hG : ∀ x ∈ s, ∀ y ∈ s, typeIINonresonant q x y → ‖G x y‖ ≤ 2 * (q:ℝ)) :
    ‖∑ x ∈ s, ∑ y ∈ s.filter (fun y => typeIINonresonant q x y),
        c x * star (c y) * G x y‖ ≤
      2 * (q:ℝ) * (∑ x ∈ s, ‖c x‖) * (∑ y ∈ s, ‖c y‖) := by
  classical
  exact norm_filtered_double_sum_le s c G (2 * (q:ℝ)) (by positivity)
    (fun x y => typeIINonresonant q x y) hG

/-- The actual dispersion kernel: the geometric sum over `d` at frequency
`(l1 - l2) * t`. -/
noncomputable def typeIIKernel (n U : ℕ) (t : ℝ) (l1 l2 : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc (U + 1) (min (n / (U + 1)) (n / max l1 l2)),
    E (((d : ℝ) * ((l1 : ℝ) - (l2 : ℝ))) * t)

/-- The dispersion pair kernel `c(l1) * conj c(l2) * G(l1,l2)`. -/
noncomputable def typeIIPair (n U : ℕ) (t : ℝ) (l1 l2 : ℕ) : ℂ :=
  typeIICoeff U l1 * star (typeIICoeff U l2) * typeIIKernel n U t l1 l2

/-- The diagonal part of the dispersion energy. -/
noncomputable def typeIIDiagonal (n U : ℕ) (t : ℝ) : ℂ :=
  ∑ l ∈ Finset.Icc 1 (n / (U + 1)), typeIIPair n U t l l

/-- The resonant off-diagonal part: `q | (l1-l2)` and `l1 ≠ l2`. -/
noncomputable def typeIIResonantOffDiag (n U q : ℕ) (t : ℝ)
    [DecidableRel (typeIINonresonant q)] : ℂ :=
  ∑ l1 ∈ Finset.Icc 1 (n / (U + 1)),
    ∑ l2 ∈ ((Finset.Icc 1 (n / (U + 1))).filter
      (fun l2 => ¬ typeIINonresonant q l1 l2)).filter (fun l2 => l2 ≠ l1),
      typeIIPair n U t l1 l2

/-- The actual diagonal term is bounded by `n (log n)^2 (1 + log n)`. -/
lemma norm_typeIIDiagonal_le (n U : ℕ) (t : ℝ) :
    ‖typeIIDiagonal n U t‖ ≤
      (n : ℝ) * (Real.log (n : ℝ)) ^ 2 * (1 + Real.log (n : ℝ)) := by
  simpa [typeIIDiagonal, typeIIPair, typeIIKernel, max_self] using
    diagonal_dispersion_part_le n U t

/-- Pointwise kernel bound on non-resonant pairs. -/
lemma norm_typeIIKernel_le (n U q a : ℕ) (β : ℝ) (l1 l2 : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hl1 : l1 ∈ Finset.Icc 1 (n / (U + 1)))
    (hl2 : l2 ∈ Finset.Icc 1 (n / (U + 1)))
    (hnon : typeIINonresonant q l1 l2)
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * ((n / (U + 1) : ℕ) : ℝ))) :
    ‖typeIIKernel n U ((a:ℝ)/(q:ℝ) + β) l1 l2‖ ≤ 2 * (q:ℝ) := by
  classical
  let L := n / (U + 1)
  have hL1 : 1 ≤ L := by
    have h1 := (Finset.mem_Icc.mp hl1).1
    have h2 := (Finset.mem_Icc.mp hl1).2
    omega
  have hne : l1 ≠ l2 := by
    intro h
    apply hnon
    rw [h]
    simp
  rcases le_or_gt l2 l1 with hle | hlt
  · let h := l1 - l2
    have hh1 : 1 ≤ h := by omega
    have hhL : h ≤ L := by
      have h2 := (Finset.mem_Icc.mp hl1).2
      omega
    have hndvd : ¬ q ∣ h := by
      intro hdvd
      apply hnon
      have hcast : ((h : ℕ) : ℤ) = (l1 : ℤ) - (l2 : ℤ) := Nat.cast_sub hle
      rw [← hcast]
      exact_mod_cast hdvd
    have hsin := abs_sin_pi_mul_majorArc_ge_pointwise q L a h β hq hcop hL1 hh1 hhL hndvd hβ
    have hphase : ((l1 : ℝ) - (l2 : ℝ)) = (h : ℝ) := (Nat.cast_sub hle).symm
    have hsin' : (1:ℝ)/(q:ℝ) ≤
        |Real.sin (Real.pi * (((l1:ℝ) - (l2:ℝ)) * ((a:ℝ)/(q:ℝ) + β)))| := by
      rw [hphase]
      exact hsin
    have hbound := norm_geometric_Icc_shift_le (U + 1)
      (min (n / (U + 1)) (n / max l1 l2))
      (((l1:ℝ) - (l2:ℝ)) * ((a:ℝ)/(q:ℝ) + β)) q hq hsin'
    simpa [typeIIKernel, L, mul_assoc] using hbound
  · let h := l2 - l1
    have hh1 : 1 ≤ h := by omega
    have hhL : h ≤ L := by
      have h2 := (Finset.mem_Icc.mp hl2).2
      omega
    have hndvd : ¬ q ∣ h := by
      intro hdvd
      apply hnon
      have hcast : ((h : ℕ) : ℤ) = (l2 : ℤ) - (l1 : ℤ) := Nat.cast_sub hlt.le
      have hneg : (l1 : ℤ) - (l2 : ℤ) = -((h : ℕ) : ℤ) := by
        rw [hcast]; ring
      rw [hneg]
      exact dvd_neg.mpr (by exact_mod_cast hdvd)
    have hsin := abs_sin_pi_mul_majorArc_ge_pointwise q L a h β hq hcop hL1 hh1 hhL hndvd hβ
    have hphase : ((l1 : ℝ) - (l2 : ℝ)) = -((h : ℝ)) := by
      have hcast : ((h : ℕ) : ℝ) = (l2 : ℝ) - (l1 : ℝ) := Nat.cast_sub hlt.le
      rw [hcast]; ring
    have hsin' : (1:ℝ)/(q:ℝ) ≤
        |Real.sin (Real.pi * (((l1:ℝ) - (l2:ℝ)) * ((a:ℝ)/(q:ℝ) + β)))| := by
      rw [hphase]
      rw [show -((h : ℝ)) * ((a:ℝ)/(q:ℝ) + β) =
        -((h : ℝ) * ((a:ℝ)/(q:ℝ) + β)) by ring]
      rw [show Real.pi * (-((h : ℝ) * ((a:ℝ)/(q:ℝ) + β))) =
        -(Real.pi * ((h : ℝ) * ((a:ℝ)/(q:ℝ) + β))) by ring]
      rw [Real.sin_neg, abs_neg]
      exact hsin
    have hbound := norm_geometric_Icc_shift_le (U + 1)
      (min (n / (U + 1)) (n / max l1 l2))
      (((l1:ℝ) - (l2:ℝ)) * ((a:ℝ)/(q:ℝ) + β)) q hq hsin'
    simpa [typeIIKernel, L, mul_assoc] using hbound

/-- Non-resonant part of the actual dispersion energy. -/
lemma typeII_nonresonant_dispersion_energy_le (n U q a : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q)
    [DecidableRel (typeIINonresonant q)]
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * ((n / (U + 1) : ℕ) : ℝ))) :
    ‖∑ l1 ∈ Finset.Icc 1 (n / (U + 1)),
        ∑ l2 ∈ (Finset.Icc 1 (n / (U + 1))).filter
          (fun l2 => typeIINonresonant q l1 l2),
          typeIICoeff U l1 * star (typeIICoeff U l2) *
            typeIIKernel n U ((a:ℝ)/(q:ℝ) + β) l1 l2‖ ≤
      2 * (q:ℝ) *
        (∑ l ∈ Finset.Icc 1 (n / (U + 1)), ‖typeIICoeff U l‖) ^ 2 := by
  classical
  let L := n / (U + 1)
  let s : Finset ℕ := Finset.Icc 1 L
  have hG : ∀ x ∈ s, ∀ y ∈ s, typeIINonresonant q x y →
      ‖typeIIKernel n U ((a:ℝ)/(q:ℝ) + β) x y‖ ≤ 2 * (q:ℝ) := by
    intro x hx y hy hxy
    exact norm_typeIIKernel_le n U q a β x y hq hcop hx hy hxy hβ
  have h := typeII_nonresonant_energy_le s q (typeIICoeff U)
    (typeIIKernel n U ((a:ℝ)/(q:ℝ) + β)) hG
  simpa [s, L, pow_two, mul_assoc] using h

/-- Explicit logarithmic form of the non-resonant energy bound. -/
lemma typeII_nonresonant_dispersion_energy_le_log (n U q a : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q)
    [DecidableRel (typeIINonresonant q)]
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * ((n / (U + 1) : ℕ) : ℝ))) :
    ‖∑ l1 ∈ Finset.Icc 1 (n / (U + 1)),
        ∑ l2 ∈ (Finset.Icc 1 (n / (U + 1))).filter
          (fun l2 => typeIINonresonant q l1 l2),
          typeIICoeff U l1 * star (typeIICoeff U l2) *
            typeIIKernel n U ((a:ℝ)/(q:ℝ) + β) l1 l2‖ ≤
      2 * (q:ℝ) * (((n / (U + 1) : ℕ) : ℝ) * Real.log (n:ℝ)) ^ 2 := by
  classical
  refine (typeII_nonresonant_dispersion_energy_le n U q a β hq hcop hβ).trans ?_
  let L := n / (U + 1)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hL0 : 0 ≤ ((L : ℕ) : ℝ) := by positivity
  have hsum : ∑ l ∈ Finset.Icc 1 L, ‖typeIICoeff U l‖ ≤
      ((L : ℕ) : ℝ) * Real.log (n : ℝ) := by
    calc
      ∑ l ∈ Finset.Icc 1 L, ‖typeIICoeff U l‖
          ≤ ∑ _l ∈ Finset.Icc 1 L, Real.log (n : ℝ) := by
        apply Finset.sum_le_sum
        intro l hl
        have hlL : l ≤ L := (Finset.mem_Icc.mp hl).2
        have hln : l ≤ n := le_trans hlL (by dsimp [L]; exact Nat.div_le_self n (U + 1))
        exact norm_typeIICoeff_le n U l hln
      _ = ((L : ℕ) : ℝ) * Real.log (n : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        norm_num
  have hS : 0 ≤ ∑ l ∈ Finset.Icc 1 L, ‖typeIICoeff U l‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsq : (∑ l ∈ Finset.Icc 1 L, ‖typeIICoeff U l‖) ^ 2 ≤
      (((L : ℕ) : ℝ) * Real.log (n : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hS hsum 2
  calc
    2 * (q:ℝ) * (∑ l ∈ Finset.Icc 1 (n / (U + 1)), ‖typeIICoeff U l‖) ^ 2
        = 2 * (q:ℝ) * (∑ l ∈ Finset.Icc 1 L, ‖typeIICoeff U l‖) ^ 2 := by
          simp only [L]
    _ ≤ 2 * (q:ℝ) * (((L : ℕ) : ℝ) * Real.log (n : ℝ)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left hsq
          positivity
    _ = 2 * (q:ℝ) * (((n / (U + 1) : ℕ) : ℝ) * Real.log (n : ℝ)) ^ 2 := by
          simp only [L]

/-- Dispersion/phase expansion of the Type-II energy: the squared sum becomes
a double sum in `l1,l2` with an inner geometric sum in `d`. -/
theorem typeII_energy_dispersion (n U : ℕ) (t : ℝ) :
    ((∑ d ∈ Finset.Icc (U + 1) (n / (U + 1)),
        ‖typeIIFourier n U t d‖ ^ 2 : ℝ) : ℂ) =
      ∑ l1 ∈ Finset.Icc 1 (n / (U + 1)), ∑ l2 ∈ Finset.Icc 1 (n / (U + 1)),
        typeIICoeff U l1 * star (typeIICoeff U l2) *
          ∑ d ∈ Finset.Icc (U + 1) (min (n / (U + 1)) (n / max l1 l2)),
            E (((d : ℝ) * ((l1 : ℝ) - (l2 : ℝ))) * t) := by
  simpa only [typeIIFourier] using
    dispersion_identity n (U + 1) (by omega) (typeIICoeff U) t

/-- Split the dispersion energy into its non-resonant and resonant parts. -/
lemma typeII_dispersion_split_nonresonant (n U q : ℕ) (t : ℝ)
    [DecidableRel (typeIINonresonant q)] :
    ((∑ d ∈ Finset.Icc (U + 1) (n / (U + 1)),
        ‖typeIIFourier n U t d‖ ^ 2 : ℝ) : ℂ) =
      (∑ l1 ∈ Finset.Icc 1 (n / (U + 1)),
        ∑ l2 ∈ (Finset.Icc 1 (n / (U + 1))).filter
          (fun l2 => typeIINonresonant q l1 l2),
          typeIICoeff U l1 * star (typeIICoeff U l2) *
            typeIIKernel n U t l1 l2)
      + (∑ l1 ∈ Finset.Icc 1 (n / (U + 1)),
        ∑ l2 ∈ (Finset.Icc 1 (n / (U + 1))).filter
          (fun l2 => ¬ typeIINonresonant q l1 l2),
          typeIICoeff U l1 * star (typeIICoeff U l2) *
            typeIIKernel n U t l1 l2) := by
  classical
  rw [typeII_energy_dispersion]
  simp only [typeIIKernel]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l1 _
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.Icc 1 (n / (U + 1)))
    (p := fun l2 => typeIINonresonant q l1 l2)]

/-- The full Type-II dispersion energy is the unconditional non-resonant
bound plus the resonant remainder. -/
lemma typeII_energy_le_nonresonant_add_resonant (n U q a : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q)
    [DecidableRel (typeIINonresonant q)]
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * ((n / (U + 1) : ℕ) : ℝ))) :
    ‖((∑ d ∈ Finset.Icc (U + 1) (n / (U + 1)),
        ‖typeIIFourier n U ((a:ℝ)/(q:ℝ) + β) d‖ ^ 2 : ℝ) : ℂ)‖ ≤
      2 * (q:ℝ) * (∑ l ∈ Finset.Icc 1 (n / (U + 1)), ‖typeIICoeff U l‖) ^ 2
      + ‖∑ l1 ∈ Finset.Icc 1 (n / (U + 1)),
          ∑ l2 ∈ (Finset.Icc 1 (n / (U + 1))).filter
            (fun l2 => ¬ typeIINonresonant q l1 l2),
            typeIICoeff U l1 * star (typeIICoeff U l2) *
              typeIIKernel n U ((a:ℝ)/(q:ℝ) + β) l1 l2‖ := by
  classical
  let t : ℝ := (a:ℝ)/(q:ℝ) + β
  rw [show ((∑ d ∈ Finset.Icc (U + 1) (n / (U + 1)),
        ‖typeIIFourier n U ((a:ℝ)/(q:ℝ) + β) d‖ ^ 2 : ℝ) : ℂ) =
      ((∑ d ∈ Finset.Icc (U + 1) (n / (U + 1)),
        ‖typeIIFourier n U t d‖ ^ 2 : ℝ) : ℂ) by simp only [t]]
  rw [typeII_dispersion_split_nonresonant n U q t]
  refine (norm_add_le _ _).trans ?_
  exact add_le_add_left (by
    simpa only [t] using
      (typeII_nonresonant_dispersion_energy_le n U q a β hq hcop hβ)) _

/-- Split the resonant part of the dispersion energy into its diagonal and
off-diagonal pieces. -/
lemma typeII_resonant_split_diagonal (n U q : ℕ) (t : ℝ)
    [DecidableRel (typeIINonresonant q)] :
    (∑ l1 ∈ Finset.Icc 1 (n / (U + 1)),
        ∑ l2 ∈ (Finset.Icc 1 (n / (U + 1))).filter
          (fun l2 => ¬ typeIINonresonant q l1 l2),
          typeIIPair n U t l1 l2)
      = typeIIDiagonal n U t + typeIIResonantOffDiag n U q t := by
  classical
  rw [typeIIDiagonal, typeIIResonantOffDiag]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l1 hl1
  have hdiagp : ¬ typeIINonresonant q l1 l1 := by
    simp [typeIINonresonant]
  have hdiag : (∑ l2 ∈ ((Finset.Icc 1 (n / (U + 1))).filter
        (fun l2 => ¬ typeIINonresonant q l1 l2)).filter (fun l2 => l2 = l1),
        typeIIPair n U t l1 l2) = typeIIPair n U t l1 l1 := by
    rw [Finset.sum_filter, Finset.sum_ite_eq']
    simp [hl1, hdiagp]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (Finset.Icc 1 (n / (U + 1))).filter
      (fun l2 => ¬ typeIINonresonant q l1 l2))
    (p := fun l2 => l2 = l1)]
  rw [hdiag]

/-- Full Type-II dispersion energy: unconditional non-resonant bound, the
diagonal bound, and the resonant off-diagonal remainder. -/
lemma typeII_energy_le_nonresonant_diagonal_add_resoff (n U q a : ℕ) (β : ℝ)
    (hq : 0 < q) (hcop : Nat.Coprime a q)
    [DecidableRel (typeIINonresonant q)]
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * ((n / (U + 1) : ℕ) : ℝ))) :
    ‖((∑ d ∈ Finset.Icc (U + 1) (n / (U + 1)),
        ‖typeIIFourier n U ((a:ℝ)/(q:ℝ) + β) d‖ ^ 2 : ℝ) : ℂ)‖ ≤
      2 * (q:ℝ) * (∑ l ∈ Finset.Icc 1 (n / (U + 1)), ‖typeIICoeff U l‖) ^ 2
      + (n : ℝ) * (Real.log (n : ℝ)) ^ 2 * (1 + Real.log (n : ℝ))
      + ‖typeIIResonantOffDiag n U q ((a:ℝ)/(q:ℝ) + β)‖ := by
  classical
  let t : ℝ := (a:ℝ)/(q:ℝ) + β
  have hbase := typeII_energy_le_nonresonant_add_resonant n U q a β hq hcop hβ
  have hbase' : ‖((∑ d ∈ Finset.Icc (U + 1) (n / (U + 1)),
        ‖typeIIFourier n U t d‖ ^ 2 : ℝ) : ℂ)‖ ≤
      2 * (q:ℝ) * (∑ l ∈ Finset.Icc 1 (n / (U + 1)), ‖typeIICoeff U l‖) ^ 2
      + ‖∑ l1 ∈ Finset.Icc 1 (n / (U + 1)),
          ∑ l2 ∈ (Finset.Icc 1 (n / (U + 1))).filter
            (fun l2 => ¬ typeIINonresonant q l1 l2),
            typeIICoeff U l1 * star (typeIICoeff U l2) *
              typeIIKernel n U t l1 l2‖ := by
    simpa only [t] using hbase
  have hsplit : (∑ l1 ∈ Finset.Icc 1 (n / (U + 1)),
        ∑ l2 ∈ (Finset.Icc 1 (n / (U + 1))).filter
          (fun l2 => ¬ typeIINonresonant q l1 l2),
          typeIICoeff U l1 * star (typeIICoeff U l2) *
            typeIIKernel n U t l1 l2)
      = typeIIDiagonal n U t + typeIIResonantOffDiag n U q t := by
    simpa only [typeIIPair] using typeII_resonant_split_diagonal n U q t
  calc
    ‖((∑ d ∈ Finset.Icc (U + 1) (n / (U + 1)),
        ‖typeIIFourier n U t d‖ ^ 2 : ℝ) : ℂ)‖
        ≤ 2 * (q:ℝ) * (∑ l ∈ Finset.Icc 1 (n / (U + 1)), ‖typeIICoeff U l‖) ^ 2
          + ‖∑ l1 ∈ Finset.Icc 1 (n / (U + 1)),
              ∑ l2 ∈ (Finset.Icc 1 (n / (U + 1))).filter
                (fun l2 => ¬ typeIINonresonant q l1 l2),
                typeIICoeff U l1 * star (typeIICoeff U l2) *
                  typeIIKernel n U t l1 l2‖ := hbase'
    _ = 2 * (q:ℝ) * (∑ l ∈ Finset.Icc 1 (n / (U + 1)), ‖typeIICoeff U l‖) ^ 2
          + ‖typeIIDiagonal n U t + typeIIResonantOffDiag n U q t‖ := by
          rw [hsplit]
    _ ≤ 2 * (q:ℝ) * (∑ l ∈ Finset.Icc 1 (n / (U + 1)), ‖typeIICoeff U l‖) ^ 2
          + (‖typeIIDiagonal n U t‖ + ‖typeIIResonantOffDiag n U q t‖) := by
          apply add_le_add_right (norm_add_le _ _)
    _ ≤ 2 * (q:ℝ) * (∑ l ∈ Finset.Icc 1 (n / (U + 1)), ‖typeIICoeff U l‖) ^ 2
          + ((n : ℝ) * (Real.log (n : ℝ)) ^ 2 * (1 + Real.log (n : ℝ))
            + ‖typeIIResonantOffDiag n U q t‖) := by
          apply add_le_add_right
          apply add_le_add_left (norm_typeIIDiagonal_le n U t) _
    _ = 2 * (q:ℝ) * (∑ l ∈ Finset.Icc 1 (n / (U + 1)), ‖typeIICoeff U l‖) ^ 2
          + (n : ℝ) * (Real.log (n : ℝ)) ^ 2 * (1 + Real.log (n : ℝ))
          + ‖typeIIResonantOffDiag n U q t‖ := by ring

lemma typeIIInner_eq_typeIIFourier (n U d : ℕ) (hd : 0 < d) (t : ℝ) :
    typeIIInner n U t d = typeIIFourier n U t d := by
  unfold typeIIInner typeIIFourier typeIICoeff
  rw [inner_high_sum_collapse n d U hd t]

/-- Support-truncated Cauchy–Schwarz: if `B` vanishes above `n/(U+1)`, then
the squared weighted sum only sees `d ≤ n/(U+1)`. -/
lemma norm_sum_mu_mul_sq_le_of_support (n U : ℕ) (B : ℕ → ℂ)
    (hsupp : ∀ d, n / (U + 1) < d → B d = 0) :
    ‖∑ d ∈ Finset.Icc (U + 1) n, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2 ≤
      ((n / (U + 1) : ℕ) : ℝ) *
        ∑ d ∈ Finset.Icc (U + 1) (n / (U + 1)), ‖B d‖ ^ 2 := by
  classical
  let s : Finset ℕ := Finset.Icc (U + 1) (n / (U + 1))
  have hsub : s ⊆ Finset.Icc (U + 1) n := by
    intro d hd
    simp only [s, Finset.mem_Icc] at hd ⊢
    have hdivle : n / (U + 1) ≤ n := Nat.div_le_self n (U + 1)
    omega
  have hzero : ∀ d ∈ Finset.Icc (U + 1) n, d ∉ s →
      ((μ : ArithmeticFunction ℝ) d : ℂ) * B d = 0 := by
    intro d hd hds
    have hd1 : U + 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hds' : d ∉ Finset.Icc (U + 1) (n / (U + 1)) := by
      simpa only [s] using hds
    have hdgt : n / (U + 1) < d := by
      by_contra h
      exact hds' (Finset.mem_Icc.mpr ⟨hd1, by omega⟩)
    rw [hsupp d hdgt, mul_zero]
  have hsum : (∑ d ∈ Finset.Icc (U + 1) n,
      ((μ : ArithmeticFunction ℝ) d : ℂ) * B d)
      = ∑ d ∈ s, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d :=
    (Finset.sum_subset hsub hzero).symm
  rw [hsum]
  have h1 : ‖∑ d ∈ s, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ≤
      ∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ := norm_sum_le _ _
  have h2 : (∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖) ^ 2 ≤
      (s.card : ℝ) * ∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : ℕ => (1:ℝ))
      (fun d => ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖)
    simpa using this
  have h3 : ∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2 ≤
      ∑ d ∈ s, ‖B d‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro d _
    have hμ : |(μ : ArithmeticFunction ℝ) d| ≤ 1 := by
      have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
        ArithmeticFunction.abs_moebius_le_one
      have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast h
      simpa using h'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    have hμ2 : |(μ : ArithmeticFunction ℝ) d| ^ 2 ≤ 1 := by
      nlinarith [abs_nonneg ((μ : ArithmeticFunction ℝ) d), hμ]
    nlinarith [sq_nonneg ‖B d‖]
  have hcard : (s.card : ℝ) ≤ ((n / (U + 1) : ℕ) : ℝ) := by
    have hcard_nat : s.card ≤ n / (U + 1) := by
      simp only [s]
      rw [Nat.card_Icc]
      rw [Nat.sub_le_iff_le_add]
      omega
    exact_mod_cast hcard_nat
  have hnorm : 0 ≤ ‖∑ d ∈ s, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ :=
    norm_nonneg _
  calc
    ‖∑ d ∈ s, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2
        ≤ (∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖) ^ 2 :=
      pow_le_pow_left₀ hnorm h1 2
    _ ≤ (s.card : ℝ) * ∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2 := h2
    _ ≤ ((n / (U + 1) : ℕ) : ℝ) *
          ∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ ((n / (U + 1) : ℕ) : ℝ) * ∑ d ∈ s, ‖B d‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)

/-- Refined Type-II Cauchy–Schwarz: the energy only runs over
`d ≤ n/(U+1)`, which removes a spurious factor `U` from the earlier bound. -/
theorem norm_expSum_high_mu_zeta_highLambda_sq_le_range (n U : ℕ) (t : ℝ) :
    ‖expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
        high U (Λ : ArithmeticFunction ℝ)) t‖ ^ 2 ≤
      ((n / (U + 1) : ℕ) : ℝ) *
        ∑ d ∈ Finset.Icc (U + 1) (n / (U + 1)), ‖typeIIInner n U t d‖ ^ 2 := by
  rw [expSum_high_mu_zeta_highLambda_eq n U t]
  apply norm_sum_mu_mul_sq_le_of_support n U (typeIIInner n U t)
  intro d hd
  dsimp only [typeIIInner]
  have hnd : n / d < U + 1 := by
    have hdpos : 0 < d := by
      have hnn : 0 ≤ n / (U + 1) := Nat.zero_le _
      omega
    rw [Nat.div_lt_iff_lt_mul hdpos]
    have h1 : n < d * (U + 1) :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < U + 1)).mp hd
    simpa [Nat.mul_comm] using h1
  rw [Finset.Icc_eq_empty (by omega)]
  simp

/-- Refined Type-II energy with the collapsed divisor-convolution inner sum. -/
theorem norm_expSum_high_mu_zeta_highLambda_sq_le_range' (n U : ℕ) (t : ℝ) :
    ‖expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
        high U (Λ : ArithmeticFunction ℝ)) t‖ ^ 2 ≤
      ((n / (U + 1) : ℕ) : ℝ) *
        ∑ d ∈ Finset.Icc (U + 1) (n / (U + 1)), ‖typeIIFourier n U t d‖ ^ 2 := by
  refine (norm_expSum_high_mu_zeta_highLambda_sq_le_range n U t).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := by
    have := (Finset.mem_Icc.mp hd).1
    omega
  rw [typeIIInner_eq_typeIIFourier n U d hdpos t]

/- Cauchy–Schwarz reduction of the Type-II term: the squared Type-II sum is
controlled by the energy of the inner `(e, m)` sums.  This is exactly the
quantity to which the large sieve is applied. -/
theorem norm_expSum_high_mu_zeta_highLambda_sq_le (n U : ℕ) (t : ℝ) :
    ‖expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
        high U (Λ : ArithmeticFunction ℝ)) t‖ ^ 2 ≤
      ((Finset.Icc (U + 1) n).card : ℝ) *
        ∑ d ∈ Finset.Icc (U + 1) n,
          ‖∑ e ∈ Finset.Icc (U + 1) (n / d),
            ((Λ : ArithmeticFunction ℝ) e : ℂ) *
              ∑ m ∈ Finset.Icc 1 (n / (d * e)),
                E (((d * e * m : ℕ) : ℝ) * t)‖ ^ 2 := by
  classical
  rw [expSum_high_mu_zeta_highLambda_eq n U t]
  let s : Finset ℕ := Finset.Icc (U + 1) n
  let B : ℕ → ℂ := fun d =>
    ∑ e ∈ Finset.Icc (U + 1) (n / d),
      ((Λ : ArithmeticFunction ℝ) e : ℂ) *
        ∑ m ∈ Finset.Icc 1 (n / (d * e)),
          E (((d * e * m : ℕ) : ℝ) * t)
  change ‖∑ d ∈ s, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2 ≤
    (s.card : ℝ) * ∑ d ∈ s, ‖B d‖ ^ 2
  have h1 : ‖∑ d ∈ s, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ≤
      ∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ := norm_sum_le _ _
  have h2 : (∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖) ^ 2 ≤
      (s.card : ℝ) * ∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : ℕ => (1:ℝ))
      (fun d => ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖)
    simpa using this
  have h3 : ∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2 ≤
      ∑ d ∈ s, ‖B d‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro d _
    have hμ : |(μ : ArithmeticFunction ℝ) d| ≤ 1 := by
      have h : |(ArithmeticFunction.moebius d : ℤ)| ≤ 1 :=
        ArithmeticFunction.abs_moebius_le_one
      have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast h
      simpa using h'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    have hμ2 : |(μ : ArithmeticFunction ℝ) d| ^ 2 ≤ 1 := by
      nlinarith [abs_nonneg ((μ : ArithmeticFunction ℝ) d), hμ]
    nlinarith [sq_nonneg ‖B d‖]
  have hnorm : 0 ≤ ‖∑ d ∈ s, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ :=
    norm_nonneg _
  calc
    ‖∑ d ∈ s, ((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2
        ≤ (∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖) ^ 2 :=
      pow_le_pow_left₀ hnorm h1 2
    _ ≤ (s.card : ℝ) * ∑ d ∈ s, ‖((μ : ArithmeticFunction ℝ) d : ℂ) * B d‖ ^ 2 := h2
    _ ≤ (s.card : ℝ) * ∑ d ∈ s, ‖B d‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)

/-- Squared-energy form of the collapsed Type-II term: the inner sums are now
single Fourier transforms of the truncated divisor convolution. -/
theorem norm_expSum_high_mu_zeta_highLambda_sq_le' (n U : ℕ) (t : ℝ) :
    ‖expSum n (high U (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) *
        high U (Λ : ArithmeticFunction ℝ)) t‖ ^ 2 ≤
      ((Finset.Icc (U + 1) n).card : ℝ) *
        ∑ d ∈ Finset.Icc (U + 1) n,
          ‖∑ l ∈ Finset.Icc 1 (n / d),
            (∑ e ∈ l.divisors.filter (fun e => U < e),
              ((Λ : ArithmeticFunction ℝ) e : ℂ)) *
              E (((d * l : ℕ) : ℝ) * t)‖ ^ 2 := by
  refine (norm_expSum_high_mu_zeta_highLambda_sq_le n U t).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := by
    have := (Finset.mem_Icc.mp hd).1
    omega
  rw [inner_high_sum_collapse n d U hdpos t]

end

end PEqualNP.Outside.Vaughan
