import Mathlib

namespace Conjectures.Goldbach.NoUniformConductorThreshold_aux

noncomputable section

def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def Q (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

def numerators (q : ℕ) : Finset ℕ := (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q)

def center (q a : ℕ) : ℝ := (a : ℝ) / q

def width (n q : ℕ) : ℝ := (Q n : ℝ) / ((q : ℝ) * n)

def K (n : ℕ) (t : ℝ) : ℂ := ∑ k ∈ Finset.range (n + 1), E ((k : ℝ) * t)

def unitMean (q a : ℕ) : ℂ :=
  (∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), E ((b : ℝ) * center q a)) /
    (q.totient : ℂ)

def finiteFourier (q a : ℕ) (v : ℕ → ℝ) : ℂ :=
  ∑ b ∈ Finset.range q, (v b : ℂ) * E ((b : ℝ) * center q a)

def secondary (d : ℕ) (c : ℕ → ℕ → ℝ) (ψ : ℕ → ℝ) (m q b : ℕ) : ℝ :=
  if d ∣ q then c q b * ψ m / q.totient else 0

def profileSize (n d : ℕ) (c : ℕ → ℕ → ℝ) (ψ : ℕ → ℝ) (q a : ℕ) : ℝ :=
  (Finset.range (n + 2)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ (n + 1))⟩
    (fun m => ‖finiteFourier q a (secondary d c ψ m q)‖)

def amplified (n : ℕ) (D β : ℝ) : ℝ := D * (1 + 2 * Real.pi * n * |β|)

def prefixCost (n q a : ℕ) (D β : ℝ) : ℝ :=
  amplified n D β * (2 * ‖unitMean q a * K n β‖ + amplified n D β)

def leftEnd (n q a : ℕ) : ℝ := max (center q a - width n q) 0 - center q a

def rightEnd (n q a : ℕ) : ℝ := min (center q a + width n q) 1 - center q a

def exceptionalBudget (n d : ℕ) (D : ℕ → ℕ → ℝ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 (Q n)).filter (fun q => d ∣ q),
    ∑ a ∈ numerators q,
      intervalIntegral (prefixCost n q a (D q a)) (leftEnd n q a) (rightEnd n q a)
        MeasureTheory.volume

def cW (d q b : ℕ) : ℝ := if q = d ∧ b = 0 then Real.sqrt (d : ℝ) else 0

private theorem continuous_E : Continuous E := by
  unfold E
  fun_prop

private theorem continuous_K (n : ℕ) : Continuous (K n) := by
  have h : ∀ m : ℕ, Continuous (fun t : ℝ => ∑ k ∈ Finset.range m, E ((k : ℝ) * t)) := by
    intro m
    induction m with
    | zero => simpa using continuous_const
    | succ m ih =>
        have h1 : (fun t : ℝ => ∑ k ∈ Finset.range (Nat.succ m), E ((k : ℝ) * t))
            = (fun t : ℝ => (∑ k ∈ Finset.range m, E ((k : ℝ) * t))
                + E ((m : ℝ) * t)) := by
          funext t
          exact Finset.sum_range_succ _ m
        rw [h1]
        exact ih.add (continuous_E.comp (continuous_const.mul continuous_id))
  exact h (n + 1)

private theorem continuous_prefixCost (n q a : ℕ) (D : ℝ) :
    Continuous (prefixCost n q a D) := by
  have hamp : Continuous fun β : ℝ => amplified n D β := by
    unfold amplified
    exact continuous_const.mul
      (continuous_const.add (continuous_const.mul continuous_abs))
  have hK : Continuous fun β : ℝ => ‖unitMean q a * K n β‖ :=
    (continuous_const.mul (continuous_K n)).norm
  exact hamp.mul ((continuous_const.mul hK).add hamp)

private theorem E_zero : E 0 = 1 := by
  simp [E]

private theorem finiteFourier_ite (q a : ℕ) (hq : 0 < q) (w : ℝ) :
    finiteFourier q a (fun b => if b = 0 then w else 0) = ((w : ℝ) : ℂ) := by
  have h1 : ∀ b ∈ Finset.range q,
      (((if b = 0 then w else 0 : ℝ) : ℂ) * E ((b : ℝ) * center q a))
        = if b = 0 then ((w : ℝ) : ℂ) * E ((b : ℝ) * center q a) else 0 := by
    intro b _
    by_cases hb : b = 0
    · subst hb; simp
    · simp [hb]
  unfold finiteFourier
  rw [Finset.sum_congr rfl h1]
  simp [Finset.mem_range.mpr hq, E_zero]

private theorem norm_finiteFourier_cW (d q a : ℕ) (hq : 0 < q) :
    ‖finiteFourier q a (cW d q)‖ = if q = d then Real.sqrt (d : ℝ) else 0 := by
  by_cases hqd : q = d
  · have hc : cW d q = (fun b => if b = 0 then Real.sqrt (d : ℝ) else 0) := by
      funext b; unfold cW; simp [hqd]
    rw [hc, finiteFourier_ite q a hq]
    simp [hqd]
  · have hc : cW d q = fun _ => (0 : ℝ) := by
      funext b; unfold cW; simp [hqd]
    rw [hc]
    unfold finiteFourier
    simp [hqd]

private theorem totient_cast (d : ℕ) (hd : Nat.Prime d) :
    ((d.totient : ℕ) : ℝ) = (d : ℝ) - 1 := by
  have h1 : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
    have h2 := Nat.sub_add_cancel hd.pos
    exact_mod_cast h2
  rw [Nat.totient_prime hd]
  linarith

private theorem norm_finiteFourier_secondary (d a m : ℕ) (hd : Nat.Prime d) (ψ : ℕ → ℝ) :
    ‖finiteFourier d a (secondary d (cW d) ψ m d)‖
      = |Real.sqrt (d : ℝ) * ψ m / ((d : ℝ) - 1)| := by
  have hfun : secondary d (cW d) ψ m d
      = (fun b => if b = 0 then Real.sqrt (d : ℝ) * ψ m / ((d : ℝ) - 1) else 0) := by
    funext b
    have h1 : secondary d (cW d) ψ m d b
        = cW d d b * ψ m / ((d.totient : ℕ) : ℝ) := by
      unfold secondary
      simp [dvd_refl]
    have h2 : cW d d b = if b = 0 then Real.sqrt (d : ℝ) else 0 := by
      unfold cW; simp
    rw [h1, h2, totient_cast d hd]
    by_cases hb : b = 0
    · simp [hb]
    · simp [hb]
  rw [hfun, finiteFourier_ite d a hd.pos, Complex.norm_real, Real.norm_eq_abs]

private theorem le_profileSize (n d : ℕ) (c : ℕ → ℕ → ℝ) (ψ : ℕ → ℝ) (q a m : ℕ)
    (hm : m < n + 2) :
    ‖finiteFourier q a (secondary d c ψ m q)‖ ≤ profileSize n d c ψ q a := by
  unfold profileSize
  exact Finset.le_sup' (fun m => ‖finiteFourier q a (secondary d c ψ m q)‖)
    (Finset.mem_range.mpr hm)

private theorem profileSize_nonneg (n d : ℕ) (c : ℕ → ℕ → ℝ) (ψ : ℕ → ℝ) (q a : ℕ) :
    0 ≤ profileSize n d c ψ q a :=
  (norm_nonneg _).trans (le_profileSize n d c ψ q a 0 (by omega))

private theorem profileSize_lower (n d a : ℕ) (hd : Nat.Prime d) (ψ : ℕ → ℝ) (m : ℕ)
    (hm : m < n + 2) (hψ : 0 ≤ ψ m) :
    Real.sqrt (d : ℝ) * ψ m / ((d : ℝ) - 1) ≤ profileSize n d (cW d) ψ d a := by
  have h1 := le_profileSize n d (cW d) ψ d a m hm
  rw [norm_finiteFourier_secondary d a m hd ψ] at h1
  rw [abs_of_nonneg] at h1
  · exact h1
  · have h2 : (0 : ℝ) < (d : ℝ) - 1 := by
      have h2d : 2 ≤ d := by have := hd.one_lt; omega
      have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h2d
      linarith
    positivity

private theorem one_mem_numerators (d : ℕ) (hd : 2 ≤ d) : 1 ∈ numerators d := by
  unfold numerators
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.Coprime.symm (Nat.coprime_one_right d)⟩

private theorem center_nonneg (q a : ℕ) : 0 ≤ center q a := by
  unfold center
  positivity

private theorem center_le_one (q a : ℕ) (ha : a < q + 1) : center q a ≤ 1 := by
  unfold center
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · exact (div_le_one (by exact_mod_cast hq)).2 (by exact_mod_cast (Nat.lt_succ_iff.mp ha))

private theorem width_nonneg (n q : ℕ) : 0 ≤ width n q := by
  unfold width
  exact div_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

private theorem leftEnd_le (n q a : ℕ) : leftEnd n q a ≤ 0 := by
  unfold leftEnd
  have h1 : max (center q a - width n q) 0 ≤ center q a :=
    max_le (sub_le_self _ (width_nonneg n q)) (center_nonneg q a)
  linarith

private theorem rightEnd_ge (n q a : ℕ) (ha : a ∈ numerators q) : 0 ≤ rightEnd n q a := by
  unfold rightEnd
  have ha' : a < q + 1 := Finset.mem_range.mp ((Finset.mem_filter.mp ha).1)
  have h1 : center q a ≤ min (center q a + width n q) 1 :=
    le_min (le_add_of_nonneg_right (width_nonneg n q)) (center_le_one q a ha')
  linarith

private theorem endpoints (n q a : ℕ) (ha : a ∈ numerators q) :
    leftEnd n q a ≤ rightEnd n q a :=
  (leftEnd_le n q a).trans (rightEnd_ge n q a ha)

private theorem le_amplified (n : ℕ) (D x : ℝ) (hD : 0 ≤ D) : D ≤ amplified n D x := by
  unfold amplified
  have h1 : (1 : ℝ) ≤ 1 + 2 * Real.pi * n * |x| := by
    have h2 : (0 : ℝ) ≤ 2 * Real.pi * (n : ℝ) * |x| := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hx := abs_nonneg x
      have hp := Real.pi_pos.le
      positivity
    linarith
  nlinarith

private theorem prefixCost_ge_sq (n q a : ℕ) (D : ℝ) (hD : 0 ≤ D) (x : ℝ) :
    D ^ 2 ≤ prefixCost n q a D x := by
  have hA : D ≤ amplified n D x := le_amplified n D x hD
  have hA0 : 0 ≤ amplified n D x := hD.trans hA
  have h1 : amplified n D x * amplified n D x ≤ prefixCost n q a D x := by
    unfold prefixCost
    nlinarith [mul_nonneg hA0 (norm_nonneg (unitMean q a * K n x))]
  calc D ^ 2 ≤ amplified n D x ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hA) (by linarith : (0 : ℝ) ≤ D + amplified n D x)]
    _ = amplified n D x * amplified n D x := by ring
    _ ≤ prefixCost n q a D x := h1

private theorem prefixCost_nonneg (n q a : ℕ) (D : ℝ) (hD : 0 ≤ D) (x : ℝ) :
    0 ≤ prefixCost n q a D x := (sq_nonneg D).trans (prefixCost_ge_sq n q a D hD x)

private theorem term_ge (n q a : ℕ) (D : ℝ) (hD : 0 ≤ D) (ha : a ∈ numerators q) :
    D ^ 2 * (rightEnd n q a - leftEnd n q a)
      ≤ intervalIntegral (prefixCost n q a D) (leftEnd n q a) (rightEnd n q a)
          MeasureTheory.volume := by
  have hlr : leftEnd n q a ≤ rightEnd n q a := endpoints n q a ha
  have h1 : (fun _ : ℝ => D ^ 2) ≤ fun x => prefixCost n q a D x := fun x =>
    prefixCost_ge_sq n q a D hD x
  have h2 : (∫ x in leftEnd n q a..rightEnd n q a, (D ^ 2 : ℝ))
      ≤ ∫ x in leftEnd n q a..rightEnd n q a, prefixCost n q a D x :=
    intervalIntegral.integral_mono hlr intervalIntegrable_const
      ((continuous_prefixCost n q a D).intervalIntegrable _ _) h1
  rw [intervalIntegral.integral_const] at h2
  simpa [smul_eq_mul, mul_comm] using h2

private theorem term_nonneg (n q a : ℕ) (D : ℝ) (hD : 0 ≤ D) (ha : a ∈ numerators q) :
    0 ≤ intervalIntegral (prefixCost n q a D) (leftEnd n q a) (rightEnd n q a)
        MeasureTheory.volume :=
  intervalIntegral.integral_nonneg_of_forall (endpoints n q a ha)
    (fun x => prefixCost_nonneg n q a D hD x)

private theorem rightEnd_sub_leftEnd (n d : ℕ) (hd : 2 ≤ d) (hn : 0 < n)
    (hQ : (Q n : ℝ) ≤ (n : ℝ)) :
    rightEnd n d 1 - leftEnd n d 1 = 2 * width n d := by
  have hdn0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdn : (0 : ℝ) < (d : ℝ) * n := by positivity
  have hc : center d 1 = 1 / (d : ℝ) := by unfold center; norm_num
  have hw : width n d ≤ center d 1 := by
    rw [hc]
    unfold width
    rw [div_le_div_iff₀ hdn hdn0]
    nlinarith [hQ]
  have h1 : center d 1 + width n d ≤ 1 := by
    have h2 : (n : ℝ) + (Q n : ℝ) ≤ (d : ℝ) * n := by
      have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      nlinarith [hQ, hn0.le]
    have heq : center d 1 + width n d = ((n : ℝ) + (Q n : ℝ)) / ((d : ℝ) * n) := by
      rw [hc]
      unfold width
      have hd' : (d : ℝ) ≠ 0 := ne_of_gt hdn0
      have hdn' : (d : ℝ) * n ≠ 0 := ne_of_gt hdn
      field_simp
    rw [heq, div_le_one hdn]
    exact h2
  have hmax : max (center d 1 - width n d) 0 = center d 1 - width n d :=
    max_eq_left (sub_nonneg.mpr hw)
  have hmin : min (center d 1 + width n d) 1 = center d 1 + width n d := min_eq_left h1
  unfold leftEnd rightEnd
  rw [hmax, hmin]
  ring

private theorem sq_le_two_pow : ∀ k : ℕ, 4 ≤ k → k ^ 2 ≤ 2 ^ k := by
  intro k
  induction k with
  | zero => intro _; omega
  | succ k ih =>
      intro hk
      rcases Nat.lt_or_ge k 4 with h | h
      · have hk3 : k = 3 := by omega
        subst hk3; norm_num
      · have ih' : k ^ 2 ≤ 2 ^ k := ih h
        calc (k + 1) ^ 2 ≤ 2 * k ^ 2 := by nlinarith
          _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih'
          _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

private theorem numeric_final (P Qn d : ℝ) (hP : 0 < P) (hd : 2 ≤ d)
    (hQ : (d + 1) ^ 2 ≤ Qn) : 2 * P / 288 < P * Qn / (d - 1) ^ 2 := by
  have h144 : (d - 1) ^ 2 < 144 * Qn := by nlinarith [hQ]
  have hpos : (0 : ℝ) < (d - 1) ^ 2 := pow_pos (by linarith : (0 : ℝ) < d - 1) 2
  rw [lt_div_iff₀ hpos, div_mul_eq_mul_div,
    div_lt_iff₀ (by norm_num : (0 : ℝ) < 288)]
  nlinarith [mul_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hP (sub_pos.mpr h144))]

theorem witness (Q₀ : ℕ) :
    ∃ (d n : ℕ) (c : ℕ → ℕ → ℝ) (β : ℝ),
      Nat.Prime d ∧ Q₀ ≤ d ∧ d ≤ Q n ∧ 100000000000 < n ∧ Even n ∧ 0 < β ∧ β < 1 ∧
      (∀ m : ℕ, m ≤ n + 1 → |(m : ℝ) ^ β| ≤ m) ∧
      (∀ q ∈ Finset.Icc 1 (Q n), d ∣ q → ∀ a ∈ numerators q,
        ‖finiteFourier q a (c q)‖ ≤ Real.sqrt (d : ℝ)) ∧
      (n : ℝ) / 288 < exceptionalBudget n d (profileSize n d c (fun m => (m : ℝ) ^ β)) := by
  obtain ⟨d, hd, hdp⟩ := Nat.exists_infinite_primes (max Q₀ 41)
  have hd41 : 41 ≤ d := le_trans (le_max_right _ _) hd
  have hdQ₀ : Q₀ ≤ d := le_trans (le_max_left _ _) hd
  have hd2 : 2 ≤ d := by omega
  set n : ℕ := 2 ^ (d + 1) with hn
  set β : ℝ := (d : ℝ) / ((d : ℝ) + 1) with hβ
  set D : ℕ → ℕ → ℝ := profileSize n d (cW d) (fun m => (m : ℝ) ^ β) with hDdef
  have hlog_lo : d + 1 ≤ Nat.log 2 (n + 2) := by
    have h1 : (2 : ℕ) ^ (d + 1) ≤ n + 2 := by rw [hn]; omega
    have h2 := Nat.log_mono_right (b := 2) h1
    rwa [Nat.log_pow (by norm_num)] at h2
  have hlog_hi : Nat.log 2 (n + 2) ≤ d + 1 := by
    have h21 : (2 : ℕ) ^ (d + 1) = 2 ^ d * 2 := by rw [Nat.pow_add]
    have h22 : (2 : ℕ) ^ (d + 2) = 2 ^ d * 4 := by rw [Nat.pow_add]
    have h2d : 1 < 2 ^ d := by
      have : (2 : ℕ) ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at this; omega
    have h2 : n + 2 < 2 ^ (d + 2) := by
      rw [hn, h21, h22]
      omega
    have h3 : Nat.log 2 (n + 2) < d + 2 :=
      (Nat.log_lt_iff_lt_pow (b := 2) (x := d + 2) (y := n + 2) (by norm_num)
        (by omega)).mpr h2
    omega
  have hQeq : Q n = (d + 1) ^ 2 := by
    unfold Q
    have : Nat.log 2 (n + 2) = d + 1 := by omega
    rw [this]
  have hdQ : d ≤ Q n := by
    rw [hQeq]
    have h1 : 1 ≤ d + 1 := Nat.succ_le_succ (Nat.zero_le d)
    calc d ≤ d + 1 := Nat.le_succ d
      _ = 1 * (d + 1) := by ring
      _ ≤ (d + 1) * (d + 1) := Nat.mul_le_mul_right (d + 1) h1
      _ = (d + 1) ^ 2 := by ring
  have hQn : (Q n : ℝ) ≤ (n : ℝ) := by
    have h1 : (d + 1) ^ 2 ≤ n := by rw [hn]; exact sq_le_two_pow (d + 1) (by omega)
    rw [hQeq]
    exact_mod_cast h1
  have hQlo : ((d : ℝ) + 1) ^ 2 ≤ (Q n : ℝ) := by
    rw [hQeq, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  have hbig : 100000000000 < n := by
    have h1 : (2 : ℕ) ^ 42 ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (100000000000 : ℕ) < 2 ^ 42 := by norm_num
    rw [hn]; omega
  have heven : Even n := ⟨2 ^ d, by rw [hn, pow_succ]; ring⟩
  have hβ0 : 0 < β := by
    rw [hβ]
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    positivity
  have hβ1 : β < 1 := by
    rw [hβ, div_lt_one (by positivity : (0 : ℝ) < (d : ℝ) + 1)]
    linarith
  have hβle : β ≤ 1 := le_of_lt hβ1
  have hβne : β ≠ 0 := ne_of_gt hβ0
  have henv : ∀ m : ℕ, m ≤ n + 1 → |(m : ℝ) ^ β| ≤ m := by
    intro m _
    rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) β)]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact (Real.zero_rpow hβne).le
    · have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      calc (m : ℝ) ^ β ≤ (m : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hβle
        _ = (m : ℝ) := Real.rpow_one _
  have hcap : ∀ q ∈ Finset.Icc 1 (Q n), d ∣ q → ∀ a ∈ numerators q,
      ‖finiteFourier q a (cW d q)‖ ≤ Real.sqrt (d : ℝ) := by
    intro q hq _ a _
    have hq1 : 0 < q := by have := (Finset.mem_Icc.mp hq).1; omega
    rw [norm_finiteFourier_cW d q a hq1]
    split_ifs
    · exact le_rfl
    · exact Real.sqrt_nonneg _
  have hψn : ((n : ℕ) : ℝ) ^ β = ((2 : ℕ) ^ d : ℝ) := by
    have e1 : ((n : ℕ) : ℝ) = (2 : ℝ) ^ (d + 1) := by
      rw [hn, Nat.cast_pow]; norm_num
    have e2 : ((d + 1 : ℕ) : ℝ) * β = (d : ℝ) := by
      rw [hβ, Nat.cast_add, Nat.cast_one]
      field_simp
    calc ((n : ℕ) : ℝ) ^ β = ((2 : ℝ) ^ (((d + 1 : ℕ) : ℝ))) ^ β := by
          rw [e1, ← Real.rpow_natCast]
      _ = (2 : ℝ) ^ (((d + 1 : ℕ) : ℝ) * β) := (Real.rpow_mul (by norm_num) _ _).symm
      _ = (2 : ℝ) ^ ((d : ℕ) : ℝ) := by rw [e2]
      _ = (2 : ℝ) ^ d := Real.rpow_natCast _ _
      _ = ((2 : ℕ) ^ d : ℝ) := by simp
  have hDnn : ∀ q a : ℕ, 0 ≤ D q a := by
    intro q a
    rw [hDdef]
    exact profileSize_nonneg n d (cW d) (fun m => (m : ℝ) ^ β) q a
  have hDlo : Real.sqrt (d : ℝ) * ((2 : ℕ) ^ d : ℝ) / ((d : ℝ) - 1) ≤ D d 1 := by
    have h1 : Real.sqrt (d : ℝ) * ((n : ℕ) : ℝ) ^ β / ((d : ℝ) - 1) ≤ D d 1 := by
      rw [hDdef]
      exact profileSize_lower n d 1 hdp (fun m => (m : ℝ) ^ β) n (by omega)
        (Real.rpow_nonneg (Nat.cast_nonneg n) β)
    rw [hψn] at h1
    exact h1
  have hT : (D d 1) ^ 2 * (2 * width n d)
      ≤ intervalIntegral (prefixCost n d 1 (D d 1)) (leftEnd n d 1) (rightEnd n d 1)
          MeasureTheory.volume := by
    have h1 := term_ge n d 1 (D d 1) (hDnn d 1) (one_mem_numerators d hd2)
    rwa [rightEnd_sub_leftEnd n d hd2 (by rw [hn]; positivity) hQn] at h1
  have hB : intervalIntegral (prefixCost n d 1 (D d 1)) (leftEnd n d 1) (rightEnd n d 1)
        MeasureTheory.volume ≤ exceptionalBudget n d D := by
    unfold exceptionalBudget
    have hmemd : d ∈ (Finset.Icc 1 (Q n)).filter (fun q => d ∣ q) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdp.pos, hdQ⟩, dvd_rfl⟩
    have h1 : intervalIntegral (prefixCost n d 1 (D d 1)) (leftEnd n d 1) (rightEnd n d 1)
          MeasureTheory.volume
        ≤ ∑ a ∈ numerators d, intervalIntegral (prefixCost n d a (D d a)) (leftEnd n d a)
            (rightEnd n d a) MeasureTheory.volume :=
      Finset.single_le_sum
        (fun a ha => term_nonneg n d a (D d a) (hDnn d a) ha) (one_mem_numerators d hd2)
    have h2 : (∑ a ∈ numerators d, intervalIntegral (prefixCost n d a (D d a))
          (leftEnd n d a) (rightEnd n d a) MeasureTheory.volume)
        ≤ ∑ q ∈ (Finset.Icc 1 (Q n)).filter (fun q => d ∣ q),
            ∑ a ∈ numerators q, intervalIntegral (prefixCost n q a (D q a))
              (leftEnd n q a) (rightEnd n q a) MeasureTheory.volume :=
      Finset.single_le_sum
        (fun q _ => Finset.sum_nonneg
          (fun a ha => term_nonneg n q a (D q a) (hDnn q a) ha)) hmemd
    exact h1.trans h2
  have hnum : (n : ℝ) / 288 < (D d 1) ^ 2 * (2 * width n d) := by
    have hP : (0 : ℝ) < ((2 : ℕ) ^ d : ℝ) := by positivity
    have hdn0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
      linarith
    have hN2 : (n : ℝ) = 2 * ((2 : ℕ) ^ d : ℝ) := by
      have h3 : ((n : ℕ) : ℝ) = ((2 : ℕ) ^ (d + 1) : ℕ) := by rw [hn]
      rw [h3, Nat.cast_pow, pow_add]
      norm_num
      ring
    have heq : (Real.sqrt (d : ℝ) * ((2 : ℕ) ^ d : ℝ) / ((d : ℝ) - 1)) ^ 2
        * (2 * (Q n : ℝ) / ((d : ℝ) * (n : ℝ)))
        = ((2 : ℕ) ^ d : ℝ) * (Q n : ℝ) / ((d : ℝ) - 1) ^ 2 := by
      have e1 : (Real.sqrt (d : ℝ) * ((2 : ℕ) ^ d : ℝ) / ((d : ℝ) - 1)) ^ 2
          = (d : ℝ) * ((2 : ℕ) ^ d : ℝ) ^ 2 / ((d : ℝ) - 1) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
      rw [e1, hN2]
      have hne1 : (d : ℝ) - 1 ≠ 0 := ne_of_gt hd1
      have hne2 : (d : ℝ) ≠ 0 := ne_of_gt hdn0
      have hne3 : ((2 : ℕ) ^ d : ℝ) ≠ 0 := ne_of_gt hP
      field_simp
    have key : (n : ℝ) / 288
        < (Real.sqrt (d : ℝ) * ((2 : ℕ) ^ d : ℝ) / ((d : ℝ) - 1)) ^ 2
          * (2 * width n d) := by
      have hwe : (2 : ℝ) * width n d = 2 * (Q n : ℝ) / ((d : ℝ) * (n : ℝ)) := by
        unfold width; ring
      rw [hwe, heq, hN2]
      exact numeric_final _ _ _ hP (by exact_mod_cast hd2) hQlo
    have hD2 : (Real.sqrt (d : ℝ) * ((2 : ℕ) ^ d : ℝ) / ((d : ℝ) - 1)) ^ 2 ≤ (D d 1) ^ 2 := by
      have h0 : 0 ≤ Real.sqrt (d : ℝ) * ((2 : ℕ) ^ d : ℝ) / ((d : ℝ) - 1) := by positivity
      have h2 := mul_self_le_mul_self h0 hDlo
      simpa [pow_two] using h2
    have hw0 : (0 : ℝ) ≤ 2 * width n d := by
      have := width_nonneg n d; linarith
    exact key.trans_le (mul_le_mul_of_nonneg_right hD2 hw0)
  have hbudget : (n : ℝ) / 288 < exceptionalBudget n d D := hnum.trans_le (hT.trans hB)
  exact ⟨d, n, cW d, β, hdp, hdQ₀, hdQ, hbig, heven, hβ0, hβ1, henv, hcap, hbudget⟩

end

end Conjectures.Goldbach.NoUniformConductorThreshold_aux

theorem Conjectures.Goldbach.NoUniformConductorThreshold :
let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let Q (n : ℕ) := (Nat.log 2 (n + 2)) ^ 2; let numerators (q : ℕ) := (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q); let center (q a : ℕ) := (a : ℝ) / q; let width (n q : ℕ) := (Q n : ℝ) / ((q : ℝ) * n); let K (n : ℕ) (t : ℝ) := ∑ k ∈ Finset.range (n + 1), E ((k : ℝ) * t); let unitMean (q a : ℕ) := (∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), E ((b : ℝ) * center q a)) / (q.totient : ℂ); let finiteFourier (q a : ℕ) (v : ℕ → ℝ) := ∑ b ∈ Finset.range q, (v b : ℂ) * E ((b : ℝ) * center q a); let secondary (d : ℕ) (c : ℕ → ℕ → ℝ) (ψ : ℕ → ℝ) (m q b : ℕ) := if d ∣ q then c q b * ψ m / q.totient else 0; let profileSize (n d : ℕ) (c : ℕ → ℕ → ℝ) (ψ : ℕ → ℝ) (q a : ℕ) := (Finset.range (n + 2)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ (n + 1))⟩ (fun m => ‖finiteFourier q a (secondary d c ψ m q)‖); let amplified (n : ℕ) (D β : ℝ) := D * (1 + 2 * Real.pi * n * |β|); let prefixCost (n q a : ℕ) (D β : ℝ) := amplified n D β * (2 * ‖unitMean q a * K n β‖ + amplified n D β); let leftEnd (n q a : ℕ) := max (center q a - width n q) 0 - center q a; let rightEnd (n q a : ℕ) := min (center q a + width n q) 1 - center q a; let exceptionalBudget (n d : ℕ) (D : ℕ → ℕ → ℝ) := ∑ q ∈ (Finset.Icc 1 (Q n)).filter (fun q => d ∣ q), ∑ a ∈ numerators q, intervalIntegral (prefixCost n q a (D q a)) (leftEnd n q a) (rightEnd n q a) MeasureTheory.volume; ∀ Q₀ : ℕ, ∃ (d n : ℕ) (c : ℕ → ℕ → ℝ) (β : ℝ), Nat.Prime d ∧ Q₀ ≤ d ∧ d ≤ Q n ∧ 100000000000 < n ∧ Even n ∧ 0 < β ∧ β < 1 ∧ (∀ m : ℕ, m ≤ n + 1 → |(m : ℝ) ^ β| ≤ m) ∧ (∀ q ∈ Finset.Icc 1 (Q n), d ∣ q → ∀ a ∈ numerators q, ‖finiteFourier q a (c q)‖ ≤ Real.sqrt (d : ℝ)) ∧ (n : ℝ) / 288 < exceptionalBudget n d (profileSize n d c (fun m => (m : ℝ) ^ β)) :=
  Conjectures.Goldbach.NoUniformConductorThreshold_aux.witness
