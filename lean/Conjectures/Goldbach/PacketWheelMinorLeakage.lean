import Mathlib

namespace Conjectures.Goldbach.PacketWheelMinorLeakage_aux

noncomputable section

def phase (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def spec (n : ℕ) (a : ℕ → ℝ) (t : ℝ) :=
  Finset.sum (Finset.range (n + 1)) (fun k => (a k : ℂ) * phase ((k : ℝ) * t))

def gridQ (n : ℕ) := (Nat.log 2 (n + 2)) ^ 2

def arcs (n : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ gridQ n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (gridQ n : ℝ) / ((q : ℝ) * (n : ℝ))}

def wheel (k : ℕ) : ℝ := if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0

def gridDistance (t : ℝ) := ‖phase (30 * t) - 1‖

def gridEnvelope (n : ℕ) (t : ℝ) :=
  ((n : ℝ) + 1) ^ 2 / (1 + ((n : ℝ) + 1) ^ 2 * (gridDistance t) ^ 2)

def lorentz (r c t : ℝ) := 1 / (r ^ 2 + (t - c) ^ 2)

theorem measurableArcs (n : ℕ) : MeasurableSet (arcs n) := by
  let Q := gridQ n
  let Index := {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.1 ≤ Q ∧ p.2 ≤ p.1 ∧ p.2.Coprime p.1}
  have cover : arcs n = ⋃ i : Index,
      {t : ℝ | |t - (i.val.2 : ℝ) / (i.val.1 : ℝ)| ≤
        (Q : ℝ) / ((i.val.1 : ℝ) * (n : ℝ))} := by
    ext t
    constructor
    · rintro ⟨q, a, hq, hQ, ha, hc, ht⟩
      exact Set.mem_iUnion.mpr ⟨⟨(q, a), hq, hQ, ha, hc⟩, ht⟩
    · intro ht
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
      exact ⟨i.val.1, i.val.2, i.property.1, i.property.2.1, i.property.2.2.1,
        i.property.2.2.2, hi⟩
  rw [cover]
  exact MeasurableSet.iUnion fun _ =>
    (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const))
      continuous_const).measurableSet

theorem phaseUnit (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem wheelGeometric (n : ℕ) (t : ℝ) :
    spec n wheel t = ((30 : ℝ) / 8 : ℂ) *
      ∑ r ∈ (Finset.range 30).filter (fun r => Nat.Coprime r 30 ∧ r ≤ n),
        phase ((r : ℝ) * t) *
          ∑ j ∈ Finset.range ((n - r) / 30 + 1), phase ((30 : ℝ) * (j : ℝ) * t) := by
  let W := (Finset.range (n + 1)).filter (fun k => Nat.Coprime k 30)
  let R := (Finset.range 30).filter (fun r => Nat.Coprime r 30 ∧ r ≤ n)
  let D := R.sigma (fun r => Finset.range ((n - r) / 30 + 1))
  let E := phase
  have cop (k : ℕ) : Nat.Coprime (k % 30) 30 ↔ Nat.Coprime k 30 := by
    unfold Nat.Coprime
    rw [← Nat.gcd_rec 30 k, Nat.gcd_comm 30 k]
  have addE (x y : ℝ) : E (x + y) = E x * E y := by
    dsimp [E, phase]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have wsum : spec n wheel t = ((30 : ℝ) / 8 : ℂ) * ∑ k ∈ W, E ((k : ℝ) * t) := by
    rw [Finset.mul_sum]
    unfold spec
    dsimp only [W]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hc : Nat.Coprime k 30
    · simp only [wheel, if_pos hc, Complex.ofReal_div, Complex.ofReal_ofNat, E]
    · simp only [wheel, if_neg hc, Complex.ofReal_zero, zero_mul]
  rw [wsum]
  apply congrArg (fun z : ℂ => ((30 : ℝ) / 8 : ℂ) * z)
  calc
    _ = ∑ d ∈ D, E ((d.1 : ℝ) * t) * E (30 * (d.2 : ℝ) * t) := by
      apply Finset.sum_nbij' (fun k : ℕ => (⟨k % 30, k / 30⟩ : Σ _ : ℕ, ℕ))
        (fun d => d.1 + 30 * d.2)
      · intro k hk
        simp only [W, Finset.mem_filter, Finset.mem_range] at hk
        simp only [D, R, Finset.mem_sigma, Finset.mem_filter, Finset.mem_range]
        exact ⟨⟨by omega, (cop k).mpr hk.2, by omega⟩, by omega⟩
      · rintro ⟨r, j⟩ hd
        simp only [D, R, Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at hd
        simp only [W, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, (cop _).mp ?_⟩
        simpa only [show (r + 30 * j) % 30 = r by omega] using hd.1.2.1
      · intro k _
        dsimp
        omega
      · rintro ⟨r, j⟩ hd
        simp only [D, R, Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at hd
        change (⟨(r + 30 * j) % 30, (r + 30 * j) / 30⟩ : Σ _ : ℕ, ℕ) = ⟨r, j⟩
        rw [show (r + 30 * j) % 30 = r by omega, show (r + 30 * j) / 30 = j by omega]
      · intro k _
        change E ((k : ℝ) * t) = E (((k % 30 : ℕ) : ℝ) * t) * E (30 * ((k / 30 : ℕ) : ℝ) * t)
        rw [← addE]
        have he : (k : ℝ) = ((k % 30 : ℕ) : ℝ) + 30 * ((k / 30 : ℕ) : ℝ) := by
          exact_mod_cast (show k = k % 30 + 30 * (k / 30) by omega)
        congr 1
        linear_combination t * he
    _ = _ := by
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro r _
      change (∑ j ∈ Finset.range ((n - r) / 30 + 1), E ((r : ℝ) * t) * E (30 * (j : ℝ) * t)) =
        E ((r : ℝ) * t) * (∑ j ∈ Finset.range ((n - r) / 30 + 1), E (30 * (j : ℝ) * t))
      rw [Finset.mul_sum]

theorem wheelDistanceBound (n : ℕ) (t : ℝ) :
    ‖spec n wheel t‖ * gridDistance t ≤ 60 := by
  let z := phase (30 * t)
  let R := (Finset.range 30).filter (fun r => Nat.Coprime r 30 ∧ r ≤ n)
  let G := fun r : ℕ => phase ((r : ℝ) * t) *
    ∑ j ∈ Finset.range ((n - r) / 30 + 1), phase (30 * (j : ℝ) * t)
  have hz : ‖z‖ = 1 := phaseUnit _
  have phasePow (j : ℕ) : phase (30 * (j : ℝ) * t) = z ^ j := by
    dsimp [z, phase]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have gb (r : ℕ) : ‖G r‖ * gridDistance t ≤ 2 := by
    simp only [G, gridDistance, norm_mul, phaseUnit, one_mul, phasePow]
    change ‖∑ j ∈ Finset.range ((n - r) / 30 + 1), z ^ j‖ * ‖z - 1‖ ≤ 2
    rw [← norm_mul, geom_sum_mul]
    exact (norm_sub_le ..).trans (by norm_num [norm_pow, hz])
  have card : R.card ≤ 8 := by
    have hsub : R ⊆ (Finset.range 30).filter (fun r => Nat.Coprime r 30) := by
      intro r hr
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2.1⟩
    exact (Finset.card_le_card hsub).trans (by decide)
  have whole : ‖∑ r ∈ R, G r‖ * gridDistance t ≤ 16 := by
    calc
      _ ≤ (∑ r ∈ R, ‖G r‖) * gridDistance t :=
        mul_le_mul_of_nonneg_right (norm_sum_le ..) (norm_nonneg _)
      _ = ∑ r ∈ R, ‖G r‖ * gridDistance t := Finset.sum_mul ..
      _ ≤ ∑ _r ∈ R, (2 : ℝ) := Finset.sum_le_sum fun r _ => gb r
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        linarith [show (R.card : ℝ) ≤ 8 by exact_mod_cast card]
  have coeff : ‖((30 : ℝ) / 8 : ℂ)‖ = 30 / 8 := by norm_num [norm_div]
  rw [wheelGeometric, norm_mul, coeff, mul_assoc]
  change (30 / 8 : ℝ) * (‖∑ r ∈ R, G r‖ * gridDistance t) ≤ _
  linarith only [whole]

theorem wheelEnvelope (n : ℕ) (t : ℝ) :
    ‖spec n wheel t‖ ^ 2 ≤ 3616 * gridEnvelope n t := by
  let S := ‖spec n wheel t‖
  let A := (n : ℝ) + 1
  let d := gridDistance t
  have hS : 0 ≤ S := norm_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hd : 0 ≤ d := norm_nonneg _
  have ht : S ≤ 4 * A := by
    calc
      _ ≤ ∑ k ∈ Finset.range (n + 1), ‖(wheel k : ℂ) * phase ((k : ℝ) * t)‖ := norm_sum_le ..
      _ ≤ ∑ _k ∈ Finset.range (n + 1), (4 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul, phaseUnit, mul_one, Complex.norm_real, Real.norm_eq_abs]
        dsimp [wheel]; split <;> norm_num
      _ = _ := by simp [A]; ring
  have hsd : S * d ≤ 60 := wheelDistanceBound n t
  have h1 := pow_le_pow_left₀ hS ht 2
  have h2 := pow_le_pow_left₀ (mul_nonneg hS hd) hsd 2
  change S ^ 2 ≤ 3616 * (A ^ 2 / (1 + A ^ 2 * d ^ 2))
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [h1, mul_le_mul_of_nonneg_left h2 (sq_nonneg A)]

theorem wheelLeakageTransfer
    (pointwise : ∀ n t, ‖spec n wheel t‖ ^ 2 ≤ 3616 * gridEnvelope n t)
    (leak : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∫ t in (0 : ℝ)..1, (arcs n)ᶜ.indicator (gridEnvelope n) t) ≤ ε * (n : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∫ t in (0 : ℝ)..1, (arcs n)ᶜ.indicator (fun u => ‖spec n wheel u‖ ^ 2) t)
        ≤ ε * (n : ℝ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := leak (ε / 3616) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn
  have hg : Continuous (gridEnvelope n) := by
    unfold gridEnvelope gridDistance phase
    fun_prop (disch := intro t; positivity)
  have hs : Continuous (fun u => ‖spec n wheel u‖ ^ 2) := by
    unfold spec phase; fun_prop
  have maskInt {f : ℝ → ℝ} (hc : Continuous f) :
      IntervalIntegrable ((arcs n)ᶜ.indicator f) MeasureTheory.volume (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator (measurableArcs n).compl
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, 3616 * (arcs n)ᶜ.indicator (gridEnvelope n) t := by
      apply intervalIntegral.integral_mono_on (by norm_num) (maskInt hs) ((maskInt hg).const_mul 3616)
      intro t _
      by_cases ht : t ∈ (arcs n)ᶜ
      · simpa only [Set.indicator_of_mem ht] using pointwise n t
      · simp [ht]
    _ ≤ _ := by rw [intervalIntegral.integral_const_mul]; linarith only [hN n hn]

theorem lorentzContinuous {r : ℝ} (hr : 0 < r) (c : ℝ) : Continuous (lorentz r c) := by
  unfold lorentz
  fun_prop (disch := intro t; positivity)

theorem lorentzIntegral {r : ℝ} (hr : 0 < r) (c : ℝ) :
    (∫ t in (0 : ℝ)..1, lorentz r c t) ≤ Real.pi / r := by
  let F := fun t : ℝ => Real.arctan ((t - c) / r) / r
  have deriv (t : ℝ) : HasDerivAt F (lorentz r c t) t := by
    have h := (((Real.hasDerivAt_arctan ((t - c) / r)).comp t
      (((hasDerivAt_id t).sub_const c).div_const r)).div_const r)
    have eq : lorentz r c t = 1 / (1 + ((t - c) / r) ^ 2) * (1 / r) / r := by
      unfold lorentz
      field_simp <;> ring
    rw [eq]
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => deriv t)
    ((lorentzContinuous hr c).intervalIntegrable ..)]
  dsimp [F]
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ hr.le
  have ha := Real.arctan_lt_pi_div_two ((1 - c) / r)
  have hb := Real.neg_pi_div_two_lt_arctan ((0 - c) / r)
  linarith

theorem denominatorExclusion {n k d : ℕ} {t : ℝ} (hn : 0 < n) (hd : 0 < d) (hQ : d ≤ gridQ n)
    (hk : k ≤ d) (hm : t ∉ arcs n) :
    (gridQ n : ℝ) / (d * (n : ℝ)) < |t - (k : ℝ) / d| := by
  obtain ⟨g, a, q, hg, hcop, hk', hq'⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_right k hd)
  have hq : 0 < q := by
    by_contra! hz
    have he : q = 0 := by omega
    rw [he, zero_mul] at hq'
    omega
  have hqd : q ≤ d := Nat.le_of_dvd hd ⟨g, hq'⟩
  have haq : a ≤ q := by
    exact (Nat.mul_le_mul_right_iff hg).mp (show a * g ≤ q * g by omega)
  have eq : (k : ℝ) / d = (a : ℝ) / (q : ℝ) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    have cross : k * q = a * d := by rw [hk', hq']; ring
    exact_mod_cast cross
  by_contra! h
  apply hm
  refine ⟨q, a, hq, hqd.trans hQ, haq, hcop, ?_⟩
  rw [← eq]
  exact h.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hqd : (q : ℝ) ≤ d) (Nat.cast_nonneg _)))

theorem integerChord (v : ℝ) (k : ℕ) (hk : |v - (k : ℝ)| ≤ 1 / 2) :
    4 * |v - (k : ℝ)| ≤ ‖phase v - 1‖ := by
  let u := v - (k : ℝ)
  let x := Real.pi * u
  let y := 2 * Real.pi * v
  have hangle : y = 2 * x + (k : ℝ) * (2 * Real.pi) := by dsimp [y, x, u]; ring
  have hs : ‖phase v - 1‖ ^ 2 = 2 - 2 * Real.cos y := by
    change ‖Complex.exp ((y : ℂ) * Complex.I) - 1‖ ^ 2 = _
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    nlinarith only [Real.sin_sq_add_cos_sq y]
  have he : ‖phase v - 1‖ = 2 * |Real.sin x| := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    change ‖phase v - 1‖ ^ 2 = (2 * |Real.sin x|) ^ 2
    rw [hs, hangle, Real.cos_add_nat_mul_two_pi, Real.cos_two_mul]
    nlinarith only [sq_abs (Real.sin x), Real.sin_sq_add_cos_sq x]
  have hx : |x| ≤ Real.pi / 2 := by
    dsimp [x]; rw [abs_mul, abs_of_pos Real.pi_pos]
    linarith [mul_le_mul_of_nonneg_left hk Real.pi_pos.le]
  have hj := Real.mul_abs_le_abs_sin hx
  have hxu : |x| = Real.pi * |u| := by dsimp [x]; rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [hxu, show 2 / Real.pi * (Real.pi * |u|) = 2 * |u| by field_simp] at hj
  rw [he]
  change 4 * |u| ≤ _
  linarith only [hj]

theorem gridChord (t : ℝ) (k : ℕ) (hk : |30 * t - (k : ℝ)| ≤ 1 / 2) :
    |t - (k : ℝ) / 30| ≤ gridDistance t := by
  have h := integerChord (30 * t) k hk
  have eq : 30 * t - (k : ℝ) = 30 * (t - (k : ℝ) / 30) := by ring
  rw [eq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 30)] at h
  change _ ≤ ‖phase (30 * t) - 1‖
  linarith [abs_nonneg (t - (k : ℝ) / 30)]

theorem gridPointMajorant {n : ℕ} (hn : 0 < n) (hQ : 30 ≤ gridQ n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (arcs n)ᶜ.indicator (gridEnvelope n) t ≤
      ∑ k ∈ Finset.range 31, 2 * lorentz ((gridQ n : ℝ) / (30 * (n : ℝ))) ((k : ℝ) / 30) t := by
  let r := (gridQ n : ℝ) / (30 * (n : ℝ))
  have hq : 0 < gridQ n := by omega
  have hr : 0 < r := by dsimp [r]; positivity
  have nonneg (k : ℕ) : 0 ≤ 2 * lorentz r ((k : ℝ) / 30) t := by unfold lorentz; positivity
  by_cases hm : t ∈ (arcs n)ᶜ
  · rw [Set.indicator_of_mem hm]
    let k := ⌊30 * t + 1 / 2⌋₊
    obtain ⟨h0, h1⟩ := ht
    have hlo : (k : ℝ) ≤ 30 * t + 1 / 2 := Nat.floor_le (by linarith)
    have hhi : 30 * t + 1 / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hk : k ≤ 30 := by
      by_contra! h
      have h' : (31 : ℝ) ≤ k := by exact_mod_cast h
      linarith
    have close : |30 * t - (k : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hdist := gridChord t k close
    have hcut : r ≤ |t - (k : ℝ) / 30| := (denominatorExclusion hn (by decide : 0 < 30) hQ hk hm).le
    have h1' := pow_le_pow_left₀ hr.le (hcut.trans hdist) 2
    have h2' := pow_le_pow_left₀ (abs_nonneg _) hdist 2
    rw [sq_abs] at h2'
    have bound : gridEnvelope n t ≤ 2 * lorentz r ((k : ℝ) / 30) t := by
      unfold gridEnvelope lorentz
      rw [← mul_div_assoc, mul_one]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left (add_le_add h1' h2') (sq_nonneg ((n : ℝ) + 1))]
    exact bound.trans (Finset.single_le_sum (fun k _ => nonneg k)
      (Finset.mem_range.mpr (by omega : k < 31)))
  · rw [Set.indicator_of_notMem hm]
    exact Finset.sum_nonneg fun k _ => nonneg k

theorem gridTailQuantitative (n : ℕ) (hn : 0 < n) (hQ : 30 ≤ gridQ n) :
    (∫ t in (0 : ℝ)..1, (arcs n)ᶜ.indicator (gridEnvelope n) t) ≤
      1860 * Real.pi * (n : ℝ) / (gridQ n : ℝ) := by
  let r := (gridQ n : ℝ) / (30 * (n : ℝ))
  have hq : 0 < gridQ n := by omega
  have hr : 0 < r := by dsimp [r]; positivity
  have hg : Continuous (gridEnvelope n) := by
    unfold gridEnvelope gridDistance phase
    fun_prop (disch := intro t; positivity)
  have hi : IntervalIntegrable ((arcs n)ᶜ.indicator (gridEnvelope n)) MeasureTheory.volume
      (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      (hg.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator (measurableArcs n).compl
  let f := fun (k : ℕ) (t : ℝ) => 2 * lorentz r ((k : ℝ) / 30) t
  have hf (k : ℕ) : Continuous (f k) := continuous_const.mul (lorentzContinuous hr _)
  have hsum : Continuous (fun t => ∑ k ∈ Finset.range 31, f k t) := by fun_prop
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, ∑ k ∈ Finset.range 31, f k t :=
      intervalIntegral.integral_mono_on (by norm_num) hi (hsum.intervalIntegrable ..)
        (fun t ht => gridPointMajorant hn hQ t ht)
    _ = ∑ k ∈ Finset.range 31, 2 * (∫ t in (0 : ℝ)..1, lorentz r ((k : ℝ) / 30) t) := by
      rw [intervalIntegral.integral_finsetSum (fun k _ => (hf k).intervalIntegrable ..)]
      simp only [f, intervalIntegral.integral_const_mul]
    _ ≤ ∑ _k ∈ Finset.range 31, 2 * (Real.pi / r) := Finset.sum_le_sum
      fun k _ => mul_le_mul_of_nonneg_left (lorentzIntegral hr _) (by norm_num)
    _ = _ := by simp [r]; field_simp; ring

theorem gridTail (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, (∫ t in (0 : ℝ)..1, (arcs n)ᶜ.indicator (gridEnvelope n) t) ≤ ε * (n : ℝ) := by
  obtain ⟨M, hM⟩ := exists_nat_ge (1860 * Real.pi / ε)
  let B := max 30 M
  refine ⟨2 ^ B, ?_⟩
  intro n hn
  have hn' : 0 < n := lt_of_lt_of_le (by positivity : 0 < 2 ^ B) hn
  have hb : B ≤ Nat.log 2 (n + 2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have hq : B ≤ gridQ n := by
    unfold gridQ; nlinarith [Nat.le_mul_self (Nat.log 2 (n + 2))]
  apply (gridTailQuantitative n hn' ((le_max_left ..).trans hq)).trans
  have hq' : 0 < gridQ n := by have : 30 ≤ B := le_max_left ..; omega
  have hM' : 1860 * Real.pi / ε ≤ (gridQ n : ℝ) :=
    hM.trans (by exact_mod_cast (le_trans (le_max_right 30 M) hq))
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp hM') (Nat.cast_nonneg (α := ℝ) n)
  linarith only [hh]

theorem main : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    intervalIntegral ((arcs n)ᶜ.indicator (fun u => ‖spec n wheel u‖ ^ 2)) (0 : ℝ) 1
      MeasureTheory.volume ≤ ε * (n : ℝ) :=
  wheelLeakageTransfer wheelEnvelope gridTail

end

end Conjectures.Goldbach.PacketWheelMinorLeakage_aux

theorem Conjectures.Goldbach.PacketWheelMinorLeakage :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, intervalIntegral ((arcs n)ᶜ.indicator (fun t => ‖S n model t‖^2)) (0:ℝ) 1 MeasureTheory.volume ≤ ε*(n:ℝ)
  := Conjectures.Goldbach.PacketWheelMinorLeakage_aux.main
