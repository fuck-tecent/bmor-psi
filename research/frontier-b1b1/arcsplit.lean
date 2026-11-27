import Mathlib
open scoped BigOperators

noncomputable section
namespace B1B1

def E (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

def Qs (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2
def Qcut (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
def Hwide (n : ℕ) : ℕ := 256 * Qcut n * Qs n
def wideArcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qcut n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a:ℝ)/(q:ℝ)| ≤ (Hwide n:ℝ)/((q:ℝ)*(n:ℝ))}

/-- The individual arc of denominator `q` and numerator `a`. -/
def arcSet (n q a : ℕ) : Set ℝ :=
  {t : ℝ | |t - (a:ℝ)/(q:ℝ)| ≤ (Hwide n:ℝ)/((q:ℝ)*(n:ℝ))}

lemma measurableSet_arcSet (n q a : ℕ) : MeasurableSet (arcSet n q a) := by
  unfold arcSet
  exact measurableSet_le (by fun_prop) measurable_const

lemma intervalIntegrable_indicator {f : ℝ → ℂ} {s : Set ℝ} (hf : Continuous f)
    (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator f) MeasureTheory.volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact (hf.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator hs

/-- Membership in the wide arcs, in the arc-family form used by the integral
expansion. -/
lemma mem_wideArcs_iff (n : ℕ) (t : ℝ) :
    t ∈ wideArcs n ↔
      ∃ q ∈ Finset.Icc 1 (Qcut n),
        ∃ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
          t ∈ arcSet n q a := by
  simp only [wideArcs, Set.mem_setOf_eq, arcSet, Finset.mem_Icc, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨q, a, hq1, hqQ, haq, hcop, hle⟩
    exact ⟨q, ⟨hq1, hqQ⟩, a, ⟨by omega, hcop⟩, hle⟩
  · rintro ⟨q, ⟨hq1, hqQ⟩, a, ⟨haq, hcop⟩, hle⟩
    exact ⟨q, a, hq1, hqQ, by omega, hcop, hle⟩

/-- Reduced fractions are equal only if numerator and denominator agree. -/
lemma fraction_inj {q q' a a' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hcop : Nat.Coprime a q) (hcop' : Nat.Coprime a' q')
    (h : (a:ℝ)/(q:ℝ) = (a':ℝ)/(q':ℝ)) : a = a' ∧ q = q' := by
  have hcross : (a:ℤ) * (q':ℤ) = (a':ℤ) * (q:ℤ) := by
    have h' : (a:ℝ) * (q':ℝ) = (a':ℝ) * (q:ℝ) := by
      rw [div_eq_div_iff (by positivity) (by positivity)] at h
      exact h
    exact_mod_cast h'
  have hqq' : q = q' := by
    have hdvd : (q:ℤ) ∣ (q':ℤ) := by
      have hq_dvd : (q:ℤ) ∣ (a:ℤ) * (q':ℤ) :=
        ⟨(a':ℤ), by rw [mul_comm (q:ℤ) (a':ℤ)]; exact hcross⟩
      have hcopZ : IsCoprime (q:ℤ) (a:ℤ) := hcop.symm.isCoprime
      have hq_dvd' : (q:ℤ) ∣ (q':ℤ) * (a:ℤ) := by rw [mul_comm]; exact hq_dvd
      exact hcopZ.dvd_of_dvd_mul_right hq_dvd'
    have hdvd' : q ∣ q' := by exact_mod_cast hdvd
    have hdvd2 : (q':ℤ) ∣ (q:ℤ) := by
      have hq'_dvd : (q':ℤ) ∣ (a':ℤ) * (q:ℤ) :=
        ⟨(a:ℤ), by rw [mul_comm (q':ℤ) (a:ℤ)]; exact hcross.symm⟩
      have hcopZ' : IsCoprime (q':ℤ) (a':ℤ) := hcop'.symm.isCoprime
      have hq'_dvd' : (q':ℤ) ∣ (q:ℤ) * (a':ℤ) := by rw [mul_comm]; exact hq'_dvd
      exact hcopZ'.dvd_of_dvd_mul_right hq'_dvd'
    have hdvd2' : q' ∣ q := by exact_mod_cast hdvd2
    exact Nat.le_antisymm (Nat.le_of_dvd hq' hdvd') (Nat.le_of_dvd hq hdvd2')
  have haa' : a = a' := by
    have hZ : (a:ℤ) * (q:ℤ) = (a':ℤ) * (q:ℤ) := by
      rw [hqq']
      have hc := hcross
      rw [hqq'] at hc
      exact hc
    have hqZ : (q:ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    have h : (a:ℤ) = (a':ℤ) := mul_right_cancel₀ hqZ hZ
    exact_mod_cast h
  exact ⟨haa', hqq'⟩

/-- Radius-sum inequality: for `q, q' ≤ Q₁` the two semi-widths sum to less
than the Farey spacing, provided `512 Q₁² Q < n`. -/
lemma radius_sum_lt (n q q' : ℕ) (hn : 512 * (Qcut n)^2 * Qs n < n)
    (hqQ : q ≤ Qcut n) (hq'Q : q' ≤ Qcut n) :
    (Hwide n : ℝ) * ((q:ℝ) + (q':ℝ)) < (n:ℝ) := by
  have hH : (Hwide n : ℝ) = 256 * (Qcut n : ℝ) * (Qs n : ℝ) := by
    unfold Hwide
    push_cast
    ring
  have hsum : (q:ℝ) + (q':ℝ) ≤ 2 * (Qcut n : ℝ) := by
    have h1 : (q:ℝ) ≤ (Qcut n : ℝ) := by exact_mod_cast hqQ
    have h2 : (q':ℝ) ≤ (Qcut n : ℝ) := by exact_mod_cast hq'Q
    linarith
  have hbound : (Hwide n : ℝ) * ((q:ℝ) + (q':ℝ)) ≤
      256 * (Qcut n : ℝ) * (Qs n : ℝ) * (2 * (Qcut n : ℝ)) := by
    rw [hH]
    apply mul_le_mul_of_nonneg_left hsum
    positivity
  have hcast : (512 * (Qcut n)^2 * Qs n : ℕ) < n := hn
  have hcastR : (256 * (Qcut n : ℝ) * (Qs n : ℝ) * (2 * (Qcut n : ℝ))) < (n:ℝ) := by
    have : (256 * (Qcut n : ℝ) * (Qs n : ℝ) * (2 * (Qcut n : ℝ))) =
        ((512 * (Qcut n)^2 * Qs n : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    exact_mod_cast hcast
  linarith

/-- The individual wide arcs are pairwise disjoint for large `n`. -/
lemma wideArcs_pieces_disjoint (n : ℕ) (hn : 512 * (Qcut n)^2 * Qs n < n)
    {q q' a a' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hqQ : q ≤ Qcut n) (hq'Q : q' ≤ Qcut n)
    (hne : (a:ℝ)/(q:ℝ) ≠ (a':ℝ)/(q':ℝ)) :
    Disjoint (arcSet n q a) (arcSet n q' a') := by
  rw [Set.disjoint_left]
  intro t h1 h2
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hq'pos : (0:ℝ) < (q':ℝ) := by exact_mod_cast hq'
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have : (0:ℕ) < n := by omega
    exact_mod_cast this
  have hspacing : (1:ℝ)/((q:ℝ)*(q':ℝ)) ≤ |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)| := by
    set z : ℤ := (a:ℤ) * (q':ℤ) - (a':ℤ) * (q:ℤ) with hz
    have hzne : z ≠ 0 := by
      intro h0
      apply hne
      have hcross : (a:ℤ) * (q':ℤ) - (a':ℤ) * (q:ℤ) = 0 := by rwa [← hz]
      have h1 : (a:ℤ) * (q':ℤ) = (a':ℤ) * (q:ℤ) := by omega
      have h2 : (a:ℝ) * (q':ℝ) = (a':ℝ) * (q:ℝ) := by exact_mod_cast h1
      rw [div_eq_div_iff (ne_of_gt hqpos) (ne_of_gt hq'pos)]
      exact h2
    have habs : (1:ℤ) ≤ |z| := Int.one_le_abs hzne
    have hkey : |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)| = ((|z| : ℤ) : ℝ)/((q:ℝ)*(q':ℝ)) := by
      have hnum : (a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ) = ((z:ℤ) : ℝ)/((q:ℝ)*(q':ℝ)) := by
        rw [hz]; push_cast; field_simp
      rw [hnum, abs_div, ← Int.cast_abs, abs_of_pos (by positivity : (0:ℝ) < (q:ℝ)*(q':ℝ))]
    rw [hkey]
    exact div_le_div_of_nonneg_right (by exact_mod_cast habs) (by positivity)
  have htri : |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)| ≤
      (Hwide n:ℝ)/((q:ℝ)*(n:ℝ)) + (Hwide n:ℝ)/((q':ℝ)*(n:ℝ)) := by
    calc |(a:ℝ)/(q:ℝ) - (a':ℝ)/(q':ℝ)|
        = |((a:ℝ)/(q:ℝ) - t) + (t - (a':ℝ)/(q':ℝ))| := by ring_nf
      _ ≤ |(a:ℝ)/(q:ℝ) - t| + |t - (a':ℝ)/(q':ℝ)| := abs_add_le _ _
      _ = |t - (a:ℝ)/(q:ℝ)| + |t - (a':ℝ)/(q':ℝ)| := by rw [abs_sub_comm]
      _ ≤ _ := add_le_add h1 h2
  have hlt : (Hwide n:ℝ)/((q:ℝ)*(n:ℝ)) + (Hwide n:ℝ)/((q':ℝ)*(n:ℝ)) <
      (1:ℝ)/((q:ℝ)*(q':ℝ)) := by
    have hsum := radius_sum_lt n q q' hn hqQ hq'Q
    have hden : (Hwide n:ℝ)/((q:ℝ)*(n:ℝ)) + (Hwide n:ℝ)/((q':ℝ)*(n:ℝ)) =
        (Hwide n:ℝ) * ((q:ℝ) + (q':ℝ)) / ((q:ℝ)*(q':ℝ)*(n:ℝ)) := by
      field_simp
      ring
    rw [hden]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hpos : (0:ℝ) < (q:ℝ)*(q':ℝ) := by positivity
    have hsum' := mul_lt_mul_of_pos_right hsum hpos
    nlinarith [hsum']
  exact absurd (lt_of_le_of_lt hspacing (lt_of_le_of_lt htri hlt)) (lt_irrefl _)

/-- Arc indices are unique: a point of the circle lies in at most one wide arc. -/
lemma arcSet_unique (n : ℕ) (hn : 512 * (Qcut n)^2 * Qs n < n)
    {q q' a a' : ℕ}
    (hq : q ∈ Finset.Icc 1 (Qcut n)) (hq' : q' ∈ Finset.Icc 1 (Qcut n))
    (ha : a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q))
    (ha' : a' ∈ (Finset.range (q'+1)).filter (fun a => Nat.Coprime a q'))
    {t : ℝ} (ht : t ∈ arcSet n q a) (ht' : t ∈ arcSet n q' a') :
    q = q' ∧ a = a' := by
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hq'1 : 1 ≤ q' := (Finset.mem_Icc.mp hq').1
  have hqpos : 0 < q := by omega
  have hq'pos : 0 < q' := by omega
  have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
  have hcop' : Nat.Coprime a' q' := (Finset.mem_filter.mp ha').2
  by_cases hfrac : (a:ℝ)/(q:ℝ) = (a':ℝ)/(q':ℝ)
  · obtain ⟨haa, hqq⟩ := fraction_inj hqpos hq'pos hcop hcop' hfrac
    exact ⟨hqq, haa⟩
  · exfalso
    exact Set.disjoint_left.mp
      (wideArcs_pieces_disjoint n hn hqpos hq'pos (Finset.mem_Icc.mp hq).2
        (Finset.mem_Icc.mp hq').2 hfrac) ht ht'

/-- Pointwise: the indicator of the wide arcs is the sum of the indicators of
the individual arcs. -/
lemma wideArcs_indicator_eq_sum (n : ℕ) (hn : 512 * (Qcut n)^2 * Qs n < n)
    (f : ℝ → ℂ) (t : ℝ) :
    (wideArcs n).indicator f t =
      ∑ q ∈ Finset.Icc 1 (Qcut n),
        ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
          (arcSet n q a).indicator f t := by
  classical
  by_cases ht : t ∈ wideArcs n
  · obtain ⟨q0, hq0, a0, ha0, ht0⟩ := (mem_wideArcs_iff n t).mp ht
    have collapse : (∑ q ∈ Finset.Icc 1 (Qcut n),
        ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
          (arcSet n q a).indicator f t) = f t := by
      rw [Finset.sum_eq_single q0]
      · rw [Finset.sum_eq_single a0]
        · exact Set.indicator_of_mem ht0 f
        · intro a ha hane
          exact Set.indicator_of_notMem
            (fun hta => hane (arcSet_unique n hn hq0 hq0 ha0 ha ht0 hta).2.symm) f
        · intro ha0notin
          exact absurd ha0 ha0notin
      · intro q hq hqne
        apply Finset.sum_eq_zero
        intro a ha
        exact Set.indicator_of_notMem
          (fun hta => hqne (arcSet_unique n hn hq hq0 ha ha0 hta ht0).1) f
      · intro hq0notin
        exact absurd hq0 hq0notin
    rw [Set.indicator_of_mem ht f, collapse]
  · have : ∀ q ∈ Finset.Icc 1 (Qcut n),
        (∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
          (arcSet n q a).indicator f t) = 0 := by
      intro q hq
      apply Finset.sum_eq_zero
      intro a ha
      exact Set.indicator_of_notMem
        (fun hta => ht ((mem_wideArcs_iff n t).mpr ⟨q, hq, a, ha, hta⟩)) f
    rw [Set.indicator_of_notMem ht f]
    rw [Finset.sum_congr rfl this]
    simp

/-- The integral over the wide arcs is the sum of the integrals over the
individual arcs. -/
lemma integral_wideArcs_eq_sum (n : ℕ) (hn : 512 * (Qcut n)^2 * Qs n < n)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ t in (0:ℝ)..1, (wideArcs n).indicator f t)
      = ∑ q ∈ Finset.Icc 1 (Qcut n),
          ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
            ∫ t in (0:ℝ)..1, (arcSet n q a).indicator f t := by
  have hpt : ∀ t : ℝ, (wideArcs n).indicator f t =
      ∑ q ∈ Finset.Icc 1 (Qcut n),
        ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
          (arcSet n q a).indicator f t := fun t => wideArcs_indicator_eq_sum n hn f t
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_finsetSum]
    intro a ha
    exact intervalIntegrable_indicator hf (measurableSet_arcSet n q a)
  · intro q hq
    convert IntervalIntegrable.sum ((Finset.range (q+1)).filter (fun a => Nat.Coprime a q))
      (fun a ha => intervalIntegrable_indicator hf (measurableSet_arcSet n q a)) using 1
    ext t
    rw [Finset.sum_apply]

end B1B1
