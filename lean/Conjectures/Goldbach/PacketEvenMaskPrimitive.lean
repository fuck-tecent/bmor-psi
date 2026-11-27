import Mathlib

open MeasureTheory

private theorem cos_sum_le_card (a m : ℕ) (θ : ℝ) :
    |∑ j ∈ Finset.range m, Real.cos (((2*(a+j):ℕ):ℝ)*θ)| ≤ (m:ℝ) := by
  calc |∑ j ∈ Finset.range m, Real.cos (((2*(a+j):ℕ):ℝ)*θ)|
      ≤ ∑ j ∈ Finset.range m, |Real.cos (((2*(a+j):ℕ):ℝ)*θ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range m, (1:ℝ) := by
        refine Finset.sum_le_sum ?_
        intro i _
        exact Real.abs_cos_le_one _
    _ = (m:ℝ) := by simp

private theorem two_sin_mul_cos_sum (a m : ℕ) (θ : ℝ) :
    2 * Real.sin θ * (∑ j ∈ Finset.range m, Real.cos (((2*(a+j):ℕ):ℝ)*θ))
      = Real.sin ((2*(a:ℝ) + 2*(m:ℝ) - 1)*θ) - Real.sin ((2*(a:ℝ) - 1)*θ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hid : 2 * Real.sin θ * Real.cos (((2*(a+m):ℕ):ℝ)*θ)
          = Real.sin ((2*(a:ℝ) + 2*(m:ℝ) + 1)*θ)
            - Real.sin ((2*(a:ℝ) + 2*(m:ℝ) - 1)*θ) := by
        have hcast : ((2*(a+m):ℕ):ℝ) = 2*(a:ℝ) + 2*(m:ℝ) := by push_cast; ring
        rw [hcast]
        have h1 : Real.sin (θ - (2*(a:ℝ) + 2*(m:ℝ))*θ)
            = -Real.sin ((2*(a:ℝ) + 2*(m:ℝ) - 1)*θ) := by
          have he : θ - (2*(a:ℝ) + 2*(m:ℝ))*θ = -((2*(a:ℝ) + 2*(m:ℝ) - 1)*θ) := by ring
          rw [he, Real.sin_neg]
        have h2 : Real.sin (θ + (2*(a:ℝ) + 2*(m:ℝ))*θ)
            = Real.sin ((2*(a:ℝ) + 2*(m:ℝ) + 1)*θ) := by
          congr 1
          ring
        calc 2 * Real.sin θ * Real.cos ((2*(a:ℝ) + 2*(m:ℝ))*θ)
            = Real.sin (θ - (2*(a:ℝ) + 2*(m:ℝ))*θ)
                + Real.sin (θ + (2*(a:ℝ) + 2*(m:ℝ))*θ) :=
              Real.two_mul_sin_mul_cos θ _
          _ = Real.sin ((2*(a:ℝ) + 2*(m:ℝ) + 1)*θ)
                - Real.sin ((2*(a:ℝ) + 2*(m:ℝ) - 1)*θ) := by
              rw [h1, h2]
              ring
      rw [Finset.sum_range_succ, mul_add, ih, hid]
      push_cast
      ring

private theorem cos_sum_bound (a m : ℕ) (θ : ℝ) :
    |∑ j ∈ Finset.range m, Real.cos (((2*(a+j):ℕ):ℝ)*θ)|
      ≤ if Real.sin θ = 0 then (m:ℝ) else min (m:ℝ) (1/|Real.sin θ|) := by
  have hcard : |∑ j ∈ Finset.range m, Real.cos (((2*(a+j):ℕ):ℝ)*θ)| ≤ (m:ℝ) :=
    cos_sum_le_card a m θ
  have hdiv : Real.sin θ ≠ 0 →
      |∑ j ∈ Finset.range m, Real.cos (((2*(a+j):ℕ):ℝ)*θ)| ≤ 1/|Real.sin θ| := by
    intro h
    have htele := two_sin_mul_cos_sum a m θ
    have habs : |2 * Real.sin θ * (∑ j ∈ Finset.range m,
        Real.cos (((2*(a+j):ℕ):ℝ)*θ))| ≤ 2 := by
      rw [htele]
      have hA := Real.abs_sin_le_one ((2*(a:ℝ) + 2*(m:ℝ) - 1)*θ)
      have hB := Real.abs_sin_le_one ((2*(a:ℝ) - 1)*θ)
      calc |Real.sin ((2*(a:ℝ) + 2*(m:ℝ) - 1)*θ) - Real.sin ((2*(a:ℝ) - 1)*θ)|
          ≤ |Real.sin ((2*(a:ℝ) + 2*(m:ℝ) - 1)*θ)|
              + |Real.sin ((2*(a:ℝ) - 1)*θ)| := by
            simpa using abs_sub_le (Real.sin ((2*(a:ℝ) + 2*(m:ℝ) - 1)*θ)) (0:ℝ)
              (Real.sin ((2*(a:ℝ) - 1)*θ))
        _ ≤ 2 := by linarith
    rw [le_div_iff₀ (abs_pos.mpr h)]
    have key : 2 * |Real.sin θ| *
        |∑ j ∈ Finset.range m, Real.cos (((2*(a+j):ℕ):ℝ)*θ)| ≤ 2 := by
      calc 2 * |Real.sin θ| * |∑ j ∈ Finset.range m, Real.cos (((2*(a+j):ℕ):ℝ)*θ)|
          = |2 * Real.sin θ * (∑ j ∈ Finset.range m,
              Real.cos (((2*(a+j):ℕ):ℝ)*θ))| := by
            rw [abs_mul, abs_mul]
            norm_num
        _ ≤ 2 := habs
    nlinarith [abs_nonneg (Real.sin θ)]
  by_cases h : Real.sin θ = 0
  · have he : (if Real.sin θ = 0 then (m:ℝ) else min (m:ℝ) (1/|Real.sin θ|)) = (m:ℝ) := by
      simp [h]
    rw [he]
    exact hcard
  · have he : (if Real.sin θ = 0 then (m:ℝ) else min (m:ℝ) (1/|Real.sin θ|))
        = min (m:ℝ) (1/|Real.sin θ|) := by
      simp [h]
    rw [he]
    exact le_min hcard (hdiv h)

private theorem cos_sum_bound_pi (a m : ℕ) (t : ℝ) :
    |∑ j ∈ Finset.range m, Real.cos (2*Real.pi*((2*(a+j):ℕ):ℝ)*t)|
      ≤ if Real.sin (2*Real.pi*t) = 0 then (m:ℝ)
        else min (m:ℝ) (1/|Real.sin (2*Real.pi*t)|) := by
  have hrw : (∑ j ∈ Finset.range m, Real.cos (2*Real.pi*((2*(a+j):ℕ):ℝ)*t))
      = ∑ j ∈ Finset.range m, Real.cos (((2*(a+j):ℕ):ℝ)*(2*Real.pi*t)) :=
    Finset.sum_congr rfl (fun j _ => by
      rw [show 2*Real.pi*((2*(a+j):ℕ):ℝ)*t = ((2*(a+j):ℕ):ℝ)*(2*Real.pi*t) by ring])
  rw [hrw]
  exact cos_sum_bound a m (2*Real.pi*t)

private theorem arcs_measurable (Q : ℕ → ℕ) (n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))} := by
  have h : {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}
      = ⋃ q : ℕ, ⋃ a : ℕ, ({t : ℝ | 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q}
          ∩ {t : ℝ | |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
      exact ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
      exact ⟨q, a, h1, h2, h3, h4, h5⟩
  rw [h]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  refine (MeasurableSet.const _).inter ?_
  exact measurableSet_le (by fun_prop) (by fun_prop)

private theorem mask_continuous (L : ℕ → ℕ) (n : ℕ) :
    Continuous (fun t : ℝ =>
      (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ)) := by
  fun_prop

private theorem mask_measurable (arcs : ℕ → Set ℝ) (harcs : ∀ k, MeasurableSet (arcs k))
    (K : ℕ → ℝ → ℝ) (hK : ∀ k, Continuous (K k)) (n : ℕ) :
    MeasurableSet {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t} :=
  (harcs n).compl.inter
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)/2)) (hK n)).measurableSet

private theorem onRegion {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable (fun t => s.indicator f t) MeasureTheory.volume (0:ℝ) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
    (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator hs

private theorem envelopeIntegrable (D : Set ℝ) (hD : MeasurableSet D) (m : ℕ) :
    IntervalIntegrable (fun t : ℝ => D.indicator
      (fun u => if Real.sin (2*Real.pi*u) = 0 then (m:ℝ)
        else min (m:ℝ) (1/|Real.sin (2*Real.pi*u)|)) t) MeasureTheory.volume (0:ℝ) 1 := by
  have henv : Measurable (fun u : ℝ => if Real.sin (2*Real.pi*u) = 0 then (m:ℝ)
      else min (m:ℝ) (1/|Real.sin (2*Real.pi*u)|)) := by
    refine Measurable.ite ?_ measurable_const ?_
    · exact measurableSet_eq_fun
        ((Real.continuous_sin.comp (by fun_prop)).measurable) measurable_const
    · exact measurable_const.min (measurable_const.div
        ((continuous_abs.comp (Real.continuous_sin.comp (by fun_prop))).measurable))
  have hfull : Measurable (fun t : ℝ => D.indicator
      (fun u => if Real.sin (2*Real.pi*u) = 0 then (m:ℝ)
        else min (m:ℝ) (1/|Real.sin (2*Real.pi*u)|)) t) := henv.indicator hD
  have hbdd : ∀ t : ℝ, ‖D.indicator
      (fun u => if Real.sin (2*Real.pi*u) = 0 then (m:ℝ)
        else min (m:ℝ) (1/|Real.sin (2*Real.pi*u)|)) t‖ ≤ (m:ℝ) := by
    intro t
    by_cases ht : t ∈ D
    · rw [Set.indicator_of_mem ht, Real.norm_eq_abs]
      split_ifs with hs
      · rw [abs_of_nonneg (Nat.cast_nonneg m)]
      · have h1 : (0:ℝ) ≤ min (m:ℝ) (1/|Real.sin (2*Real.pi*t)|) :=
          le_min (Nat.cast_nonneg m) (by positivity)
        have h2 : min (m:ℝ) (1/|Real.sin (2*Real.pi*t)|) ≤ (m:ℝ) := min_le_left _ _
        rw [abs_of_nonneg h1]
        exact h2
    · rw [Set.indicator_of_notMem ht, Real.norm_eq_abs, abs_zero]
      exact Nat.cast_nonneg m
  have hInt : Integrable (fun t : ℝ => D.indicator
      (fun u => if Real.sin (2*Real.pi*u) = 0 then (m:ℝ)
        else min (m:ℝ) (1/|Real.sin (2*Real.pi*u)|)) t)
      (MeasureTheory.volume.restrict (Set.Ioc 0 1)) :=
    (integrable_const (m:ℝ)).mono' hfull.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => hbdd t))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact hInt

theorem Conjectures.Goldbach.PacketEvenMaskPrimitive :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∀ (n a m : ℕ), |∑ j ∈ Finset.range m, V n (2*(a+j))| ≤ intervalIntegral ((B n).indicator (fun t => if Real.sin (2*Real.pi*t) = 0 then (m:ℝ) else min (m:ℝ) (1/|Real.sin (2*Real.pi*t)|))) (0:ℝ) 1 MeasureTheory.volume := by
  intro w E S Q arcs low high I L K B U V A model short long n a m
  have hB : MeasurableSet (B n) :=
    mask_measurable arcs (fun k => arcs_measurable Q k) K (fun k => mask_continuous L k) n
  have hcos : ∀ j : ℕ, Continuous (fun u : ℝ => Real.cos (2*Real.pi*((2*(a+j):ℕ):ℝ)*u)) := by
    intro j
    fun_prop
  have hii : ∀ j ∈ Finset.range m, IntervalIntegrable
      (fun t => (B n).indicator (fun u => Real.cos (2*Real.pi*((2*(a+j):ℕ):ℝ)*u)) t)
      MeasureTheory.volume (0:ℝ) 1 := by
    intro j _
    exact onRegion hB (hcos j)
  have hV : ∀ h : ℕ, V n h = intervalIntegral
      ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1
      MeasureTheory.volume := by
    intro h
    rfl
  have hstep1 : (∑ j ∈ Finset.range m, V n (2*(a+j)))
      = intervalIntegral (fun t => ∑ j ∈ Finset.range m,
          (B n).indicator (fun u => Real.cos (2*Real.pi*((2*(a+j):ℕ):ℝ)*u)) t)
        (0:ℝ) 1 MeasureTheory.volume := by
    calc (∑ j ∈ Finset.range m, V n (2*(a+j)))
        = ∑ j ∈ Finset.range m, intervalIntegral
            (fun t => (B n).indicator (fun u => Real.cos (2*Real.pi*((2*(a+j):ℕ):ℝ)*u)) t)
            (0:ℝ) 1 MeasureTheory.volume :=
          Finset.sum_congr rfl (fun j _ => hV (2*(a+j)))
      _ = intervalIntegral (fun t => ∑ j ∈ Finset.range m,
            (B n).indicator (fun u => Real.cos (2*Real.pi*((2*(a+j):ℕ):ℝ)*u)) t)
            (0:ℝ) 1 MeasureTheory.volume :=
          (intervalIntegral.integral_finsetSum hii).symm
  have hfun : (fun t => ∑ j ∈ Finset.range m,
        (B n).indicator (fun u => Real.cos (2*Real.pi*((2*(a+j):ℕ):ℝ)*u)) t)
      = (B n).indicator (fun u => ∑ j ∈ Finset.range m,
        Real.cos (2*Real.pi*((2*(a+j):ℕ):ℝ)*u)) := by
    funext t
    by_cases ht : t ∈ B n
    · simp only [Set.indicator_of_mem ht]
    · simp only [Set.indicator_of_notMem ht]
      exact Finset.sum_const_zero
  have hpt : ∀ t : ℝ, ‖(B n).indicator (fun u => ∑ j ∈ Finset.range m,
        Real.cos (2*Real.pi*((2*(a+j):ℕ):ℝ)*u)) t‖
      ≤ (B n).indicator (fun t => if Real.sin (2*Real.pi*t) = 0 then (m:ℝ)
          else min (m:ℝ) (1/|Real.sin (2*Real.pi*t)|)) t := by
    intro t
    by_cases ht : t ∈ B n
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, Real.norm_eq_abs]
      exact cos_sum_bound_pi a m t
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
      exact norm_zero.le
  have henv : IntervalIntegrable ((B n).indicator
      (fun t => if Real.sin (2*Real.pi*t) = 0 then (m:ℝ)
        else min (m:ℝ) (1/|Real.sin (2*Real.pi*t)|))) MeasureTheory.volume (0:ℝ) 1 :=
    envelopeIntegrable (B n) hB m
  rw [hstep1, hfun]
  have hmain : ‖intervalIntegral ((B n).indicator (fun u => ∑ j ∈ Finset.range m,
        Real.cos (2*Real.pi*((2*(a+j):ℕ):ℝ)*u))) (0:ℝ) 1 MeasureTheory.volume‖
      ≤ intervalIntegral ((B n).indicator (fun t => if Real.sin (2*Real.pi*t) = 0 then (m:ℝ)
        else min (m:ℝ) (1/|Real.sin (2*Real.pi*t)|))) (0:ℝ) 1 MeasureTheory.volume :=
    intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Filter.Eventually.of_forall (fun t _ => hpt t)) henv
  simpa [Real.norm_eq_abs] using hmain
