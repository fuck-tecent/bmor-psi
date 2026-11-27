import Mathlib

open MeasureTheory

private theorem pcMeasArcs (X : ℕ) (ρ n : ℝ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)} := by
  have h : {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)}
      = ⋃ q : ℕ, ⋃ a : ℕ, ({t : ℝ | 1≤q ∧ q≤X ∧ a≤q ∧ Nat.Coprime a q} ∩ {t : ℝ | |t-(a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)}) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
      exact ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
      exact ⟨q, a, h1, h2, h3, h4, h5⟩
  rw [h]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  refine (MeasurableSet.const _).inter ?_
  exact measurableSet_le (by fun_prop) (by fun_prop)

private theorem pcIntC {A : Set ℝ} {f : ℝ → ℂ} (hA : MeasurableSet A) (hf : Continuous f) :
    IntervalIntegrable (fun t => A.indicator f t) volume (0:ℝ) 1 := by
  have hi := hf.intervalIntegrable (μ := volume) (0:ℝ) 1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hi ⊢
  exact hi.indicator hA

private theorem pcIntR {A : Set ℝ} {f : ℝ → ℝ} (hA : MeasurableSet A) (hf : Continuous f) :
    IntervalIntegrable (fun t => A.indicator f t) volume (0:ℝ) 1 := by
  have hi := hf.intervalIntegrable (μ := volume) (0:ℝ) 1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hi ⊢
  exact hi.indicator hA

theorem Conjectures.Goldbach.PacketCapComparison :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let J := fun (n : ℕ) (v : ℝ → ℝ) => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => (v u:ℂ)*S n (high n) u*S n (high n) u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re; let B :=  fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; ∀ n : ℕ, J n (fun t => min (K n t) (1/2)) - U n (high n)/2 ≤ J n (K n) := by
  classical
  intro w E S Q arcs low high I L K J B U n
  have hEcont : Continuous E := by
    show Continuous (fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I))
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)
  have hScont : Continuous (S n (high n)) := by
    show Continuous (fun t : ℝ => Finset.sum (Finset.range (n+1))
      (fun k => ((high n) k : ℂ) * E ((k:ℝ)*t)))
    apply continuous_finsetSum
    intro k hk
    exact continuous_const.mul (hEcont.comp (by fun_prop))
  have harcs : MeasurableSet (arcs n) := pcMeasArcs (Q n) ((Q n : ℕ) : ℝ) (n : ℝ)
  have hLpos : (0:ℝ) < ((L n : ℕ) : ℝ) := by
    have h1 : (0:ℕ) < L n := by
      show (0:ℕ) < max 1 (Nat.log 2 n / 2)
      exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
    exact Nat.cast_pos.mpr h1
  have hKnum : Continuous (fun t : ℝ =>
      ∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)) := by
    apply continuous_finsetSum
    intro j hj
    exact Real.continuous_cos.comp (by fun_prop)
  have hKcont : Continuous (K n) := by
    show Continuous (fun t : ℝ =>
      (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/((L n : ℕ):ℝ))
    exact hKnum.div continuous_const (fun t => hLpos.ne')
  have hKle (t : ℝ) : K n t ≤ 1 := by
    show (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/((L n : ℕ):ℝ) ≤ 1
    rw [div_le_iff₀ hLpos]
    calc ∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)
        ≤ ∑ _j ∈ Finset.range (L n), (1:ℝ) :=
          Finset.sum_le_sum fun j _ => Real.cos_le_one _
      _ = 1 * ((L n : ℕ):ℝ) := by simp
  have hBmeas : MeasurableSet (B n) := by
    have h1 : MeasurableSet {t : ℝ | (1:ℝ)/2 < K n t} :=
      measurableSet_lt measurable_const hKcont.measurable
    have h2 : B n = (arcs n)ᶜ ∩ {t : ℝ | (1:ℝ)/2 < K n t} := by
      ext t
      show (t ∉ arcs n ∧ (1:ℝ)/2 < K n t) ↔ (t ∈ (arcs n)ᶜ ∧ t ∈ {t : ℝ | (1:ℝ)/2 < K n t})
      exact Iff.rfl
    rw [h2]
    exact harcs.compl.inter h1
  have hBmem {t : ℝ} (h1 : t ∈ (arcs n)ᶜ) (h2 : (1:ℝ)/2 < K n t) : t ∈ B n := ⟨h1, h2⟩
  let F : (ℝ → ℝ) → ℝ → ℂ := fun v t => (arcs n)ᶜ.indicator
    (fun u => (v u : ℂ) * S n (high n) u * S n (high n) u * E (-(n:ℝ) * u)) t
  let cap : ℝ → ℝ := fun t => min (K n t) (1/2)
  let d : ℝ → ℝ := fun t => K n t - cap t
  let G : ℝ → ℝ := (B n).indicator (fun u => (1/2) * ‖S n (high n) u‖^2)
  have hFdef (v : ℝ → ℝ) (t : ℝ) : F v t = (arcs n)ᶜ.indicator
      (fun u => (v u : ℂ) * S n (high n) u * S n (high n) u * E (-(n:ℝ) * u)) t := rfl
  have hJF (v : ℝ → ℝ) : J n v = (intervalIntegral (F v) (0:ℝ) 1 volume).re := rfl
  have hUdef : U n (high n) =
      intervalIntegral ((B n).indicator (fun t => ‖S n (high n) t‖^2)) (0:ℝ) 1 volume := rfl
  have hinner (v : ℝ → ℝ) (hv : Continuous v) :
      Continuous (fun t => (v t : ℂ) * S n (high n) t * S n (high n) t * E (-(n:ℝ)*t)) :=
    (((Complex.continuous_ofReal.comp hv).mul hScont).mul hScont).mul
      (hEcont.comp (continuous_const.mul continuous_id))
  have hcapcont : Continuous cap := by
    show Continuous (fun t => min (K n t) (1/2))
    exact hKcont.min continuous_const
  have hdcont : Continuous d := by
    show Continuous (fun t => K n t - min (K n t) (1/2))
    exact hKcont.sub hcapcont
  have hdnn (t : ℝ) : 0 ≤ d t := by
    show 0 ≤ K n t - min (K n t) (1/2)
    exact sub_nonneg.mpr (min_le_left _ _)
  have hdle (t : ℝ) : d t ≤ 1/2 := by
    show K n t - min (K n t) (1/2) ≤ 1/2
    by_cases h : K n t ≤ 1/2
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right (le_of_not_ge h)]; linarith [hKle t]
  have hdzero {t : ℝ} (h : K n t ≤ 1/2) : d t = 0 := by
    show K n t - min (K n t) (1/2) = 0
    rw [min_eq_left h]; ring
  have hFint (v : ℝ → ℝ) (hv : Continuous v) : IntervalIntegrable (F v) volume (0:ℝ) 1 :=
    pcIntC harcs.compl (hinner v hv)
  have hFKint : IntervalIntegrable (F (K n)) volume (0:ℝ) 1 := hFint (K n) hKcont
  have hFmInt : IntervalIntegrable (F cap) volume (0:ℝ) 1 := hFint cap hcapcont
  have hFdInt : IntervalIntegrable (F d) volume (0:ℝ) 1 := hFint d hdcont
  have hGint : IntervalIntegrable G volume (0:ℝ) 1 :=
    pcIntR hBmeas (continuous_const.mul (hScont.norm.pow 2))
  have hEnorm (t : ℝ) : ‖E (-(n:ℝ)*t)‖ = 1 := by
    show ‖Complex.exp (((2*Real.pi*(-(n:ℝ)*t):ℝ):ℂ)*Complex.I)‖ = 1
    exact Complex.norm_exp_ofReal_mul_I _
  have hdiff (t : ℝ) : F (K n) t - F cap t = F d t := by
    simp only [hFdef]
    by_cases h : t ∈ (arcs n)ᶜ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Set.indicator_of_mem h]
      have hd' : (d t : ℂ) = (K n t : ℂ) - (cap t : ℂ) := by
        show ((K n t - cap t : ℝ) : ℂ) = (K n t : ℂ) - (cap t : ℂ)
        push_cast; ring
      rw [hd']; ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      simp
  have hsub : intervalIntegral (F (K n)) (0:ℝ) 1 volume - intervalIntegral (F cap) (0:ℝ) 1 volume
      = intervalIntegral (F d) (0:ℝ) 1 volume := by
    rw [← intervalIntegral.integral_sub hFKint hFmInt]
    apply intervalIntegral.integral_congr
    intro t ht
    exact hdiff t
  have hJsub : J n (K n) - J n cap = (intervalIntegral (F d) (0:ℝ) 1 volume).re := by
    have h := congrArg Complex.re hsub
    rw [Complex.sub_re] at h
    simpa only [hJF] using h
  have hG (t : ℝ) : ‖F d t‖ ≤ G t := by
    show ‖F d t‖ ≤ (B n).indicator (fun u => (1/2) * ‖S n (high n) u‖^2) t
    by_cases hB : t ∈ B n
    · have h1 : t ∈ (arcs n)ᶜ := hB.1
      rw [hFdef, Set.indicator_of_mem h1, Set.indicator_of_mem hB]
      have hnorm : ‖(d t : ℂ) * S n (high n) t * S n (high n) t * E (-(n:ℝ)*t)‖
          = |d t| * ‖S n (high n) t‖^2 := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hEnorm]
        ring
      rw [hnorm, abs_of_nonneg (hdnn t)]
      exact mul_le_mul_of_nonneg_right (hdle t) (sq_nonneg _)
    · by_cases h1 : t ∈ (arcs n)ᶜ
      · have h2 : K n t ≤ 1/2 := by
          by_contra hc
          exact hB (hBmem h1 (lt_of_not_ge hc))
        have hz : d t = 0 := hdzero h2
        rw [hFdef, Set.indicator_of_mem h1, Set.indicator_of_notMem hB, hz]
        simp
      · rw [hFdef, Set.indicator_of_notMem h1, Set.indicator_of_notMem hB]
        simp
  have hGval : intervalIntegral G (0:ℝ) 1 volume = U n (high n) / 2 := by
    have h1 : intervalIntegral G (0:ℝ) 1 volume
        = (1/2) * intervalIntegral ((B n).indicator (fun u => ‖S n (high n) u‖^2)) (0:ℝ) 1 volume := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      show (B n).indicator (fun u => (1/2) * ‖S n (high n) u‖^2) t
          = (1/2) * (B n).indicator (fun u => ‖S n (high n) u‖^2) t
      by_cases hB : t ∈ B n
      · rw [Set.indicator_of_mem hB, Set.indicator_of_mem hB]
      · rw [Set.indicator_of_notMem hB, Set.indicator_of_notMem hB]; ring
    rw [h1, hUdef]
    ring
  have hnormint : ‖intervalIntegral (F d) (0:ℝ) 1 volume‖ ≤ intervalIntegral G (0:ℝ) 1 volume := by
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    · exact Filter.Eventually.of_forall (fun t _ => hG t)
    · exact hGint
  have hre : -(U n (high n)/2) ≤ (intervalIntegral (F d) (0:ℝ) 1 volume).re := by
    have h1 : -‖intervalIntegral (F d) (0:ℝ) 1 volume‖ ≤ (intervalIntegral (F d) (0:ℝ) 1 volume).re := by
      have h2 := Complex.re_le_norm (-(intervalIntegral (F d) (0:ℝ) 1 volume))
      rw [Complex.neg_re, norm_neg] at h2
      linarith
    rw [hGval] at hnormint
    linarith
  show J n cap - U n (high n) / 2 ≤ J n (K n)
  linarith [hJsub, hre]
