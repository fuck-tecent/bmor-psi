import Mathlib

open MeasureTheory

namespace Conjectures.Goldbach.PacketRemainingPeakOverlapFromFull_aux

/-- Monotonicity of the interval integral of a set indicator in the set, for a nonnegative
integrand. Only the larger set needs to be measurable. -/
lemma intervalIntegral_indicator_mono {s t : Set ℝ} {f : ℝ → ℝ} (hsub : s ⊆ t)
    (hmt : MeasurableSet t) (hcont : Continuous f) (hnonneg : ∀ x, 0 ≤ f x) :
    intervalIntegral (s.indicator f) (0:ℝ) 1 volume ≤
      intervalIntegral (t.indicator f) (0:ℝ) 1 volume := by
  have hInt : IntegrableOn f (Set.Icc (0:ℝ) 1) (volume : Measure ℝ) := hcont.integrableOn_Icc
  have hbig : IntegrableOn (t.indicator f) (Set.Ioc (0:ℝ) 1) (volume : Measure ℝ) :=
    (hInt.mono_set Set.Ioc_subset_Icc_self).indicator hmt
  have hle : ∀ x, s.indicator f x ≤ t.indicator f x := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hsub hx)]
    · rw [Set.indicator_of_notMem hx]
      by_cases hy : x ∈ t
      · rw [Set.indicator_of_mem hy]
        exact hnonneg x
      · rw [Set.indicator_of_notMem hy]
  have hnn : ∀ x, 0 ≤ t.indicator f x := by
    intro x
    by_cases hx : x ∈ t
    · rw [Set.indicator_of_mem hx]
      exact hnonneg x
    · rw [Set.indicator_of_notMem hx]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  by_cases hint : IntegrableOn (s.indicator f) (Set.Ioc (0:ℝ) 1) (volume : Measure ℝ)
  · exact setIntegral_mono_ae hint hbig (Filter.Eventually.of_forall hle)
  · have hzero : (∫ x in Set.Ioc (0:ℝ) 1, s.indicator f x ∂volume) = 0 :=
      MeasureTheory.integral_undef
        (show ¬ Integrable (s.indicator f) (volume.restrict (Set.Ioc (0:ℝ) 1)) from hint)
    rw [hzero]
    exact MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall hnn)

/-- Positivity of the totient factor for `q ≥ 1`. -/
lemma totient_cast_pos {q : ℕ} (hq : 1 ≤ q) : (0:ℝ) < (Nat.totient q : ℝ) := by
  have h : 0 < Nat.totient q := Nat.totient_pos.mpr (Nat.lt_of_lt_of_le (by omega) hq)
  exact_mod_cast h

/-- Every summand of the model integrand is nonnegative. -/
lemma model_summand_nonneg (n q a : ℕ) (hq : 1 ≤ q) (t : ℝ) :
    0 ≤ 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)) := by
  have hφ : (0:ℝ) < (Nat.totient q : ℝ) := totient_cast_pos hq
  have hden : (0:ℝ) < (Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2) := by positivity
  exact div_nonneg (by positivity) (le_of_lt hden)

/-- The model integrand is nonnegative. -/
lemma model_nonneg (n X : ℕ) (t : ℝ) :
    0 ≤ ∑ q ∈ Finset.Icc 1 X, ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)) := by
  refine Finset.sum_nonneg fun q hq => ?_
  refine Finset.sum_nonneg fun a _ => ?_
  exact model_summand_nonneg n q a (Finset.mem_Icc.mp hq).1 t

/-- The model integrand is continuous. -/
lemma model_continuous (n X : ℕ) :
    Continuous (fun t : ℝ => ∑ q ∈ Finset.Icc 1 X,
      ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2))) := by
  refine continuous_finsetSum _ fun q hq => ?_
  refine continuous_finsetSum _ fun a _ => ?_
  have hφ : (0:ℝ) < (Nat.totient q : ℝ) := totient_cast_pos (Finset.mem_Icc.mp hq).1
  have hden : ∀ t : ℝ, ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)) ≠ 0 := by
    intro t
    have hpos : (0:ℝ) < (Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2) := by positivity
    linarith
  refine continuous_const.div ?_ hden
  exact continuous_const.mul (continuous_const.add
    ((continuous_const.mul (continuous_id.sub continuous_const)).pow 2))

/-- A closed interval is a measurable set. -/
lemma measurableSet_abs_le (c r : ℝ) :
    MeasurableSet {t : ℝ | |t - c| ≤ r} :=
  (isClosed_le ((continuous_id.sub continuous_const).abs) continuous_const).measurableSet

end Conjectures.Goldbach.PacketRemainingPeakOverlapFromFull_aux

open Conjectures.Goldbach.PacketRemainingPeakOverlapFromFull_aux

theorem Conjectures.Goldbach.PacketRemainingPeakOverlapFromFull :
(let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, m (B n) (G n) ≤ ε*(n:ℝ)) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) \ W n (o n)) (G n) ≤ (n:ℝ)/4608) := by
  intro h
  dsimp only at h
  obtain ⟨N, hN⟩ := h (1/4608) (by norm_num)
  intro Q arcs L K B W o G m
  refine ⟨N, fun n hn _ => ?_⟩
  have hsub : (B n ∩ W n (fun _ => True)) \ W n (o n) ⊆ B n := fun _ ht => ht.1.1
  have hnonneg : ∀ t, 0 ≤ G n t := by
    intro t
    show 0 ≤ ∑ q ∈ Finset.Icc 1 ((Q n)^2),
      ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2))
    exact model_nonneg n ((Q n)^2) t
  have hcont : Continuous (G n) := by
    show Continuous (fun t : ℝ => ∑ q ∈ Finset.Icc 1 ((Q n)^2),
      ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)))
    exact model_continuous n ((Q n)^2)
  have hK : Continuous (K n) := by
    show Continuous (fun t : ℝ =>
      (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ))
    have hnum : Continuous (fun t : ℝ =>
        ∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)) := by
      refine continuous_finsetSum _ fun j _ => ?_
      exact Real.continuous_cos.comp (continuous_const.mul continuous_id)
    have hL : (0:ℝ) < (L n : ℝ) := by
      have h1 : (1:ℕ) ≤ L n := le_max_left _ _
      have h2 : (1:ℝ) ≤ (L n : ℝ) := by exact_mod_cast h1
      linarith
    exact hnum.div continuous_const (fun _ => hL.ne')
  have hA : MeasurableSet (arcs n) := by
    have hset : arcs n = ⋃ q : ℕ, ⋃ a : ℕ,
        {t : ℝ | 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧
          |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))} := by
      ext t
      simp only [arcs, Set.mem_iUnion, Set.mem_setOf_eq]
    rw [hset]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
    by_cases hcond : 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q
    · have hset2 : {t : ℝ | 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧
          |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}
          = {t : ℝ | |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))} := by
        apply Set.ext
        intro t
        constructor
        · intro ht
          exact ht.2.2.2.2
        · intro ht
          exact ⟨hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2, ht⟩
      rw [hset2]
      exact measurableSet_abs_le _ _
    · have hset2 : {t : ℝ | 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧
          |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))} = ∅ := by
        apply Set.Subset.antisymm
        · intro t ht
          exact False.elim (hcond ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩)
        · exact Set.empty_subset _
      rw [hset2]
      exact MeasurableSet.empty
  have hB : MeasurableSet (B n) := by
    have h2 : MeasurableSet {t : ℝ | (1:ℝ)/2 < K n t} :=
      measurableSet_lt measurable_const hK.measurable
    have h3 : MeasurableSet ((arcs n)ᶜ ∩ {t : ℝ | (1:ℝ)/2 < K n t}) := hA.compl.inter h2
    rw [show B n = (arcs n)ᶜ ∩ {t : ℝ | (1:ℝ)/2 < K n t} by
      apply Set.ext
      intro t
      show (t ∉ arcs n ∧ (1:ℝ)/2 < K n t) ↔
        (t ∈ (arcs n)ᶜ ∧ t ∈ {t : ℝ | (1:ℝ)/2 < K n t})
      constructor
      · intro h
        exact ⟨h.1, h.2⟩
      · intro h
        exact ⟨h.1, h.2⟩]
    exact h3
  have hN' : m (B n) (G n) ≤ (1/4608) * (n:ℝ) := hN n hn
  calc m ((B n ∩ W n (fun _ => True)) \ W n (o n)) (G n)
      ≤ m (B n) (G n) := intervalIntegral_indicator_mono hsub hB hcont hnonneg
    _ ≤ (1/4608) * (n:ℝ) := hN'
    _ = (n:ℝ)/4608 := by ring
