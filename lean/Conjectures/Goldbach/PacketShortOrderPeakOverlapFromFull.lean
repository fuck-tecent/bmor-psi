import Mathlib

private theorem measurable_arcs (R n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ R ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a:ℝ)/(q:ℝ)| ≤ (R:ℝ)/((q:ℝ)*(n:ℝ))} := by
  have hset : {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ R ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a:ℝ)/(q:ℝ)| ≤ (R:ℝ)/((q:ℝ)*(n:ℝ))} =
      ⋃ q : ℕ, ⋃ a : ℕ, {t : ℝ | 1 ≤ q ∧ q ≤ R ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ (R:ℝ)/((q:ℝ)*(n:ℝ))} := by
    ext t
    simp [Set.mem_iUnion]
  rw [hset]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro a
  by_cases h : 1 ≤ q ∧ q ≤ R ∧ a ≤ q ∧ Nat.Coprime a q
  · obtain ⟨h1, h2, h3, h4⟩ := h
    have heq : {t : ℝ | 1 ≤ q ∧ q ≤ R ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ (R:ℝ)/((q:ℝ)*(n:ℝ))} =
        {t : ℝ | |t - (a:ℝ)/(q:ℝ)| ≤ (R:ℝ)/((q:ℝ)*(n:ℝ))} := by
      ext t
      exact ⟨fun ht => ht.2.2.2.2, fun ht => ⟨h1, h2, h3, h4, ht⟩⟩
    rw [heq]
    exact measurableSet_le
      (show Continuous (fun t : ℝ => |t - (a:ℝ)/(q:ℝ)|) by fun_prop).measurable measurable_const
  · have heq : {t : ℝ | 1 ≤ q ∧ q ≤ R ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a:ℝ)/(q:ℝ)| ≤ (R:ℝ)/((q:ℝ)*(n:ℝ))} = (∅ : Set ℝ) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, h3, h4, _⟩
      exact h ⟨h1, h2, h3, h4⟩
    rw [heq]
    exact MeasurableSet.empty

theorem Conjectures.Goldbach.PacketShortOrderPeakOverlapFromFull : (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, m (B n) (G n) ≤ ε*(n:ℝ)) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) ∩ W n (o n)) (G n) ≤ (n:ℝ)/4608) := by
  intro H
  intro Q arcs L K B W o G m
  obtain ⟨N, hN⟩ := H (1/4608) (by norm_num)
  refine ⟨N, fun n hn _ => ?_⟩
  have hG0 : ∀ t : ℝ, 0 ≤ G n t := by
    intro t
    show 0 ≤ ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter
      (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 *
      (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2))
    apply Finset.sum_nonneg
    intro q hq
    apply Finset.sum_nonneg
    intro a ha
    exact div_nonneg (by positivity) (by positivity)
  have hGc : Continuous (G n) := by
    show Continuous (fun t : ℝ => ∑ q ∈ Finset.Icc 1 ((Q n)^2),
      ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
      4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)))
    refine continuous_finsetSum _ (fun q hq => ?_)
    refine continuous_finsetSum _ (fun a ha => ?_)
    refine Continuous.div (f := fun _ : ℝ => 4*(n:ℝ)^2)
      (g := fun t : ℝ => (Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2))
      continuous_const ?_ ?_
    · exact continuous_const.mul (continuous_const.add
        ((continuous_const.mul (continuous_id.sub continuous_const)).pow 2))
    · intro t
      refine mul_ne_zero ?_ ?_
      · have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        have hpos : (0:ℕ) < Nat.totient q := Nat.totient_pos.mpr (by omega)
        exact pow_ne_zero 2 (by exact_mod_cast hpos.ne')
      · exact ne_of_gt (by positivity)
  have hB : MeasurableSet (B n) := by
    have hA : MeasurableSet (arcs n) := measurable_arcs (Q n) n
    have hKc : Continuous (K n) := by
      show Continuous (fun t : ℝ => (∑ j ∈ Finset.range (L n),
        Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ))
      have h1 : Continuous (fun t : ℝ => ∑ j ∈ Finset.range (L n),
          Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)) :=
        continuous_finsetSum _ fun j _ =>
          Real.continuous_cos.comp (continuous_const.mul continuous_id)
      have h2 : Continuous (fun t : ℝ => (∑ j ∈ Finset.range (L n),
          Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)) * ((L n:ℝ)⁻¹)) := h1.mul continuous_const
      simpa only [div_eq_mul_inv] using h2
    exact hA.compl.inter (measurableSet_lt (f := fun _ : ℝ => (1/2:ℝ)) (g := K n)
      measurable_const hKc.measurable)
  have hsub : (B n ∩ W n (fun _ => True)) ∩ W n (o n) ⊆ B n := fun _ ht => ht.1.1
  have hGi : MeasureTheory.IntegrableOn ((B n).indicator (G n)) (Set.Ioc (0:ℝ) 1)
      MeasureTheory.volume :=
    ((hGc.integrableOn_Icc (a := (0:ℝ)) (b := (1:ℝ))).mono_set
      Set.Ioc_subset_Icc_self).indicator hB
  have hmono : m ((B n ∩ W n (fun _ => True)) ∩ W n (o n)) (G n) ≤ m (B n) (G n) := by
    show intervalIntegral (((B n ∩ W n (fun _ => True)) ∩ W n (o n)).indicator (G n)) (0:ℝ) 1
        MeasureTheory.volume ≤ intervalIntegral ((B n).indicator (G n)) (0:ℝ) 1
        MeasureTheory.volume
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    exact MeasureTheory.setIntegral_mono_of_nonneg
      (fun x _ => Set.indicator_nonneg (fun t _ => hG0 t) x)
      (fun x _ => Set.indicator_le_indicator_of_subset hsub (fun t => hG0 t) x)
      hGi
  calc m ((B n ∩ W n (fun _ => True)) ∩ W n (o n)) (G n)
      ≤ m (B n) (G n) := hmono
    _ ≤ (1/4608) * (n:ℝ) := hN n hn
    _ = (n:ℝ)/4608 := by ring
