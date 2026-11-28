import Mathlib
import Conjectures.Goldbach.PacketMaskLogDecay
import Conjectures.Goldbach.PacketShortLagEnvelope

/-! We use the zero-log-power instance of mask decay and the comparison
of integrals over a measurable mask from PacketShortLagEnvelope. -/

theorem Conjectures.Cuts.Task05a24032f4d0a2aeab14a66c :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
      let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
      let L := fun n : ℕ => max 1 (Nat.log 2 n / 2);
      let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ);
      let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t};
      let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume;
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
        (∑ h ∈ Finset.Icc ((L n)^2+1) n, |V n h|) ≤ ε * (n:ℝ) := by
  intro Q arcs L K B V ε hε
  obtain ⟨N,hN⟩ := Conjectures.Goldbach.PacketMaskLogDecay 0 ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have mass : intervalIntegral ((B n).indicator (fun _ => (1:ℝ))) (0:ℝ) 1 MeasureTheory.volume ≤ ε := by
    simpa only [pow_zero, one_mul] using hN n hn
  have hK : Continuous (K n) := by
    exact (continuous_finsetSum _ fun j _ =>
      Real.continuous_cos.comp (continuous_const.mul continuous_id)).div_const _
  have hArcs : MeasurableSet (arcs n) := by
    simp only [arcs, Set.ofPred_exists, Set.ofPred_and]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
    iterate 4 refine MeasurableSet.inter (MeasurableSet.const _) ?_
    exact measurableSet_le ((continuous_abs.comp (continuous_id.sub continuous_const)).measurable) measurable_const
  have hB : MeasurableSet (B n) := by
    simp only [B, Set.ofPred_and]
    exact hArcs.compl.inter (measurableSet_lt measurable_const hK.measurable)
  have coeff (h : ℕ) : |V n h| ≤ ε := by
    apply le_trans _ mass
    apply Conjectures.Goldbach.PacketShortLagEnvelope_aux.mask_le_mask hB
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)) continuous_const
    intro t
    exact abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  let D := Finset.Icc ((L n)^2+1) n
  have card : D.card ≤ n := by
    dsimp only [D]
    rw [Nat.card_Icc]
    omega
  calc
    _ ≤ ∑ _h ∈ D, ε := Finset.sum_le_sum (fun h _ => coeff h)
    _ = ε * (D.card:ℝ) := by simp [mul_comm]
    _ ≤ ε * (n:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast card) hε.le
