import Mathlib

open MeasureTheory

noncomputable section

private def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private theorem phase_continuous : Continuous phase := by
  unfold phase
  fun_prop

private theorem phase_half (x : ℝ) : phase (x / 2) ^ 2 = phase x := by
  unfold phase
  rw [pow_two, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private def maskedIntegral {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (M : Set ℝ) (f : ℝ → G) : G :=
  intervalIntegral (M.indicator f) 0 1 volume

/-- Removing half the phase expresses the signed square using total and imaginary energy. -/
private theorem masked_square_re (M : Set ℝ) (hM : MeasurableSet M)
    (s : ℝ → ℂ) (θ : ℝ → ℝ) (hs : Continuous s) (hθ : Continuous θ) :
    let z := fun t => s t * phase (θ t / 2)
    (maskedIntegral M (fun t => s t ^ 2 * phase (θ t))).re =
      maskedIntegral M (fun t => ‖s t‖ ^ 2) -
      2 * maskedIntegral M (fun t => (z t).im ^ 2) := by
  let z := fun t => s t * phase (θ t / 2)
  let μ := (volume : Measure ℝ).restrict (Set.Ioc 0 1)
  have hz : Continuous z := hs.mul (phase_continuous.comp (hθ.div_const _))
  have hF : Continuous (fun t => s t ^ 2 * phase (θ t)) :=
    (hs.pow 2).mul (phase_continuous.comp hθ)
  have hre : Continuous (fun t => ‖s t‖ ^ 2) := hs.norm.pow 2
  have him : Continuous (fun t => (z t).im ^ 2) := (Complex.continuous_im.comp hz).pow 2
  have hintF : Integrable (M.indicator (fun t => s t ^ 2 * phase (θ t))) μ :=
    ((hF.intervalIntegrable 0 1).1).indicator hM
  have hintRe : Integrable (M.indicator (fun t => ‖s t‖ ^ 2)) μ :=
    ((hre.intervalIntegrable 0 1).1).indicator hM
  have hintIm : Integrable (M.indicator (fun t => (z t).im ^ 2)) μ :=
    ((him.intervalIntegrable 0 1).1).indicator hM
  dsimp only
  simp only [maskedIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change (∫ t, M.indicator (fun t => s t ^ 2 * phase (θ t)) t ∂μ).re =
    (∫ t, M.indicator (fun t => ‖s t‖ ^ 2) t ∂μ) -
    2 * (∫ t, M.indicator (fun t => (z t).im ^ 2) t ∂μ)
  have hReal : (∫ t, (M.indicator (fun t => s t ^ 2 * phase (θ t)) t).re ∂μ) =
      (∫ t, M.indicator (fun t => s t ^ 2 * phase (θ t)) t ∂μ).re := integral_re hintF
  rw [← hReal, ← integral_const_mul, ← integral_sub hintRe (hintIm.const_mul 2)]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ M
  · simp only [Set.indicator_of_mem ht]
    rw [← phase_half (θ t), ← mul_pow]
    have hnorm : ‖z t‖ = ‖s t‖ := by
      dsimp [z, phase]
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    change ((z t) ^ 2).re = ‖s t‖ ^ 2 - 2 * (z t).im ^ 2
    rw [← hnorm, Complex.sq_norm, Complex.normSq_apply, pow_two, Complex.mul_re]
    ring
  · simp [Set.indicator_of_notMem ht]

private def cutoff (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

private def arcs (n : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}

private theorem arcs_measurable (n : ℕ) : MeasurableSet (arcs n) := by
  classical
  let arc (q a : ℕ) : Set ℝ :=
    if 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q then
      {t | |t - (a : ℝ) / (q : ℝ)| ≤ (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}
    else ∅
  have hEq : arcs n = ⋃ q : ℕ, ⋃ a : ℕ, arc q a := by
    ext t
    simp only [arcs, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q, a, hq, hQ, ha, hcop, hdist⟩
      refine ⟨q, a, ?_⟩
      unfold arc
      rw [ite_eq_left (show 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q from
        ⟨hq, hQ, ha, hcop⟩)]
      exact hdist
    · rintro ⟨q, a, ht⟩
      by_cases h : 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ Nat.Coprime a q
      · refine ⟨q, a, h.1, h.2.1, h.2.2.1, h.2.2.2, ?_⟩
        unfold arc at ht
        rw [ite_eq_left h] at ht
        exact ht
      · unfold arc at ht
        rw [ite_eq_right h] at ht
        exact (Set.notMem_empty t ht).elim
  rw [hEq]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  unfold arc
  split
  · exact (isClosed_le ((continuous_id.sub continuous_const).abs) continuous_const).measurableSet
  · exact MeasurableSet.empty

theorem Conjectures.Goldbach.MinorSineEnergyIff :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t));
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
    let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
    let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t);
    let minor := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume;
    let A := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun x => ‖S n w x‖^2) t) (0:ℝ) 1 MeasureTheory.volume;
    let B := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun x => ((S n w x)*E (-(n:ℝ)*x/2)).im^2) t) (0:ℝ) 1 MeasureTheory.volume; (∀ e : ℝ, 0<e → ∃ N : ℕ, ∀ n : ℕ, N≤n → Even n → -(e*(n:ℝ)) ≤ (minor n).re) ↔ (∀ e : ℝ, 0<e → ∃ N : ℕ, ∀ n : ℕ, N≤n → Even n → 2*B n ≤ A n+e*(n:ℝ)) := by
  intro w E S Q arcs f minor A B
  have hidentity (n : ℕ) : (minor n).re = A n - 2 * B n := by
    have hm : MeasurableSet (arcs n) := arcs_measurable n
    have hs : Continuous (S n w) := by
      dsimp [S, E]
      fun_prop
    exact masked_square_re (arcs n)ᶜ hm.compl (S n w) (fun t => -(n : ℝ) * t)
      hs (continuous_const.mul continuous_id)
  constructor
  · intro h e he
    obtain ⟨N, hN⟩ := h e he
    refine ⟨N, fun n hn hEven => ?_⟩
    linarith only [hidentity n, hN n hn hEven]
  · intro h e he
    obtain ⟨N, hN⟩ := h e he
    refine ⟨N, fun n hn hEven => ?_⟩
    linarith only [hidentity n, hN n hn hEven]

end
