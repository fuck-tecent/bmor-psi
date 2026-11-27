import Mathlib

open MeasureTheory Set

private theorem shell_arcs_measurable (n D R : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧
      Nat.Coprime a q ∧ |t - (a : ℝ) / q| ≤ (R : ℝ) / ((q : ℝ) * n)} := by
  classical
  let arc (q a : ℕ) : Set ℝ :=
    if 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q then
      {t | |t - (a : ℝ) / q| ≤ (R : ℝ) / ((q : ℝ) * n)}
    else ∅
  have heq : {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧
      Nat.Coprime a q ∧ |t - (a : ℝ) / q| ≤ (R : ℝ) / ((q : ℝ) * n)} =
      ⋃ q : ℕ, ⋃ a : ℕ, arc q a := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q, a, hq, hD, ha, hc, hd⟩
      refine ⟨q, a, ?_⟩
      unfold arc
      rw [ite_eq_left (show 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q from
        ⟨hq, hD, ha, hc⟩)]
      exact hd
    · rintro ⟨q, a, ht⟩
      by_cases h : 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q
      · refine ⟨q, a, h.1, h.2.1, h.2.2.1, h.2.2.2, ?_⟩
        unfold arc at ht
        rw [ite_eq_left h] at ht
        exact ht
      · unfold arc at ht
        rw [ite_eq_right h] at ht
        exact (Set.notMem_empty t ht).elim
  rw [heq]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  unfold arc
  split
  · exact (isClosed_le ((continuous_id.sub continuous_const).abs) continuous_const).measurableSet
  · exact MeasurableSet.empty

theorem PEqualNP.Outside.L_goldbach_sqrt_band_old_new_shells :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
    let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t));
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
    let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t);
    let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊;
    let H := fun n : ℕ => 256 * Q₁ n * Q n;
    let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))};
    let Q₂ := fun n : ℕ => ⌊Real.sqrt (n : ℝ) / ((Nat.log 2 (n + 2) : ℝ) ^ 4)⌋₊;
    let sqrtArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q₂ n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ ((256 * Q₂ n * Q n : ℕ) : ℝ) / ((q : ℝ) * (n : ℝ))}; ∀ n : ℕ, 0 < n → Q₁ n ≤ Q₂ n → let old := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/q| ≤ ((256*Q₂ n*Q n:ℕ):ℝ)/((q:ℝ)*n)};
    let J := fun A : Set ℝ => intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; J ((wideArcs n)ᶜ) = J (old \ wideArcs n) + J (sqrtArcs n \ old) + J ((sqrtArcs n)ᶜ) := by
  intro w E S Q f Q₁ H wideArcs Q₂ sqrtArcs n _ hle old J
  have hWO : wideArcs n ⊆ old := by
    intro t ht
    obtain ⟨q, a, hq, hD, ha, hc, hd⟩ := ht
    refine ⟨q, a, hq, hD, ha, hc, hd.trans ?_⟩
    have hnum : H n ≤ 256 * Q₂ n * Q n := by
      change 256 * Q₁ n * Q n ≤ _
      gcongr
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnum) (by positivity)
  have hOU : old ⊆ sqrtArcs n := by
    intro t ht
    obtain ⟨q, a, hq, hD, ha, hc, hd⟩ := ht
    exact ⟨q, a, hq, hD.trans hle, ha, hc, hd⟩
  have hmW : MeasurableSet (wideArcs n) := shell_arcs_measurable n (Q₁ n) (H n)
  have hmO : MeasurableSet old := shell_arcs_measurable n (Q₁ n) (256 * Q₂ n * Q n)
  have hmU : MeasurableSet (sqrtArcs n) := shell_arcs_measurable n (Q₂ n) (256 * Q₂ n * Q n)
  have hf : Continuous (f n) := by
    dsimp [f, S, E]
    fun_prop
  have hfI := hf.intervalIntegrable (μ := volume) 0 1
  have hint (A : Set ℝ) (hA : MeasurableSet A) :
      IntervalIntegrable (A.indicator (f n)) volume 0 1 :=
    ⟨hfI.1.indicator hA, hfI.2.indicator hA⟩
  let A := (old \ wideArcs n).indicator (f n)
  let B := (sqrtArcs n \ old).indicator (f n)
  let C := ((sqrtArcs n)ᶜ).indicator (f n)
  have hA : IntervalIntegrable A volume 0 1 := hint _ (hmO.diff hmW)
  have hB : IntervalIntegrable B volume 0 1 := hint _ (hmU.diff hmO)
  have hC : IntervalIntegrable C volume 0 1 := hint _ hmU.compl
  have hsplit : ((wideArcs n)ᶜ).indicator (f n) = fun t => (A t + B t) + C t := by
    funext t
    by_cases hW : t ∈ wideArcs n
    · have hO := hWO hW
      have hU := hOU hO
      simp [A, B, C, Set.indicator, hW, hO, hU]
    · by_cases hO : t ∈ old
      · have hU := hOU hO
        simp [A, B, C, Set.indicator, hW, hO, hU]
      · by_cases hU : t ∈ sqrtArcs n <;>
          simp [A, B, C, Set.indicator, hW, hO, hU]
  change (∫ t in (0 : ℝ)..1, ((wideArcs n)ᶜ).indicator (f n) t) =
    (∫ t in (0 : ℝ)..1, A t) + (∫ t in (0 : ℝ)..1, B t) + (∫ t in (0 : ℝ)..1, C t)
  rw [hsplit, intervalIntegral.integral_add (hA.add hB) hC, intervalIntegral.integral_add hA hB]
