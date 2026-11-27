import Mathlib

namespace Conjectures.Goldbach.PacketShortLagEnvelope_aux

theorem mask_le_mask {s : Set ℝ} (hs : MeasurableSet s) {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) (hle : ∀ t, |φ t| ≤ ψ t) :
    |∫ t in (0:ℝ)..1, s.indicator φ t| ≤ ∫ t in (0:ℝ)..1, s.indicator ψ t := by
  have hφi : IntervalIntegrable (s.indicator (fun t => |φ t|)) MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    exact ((continuous_abs.comp hφ).integrableOn_Icc).indicator hs
  have hψi : IntervalIntegrable (s.indicator ψ) MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    exact (hψ.integrableOn_Icc).indicator hs
  calc |∫ t in (0:ℝ)..1, s.indicator φ t|
      ≤ ∫ t in (0:ℝ)..1, |s.indicator φ t| :=
        intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ = ∫ t in (0:ℝ)..1, s.indicator (fun t => |φ t|) t := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        by_cases ht : t ∈ s
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
        · simp [Set.indicator, ht]
    _ ≤ ∫ t in (0:ℝ)..1, s.indicator ψ t := by
        refine intervalIntegral.integral_mono_on zero_le_one hφi hψi fun t _ => ?_
        by_cases ht : t ∈ s
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
          exact hle t
        · simp [Set.indicator, ht]

end Conjectures.Goldbach.PacketShortLagEnvelope_aux

theorem Conjectures.Goldbach.PacketShortLagEnvelope :
let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∀ (n : ℕ) (a : ℕ → ℝ) (M : ℝ), 0 ≤ M → (∀ k ≤ n, |a k| ≤ M) → |short n a| ≤ (1+2*((L n:ℝ)^2))*((n:ℝ)+1)*M^2*V n 0
:= by
  intro w E S Q arcs low high I L K B U V A model short long n a M hM ha
  have htwo : (0:ℝ) ≤ 2 := by norm_num
  have hK : Continuous (K n) := by
    simp only [K]
    exact (continuous_finsetSum _ fun j _ =>
      Real.continuous_cos.comp (continuous_const.mul continuous_id)).div_const _
  have harcs : MeasurableSet (arcs n) := by
    simp only [arcs, Set.ofPred_exists, Set.ofPred_and]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
    refine MeasurableSet.inter (MeasurableSet.const _) ?_
    refine MeasurableSet.inter (MeasurableSet.const _) ?_
    refine MeasurableSet.inter (MeasurableSet.const _) ?_
    refine MeasurableSet.inter (MeasurableSet.const _) ?_
    exact measurableSet_le
      ((continuous_abs.comp (continuous_id.sub continuous_const)).measurable) measurable_const
  have hBmeas : MeasurableSet (B n) := by
    simp only [B, Set.ofPred_and]
    refine MeasurableSet.inter ?_ ?_
    · exact harcs.compl
    · exact measurableSet_lt measurable_const hK.measurable
  have hV0 : 0 ≤ V n 0 := by
    simp only [V]
    refine intervalIntegral.integral_nonneg_of_forall zero_le_one fun t => ?_
    by_cases ht : t ∈ B n
    · rw [Set.indicator_of_mem ht]
      have hz : Real.cos (2 * Real.pi * ((0:ℕ):ℝ) * t) = 1 := by simp
      rw [hz]
      exact zero_le_one
    · simp [Set.indicator, ht]
  have hVh : ∀ h : ℕ, |V n h| ≤ V n 0 := by
    intro h
    simp only [V]
    refine Conjectures.Goldbach.PacketShortLagEnvelope_aux.mask_le_mask hBmeas
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)) ?_
    intro t
    have hz : Real.cos (2 * Real.pi * ((0:ℕ):ℝ) * t) = 1 := by simp
    rw [hz]
    exact Real.abs_cos_le_one _
  have hA : ∀ h : ℕ, |A n h a| ≤ ((n:ℝ)+1) * M^2 := by
    intro h
    simp only [A]
    have hc : ((n + 1 - h : ℕ) : ℝ) ≤ (n:ℝ) + 1 := by
      have h1 : n + 1 - h ≤ n + 1 := Nat.sub_le (n + 1) h
      calc ((n + 1 - h : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (n:ℝ) + 1 := by push_cast; ring
    calc |∑ k ∈ Finset.range (n + 1 - h), a k * a (k + h)|
        ≤ ∑ k ∈ Finset.range (n + 1 - h), |a k * a (k + h)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ Finset.range (n + 1 - h), |a k| * |a (k + h)| := by simp only [abs_mul]
      _ ≤ ∑ k ∈ Finset.range (n + 1 - h), M * M := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k < n + 1 - h := Finset.mem_range.1 hk
          have hb1 : k ≤ n := by omega
          have hb2 : k + h ≤ n := by omega
          calc |a k| * |a (k + h)| ≤ M * |a (k + h)| :=
                  mul_le_mul_of_nonneg_right (ha k hb1) (abs_nonneg _)
            _ ≤ M * M := mul_le_mul_of_nonneg_left (ha (k + h) hb2) hM
      _ = ((n + 1 - h : ℕ) : ℝ) * (M * M) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ((n + 1 - h : ℕ) : ℝ) * M ^ 2 := by ring
      _ ≤ ((n:ℝ) + 1) * M ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg M)
  have hcard : ((Finset.Icc 1 (min n ((L n)^2))).card : ℝ) ≤ ((L n:ℝ)^2) := by
    have h1 : (Finset.Icc 1 (min n ((L n)^2))).card = min n ((L n)^2) := by
      rw [Nat.card_Icc]
      omega
    have h2 : ((min n ((L n)^2) : ℕ) : ℝ) ≤ (((L n)^2 : ℕ) : ℝ) := by
      exact_mod_cast min_le_right n ((L n)^2)
    calc ((Finset.Icc 1 (min n ((L n)^2))).card : ℝ)
        = ((min n ((L n)^2) : ℕ) : ℝ) := by rw [h1]
      _ ≤ (((L n)^2 : ℕ) : ℝ) := h2
      _ = ((L n:ℝ)^2) := by push_cast; ring
  have hC1 : 0 ≤ ((n:ℝ)+1) * M^2 := mul_nonneg (by positivity) (sq_nonneg M)
  have hC : 0 ≤ ((n:ℝ)+1) * M^2 * V n 0 := mul_nonneg hC1 hV0
  have hsum : |∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h|
      ≤ ((Finset.Icc 1 (min n ((L n)^2))).card : ℝ) * (((n:ℝ)+1) * M^2 * V n 0) := by
    calc |∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h|
        ≤ ∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), |A n h a * V n h| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), |A n h a| * |V n h| := by
          simp only [abs_mul]
      _ ≤ ∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), ((n:ℝ)+1) * M^2 * V n 0 := by
          refine Finset.sum_le_sum fun h _ => ?_
          calc |A n h a| * |V n h| ≤ ((n:ℝ)+1) * M^2 * |V n h| :=
                  mul_le_mul_of_nonneg_right (hA h) (abs_nonneg _)
            _ ≤ ((n:ℝ)+1) * M^2 * V n 0 := mul_le_mul_of_nonneg_left (hVh h) hC1
      _ = ((Finset.Icc 1 (min n ((L n)^2))).card : ℝ) * (((n:ℝ)+1) * M^2 * V n 0) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  show |A n 0 a * V n 0 + 2 * (∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h)|
      ≤ (1 + 2 * ((L n:ℝ)^2)) * ((n:ℝ)+1) * M^2 * V n 0
  have habs2 : |(2:ℝ)| = 2 := by norm_num
  have hstep : ((Finset.Icc 1 (min n ((L n)^2))).card : ℝ) * (((n:ℝ)+1) * M^2 * V n 0)
      ≤ ((L n:ℝ)^2) * (((n:ℝ)+1) * M^2 * V n 0) := mul_le_mul_of_nonneg_right hcard hC
  calc |A n 0 a * V n 0 + 2 * (∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h)|
      ≤ |A n 0 a * V n 0| + |2 * (∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h)| :=
        abs_add_le _ _
    _ = |A n 0 a| * |V n 0| + 2 * |∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h| := by
        rw [abs_mul, abs_mul, habs2]
    _ ≤ ((n:ℝ)+1) * M^2 * V n 0 + 2 * (((Finset.Icc 1 (min n ((L n)^2))).card : ℝ)
        * (((n:ℝ)+1) * M^2 * V n 0)) := by
        refine add_le_add ?_ (mul_le_mul_of_nonneg_left hsum htwo)
        rw [abs_of_nonneg hV0]
        exact mul_le_mul_of_nonneg_right (hA 0) hV0
    _ ≤ ((n:ℝ)+1) * M^2 * V n 0 + 2 * (((L n:ℝ)^2) * (((n:ℝ)+1) * M^2 * V n 0)) := by
        have hx : 2 * (((Finset.Icc 1 (min n ((L n)^2))).card : ℝ) * (((n:ℝ)+1) * M^2 * V n 0))
            ≤ 2 * (((L n:ℝ)^2) * (((n:ℝ)+1) * M^2 * V n 0)) :=
          mul_le_mul_of_nonneg_left hstep htwo
        exact add_le_add (le_refl _) hx
    _ = (1 + 2 * ((L n:ℝ)^2)) * ((n:ℝ)+1) * M^2 * V n 0 := by ring
