import Mathlib

namespace Conjectures.Goldbach.FrozenRelativeMajorMargin_aux.C1
noncomputable def gbPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

theorem L_goldbach_circle_coefficient :
    ∀ (n : ℕ) (w : ℕ → ℝ), let phase : ℝ → ℂ := fun t => Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I); let S : ℝ → ℂ := fun t => Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * phase ((k : ℝ) * t)); let f : ℝ → ℂ := fun t => (S t) ^ 2 * phase (-(n : ℝ) * t); intervalIntegral f (0 : ℝ) 1 MeasureTheory.volume = ((Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) : ℝ) : ℂ) := by
  intro n w
  dsimp only
  change intervalIntegral (fun t : ℝ => (Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * gbPhase ((k : ℝ) * t))) ^ 2 * gbPhase (-(n : ℝ) * t)) (0 : ℝ) 1 MeasureTheory.volume = ((Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) : ℝ) : ℂ)
  have hphase_mul : ∀ x y : ℝ, gbPhase (x + y) = gbPhase x * gbPhase y := by
    intro x y
    unfold gbPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphase_cont : Continuous gbPhase := by
    unfold gbPhase
    fun_prop
  have hphase_exp : ∀ m : ℤ, Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I) = 1 := by
    intro m
    have h : 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hphase_one : ∀ m : ℤ, gbPhase (m : ℝ) = 1 := by
    intro m
    unfold gbPhase
    have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) = 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, hphase_exp m]
  have horth : ∀ m : ℤ, (∫ t in (0 : ℝ)..1, gbPhase ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
    intro m
    have hrewrite : (∫ t in (0 : ℝ)..1, gbPhase ((m : ℝ) * t)) = ∫ t in (0 : ℝ)..1, Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      unfold gbPhase
      congr 1
      push_cast
      ring
    rw [hrewrite]
    by_cases hm : m = 0
    · subst hm
      simp
    · have hmr : (m : ℝ) ≠ 0 := by
        intro hzero
        exact hm (by exact_mod_cast hzero)
      have h1 : (2 * Real.pi * (m : ℝ)) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmr
      have hc : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
        have h2 : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
          simpa [Complex.ofReal_eq_zero] using h1
        exact mul_ne_zero h2 Complex.I_ne_zero
      have hval : Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ)) * Complex.I) = 1 := by
        have hone := hphase_one m
        simpa only [gbPhase] using hone
      rw [integral_exp_mul_complex hc]
      simp [hphase_exp m, hm]
  have hint_single : ∀ (c : ℂ) (a : ℝ), IntervalIntegrable (fun t : ℝ => c * gbPhase (a * t)) MeasureTheory.volume (0 : ℝ) 1 := by
    intro c a
    exact (continuous_const.mul (hphase_cont.comp (by fun_prop))).intervalIntegrable (0 : ℝ) 1
  have hint : ∀ k : ℕ, IntervalIntegrable (fun t : ℝ => Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * gbPhase (((k : ℝ) + (j : ℝ) - (n : ℝ)) * t))) MeasureTheory.volume (0 : ℝ) 1 := by
    intro k
    exact (continuous_finsetSum _ (fun j _ => continuous_const.mul (hphase_cont.comp (by fun_prop)))).intervalIntegrable (0 : ℝ) 1
  have hpoint : ∀ t : ℝ, (Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * gbPhase ((k : ℝ) * t))) ^ 2 * gbPhase (-(n : ℝ) * t) = Finset.sum (Finset.range (n + 1)) (fun k => Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * gbPhase (((k : ℝ) + (j : ℝ) - (n : ℝ)) * t))) := by
    intro t
    rw [pow_two, Finset.sum_mul_sum, Finset.sum_mul]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have h1 : gbPhase ((k : ℝ) * t) * gbPhase ((j : ℝ) * t) = gbPhase (((k : ℝ) + (j : ℝ)) * t) := by
      rw [← hphase_mul]
      congr 1
      ring
    have h2 : gbPhase (((k : ℝ) + (j : ℝ)) * t) * gbPhase (-(n : ℝ) * t) = gbPhase (((k : ℝ) + (j : ℝ) - (n : ℝ)) * t) := by
      rw [← hphase_mul]
      congr 1
      ring
    calc ((w k : ℂ) * gbPhase ((k : ℝ) * t)) * ((w j : ℂ) * gbPhase ((j : ℝ) * t)) * gbPhase (-(n : ℝ) * t)
        = ((w k : ℂ) * (w j : ℂ)) * (gbPhase ((k : ℝ) * t) * gbPhase ((j : ℝ) * t)) * gbPhase (-(n : ℝ) * t) := by ring
      _ = ((w k : ℂ) * (w j : ℂ)) * (gbPhase (((k : ℝ) + (j : ℝ)) * t) * gbPhase (-(n : ℝ) * t)) := by
        rw [h1]; ring
      _ = ((w k : ℂ) * (w j : ℂ)) * gbPhase (((k : ℝ) + (j : ℝ) - (n : ℝ)) * t) := by
        rw [h2]
  have hcollapse : (Finset.sum (Finset.range (n + 1)) (fun k => Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * (if ((k : ℤ) + (j : ℤ) - (n : ℤ)) = 0 then 1 else 0)))) = ((Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) : ℝ) : ℂ) := by
    have hcast : (Finset.sum (Finset.range (n + 1)) (fun p => (w p : ℂ) * (w (n - p) : ℂ))) = ((Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) : ℝ) : ℂ) := by
      simp only [Complex.ofReal_sum (Finset.range (n + 1)) (fun p => w p * w (n - p)), Complex.ofReal_mul]
    rw [← hcast]
    have hinner : ∀ k ∈ Finset.range (n + 1), (Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * (if ((k : ℤ) + (j : ℤ) - (n : ℤ)) = 0 then 1 else 0))) = (w k : ℂ) * (w (n - k) : ℂ) := by
      intro k hk
      have hle : k ≤ n := by
        have := Finset.mem_range.mp hk
        omega
      have hmem : n - k ∈ Finset.range (n + 1) := by
        simp only [Finset.mem_range]
        omega
      have hzero : ∀ j ∈ Finset.range (n + 1), j ≠ n - k → ((w k : ℂ) * (w j : ℂ)) * (if ((k : ℤ) + (j : ℤ) - (n : ℤ)) = 0 then 1 else 0) = 0 := by
        intro j hj hne
        have hjle : j ≤ n := by
          have := Finset.mem_range.mp hj
          omega
        have h2 : ((k : ℤ) + (j : ℤ) - (n : ℤ)) ≠ 0 := by
          intro hz
          have hsum : k + j = n := by omega
          exact hne (by omega)
        simp [h2]
      have hval : ((w k : ℂ) * (w (n - k) : ℂ)) * (if ((k : ℤ) + ((n - k : ℕ) : ℤ) - (n : ℤ)) = 0 then 1 else 0) = (w k : ℂ) * (w (n - k) : ℂ) := by
        have h1 : ((k : ℤ) + ((n - k : ℕ) : ℤ) - (n : ℤ)) = 0 := by omega
        simp [h1]
      calc (Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * (if ((k : ℤ) + (j : ℤ) - (n : ℤ)) = 0 then 1 else 0)))
          = ((w k : ℂ) * (w (n - k) : ℂ)) * (if ((k : ℤ) + ((n - k : ℕ) : ℤ) - (n : ℤ)) = 0 then 1 else 0) := Finset.sum_eq_single_of_mem (n - k) hmem hzero
        _ = (w k : ℂ) * (w (n - k) : ℂ) := hval
    refine Finset.sum_congr rfl (fun k hk => ?_)
    exact hinner k hk
  have hmain : (∫ t in (0 : ℝ)..1, Finset.sum (Finset.range (n + 1)) (fun k => Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * gbPhase (((k : ℝ) + (j : ℝ) - (n : ℝ)) * t)))) = ((Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_finsetSum (fun k _ => hint k)]
    have hstep : ∀ k ∈ Finset.range (n + 1), (∫ t in (0 : ℝ)..1, Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * gbPhase (((k : ℝ) + (j : ℝ) - (n : ℝ)) * t))) = Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * (if ((k : ℤ) + (j : ℤ) - (n : ℤ)) = 0 then 1 else 0)) := by
      intro k _
      rw [intervalIntegral.integral_finsetSum (fun j _ => hint_single ((w k : ℂ) * (w j : ℂ)) (((k : ℝ) + (j : ℝ) - (n : ℝ))))]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hm : ((k : ℝ) + (j : ℝ) - (n : ℝ)) = ((((k : ℤ) + (j : ℤ) - (n : ℤ)) : ℤ) : ℝ) := by
        push_cast
        ring
      rw [hm, horth]
    calc Finset.sum (Finset.range (n + 1)) (fun k => (∫ t in (0 : ℝ)..1, Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * gbPhase (((k : ℝ) + (j : ℝ) - (n : ℝ)) * t))))
        = Finset.sum (Finset.range (n + 1)) (fun k => Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * (if ((k : ℤ) + (j : ℤ) - (n : ℤ)) = 0 then 1 else 0))) := Finset.sum_congr rfl hstep
      _ = ((Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) : ℝ) : ℂ) := hcollapse
  rw [show (∫ t in (0 : ℝ)..1, (Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * gbPhase ((k : ℝ) * t))) ^ 2 * gbPhase (-(n : ℝ) * t)) = (∫ t in (0 : ℝ)..1, Finset.sum (Finset.range (n + 1)) (fun k => Finset.sum (Finset.range (n + 1)) (fun j => ((w k : ℂ) * (w j : ℂ)) * gbPhase (((k : ℝ) + (j : ℝ) - (n : ℝ)) * t)))) from intervalIntegral.integral_congr (fun t _ => hpoint t)]
  exact hmain
end Conjectures.Goldbach.FrozenRelativeMajorMargin_aux.C1

namespace Conjectures.Goldbach.FrozenRelativeMajorMargin_aux.C2
open MeasureTheory

theorem measurable_arcs (Q n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / ((q : ℝ) * (n : ℝ))} := by
  simp only [Set.ofPred_exists, Set.ofPred_and]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  repeat' apply (MeasurableSet.const _).inter
  exact (isClosed_le (continuous_id.sub continuous_const).abs continuous_const).measurableSet

theorem split_arc_integral {A : Set ℝ} {g : ℝ → ℂ}
    (hA : MeasurableSet A) (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, A.indicator g t) + (∫ t in (0 : ℝ)..1, Aᶜ.indicator g t) =
      ∫ t in (0 : ℝ)..1, g t := by
  have hint : IntegrableOn g (Set.Ioc (0 : ℝ) 1) volume :=
    (hg.intervalIntegrable (μ := volume) 0 1).1
  simp only [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  rw [MeasureTheory.integral_indicator hA, MeasureTheory.integral_indicator hA.compl]
  exact MeasureTheory.integral_add_compl hA hint
end Conjectures.Goldbach.FrozenRelativeMajorMargin_aux.C2

namespace Conjectures.Goldbach.FrozenRelativeMajorMargin_aux.C3
theorem L_goldbach_minor_bilinear_split :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0;
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * E ((k : ℝ) * t));
    let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2;
    let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))};
    let low := fun (n k : ℕ) => if k ^ 3 ≤ n then w k else 0;
    let high := fun (n k : ℕ) => w k - low n k;
    let I := fun (n : ℕ) (a b : ℕ → ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u * S n b u * E (-(n : ℝ) * u)) t) (0 : ℝ) 1 MeasureTheory.volume;
    ∀ n : ℕ, I n w w = I n (low n) (low n) + 2 * I n (low n) (high n) + I n (high n) (high n) := by
  intro w E S Q arcs low high I n
  have harcs_meas : MeasurableSet (arcs n) := by
    have heq : arcs n =
        ⋃ q ∈ Finset.range (Q n + 1), ⋃ a ∈ Finset.range (Q n + 1),
          if 1 ≤ q ∧ a ≤ q ∧ Nat.Coprime a q then
            {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))}
          else ∅ := by
      ext t
      simp only [arcs, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
      constructor
      · rintro ⟨q, a, hq1, hqQ, haq, hcop, hdist⟩
        refine ⟨q, Nat.lt_succ_of_le hqQ, a, Nat.lt_succ_of_le (haq.trans hqQ), ?_⟩
        split_ifs with hcond
        · exact hdist
        · exact False.elim (hcond ⟨hq1, haq, hcop⟩)
      · rintro ⟨q, hq, a, ha, ht⟩
        split_ifs at ht with hcond
        · exact ⟨q, a, hcond.1, Nat.lt_succ_iff.mp hq, hcond.2.1, hcond.2.2, ht⟩
        · exact False.elim ht
    rw [heq]
    refine Finset.measurableSet_biUnion _ fun q _ => Finset.measurableSet_biUnion _ fun a _ => ?_
    split_ifs
    · exact isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const |>.measurableSet
    · exact MeasurableSet.empty
  have hcompl_meas : MeasurableSet (arcs n)ᶜ := harcs_meas.compl
  have hE_cont : Continuous E := by
    unfold E
    fun_prop
  have hS_cont : ∀ a : ℕ → ℝ, Continuous (fun u : ℝ => S n a u) := by
    intro a
    unfold S
    fun_prop
  have hint : ∀ a b : ℕ → ℝ,
      IntervalIntegrable
        (fun t => (arcs n)ᶜ.indicator (fun u => S n a u * S n b u * E (-(n : ℝ) * u)) t)
        MeasureTheory.volume (0 : ℝ) 1 := by
    intro a b
    have hcont : Continuous (fun u : ℝ => S n a u * S n b u * E (-(n : ℝ) * u)) :=
      ((hS_cont a).mul (hS_cont b)).mul (hE_cont.comp (continuous_const.mul continuous_id))
    have hbase : IntervalIntegrable (fun u : ℝ => S n a u * S n b u * E (-(n : ℝ) * u))
        MeasureTheory.volume (0 : ℝ) 1 := hcont.intervalIntegrable 0 1
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hbase ⊢
    exact hbase.indicator hcompl_meas
  have hS_split : ∀ u : ℝ, S n w u = S n (low n) u + S n (high n) u := by
    intro u
    unfold S
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hw : w k = low n k + high n k := by
      dsimp only [high]
      ring
    rw [hw, Complex.ofReal_add, add_mul]
  have hpt : ∀ t : ℝ,
      (arcs n)ᶜ.indicator (fun u => S n w u * S n w u * E (-(n : ℝ) * u)) t =
      ((arcs n)ᶜ.indicator (fun u => S n (low n) u * S n (low n) u * E (-(n : ℝ) * u)) t +
        (2 : ℂ) * (arcs n)ᶜ.indicator (fun u => S n (low n) u * S n (high n) u * E (-(n : ℝ) * u)) t) +
      (arcs n)ᶜ.indicator (fun u => S n (high n) u * S n (high n) u * E (-(n : ℝ) * u)) t := by
    intro t
    by_cases ht : t ∈ (arcs n)ᶜ
    · simp only [Set.indicator_of_mem ht]
      rw [hS_split t]
      ring
    · simp only [Set.indicator_of_notMem ht, mul_zero, add_zero]
  have h1 := hint (low n) (low n)
  have h2 := (hint (low n) (high n)).const_mul (2 : ℂ)
  have h3 := hint (high n) (high n)
  dsimp only [I]
  calc
    intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n w u * S n w u * E (-(n : ℝ) * u)) t) (0 : ℝ) 1 MeasureTheory.volume
      = intervalIntegral
          (fun t =>
            ((arcs n)ᶜ.indicator (fun u => S n (low n) u * S n (low n) u * E (-(n : ℝ) * u)) t +
              (2 : ℂ) * (arcs n)ᶜ.indicator (fun u => S n (low n) u * S n (high n) u * E (-(n : ℝ) * u)) t) +
            (arcs n)ᶜ.indicator (fun u => S n (high n) u * S n (high n) u * E (-(n : ℝ) * u)) t)
          (0 : ℝ) 1 MeasureTheory.volume := by
        refine intervalIntegral.integral_congr fun t _ => hpt t
    _ = intervalIntegral
          (fun t =>
            (arcs n)ᶜ.indicator (fun u => S n (low n) u * S n (low n) u * E (-(n : ℝ) * u)) t +
              (2 : ℂ) * (arcs n)ᶜ.indicator (fun u => S n (low n) u * S n (high n) u * E (-(n : ℝ) * u)) t)
          (0 : ℝ) 1 MeasureTheory.volume +
        intervalIntegral
          (fun t => (arcs n)ᶜ.indicator (fun u => S n (high n) u * S n (high n) u * E (-(n : ℝ) * u)) t)
          (0 : ℝ) 1 MeasureTheory.volume :=
        intervalIntegral.integral_add (h1.add h2) h3
    _ = (intervalIntegral
          (fun t => (arcs n)ᶜ.indicator (fun u => S n (low n) u * S n (low n) u * E (-(n : ℝ) * u)) t)
          (0 : ℝ) 1 MeasureTheory.volume +
        intervalIntegral
          (fun t => (2 : ℂ) * (arcs n)ᶜ.indicator (fun u => S n (low n) u * S n (high n) u * E (-(n : ℝ) * u)) t)
          (0 : ℝ) 1 MeasureTheory.volume) +
        intervalIntegral
          (fun t => (arcs n)ᶜ.indicator (fun u => S n (high n) u * S n (high n) u * E (-(n : ℝ) * u)) t)
          (0 : ℝ) 1 MeasureTheory.volume := by
        rw [intervalIntegral.integral_add h1 h2]
    _ = (intervalIntegral
          (fun t => (arcs n)ᶜ.indicator (fun u => S n (low n) u * S n (low n) u * E (-(n : ℝ) * u)) t)
          (0 : ℝ) 1 MeasureTheory.volume +
        (2 : ℂ) * intervalIntegral
          (fun t => (arcs n)ᶜ.indicator (fun u => S n (low n) u * S n (high n) u * E (-(n : ℝ) * u)) t)
          (0 : ℝ) 1 MeasureTheory.volume) +
        intervalIntegral
          (fun t => (arcs n)ᶜ.indicator (fun u => S n (high n) u * S n (high n) u * E (-(n : ℝ) * u)) t)
          (0 : ℝ) 1 MeasureTheory.volume := by
        rw [intervalIntegral.integral_const_mul]
end Conjectures.Goldbach.FrozenRelativeMajorMargin_aux.C3

namespace Conjectures.Goldbach.FrozenRelativeMajorMargin_aux.C4
open Filter

theorem L_goldbach_small_small_saving : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n≥N, ‖I n (low n) (low n)‖≤e*(n:ℝ) := by
  intro w E S Q arcs low high I e he
  have cap (n : ℕ) (t : ℝ) (hn : 2 ≤ n) :
      ‖S n (low n) t‖ ≤ ((n : ℝ) ^ (1 / 3 : ℝ) + 1) * Real.log n := by
    let f (k : ℕ) : ℂ := (low n k : ℂ) * E ((k : ℝ) * t)
    let K := (Finset.range (n + 1)).filter (fun k => k^3 ≤ n ∧ Nat.Prime k)
    let R : ℝ := (n : ℝ) ^ (1 / 3 : ℝ)
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have hs : ∑ k ∈ K, f k = S n (low n) t := by
      apply Finset.sum_filter_of_ne
      intro k _ hk
      by_contra! h
      by_cases hc : k^3 ≤ n
      · exact hk (by simp [f, low, w, hc, h hc])
      · exact hk (by simp [f, low, hc])
    have hcard : (K.card : ℝ) ≤ R + 1 := by
      have hsub : K ⊆ Finset.range (⌊R⌋₊ + 1) := by
        intro k hk
        obtain ⟨_, hc, _⟩ := Finset.mem_filter.mp hk
        apply Finset.mem_range.mpr
        apply Nat.lt_succ_of_le
        apply Nat.le_floor
        dsimp [R]
        rw [one_div, Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by norm_num)]
        norm_cast
      have hc : K.card ≤ ⌊R⌋₊ + 1 := by simpa using Finset.card_le_card hsub
      calc
        (K.card : ℝ) ≤ (⌊R⌋₊ : ℝ) + 1 := by exact_mod_cast hc
        _ ≤ R + 1 := by gcongr; exact Nat.floor_le (by dsimp [R]; positivity)
    change ‖S n (low n) t‖ ≤ (R + 1) * Real.log n
    rw [← hs]
    calc
      ‖∑ k ∈ K, f k‖ ≤ ∑ k ∈ K, ‖f k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ K, Real.log (n : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        obtain ⟨hkn, hc, hp⟩ := Finset.mem_filter.mp hk
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hp.one_le
        simp only [f, low, hc, ite_true, w, hp, E, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hk1), Complex.norm_exp_ofReal_mul_I, mul_one]
        exact Real.log_le_log (by linarith) (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hkn))
      _ = (K.card : ℝ) * Real.log n := by simp
      _ ≤ (R + 1) * Real.log n := mul_le_mul_of_nonneg_right hcard hlog
  have asymp := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 3)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (asymp.bound (by positivity : 0 < e / 4))
  refine ⟨max N 2, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  let R : ℝ := (n : ℝ) ^ (1 / 3 : ℝ)
  have hR : 1 ≤ R := Real.one_le_rpow hn1 (by norm_num)
  have hR0 : 0 ≤ R := by linarith
  have hcube : R^3 = n := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlog2 : (Real.log n)^2 ≤ (e / 4) * R := by
    have h := hN n (le_trans (le_max_left _ _) hn)
    change ‖(Real.log n) ^ (2 : ℝ)‖ ≤ e / 4 * ‖R‖ at h
    simpa only [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg hR0] using h
  let B : ℝ := (R + 1) * Real.log n
  have pointwise (t : ℝ) : ‖(arcs n)ᶜ.indicator (fun u => S n (low n) u * S n (low n) u * E (-(n : ℝ) * u)) t‖ ≤ B^2 := by
    by_cases hm : t ∈ (arcs n)ᶜ
    · rw [Set.indicator_of_mem hm, norm_mul, norm_mul]
      simp only [E, Complex.norm_exp_ofReal_mul_I, mul_one, ← sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (cap n t hn2) _
    · rw [Set.indicator_of_notMem hm, norm_zero]; exact sq_nonneg _
  have hint : ‖I n (low n) (low n)‖ ≤ B^2 := by
    simpa only [I, sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (fun t _ => pointwise t)
  calc
    ‖I n (low n) (low n)‖ ≤ B^2 := hint
    _ = (R + 1)^2 * (Real.log n)^2 := mul_pow _ _ _
    _ ≤ (2 * R)^2 * ((e / 4) * R) := by
      gcongr
      linarith
    _ = e * (n : ℝ) := by rw [← hcube]; ring
end Conjectures.Goldbach.FrozenRelativeMajorMargin_aux.C4

namespace Conjectures.Goldbach.FrozenRelativeMajorMargin_aux.C5
open scoped BigOperators ComplexConjugate
open MeasureTheory Filter

noncomputable def parsevalPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

theorem bulkParseval :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); ∀ n w, intervalIntegral (fun t => ‖S n w t‖^2) (0:ℝ) 1 MeasureTheory.volume = Finset.sum (Finset.range (n+1)) (fun k => (w k)^2) := by
  dsimp only
  intro n w
  let T := Finset.range (n + 1)
  let S : ℝ → ℂ := fun t => ∑ k ∈ T, (w k : ℂ) * parsevalPhase ((k : ℝ) * t)
  let z : ℝ → ℂ := fun t => ∑ k ∈ T, ∑ j ∈ T,
    ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t)
  change intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume = _
  have hphase_mul : ∀ x y : ℝ, parsevalPhase (x + y) = parsevalPhase x * parsevalPhase y := by
    intro x y
    unfold parsevalPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphase_cont : Continuous parsevalPhase := by
    unfold parsevalPhase
    fun_prop
  have hphase_exp : ∀ m : ℤ, Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I) = 1 := by
    intro m
    have h : 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I =
        (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hphase_one : ∀ m : ℤ, parsevalPhase (m : ℝ) = 1 := by
    intro m
    unfold parsevalPhase
    have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, hphase_exp m]
  have hphase_conj : ∀ x : ℝ, conj (parsevalPhase x) = parsevalPhase (-x) := by
    intro x
    unfold parsevalPhase
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have horth : ∀ m : ℤ, intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
      (0 : ℝ) 1 MeasureTheory.volume = if m = 0 then 1 else 0 := by
    intro m
    have hrewrite : intervalIntegral (fun t : ℝ => parsevalPhase ((m : ℝ) * t))
        (0 : ℝ) 1 MeasureTheory.volume =
        ∫ t in (0 : ℝ)..1, Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      unfold parsevalPhase
      congr 1
      push_cast
      ring
    rw [hrewrite]
    by_cases hm : m = 0
    · subst hm
      simp
    · have hmr : (m : ℝ) ≠ 0 := by
        intro hzero
        exact hm (by exact_mod_cast hzero)
      have h1 : (2 * Real.pi * (m : ℝ)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmr
      have hc : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
        have h2 : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
          simpa [Complex.ofReal_eq_zero] using h1
        exact mul_ne_zero h2 Complex.I_ne_zero
      have hval : Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ)) * Complex.I) = 1 := by
        have hone := hphase_one m
        simpa only [parsevalPhase] using hone
      rw [integral_exp_mul_complex hc]
      simp [hphase_exp m, hm]
  have hint_single : ∀ (c : ℂ) (a : ℝ),
      IntervalIntegrable (fun t : ℝ => c * parsevalPhase (a * t)) MeasureTheory.volume (0 : ℝ) 1 := by
    intro c a
    exact (continuous_const.mul (hphase_cont.comp (by fun_prop))).intervalIntegrable (0 : ℝ) 1
  have hpoint : ∀ t : ℝ, (Complex.normSq (S t) : ℂ) = z t := by
    intro t
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp only [S, z]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul, Complex.conj_ofReal, hphase_conj]
    have hmul : parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t) =
        parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
      rw [← hphase_mul]
      congr 1
      ring
    calc
      ((w k : ℂ) * parsevalPhase (-((k : ℝ) * t))) *
          ((w j : ℂ) * parsevalPhase ((j : ℝ) * t)) =
          ((w k : ℂ) * (w j : ℂ)) *
            (parsevalPhase (-((k : ℝ) * t)) * parsevalPhase ((j : ℝ) * t)) := by ring
      _ = ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t) := by
        rw [hmul]
  have hint_z : IntervalIntegrable z MeasureTheory.volume (0 : ℝ) 1 := by
    dsimp only [z]
    exact (continuous_finsetSum _ (fun k _ => continuous_finsetSum _
      (fun j _ => continuous_const.mul (hphase_cont.comp (by fun_prop))))).intervalIntegrable (0 : ℝ) 1
  have hmain : intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume =
      ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
    dsimp only [z]
    have houter (k : ℕ) (hk : k ∈ T) : IntervalIntegrable (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        MeasureTheory.volume (0 : ℝ) 1 := by
      exact (continuous_finsetSum _ (fun j _ => continuous_const.mul
        (hphase_cont.comp (by fun_prop)))).intervalIntegrable (0 : ℝ) 1
    rw [intervalIntegral.integral_finsetSum houter]
    have hstep : ∀ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
        (0 : ℝ) 1 MeasureTheory.volume = ∑ j ∈ T,
        ((w k : ℂ) * (w j : ℂ)) * (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := by
      intro k hk
      rw [intervalIntegral.integral_finsetSum (fun j _ =>
        hint_single ((w k : ℂ) * (w j : ℂ)) (((j : ℝ) - (k : ℝ))))]
      apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hm : ((j : ℝ) - (k : ℝ)) = (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) := by
        push_cast
        ring
      simp_rw [hm]
      rw [horth]
    calc
      (∑ k ∈ T, intervalIntegral (fun t : ℝ => ∑ j ∈ T,
          ((w k : ℂ) * (w j : ℂ)) * parsevalPhase (((j : ℝ) - (k : ℝ)) * t))
          (0 : ℝ) 1 MeasureTheory.volume) =
          ∑ k ∈ T, ∑ j ∈ T, ((w k : ℂ) * (w j : ℂ)) *
            (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := Finset.sum_congr rfl hstep
      _ = ((∑ k ∈ T, (w k) ^ 2 : ℝ) : ℂ) := by
        push_cast
        simp only [sub_eq_zero, Int.ofNat_inj]
        apply Finset.sum_congr rfl
        intro k hk
        simp [hk, pow_two]
  have hre : intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume =
      (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
      intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp only [show (0 : ℝ) ≤ 1 by norm_num, ite_true, one_smul]
    exact integral_re hint_z.def'
  calc
    intervalIntegral (fun t => ‖S t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume =
        intervalIntegral (fun t => (z t).re) (0 : ℝ) 1 MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hp := congrArg Complex.re (hpoint t)
      simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hp
    _ = (intervalIntegral z (0 : ℝ) 1 MeasureTheory.volume).re := hre
    _ = ∑ k ∈ T, (w k) ^ 2 := by rw [hmain]; exact Complex.ofReal_re _

theorem highEnergy :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; ∀ n:ℕ,2≤n → intervalIntegral (fun t => ‖S n (high n) t‖^2) (0:ℝ) 1 MeasureTheory.volume≤((n:ℝ)+1)*(Real.log (n:ℝ))^2 := by
  dsimp only
  intro n hn
  rw [bulkParseval n]
  calc
    _ ≤ ∑ _k ∈ Finset.range (n + 1), (Real.log (n : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      by_cases hcut : k ^ 3 ≤ n
      · simp [hcut, sq_nonneg]
      · by_cases hkprime : Nat.Prime k
        · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hkprime.one_le
          have hlog : Real.log (k : ℝ) ≤ Real.log (n : ℝ) :=
            Real.log_le_log (by linarith) (by exact_mod_cast hkn)
          simpa [hcut, hkprime] using pow_le_pow_left₀ (Real.log_nonneg hk1) hlog 2
        · simp [hcut, hkprime, sq_nonneg]
    _ = _ := by simp

theorem lowCap : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let low := fun (n k : ℕ) => if k^3≤n then w k else 0; ∀ (n:ℕ) (t:ℝ), 2≤n → ‖S n (low n) t‖≤((n:ℝ)^(1/3:ℝ)+1)*Real.log (n:ℝ) := by
  intro w E S low n t hn
  let f (k : ℕ) : ℂ := (low n k : ℂ) * E ((k : ℝ) * t)
  let K := (Finset.range (n + 1)).filter (fun k => k^3 ≤ n ∧ Nat.Prime k)
  let R : ℝ := (n : ℝ) ^ (1 / 3 : ℝ)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hs : ∑ k ∈ K, f k = S n (low n) t := by
    apply Finset.sum_filter_of_ne
    intro k _ hk
    by_contra! h
    by_cases hc : k^3 ≤ n
    · exact hk (by simp [f, low, w, hc, h hc])
    · exact hk (by simp [f, low, hc])
  have hcard : (K.card : ℝ) ≤ R + 1 := by
    have hsub : K ⊆ Finset.range (⌊R⌋₊ + 1) := by
      intro k hk
      obtain ⟨_, hc, _⟩ := Finset.mem_filter.mp hk
      apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      apply Nat.le_floor
      dsimp [R]
      rw [one_div, Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by norm_num)]
      norm_cast
    have hc : K.card ≤ ⌊R⌋₊ + 1 := by simpa using Finset.card_le_card hsub
    calc
      (K.card : ℝ) ≤ (⌊R⌋₊ : ℝ) + 1 := by exact_mod_cast hc
      _ ≤ R + 1 := by gcongr; exact Nat.floor_le (by dsimp [R]; positivity)
  change ‖S n (low n) t‖ ≤ (R + 1) * Real.log n
  rw [← hs]
  calc
    ‖∑ k ∈ K, f k‖ ≤ ∑ k ∈ K, ‖f k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ K, Real.log (n : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hkn, hc, hp⟩ := Finset.mem_filter.mp hk
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hp.one_le
      simp only [f, low, hc, ite_true, w, hp, E, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hk1), Complex.norm_exp_ofReal_mul_I, mul_one]
      exact Real.log_le_log (by linarith) (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hkn))
    _ = (K.card : ℝ) * Real.log n := by simp
    _ ≤ (R + 1) * Real.log n := mul_le_mul_of_nonneg_right hcard hlog

theorem unitMeanSq (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in (0 : ℝ)..1, f t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, (f t) ^ 2 := by
  let m := ∫ t in (0 : ℝ)..1, f t
  have hnon := intervalIntegral.integral_nonneg_of_forall (μ := volume)
    (show (0 : ℝ) ≤ 1 by norm_num) (fun t : ℝ => sq_nonneg (f t - m))
  have hexp (t : ℝ) : (f t - m)^2 = ((f t)^2 - (2*m)*f t) + m^2 := by ring
  simp_rw [hexp] at hnon
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const] at hnon
  · simp only [sub_zero, one_smul] at hnon
    dsimp [m] at hnon
    nlinarith
  all_goals apply Continuous.intervalIntegrable; fun_prop

theorem L_goldbach_small_bulk_saving :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n≥N, ‖I n (low n) (high n)‖≤e*(n:ℝ) := by
  intro w E S Q arcs low high I e he
  have hsmall := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1/6) (by norm_num)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hev := hsmall.bound (show 0 < e / 4 by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨max 2 N, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog := Real.log_nonneg hn1
  let R : ℝ := (n : ℝ) ^ (1/3 : ℝ)
  let B : ℝ := (n : ℝ) ^ (1/2 : ℝ)
  let D : ℝ := (n : ℝ) ^ (1/6 : ℝ)
  have hR : 1 ≤ R := Real.one_le_rpow hn1 (by norm_num)
  have hR0 : 0 ≤ R := by linarith
  have hB : 0 ≤ B := Real.rpow_nonneg hn0.le _
  have hB2 : B^2 = (n : ℝ) := by
    dsimp [B]
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hn0.le]
  have hRBD : R*B*D = (n : ℝ) := by
    dsimp [R,B,D]
    rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]; norm_num
  let f := fun t : ℝ => ‖S n (high n) t‖
  have hcont : Continuous f := by
    dsimp only [f, S, E]
    fun_prop
  have hsquare := unitMeanSq f hcont
  have henergy : (∫ t in (0:ℝ)..1, (f t)^2) ≤ ((n:ℝ)+1) * (Real.log (n:ℝ))^2 := highEnergy n hn2
  have hmean : (∫ t in (0:ℝ)..1, f t) ≤ 2 * B * Real.log n := by
    apply le_of_sq_le_sq _ (by positivity)
    calc
      _ ≤ _ := hsquare.trans henergy
      _ ≤ (2 * B * Real.log n)^2 := by
        have hnum : (n:ℝ)+1 ≤ 4 * B^2 := by rw [hB2]; linarith
        nlinarith only [mul_le_mul_of_nonneg_right hnum (sq_nonneg (Real.log n))]
  let M := (R+1)*Real.log n
  have hM : 0 ≤ M := mul_nonneg (by linarith) hlog
  have hI : ‖I n (low n) (high n)‖ ≤ M * (∫ t in (0:ℝ)..1, f t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · apply Filter.Eventually.of_forall
      intro t _
      by_cases ht : t ∈ (arcs n)ᶜ
      · rw [Set.indicator_of_mem ht]
        simp only [norm_mul, E, Complex.norm_exp_ofReal_mul_I, mul_one]
        exact mul_le_mul_of_nonneg_right (lowCap n t hn2) (norm_nonneg _)
      · rw [Set.indicator_of_notMem ht]
        simpa using mul_nonneg hM (norm_nonneg (S n (high n) t))
    · exact (continuous_const.mul hcont).intervalIntegrable _ _
  have hpow : (Real.log (n:ℝ))^2 ≤ e/4*D := by
    have h := hN n (le_trans (le_max_right _ _) hn)
    change ‖Real.log (n:ℝ) ^ (2:ℝ)‖ ≤ e / 4 * ‖D‖ at h
    rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _)] at h
    exact h
  calc
    ‖I n (low n) (high n)‖ ≤ M * (∫ t in (0:ℝ)..1, f t) := hI
    _ ≤ M * (2*B*Real.log n) := mul_le_mul_of_nonneg_left hmean hM
    _ ≤ 4*R*B*(Real.log n)^2 := by
      dsimp [M]
      nlinarith only [mul_nonneg (mul_nonneg (sub_nonneg.mpr hR) hB) (sq_nonneg (Real.log n))]
    _ ≤ 4*R*B*(e/4*D) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = e*(n:ℝ) := by rw [← hRBD]; ring
end Conjectures.Goldbach.FrozenRelativeMajorMargin_aux.C5

namespace Conjectures.Goldbach.FrozenRelativeMajorMargin_aux
noncomputable def W (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k:ℝ) else 0

noncomputable def EE (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

noncomputable def SS (n : ℕ) (v : ℕ → ℝ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n+1)) (fun k => (v k:ℂ)*EE ((k:ℝ)*t))

def QQ (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2

def ARCS (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤QQ n ∧ a≤q ∧ Nat.Coprime a q ∧
    |t-(a:ℝ)/(q:ℝ)| ≤ (QQ n:ℝ)/((q:ℝ)*(n:ℝ))}

noncomputable def FF (n : ℕ) (t : ℝ) : ℂ := (SS n W t)^2*EE (-(n:ℝ)*t)

noncomputable def MAJOR (n : ℕ) : ℂ :=
  intervalIntegral (fun t => (ARCS n).indicator (FF n) t) (0:ℝ) 1 MeasureTheory.volume

noncomputable def LOW (n k : ℕ) : ℝ := if k^3≤n then W k else 0

noncomputable def HIGH (n k : ℕ) : ℝ := W k - LOW n k

noncomputable def II (n : ℕ) (a b : ℕ → ℝ) : ℂ :=
  intervalIntegral (fun t => (ARCS n)ᶜ.indicator
    (fun u => SS n a u*SS n b u*EE (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume

noncomputable def MASS (n : ℕ) : ℝ := Finset.sum (Finset.range (n+1)) (fun p => W p * W (n-p))

theorem measurable_ARCS (n : ℕ) : MeasurableSet (ARCS n) :=
  C2.measurable_arcs (QQ n) n

theorem cont_FF (n : ℕ) : Continuous (FF n) := by
  show Continuous (fun t : ℝ => (SS n W t)^2*EE (-(n:ℝ)*t))
  dsimp only [SS, EE, W]
  fun_prop

theorem coeff_eq (n : ℕ) :
    intervalIntegral (FF n) (0:ℝ) 1 MeasureTheory.volume = ((MASS n : ℝ):ℂ) :=
  C1.L_goldbach_circle_coefficient n W

theorem minor_eq (n : ℕ) :
    intervalIntegral (fun t => (ARCS n)ᶜ.indicator (FF n) t) (0:ℝ) 1 MeasureTheory.volume
      = II n W W := by
  show intervalIntegral (fun t => (ARCS n)ᶜ.indicator (FF n) t) (0:ℝ) 1 MeasureTheory.volume
      = intervalIntegral (fun t => (ARCS n)ᶜ.indicator
          (fun u => SS n W u*SS n W u*EE (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  by_cases ht : t ∈ (ARCS n)ᶜ
  · simp only [Set.indicator_of_mem ht]
    show FF n t = SS n W t*SS n W t*EE (-(n:ℝ)*t)
    dsimp only [FF]
    rw [sq]
  · simp only [Set.indicator_of_notMem ht]

theorem bilinear_eq (n : ℕ) :
    II n W W = II n (LOW n) (LOW n) + 2*II n (LOW n) (HIGH n) + II n (HIGH n) (HIGH n) :=
  C3.L_goldbach_minor_bilinear_split n

theorem smallSmall : ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n ≥ N, ‖II n (LOW n) (LOW n)‖ ≤ e*(n:ℝ) := by
  intro e he
  obtain ⟨N, hN⟩ := C4.L_goldbach_small_small_saving e he
  exact ⟨N, fun n hn => hN n hn⟩

theorem smallBulk : ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n ≥ N, ‖II n (LOW n) (HIGH n)‖ ≤ e*(n:ℝ) := by
  intro e he
  obtain ⟨N, hN⟩ := C5.L_goldbach_small_bulk_saving e he
  exact ⟨N, fun n hn => hN n hn⟩

theorem core (c : ℝ) (hc : 0 < c)
    (hmajor : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → Even n → c * (n : ℝ) ≤ (MAJOR n).re)
    (hhigh : ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n → Even n →
      -(c * (n : ℝ) / 2) ≤ (II n (HIGH n) (HIGH n)).re) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → c * (n : ℝ) / 4 ≤ MASS n := by
  obtain ⟨N₁, hN₁⟩ := hmajor
  obtain ⟨N₂, hN₂⟩ := hhigh
  obtain ⟨A, hA⟩ := smallSmall (c/16) (by positivity)
  obtain ⟨B, hB⟩ := smallBulk (c/16) (by positivity)
  refine ⟨max (max N₁ N₂) (max A B), ?_⟩
  intro n hn heven
  have hL : max N₁ N₂ ≤ n := (le_max_left _ _).trans hn
  have hR : max A B ≤ n := (le_max_right _ _).trans hn
  have hmaj := hN₁ n ((le_max_left _ _).trans hL) heven
  have hhh := hN₂ n ((le_max_right _ _).trans hL) heven
  have hll := hA n ((le_max_left _ _).trans hR)
  have hlh := hB n ((le_max_right _ _).trans hR)
  have lower {z : ℂ} {y : ℝ} (h : ‖z‖ ≤ y) : -y ≤ z.re :=
    (neg_le_neg h).trans (abs_le.mp (Complex.abs_re_le_norm _)).1
  have hsplit : MAJOR n + II n W W = ((MASS n : ℝ):ℂ) := by
    rw [← coeff_eq n, ← minor_eq n]
    exact C2.split_arc_integral (measurable_ARCS n) (cont_FF n)
  have h1 := congrArg Complex.re hsplit
  have h2 := congrArg Complex.re (bilinear_eq n)
  simp only [Complex.add_re, Complex.ofReal_re] at h1
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero, Nat.cast_ofNat] at h2
  have hcn : 0 ≤ c * (n:ℝ) := mul_nonneg (le_of_lt hc) (Nat.cast_nonneg n)
  have hcomb : c * (n:ℝ) / 4 ≤ c * (n:ℝ) - (c/16 * (n:ℝ)) - 2 * (c/16 * (n:ℝ))
      - c * (n:ℝ) / 2 := by
    nlinarith only [hcn]
  linarith only [h1, h2, hmaj, hhh, lower hll, lower hlh, hcomb]
end Conjectures.Goldbach.FrozenRelativeMajorMargin_aux

theorem Conjectures.Goldbach.FrozenRelativeMajorMargin :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let major := fun n : ℕ => intervalIntegral (fun t => (arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ c : ℝ, 0 < c → (∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → Even n → c * (n : ℝ) ≤ (major n).re) → (∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n → Even n → -(c * (n : ℝ) / 2) ≤ (I n (high n) (high n)).re) → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → c * (n : ℝ) / 4 ≤ Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p))) := by
  intro w E S Q arcs f major low high I c hc hM hH
  have hM2 : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → Even n → c * (n : ℝ) ≤
      (Conjectures.Goldbach.FrozenRelativeMajorMargin_aux.MAJOR n).re := hM
  have hH2 : ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n → Even n →
      -(c * (n : ℝ) / 2) ≤ (Conjectures.Goldbach.FrozenRelativeMajorMargin_aux.II n
        (Conjectures.Goldbach.FrozenRelativeMajorMargin_aux.HIGH n)
        (Conjectures.Goldbach.FrozenRelativeMajorMargin_aux.HIGH n)).re := hH
  exact Conjectures.Goldbach.FrozenRelativeMajorMargin_aux.core c hc hM2 hH2
