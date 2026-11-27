import Mathlib

theorem PEqualNP.Outside.L_goldbach_minor_bilinear_split :
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
