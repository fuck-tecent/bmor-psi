import Mathlib

namespace GoldbachPacket

private noncomputable def wave (j : ℕ) (t : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)

private noncomputable def waves (m : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, wave j t

private noncomputable def mass (m : ℕ) (s t : ℝ) : ℝ :=
  Real.exp (s * waves m t)

private theorem wave_step (j : ℕ) (t : ℝ) :
    wave (j + 1) t = wave j (2 * t) := by
  unfold wave
  congr 1
  rw [pow_succ (2 : ℝ) (j + 1)]
  ring

private theorem waves_step (m : ℕ) (t : ℝ) :
    waves (m + 1) t = wave 0 t + waves m (2 * t) := by
  change (∑ j ∈ Finset.range (m + 1), wave j t) =
    wave 0 t + (∑ j ∈ Finset.range m, wave j (2 * t))
  calc
    _ = (∑ j ∈ Finset.range m, wave (j + 1) t) + wave 0 t :=
      Finset.sum_range_succ' _ _
    _ = (∑ j ∈ Finset.range m, wave j (2 * t)) + wave 0 t :=
      congrArg (fun s : ℝ => s + wave 0 t)
        (Finset.sum_congr rfl (fun j _ => wave_step j t))
    _ = _ := add_comm _ _

private theorem wave_half (j : ℕ) (t : ℝ) : wave j (t + 1 / 2) = wave j t := by
  unfold wave
  have h :
      2 * Real.pi * (2 : ℝ) ^ (j + 1) * (t + 1 / 2) =
        2 * Real.pi * (2 : ℝ) ^ (j + 1) * t + ((2 ^ j : ℕ) : ℝ) * (2 * Real.pi) := by
    push_cast
    rw [pow_succ (2 : ℝ) j]
    ring
  rw [h, Real.cos_add_nat_mul_two_pi]

private theorem wave_quarter (t : ℝ) : wave 0 (t + 1 / 4) = -wave 0 t := by
  unfold wave
  rw [show 2 * Real.pi * (2 : ℝ) ^ (0 + 1 : ℕ) * (t + 1 / 4) =
    2 * Real.pi * (2 : ℝ) ^ (0 + 1 : ℕ) * t + Real.pi from by norm_num; ring]
  exact Real.cos_add_pi _

private theorem waves_half (m : ℕ) (t : ℝ) : waves m (t + 1 / 2) = waves m t :=
  Finset.sum_congr rfl (fun j _ => wave_half j t)

private theorem mass_continuous (m : ℕ) (s : ℝ) : Continuous (mass m s) := by
  unfold mass waves wave
  fun_prop

private theorem mass_period (m : ℕ) (s : ℝ) : Function.Periodic (mass m s) 1 := by
  intro t
  unfold mass
  rw [show t + 1 = t + 1 / 2 + 1 / 2 from by ring, waves_half, waves_half]

private theorem mass_integral_shift (m : ℕ) (s d : ℝ) :
    (∫ t in (0 : ℝ)..1, mass m s (t + d)) = ∫ t in (0 : ℝ)..1, mass m s t := by
  rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm (1 : ℝ)]
  simpa only [zero_add] using (mass_period m s).intervalIntegral_add_eq d 0

private theorem mass_integral_double (m : ℕ) (s : ℝ) :
    (∫ t in (0 : ℝ)..1, mass m s (2 * t)) = ∫ t in (0 : ℝ)..1, mass m s t := by
  rw [intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1) (c := 2)
    (f := mass m s) (by norm_num)]
  simp only [mul_zero, mul_one, smul_eq_mul]
  have h := (mass_period m s).intervalIntegral_add_eq 1 0
  norm_num at h
  have h₁ : IntervalIntegrable (mass m s) MeasureTheory.volume 0 1 :=
    (mass_continuous m s).intervalIntegrable _ _
  have h₂ : IntervalIntegrable (mass m s) MeasureTheory.volume 1 2 :=
    (mass_continuous m s).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals h₁ h₂, h]
  ring

private theorem mass_pair_le (m : ℕ) (s t : ℝ) :
    mass (m + 1) s t + mass (m + 1) s (t + 1 / 4) ≤
      (2 * Real.cosh s) * mass m s (2 * t) := by
  unfold mass
  rw [waves_step, waves_step, wave_quarter,
    show 2 * (t + 1 / 4) = 2 * t + 1 / 2 from by ring, waves_half]
  have hw : |wave 0 t| ≤ 1 := Real.abs_cos_le_one _
  have hc : Real.cosh (s * wave 0 t) ≤ Real.cosh s := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg s) hw
  have heq :
      Real.exp (s * (wave 0 t + waves m (2 * t))) +
        Real.exp (s * (-wave 0 t + waves m (2 * t))) =
          (2 * Real.cosh (s * wave 0 t)) * Real.exp (s * waves m (2 * t)) := by
    rw [mul_add, mul_add, Real.exp_add, Real.exp_add, mul_neg, Real.cosh_eq]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right (by linarith [hc]) (Real.exp_nonneg _)

theorem exponentialMoment (m : ℕ) (s : ℝ) :
    (∫ t in (0 : ℝ)..1, mass m s t) ≤ (Real.cosh s)^m := by
  induction m with
  | zero => simp [mass, waves]
  | succ m ih =>
    have hF := mass_continuous (m + 1) s
    have hG : Continuous (fun t : ℝ => mass (m + 1) s (t + 1 / 4)) :=
      hF.comp (continuous_id.add continuous_const)
    have hR : Continuous (fun t : ℝ => (2 * Real.cosh s) * mass m s (2 * t)) :=
      continuous_const.mul ((mass_continuous m s).comp (continuous_const.mul continuous_id))
    have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (by norm_num : (0 : ℝ) ≤ 1)
      ((hF.add hG).intervalIntegrable 0 1) (hR.intervalIntegrable 0 1)
      (fun t _ => mass_pair_le m s t)
    change (∫ t in (0 : ℝ)..1, mass (m + 1) s t + mass (m + 1) s (t + 1 / 4)) ≤
      ∫ t in (0 : ℝ)..1, (2 * Real.cosh s) * mass m s (2 * t) at h
    rw [intervalIntegral.integral_add (hF.intervalIntegrable 0 1) (hG.intervalIntegrable 0 1),
      mass_integral_shift, intervalIntegral.integral_const_mul, mass_integral_double] at h
    have hb : (∫ t in (0 : ℝ)..1, mass (m + 1) s t) ≤
        Real.cosh s * ∫ t in (0 : ℝ)..1, mass m s t := by nlinarith
    rw [pow_succ, mul_comm ((Real.cosh s) ^ m) (Real.cosh s)]
    have hcosh : 0 ≤ Real.cosh s := by
      rw [Real.cosh_eq]
      positivity
    exact hb.trans (mul_le_mul_of_nonneg_left ih hcosh)

theorem highMaskMass (m : ℕ) (A : Set ℝ) (hA : MeasurableSet A)
    (hmask : ∀ t ∈ A, (m : ℝ) / 2 ≤ waves m t) :
    (∫ t in (0 : ℝ)..1, A.indicator (fun _ => (1 : ℝ)) t) ≤ ((9 : ℝ) / 10) ^ m := by
  let s : ℝ := Real.log 2
  let a : ℝ := Real.exp (s / 2)
  have hs : 0 ≤ s := Real.log_nonneg (by norm_num)
  have ha : 0 < a := Real.exp_pos _
  have hExp : Real.exp s = 2 := Real.exp_log (by norm_num)
  have hSquare : a ^ 2 = 2 := by
    calc
      a ^ 2 = Real.exp (s / 2 + s / 2) := by rw [pow_two, Real.exp_add]
      _ = Real.exp s := by congr 1; ring
      _ = 2 := hExp
  have ha_lower : (7 : ℝ) / 5 < a := by
    by_contra! h
    have hsq := pow_le_pow_left₀ ha.le h 2
    rw [hSquare] at hsq
    norm_num at hsq
  have hC : Real.cosh s = 5 / 4 := by
    rw [Real.cosh_eq, Real.exp_neg, hExp]
    norm_num
  have hC_le : Real.cosh s ≤ (9 / 10 : ℝ) * a := by rw [hC]; linarith
  let f := A.indicator (fun _ : ℝ => (1 : ℝ))
  have hf : IntervalIntegrable f MeasureTheory.volume (0 : ℝ) 1 := by
    have h : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume (0 : ℝ) 1 :=
      intervalIntegrable_const
    exact ⟨h.1.indicator hA, h.2.indicator hA⟩
  have hpoint (t : ℝ) : a ^ m * f t ≤ mass m s t := by
    by_cases ht : t ∈ A
    · rw [show f t = 1 from Set.indicator_of_mem ht _, mul_one]
      change (Real.exp (s / 2)) ^ m ≤ Real.exp (s * waves m t)
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (hmask t ht) hs
      nlinarith
    · rw [show f t = 0 from Set.indicator_of_notMem ht _, mul_zero]
      exact Real.exp_nonneg _
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (hf.const_mul (a ^ m)) ((mass_continuous m s).intervalIntegrable 0 1) (fun t _ => hpoint t)
  rw [intervalIntegral.integral_const_mul] at h
  have hu := (h.trans (exponentialMoment m s)).trans
    (pow_le_pow_left₀ (by rw [hC]; norm_num) hC_le m)
  rw [mul_pow, mul_comm (((9 : ℝ) / 10) ^ m)] at hu
  exact le_of_mul_le_mul_left hu (pow_pos ha m)

end GoldbachPacket

theorem Conjectures.Goldbach.PacketMaskLogDecay :
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; ∀ d : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, (1+Real.log (n:ℝ))^d * (intervalIntegral ((B n).indicator (fun _ => (1:ℝ))) (0:ℝ) 1 MeasureTheory.volume) ≤ ε := by
  intro w E S Q arcs low high I L K B U d ε hε
  have h_arcs_meas (n : ℕ) : MeasurableSet (arcs n) := by
    have h_eq : arcs n = ⋃ q : ℕ, ⋃ a : ℕ,
        {t : ℝ | 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))} := by
      ext t
      simp only [arcs, Set.mem_setOf_eq, Set.mem_iUnion]
    rw [h_eq]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
    by_cases hqa : 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q
    · rcases hqa with ⟨h1, h2, h3, h4⟩
      have hset : {t : ℝ | 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))} =
          {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))} := by
        ext t
        exact ⟨fun ht => ht.2.2.2.2, fun ht => ⟨h1, h2, h3, h4, ht⟩⟩
      rw [hset]
      exact (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const))
        continuous_const).measurableSet
    · have hset : {t : ℝ | 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))} = ∅ := by
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro ht
        exact hqa ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩
      rw [hset]
      exact MeasurableSet.empty
  have hK_cont (n : ℕ) : Continuous (K n) := by
    dsimp only [K]
    have hc : Continuous (fun t : ℝ => ∑ j ∈ Finset.range (L n),
        Real.cos (2 * Real.pi * (2 : ℝ)^(j+1) * t)) := by
      exact continuous_finsetSum _ fun j _ =>
        Real.continuous_cos.comp (continuous_const.mul continuous_id)
    exact hc.div_const _
  have hB_meas (n : ℕ) : MeasurableSet (B n) := by
    have h_eq : B n = (arcs n)ᶜ ∩ {t : ℝ | (1 : ℝ) / 2 < K n t} := by
      ext t
      simp only [B, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    rw [h_eq]
    exact (h_arcs_meas n).compl.inter (isOpen_lt continuous_const (hK_cont n)).measurableSet
  have hB_mass (n : ℕ) :
      intervalIntegral ((B n).indicator (fun _ => (1 : ℝ))) (0 : ℝ) 1 MeasureTheory.volume ≤
        ((9 : ℝ) / 10) ^ (L n) := by
    apply GoldbachPacket.highMaskMass (L n) (B n) (hB_meas n)
    intro t ht
    have hL_pos : (0 : ℝ) < (L n : ℝ) := by
      exact_mod_cast (show 0 < L n from lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _))
    have hmul : (1 : ℝ) / 2 * (L n : ℝ) <
        ∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t) :=
      (lt_div_iff₀ hL_pos).mp ht.2
    change (L n : ℝ) / 2 ≤
      ∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)
    linarith
  have hsum : Summable (fun m : ℕ => (m : ℝ) ^ d * ((9 : ℝ) / 10) ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one d (by rw [Real.norm_eq_abs]; norm_num)
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ d := by positivity
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hsum.tendsto_atTop_zero (ε / (4 : ℝ) ^ d)
    (div_pos hε h4pos)
  refine ⟨max 16 (2 ^ (2 * M)), fun n hn => ?_⟩
  have hn16 : 16 ≤ n := le_trans (le_max_left 16 (2 ^ (2 * M))) hn
  have h2M : 2 * M ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num : 1 < 2) (le_trans (le_max_right 16 (2 ^ (2 * M))) hn)
  have hLM : M ≤ L n := by
    have hL : Nat.log 2 n / 2 ≤ L n := le_max_right 1 (Nat.log 2 n / 2)
    omega
  have hlog_ge4 : 4 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by omega : 2 ^ 4 ≤ n)
  have hn_lt : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog_le : Real.log (n : ℝ) ≤ (Nat.log 2 n : ℝ) + 1 := by
    calc Real.log (n : ℝ)
      _ ≤ Real.log ((2 : ℝ) ^ (Nat.log 2 n + 1)) :=
          Real.log_le_log (Nat.cast_pos.mpr (by omega)) hn_lt.le
      _ = ((Nat.log 2 n + 1 : ℕ) : ℝ) * Real.log 2 := Real.log_pow _ _
      _ ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
      _ = (Nat.log 2 n : ℝ) + 1 := by push_cast; ring
  have h_nat : Nat.log 2 n + 2 ≤ 4 * L n := by
    have hL : Nat.log 2 n / 2 ≤ L n := le_max_right 1 (Nat.log 2 n / 2)
    omega
  have h_real : (Nat.log 2 n : ℝ) + 2 ≤ 4 * (L n : ℝ) := by
    exact_mod_cast h_nat
  have h1log_le : 1 + Real.log (n : ℝ) ≤ 4 * (L n : ℝ) := by linarith
  have h1log_nonneg : 0 ≤ 1 + Real.log (n : ℝ) := by
    have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    linarith
  have hpow : (1 + Real.log (n : ℝ)) ^ d ≤ (4 : ℝ) ^ d * (L n : ℝ) ^ d := by
    calc (1 + Real.log (n : ℝ)) ^ d
      _ ≤ (4 * (L n : ℝ)) ^ d := pow_le_pow_left₀ h1log_nonneg h1log_le d
      _ = (4 : ℝ) ^ d * (L n : ℝ) ^ d := mul_pow 4 (L n : ℝ) d
  have h_int_nonneg :
      0 ≤ intervalIntegral ((B n).indicator (fun _ => (1 : ℝ))) (0 : ℝ) 1 MeasureTheory.volume :=
    intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (fun t _ => Set.indicator_nonneg (fun _ _ => by norm_num) t)
  have h_prod :
      (1 + Real.log (n : ℝ)) ^ d *
          intervalIntegral ((B n).indicator (fun _ => (1 : ℝ))) (0 : ℝ) 1 MeasureTheory.volume ≤
        (4 : ℝ) ^ d * ((L n : ℝ) ^ d * ((9 : ℝ) / 10) ^ (L n)) := by
    calc (1 + Real.log (n : ℝ)) ^ d *
            intervalIntegral ((B n).indicator (fun _ => (1 : ℝ))) (0 : ℝ) 1 MeasureTheory.volume
      _ ≤ ((4 : ℝ) ^ d * (L n : ℝ) ^ d) * ((9 : ℝ) / 10) ^ (L n) :=
          mul_le_mul hpow (hB_mass n) h_int_nonneg (by positivity)
      _ = (4 : ℝ) ^ d * ((L n : ℝ) ^ d * ((9 : ℝ) / 10) ^ (L n)) := by ring
  have h_tail : (4 : ℝ) ^ d * ((L n : ℝ) ^ d * ((9 : ℝ) / 10) ^ (L n)) ≤ ε := by
    have hdist := hM (L n) hLM
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hdist
    have h1 := (lt_div_iff₀ h4pos).mp hdist
    rw [mul_comm] at h1
    exact h1.le
  exact h_prod.trans h_tail