import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_skirt_polylog_moduli

-- child 1 zh: 分母截断从 Q 扩至 min(B,Q²) 后，新增区域的完整相位积分具有最终单侧下界 −εn。
-- child 1 en: The full-phase region newly covered when the denominator cap rises from Q to min(B,Q²) has eventual signed floor −εn.
-- child 2 zh: 分母截断从 min(B,Q²) 扩至 B 后，新增区域的完整相位积分具有最终单侧下界 −εn。
-- child 2 en: The full-phase region newly covered when the denominator cap rises from min(B,Q²) to B has eventual signed floor −εn.

theorem Conjectures.Cuts.Cutc04cdc8f2268a337c6b7538d
  (hMid :
    let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2
    let B := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
    let H := fun n : ℕ => 256 * B n * Q n
    let C := fun n : ℕ => min (B n) ((Q n) ^ 2)
    let A := fun (n D R : ℕ) => {t : ℝ | ∃ q a : ℕ,
      1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ (R : ℝ) / ((q : ℝ) * (n : ℝ))}
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
    let E := fun t : ℝ => Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
    let f := fun (n : ℕ) (t : ℝ) =>
      (∑ k ∈ Finset.range (n + 1), (w k : ℂ) * E ((k : ℝ) * t)) ^ 2 * E (-(n : ℝ) * t)
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      -(e * (n : ℝ)) ≤ (intervalIntegral (fun t =>
        (A n (C n) (H n) \ A n (Q n) (H n)).indicator (f n) t)
        (0 : ℝ) 1 MeasureTheory.volume).re)
  (hHigh :
    let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2
    let B := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
    let H := fun n : ℕ => 256 * B n * Q n
    let C := fun n : ℕ => min (B n) ((Q n) ^ 2)
    let A := fun (n D R : ℕ) => {t : ℝ | ∃ q a : ℕ,
      1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ (R : ℝ) / ((q : ℝ) * (n : ℝ))}
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
    let E := fun t : ℝ => Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
    let f := fun (n : ℕ) (t : ℝ) =>
      (∑ k ∈ Finset.range (n + 1), (w k : ℂ) * E ((k : ℝ) * t)) ^ 2 * E (-(n : ℝ) * t)
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      -(e * (n : ℝ)) ≤ (intervalIntegral (fun t =>
        (A n (B n) (H n) \ A n (C n) (H n)).indicator (f n) t)
        (0 : ℝ) 1 MeasureTheory.volume).re) :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
    let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t))
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2
    let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}
    let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t)
    let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
    let H := fun n : ℕ => 256 * Q₁ n * Q n
    let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}
    let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}
    let lowPart := fun n : ℕ => lowWideArcs n \ arcs n
    let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n
    let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}
    let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re
    let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (A n)
    floor (fun n => wideArcs n \ arcs n)) := by
  intro w E S Q arcs f B H wide low lowPart remainder inner J floor
  let C := fun n : ℕ => min (B n) ((Q n) ^ 2)
  let A := fun (n D R : ℕ) => {t : ℝ | ∃ q a : ℕ,
    1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ (R : ℝ) / ((q : ℝ) * (n : ℝ))}
  let mid := fun n => A n (C n) (H n)
  have hLow : ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      -(e * (n : ℝ)) ≤ J n (low n \ arcs n) :=
    PEqualNP.Outside.L_goldbach_frontier_skirt_polylog_moduli
  change (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    -(e * (n : ℝ)) ≤ J n (mid n \ low n)) at hMid
  change (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    -(e * (n : ℝ)) ≤ J n (wide n \ mid n)) at hHigh
  change ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    -(e * (n : ℝ)) ≤ J n (wide n \ arcs n)

  have powGap (m : ℕ) (hm : 40 ≤ m) : m ^ 6 + 2 ≤ 2 ^ m := by
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      have hstep : (10 * (m + 1)) ^ 6 ≤ (11 * m) ^ 6 :=
        Nat.pow_le_pow_left (by omega) 6
      have hscale : 10 ^ 6 * (m + 1) ^ 6 ≤ 10 ^ 6 * (2 * m ^ 6) := by
        calc
          10 ^ 6 * (m + 1) ^ 6 = (10 * (m + 1)) ^ 6 := by ring
          _ ≤ (11 * m) ^ 6 := hstep
          _ = 11 ^ 6 * m ^ 6 := by ring
          _ ≤ (10 ^ 6 * 2) * m ^ 6 := Nat.mul_le_mul_right _ (by norm_num)
          _ = 10 ^ 6 * (2 * m ^ 6) := Nat.mul_assoc _ _ _
      have hpow := Nat.le_of_mul_le_mul_left hscale (by norm_num)
      calc
        (m + 1) ^ 6 + 2 ≤ 2 * 2 ^ m := by omega
        _ = 2 ^ (m + 1) := by rw [pow_succ 2 m, Nat.mul_comm]
  have hGrowth : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Q n ≤ B n := by
    refine ⟨2 ^ 40, fun n hn => ?_⟩
    have hlog : 40 ≤ Nat.log 2 (n + 2) := by
      apply Nat.le_log_of_pow_le (by norm_num)
      omega
    have hpow := powGap _ hlog
    have hle := Nat.pow_log_le_self 2 (x := n + 2) (by omega)
    have hnat : Q n ^ 3 ≤ n := by
      dsimp only [Q]
      rw [← pow_mul]
      change Nat.log 2 (n + 2) ^ 6 ≤ n
      exact Nat.le_of_add_le_add_right (hpow.trans hle)
    have hreal : ((Q n : ℕ) : ℝ) ^ (3 : ℕ) ≤ (n : ℝ) := by exact_mod_cast hnat
    change Q n ≤ ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
    apply Nat.le_floor
    calc
      (Q n : ℝ) = (((Q n : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hreal (by norm_num)

  have hMeas (n D R : ℕ) : MeasurableSet (A n D R) := by
    have hset : A n D R =
        ⋃ q : ℕ, ⋃ a : ℕ,
          {t : ℝ | 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q} ∩
          {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (R : ℝ) / ((q : ℝ) * (n : ℝ))} := by
      ext t
      simp only [A, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨q, a, hq, hD, ha, hc, ht⟩
        exact ⟨q, a, ⟨hq, hD, ha, hc⟩, ht⟩
      · rintro ⟨q, a, ⟨hq, hD, ha, hc⟩, ht⟩
        exact ⟨q, a, hq, hD, ha, hc, ht⟩
    rw [hset]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
    exact (MeasurableSet.const _).inter (measurableSet_le (by fun_prop) (by fun_prop))
  have hMono (n : ℕ) {D D' R R' : ℕ} (hD : D ≤ D') (hR : R ≤ R') :
      A n D R ⊆ A n D' R' := by
    rintro t ⟨q, a, hq, hqD, ha, hc, ht⟩
    exact ⟨q, a, hq, hqD.trans hD, ha, hc, ht.trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hR) (by positivity))⟩

  have hAdd (n : ℕ) (X Y Z : Set ℝ) (hXY : X ⊆ Y) (hYZ : Y ⊆ Z)
      (hX : MeasurableSet X) (hY : MeasurableSet Y) (hZ : MeasurableSet Z) :
      J n (Z \ X) = J n (Y \ X) + J n (Z \ Y) := by
    have hf : Continuous (f n) := by
      simp only [f, S, E]
      fun_prop
    have hInt (U : Set ℝ) (hU : MeasurableSet U) :
        IntervalIntegrable (U.indicator (f n)) MeasureTheory.volume 0 1 := by
      have h := hf.intervalIntegrable (μ := MeasureTheory.volume) 0 1
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h ⊢
      exact h.indicator hU
    have hSplit : Z \ X = (Y \ X) ∪ (Z \ Y) := by
      ext t
      constructor
      · intro ht
        by_cases h : t ∈ Y
        · exact Or.inl ⟨h, ht.2⟩
        · exact Or.inr ⟨ht.1, h⟩
      · rintro (ht | ht)
        · exact ⟨hYZ ht.1, ht.2⟩
        · exact ⟨ht.1, fun h => ht.2 (hXY h)⟩
    have hDisj : Disjoint (Y \ X) (Z \ Y) :=
      Set.disjoint_left.mpr fun _ ht ht' => ht'.2 ht.1
    have hFun : (fun t => ((Y \ X) ∪ (Z \ Y)).indicator (f n) t) =
        fun t => (Y \ X).indicator (f n) t + (Z \ Y).indicator (f n) t := by
      funext t
      rw [Set.indicator_union_of_disjoint hDisj]
    unfold J
    rw [hSplit, hFun, intervalIntegral.integral_add (hInt _ (hY.diff hX)) (hInt _ (hZ.diff hY)),
      Complex.add_re]

  intro e he
  obtain ⟨NG, hG⟩ := hGrowth
  obtain ⟨NL, hL⟩ := hLow (e / 3) (by positivity)
  obtain ⟨NM, hM⟩ := hMid (e / 3) (by positivity)
  obtain ⟨NH, hH⟩ := hHigh (e / 3) (by positivity)
  refine ⟨max NG (max NL (max NM NH)), fun n hn hEven => ?_⟩
  have hQB := hG n (by omega)
  have hQC : Q n ≤ C n := le_min hQB (by
    rw [pow_two]
    exact Nat.le_mul_self _)
  have hQH : Q n ≤ H n := by
    by_cases hzero : Q n = 0
    · simp [hzero]
    have hpos : 1 ≤ 256 * B n := by omega
    change Q n ≤ (256 * B n) * Q n
    simpa using Nat.mul_le_mul_right (Q n) hpos
  have hAL : arcs n ⊆ low n := hMono n le_rfl hQH
  have hLM : low n ⊆ mid n := hMono n hQC le_rfl
  have hMW : mid n ⊆ wide n := hMono n (min_le_left _ _) le_rfl
  have mA : MeasurableSet (arcs n) := hMeas n (Q n) (Q n)
  have mL : MeasurableSet (low n) := hMeas n (Q n) (H n)
  have mM : MeasurableSet (mid n) := hMeas n (C n) (H n)
  have mW : MeasurableSet (wide n) := hMeas n (B n) (H n)
  rw [hAdd n (arcs n) (mid n) (wide n) (hAL.trans hLM) hMW mA mM mW,
      hAdd n (arcs n) (low n) (mid n) hAL hLM mA mL mM]
  linarith only [hL n (by omega) hEven, hM n (by omega) hEven, hH n (by omega) hEven]
