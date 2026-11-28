import Mathlib

open Finset MeasureTheory Set
open scoped BigOperators Classical Interval

-- Fourier orthogonality and indicator splitting adapt PR #158 and their use in
-- EstermannAlmostAllPolylog (Apache-2.0). The reflected scale follows the
-- checkpoint of HymnOfLight, revision b3e8a9fec6067484ff44957e93f85e23697040a5.

-- child 1 zh: 對多對數分母的主弧核心，證明實際素數平方係數在反射區間有一致正下界。
-- child 1 en: Give the actual prime-square coefficient on the polylogarithmic core a uniform positive floor on the reflected interval.
-- child 2 zh: 對分母小於四次方根的寬弧之外，將係數實部不超過負 Y/32 的目標數界在 Y 的 19/25 次方量級。
-- child 2 en: Bound the negative tail outside the small-denominator wide arcs at threshold Y/32 with exponent 19/25.
-- child 3 zh: 對四次方根以下寬弧扣除核心後的部分，將反射區間的偶數負尾目標數界在 Y 的 79/100 次方量級。
-- child 3 en: Bound the negative tail of the intermediate arcs at the same threshold on the reflected even interval with exponent 79/100.

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem Conjectures.Cuts.Cut415b3da0b761ef02224b42bf
    (hCore :
    let e := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    let S := fun (Y : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (Y+1)).filter Nat.Prime,
      (Real.log p : ℂ) * e ((p : ℝ) * t);
    let F := fun (Y m : ℕ) (t : ℝ) => (S Y t)^2 * e (-(m : ℝ) * t);
    let B := fun Y : ℕ =>
      let L := Nat.log 2 (Y+2)
      {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ L ∧ a ≤ q ∧ a.Coprime q ∧
        |t-(a:ℝ)/q| ≤ ((L^3 : ℕ) : ℝ)/((q:ℝ)*Y)};
    let C := fun (D : Set ℝ) (Y m : ℕ) =>
      intervalIntegral (D.indicator (F Y m)) 0 1 MeasureTheory.volume;
    ∃ N : ℕ, ∀ Y ≥ N, ∀ m : ℕ, 2*m ≤ 3*Y → 4*Y ≤ 3*m → Even m →
      7*(Y:ℝ)/64 ≤ (C (B Y) Y m).re)
    (hComp :
    let e := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    let S := fun (Y : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (Y+1)).filter Nat.Prime,
      (Real.log p : ℂ) * e ((p : ℝ) * t);
    let F := fun (Y m : ℕ) (t : ℝ) => (S Y t)^2 * e (-(m : ℝ) * t);
    let A := fun Y : ℕ =>
      let Q := ⌊(Y : ℝ)^(1/3 : ℝ)⌋₊
      let H : ℕ := 256*Q*(Nat.log 2 (Y+2))^2
      {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ (q : ℝ) < (Y : ℝ)^(1/4 : ℝ) ∧
        q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧ |t-(a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*Y)};
    let C := fun (D : Set ℝ) (Y m : ℕ) =>
      intervalIntegral (D.indicator (F Y m)) 0 1 MeasureTheory.volume;
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ Y ≥ N,
      (((Finset.Icc Y (2*Y)).filter (fun m => (C (A Y)ᶜ Y m).re ≤ -(Y:ℝ)/32)).card : ℝ)
        ≤ K*(Y:ℝ)^(19/25:ℝ))
    (hMiddle :
    let e := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    let S := fun (Y : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (Y+1)).filter Nat.Prime,
      (Real.log p : ℂ) * e ((p : ℝ) * t);
    let F := fun (Y m : ℕ) (t : ℝ) => (S Y t)^2 * e (-(m : ℝ) * t);
    let A := fun Y : ℕ =>
      let Q := ⌊(Y : ℝ)^(1/3 : ℝ)⌋₊
      let H : ℕ := 256*Q*(Nat.log 2 (Y+2))^2
      {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ (q : ℝ) < (Y : ℝ)^(1/4 : ℝ) ∧
        q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧ |t-(a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*Y)};
    let B := fun Y : ℕ =>
      let L := Nat.log 2 (Y+2)
      {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ L ∧ a ≤ q ∧ a.Coprime q ∧
        |t-(a:ℝ)/q| ≤ ((L^3 : ℕ) : ℝ)/((q:ℝ)*Y)};
    let C := fun (D : Set ℝ) (Y m : ℕ) =>
      intervalIntegral (D.indicator (F Y m)) 0 1 MeasureTheory.volume;
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ Y ≥ N,
      (((Finset.Icc Y (2*Y)).filter (fun m => Even m ∧ 2*m ≤ 3*Y ∧ 4*Y ≤ 3*m ∧
        (C (A Y \ B Y) Y m).re ≤ -(Y:ℝ)/32)).card : ℝ) ≤ K*(Y:ℝ)^(79/100:ℝ)) : (let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card; ∃ X₀ : ℕ, ∀ X ≥ X₀, let L := Nat.log 2 X / 2; let E := (Finset.Ico X (2*X)).filter (fun n => Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e)=0)).card); E.card^5 ≤ X^4) := by
  classical
  let e := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
  let S := fun (Y : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (Y+1)).filter Nat.Prime,
    (Real.log p : ℂ) * e ((p : ℝ) * t);
  let F := fun (Y m : ℕ) (t : ℝ) => (S Y t)^2 * e (-(m : ℝ) * t)
  let A := fun Y : ℕ =>
    let Q := ⌊(Y : ℝ)^(1/3 : ℝ)⌋₊
    let H : ℕ := 256*Q*(Nat.log 2 (Y+2))^2
    {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ (q : ℝ) < (Y : ℝ)^(1/4 : ℝ) ∧
      q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧ |t-(a:ℝ)/q| ≤ (H:ℝ)/((q:ℝ)*Y)}
  let B := fun Y : ℕ =>
    let L := Nat.log 2 (Y+2)
    {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ L ∧ a ≤ q ∧ a.Coprime q ∧
      |t-(a:ℝ)/q| ≤ ((L^3 : ℕ) : ℝ)/((q:ℝ)*Y)}
  let C := fun (D : Set ℝ) (Y m : ℕ) =>
    intervalIntegral (D.indicator (F Y m)) 0 1 MeasureTheory.volume
  have phase_add (u v : ℝ) : e (u + v) = e u * e v := by
    unfold e
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

  have fourier_mode (m : ℤ) :
      (∫ t in (0 : ℝ)..1, e ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
    by_cases hm : m = 0
    · subst m
      simp [e]
    let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
    have he (t : ℝ) : e ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
      unfold e c
      congr 1
      push_cast
      ring
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero (by exact_mod_cast hm)
        (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
    simp_rw [he]
    rw [integral_exp_mul_complex hc]
    simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]

  have zero_from_pairs (w : ℕ → ℝ) (n Y : ℕ) (hn : ∀ k j : ℕ, k+j=n → w k*w j=0) :
      (∫ t in (0 : ℝ)..1, (∑ k ∈ Finset.range (Y+1), (w k : ℂ)*e ((k : ℝ)*t))^2 * e (-(n:ℝ)*t)) = 0 := by
    let I := Finset.range (Y+1)
    let term := fun (k j : ℕ) (t : ℝ) =>
      ((w k : ℂ) * (w j : ℂ)) * e (((((k : ℤ) + j - n) : ℤ) : ℝ) * t)
    have hcont (k j : ℕ) : Continuous (term k j) := by dsimp [term, e]; fun_prop
    have hpoint (t : ℝ) : (∑ k ∈ I, (w k : ℂ) * e ((k : ℝ) * t)) ^ 2 * e (-(n : ℝ) * t) =
        ∑ k ∈ I, ∑ j ∈ I, term k j t := by
      simp only [sq, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
      dsimp [term]
      push_cast
      rw [show ((k : ℝ) + j - n) * t = ((k : ℝ) * t + j * t) + -(n : ℝ) * t by ring,
        phase_add, phase_add]
      ring
    change (∫ t in (0:ℝ)..1, (∑ k ∈ I, (w k : ℂ) * e ((k : ℝ) * t))^2 * e (-(n:ℝ)*t)) = _
    simp_rw [hpoint]
    rw [intervalIntegral.integral_finsetSum (fun k _ =>
      (continuous_finsetSum I (fun j _ => hcont k j)).intervalIntegrable _ _)]
    apply Finset.sum_eq_zero
    intro k _
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont k j).intervalIntegrable _ _)]
    apply Finset.sum_eq_zero
    intro j _
    simp only [term, intervalIntegral.integral_const_mul, fourier_mode]
    by_cases heq : (k : ℤ)+j-n = 0
    · have hz : w k*w j=0 := hn k j (by omega)
      simp only [heq, ite_true, mul_one]
      exact_mod_cast hz
    · simp [heq]

  have indicator_integral_split {f : ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s)
      {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
      intervalIntegral (s.indicator f) a b volume +
        intervalIntegral (sᶜ.indicator f) a b volume = intervalIntegral f a b volume := by
    have hi {u : Set ℝ} (hu : MeasurableSet u) :
        IntervalIntegrable (u.indicator f) volume a b :=
      ⟨hf.1.indicator hu, hf.2.indicator hu⟩
    rw [← intervalIntegral.integral_add (hi hs) (hi hs.compl)]
    apply congrArg (fun g : ℝ → ℂ => intervalIntegral g a b volume)
    funext t
    by_cases ht : t ∈ s <;> simp [ht]
  have zeroAtFailure (Y m : ℕ)
      (h : ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card = 0) :
      (∫ t in (0:ℝ)..1, F Y m t) = 0 := by
    let w (p : ℕ) : ℝ := if p.Prime then Real.log p else 0
    have hw (k j : ℕ) (hkj : k+j=m) : w k * w j = 0 := by
      by_cases hk : k.Prime
      · have hj : ¬ j.Prime := by
          intro hj
          have hm : k ∈ (Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p)) :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hk,by
              rwa [show m-k=j by omega]⟩
          simp [Finset.card_eq_zero.mp h] at hm
        simp [w, hj]
      · simp [w,hk]
    have hS (t : ℝ) :
        S Y t = ∑ k ∈ Finset.range (Y+1), (w k : ℂ) * e ((k : ℝ) * t) := by
      dsimp [S]
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl (fun k _ => by by_cases hk : k.Prime <;> simp [w,hk])
    have hh := zero_from_pairs w m Y hw
    change (∫ t in (0:ℝ)..1, (∑ k ∈ Finset.range (Y+1), (w k : ℂ) * e ((k : ℝ) * t))^2 *
      e (-(m:ℝ)*t)) = 0 at hh
    simpa only [F, hS] using hh
  have measurableArcs (P : ℕ → ℕ → Prop) (width : ℕ → ℝ) :
      MeasurableSet {t : ℝ | ∃ q a : ℕ, P q a ∧ |t-(a:ℝ)/q| ≤ width q} := by
    have he : {t : ℝ | ∃ q a : ℕ, P q a ∧ |t-(a:ℝ)/q| ≤ width q} =
        ⋃ q : ℕ, ⋃ a : ℕ, if P q a then {t : ℝ | |t-(a:ℝ)/q| ≤ width q} else ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, mem_iUnion]
      refine exists_congr (fun q => exists_congr (fun a => ?_))
      by_cases h : P q a <;> simp [h]
    rw [he]
    refine MeasurableSet.iUnion (fun q => MeasurableSet.iUnion (fun a => ?_))
    by_cases h : P q a
    · simpa only [ite_eq_left h] using (measurableSet_le
        (((continuous_id.sub continuous_const).abs).measurable)
        measurable_const : MeasurableSet {t : ℝ | |t-(a:ℝ)/q| ≤ width q})
    · simp [h]
  have hA (Y : ℕ) : MeasurableSet (A Y) := by
    simpa only [A, and_assoc] using measurableArcs (fun q a => 1 ≤ q ∧ (q : ℝ) < (Y : ℝ)^(1/4:ℝ) ∧
      q ≤ ⌊(Y:ℝ)^(1/3:ℝ)⌋₊ ∧ a ≤ q ∧ a.Coprime q)
      (fun q => ((256 * ⌊(Y:ℝ)^(1/3:ℝ)⌋₊ * (Nat.log 2 (Y+2))^2 : ℕ) : ℝ) / ((q:ℝ)*Y))
  have hB (Y : ℕ) : MeasurableSet (B Y) := by
    simpa only [B, and_assoc] using
      measurableArcs (fun q a => 1 ≤ q ∧ q ≤ Nat.log 2 (Y+2) ∧ a ≤ q ∧ a.Coprime q)
      (fun q => (((Nat.log 2 (Y+2))^3 : ℕ) : ℝ) / ((q:ℝ)*Y))
  have continuousF (Y m : ℕ) : Continuous (F Y m) := by
    dsimp [F, S, e]
    fun_prop
  have splitArcs (Y m : ℕ) (hBA : B Y ⊆ A Y) :
      C (B Y) Y m + C (A Y \ B Y) Y m + C (A Y)ᶜ Y m = (∫ t in (0:ℝ)..1, F Y m t) := by
    have hFI : IntervalIntegrable (F Y m) volume 0 1 := (continuousF Y m).intervalIntegrable _ _
    have hI (D : Set ℝ) (hD : MeasurableSet D) : IntervalIntegrable (D.indicator (F Y m)) volume 0 1 :=
      ⟨hFI.1.indicator hD, hFI.2.indicator hD⟩
    have hEq : C (B Y) Y m + C (A Y \ B Y) Y m = C (A Y) Y m := by
      dsimp only [C]
      rw [← intervalIntegral.integral_add (hI _ (hB Y)) (hI _ ((hA Y).diff (hB Y)))]
      apply intervalIntegral.integral_congr
      intro t _
      by_cases ht : t ∈ B Y
      · simp [ht, hBA ht]
      · by_cases ha : t ∈ A Y
        · simp [ht, ha]
        · simp [ht, ha]
    rw [hEq]
    exact indicator_integral_split (hA Y) hFI
  have hLog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : Filter.Tendsto (fun n : ℕ => (n:ℝ)) Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hb := (isLittleO_log_rpow_atTop (by norm_num : 0 < (1/4:ℝ))).bound
    (show 0 < Real.log 2 / 4 by positivity)
  obtain ⟨NG, hNG⟩ := Filter.eventually_atTop.mp (ht.eventually hb)
  have coreSubset (Y : ℕ) (hY : max 2 NG ≤ Y) : B Y ⊆ A Y := by
    have hy : (1:ℝ) ≤ Y := by exact_mod_cast (show 1 ≤ Y by omega)
    have hyp : 0 < (Y:ℝ) := zero_lt_one.trans_le hy
    have hg := hNG Y (by omega)
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hy),
      abs_of_nonneg (Real.rpow_nonneg hyp.le _)] at hg
    have hLog : Real.log ((Y:ℝ)+2) ≤ 2 * Real.log Y := by
      calc
        _ ≤ Real.log ((Y:ℝ)^2) := Real.log_le_log (by positivity) (by
          have hy2 : (2:ℝ) ≤ Y := by exact_mod_cast (show 2 ≤ Y by omega)
          nlinarith only [mul_nonneg (sub_nonneg.mpr hy2) (show 0 ≤ (Y:ℝ)+1 by positivity)])
        _ = _ := by rw [Real.log_pow]; norm_num
    let L := Nat.log 2 (Y+2)
    have hL : (L:ℝ) ≤ (Y:ℝ)^(1/4:ℝ)/2 := by
      apply (le_trans (Real.natLog_le_logb (Y+2) 2))
      unfold Real.logb
      rw [Nat.cast_add, Nat.cast_ofNat]
      apply (div_le_iff₀ hLog2).mpr
      linarith only [hLog, hg]
    have hLlt : (L:ℝ) < (Y:ℝ)^(1/4:ℝ) := by
      linarith [Real.rpow_pos_of_pos hyp (1/4:ℝ)]
    have hLQ : L ≤ ⌊(Y:ℝ)^(1/3:ℝ)⌋₊ := Nat.le_floor
      (hLlt.le.trans (Real.rpow_le_rpow_of_exponent_le hy (by norm_num)))
    have hWidth : L^3 ≤ (256*⌊(Y:ℝ)^(1/3:ℝ)⌋₊)*L^2 := by
      rw [show L^3 = L*L^2 by ring]
      exact Nat.mul_le_mul_right (L^2) (by omega)
    intro t ht'
    obtain ⟨q,a,hq,hqL,ha,hcop,hw⟩ := ht'
    refine ⟨q,a,hq,(Nat.cast_le.mpr hqL).trans_lt hLlt,hqL.trans hLQ,ha,hcop, hw.trans ?_⟩
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hWidth
  let D (Y : ℕ) := (Finset.Icc Y (2*Y)).filter (fun m => (C (A Y)ᶜ Y m).re ≤ -(Y:ℝ)/32)
  let J (Y : ℕ) := (Finset.Icc Y (2*Y)).filter (fun m => Even m ∧ 2*m ≤ 3*Y ∧
    4*Y ≤ 3*m ∧ (C (A Y \ B Y) Y m).re ≤ -(Y:ℝ)/32)
  obtain ⟨NB, hNB⟩ := hCore
  obtain ⟨KD, hKD, ND, hND⟩ := hComp
  obtain ⟨KJ, hKJ, NJ, hNJ⟩ := hMiddle
  let N := max (max 2 NG) (max NB (max ND NJ))
  let K : ℝ := 256*(KD+KJ)*(4:ℝ)^(79/100:ℝ)
  have hK : 0 < K := by dsimp [K]; positivity
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : 0 < (1/100:ℝ))).bound
    (show 0 < Real.log 2 / K by positivity)
  obtain ⟨NL,hNL⟩ := Filter.eventually_atTop.mp (ht.eventually hlog)
  intro G
  refine ⟨max (max 128 (128*N)) NL, ?_⟩
  intro X hX L E
  have h128 : 128 ≤ X := by omega
  let s := X/64
  have hs : 0 < s := by dsimp [s]; omega
  have hXs : X ≤ 128*s := by dsimp [s]; omega
  have hXs' : 64*s ≤ X := by dsimp [s]; omega
  have hsN : N ≤ s := by dsimp [s]; omega
  have hX1 : (1:ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hXp : 0 < (X:ℝ) := zero_lt_one.trans_le hX1
  let U := (Finset.Icc 1 256).biUnion (fun k => D (k*s) ∪ J (k*s))
  have hU : (U.card:ℝ) ≤ K * (X:ℝ)^(79/100:ℝ) := by
    have hmono (Y : ℕ) (hY : Y ≤ 4*X) :
        (Y:ℝ)^(79/100:ℝ) ≤ (4*(X:ℝ))^(79/100:ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hY) (by norm_num)
    have hEach (k : ℕ) (hk : k ∈ Finset.Icc 1 256) :
        ((D (k*s) ∪ J (k*s)).card:ℝ) ≤ (KD+KJ)*(4*(X:ℝ))^(79/100:ℝ) := by
      obtain ⟨hk1,hk256⟩ := Finset.mem_Icc.mp hk
      have hYs : s ≤ k*s := by simpa using Nat.mul_le_mul_right s hk1
      have hYN : N ≤ k*s := hsN.trans hYs
      have hY4 : k*s ≤ 4*X := (Nat.mul_le_mul_right s hk256).trans (by omega)
      have hY1 : (1:ℝ) ≤ (k*s:ℕ) := by exact_mod_cast (show 1 ≤ k*s by omega)
      have hd : ((D (k*s)).card:ℝ) ≤ KD*((k*s:ℕ):ℝ)^(19/25:ℝ) := hND _ (by
        exact (le_max_left ND NJ).trans ((le_max_right NB _).trans ((le_max_right _ _).trans hYN)))
      have hj : ((J (k*s)).card:ℝ) ≤ KJ*((k*s:ℕ):ℝ)^(79/100:ℝ) := hNJ _ (by
        exact (le_max_right ND NJ).trans ((le_max_right NB _).trans ((le_max_right _ _).trans hYN)))
      have hd' := (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num : (19/25:ℝ) ≤ 79/100)).trans
        (hmono (k*s) hY4)
      calc
        _ ≤ ((D (k*s)).card:ℝ) + ((J (k*s)).card:ℝ) := by
          exact_mod_cast Finset.card_union_le _ _
        _ ≤ KD*(4*(X:ℝ))^(79/100:ℝ) + KJ*(4*(X:ℝ))^(79/100:ℝ) :=
          (add_le_add (hd.trans (mul_le_mul_of_nonneg_left hd' hKD.le))
            (hj.trans (mul_le_mul_of_nonneg_left (hmono _ hY4) hKJ.le)))
        _ = _ := (add_mul ..).symm
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 256, ((D (k*s) ∪ J (k*s)).card:ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := Finset.Icc 1 256) (t := fun k => D (k*s) ∪ J (k*s)))
      _ ≤ ∑ _k ∈ Finset.Icc 1 256, (KD+KJ)*(4*(X:ℝ))^(79/100:ℝ) := Finset.sum_le_sum hEach
      _ = _ := by
        rw [Finset.sum_const, Nat.card_Icc]
        norm_num only [Nat.reduceSub, Nat.reduceAdd, nsmul_eq_mul]
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hXp.le]
        dsimp [K]
        ring
  let exps := Finset.Icc 1 L
  have hCover : E ⊆ (U ×ˢ exps).image (fun me : ℕ × ℕ => me.1+2^me.2) := by
    intro n hn
    change n ∈ (Finset.Ico X (2*X)).filter (fun j => Even j ∧
      0 < ((Finset.Icc 1 L).filter (fun a => G (j-2^a)=0)).card) at hn
    obtain ⟨hnI, heven, hExists⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnlow,hnhigh⟩ := Finset.mem_Ico.mp hnI
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hExists
    obtain ⟨haL, haFail⟩ := Finset.mem_filter.mp ha
    have hal := (Finset.mem_Icc.mp haL).1
    have hau := (Finset.mem_Icc.mp haL).2
    have hlog4 : 2 ≤ Nat.log 2 X := Nat.le_log_of_pow_le (by decide) (by omega)
    have hshift : 2 ^ a * 2 ≤ X := by
      rw [← pow_succ]
      apply (Nat.le_log_iff_pow_le (by decide) (by omega)).mp
      dsimp only [L] at hau
      omega
    let m := n-2^a
    have hmrange : X/2 ≤ m ∧ m ≤ 2*X := by dsimp [m]; omega
    have hme : Even m := by
      have he : Even (2^a : ℕ) := Nat.even_pow.mpr ⟨by decide, by omega⟩
      exact (Nat.even_sub (by omega)).mpr ⟨fun _ => he, fun _ => heven⟩
    let z := (2*m+2)/3
    let k := (z+s-1)/s
    let Y := k*s
    have hCeil : z ≤ Y := by
      have hr := Nat.mod_lt (z+s-1) hs
      have he := Nat.mod_add_div (z+s-1) s
      rw [Nat.mul_comm s] at he
      dsimp only [Y,k]
      omega
    have hFloor : Y ≤ z+s-1 := Nat.div_mul_le_self _ _
    have hyShape : 2*m ≤ 3*Y ∧ 4*Y ≤ 3*m := by
      dsimp only [z] at hCeil hFloor
      omega
    have hyI : m ∈ Finset.Icc Y (2*Y) := Finset.mem_Icc.mpr (by omega)
    have hy0 : 0 < Y := by dsimp only [z] at hCeil; omega
    have hk1 : 1 ≤ k := by
      apply Nat.pos_of_ne_zero
      intro hk0
      simp [Y,hk0] at hy0
    have hk256 : k ≤ 256 := by
      by_contra! h
      have hbig : 256*s ≤ Y := Nat.mul_le_mul_right s (by omega : 256 ≤ k)
      omega
    have hyN : N ≤ Y := hsN.trans (by simpa [Y] using Nat.mul_le_mul_right s hk1)
    have hgeom : max 2 NG ≤ Y := (le_max_left _ _).trans hyN
    have hNB' : NB ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hyN)
    have hfull : C (B Y) Y m + C (A Y \ B Y) Y m + C (A Y)ᶜ Y m = 0 :=
      (splitArcs Y m (coreSubset Y hgeom)).trans (zeroAtFailure Y m haFail)
    have hmU : m ∈ U := by
      refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk1,hk256⟩, ?_⟩
      apply Finset.mem_union.mpr
      by_cases hD : (C (A Y)ᶜ Y m).re ≤ -(Y:ℝ)/32
      · exact Or.inl (Finset.mem_filter.mpr ⟨hyI, hD⟩)
      · have hCoreY : 7*(Y:ℝ)/64 ≤ (C (B Y) Y m).re :=
          hNB Y hNB' m hyShape.1 hyShape.2 hme
        have hRe := congrArg Complex.re hfull
        simp only [Complex.add_re, Complex.zero_re] at hRe
        have hyR : 0 < (Y:ℝ) := by exact_mod_cast hy0
        exact Or.inr (Finset.mem_filter.mpr ⟨hyI, hme, hyShape.1, hyShape.2, by linarith⟩)
    exact Finset.mem_image.mpr ⟨(m,a), Finset.mem_product.mpr ⟨hmU,haL⟩, by dsimp [m]; omega⟩
  have hE : (E.card:ℝ) ≤ (X:ℝ)^(4/5:ℝ) := by
    have hlogX := hNL X (by omega)
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hX1),
      abs_of_nonneg (Real.rpow_nonneg hXp.le _)] at hlogX
    have hL : (L:ℝ) ≤ (X:ℝ)^(1/100:ℝ)/K := by
      calc
        _ ≤ Real.log X / Real.log 2 :=
          (Nat.cast_le.mpr (Nat.div_le_self ..)).trans (by simpa [Real.logb] using Real.natLog_le_logb X 2)
        _ ≤ _ := by
          apply (div_le_div_iff₀ hLog2 hK).mpr
          calc
            _ ≤ (Real.log 2/K*(X:ℝ)^(1/100:ℝ))*K := mul_le_mul_of_nonneg_right hlogX hK.le
            _ = _ := by field_simp [hK.ne'] <;> ring
    have hExps : (exps.card:ℝ) ≤ (L:ℝ) := by
      exact_mod_cast (show exps.card ≤ L by dsimp [exps]; rw [Nat.card_Icc]; omega)
    calc
      _ ≤ (U.card:ℝ) * exps.card := by
        exact_mod_cast (show E.card ≤ U.card * exps.card from
          (Finset.card_le_card hCover).trans (Finset.card_image_le.trans_eq (Finset.card_product U exps)))
      _ ≤ (K*(X:ℝ)^(79/100:ℝ))*((X:ℝ)^(1/100:ℝ)/K) :=
        mul_le_mul hU (hExps.trans hL) (Nat.cast_nonneg _) (by positivity)
      _ = _ := by
        rw [show K*(X:ℝ)^(79/100:ℝ)*((X:ℝ)^(1/100:ℝ)/K) =
          (X:ℝ)^(79/100:ℝ)*(X:ℝ)^(1/100:ℝ) by field_simp [hK.ne'] <;> ring,
          ← Real.rpow_add hXp]
        norm_num
  have hPow := pow_le_pow_left₀ (Nat.cast_nonneg E.card) hE 5
  rw [← Real.rpow_mul_natCast hXp.le, show (4/5:ℝ)*↑(5:ℕ)=4 by norm_num, Real.rpow_ofNat] at hPow
  exact_mod_cast hPow
