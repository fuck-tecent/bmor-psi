import Mathlib

open Finset
open scoped BigOperators

namespace GoldbachNearShift

private theorem primePower_factorial_dvd_AP (a d m p : ℕ) (hp : p.Prime) (hd : ¬ p ∣ d) :
    p ^ m.factorial.factorization p ∣ ∏ i ∈ range m, (a + d * i) := by
  let M := p ^ m.factorial.factorization p
  let _ : NeZero M := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcop : d.Coprime M := (hp.coprime_iff_not_dvd.mpr hd).symm.pow_right _
  let u : (ZMod M)ˣ := ZMod.unitOfCoprime d hcop
  let c : ZMod M := (↑u⁻¹ : ZMod M) * (a : ZMod M)
  let b := c.val
  have hbc : (b : ZMod M) = c := ZMod.natCast_zmod_val _
  have hud : (↑u : ZMod M) = (d : ZMod M) := ZMod.coe_unitOfCoprime d hcop
  have hdb : (d : ZMod M) * (b : ZMod M) = (a : ZMod M) := by
    rw [hbc, ← hud]
    simp [c, ← mul_assoc]
  have hfac : M ∣ m.factorial :=
    (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero m)).mpr le_rfl
  have hcon : M ∣ ∏ i ∈ range m, (b + i) := by
    rw [← Nat.ascFactorial_eq_prod_range]
    exact hfac.trans (Nat.factorial_dvd_ascFactorial b m)
  have hzero := (ZMod.natCast_eq_zero_iff _ M).mpr hcon
  push_cast at hzero
  apply (ZMod.natCast_eq_zero_iff _ M).mp
  push_cast
  have hterm (i : ℕ) :
      (a : ZMod M) + (d : ZMod M) * (i : ZMod M) =
        (d : ZMod M) * ((b : ZMod M) + (i : ZMod M)) := by rw [mul_add, hdb]
  simp_rw [hterm, Finset.prod_mul_distrib, hzero, mul_zero]

private theorem factorial_dvd_scaled_AP (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) :
    m.factorial ∣ d ^ m * ∏ i ∈ range m, (a + d * i) := by
  let P := ∏ i ∈ range m, (a + d * i)
  have hP : P ≠ 0 := Nat.ne_of_gt (Finset.prod_pos fun i _ ↦ by positivity)
  have hdM : d ^ m ≠ 0 := pow_ne_zero _ hd.ne'
  apply (Nat.factorization_prime_le_iff_dvd (Nat.factorial_ne_zero m) (mul_ne_zero hdM hP)).mp
  intro p hp
  rw [Nat.factorization_mul hdM hP, Finsupp.add_apply]
  by_cases hpd : p ∣ d
  · have hdp : 1 ≤ d.factorization p := (hp.dvd_iff_one_le_factorization hd.ne').mp hpd
    have hmp : m.factorial.factorization p ≤ m :=
      (Nat.factorization_factorial_le_div_pred hp m).trans (Nat.div_le_self _ _)
    have hmulp : m ≤ m * d.factorization p := by
      simpa only [mul_one] using Nat.mul_le_mul_left m hdp
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact hmp.trans (hmulp.trans (Nat.le_add_right _ _))
  · have h := (hp.pow_dvd_iff_le_factorization hP).mp (primePower_factorial_dvd_AP a d m p hp hpd)
    exact h.trans (Nat.le_add_left _ _)

private theorem primeProduct_factorial_dvd_scaled_AP (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) :
    m.factorial * (∏ i ∈ (range m).filter (fun i ↦ m < a + d * i ∧ (a + d * i).Prime),
      (a + d * i)) ∣ d ^ m * ∏ i ∈ range m, (a + d * i) := by
  let B := (range m).filter (fun i ↦ m < a + d * i ∧ (a + d * i).Prime)
  have hc : m.factorial.Coprime (∏ i ∈ B, (a + d * i)) := by
    apply Nat.Coprime.prod_right
    intro i hi
    obtain ⟨hbig, hp⟩ := (mem_filter.mp hi).2
    exact (hp.coprime_factorial_of_lt hbig).symm
  have hdiv : (∏ i ∈ B, (a + d * i)) ∣ ∏ i ∈ range m, (a + d * i) :=
    Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  exact hc.mul_dvd_of_dvd_of_dvd (factorial_dvd_scaled_AP a d m ha hd)
    (dvd_mul_of_dvd_right hdiv _)

/-- Prime logarithmic weight on a positive arithmetic progression. -/
theorem primeProgressionWeight_le (a d m n : ℕ)
    (ha : 0 < a) (hd : 0 < d) (hn : ∀ i < m, a + d * i ≤ n) :
    (∑ i ∈ range m, if (a + d * i).Prime then Real.log (a + d * i : ℕ) else 0) ≤
      (m : ℝ) * (Real.log 4 + 1 + Real.log ((n : ℝ) / (m : ℝ)) + Real.log d) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  classical
  let f (i : ℕ) := a + d * i
  let S := (range m).filter (fun i ↦ (f i).Prime)
  let B := (range m).filter (fun i ↦ m < f i ∧ (f i).Prime)
  let A := S.filter (fun i ↦ ¬ m < f i)
  let P := ∏ i ∈ range m, f i
  let BP := ∏ i ∈ B, f i
  have hfpos (i : ℕ) : 0 < f i := by dsimp [f]; positivity
  have hPpos : 0 < P := Finset.prod_pos (fun i _ ↦ hfpos i)
  have hBPpos : 0 < BP := Finset.prod_pos (fun i _ ↦ hfpos i)
  have hmd : 0 < (m : ℝ) := Nat.cast_pos.mpr hm.bot_lt
  have hnd : 0 < (n : ℝ) := by
    exact Nat.cast_pos.mpr (ha.trans_le (by simpa using hn 0 hm.bot_lt))
  have hdd : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hfinj : Function.Injective f := by
    intro i j h
    dsimp [f] at h
    exact Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel h)
  have hsub : A.image f ⊆ Nat.primesLE m := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    rw [Nat.primesLE_eq_filter_Icc_zero]
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _, le_of_not_gt (mem_filter.mp hi).2⟩,
      (mem_filter.mp (mem_filter.mp hi).1).2⟩
  have hsmall : (∑ i ∈ A, Real.log (f i)) ≤ Real.log 4 * (m : ℝ) := by
    calc
      _ = ∑ p ∈ A.image f, Real.log (p : ℝ) := (Finset.sum_image hfinj.injOn).symm
      _ ≤ ∑ p ∈ Nat.primesLE m, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p hp _
        rw [Nat.primesLE_eq_filter_Icc_zero] at hp
        exact Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_lt.le)
      _ = Chebyshev.theta (m : ℝ) := (Chebyshev.theta_eq_sum_primesLE_log m).symm
      _ ≤ _ := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg m)
  have hdvd : m.factorial * BP ∣ d ^ m * P :=
    primeProduct_factorial_dvd_scaled_AP a d m ha hd
  have hle : (m.factorial : ℝ) * (BP : ℝ) ≤ (d : ℝ)^m * (P : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (pow_pos hd _) hPpos) hdvd
  have hlog := Real.log_le_log (by positivity : 0 < (m.factorial : ℝ) * (BP : ℝ)) hle
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow] at hlog
  have hlogP : Real.log (P : ℝ) = ∑ i ∈ range m, Real.log (f i) := by
    dsimp [P]
    rw [Nat.cast_prod, Real.log_prod (fun i _ ↦ (Nat.cast_pos.mpr (hfpos i) : (0:ℝ) < f i).ne')]
  have hlogBP : Real.log (BP : ℝ) = ∑ i ∈ B, Real.log (f i) := by
    dsimp [BP]
    rw [Nat.cast_prod, Real.log_prod (fun i _ ↦ (Nat.cast_pos.mpr (hfpos i) : (0:ℝ) < f i).ne')]
  have hlogP_le : Real.log (P : ℝ) ≤ (m : ℝ) * Real.log n := by
    rw [hlogP]
    calc
      _ ≤ ∑ _i ∈ range m, Real.log (n : ℝ) := by
        exact Finset.sum_le_sum (fun i hi ↦ Real.log_le_log
          (Nat.cast_pos.mpr (hfpos i)) (by exact_mod_cast hn i (mem_range.mp hi)))
      _ = _ := by simp [nsmul_eq_mul]
  have hlogFactorial : (m : ℝ) * Real.log m - (m : ℝ) ≤ Real.log (m.factorial : ℝ) := by
    rw [← Real.sum_log_eq_log_factorial]
    exact Real.le_sum_log_nat m
  have hB : S.filter (fun i ↦ m < f i) = B := by
    ext i
    simp [S, B, and_left_comm, and_comm]
  have hsplit : (∑ i ∈ B, Real.log (f i)) + (∑ i ∈ A, Real.log (f i)) =
      ∑ i ∈ S, Real.log (f i) := by
    simpa only [hB, A] using sum_filter_add_sum_filter_not S (fun i ↦ m < f i)
      (fun i ↦ Real.log (f i))
  rw [hlogBP] at hlog
  change (∑ i ∈ range m, if (f i).Prime then Real.log (f i) else 0) ≤ _
  rw [← sum_filter, ← hsplit, Real.log_div hnd.ne' hmd.ne']
  linarith only [hlog, hlogP_le, hlogFactorial, hsmall]

noncomputable def primeLog (k : ℕ) : ℝ := if k.Prime then Real.log (k : ℝ) else 0

private theorem primeLog_nonneg (k : ℕ) : 0 ≤ primeLog k := by
  unfold primeLog
  split_ifs with h
  · exact Real.log_nonneg (Nat.one_le_cast.mpr h.one_lt.le)
  · exact le_rfl

private theorem progressScale_nonneg {n H Q : ℕ} (hH : 0 < H) (hHn : H ≤ n) (hQ : 0 < Q) :
    0 ≤ Real.log 4 + 1 + Real.log ((n : ℝ) / H) + 2 * Real.log Q := by
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  have hratio : 1 ≤ (n : ℝ) / H := (one_le_div hHr).2 (by exact_mod_cast hHn)
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hln := Real.log_nonneg hratio
  have hlQ := Real.log_nonneg hQ1
  positivity

/-- A clipped progression retains the upper bound for the full half-window. -/
theorem primeProgressionWindowScale_le (a d m n H Q : ℕ)
    (ha : 0 < a) (hd : 0 < d) (hdQ : d ≤ Q)
    (hH : 0 < H) (hHn : H ≤ n) (hmH : m * d ≤ H)
    (hn : ∀ i < m, a + d * i ≤ n) :
    (∑ i ∈ range m, primeLog (a + d * i)) ≤
      ((H : ℝ) / d) * (Real.log 4 + 1 + Real.log ((n : ℝ) / H) + 2 * Real.log Q) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hHR : 0 < (H : ℝ) := by exact_mod_cast hH
  have hHRn : (H : ℝ) ≤ n := by exact_mod_cast hHn
  have hnR : (0 : ℝ) < n := hHR.trans_le hHRn
  have hQ : 0 < Q := hd.trans_le hdQ
  have hln := Real.log_nonneg ((one_le_div hHR).2 hHRn)
  have hld := Real.log_nonneg (show (1 : ℝ) ≤ d by exact_mod_cast hd)
  have hlQ := Real.log_le_log hdR (show (d : ℝ) ≤ Q by exact_mod_cast hdQ)
  have hX : 0 < (H : ℝ) / d := div_pos hHR hdR
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [range_zero, sum_empty]
    exact mul_nonneg hX.le (progressScale_nonneg hH hHn hQ)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm.bot_lt
  have hmX : (m : ℝ) ≤ (H : ℝ) / d := by
    exact (le_div_iff₀ hdR).2 (by exact_mod_cast hmH)
  have hsplit : Real.log ((n : ℝ) / m) + Real.log d =
      Real.log ((n : ℝ) / H) + 2 * Real.log d + Real.log (((H : ℝ) / d) / m) := by
    rw [Real.log_div hnR.ne' hmR.ne', Real.log_div hnR.ne' hHR.ne',
      Real.log_div hX.ne' hmR.ne', Real.log_div hHR.ne' hdR.ne']
    ring
  have htail : (m : ℝ) * Real.log (((H : ℝ) / d) / m) ≤ (H : ℝ) / d - m := by
    have hh := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hX hmR)) hmR.le
    convert hh using 1
    field_simp
  let B : ℝ := Real.log 4 + 1 + Real.log ((n : ℝ) / H) + 2 * Real.log d
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith only [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4), hln, hld]
  calc
    _ ≤ (m : ℝ) * (Real.log 4 + 1 + Real.log ((n : ℝ) / m) + Real.log d) :=
      primeProgressionWeight_le a d m n ha hd hn
    _ = (m : ℝ) * B + (m : ℝ) * Real.log (((H : ℝ) / d) / m) := by
      rw [add_assoc (Real.log 4 + 1), hsplit]
      dsimp [B]
      ring
    _ ≤ (m : ℝ) * B + ((H : ℝ) / d - m) := add_le_add (le_refl _) htail
    _ ≤ ((H : ℝ) / d) * B := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hmX) (sub_nonneg.mpr hB)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [B]; linarith only [hlQ]) hX.le

private theorem sum_primeLog_subset_AP {S : Finset ℕ} {a d m : ℕ} (hd : 0 < d)
    (hsub : S ⊆ (range m).image (fun i ↦ a + d * i)) :
    (∑ r ∈ S, primeLog r) ≤ ∑ i ∈ range m, primeLog (a + d * i) := by
  have hinj : Function.Injective (fun i : ℕ ↦ a + d * i) := fun _ _ hie ↦
    Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel hie)
  rw [← Finset.sum_image hinj.injOn]
  exact sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ ↦ primeLog_nonneg r)

theorem aboveCenterWeight_le (n c d H Q : ℕ) (hc : c ≤ n) (hd : 0 < d) (hdQ : d ≤ Q)
    (hH : 0 < H) (hHn : H ≤ n) :
    (∑ r ∈ (range (n + 1)).filter (fun r ↦ c < r ∧ r - c ≤ H ∧ d ∣ r - c), primeLog r) ≤
      ((H : ℝ) / d) * (Real.log 4 + 1 + Real.log ((n : ℝ) / H) + 2 * Real.log Q) := by
  classical
  let m := min (H / d) ((n - c) / d)
  have hmH : m * d ≤ H := (Nat.le_div_iff_mul_le hd).mp (min_le_left _ _)
  have hmN : m * d ≤ n - c := (Nat.le_div_iff_mul_le hd).mp (min_le_right _ _)
  have hsub : (range (n + 1)).filter (fun r ↦ c < r ∧ r - c ≤ H ∧ d ∣ r - c) ⊆
      (range m).image (fun i ↦ c + d + d * i) := by
    intro r hr
    obtain ⟨hrn, hcr, hrH, j, hj⟩ := mem_filter.mp hr
    have hrn' : r ≤ n := Nat.le_of_lt_succ (mem_range.mp hrn)
    have hJpos : 0 < j := by
      by_contra! hJ
      have hJ0 : j = 0 := by omega
      rw [hJ0, mul_zero] at hj
      omega
    have hjH : j ≤ H / d := (Nat.le_div_iff_mul_le hd).2 (by rw [Nat.mul_comm j d]; omega : j*d ≤ H)
    have hjN : j ≤ (n - c) / d := (Nat.le_div_iff_mul_le hd).2 (by rw [Nat.mul_comm j d]; omega : j*d ≤ n - c)
    have hjm : j ≤ m := le_min hjH hjN
    refine mem_image.mpr ⟨j - 1, mem_range.mpr (by omega), ?_⟩
    have he : d * j = d * (j - 1) + d := by
      conv_lhs => rw [show j = (j - 1) + 1 by omega, Nat.mul_add, mul_one]
    omega
  refine (sum_primeLog_subset_AP hd hsub).trans
    (primeProgressionWindowScale_le (c + d) d m n H Q (by positivity) hd hdQ hH hHn hmH ?_)
  intro i hi
  have ht : (i + 1) * d ≤ m * d := Nat.mul_le_mul_right d (Nat.succ_le_of_lt hi)
  rw [Nat.add_mul, one_mul, Nat.mul_comm i d] at ht
  omega

theorem belowCenterWeight_le (n c d H Q : ℕ) (hc : c ≤ n) (hd : 0 < d) (hdQ : d ≤ Q)
    (hH : 0 < H) (hHn : H ≤ n) :
    (∑ r ∈ (range (n + 1)).filter (fun r ↦ 0 < r ∧ r < c ∧ c - r ≤ H ∧ d ∣ c - r), primeLog r) ≤
      ((H : ℝ) / d) * (Real.log 4 + 1 + Real.log ((n : ℝ) / H) + 2 * Real.log Q) := by
  classical
  let m := min (H / d) ((c - 1) / d)
  let a := max 1 (c - m * d)
  have hmH : m * d ≤ H := (Nat.le_div_iff_mul_le hd).mp (min_le_left _ _)
  have hmC : m * d ≤ c - 1 := (Nat.le_div_iff_mul_le hd).mp (min_le_right _ _)
  have hae (hc0 : 0 < c) : a = c - m*d := max_eq_right (by omega)
  have hsub : (range (n + 1)).filter
      (fun r ↦ 0 < r ∧ r < c ∧ c - r ≤ H ∧ d ∣ c - r) ⊆
      (range m).image (fun i ↦ a + d * i) := by
    intro r hr
    obtain ⟨_, hrp, hrc, hrH, j, hj⟩ := mem_filter.mp hr
    have hjpos : 0 < j := by
      by_contra! hJ
      have hJ0 : j = 0 := by omega
      rw [hJ0, mul_zero] at hj
      omega
    have hjH : j ≤ H / d := (Nat.le_div_iff_mul_le hd).2 (by rw [Nat.mul_comm j d]; omega : j*d ≤ H)
    have hjC : j ≤ (c - 1) / d := (Nat.le_div_iff_mul_le hd).2 (by rw [Nat.mul_comm j d]; omega : j*d ≤ c - 1)
    have hjm : j ≤ m := le_min hjH hjC
    refine mem_image.mpr ⟨m - j, mem_range.mpr (by omega), ?_⟩
    rw [hae (by omega)]
    have he : d * j + d * (m - j) = m * d := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hjm, Nat.mul_comm d m]
    omega
  have ha : 0 < a := (Nat.zero_lt_succ 0).trans_le (le_max_left _ _)
  refine (sum_primeLog_subset_AP hd hsub).trans
    (primeProgressionWindowScale_le a d m n H Q ha hd hdQ hH hHn hmH ?_)
  intro i hi
  have hmpos : 0 < m := Nat.zero_le i |>.trans_lt hi
  have hmDp : 0 < m * d := Nat.mul_pos hmpos hd
  have hcab : 0 < c := by omega
  rw [hae hcab]
  have hiD : i * d ≤ m * d := Nat.mul_le_mul_right d hi.le
  rw [Nat.mul_comm d i]
  omega

theorem nearCenterWeight_le (n c d H Q : ℕ) (hc : c ≤ n) (hd : 0 < d) (hdQ : d ≤ Q)
    (hH : 0 < H) (hHn : H ≤ n) :
    (∑ r ∈ (range (n + 1)).filter
      (fun (r : ℕ) ↦ (r : ℤ) - c ≠ 0 ∧ |(r : ℤ) - c| ≤ (H : ℤ) ∧ (d : ℤ) ∣ (r : ℤ) - c),
      primeLog r) ≤
      (2 * (H : ℝ) / d) * (Real.log 4 + 1 + Real.log ((n : ℝ) / H) + 2 * Real.log Q) := by
  classical
  let left (r : ℕ) : Prop := 0 < r ∧ r < c ∧ c - r ≤ H ∧ d ∣ c - r
  let right (r : ℕ) : Prop := c < r ∧ r - c ≤ H ∧ d ∣ r - c
  let near (r : ℕ) : Prop :=
    (r : ℤ) - c ≠ 0 ∧ |(r : ℤ) - c| ≤ (H : ℤ) ∧ (d : ℤ) ∣ (r : ℤ) - c
  change (∑ r ∈ (range (n+1)).filter near, primeLog r) ≤ _
  have hpoint (r : ℕ) :
      (if near r then primeLog r else 0) ≤
      (if left r then primeLog r else 0) + (if right r then primeLog r else 0) := by
    by_cases hrN : near r
    · rw [ite_eq_left hrN]
      rcases eq_or_ne r 0 with rfl | hr0
      · simp [primeLog]
      obtain ⟨hne, habs, hdvd⟩ := hrN
      have hrc : r ≠ c := by
        intro he
        exact hne (by simp [he])
      rcases lt_or_gt_of_ne hrc with hlt | hgt
      · have hltZ : (r : ℤ) < c := by exact_mod_cast hlt
        have hl : left r := by
          refine ⟨hr0.bot_lt, hlt, ?_, ?_⟩
          · rw [abs_of_neg (sub_neg.mpr hltZ), neg_sub, ← Nat.cast_sub hlt.le] at habs
            exact_mod_cast habs
          · have hneg := dvd_neg.mpr hdvd
            rw [neg_sub, ← Nat.cast_sub hlt.le] at hneg
            exact_mod_cast hneg
        rw [ite_eq_left hl]
        exact le_add_of_nonneg_right (by split_ifs <;> first | exact primeLog_nonneg _ | exact le_rfl)
      · have hgtZ : (c : ℤ) < r := by exact_mod_cast hgt
        have hr : right r := by
          refine ⟨hgt, ?_, ?_⟩
          · rw [abs_of_pos (sub_pos.mpr hgtZ), ← Nat.cast_sub hgt.le] at habs
            exact_mod_cast habs
          · rw [← Nat.cast_sub hgt.le] at hdvd
            exact_mod_cast hdvd
        rw [ite_eq_left hr]
        exact le_add_of_nonneg_left (by split_ifs <;> first | exact primeLog_nonneg _ | exact le_rfl)
    · rw [ite_eq_right hrN]
      exact add_nonneg (by split_ifs <;> first | exact primeLog_nonneg _ | exact le_rfl)
        (by split_ifs <;> first | exact primeLog_nonneg _ | exact le_rfl)
  calc
    _ ≤ (∑ r ∈ (range (n+1)).filter left, primeLog r) +
        (∑ r ∈ (range (n+1)).filter right, primeLog r) := by
      simp_rw [Finset.sum_filter]
      rw [← sum_add_distrib]
      exact Finset.sum_le_sum (fun r _ ↦ hpoint r)
    _ ≤ ((H : ℝ) / d) * (Real.log 4 + 1 + Real.log ((n : ℝ) / H) + 2 * Real.log Q) +
        ((H : ℝ) / d) * (Real.log 4 + 1 + Real.log ((n : ℝ) / H) + 2 * Real.log Q) := by
      exact add_le_add (belowCenterWeight_le n c d H Q hc hd hdQ hH hHn)
        (aboveCenterWeight_le n c d H Q hc hd hdQ hH hHn)
    _ = _ := by ring

private theorem harmonic_log (N : ℕ) :
    (∑ k ∈ Icc 1 N, 1 / (k : ℝ)) ≤ 1 + Real.log N := by
  induction N with
  | zero => simp
  | succ n ih =>
    by_cases h : n = 0
    · subst n
      simp
    · have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
      have hnext : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hset : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
        ext k
        simp only [mem_Icc, mem_insert]
        omega
      rw [hset, Finset.sum_insert (by simp)]
      push_cast
      have heq : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
        field_simp
        ring
      have hlog := Real.log_le_sub_one_of_pos (div_pos hpos hnext)
      rw [Real.log_div hpos.ne' hnext.ne', heq] at hlog
      linarith only [hlog, ih]

private theorem harmonic_multiples (N d : ℕ) (hd : 0 < d) :
    (∑ q ∈ (Icc 1 N).filter (fun q => d ∣ q), 1 / (q : ℝ)) ≤
      (1 / (d : ℝ)) * (1 + Real.log N) := by
  classical
  let A := (Icc 1 N).filter (fun q => d ∣ q)
  have hmul {q : ℕ} (hq : q ∈ A) : q / d * d = q :=
    Nat.div_mul_cancel (mem_filter.mp hq).2
  have hinj : Set.InjOn (fun q : ℕ => q / d) ↑A := by
    intro q hq r hr he
    change q ∈ A at hq
    change r ∈ A at hr
    calc q = q / d * d := (hmul hq).symm
      _ = r / d * d := congrArg (fun k : ℕ => k * d) he
      _ = r := hmul hr
  have hsub : A.image (fun q => q / d) ⊆ Icc 1 N := by
    intro k hk
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hk
    have hq' := mem_Icc.mp (mem_filter.mp hq).1
    refine mem_Icc.mpr ⟨?_, (Nat.div_le_self q d).trans hq'.2⟩
    apply Nat.pos_of_ne_zero
    intro he
    have hm := hmul hq
    rw [he, zero_mul] at hm
    omega
  change (∑ q ∈ A, 1 / (q : ℝ)) ≤ _
  calc
    _ = ∑ k ∈ A.image (fun q => q / d), (1 / (d : ℝ)) * (1 / (k : ℝ)) := by
      rw [sum_image hinj]
      refine sum_congr rfl (fun q hq => ?_)
      have hR : ((q / d : ℕ) : ℝ) * (d : ℝ) = (q : ℝ) := by exact_mod_cast hmul hq
      rw [one_div_mul_one_div, mul_comm (d : ℝ), hR]
    _ ≤ ∑ k ∈ Icc 1 N, (1 / (d : ℝ)) * (1 / (k : ℝ)) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (harmonic_log N) (by positivity)

theorem divisor_reciprocal_le (Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Icc 1 Q, (q.divisors.card : ℝ) / q) ≤ (1 + Real.log Q) ^ 2 := by
  classical
  calc
    _ = ∑ q ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q, if l ∣ q then 1 / (q : ℝ) else 0 := by
      apply sum_congr rfl
      intro q hq
      obtain ⟨hq₁, hqQ⟩ := mem_Icc.mp hq
      have hqpos : 0 < q := hq₁
      have hs : (Icc 1 Q).filter (fun l ↦ l ∣ q) = q.divisors := by
        ext l
        constructor
        · intro hl
          exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hl).2, hqpos.ne'⟩
        · intro hl
          have hld := (Nat.mem_divisors.mp hl).1
          exact mem_filter.mpr ⟨mem_Icc.mpr
            ⟨Nat.pos_of_dvd_of_pos hld hqpos, (Nat.le_of_dvd hqpos hld).trans hqQ⟩, hld⟩
      rw [← sum_filter, hs, sum_const, nsmul_eq_mul, div_eq_mul_inv, one_div]
    _ = ∑ l ∈ Icc 1 Q, ∑ q ∈ (Icc 1 Q).filter (fun q ↦ l ∣ q), 1 / (q : ℝ) := by
      rw [sum_comm]
      simp_rw [sum_filter]
    _ ≤ ∑ l ∈ Icc 1 Q, (1 / (l : ℝ)) * (1 + Real.log Q) :=
      sum_le_sum (fun l hl ↦ harmonic_multiples Q l (mem_Icc.mp hl).1)
    _ = (∑ l ∈ Icc 1 Q, 1 / (l : ℝ)) * (1 + Real.log Q) := by rw [sum_mul]
    _ ≤ _ := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (harmonic_log Q)
        (by have hh := Real.log_nonneg (show (1:ℝ) ≤ Q by exact_mod_cast hQ); positivity)


end GoldbachNearShift


open Finset ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace GoldbachNearShift

noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  apply Complex.norm_exp_ofReal_mul_I

private theorem coprimeIndicator_moebius (a q : ℕ) (hq : 0 < q) :
    (if a.Coprime q then (1 : ℂ) else 0) =
      ∑ l ∈ q.divisors, if l ∣ a then (ArithmeticFunction.moebius l : ℂ) else 0 := by
  rw [← Finset.sum_filter]
  have hs : q.divisors.filter (fun l ↦ l ∣ a) = (a.gcd q).divisors := by
    have hg : a.gcd q ≠ 0 := (Nat.gcd_pos_of_pos_right a hq).ne'
    ext l
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    exact ⟨fun h ↦ ⟨⟨h.2, h.1.1⟩, hg⟩, fun h ↦ ⟨⟨h.1.2, hq.ne'⟩, h.1.1⟩⟩
  rw [hs]
  have h := congrArg (fun f : ArithmeticFunction ℂ ↦ f (a.gcd q))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h.symm

private theorem sum_cast_zmod {m : ℕ} [NeZero m] (f : ZMod m → ℂ) :
    (∑ b ∈ range m, f (b : ZMod m)) = ∑ b : ZMod m, f b := by
  rw [← Fin.sum_univ_eq_sum_range]
  let e : Fin m ≃ ZMod m :=
    { toFun := fun b ↦ ((b : ℕ) : ZMod m)
      invFun := fun a ↦ ⟨a.val, ZMod.val_lt a⟩
      left_inv := fun b ↦ Fin.ext (ZMod.val_natCast_of_lt b.isLt)
      right_inv := ZMod.natCast_zmod_val }
  exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)

private theorem character_sum (d : ℤ) (m : ℕ) (hm : 0 < m) :
    (∑ b ∈ range m, phase ((d : ℝ) * (b : ℝ) / m)) =
      if (m : ℤ) ∣ d then (m : ℂ) else 0 := by
  let _ : NeZero m := ⟨hm.ne'⟩
  have hterm (b : ℕ) :
      phase ((d : ℝ) * (b : ℝ) / m) =
        ZMod.stdAddChar ((d : ZMod m) * (b : ZMod m)) := by
    rw [show (d : ZMod m) * (b : ZMod m) = ((d * (b : ℤ) : ℤ) : ZMod m) by
      push_cast; rfl, ZMod.stdAddChar_coe]
    unfold phase
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  rw [sum_cast_zmod (fun b : ZMod m ↦ ZMod.stdAddChar ((d : ZMod m) * b))]
  by_cases hd : (m : ℤ) ∣ d
  · have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd d m).2 hd
    simp [hd, hz, ZMod.card]
  · have hz : (d : ZMod m) ≠ 0 := fun h ↦ hd ((ZMod.intCast_zmod_eq_zero_iff_dvd d m).1 h)
    rw [ite_eq_right hd]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar m hz)

private theorem sum_multiples_phase (q l : ℕ) (d : ℤ) (hl : 0 < l) (hld : l ∣ q) :
    (∑ a ∈ (range q).filter (fun a ↦ l ∣ a), phase ((d : ℝ) * (a : ℝ) / q)) =
      ∑ b ∈ range (q / l), phase ((d : ℝ) * (b : ℝ) / (q / l : ℕ)) := by
  obtain ⟨k, rfl⟩ := hld
  rw [Nat.mul_div_cancel_left _ hl]
  symm
  apply Finset.sum_bij (fun b _ ↦ l * b)
  · intro b hb
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hl),
      dvd_mul_right l b⟩
  · intro b hb c hc he
    exact Nat.eq_of_mul_eq_mul_left hl he
  · intro a ha
    obtain ⟨har, j, rfl⟩ := mem_filter.mp ha
    exact ⟨j, mem_range.mpr ((Nat.mul_lt_mul_left hl).1 (mem_range.mp har)), rfl⟩
  · intro b _
    congr 1
    push_cast
    have hlR : (l : ℝ) ≠ 0 := (Nat.cast_pos.mpr hl : 0 < (l : ℝ)).ne'
    by_cases hk : k = 0
    · simp [hk]
    · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      field_simp

theorem norm_ramanujan_le (q : ℕ) (d : ℤ) (hq : 0 < q) :
    ‖∑ a ∈ (range q).filter (fun a ↦ a.Coprime q), phase ((d : ℝ) * (a : ℝ) / q)‖ ≤
      ∑ l ∈ q.divisors, if ((q / l : ℕ) : ℤ) ∣ d then ((q/l : ℕ) : ℝ) else 0 := by
  classical
  let f (a : ℕ) := phase ((d : ℝ) * (a : ℝ) / q)
  have hsum : (∑ a ∈ (range q).filter (fun a ↦ a.Coprime q), f a) =
      ∑ l ∈ q.divisors, (ArithmeticFunction.moebius l : ℂ) *
        ∑ a ∈ (range q).filter (fun a ↦ l ∣ a), f a := by
    calc
      _ = ∑ a ∈ range q, (if a.Coprime q then (1:ℂ) else 0) * f a := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : a.Coprime q <;> simp [h]
      _ = ∑ a ∈ range q, (∑ l ∈ q.divisors, if l∣a then (ArithmeticFunction.moebius l : ℂ) else 0) *
          f a := by simp_rw [coprimeIndicator_moebius _ _ hq]
      _ = _ := by
        simp_rw [sum_mul]
        rw [sum_comm]
        apply sum_congr rfl
        intro l _
        rw [mul_sum, sum_filter]
        apply sum_congr rfl
        intro a _
        by_cases h : l ∣ a <;> simp [h]
  change ‖∑ a ∈ _, f a‖ ≤ _
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro l hl
  have hld := (Nat.mem_divisors.mp hl).1
  have hlpos := Nat.pos_of_dvd_of_pos hld hq
  have hmpos := Nat.div_pos (Nat.le_of_dvd hq hld) hlpos
  dsimp [f]
  rw [sum_multiples_phase q l d hlpos hld, character_sum d _ hmpos]
  change ‖(ArithmeticFunction.moebius l : ℂ) *
       (if ((q/l : ℕ) : ℤ) ∣ d then ((q/l : ℕ) : ℂ) else 0)‖ ≤
        if ((q/l : ℕ) : ℤ) ∣ d then ((q/l : ℕ) : ℝ) else 0
  by_cases hd : ((q / l : ℕ) : ℤ) ∣ d
  · simp only [ite_eq_left hd, norm_mul, Complex.norm_natCast]
    refine mul_le_of_le_one_left (Nat.cast_nonneg (α := ℝ) (q/l)) ?_
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := l)
  · rw [ite_eq_right hd, ite_eq_right hd, mul_zero, norm_zero]


end GoldbachNearShift

open Finset MeasureTheory

namespace GoldbachNearShift

noncomputable section

def cutoff (n : ℕ) : ℕ := (Nat.log 2 (n + 2))^2
def arcs (n : ℕ) : Set ℝ := {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ a.Coprime q ∧
  |t - (a : ℝ) / q| ≤ (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))}
def width (n q : ℕ) : ℝ := (cutoff n : ℝ) / ((q : ℝ) * (n : ℝ))

-- Adapted arc separation and clipping from MajorFixed144 at de53ad6299b1ab4e34e37f7f54be8ecf79e09465.
def numerators (q : ℕ) := (range (q+1)).filter (fun a => a.Coprime q)
def center (q a : ℕ) : ℝ := (a : ℝ) / q
def window (n q a : ℕ) : Set ℝ := Set.Icc (center q a - width n q) (center q a + width n q)
def leftEnd (n q a : ℕ) : ℝ := max (center q a - width n q) 0 - center q a
def rightEnd (n q a : ℕ) : ℝ := min (center q a + width n q) 1 - center q a

theorem cutoff_positive (n : ℕ) : 1 ≤ cutoff n :=
  Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n+2)).ne')

theorem width_nonneg (n q : ℕ) : 0 ≤ width n q := by unfold width; positivity

theorem mem_window (n q a : ℕ) (t : ℝ) : t ∈ window n q a ↔ |t - center q a| ≤ width n q := by
  change _ ∧ _ ↔ _
  rw [abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

/-- Separation of reduced rational arcs, using the spacing argument of wzhxzkk,
goldbach-proofs PR 153 (93d33090fdfc93fb272dde08cb463f3bff3c64ce). -/
private theorem cross_eq_of_overlap {n q r a b : ℕ} {t : ℝ} (hn : 2 * (cutoff n)^2 < n)
    (hq : q ∈ Icc 1 (cutoff n)) (hr : r ∈ Icc 1 (cutoff n))
    (ha : t ∈ window n q a) (hb : t ∈ window n r b) : a*r=b*q := by
  obtain ⟨hq₁,hqQ⟩ := mem_Icc.mp hq
  obtain ⟨hr₁,hrQ⟩ := mem_Icc.mp hr
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq₁
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr₁
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let Q := cutoff n
  have hsmall : Q * r + Q * q < n := by nlinarith only [hn, Nat.mul_le_mul_left Q hrQ, Nat.mul_le_mul_left Q hqQ]
  have hradii : (Q : ℝ) / (q*n) + Q/(r*n) < 1/(q*r) := calc
    _ = ((Q : ℝ)*r+Q*q)/(q*r*n) := by field_simp
    _ < (n : ℝ)/(q*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
    _ = _ := by field_simp
  by_contra hne
  have hsep : 1 / ((q : ℝ)*r) ≤ |(a : ℝ)/q - b/r| := by
    rw [show (a:ℝ)/q - b/r = (a*r-b*q)/(q*r) by field_simp, abs_div, abs_of_pos (mul_pos hqr hrr)]
    apply (div_le_div_iff_of_pos_right (mul_pos hqr hrr)).mpr
    rcases lt_or_gt_of_ne hne with hab | hba
    · have hgap : (a:ℝ)*r + 1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
      linarith [neg_le_abs ((a:ℝ)*r - b*q)]
    · have hgap : (b:ℝ)*q + 1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
      linarith [le_abs_self ((a:ℝ)*r - b*q)]
  have ht := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
  rw [abs_sub_comm ((a:ℝ)/q) t] at ht
  have h₁ := (mem_window n q a t).mp ha
  have h₂ := (mem_window n r b t).mp hb
  change |t-(a:ℝ)/q| ≤ (Q:ℝ)/(q*n) at h₁
  change |t-(b:ℝ)/r| ≤ (Q:ℝ)/(r*n) at h₂
  linarith

private theorem center_unique {n q r a b : ℕ} {t : ℝ} (hn : 2*(cutoff n)^2<n)
    (hq : q ∈ Icc 1 (cutoff n)) (hr : r ∈ Icc 1 (cutoff n))
    (ha : a ∈ numerators q) (hb : b ∈ numerators r)
    (hta : t ∈ window n q a) (htb : t ∈ window n r b) : q=r ∧ a=b := by
  have he := cross_eq_of_overlap hn hq hr hta htb
  have hc := (mem_filter.mp ha).2
  have hc' := (mem_filter.mp hb).2
  have hqr : q ∣ r := hc.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hrq : r ∣ q := hc'.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hqr hrq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (mem_Icc.mp hq).1 he⟩

theorem arc_indicator_sum {n : ℕ} (hn : 2*(cutoff n)^2<n) (F : ℝ → ℂ) (t : ℝ) :
    (arcs n).indicator F t =
    ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q, (window n q a).indicator F t := by
  classical
  by_cases ht : t ∈ arcs n
  · rw [Set.indicator_of_mem ht]
    obtain ⟨q,a,hq₁,hqQ,ha,hc,habs⟩ := ht
    have hq := mem_Icc.mpr ⟨hq₁,hqQ⟩
    have ha' : a ∈ numerators q := mem_filter.mpr ⟨mem_range.mpr (by omega),hc⟩
    have hw := (mem_window n q a t).mpr habs
    symm
    calc
      _ = ∑ b ∈ numerators q, (window n q b).indicator F t := by
        apply sum_eq_single_of_mem q hq
        intro r hr hrq
        exact sum_eq_zero fun b hb => Set.indicator_of_notMem (fun ht' => hrq (center_unique hn hr hq hb ha' ht' hw).1) _
      _ = (window n q a).indicator F t := by
        exact sum_eq_single_of_mem a ha' fun b hb hba =>
          Set.indicator_of_notMem (fun ht' => hba (center_unique hn hq hq hb ha' ht' hw).2) _
      _ = _ := Set.indicator_of_mem hw _
  · rw [Set.indicator_of_notMem ht]
    symm
    apply sum_eq_zero
    intro q hq
    apply sum_eq_zero
    intro a ha
    exact Set.indicator_of_notMem (fun hw => ht ⟨q,a,(mem_Icc.mp hq).1,(mem_Icc.mp hq).2,
      Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1),(mem_filter.mp ha).2,(mem_window n q a t).mp hw⟩) _

theorem center_in_unit {q a : ℕ} (hq : 0<q) (ha : a≤q) :
    0 ≤ center q a ∧ center q a ≤ 1 := by
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  exact ⟨by unfold center; positivity, (div_le_one hq').mpr (by exact_mod_cast ha)⟩

theorem clipped_order {n q a : ℕ} (hq : 0<q) (ha : a≤q) :
    -width n q ≤ leftEnd n q a ∧ leftEnd n q a ≤ rightEnd n q a ∧ rightEnd n q a ≤ width n q := by
  obtain ⟨h₁,h₂⟩ := center_in_unit hq ha
  have hw := width_nonneg n q
  unfold leftEnd rightEnd
  constructor
  · linarith [le_max_left (center q a-width n q) 0]
  constructor
  · apply sub_le_sub_right
    exact max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) zero_le_one)
  · linarith [min_le_left (center q a+width n q) 1]

theorem indicator_clipped {n q a : ℕ} (hq : 0<q) (ha : a≤q) (F : ℝ→ℂ) :
    (∫ t in (0:ℝ)..1, (window n q a).indicator F t) =
    ∫ β in leftEnd n q a..rightEnd n q a, F (center q a+β) := by
  rw [intervalIntegral.integral_comp_add_left]
  have h := (clipped_order (n := n) hq ha).2.1
  unfold leftEnd rightEnd at h ⊢
  simp only [add_sub_cancel]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    window, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Set.Icc_inter_Icc, intervalIntegral.integral_of_le (by linarith : max (center q a-width n q) 0 ≤ min (center q a+width n q) 1),
    ← integral_Icc_eq_integral_Ioc]

theorem width_le_unit {n q : ℕ} (hn : 2*(cutoff n)^2<n) (hq : 0<q) :
    width n q ≤ 1/(q:ℝ) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hQn : cutoff n ≤ n := by nlinarith [cutoff_positive n]
  calc
    width n q = ((cutoff n:ℝ)/n)/q := by unfold width; ring
    _ ≤ _ := div_le_div_of_nonneg_right ((div_le_one hn').mpr (by exact_mod_cast hQn)) hq'.le

private theorem interior_order {q a : ℕ} (hq : 1<q) (ha : a ∈ numerators q) : 0<a ∧ a<q := by
  obtain ⟨h,hc⟩ := mem_filter.mp ha
  have hle : a≤q := Nat.le_of_lt_succ (mem_range.mp h)
  have ha0 : a ≠ 0 := by rintro rfl; simp [Nat.Coprime] at hc; omega
  have hne : a ≠ q := by rintro rfl; simp [Nat.Coprime] at hc; omega
  omega

private theorem uncut {n q a : ℕ} (hn : 2*(cutoff n)^2<n) (hq : 1<q) (ha : a∈numerators q) :
    leftEnd n q a = -(width n q) ∧ rightEnd n q a = width n q := by
  obtain ⟨ha₁,haq⟩ := interior_order hq ha
  have hq' : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hw := width_le_unit hn (by omega : 0<q)
  have hc₁ : 1/(q:ℝ) ≤ center q a :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha₁) hq'.le
  have hc₂ : center q a + 1/q ≤ 1 := by
    rw [center, ← add_div, div_le_one hq']
    exact_mod_cast (Nat.succ_le_of_lt haq)
  unfold leftEnd rightEnd
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  constructor <;> ring

-- Period integral and measurability adapted from ArcBudgetTransfer at 74e41841406938b70861d75a973c922bfc4f1c93.
private theorem integral_integer_frequency (m : ℤ) :
    (∫ t in (0 : ℝ)..1, phase ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · simp [hm, phase]
  · let a : ℂ := (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ha : a ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hm)
        (mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero)
    have hexp (t : ℝ) : phase ((m : ℝ) * t) = Complex.exp (a * (t : ℂ)) := by
      unfold phase
      dsimp only [a]
      push_cast
      congr 1
      ring
    have hend : Complex.exp a = 1 := Complex.exp_int_mul_two_pi_mul_I m
    simp_rw [hexp]
    rw [integral_exp_mul_complex ha]
    simp [hm, hend]

private theorem measurable_arcs (Q n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / ((q : ℝ) * (n : ℝ))} := by
  simp only [Set.ofPred_exists, Set.ofPred_and]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  repeat' apply (MeasurableSet.const _).inter
  exact (isClosed_le (continuous_id.sub continuous_const).abs continuous_const).measurableSet

private theorem split_arc_integral {A : Set ℝ} {g : ℝ → ℂ}
    (hA : MeasurableSet A) (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, A.indicator g t) + (∫ t in (0 : ℝ)..1, Aᶜ.indicator g t) =
      ∫ t in (0 : ℝ)..1, g t := by
  have hint : IntegrableOn g (Set.Ioc (0 : ℝ) 1) volume :=
    (hg.intervalIntegrable 0 1).1
  simp only [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  rw [MeasureTheory.integral_indicator hA, MeasureTheory.integral_indicator hA.compl]
  exact MeasureTheory.integral_add_compl hA hint

private def freq (d : ℤ) (t : ℝ) : ℂ := phase ((d : ℝ) * t)

private theorem continuous_freq (d : ℤ) : Continuous (freq d) := by
  unfold freq phase
  fun_prop

private theorem major_frequency_split {n : ℕ} (hn : 2*(cutoff n)^2<n) (d : ℤ) :
    (∫ t in (0 : ℝ)..1, (arcs n).indicator (freq d) t) =
      ∑ q ∈ Icc 1 (cutoff n), ∑ a ∈ numerators q,
        ∫ β in leftEnd n q a..rightEnd n q a, freq d (center q a + β) := by
  have hcont := continuous_freq d
  have hInt (q a : ℕ) : IntervalIntegrable ((window n q a).indicator (freq d)) volume 0 1 :=
    ⟨(hcont.intervalIntegrable 0 1).1.indicator measurableSet_Icc,
      (hcont.intervalIntegrable 0 1).2.indicator measurableSet_Icc⟩
  simp_rw [arc_indicator_sum hn (freq d)]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_finsetSum (fun a _ ↦ hInt q a)]
    exact sum_congr rfl fun a ha => indicator_clipped (mem_Icc.mp hq).1
      (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp ha).1)) _
  · intro q _
    exact ⟨integrable_finsetSum _ (fun a _ ↦ (hInt q a).1),
      integrable_finsetSum _ (fun a _ ↦ (hInt q a).2)⟩

private theorem freq_add (d : ℤ) (x y : ℝ) : freq d (x + y) = freq d x * freq d y := by
  unfold freq
  rw [mul_add, phase_add]

private theorem freq_one (d : ℤ) : freq d 1 = 1 := by
  simp only [freq, mul_one]
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I d using 2
  push_cast
  ring

private theorem endpoint_frequency {n : ℕ} (hn : 2*(cutoff n)^2<n) (d : ℤ) :
    (∑ a ∈ numerators 1, ∫ β in leftEnd n 1 a..rightEnd n 1 a, freq d (center 1 a + β)) =
      ∫ β in -(width n 1)..width n 1, freq d β := by
  let w := width n 1
  have hw : 0 ≤ w := width_nonneg _ _
  have hw1 : w ≤ 1 := by simpa using width_le_unit hn (show 0 < 1 by decide)
  have hNum : numerators 1 = {0, 1} := by
    ext a
    simp [numerators]
    omega
  have hcl₀ : center 1 0 = 0 := by norm_num [center]
  have hcl₁ : center 1 1 = 1 := by norm_num [center]
  have hl₀ : leftEnd n 1 0 = 0 := by
    simp only [leftEnd, hcl₀, zero_sub, sub_zero]
    exact max_eq_right (by change -w ≤ 0; linarith)
  have hr₀ : rightEnd n 1 0 = w := by
    simp only [rightEnd, hcl₀, zero_add, sub_zero]
    exact min_eq_left hw1
  have hl₁ : leftEnd n 1 1 = -w := by
    simp only [leftEnd, hcl₁]
    change max (1-w) 0 - 1 = -w
    rw [max_eq_left (by linarith)]
    ring
  have hr₁ : rightEnd n 1 1 = 0 := by
    simp only [rightEnd, hcl₁]
    change min (1+w) 1 - 1 = 0
    rw [min_eq_right (by linarith), sub_self]
  rw [hNum, sum_insert (by decide : (0 : ℕ) ∉ {1}), sum_singleton,
    hl₀, hr₀, hl₁, hr₁, hcl₀, hcl₁]
  simp only [zero_add]
  simp_rw [freq_add d 1, freq_one, one_mul]
  rw [add_comm, intervalIntegral.integral_add_adjacent_intervals
    ((continuous_freq d).intervalIntegrable _ _) ((continuous_freq d).intervalIntegrable _ _)]

private theorem group_frequency {n q : ℕ} (hn : 2*(cutoff n)^2<n) (hq : 0 < q) (d : ℤ) :
    (∑ a ∈ numerators q, ∫ β in leftEnd n q a..rightEnd n q a, freq d (center q a + β)) =
      (∑ a ∈ (range q).filter (fun a ↦ a.Coprime q), phase ((d : ℝ) * (a : ℝ) / q)) *
        (∫ β in -(width n q)..width n q, freq d β) := by
  rcases eq_or_ne q 1 with rfl | hq1
  · rw [endpoint_frequency hn d]
    simp [phase]
  · have hq₂ : 1 < q := by omega
    have hNum : numerators q = (range q).filter (fun a ↦ a.Coprime q) := by
      ext a
      constructor
      · intro ha
        exact mem_filter.mpr ⟨mem_range.mpr (interior_order hq₂ ha).2, (mem_filter.mp ha).2⟩
      · intro ha
        obtain ⟨hb, hc⟩ := mem_filter.mp ha
        exact mem_filter.mpr ⟨mem_range.mpr (by have ht := mem_range.mp hb; omega), hc⟩
    rw [sum_mul]
    refine sum_congr hNum (fun a ha ↦ ?_)
    have ha' : a ∈ numerators q := hNum.symm ▸ ha
    obtain ⟨hl, hr⟩ := uncut hn hq₂ ha'
    rw [hl, hr]
    simp_rw [freq_add d (center q a), intervalIntegral.integral_const_mul]
    congr 1
    unfold freq center
    congr 1
    ring

private theorem norm_freq_integral_le (n q : ℕ) (d : ℤ) :
    ‖∫ β in -(width n q)..width n q, freq d β‖ ≤ 2 * (width n q) := by
  have hw := width_nonneg n q
  refine (intervalIntegral.norm_integral_le_integral_norm (by linarith : -(width n q) ≤ width n q)).trans ?_
  simp [freq, norm_phase, intervalIntegral.integral_const, smul_eq_mul, two_mul]

def minorKernel (n : ℕ) (d : ℤ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (arcs n)ᶜ.indicator (freq d) t

theorem norm_minorKernel_le {n : ℕ} (hn : 2*(cutoff n)^2<n) {d : ℤ} (hd : d ≠ 0) :
    ‖minorKernel n d‖ ≤ (2 * (cutoff n : ℝ) / n) *
      ∑ q ∈ Icc 1 (cutoff n), (1 / (q : ℝ)) *
        ∑ l ∈ q.divisors, if ((q/l : ℕ) : ℤ) ∣ d then ((q/l : ℕ) : ℝ) else 0 := by
  have hsplit := split_arc_integral (measurable_arcs (cutoff n) n) (continuous_freq d)
  change (∫ t in (0 : ℝ)..1, (arcs n).indicator (freq d) t) + minorKernel n d =
    ∫ t in (0 : ℝ)..1, phase ((d : ℝ) * t) at hsplit
  rw [integral_integer_frequency, ite_eq_right hd, major_frequency_split hn d] at hsplit
  have hneg := eq_neg_of_add_eq_zero_right hsplit
  rw [hneg, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ q ∈ Icc 1 (cutoff n), (2 * width n q) *
        ∑ l ∈ q.divisors, if ((q/l : ℕ) : ℤ) ∣ d then ((q/l : ℕ) : ℝ) else 0 := by
      refine sum_le_sum (fun q hq ↦ ?_)
      have hqpos : 0 < q := (mem_Icc.mp hq).1
      rw [group_frequency hn hqpos d, norm_mul, mul_comm]
      exact mul_le_mul (norm_freq_integral_le n q d) (norm_ramanujan_le q d hqpos)
        (norm_nonneg _) (mul_nonneg (by norm_num) (width_nonneg _ _))
    _ = _ := by
      rw [mul_sum]
      refine sum_congr rfl (fun q _ ↦ ?_)
      unfold width
      ring

end

end GoldbachNearShift


namespace GoldbachNearShift

noncomputable section

private def highPrimeLog (n p : ℕ) : ℝ :=
  primeLog p - if p ^ 3 ≤ n then primeLog p else 0

private theorem highPrimeLog_nonneg (n p : ℕ) : 0 ≤ highPrimeLog n p := by
  unfold highPrimeLog
  split_ifs <;> simp [primeLog_nonneg]

private theorem highPrimeLog_le (n p : ℕ) : highPrimeLog n p ≤ primeLog p := by
  unfold highPrimeLog
  split_ifs <;> simp [primeLog_nonneg]

private def diff (n p r : ℕ) : ℤ := (p : ℤ) + (r : ℤ) - (n : ℤ)
private abbrev short (n H p r : ℕ) : Prop := diff n p r ≠ 0 ∧ |diff n p r| ≤ (H : ℤ)
private def cap (n H : ℕ) : ℝ := Real.log 4 + 1 + Real.log ((n : ℝ) / H) + 2 * Real.log (cutoff n)
private def raw (n H p r : ℕ) : ℂ :=
  if short n H p r then (highPrimeLog n r : ℂ) * minorKernel n (diff n p r) else 0
private def row (n H p : ℕ) : ℂ := ∑ r ∈ range (n+1), raw n H p r
private def rowBound (n H : ℕ) : ℝ :=
  (2 * (cutoff n : ℝ) / n) * ((2 * (H : ℝ)) * cap n H) * (1 + Real.log (cutoff n))^2

private theorem row_estimate {n H p : ℕ} (hsep : 2 * (cutoff n)^2 < n)
    (hH : 0 < H) (hHn : H ≤ n) (hp : p ≤ n) :
    ‖row n H p‖ ≤ rowBound n H := by
  classical
  let Q := cutoff n
  let R := range (n+1)
  let A : ℝ := 2 * (Q : ℝ) / n
  let W (q l r : ℕ) : ℝ :=
    if short n H p r ∧ ((q/l : ℕ) : ℤ) ∣ diff n p r then
      ((q/l : ℕ) : ℝ) * primeLog r else 0
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hQ : 0 < Q := cutoff_positive n
  have hcap : 0 ≤ cap n H := progressScale_nonneg hH hHn hQ
  have hB : 0 ≤ (2 * (H : ℝ)) * cap n H := mul_nonneg (by positivity) hcap
  have hpoint (r : ℕ) : ‖raw n H p r‖ ≤ A *
      ∑ q ∈ Icc 1 Q, (1 / (q : ℝ)) * ∑ l ∈ q.divisors, W q l r := by
    by_cases h : short n H p r
    · unfold raw
      rw [ite_eq_left h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (highPrimeLog_nonneg n r)]
      have hK := norm_minorKernel_le hsep h.1
      calc
        _ ≤ primeLog r * (A * ∑ q ∈ Icc 1 Q, (1 / (q : ℝ)) *
            ∑ l ∈ q.divisors, if ((q/l : ℕ) : ℤ) ∣ diff n p r then ((q/l : ℕ) : ℝ) else 0) :=
          mul_le_mul (highPrimeLog_le n r) hK (norm_nonneg _) (primeLog_nonneg _)
        _ = _ := by
          rw [mul_left_comm, mul_sum]
          apply congrArg (fun x : ℝ => A*x)
          refine sum_congr rfl (fun q _ ↦ ?_)
          rw [mul_left_comm, mul_sum]
          apply congrArg (fun x : ℝ => (1 / (q : ℝ))*x)
          refine sum_congr rfl (fun l _ ↦ ?_)
          change primeLog r * (if ((q/l : ℕ) : ℤ) ∣ diff n p r then ((q/l : ℕ) : ℝ) else 0) =
            (if short n H p r ∧ ((q/l : ℕ) : ℤ) ∣ diff n p r then
              ((q/l : ℕ) : ℝ) * primeLog r else 0)
          by_cases hl : ((q/l : ℕ) : ℤ) ∣ diff n p r
          · rw [ite_eq_left hl, ite_eq_left (And.intro h hl), mul_comm]
          · have hno : ¬(short n H p r ∧ ((q/l : ℕ) : ℤ) ∣ diff n p r) := fun hc ↦ hl hc.2
            rw [ite_eq_right hl, ite_eq_right hno, mul_zero]
    · unfold raw
      simp [h, W]
  have hsum (q l : ℕ) (hq : q ∈ Icc 1 Q) (hl : l ∈ q.divisors) :
      (∑ r ∈ R, W q l r) ≤ (2 * (H : ℝ)) * cap n H := by
    obtain ⟨hq₁,hqQ⟩ := mem_Icc.mp hq
    have hlq := (Nat.mem_divisors.mp hl).1
    have hlpos := Nat.pos_of_dvd_of_pos hlq (show 0 < q from hq₁)
    have hmpos := Nat.div_pos (Nat.le_of_dvd (show 0 < q from hq₁) hlq) hlpos
    let c := n - p
    have hdiff (r : ℕ) : diff n p r = (r : ℤ) - (c : ℤ) := by
      dsimp [diff,c]
      rw [Nat.cast_sub hp]
      ring
    have hNear := nearCenterWeight_le n c (q/l) H Q (Nat.sub_le _ _) hmpos
      ((Nat.div_le_self _ _).trans hqQ) hH hHn
    simp only [← hdiff] at hNear
    calc
      _ = ((q/l : ℕ) : ℝ) * ∑ r ∈ R.filter
          (fun r ↦ short n H p r ∧ ((q/l : ℕ) : ℤ) ∣ diff n p r), primeLog r := by
        rw [sum_filter, mul_sum]
        refine sum_congr rfl (fun r _ ↦ ?_)
        unfold W
        split_ifs <;> simp
      _ ≤ ((q/l : ℕ) : ℝ) * ((2 * (H : ℝ) / ((q/l : ℕ) : ℝ)) * cap n H) :=
        mul_le_mul_of_nonneg_left (by simpa only [short, and_assoc, R, cap, Q] using hNear)
          (by positivity)
      _ = _ := by
        have hmR : (((q/l : ℕ) : ℝ)) ≠ 0 := (Nat.cast_pos.mpr hmpos : (0 : ℝ) < (q/l : ℕ)).ne'
        field_simp
  unfold row
  calc
    _ ≤ ∑ r ∈ R, ‖raw n H p r‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ R, A * ∑ q ∈ Icc 1 Q, (1 / (q : ℝ)) * ∑ l ∈ q.divisors, W q l r :=
      sum_le_sum (fun r _ ↦ hpoint r)
    _ = A * ∑ q ∈ Icc 1 Q, (1 / (q : ℝ)) * ∑ l ∈ q.divisors, ∑ r ∈ R, W q l r := by
      rw [← mul_sum]
      apply congrArg (fun x : ℝ => A*x)
      rw [sum_comm]
      refine sum_congr rfl (fun q _ ↦ ?_)
      rw [← mul_sum, sum_comm]
    _ ≤ A * ∑ q ∈ Icc 1 Q, (1 / (q : ℝ)) * ∑ _l ∈ q.divisors, (2 * (H : ℝ)) * cap n H := by
      apply mul_le_mul_of_nonneg_left _ hA
      refine sum_le_sum (fun q hq ↦ mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact sum_le_sum (fun l hl ↦ hsum q l hq hl)
    _ = A * ((2 * (H : ℝ)) * cap n H) * ∑ q ∈ Icc 1 Q, (q.divisors.card : ℝ) / q := by
      simp only [sum_const, nsmul_eq_mul]
      rw [mul_assoc A]
      apply congrArg (fun x : ℝ => A*x)
      rw [mul_sum]
      refine sum_congr rfl (fun q _ ↦ ?_)
      ring
    _ ≤ rowBound n H :=
      mul_le_mul_of_nonneg_left (divisor_reciprocal_le Q hQ) (mul_nonneg hA hB)

private def nearSum (n H : ℕ) : ℂ :=
  ∑ p ∈ range (n+1), ∑ r ∈ range (n+1),
    if short n H p r then
      (highPrimeLog n p : ℂ) * (highPrimeLog n r : ℂ) * minorKernel n (diff n p r) else 0

private theorem sum_primeLog_le (n : ℕ) :
    (∑ p ∈ range (n+1), primeLog p) ≤ Real.log 4 * (n : ℝ) := by
  have hset : (range (n+1)).filter Nat.Prime = n.primesLE := by
    rw [Nat.primesLE_eq_filter_Icc_zero]
    ext k
    simp
  simp_rw [primeLog]
  rw [← sum_filter, hset, ← Chebyshev.theta_eq_sum_primesLE_log]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)

theorem estimate_nearSum (n H : ℕ) (hn : 2 ≤ n) (hsep : 2*(cutoff n)^2 < n)
    (hH : 1 ≤ H) (hHn : H ≤ n) :
    ‖nearSum n H‖ ≤ 4 * Real.log 4 * (H : ℝ) * cutoff n *
      (1 + Real.log (cutoff n))^2 * cap n H := by
  classical
  have hrow : nearSum n H = ∑ p ∈ range (n+1), (highPrimeLog n p : ℂ) * row n H p := by
    unfold nearSum row
    refine sum_congr rfl (fun p _ ↦ ?_)
    rw [mul_sum]
    refine sum_congr rfl (fun r _ ↦ ?_)
    by_cases h : short n H p r <;> simp [raw, h, mul_assoc]
  have hcap : 0 ≤ cap n H := progressScale_nonneg hH hHn (cutoff_positive n)
  have hrowPos : 0 ≤ rowBound n H := by unfold rowBound; positivity
  rw [hrow]
  calc
    _ ≤ ∑ p ∈ range (n+1), ‖(highPrimeLog n p : ℂ) * row n H p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ range (n+1), primeLog p * rowBound n H := by
      refine sum_le_sum (fun p hp ↦ ?_)
      have hp' : p ≤ n := Nat.le_of_lt_succ (mem_range.mp hp)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (highPrimeLog_nonneg n p)]
      exact mul_le_mul (highPrimeLog_le n p) (row_estimate hsep hH hHn hp')
        (norm_nonneg _) (primeLog_nonneg p)
    _ = (∑ p ∈ range (n+1), primeLog p) * rowBound n H := by rw [sum_mul]
    _ ≤ (Real.log 4 * (n : ℝ)) * rowBound n H :=
      mul_le_mul_of_nonneg_right (sum_primeLog_le n) hrowPos
    _ = _ := by
      unfold rowBound
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      field_simp
      ring

end

end GoldbachNearShift

theorem Conjectures.Goldbach.BulkNearShiftBound :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let K := fun (n : ℕ) (d : ℤ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => E ((d:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let T := fun (n H : ℕ) => Finset.sum (Finset.range (n+1)) (fun p => Finset.sum (Finset.range (n+1)) (fun r => let d : ℤ := (p:ℤ)+(r:ℤ)-(n:ℤ); if d ≠ 0 ∧ |d| ≤ (H:ℤ) then (high n p:ℂ)*(high n r:ℂ)*K n d else 0)); let C : ℝ := Real.log 4; ∀ n H : ℕ, 2 ≤ n → 2*(Q n)^2 < n → 1 ≤ H → H ≤ n → ‖T n H‖ ≤ 4*C*(H:ℝ)*(Q n:ℝ)*(1+Real.log (Q n:ℝ))^2*(C+1+Real.log ((n:ℝ)/(H:ℝ))+2*Real.log (Q n:ℝ)) := by
  exact GoldbachNearShift.estimate_nearSum
