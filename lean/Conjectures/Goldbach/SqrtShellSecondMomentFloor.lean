import Conjectures.Goldbach.SqrtArcSecondMomentFloor

/-! Logarithmic reciprocal mass of squarefree denominators in the shell.

The factor-of-eight mass bound and the normalization of rational windows are
taken from the imported SqrtArcSecondMomentFloor module.
-/

namespace GoldbachShellFloor

open Conjectures.Goldbach.SqrtArcSecondMomentFloor
open Filter Finset
open scoped BigOperators Topology

noncomputable def cubeCutoff (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1/3 : ℝ)⌋₊

noncomputable def cubeHeight (n : ℕ) : ℕ := 256 * cubeCutoff n * (Nat.log 2 (n + 2)) ^ 2

noncomputable def shellUpper (n : ℕ) : ℕ :=
  min (GoldbachCount.sqrtCutoff n) ⌊Real.sqrt n / 4⌋₊

private theorem binaryLog_le_four_log (n : ℕ) (hn : 2 ≤ n) :
    (Nat.log 2 (n + 2) : ℝ) ≤ 4 * Real.log n := by
  let l := Nat.log 2 (n + 2)
  have h₂ : 2 ^ l ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
  have hnss : n + 2 ≤ n ^ 2 := by
    nlinarith only [Nat.mul_le_mul_left n hn, hn]
  have hpow : (2 : ℝ)^l ≤ (n : ℝ)^2 := by exact_mod_cast h₂.trans hnss
  have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ)^l) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  have hlow : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl := mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg l : (0 : ℝ) ≤ l)
  change (l : ℝ) ≤ 4 * Real.log n
  nlinarith only [hlog, hl]

private theorem eventually_scale_data :
    ∀ᶠ n : ℕ in atTop, ∃ u : ℝ,
      4 ≤ u ∧ u^48 = n ∧ (n : ℝ)^(1/3 : ℝ) = u^16 ∧ Real.sqrt n = u^24 ∧
        (Nat.log 2 (n + 2) : ℝ) ≤ u ∧ 0 < Nat.log 2 (n + 2) := by
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/48)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound (by norm_num : (0 : ℝ) < 1/4)
  filter_upwards [eventually_ge_atTop (4^48 : ℕ), hsmall] with n hn hsmall
  let u : ℝ := (n : ℝ)^(1/48 : ℝ)
  have hn2 : 2 ≤ n := (by norm_num : 2 ≤ (4^48 : ℕ)).trans hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hu : (4 : ℝ) ≤ u := by
    have hfour : ((4 : ℝ)^48)^(1/48 : ℝ) = 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [← hfour]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn) (by norm_num)
  have hsmall' : Real.log (n : ℝ) ≤ (1/4 : ℝ) * u := by
    simp only [Function.comp_def, Real.norm_eq_abs] at hsmall
    rw [abs_of_nonneg (Real.log_natCast_nonneg n),
      abs_of_nonneg (Real.rpow_nonneg hn0 (1/48 : ℝ))] at hsmall
    exact hsmall
  refine ⟨u, hu, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    norm_num
  · dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    norm_num
  · rw [Real.sqrt_eq_rpow]
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    norm_num
  · exact (binaryLog_le_four_log n hn2).trans (by linarith only [hsmall'])
  · have hlog : 1 ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
    omega

theorem cubeMaskScales : ∀ᶠ n : ℕ in atTop,
    (cubeCutoff n : ℝ) ≤ Real.sqrt n ∧ (cubeHeight n : ℝ) ≤ Real.sqrt n := by
  filter_upwards [eventually_scale_data] with n hn
  obtain ⟨u, hu, _, hcube, hsqrt, hlog, _⟩ := hn
  have hu0 : 0 < u := by linarith only [hu]
  have hD : (cubeCutoff n : ℝ) ≤ u^16 := by
    unfold cubeCutoff
    rw [hcube]
    exact Nat.floor_le (by positivity)
  have hℓ : (Nat.log 2 (n + 2) : ℝ)^2 ≤ u^2 :=
    pow_le_pow_left₀ (by positivity) hlog 2
  have h256 : (256 : ℝ) ≤ u^6 :=
    (by norm_num : (256 : ℝ) ≤ (4 : ℝ)^6).trans
      (pow_le_pow_left₀ (by norm_num) hu 6)
  rw [hsqrt]
  constructor
  · exact hD.trans (by
      calc
        u^16 = u^16 * 1 := by ring
        _ ≤ u^16 * u^8 :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ (by linarith only [hu])) (by positivity)
        _ = u^24 := by ring)
  · unfold cubeHeight
    push_cast
    calc
      (256 : ℝ) * cubeCutoff n * (Nat.log 2 (n + 2) : ℝ)^2 ≤
          256 * u^16 * u^2 := by gcongr
      _ = 256 * u^18 := by ring
      _ ≤ u^6 * u^18 := mul_le_mul_of_nonneg_right h256 (by positivity)
      _ = u^24 := by ring

private theorem eventually_shell_block_budget :
    ∀ᶠ n : ℕ in atTop, ∃ J : ℕ, 0 < cubeCutoff n ∧
      8^J * cubeCutoff n ≤ shellUpper n ∧
      1/(192 * Real.log 8) * Real.log n ≤ (J : ℝ)/8 := by
  filter_upwards [eventually_scale_data] with n hn
  obtain ⟨u, hu, hu48, hcube, hsqrt, hlog, hlogpos⟩ := hn
  have hu0 : 0 < u := by linarith only [hu]
  let l := Nat.log 2 (n + 2)
  let D := cubeCutoff n
  let m : ℕ := ⌊u^4⌋₊
  let J := Nat.log 8 m
  have hm8 : 8 ≤ m := by
    apply Nat.le_floor
    exact (by norm_num : (8 : ℝ) ≤ (4 : ℝ)^4).trans
      (pow_le_pow_left₀ (by norm_num) hu 4)
  have hJ : 1 ≤ J := Nat.le_log_of_pow_le (by decide) (by simpa using hm8)
  have hpowJ : 8^J ≤ m := Nat.pow_log_le_self _ (by omega)
  have hpowJr : (8 : ℝ)^J ≤ u^4 :=
    (by exact_mod_cast hpowJ : (8 : ℝ)^J ≤ m).trans (Nat.floor_le (by positivity))
  have hDpos : 0 < D := by
    have h₁ : 1 ≤ D := by
      unfold D cubeCutoff
      rw [hcube]
      apply Nat.le_floor
      exact one_le_pow₀ (by linarith only [hu])
    omega
  have hD : (D : ℝ) ≤ u^16 := by
    unfold D cubeCutoff
    rw [hcube]
    exact Nat.floor_le (by positivity)
  have hproduct : ((8^J * D : ℕ) : ℝ) ≤ u^20 := by
    push_cast
    calc
      (8 : ℝ)^J * D ≤ u^4 * u^16 :=
        mul_le_mul hpowJr hD (Nat.cast_nonneg D) (by positivity)
      _ = u^20 := by ring
  have hl4 : (l : ℝ)^4 ≤ u^4 := pow_le_pow_left₀ (by positivity) hlog 4
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hlogpos
  have hToSqrt : u^20 ≤ Real.sqrt n / (l : ℝ)^4 := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (l:ℝ)^4)).2
    rw [hsqrt]
    calc
      u^20 * (l : ℝ)^4 ≤ u^20 * u^4 := mul_le_mul_of_nonneg_left hl4 (by positivity)
      _ = u^24 := by ring
  have hfour : (4 : ℝ) ≤ u^4 :=
    (by norm_num : (4 : ℝ) ≤ (4 : ℝ)^4).trans
      (pow_le_pow_left₀ (by norm_num) hu 4)
  have hToQuarter : u^20 ≤ Real.sqrt n / 4 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    rw [hsqrt]
    calc
      u^20 * 4 ≤ u^20 * u^4 := mul_le_mul_of_nonneg_left hfour (by positivity)
      _ = u^24 := by ring
  have hfit : 8^J * D ≤ shellUpper n :=
    le_min (Nat.le_floor (hproduct.trans hToSqrt)) (Nat.le_floor (hproduct.trans hToQuarter))
  have hsuc : m + 1 ≤ 8^(J+1) := Nat.lt_pow_succ_log_self (by decide) m
  have hu4lt : u^4 < (8 : ℝ)^(J+1) :=
    (Nat.lt_floor_add_one (u^4)).trans_le (by exact_mod_cast hsuc)
  have hlogs := Real.log_lt_log (by positivity : 0 < u^4) hu4lt
  rw [Real.log_pow, Real.log_pow] at hlogs
  push_cast at hlogs
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJlog := mul_le_mul_of_nonneg_right
    (by linarith only [hJr] : (J : ℝ)+1 ≤ 2*J) h8.le
  have hln : Real.log (n : ℝ) = 48 * Real.log u := by
    rw [← hu48, Real.log_pow]
    norm_num
  refine ⟨J, hDpos, hfit, ?_⟩
  rw [hln, one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity : 0 < 192 * Real.log 8)).2
  nlinarith only [hlogs, hJlog]

theorem eventually_cube_le_sqrtCutoff :
    ∀ᶠ n : ℕ in atTop, cubeCutoff n ≤ GoldbachCount.sqrtCutoff n := by
  filter_upwards [eventually_shell_block_budget] with n hn
  obtain ⟨J, _, hfit, _⟩ := hn
  exact (Nat.le_mul_of_pos_left (cubeCutoff n) (by positivity : 0 < 8^J)).trans
    (hfit.trans (min_le_left _ _))

theorem shellDenominatorMass :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ n : ℕ in atTop,
      d * Real.log n ≤ ∑ q ∈ (Ioc (cubeCutoff n) (shellUpper n)).filter Squarefree, 1 / (q : ℝ) := by
  classical
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  refine ⟨1/(192 * Real.log 8), by positivity, ?_⟩
  filter_upwards [eventually_shell_block_budget] with n hn
  obtain ⟨J, hD, hfit, hlog⟩ := hn
  refine (hlog.trans (GoldbachCount.mass_blocks (cubeCutoff n) J hD)).trans ?_
  apply sum_le_sum_of_subset_of_nonneg
  · exact filter_subset_filter _ (Ioc_subset_Ioc le_rfl hfit)
  · intro q _ _
    positivity


end GoldbachShellFloor

/- Window assembly adapted from the Apache-2.0 accepted SqrtArcSecondMomentFloor,
   PR #3727, with an added measurable target and containment of each reduced window. -/
namespace GoldbachShellFloor

open Conjectures.Goldbach.SqrtArcSecondMomentFloor
open GoldbachSupport Filter Finset MeasureTheory Set
open scoped BigOperators Interval Topology

noncomputable section

private theorem shell_reduced_centers_unique {q r a b : ℕ} (hq : 0 < q)
    (ha : Nat.Coprime a q) (hb : Nat.Coprime b r) (he : a * r = b * q) :
    q = r ∧ a = b := by
  have hdq : q ∣ a * r := he ▸ Nat.dvd_mul_left q b
  have hdr : r ∣ b * q := he.symm ▸ Nat.dvd_mul_left r a
  have hqr := Nat.dvd_antisymm (ha.symm.dvd_of_dvd_mul_left hdq) (hb.symm.dvd_of_dvd_mul_left hdr)
  subst r
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

theorem assembleShellWindows (s : Finset ℕ) (D H n : ℕ) (S : ℝ → ℂ) (hS : Continuous S)
    {shell : Set ℝ} (hShell : MeasurableSet shell) (hn : 0 < n)
    (hInside : ∀ q ∈ s, ∀ a < q, Nat.Coprime a q → ∀ h ∈ Icc (0 : ℝ) (1 / (6 * n)),
      (a : ℝ) / q + h ∈ shell)
    (hden : ∀ q ∈ s, D < q)
    (hend : ∀ q ∈ s, (q : ℝ) ≤ 6 * n)
    (hmask : ∀ q ∈ s, (q : ℝ) * H + (q : ℝ) * D / 6 < n)
    (hpair : ∀ q ∈ s, ∀ r ∈ s, (q : ℝ) * r < 6 * n)
    (hamp : ∀ q ∈ s, ∀ h ∈ Icc (0 : ℝ) (1 / (6 * n)),
      (n : ℝ) / 8 ≤ ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          S ((a : ℝ) / q + h)‖) :
    ∑ q ∈ s, (n : ℝ) / (384 * (q : ℝ)) ≤
      ∫ t in (0 : ℝ)..1, (shell \ publishedWideArcs D H n).indicator (fun x => ‖S x‖ ^ 2) t := by
  classical
  let A := fun q : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q)
  let indices := s.sigma A
  let w : ℝ := 1 / (6 * (n : ℝ))
  let f : ℝ → ℝ := fun t => ‖S t‖ ^ 2
  let c : (Σ _ : ℕ, ℕ) → ℝ := fun i => (i.2 : ℝ) / i.1
  let W := fun i => Ioc (c i) (c i + w)
  let target := Ioc (0 : ℝ) 1 ∩ (shell \ publishedWideArcs D H n)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hc : Continuous f := hS.norm.pow 2
  have hindex {i : Σ _ : ℕ, ℕ} (hi : i ∈ indices) :
      i.1 ∈ s ∧ i.2 < i.1 ∧ Nat.Coprime i.2 i.1 := by
    simpa [indices, A] using hi
  have hqpos {q : ℕ} (hq : q ∈ s) : 0 < q := Nat.zero_lt_of_lt (hden q hq)
  have hge {q : ℕ} (hq : q ∈ s) : 0 < (q : ℝ) := by exact_mod_cast hqpos hq
  have hsubset {i : Σ _ : ℕ, ℕ} (hi : i ∈ indices) : W i ⊆ target := by
    rcases hindex hi with ⟨hq, ha, hcop⟩
    intro t ht
    change c i < t ∧ t ≤ c i + w at ht
    have hfirst : 0 ≤ c i := by dsimp [c]; positivity
    have hq := hge hq
    have ha1 : (i.2 : ℝ) + 1 ≤ i.1 := by exact_mod_cast ha
    have hsmall : w ≤ 1 / (i.1 : ℝ) := one_div_le_one_div_of_le hq (hend _ (hindex hi).1)
    have hlast : t ≤ 1 := calc
      t ≤ (i.2 : ℝ) / i.1 + 1 / i.1 := by change t ≤ c i + 1 / i.1; linarith only [ht.2, hsmall]
      _ = ((i.2 : ℝ) + 1) / i.1 := by ring
      _ ≤ 1 := (div_le_one hq).2 ha1
    have hins := hInside i.1 (hindex hi).1 i.2 ha hcop (t - c i)
      ⟨sub_nonneg.mpr ht.1.le, by change t - c i ≤ w; linarith only [ht.2]⟩
    change c i + (t - c i) ∈ shell at hins
    rw [add_sub_cancel] at hins
    refine ⟨⟨hfirst.trans_lt ht.1, hlast⟩, hins, ?_⟩
    have hout := outsideWideArcs i.2 i.1 D H n (t - c i) hcop
      (hden _ (hindex hi).1) hn (sub_nonneg.mpr ht.1.le)
      (by change t - c i ≤ w; linarith only [ht.2]) (hmask _ (hindex hi).1)
    change t ∉ publishedWideArcs D H n
    change c i + (t - c i) ∉ publishedWideArcs D H n at hout
    rwa [add_sub_cancel] at hout
  have hdisj : Set.Pairwise (↑indices) (fun i j => Disjoint (W i) (W j)) := by
    intro i hi j hj hne
    rcases hindex hi with ⟨hqi, hai, hci⟩
    rcases hindex hj with ⟨hqj, haj, hcj⟩
    have hcross : i.2 * j.1 ≠ j.2 * i.1 := by
      intro he
      obtain ⟨h₁,h₂⟩ := shell_reduced_centers_unique (hqpos hqi) hci hcj he
      apply hne
      cases i
      cases j
      simp_all
    apply Set.disjoint_left.mpr
    intro t ht hu
    change c i < t ∧ t ≤ c i + w at ht
    change c j < t ∧ t ≤ c j + w at hu
    have h := deepArcWindowsDisjoint i.2 j.2 i.1 j.1 n (t - c i) (t - c j)
      (hge hqi) (hge hqj) hn' hcross (hpair _ hqi _ hqj)
      (sub_nonneg.mpr ht.1.le) (by change t - c i ≤ w; linarith only [ht.2])
      (sub_nonneg.mpr hu.1.le) (by change t - c j ≤ w; linarith only [hu.2])
    apply h
    change c i + (t - c i) = c j + (t - c j)
    abel
  have hint {a b : ℝ} : IntegrableOn f (Ioc a b) volume := by
    exact (hc.integrableOn_Icc (a := a) (b := b)).mono_set Ioc_subset_Icc_self
  have htarget : IntegrableOn f target volume := hint.mono_set (Set.inter_subset_left ..)
  have hshift (i : Σ _ : ℕ, ℕ) : (∫ h in (0 : ℝ)..w, f (c i + h)) = ∫ x in W i, f x := by
    rw [intervalIntegral.integral_comp_add_left, add_zero, intervalIntegral.integral_of_le]
    exact le_add_of_nonneg_right hw
  calc
    ∑ q ∈ s, (n : ℝ) / (384 * (q : ℝ)) ≤
        ∑ q ∈ s, ∑ a ∈ A q, ∫ h in (0 : ℝ)..w, f ((a : ℝ) / q + h) := by
      apply Finset.sum_le_sum
      intro q hq
      have hcard : (A q).card ≤ q :=
        (Finset.card_filter_le ..).trans_eq (Finset.card_range q)
      exact residueWindowEnergy (A q) (fun a h => S ((a : ℝ) / q + h))
        hn' (hqpos hq) hcard (fun a _ => hS.comp (continuous_const.add continuous_id)) (hamp q hq)
    _ = ∑ i ∈ indices, ∫ h in (0 : ℝ)..w, f (c i + h) :=
      Finset.sum_sigma' s A _
    _ = ∑ i ∈ indices, ∫ x in W i, f x := Finset.sum_congr rfl fun i _ => hshift i
    _ = ∫ x in ⋃ i ∈ indices, W i, f x :=
      (integral_biUnion_finset indices (fun _ _ => measurableSet_Ioc) hdisj (fun _ _ => hint)).symm
    _ ≤ ∫ x in target, f x := by
      apply setIntegral_mono_set htarget (Filter.Eventually.of_forall fun x => sq_nonneg ‖S x‖)
      exact Filter.Eventually.of_forall fun _ hx => by
        rcases Set.mem_iUnion₂.mp hx with ⟨i,hi,ht⟩
        exact hsubset hi ht
    _ = ∫ t in (0 : ℝ)..1, (shell \ publishedWideArcs D H n).indicator (fun x => ‖S x‖ ^ 2) t := by
      rw [intervalIntegral.integral_of_le (by norm_num), setIntegral_indicator (hShell.diff (measurable_publishedWideArcs ..))]

/-- At an allowed fraction, the published square-root mask contains the
whole one-sided interval of width `1/(6n)`. -/
theorem centered_window_inside {n B q a : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hB : q ≤ B) (ha : a ≤ q) (hcop : a.Coprime q) (h : ℝ)
    (hh : h ∈ Icc (0 : ℝ) (1 / (6 * n))) :
    (a : ℝ) / q + h ∈ publishedWideArcs B (256 * B * (Nat.log 2 (n+2))^2) n := by
  have hLog : 1 ≤ Nat.log 2 (n+2) :=
    Nat.le_log_of_pow_le (by decide) (show 2^1 ≤ n+2 by omega)
  have hL2 : 1 ≤ Nat.log 2 (n+2)^2 := one_le_pow₀ hLog
  let H := 256 * B * (Nat.log 2 (n+2))^2
  have hH : q ≤ H := by
    dsimp [H]
    have h₁ := Nat.mul_le_mul_left (256*B) hL2
    omega
  change (a : ℝ) / q + h ∈ publishedWideArcs B H n
  refine ⟨q, a, hq, hB, ha, hcop, ?_⟩
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hH' : (q : ℝ) ≤ H := by exact_mod_cast hH
  rw [show (a : ℝ) / q + h - (a : ℝ) / q = h by ring, abs_of_nonneg hh.1]
  refine hh.2.trans ((div_le_div_iff₀ (by positivity) (by positivity)).2 ?_)
  have hmul := mul_le_mul_of_nonneg_right hH' hn'.le
  nlinarith only [hmul, mul_nonneg (Nat.cast_nonneg H : (0:ℝ) ≤ H) hn'.le]

/-- Turn a certified squarefree reciprocal mass into the frozen type of shell bound. -/
theorem primeMassFloor_shell_of_density (D H B : ℕ → ℕ)
    (hcuts : ∀ᶠ n : ℕ in atTop, (D n : ℝ) ≤ Real.sqrt n ∧ (H n : ℝ) ≤ Real.sqrt n)
    (d : ℝ) (hd : 0 < d)
    (hdens : ∀ᶠ n : ℕ in atTop, d * Real.log n ≤
      ∑ q ∈ (Finset.Ioc (D n) (min (B n) ⌊Real.sqrt n / 4⌋₊)).filter Squarefree,
        1 / (q : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * (n : ℝ) * Real.log n ≤ intervalIntegral (fun t =>
        (publishedWideArcs (B n) (256 * B n * (Nat.log 2 (n+2))^2) n \
          publishedWideArcs (D n) (H n) n).indicator
          (fun u => ‖GoldbachL2Arithmetic.primeSum n u‖ ^ 2) t) 0 1 MeasureTheory.volume := by
  classical
  refine ⟨d/384, by positivity, Filter.eventually_atTop.1 ?_⟩
  filter_upwards [hdens, hcuts, primeAmplitudeBounds] with n hden ⟨hD, hH⟩ ⟨hn, hθ, hqlog⟩
  let L := min (B n) ⌊Real.sqrt n / 4⌋₊
  let s := (Finset.Ioc (D n) L).filter Squarefree
  have hs {q : ℕ} (hq : q ∈ s) : (D n < q ∧ q ≤ L) ∧ Squarefree q := by
    simpa [s] using hq
  have hb {q : ℕ} (hq : q ∈ s) : q ≤ B n := (hs hq).1.2.trans (min_le_left ..)
  have hroot {q : ℕ} (hq : q ∈ s) : q ≤ ⌊Real.sqrt n / 4⌋₊ :=
    (hs hq).1.2.trans (min_le_right ..)
  obtain ⟨hend, hmask, hpair⟩ := denominatorWindowLimits n (D n) (H n) hn hD hH
  have hc : Continuous (GoldbachL2Arithmetic.primeSum n) := by
    unfold GoldbachL2Arithmetic.primeSum GoldbachL2Arithmetic.primeTerm GoldbachL2Arithmetic.E
    fun_prop
  apply (scaleDenominatorMass s n d (Real.log n) hden).trans
  apply assembleShellWindows s (D n) (H n) n _ hc (measurable_publishedWideArcs ..) (by omega)
  · intro q hq a ha hcop h hh
    exact centered_window_inside (by omega) (Nat.zero_lt_of_lt (hs hq).1.1)
      (hb hq) ha.le hcop h hh
  · exact fun _ hq => (hs hq).1.1
  · exact fun q hq => hend q (hroot hq)
  · exact fun q hq => hmask q (hroot hq)
  · exact fun q hq r hr => hpair q r (hroot hq) (hroot hr)
  · exact fun q hq h hh => GoldbachL2Arithmetic.reduced_amplitude n q (by omega)
      (hs hq).2 hθ (hqlog q (hroot hq)) h hh.1 hh.2


end

end GoldbachShellFloor

open GoldbachShellFloor Conjectures.Goldbach.SqrtArcSecondMomentFloor in
theorem Conjectures.Goldbach.SqrtShellSecondMomentFloor :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Q₂ := fun n : ℕ => ⌊Real.sqrt (n : ℝ) / ((Nat.log 2 (n + 2) : ℝ) ^ 4)⌋₊; let sqrtArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q₂ n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ ((256 * Q₂ n * Q n : ℕ) : ℝ) / ((q : ℝ) * (n : ℝ))}; ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * (n : ℝ) * Real.log (n : ℝ) ≤ intervalIntegral (fun t => (sqrtArcs n \ wideArcs n).indicator (fun u => ‖S n w u‖ ^ 2) t) (0 : ℝ) 1 MeasureTheory.volume := by
  obtain ⟨d, hd, hden⟩ := shellDenominatorMass
  simpa only [cubeCutoff, cubeHeight, shellUpper, GoldbachCount.sqrtCutoff,
    GoldbachL2Arithmetic.primeSum_eq_catalogue, GoldbachL2Arithmetic.E,
    GoldbachSupport.publishedWideArcs] using
    primeMassFloor_shell_of_density cubeCutoff cubeHeight GoldbachCount.sqrtCutoff
      cubeMaskScales d hd hden
