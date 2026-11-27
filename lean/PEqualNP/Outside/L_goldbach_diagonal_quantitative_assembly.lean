import Mathlib

open scoped Classical

private theorem abelError :
    let p := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let θ := fun n : ℕ => ∑ k ∈ Finset.range (n+1), p k; let g := fun (φ : ℝ → ℝ) (n k : ℕ) => Real.log (k:ℝ)*(φ ((k:ℝ)/n))^2; ∀ (φ : ℝ → ℝ) (n : ℕ), 1≤n → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → (∑ k ∈ Finset.Icc 1 n, (p k-1)*g φ n k) = - ∑ k ∈ Finset.range n, (θ k-(k:ℝ))*(g φ n (k+1)-g φ n k) := by
  intro p θ g φ n hn hφ
  let T := fun k : ℕ => θ k - (k:ℝ)
  have hz : T 0 = 0 := by simp [T,θ,p]
  have hstep (k : ℕ) : T (k+1) = T k + (p (k+1) - 1) := by
    dsimp only [T,θ]
    rw [Finset.sum_range_succ]
    push_cast
    ring
  have h (m : ℕ) :
      (∑ k ∈ Finset.Icc 1 m, (p k-1)*g φ n k) =
        T m * g φ n m - ∑ k ∈ Finset.range m, T k * (g φ n (k+1)-g φ n k) := by
    induction m with
    | zero => simp [hz]
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega),Finset.sum_range_succ,ih,hstep]
      ring
  have hnn : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have htail : g φ n n = 0 := by
    dsimp only [g]
    rw [div_self hnn,hφ 1 (Or.inr (by norm_num))]
    ring
  simpa only [htail,mul_zero,zero_sub,T] using h n


open scoped NNReal
private def smoothWeight (φ : ℝ → ℝ) (u : ℝ) := (φ u)^2
private noncomputable def logWeight (φ : ℝ → ℝ) (u : ℝ) := smoothWeight φ u * Real.log u

private theorem smoothBounds {φ : ℝ → ℝ} (hd : ContDiff ℝ 1 φ)
    (hs : ∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) :
    ∃ A B : ℝ≥0,
      LipschitzOnWith A (smoothWeight φ) (Set.Icc 0 1) ∧
      LipschitzOnWith B (logWeight φ) (Set.Icc 0 1) ∧ Continuous (logWeight φ) := by
  have hf : ContDiff ℝ 1 (smoothWeight φ) := hd.pow 2
  have hg : ContDiff ℝ 1 (logWeight φ) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst x
      apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      filter_upwards [gt_mem_nhds (by norm_num : (0:ℝ)<1/3)] with y hy
      simp [logWeight,smoothWeight,hs y (Or.inl hy)]
    · exact hf.contDiffAt.mul (Real.contDiffAt_log.mpr hx)
  obtain ⟨A,hA⟩ := hf.contDiffOn.exists_lipschitzOnWith (by decide) (convex_Icc 0 1) isCompact_Icc
  obtain ⟨B,hB⟩ := hg.contDiffOn.exists_lipschitzOnWith (by decide) (convex_Icc 0 1) isCompact_Icc
  exact ⟨A,B,hA,hB,hg.continuous⟩

private theorem splitWeight (φ : ℝ → ℝ) (hs : ∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0)
    (n k : ℕ) (hn : 0 < n) :
    Real.log (k:ℝ)*(φ ((k:ℝ)/n))^2 =
      Real.log (n:ℝ)*smoothWeight φ ((k:ℝ)/n) + logWeight φ ((k:ℝ)/n) := by
  by_cases hk : k = 0
  · subst k; simp [smoothWeight,logWeight,hs 0 (Or.inl (by norm_num))]
  · have hnk : (n:ℝ) ≠ 0 := by positivity
    have hkk : (k:ℝ) ≠ 0 := by exact_mod_cast hk
    rw [logWeight,Real.log_div hkk hnk,smoothWeight]
    ring

private theorem logSize (n : ℕ) (hn : 2 ≤ n) :
    1 ≤ Real.log (2*(n:ℝ)) ∧ Real.log (n:ℝ) ≤ Real.log (2*(n:ℝ)) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · apply (Real.le_log_iff_exp_le (by positivity)).mpr
    linarith only [Real.exp_one_lt_three, hn']
  · exact Real.log_le_log (by positivity) (by linarith)

private theorem variation :
    let g := fun (φ : ℝ → ℝ) (n k : ℕ) => Real.log (k:ℝ)*(φ ((k:ℝ)/n))^2; ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 2≤n → (∑ k ∈ Finset.range n, |g φ n (k+1)-g φ n k|) ≤ K*Real.log (2*(n:ℝ)) := by
  intro g φ hd hs
  obtain ⟨A,B,hA,hB,hcont⟩ := smoothBounds hd hs
  refine ⟨(A:ℝ)+B+1,by positivity,?_⟩
  intro n hn
  have hn' : 0 < (n:ℝ) := by positivity
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤n))
  let u := fun k : ℕ => (k:ℝ)/n
  have hu {k : ℕ} (hk : k ≤ n) : u k ∈ Set.Icc 0 1 :=
    ⟨by dsimp [u]; positivity,(div_le_one hn').mpr (by exact_mod_cast hk)⟩
  have diff (k : ℕ) : u (k+1)-u k = 1/n := by dsimp [u]; push_cast; ring
  have bound (k : ℕ) (hk : k<n) :
      |g φ n (k+1)-g φ n k| ≤ ((A:ℝ)*Real.log (n:ℝ)+B)/n := by
    have ha := hA.dist_le_mul _ (hu (Nat.succ_le_of_lt hk)) _ (hu hk.le)
    have hb := hB.dist_le_mul _ (hu (Nat.succ_le_of_lt hk)) _ (hu hk.le)
    simp only [Real.dist_eq,diff,abs_of_nonneg (show 0 ≤ 1/(n:ℝ) by positivity)] at ha hb
    change |Real.log ((k+1:ℕ):ℝ)*(φ (u (k+1)))^2 - Real.log (k:ℝ)*(φ (u k))^2| ≤ _
    rw [splitWeight φ hs n (k+1) (by omega), splitWeight φ hs n k (by omega)]

    calc
      _ = |Real.log (n:ℝ)*(smoothWeight φ (u (k+1))-smoothWeight φ (u k)) +
        (logWeight φ (u (k+1))-logWeight φ (u k))| := by congr 1; ring
      _ ≤ _ := abs_add_le .. |>.trans (show
        |Real.log (n:ℝ)*(smoothWeight φ (u (k+1))-smoothWeight φ (u k))| +
        |logWeight φ (u (k+1))-logWeight φ (u k)| ≤ _ from by
          rw [abs_mul, abs_of_nonneg hlog]
          calc
            _ ≤ Real.log (n:ℝ)*((A:ℝ)*(1/n)) + (B:ℝ)*(1/n) :=
              by linarith only [mul_le_mul_of_nonneg_left ha hlog, hb]
            _ = _ := by ring)
  have hh := Finset.sum_le_sum (s := Finset.range n) (fun k hk => bound k (Finset.mem_range.mp hk))
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  calc
    _ ≤ _ := hh
    _ = (A:ℝ)*Real.log (n:ℝ)+B := by field_simp
    _ ≤ _ := by
      obtain ⟨hl,hm⟩ := logSize n hn
      nlinarith [mul_nonneg A.coe_nonneg (sub_nonneg.mpr hm),mul_nonneg B.coe_nonneg (sub_nonneg.mpr hl)]


private theorem shiftedSum (n : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 n, f k) = (∑ k ∈ Finset.range n, f (k+1)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega),Finset.sum_range_succ,ih]

private theorem gridError {f : ℝ → ℝ} {L : ℝ≥0} (hc : Continuous f)
    (hL : LipschitzOnWith L f (Set.Icc 0 1)) (n : ℕ) (hn : 0 < n) :
    |(∑ k ∈ Finset.Icc 1 n, f ((k:ℝ)/n))/(n:ℝ) - (∫ x in (0:ℝ)..1, f x)| ≤ L/(n:ℝ) := by
  let u := fun k : ℕ => (k:ℝ)/n
  have hp : 0 < (n:ℝ) := by exact_mod_cast hn
  have step (k : ℕ) : u (k+1) - u k = 1/n := by dsimp [u]; push_cast; ring
  have hmono (k : ℕ) : u k ≤ u (k+1) := by have := step k; linarith [show 0 ≤ 1/(n:ℝ) by positivity]
  have hpt {k : ℕ} (hk : k ≤ n) : u k ∈ Set.Icc 0 1 :=
    ⟨by dsimp [u]; positivity, (div_le_one hp).mpr (by exact_mod_cast hk)⟩
  have pieces (k : ℕ) (hk : k<n) :
      |f (u (k+1))/n - (∫ t in u k..u (k+1), f t)| ≤ ((L:ℝ)/n)/n := by
    have ha := hpt (Nat.le_of_lt hk)
    have hb := hpt (Nat.succ_le_of_lt hk)
    have bd (t : ℝ) (ht : t ∈ Set.uIoc (u k) (u (k+1))) :
        ‖f (u (k+1))-f t‖ ≤ (L:ℝ)/n := by
      rw [Set.uIoc_of_le (hmono k)] at ht
      have h := hL.dist_le_mul _ hb t ⟨ha.1.trans ht.1.le,ht.2.trans hb.2⟩
      rw [Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr ht.2)] at h
      rw [Real.norm_eq_abs]
      calc
        _ ≤ _ := h
        _ ≤ (L:ℝ)*(u (k+1)-u k) := by gcongr; exact ht.1.le
        _ = _ := by rw [step]; ring
    have H := intervalIntegral.norm_integral_le_of_norm_le_const bd
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable ..) (hc.intervalIntegrable ..),
      intervalIntegral.integral_const,Real.norm_eq_abs,smul_eq_mul,step,abs_of_nonneg (show 0 ≤ 1/(n:ℝ) by positivity)] at H
    convert H using 1 <;> congr 1 <;> ring
  have sumints := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume) (a := u)
     (n := n) (f := f) (fun k _ => hc.intervalIntegrable ..)
  have u0 : u 0 = 0 := by simp [u]
  have un : u n = 1 := by dsimp [u]; exact div_self hp.ne'
  rw [u0,un] at sumints
  rw [shiftedSum,Finset.sum_div, ← sumints,← Finset.sum_sub_distrib]
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _k ∈ Finset.range n, ((L:ℝ)/n)/n :=
      Finset.sum_le_sum (fun k hk => pieces k (Finset.mem_range.mp hk))
    _ = _ := by simp; field_simp

private theorem riemann :
    let g := fun (φ : ℝ → ℝ) (n k : ℕ) => Real.log (k:ℝ)*(φ ((k:ℝ)/n))^2; let c := fun φ : ℝ → ℝ => intervalIntegral (fun u : ℝ => (φ u)^2) 0 1 MeasureTheory.volume; let b := fun φ : ℝ → ℝ => intervalIntegral (fun u : ℝ => (φ u)^2*Real.log u) 0 1 MeasureTheory.volume; ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 2≤n → |(∑ k ∈ Finset.Icc 1 n, g φ n k)/(n:ℝ) - (c φ*Real.log (n:ℝ)+b φ)| ≤ K*Real.log (2*(n:ℝ))/(n:ℝ) := by
  intro g c b φ hd hs
  obtain ⟨A,B,hA,hB,hcont⟩ := smoothBounds hd hs
  refine ⟨(A:ℝ)+B+1,by positivity,?_⟩
  intro n hn
  have hpos : 0 < (n:ℝ) := by positivity
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hF := gridError (f := smoothWeight φ) (hd.continuous.pow 2) hA n (by omega)
  have hG := gridError hcont hB n (by omega)
  change |(∑ k ∈ Finset.Icc 1 n, smoothWeight φ ((k:ℝ)/n))/(n:ℝ)-c φ| ≤ _ at hF
  change |(∑ k ∈ Finset.Icc 1 n, logWeight φ ((k:ℝ)/n))/(n:ℝ)-b φ| ≤ _ at hG
  have eq (k : ℕ) : g φ n k =
      Real.log (n:ℝ)*smoothWeight φ ((k:ℝ)/n) + logWeight φ ((k:ℝ)/n) := splitWeight φ hs n k (by omega)
  simp_rw [eq]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  calc
    _ = |Real.log (n:ℝ)*((∑ k ∈ Finset.Icc 1 n, smoothWeight φ ((k:ℝ)/n))/(n:ℝ)-c φ)
        + ((∑ k ∈ Finset.Icc 1 n, logWeight φ ((k:ℝ)/n))/(n:ℝ)-b φ)| := by congr 1; ring
    _ ≤ _ := (abs_add_le ..).trans (by
      rw [abs_mul,abs_of_nonneg hlog]
      calc
        _ ≤ Real.log (n:ℝ)*((A:ℝ)/n)+(B:ℝ)/n := add_le_add (mul_le_mul_of_nonneg_left hF hlog) hG
        _ = ((A:ℝ)*Real.log (n:ℝ)+B)/n := by ring
        _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ hpos.le
          obtain ⟨hl,hm⟩ := logSize n hn
          nlinarith [mul_nonneg A.coe_nonneg (sub_nonneg.mpr hm),mul_nonneg B.coe_nonneg (sub_nonneg.mpr hl)])




open Finset
private theorem window_count : let B := fun n p : ℕ => (Finset.Icc 1 (Nat.log 2 n)).filter (fun a => n≤3*p^a ∧ 3*p^a≤2*n); ∀ n p : ℕ, 0<n → p.Prime → (B n p).card ≤ (if p=2 then 2 else 1) := by
  dsimp only
  intro n p hn hp
  let B := (Finset.Icc 1 (Nat.log 2 n)).filter (fun a => n≤3*p^a ∧ 3*p^a≤2*n)
  change B.card ≤ _
  by_cases h : B.Nonempty
  · let a := B.min' h
    have ha := (Finset.mem_filter.mp (B.min'_mem h)).2
    have narrow (b : ℕ) (hb : b ∈ B) : p^b ≤ 2*p^a := by
      have hi := (Finset.mem_filter.mp hb).2.2
      dsimp [a] at *
      omega
    have hpos : 0 < p^a := pow_pos hp.pos _
    by_cases htwo : p = 2
    · rw [if_pos htwo]
      have inc : B ⊆ Finset.Icc a (a+1) := by
        intro b hb
        refine Finset.mem_Icc.mpr ⟨B.min'_le b hb, ?_⟩
        by_contra! hf
        have hh := narrow b hb
        have hpow := Nat.pow_le_pow_right hp.pos (show a+2 ≤ b by omega)
        rw [pow_add] at hpow
        rw [htwo] at hpow hh hpos
        norm_num at hpow
        omega
      have hc := Finset.card_le_card inc
      simp only [Nat.card_Icc] at hc
      omega
    · rw [if_neg htwo]
      have inc : B ⊆ {a} := by
        intro b hb
        have hlo : a ≤ b := B.min'_le b hb
        have hp3 : 3 ≤ p := by have := hp.two_le; omega
        apply Finset.mem_singleton.mpr
        by_contra hne
        have hpow := Nat.pow_le_pow_right hp.pos (show a+1 ≤ b by omega)
        rw [pow_succ] at hpow
        have hlim := narrow b hb
        nlinarith [Nat.mul_le_mul_left (p^a) hp3]
      simpa using Finset.card_le_card inc
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp

private theorem ramified_total : ∀ n : ℕ, 2≤n → (∑ k ∈ (Finset.range (n+1)).filter (fun k => n≤3*k ∧ 3*k≤2*n ∧ ¬k.Coprime n), ArithmeticFunction.vonMangoldt k) ≤ 2*Real.log (n:ℝ) := by
  classical
  intro n hn
  let B := fun p : ℕ => (Finset.Icc 1 (Nat.log 2 n)).filter
    (fun a => n≤3*p^a ∧ 3*p^a≤2*n)
  let T := (Finset.range (n+1)).filter (fun k => n≤3*k ∧ 3*k≤2*n ∧ ¬k.Coprime n)
  let V := fun p a k : ℕ => if p^a=k then Real.log (p:ℝ) else 0
  have pos (p : ℕ) (hp : p ∈ n.primeFactors) : 0 ≤ Real.log (p:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)
  have vpos (p : ℕ) (hp : p ∈ n.primeFactors) (a k : ℕ) : 0 ≤ V p a k := by
    dsimp [V]
    split <;> first | exact pos p hp | exact le_rfl
  have one (k : ℕ) (hk : k ∈ T) :
      ArithmeticFunction.vonMangoldt k ≤ ∑ p ∈ n.primeFactors, ∑ a ∈ B p, V p a k := by
    by_cases hzero : ArithmeticFunction.vonMangoldt k = 0
    · rw [hzero]; exact sum_nonneg fun p hp => sum_nonneg fun a _ => vpos p hp a k
    obtain ⟨p,a,hp,ha,hpk⟩ := (isPrimePow_nat_iff k).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hzero)
    obtain ⟨hkr, hklo, hkhi, hnc⟩ := Finset.mem_filter.mp hk
    have hmem : p ∈ n.primeFactors := by
      apply Nat.mem_primeFactors.mpr
      refine ⟨hp, ?_, by omega⟩
      by_contra hnd
      exact hnc (hpk ▸ ((hp.coprime_iff_not_dvd.mpr hnd).pow_left a))
    have hba : a ∈ B p := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha, Nat.le_log_of_pow_le (by decide) ?_⟩, ?_⟩
      · have hkmax := Finset.mem_range.mp hkr
        exact (Nat.pow_le_pow_left hp.two_le _).trans (hpk ▸ (show k ≤ n by omega))
      · simpa only [hpk] using And.intro hklo hkhi
    calc
      _ = V p a k := by rw [← hpk, ArithmeticFunction.vonMangoldt_apply_pow ha.ne', ArithmeticFunction.vonMangoldt_apply_prime hp]; simp [V]
      _ ≤ ∑ a ∈ B p, V p a k := Finset.single_le_sum (fun j _ => vpos p hmem j k) hba
      _ ≤ _ := Finset.single_le_sum (fun p hp => sum_nonneg fun a _ => vpos p hp a k) hmem
  have hsum : (∑ p ∈ n.primeFactors, Real.log (p:ℝ)) ≤ Real.log n := by
    rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
    rw [← Nat.cast_prod]
    apply Real.log_le_log
    · exact_mod_cast Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    · exact_mod_cast Nat.le_of_dvd (by omega : 0<n) (Nat.prod_primeFactors_dvd n)
  change (∑ k ∈ T, _) ≤ _
  calc
    _ ≤ ∑ k ∈ T, ∑ p ∈ n.primeFactors, ∑ a ∈ B p, V p a k := sum_le_sum one
    _ = ∑ p ∈ n.primeFactors, ∑ a ∈ B p, ∑ k ∈ T, V p a k := by
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun p _ => Finset.sum_comm)
    _ ≤ ∑ p ∈ n.primeFactors, (B p).card*Real.log (p:ℝ) := by
      refine sum_le_sum fun p hp => ?_
      calc
        _ ≤ ∑ _a ∈ B p, Real.log (p:ℝ) := by
          refine sum_le_sum fun a _ => ?_
          simp only [V, Finset.sum_ite_eq]
          split <;> first | exact le_rfl | exact pos _ hp
        _ = _ := by simp
    _ ≤ ∑ p ∈ n.primeFactors, 2*Real.log (p:ℝ) := by
      refine sum_le_sum fun p hp => mul_le_mul_of_nonneg_right ?_ (pos p hp)
      have hc := window_count n p (by omega) (Nat.prime_of_mem_primeFactors hp)
      have hbound : (B p).card ≤ 2 := by
        change (B p).card ≤ (if p=2 then 2 else 1) at hc
        split at hc <;> omega
      exact_mod_cast hbound
    _ ≤ _ := by rw [← Finset.mul_sum]; linarith


 private theorem ramifiedSquares : ∀ n : ℕ, 2≤n → (∑ k ∈ (Finset.range (n+1)).filter (fun k => n≤3*k ∧ 3*k≤2*n ∧ ¬k.Coprime n), (ArithmeticFunction.vonMangoldt k)^2) ≤ 2*(Real.log (n:ℝ))^2 := by
  intro n hn
  let T := (Finset.range (n+1)).filter (fun k => n≤3*k ∧ 3*k≤2*n ∧ ¬k.Coprime n)
  have bound := ramified_total n hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  calc
    _ ≤ ∑ k ∈ T, ArithmeticFunction.vonMangoldt k * Real.log n := by
      apply sum_le_sum
      intro k hk
      obtain ⟨hr, hlo, _, _⟩ := Finset.mem_filter.mp hk
      have hkp : 0 < (k:ℝ) := by exact_mod_cast (show 0<k by omega)
      have hkmax := Finset.mem_range.mp hr
      have hkLe : (k:ℝ) ≤ n := by exact_mod_cast (show k≤n by omega)
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hkp hkLe)) ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ _ := by
      rw [← sum_mul]
      change (∑ k ∈ T, _) ≤ _ at bound
      nlinarith [mul_le_mul_of_nonneg_right bound hlog]


private theorem squareBudget :
    let p := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let D := fun (φ : ℝ → ℝ) (n : ℕ) => (∑ k ∈ (Finset.range (n+1)).filter (fun k => k.Coprime n), (ArithmeticFunction.vonMangoldt k)^2*(φ ((k:ℝ)/n))^2)/(n:ℝ); ∃ K : ℝ, 0<K ∧ ∀ (n : ℕ) (φ : ℝ → ℝ), 2≤n → (∀ u, |φ u|≤1) → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → |D φ n - (∑ k ∈ Finset.range (n+1), (p k)^2*(φ ((k:ℝ)/n))^2)/(n:ℝ)| ≤ K*(Real.log (2*(n:ℝ)))^3/Real.sqrt (n:ℝ) := by
  intro p D
  refine ⟨2,by norm_num,?_⟩
  intro n φ hn hb hs
  let W := ArithmeticFunction.vonMangoldt
  let w := fun k : ℕ => (φ ((k:ℝ)/n))^2
  let F := Finset.range (n+1)
  let L := Real.log (n:ℝ)
  let T := Real.log (2*(n:ℝ))
  have hn' : 2 ≤ (n:ℝ) := by exact_mod_cast hn
  have hpos : 0 < (n:ℝ) := by positivity
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hLT : L ≤ T := Real.log_le_log hpos (by linarith)
  have hT : 1 ≤ T := (Real.le_log_iff_exp_le (by positivity)).mpr (by linarith [Real.exp_one_lt_three])
  have hsqrt : 1 ≤ Real.sqrt n := (Real.one_le_sqrt).mpr (by linarith)
  have hroot := Real.sq_sqrt hpos.le
  have wpos (k : ℕ) : 0 ≤ w k := sq_nonneg _
  have wle (k : ℕ) : w k ≤ 1 := by
    obtain ⟨hu,hv⟩ := abs_le.mp (hb ((k:ℝ)/n))
    dsimp [w]; nlinarith [mul_nonneg (sub_nonneg.mpr hv) (by linarith : 0 ≤ 1+φ ((k:ℝ)/n))]
  have ppos (k : ℕ) : 0 ≤ W k - p k := by
    by_cases hk : k.Prime <;> simp [W,p,hk,ArithmeticFunction.vonMangoldt_apply_prime]
  have psub (k : ℕ) : 0 ≤ (W k)^2 - (p k)^2 := by
    by_cases hk : k.Prime <;> simp [W,p,hk,ArithmeticFunction.vonMangoldt_apply_prime]
  have mass : (∑ k ∈ F, (W k - p k)) ≤ 2*Real.sqrt n * L := by
    calc
      _ = Chebyshev.psi n - Chebyshev.theta n := by
        dsimp only [F,W]
        rw [Nat.range_succ_eq_Icc_zero,← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
        simp [Chebyshev.psi,Chebyshev.theta,p,Finset.sum_filter,Finset.sum_sub_distrib]
      _ ≤ _ := Chebyshev.psi_sub_theta_le (by linarith)
  have hh : (∑ k ∈ F, ((W k)^2-(p k)^2)*w k) ≤ L*(2*Real.sqrt n * L) := by
    calc
      _ ≤ ∑ k ∈ F, L*(W k-p k) := by
        apply Finset.sum_le_sum
        intro k hk
        calc
          _ ≤ ((W k)^2 - (p k)^2) * 1 := mul_le_mul_of_nonneg_left (wle _) (psub _)
          _ ≤ _ := by
            by_cases hk' : k.Prime
            · simp [W,p,hk',ArithmeticFunction.vonMangoldt_apply_prime]
            · simp only [p,if_neg hk',zero_pow (by omega : 2≠0),sub_zero,mul_one,pow_two]
              by_cases hz : k=0
              · subst k; simp [W]
              · apply mul_le_mul_of_nonneg_right _ ArithmeticFunction.vonMangoldt_nonneg
                refine ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by positivity) ?_)
                have := Finset.mem_range.mp hk
                exact_mod_cast (by omega : k≤n)
      _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left mass hL
  have rm : (∑ k ∈ F.filter (fun k => ¬ k.Coprime n), (W k)^2*w k) ≤ 2*L^2 := by
    let C := fun k : ℕ => n≤3*k ∧ 3*k≤2*n ∧ ¬k.Coprime n
    calc
      _ = ∑ k ∈ F.filter C, (W k)^2*w k := by
        simp only [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hcop : k.Coprime n
        · simp [C,hcop]
        · by_cases hcen : n ≤ 3*k ∧ 3*k ≤ 2*n
          · simp [C,hcop,hcen.1,hcen.2]
          · have hout : (k:ℝ)/n < 1/3 ∨ 2/3 < (k:ℝ)/n := by
              rcases not_and_or.mp hcen with hlo|hhi
              · left; rw [div_lt_iff₀ hpos]; have hh : (3:ℝ)*k < n := by exact_mod_cast (by omega : 3*k<n)
                linarith
              · right; rw [lt_div_iff₀ hpos]; have hh : (2:ℝ)*n < 3*k := by exact_mod_cast (by omega : 2*n<3*k)
                linarith
            simp [C,hcop,w,hs _ hout]
      _ ≤ ∑ k ∈ F.filter C, (W k)^2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (wle k) (sq_nonneg (W k))
      _ ≤ _ := ramifiedSquares n hn
  let P := ∑ k ∈ F, (p k)^2*w k
  let B := ∑ k ∈ F.filter (fun k => k.Coprime n), (W k)^2*w k
  let E := ∑ k ∈ F.filter (fun k => ¬k.Coprime n), (W k)^2*w k
  have ident : B + E - P = ∑ k ∈ F, ((W k)^2-(p k)^2)*w k := by
    dsimp only [B,E,P]
    rw [Finset.sum_filter_add_sum_filter_not,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  have enon : 0 ≤ E := Finset.sum_nonneg (fun k _ => mul_nonneg (sq_nonneg _) (wpos _))
  have dnon : 0 ≤ B+E-P := by rw [ident]; exact Finset.sum_nonneg (fun k _ => mul_nonneg (psub _) (wpos _))
  have er : E ≤ 2*L^2 := rm
  rw [← ident] at hh
  have L2 : L^2 ≤ T^3 := calc
    L^2 ≤ T^2 := by gcongr
    _ ≤ T^3 := pow_le_pow_right₀ hT (by decide)
  have upp : L*(2*Real.sqrt n * L) ≤ 2*Real.sqrt n*T^3 := by
    calc _ = 2*Real.sqrt n*L^2 := by ring
         _ ≤ _ := by gcongr
  have low : 2*L^2 ≤ 2*Real.sqrt n*T^3 := by
    have hT3 : 0 ≤ T^3 := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt) hT3]
  change |B/(n:ℝ) - P/(n:ℝ)| ≤ 2*T^3/Real.sqrt n
  rw [←sub_div,abs_div,abs_of_pos hpos,div_le_div_iff₀ hpos (Real.sqrt_pos.mpr hpos)]
  have hh' : |B-P| ≤ 2*Real.sqrt n*T^3 := by
    rw [abs_le]
    constructor <;> linarith
  calc
    _ ≤ (2*Real.sqrt n*T^3)*Real.sqrt n := by gcongr
    _ = _ := by linear_combination (2*T^3)*hroot


theorem PEqualNP.Outside.L_goldbach_diagonal_quantitative_assembly :
    let p := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let θ := fun n : ℕ => ∑ k ∈ Finset.range (n+1), p k; let D := fun (φ : ℝ → ℝ) (n : ℕ) => (∑ k ∈ (Finset.range (n+1)).filter (fun k => k.Coprime n), (ArithmeticFunction.vonMangoldt k)^2*(φ ((k:ℝ)/n))^2)/(n:ℝ); let c := fun φ : ℝ → ℝ => intervalIntegral (fun u : ℝ => (φ u)^2) 0 1 MeasureTheory.volume; let b := fun φ : ℝ → ℝ => intervalIntegral (fun u : ℝ => (φ u)^2*Real.log u) 0 1 MeasureTheory.volume; (∃ A : ℝ, 0<A ∧ ∀ k : ℕ, 2≤k → |θ k-(k:ℝ)| ≤ A*Real.sqrt (k:ℝ)*(Real.log (2*(k:ℝ)))^2) → ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → (∀ u, |φ u|≤1) → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 2≤n → |D φ n-(c φ*Real.log (n:ℝ)+b φ)| ≤ K*(Real.log (2*(n:ℝ)))^3/Real.sqrt (n:ℝ) := by
  intro p θ D c b hRH φ hd hb hs
  obtain ⟨A,hA,hθ⟩ := hRH
  let g := fun (n k : ℕ) => Real.log (k:ℝ)*(φ ((k:ℝ)/n))^2
  obtain ⟨V,hV,hvar⟩ := variation φ hd hs
  obtain ⟨R,hR,hri⟩ := riemann φ hd hs
  obtain ⟨Q,hQ,hprime⟩ := squareBudget
  refine ⟨Q + (A+1)*V + R,by positivity,?_⟩
  intro n hn
  let T := Real.log (2*(n:ℝ))
  have hr : 2 ≤ (n:ℝ) := by exact_mod_cast hn
  have hp : 0 < (n:ℝ) := by positivity
  have ht : 1 ≤ T := (logSize n hn).1
  have ht0 : 0 ≤ T := by linarith
  have hrt : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by linarith)
  have hrt0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hp
  have hrr := Real.sq_sqrt hp.le
  let E := (A+1)*Real.sqrt n*T^2
  have E0 : 0 ≤ E := by dsimp [E]; positivity
  have hmax (k : ℕ) (hk : k ∈ Finset.range n) : |θ k-(k:ℝ)| ≤ E := by
    have hkn := Finset.mem_range.mp hk
    by_cases h : 2 ≤ k
    · refine (hθ k h).trans ?_
      dsimp only [E,T]
      have hkr : (0:ℝ) < k := by positivity
      have hxr : (k:ℝ) ≤ n := by exact_mod_cast hkn.le
      have hl : 0 ≤ Real.log (2*(k:ℝ)) := Real.log_nonneg (by linarith [show (2:ℝ) ≤ k by exact_mod_cast h])
      gcongr <;> first | positivity | linarith | exact Real.log_le_log (by positivity) (by linarith)
    · have e : k = 0 ∨ k = 1 := by omega
      rcases e with rfl|rfl
      · simpa [θ,p] using E0
      · have hE : 1 ≤ E := by
          dsimp only [E]
          calc
            (1:ℝ) = 1*1*1^2 := by norm_num
            _ ≤ _ := by gcongr <;> linarith
        simpa [θ,p,Finset.sum_range_succ] using hE
  let P := ∑ k ∈ Finset.range (n+1), (p k)^2*(φ ((k:ℝ)/n))^2
  let G := ∑ k ∈ Finset.Icc 1 n, g n k
  have hprimeG (k : ℕ) : (p k)^2*(φ ((k:ℝ)/n))^2 = (p k)*g n k := by
    dsimp only [g,p]
    split_ifs <;> ring
  have hsplit : P - G = ∑ k ∈ Finset.Icc 1 n, (p k-1)*g n k := by
    dsimp only [P,G]
    simp_rw [hprimeG]
    rw [Nat.range_succ_eq_Icc_zero,← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
    have hset : Finset.Ioc 0 n = Finset.Icc 1 n := by ext k; simp; omega
    rw [hset]
    have h0 : p 0 = 0 := by simp [p]
    rw [h0,zero_mul,zero_add,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _; ring
  have hab := abelError φ n (by omega) hs
  change (∑ k ∈ Finset.Icc 1 n, (p k-1)*g n k) =
    -∑ k ∈ Finset.range n, (θ k-(k:ℝ))*(g n (k+1)-g n k) at hab
  have hadd : |P-G| ≤ E*(V*T) := by
    rw [hsplit,hab,abs_neg]
    calc
      _ ≤ _ := Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ k ∈ Finset.range n, E*|g n (k+1)-g n k| := by
        exact Finset.sum_le_sum (fun k hk => by rw [abs_mul]; gcongr; exact hmax _ hk)
      _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hvar n hn) E0
  have hadiv : |P/(n:ℝ)-G/n| ≤ (A+1)*V*T^3 / Real.sqrt n := by
    rw [←sub_div,abs_div,abs_of_pos hp,div_le_div_iff₀ hp hrt0]
    calc
      _ ≤ E*(V*T)*Real.sqrt n := by gcongr
      _ = _ := by dsimp only [E]; linear_combination ((A+1)*V*T^3)*hrr
  let target := c φ * Real.log (n:ℝ) + b φ
  have h1 : |D φ n - P/(n:ℝ)| ≤ Q*T^3/Real.sqrt n := hprime n φ hn hb hs
  have h3 : |G/(n:ℝ)-target| ≤ R*T/(n:ℝ) := hri n hn
  have h3' : R*T/(n:ℝ) ≤ R*T^3 / Real.sqrt n := by
    apply div_le_div₀ (by positivity) _ hrt0 _
    · apply mul_le_mul_of_nonneg_left _ hR.le
      simpa only [pow_one] using pow_le_pow_right₀ ht (by decide : 1 ≤ 3)
    · nlinarith [mul_nonneg (sub_nonneg.mpr hrt) hrt0.le]
  calc
    _ ≤ |D φ n - P/(n:ℝ)| + |P/(n:ℝ)-target| := abs_sub_le ..
    _ ≤ |D φ n - P/(n:ℝ)| + (|P/(n:ℝ)-G/n| + |G/(n:ℝ)-target|) := by gcongr; exact abs_sub_le ..
    _ ≤ Q*T^3/Real.sqrt n + ((A+1)*V*T^3/Real.sqrt n + R*T^3/Real.sqrt n) :=
      by linarith only [h1,hadiv,h3.trans h3']
    _ = _ := by ring
