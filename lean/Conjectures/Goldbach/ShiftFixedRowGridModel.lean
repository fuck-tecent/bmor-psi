import Mathlib

/- Portions adapted from 26day, Apache-2.0, ShiftGridMaskCrossings.lean at
928889383712c2fa5d2480d3c5ea4623d1359af1 and FiniteMajorRescaledIntervalKernel.lean
at 96f7394665112bc519d68a3dbb44861f0d3ae550. Changed to private supporting lemmas. -/
open MeasureTheory intervalIntegral
open scoped Interval

private noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
private theorem phaseNorm (x : ℝ) : ‖phase x‖=1 := Complex.norm_exp_ofReal_mul_I _
private theorem phaseAdd (x y : ℝ) : phase (x+y)=phase x*phase y := by
  simp only [phase, mul_add, Complex.ofReal_add,add_mul,Complex.exp_add]
private theorem phaseLip (x y : ℝ) : ‖phase x-phase y‖ ≤ 2*Real.pi*|x-y| := by
  have h : phase x-phase y = (phase (x-y)-1)*phase y := by
    rw [sub_mul, ← phaseAdd, sub_add_cancel,one_mul]
  rw [h,norm_mul,phaseNorm,mul_one]
  unfold phase
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,abs_mul]
  rw [show 2*Real.pi*(x-y)/2=Real.pi*(x-y) by ring]
  have hb : |Real.sin (Real.pi*(x-y))| ≤ |Real.pi*(x-y)| := Real.abs_sin_le_abs
  rw [abs_mul,abs_of_pos Real.pi_pos] at hb
  norm_num
  linarith

private theorem continuousPhase : Continuous phase := by unfold phase; fun_prop


private noncomputable def gridCell (K j : ℕ) : Set ℝ := Set.Icc ((j:ℝ)/K) (((j:ℝ)+1)/K)

private noncomputable def hits (K : ℕ) (x : ℝ) : Finset ℕ :=
  @Finset.filter ℕ (fun j => x ∈ gridCell K j) (fun _ => Classical.propDecidable _) (Finset.range K)

private theorem atMostTwo {K : ℕ} (hK : 0 < K) (x : ℝ) : (hits K x).card ≤ 2 := by
  classical
  by_cases h : (hits K x).Nonempty
  · let i := (hits K x).min' h
    have hi' : i ∈ hits K x := Finset.min'_mem _ _
    simp only [hits, Finset.mem_filter] at hi'
    have hi := hi'.2
    change (i:ℝ)/K ≤ x ∧ x ≤ ((i:ℝ)+1)/K at hi
    have sub : hits K x ⊆ {i,i+1} := by
      intro j hj
      have hlo : i ≤ j := Finset.min'_le _ _ hj
      simp only [hits, Finset.mem_filter] at hj
      have hjx := hj.2
      change (j:ℝ)/K ≤ x ∧ x ≤ ((j:ℝ)+1)/K at hjx
      have hk : (0:ℝ) < K := by exact_mod_cast hK
      have hreal : (j:ℝ) ≤ (i:ℝ)+1 := (div_le_div_iff_of_pos_right hk).mp (hjx.1.trans hi.2)
      have hhi : j ≤ i+1 := by exact_mod_cast hreal
      simp only [Finset.mem_insert,Finset.mem_singleton]
      omega
    exact (Finset.card_le_card sub).trans (by simp)
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]

private theorem countCross {K : ℕ} (hk : 0 < K) (Q : ℕ) (c d : ℕ → ℕ → ℝ)
    (ok : ℕ → ℕ → Prop) :
    let arcs : Set ℝ := {t | ∃ q ∈ Finset.Icc 1 Q, ∃ a ∈ Finset.range (q+1),
      ok q a ∧ |t - c q a| ≤ d q a}
    let cross := @Finset.filter ℕ (fun j => ((gridCell K j) ∩ arcs).Nonempty ∧
      ((gridCell K j) ∩ arcsᶜ).Nonempty) (fun _ => Classical.propDecidable _) (Finset.range K)
    cross.card ≤ 4 * ∑ q ∈ Finset.Icc 1 Q, (q+1) := by
  classical
  intro arcs cross
  let ends := fun q a => hits K (c q a - d q a) ∪ hits K (c q a + d q a)
  let row := fun q => (Finset.range (q+1)).biUnion (ends q)
  have sub : cross ⊆ (Finset.Icc 1 Q).biUnion row := by
    intro j hj
    simp only [cross,Finset.mem_filter] at hj
    obtain ⟨hj,⟨u,hu,⟨q,hq,a,ha,hgood,huarc⟩⟩,⟨v,hv,hvout⟩⟩ := hj
    refine Finset.mem_biUnion.mpr ⟨q,hq,Finset.mem_biUnion.mpr ⟨a,ha,?_⟩⟩
    have hvbad : ¬ |v-c q a| ≤ d q a := fun hv' => hvout ⟨q,hq,a,ha,hgood,hv'⟩
    rw [abs_le] at huarc hvbad
    change (j:ℝ)/K ≤ u ∧ u ≤ ((j:ℝ)+1)/K at hu
    change (j:ℝ)/K ≤ v ∧ v ≤ ((j:ℝ)+1)/K at hv
    simp only [ends,Finset.mem_union,hits,Finset.mem_filter]
    
    by_cases hleft : v < c q a - d q a
    · left
      refine ⟨hj,?_,?_⟩ <;> linarith
    · right
      have ht : c q a + d q a < v := by by_contra! hc; exact hvbad ⟨by linarith,by linarith⟩
      refine ⟨hj,?_,?_⟩ <;> linarith
  have rowle (q : ℕ) : (row q).card ≤ (q+1)*4 := by
    calc
      _ ≤ ∑ a ∈ Finset.range (q+1), (ends q a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ Finset.range (q+1), 4 := Finset.sum_le_sum fun a _ =>
        (Finset.card_union_le _ _).trans (Nat.add_le_add (atMostTwo hk _) (atMostTwo hk _))
      _ = _ := by simp
  calc
    _ ≤ _ := Finset.card_le_card sub
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, (row q).card := Finset.card_biUnion_le
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, (q+1)*4 := Finset.sum_le_sum fun q _ => rowle q
    _ = _ := by rw [← Finset.sum_mul, Nat.mul_comm]

private theorem maskCrossings :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; ∀ n K : ℕ, 0 < n → 0 < K →
let cell := fun j : ℕ => Set.Icc ((j : ℝ) / K) (((j : ℝ)+1) / K)
let cross := @Finset.filter ℕ (fun j => ((cell j) ∩ (wideArcs n)).Nonempty ∧ ((cell j) ∩ (wideArcs n)ᶜ).Nonempty) (fun _ => Classical.propDecidable _) (Finset.range K)
cross.card ≤ 4 * (∑ q ∈ Finset.Icc 1 (Q₁ n), (q+1)) := by
  intro Q Q₁ H arcs n K hn hK cell cross
  have harcs : arcs n = {t | ∃ q ∈ Finset.Icc 1 (Q₁ n), ∃ a ∈ Finset.range (q+1),
      Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))} := by
    ext t
    constructor
    · rintro ⟨q,a,h1,h2,h3,h4,h5⟩
      exact ⟨q,Finset.mem_Icc.mpr ⟨h1,h2⟩,a,Finset.mem_range.mpr (by omega),h4,h5⟩
    · rintro ⟨q,hq,a,ha,h4,h5⟩
      exact ⟨q,a,(Finset.mem_Icc.mp hq).1,(Finset.mem_Icc.mp hq).2,
        Nat.le_of_lt_succ (Finset.mem_range.mp ha),h4,h5⟩
  dsimp only [cross,cell]
  rw [harcs]
  exact countCross hK (Q₁ n) (fun q a => (a:ℝ)/q) (fun q _ => (H n:ℝ)/((q:ℝ)*n))
    (fun q a => Nat.Coprime a q)

private theorem gridApprox (K : ℕ) (hk : 0<K) (A : Set ℝ) (ha : MeasurableSet A)
    (g : ℝ → ℂ) (hg : Continuous g) (B L : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hb : ∀ x, ‖g x‖≤B) (hl : ∀ x y, ‖g x-g y‖ ≤ L*|x-y|) :
    let F := Aᶜ.indicator g
    let bad := @Finset.filter ℕ (fun j => ((gridCell K j) ∩ A).Nonempty ∧
      ((gridCell K j) ∩ Aᶜ).Nonempty) (fun _ => Classical.propDecidable _) (Finset.range K)
    |(∫ x in (0:ℝ)..1, F x).re -
      (∑ j ∈ Finset.range K, F (((j:ℝ)+1/2)/K)).re/K| ≤ L/K+2*B*bad.card/K := by
  classical
  intro F bad
  let u := fun j : ℕ => (j:ℝ)/K
  let mid := fun j : ℕ => ((j:ℝ)+1/2)/K
  have hK : (0:ℝ)<K := by exact_mod_cast hk
  have ints (a b : ℝ) : IntervalIntegrable F volume a b := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp (hg.intervalIntegrable a b)).indicator ha.compl
  have fn (x : ℝ) : ‖F x‖≤B := by by_cases hx : x∈Aᶜ <;> simp [F,hx,hb,hB]
  let err := fun j => (∫ x in u j..u (j+1), F x) - (1/(K:ℝ)) • F (mid j)
  have cellBound (j : ℕ) (hj : j ∈ Finset.range K) :
      ‖err j‖ ≤ (L/K + if j∈bad then 2*B else 0)/K := by
    have len : u (j+1) - u j = 1/(K:ℝ) := by dsimp [u]; push_cast; ring
    have ord : u j≤u (j+1) := sub_nonneg.mp (len ▸ by positivity)
    have hm : mid j ∈ gridCell K j := by
      constructor <;> apply (div_le_div_iff_of_pos_right hK).mpr <;> linarith
    have e : err j = ∫ x in u j..u (j+1), F x - F (mid j) := by
      rw [intervalIntegral.integral_sub (ints _ _) (continuous_const.intervalIntegrable _ _),
        intervalIntegral.integral_const,len]
    rw [e]
    have bd (x) (hx : x∈Set.uIoc (u j) (u (j+1))) :
        ‖F x-F (mid j)‖≤ L/K + if j∈bad then 2*B else 0 := by
      rw [Set.uIoc_of_le ord] at hx
      have hx' : x∈gridCell K j := ⟨hx.1.le,by simpa [u,Nat.cast_add] using hx.2⟩
      by_cases hh : j∈bad
      · rw [if_pos hh]
        linarith [norm_sub_le (F x) (F (mid j)),fn x,fn (mid j),div_nonneg hL hK.le]
      rw [if_neg hh,add_zero]
      have hs : x∈A ↔ mid j∈A := by
        constructor
        · intro a; by_contra b; apply hh; simp only [bad,Finset.mem_filter]; exact ⟨hj,⟨x,hx',a⟩,mid j,hm,b⟩
        · intro b; by_contra a; apply hh; simp only [bad,Finset.mem_filter]; exact ⟨hj,⟨mid j,hm,b⟩,x,hx',a⟩
      by_cases hxa : x∈A
      · simp [F,hxa,hs.mp hxa,div_nonneg hL hK.le]
      have hmout := mt hs.mpr hxa
      rw [show F x = g x from Set.indicator_of_mem (s:=Aᶜ) hxa _, show F (mid j)=g (mid j) from Set.indicator_of_mem (s:=Aᶜ) hmout _]
      have hxy : |x-mid j| ≤ 1/(K:ℝ) := by
        change (j:ℝ)/K≤x ∧ x≤((j:ℝ)+1)/K at hx'
        change (j:ℝ)/(K:ℝ) ≤ mid j ∧ mid j ≤ ((j:ℝ)+1)/K at hm
        have he : ((j:ℝ)+1)/K - (j:ℝ)/K = 1/(K:ℝ) := by ring
        rw [abs_le]; constructor <;> linarith
      exact (hl _ _).trans ((mul_le_mul_of_nonneg_left hxy hL).trans_eq (by ring))
    exact (intervalIntegral.norm_integral_le_of_norm_le_const bd).trans_eq (by rw [len,abs_of_pos (by positivity)]; ring)
  have tel := intervalIntegral.sum_integral_adjacent_intervals (a:=u) (n:=K) (fun _ _ => ints _ _)
  have es : ∑ j ∈ Finset.range K, err j = (∫ x in (0:ℝ)..1, F x) -
      (1/(K:ℝ)) • (∑ j ∈ Finset.range K, F (mid j)) := by
    simp only [err,Finset.sum_sub_distrib,tel,← Finset.smul_sum,u,Nat.cast_zero,zero_div,div_self hK.ne']
  have eabs := (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum cellBound))
  rw [es,Complex.sub_re,Complex.real_smul,Complex.mul_re] at eabs
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at eabs
  calc
    _ = _ := show _ = |(∫ x in (0:ℝ)..1, F x).re - 1/(K:ℝ) * (∑ j ∈ Finset.range K,F (mid j)).re| by congr 2 <;> ring
    _ ≤ _ := eabs
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      have sub : bad ⊆ Finset.range K := by intro i hi; simp only [bad,Finset.mem_filter] at hi; exact hi.1
      rw [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr sub]
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; field_simp <;> ring

private noncomputable def wt (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
private noncomputable def poly (n : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), (wt k:ℂ)*phase (k*x)
private noncomputable def osc (n m : ℕ) (x : ℝ) : ℂ := (poly n x)^2*phase (-(m:ℝ)*x)

private theorem oscBounds (n m : ℕ) (hm : m≤2*n) :
    let P := (n:ℝ)+1
    Continuous (osc n m) ∧ (∀ x, ‖osc n m x‖ ≤ 4*P^3) ∧
    ∀ x y, ‖osc n m x - osc n m y‖ ≤ 32*Real.pi*P^4*|x-y| := by
  intro P
  have hp : 0≤P := by dsimp [P]; positivity
  let T := 2*Real.sqrt P
  have ht : 0≤T := by dsimp [T]; positivity
  have t2 : T^2=4*P := by dsimp [T]; rw [mul_pow,Real.sq_sqrt hp]; ring
  have kn (k : ℕ) (hk : k∈Finset.range (n+1)) : (k:ℝ)≤P := by
    dsimp [P]; exact_mod_cast (Finset.mem_range.mp hk).le
  have kw (k : ℕ) (hk : k∈Finset.range (n+1)) : |wt k| ≤ T := by
    by_cases h : k.Prime
    · have hk1 : (1:ℝ)≤k := by exact_mod_cast h.one_le
      rw [wt,if_pos h, abs_of_nonneg (Real.log_nonneg hk1)]
      calc
        _ ≤ (k:ℝ)^(1/2:ℝ)/(1/2) := Real.log_le_rpow_div (by positivity) (by norm_num)
        _ = 2*Real.sqrt k := by rw [Real.sqrt_eq_rpow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (kn _ hk)) (by norm_num)
    · simpa [wt,h] using ht
  have ph (k : ℝ) (x y : ℝ) : ‖phase (k*x)-phase (k*y)‖ ≤ 2*Real.pi*|k| *|x-y| := by
    refine (phaseLip _ _).trans_eq ?_
    rw [← mul_sub,abs_mul]; ring
  have amp (x : ℝ) : ‖poly n x‖≤P*T := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _k ∈ Finset.range (n+1), T := Finset.sum_le_sum fun k hk => by
        rw [norm_mul,phaseNorm,mul_one,Complex.norm_real,Real.norm_eq_abs]; exact kw _ hk
      _ = _ := by simp [P]
  have lip (x y : ℝ) : ‖poly n x - poly n y‖ ≤ 2*Real.pi*P^2*T*|x-y| := by
    simp only [poly,← Finset.sum_sub_distrib,← mul_sub]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _k ∈ Finset.range (n+1), T*(2*Real.pi*P*|x-y|) := Finset.sum_le_sum fun k hk => by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        apply mul_le_mul (kw _ hk) _ (norm_nonneg _) ht
        refine (ph _ _ _).trans ?_
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        gcongr; exact kn _ hk
      _ = _ := by simp [P]; ring
  have phaseM (x y : ℝ) : ‖phase (-(m:ℝ)*x)-phase (-(m:ℝ)*y)‖ ≤ 4*Real.pi*P*|x-y| := by
    refine (ph _ _ _).trans ?_
    rw [abs_neg,abs_of_nonneg (Nat.cast_nonneg m)]
    have mm : (m:ℝ)≤2*P := by dsimp [P]; exact_mod_cast (show m≤2*(n+1) by omega)
    calc 2*Real.pi*m*|x-y| ≤ 2*Real.pi*(2*P)*|x-y| := by gcongr
         _ = _ := by ring
  refine ⟨by unfold osc poly phase; fun_prop,?_,?_⟩
  · intro x
    rw [osc,norm_mul,norm_pow,phaseNorm,mul_one]
    calc _ ≤ (P*T)^2 := by gcongr; exact amp x
         _ = _ := by rw [mul_pow,t2]; ring
  intro x y
  have e : osc n m x-osc n m y =
      ((poly n x-poly n y)*(poly n x+poly n y))*phase (-(m:ℝ)*x) +
      (poly n y)^2*(phase (-(m:ℝ)*x)-phase (-(m:ℝ)*y)) := by unfold osc; ring
  rw [e]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_pow,phaseNorm,mul_one]
  calc
    _ ≤ (2*Real.pi*P^2*T*|x-y|)*(P*T+P*T)+(P*T)^2*(4*Real.pi*P*|x-y|) := by
      gcongr
      · exact lip x y
      · exact (norm_add_le _ _).trans (add_le_add (amp _) (amp _))
      · exact amp _
      · exact phaseM _ _
    _ = _ := by ring_nf; nlinarith only [congrArg (fun z : ℝ => 8*Real.pi*P^3*|x-y| *z) t2]

private noncomputable def qOne (n : ℕ) := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
private noncomputable def height (n : ℕ) := 256 * qOne n * (Nat.log 2 (n+2))^2
private noncomputable def wide (n : ℕ) : Set ℝ := {t | ∃ q a : ℕ, 1≤q ∧ q≤qOne n ∧
  a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (height n:ℝ)/((q:ℝ)*(n:ℝ))}
private theorem measWide (n : ℕ) : MeasurableSet (wide n) := by
  have he : wide n = ⋃ q : ℕ, ⋃ a : ℕ, {t : ℝ | (1≤q ∧ q≤qOne n ∧ a≤q ∧ Nat.Coprime a q) ∧
      |t-(a:ℝ)/(q:ℝ)| ≤ (height n:ℝ)/((q:ℝ)*(n:ℝ))} := by
    ext t; simp only [wide,Set.mem_setOf_eq,Set.mem_iUnion]; aesop
  rw [he]; apply MeasurableSet.iUnion; intro q; apply MeasurableSet.iUnion; intro a
  by_cases h : 1≤q ∧ q≤qOne n ∧ a≤q ∧ Nat.Coprime a q
  · convert (isClosed_le (show Continuous (fun t : ℝ => |t-(a:ℝ)/(q:ℝ)|) by fun_prop) (continuous_const (y:=(height n:ℝ)/((q:ℝ)*(n:ℝ))))).measurableSet using 1
    ext t; exact ⟨fun x => x.2,fun x => ⟨h,x⟩⟩
  · simp [h]

private theorem gridCoeff (n m : ℕ) (hn : 1≤n) (hm : m≤2*n) :
    let K := (n+1)^6
    let F := (wide n)ᶜ.indicator (osc n m)
    |(∫ x in (0:ℝ)..1, F x).re - (∑ j ∈ Finset.range K, F (((j:ℝ)+1/2)/K)).re/K|
       ≤ 300/((n:ℝ)+1)^2 := by
  intro K F
  let P := (n:ℝ)+1
  let bad := @Finset.filter ℕ (fun j => ((gridCell K j) ∩ wide n).Nonempty ∧
      ((gridCell K j) ∩ (wide n)ᶜ).Nonempty) (fun _ => Classical.propDecidable _) (Finset.range K)
  have hk : 0<K := by dsimp [K]; positivity
  have pk : (K:ℝ)=P^6 := by norm_num [P,K]
  have hp : (0:ℝ)<P := by dsimp [P]; positivity
  have n1 : (1:ℝ)≤n := by exact_mod_cast hn
  have qb : (qOne n:ℝ)≤Real.sqrt P := by
    calc
      _ ≤ (n:ℝ)^(1/3:ℝ) := Nat.floor_le (by positivity)
      _ ≤ (n:ℝ)^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
      _ ≤ _ := by rw [← Real.sqrt_eq_rpow]; apply Real.sqrt_le_sqrt; dsimp [P]; linarith
  have q2 : (qOne n:ℝ)^2 ≤ P := (show (qOne n:ℝ)^2 ≤ (Real.sqrt P)^2 by gcongr).trans_eq (Real.sq_sqrt hp.le)
  have bcount : (bad.card:ℝ) ≤ 16*P := by
    have cb : bad.card ≤ 4*∑ q ∈ Finset.Icc 1 (qOne n),(q+1) := maskCrossings n K hn hk
    have sub : (∑ q ∈ Finset.Icc 1 (qOne n), (q+1)) ≤ qOne n*(qOne n+1) := by
      calc _ ≤ ∑ _q ∈ Finset.Icc 1 (qOne n), (qOne n+1) :=
             Finset.sum_le_sum fun q h => Nat.succ_le_succ (Finset.mem_Icc.mp h).2
           _ = _ := by simp [Nat.card_Icc]
    have h := cb.trans (Nat.mul_le_mul_left 4 sub)
    have hr : (bad.card:ℝ)≤4*((qOne n:ℝ)*((qOne n:ℝ)+1)) := by exact_mod_cast h
    dsimp [P] at *; nlinarith [sq_nonneg ((qOne n:ℝ)-1)]
  obtain ⟨c,a,l⟩ := oscBounds n m hm
  have ge := gridApprox K hk (wide n) (measWide n) (osc n m) c (4*P^3) (32*Real.pi*P^4)
    (by positivity) (by positivity) a l
  change _ ≤ 32*Real.pi*P^4/K+2*(4*P^3)*bad.card/K at ge
  apply ge.trans
  rw [pk]
  change _ ≤ 300/P^2
  calc
    _ ≤ 32*4*P^4/P^6+2*(4*P^3)*(16*P)/P^6 := by gcongr <;> first | exact Real.pi_lt_four.le | exact bcount
    _ ≤ 300/P^2 := by field_simp; nlinarith [show 0 ≤ P^6 by positivity]

private theorem windowCard (n : ℕ) (he : Even n) :
    n/2+1 ≤ ((Finset.Icc n (2*n)).filter Even).card ∧
    ((Finset.Icc n (2*n)).filter Even).card ≤ n+1 := by
  classical
  constructor
  · let f := fun j : ℕ => n+2*j
    have sub : (Finset.range (n/2+1)).image f ⊆ (Finset.Icc n (2*n)).filter Even := by
      rintro _ hk
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
      have h := Finset.mem_range.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by dsimp [f]; omega,by dsimp [f]; omega⟩,
        he.add (even_two_mul _)⟩
    have inj : Function.Injective f := by intro x y h; dsimp [f] at h; omega
    simpa [Finset.card_image_of_injective _ inj] using Finset.card_le_card sub
  · exact (Finset.card_filter_le _ _).trans (by simp [Nat.card_Icc]; omega)

private theorem weightArithmetic (n ε A : ℝ) (hn : 0<n) (h : A*8≤n^3*ε^2) :
    (2/n)*A ≤ ((ε/2)*n)^2 := by field_simp; nlinarith only [h]

private theorem sqOfAbs {x y : ℝ} (hy : 0≤y) (h : |x|≤y) : x^2≤y^2 := by
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hy).mpr h

set_option maxHeartbeats 600000 in
theorem Conjectures.Goldbach.ShiftFixedRowGridModel : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let deepCoeff := fun (n m : ℕ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun u => (S n w u)^2 * E (-(m:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let model := fun n m : ℕ =>
  let K : ℕ := (n+1)^6
  let t := fun j : ℕ => ((j:ℝ) + 1/2) / K
  ((∑ j ∈ Finset.range K, ((wideArcs n)ᶜ.indicator (fun u => (S n w u)^2 * E (-(m:ℝ)*u)) (t j))).re) / K
∀ ε η : ℝ, 0 < ε → 0 < η → η < 1/3 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Even n →
let W := (Finset.Icc n (2*n)).filter Even
let ω := fun m : ℕ => if m ∈ W then 1 / (W.card : ℝ) else 0
(∑ m ∈ W, ω m) = 1 ∧
(∑ m ∈ W, (ω m)^2) * (n:ℝ)^(8/3+η) ≤ ((ε/2)*(n:ℝ))^2 ∧
(∑ m ∈ W, ((deepCoeff n m).re - model n m)^2) ≤ 1/(n:ℝ)^2 := by
  classical
  intro w E S Q Q₁ H wideArcs deepCoeff model ε η hε _hη hη3
  have ha := (tendsto_rpow_atTop (show 0<1/3-η by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := Filter.tendsto_atTop_atTop.mp ha (8/ε^2)
  refine ⟨max N 90000,?_⟩
  intro n hn he W ω
  have hnB := (le_max_right N 90000).trans hn
  have hn1 : 1≤n := by omega
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn1
  have hN' : 8/ε^2 ≤ (n:ℝ)^(1/3-η) := hN n ((le_max_left _ _).trans hn)
  obtain ⟨wc,wt'⟩ := windowCard n he
  change n/2+1≤W.card at wc
  change W.card≤n+1 at wt'
  have hw : 0<(W.card:ℝ) := by exact_mod_cast (show 0<W.card by omega)
  have size : (n:ℝ)≤2*(W.card:ℝ) := by exact_mod_cast (show n≤2*W.card by omega)
  have sumw (j : ℕ) : (∑ m ∈ W, (ω m)^j) = (W.card:ℝ)*(1/(W.card:ℝ))^j := by
    calc
      _ = ∑ _m ∈ W, (1/(W.card:ℝ))^j := Finset.sum_congr rfl fun m hm => by simp [ω,hm]
      _ = _ := by simp
  refine ⟨by simpa [hw.ne'] using sumw 1,?_,?_⟩
  · rw [sumw]
    have s2 : (W.card:ℝ)*(1/(W.card:ℝ))^2≤2/n := by field_simp; nlinarith
    have divbd := (div_le_iff₀ (by positivity : 0<ε^2)).mp hN'
    have v : (n:ℝ)^(8/3+η)*(n:ℝ)^(1/3-η)=(n:ℝ)^3 := by
      rw [← Real.rpow_add hnR,show (8/3+η)+(1/3-η)=(3:ℝ) by ring]; norm_num
    have pos : 0≤(n:ℝ)^(8/3+η) := by positivity
    calc
      _ ≤ (2/n)*(n:ℝ)^(8/3+η) := mul_le_mul_of_nonneg_right s2 pos
      _ ≤ _ := by
        have q := mul_le_mul_of_nonneg_left divbd pos
        rw [← mul_assoc,v] at q
        exact weightArithmetic _ _ _ hnR q
  · let P := (n:ℝ)+1
    have p : 0<P := by dsimp [P]; positivity
    have point (m : ℕ) (hm : m∈W) : ((deepCoeff n m).re-model n m)^2≤(300/P^2)^2 := by
      have h := gridCoeff n m hn1 (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
      change |(deepCoeff n m).re-model n m|≤300/P^2 at h
      exact sqOfAbs (by positivity) h
    calc
      _ ≤ ∑ _m ∈ W, (300/P^2)^2 := Finset.sum_le_sum point
      _ ≤ P*(300/P^2)^2 := by
        simp only [Finset.sum_const,nsmul_eq_mul]; gcongr; dsimp [P]; exact_mod_cast wt'
      _ ≤ 1/(n:ℝ)^2 := by
        have big : (90000:ℝ)≤P := by dsimp [P]; exact_mod_cast (show 90000≤n+1 by omega)
        have np : (n:ℝ)≤P := by dsimp [P]; linarith
        calc
          _ = (90000/P)*(1/P^2) := by field_simp; ring
          _ ≤ 1*(1/P^2) := by gcongr; exact (div_le_one p).mpr big
          _ ≤ _ := by rw [one_mul]; gcongr
