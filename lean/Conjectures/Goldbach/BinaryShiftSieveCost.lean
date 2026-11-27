import Mathlib

namespace BinaryShiftCost

private theorem prime_log_sum_le {n : ℕ} (hn : 0 < n) :
    (∑ p ∈ n.primesLE, Real.log p / p) ≤ 2 * Real.log n := by
  let S := n.factorial.primeFactors
  have sub : n.primesLE ⊆ S := by
    intro p h
    obtain ⟨hle,hp⟩ := Nat.mem_primesLE.mp h
    exact Nat.mem_primeFactors.mpr ⟨hp, Nat.dvd_factorial hp.pos hle, n.factorial_ne_zero⟩
  have logfac : ∑ p ∈ S, (n.factorial.factorization p:ℝ)*Real.log p =
      Real.log (n.factorial:ℝ) := by
    have hnat := Nat.prod_primeFactors_pow_factorization n.factorial_ne_zero
    have hreal := congrArg (fun k : ℕ => Real.log (k:ℝ)) hnat
    push_cast at hreal
    rw [Real.log_prod] at hreal
    · simpa [S, Real.log_pow] using hreal.symm
    · intro p h
      exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_primeFactors h).ne')
  have bound (p : ℕ) (h : p ∈ n.primesLE) :
      (n:ℝ) * (Real.log p / p) ≤ 2 * ((n.factorial.factorization p:ℝ)*Real.log p) := by
    obtain ⟨hle,hp⟩ := Nat.mem_primesLE.mp h
    have hdiv : 0 < n/p := Nat.div_pos hle hp.pos
    have hrem := Nat.mod_lt n hp.pos
    have he := Nat.mod_add_div n p
    have hsize : n ≤ (2*(n/p))*p := by nlinarith [Nat.mul_le_mul_left p hdiv]
    have hfac : n/p ≤ n.factorial.factorization p := by
      rw [Nat.factorization_factorial hp (show p.log n < p.log n + 2 by omega)]
      simpa using (Finset.single_le_sum (f := fun i => n/p^i) (fun i _ => Nat.zero_le _)
        (show 1 ∈ Finset.Ico 1 (p.log n + 2) by simp))
    have hnr : (n:ℝ) ≤ 2*(n.factorial.factorization p:ℝ)*p := by
      exact_mod_cast hsize.trans (Nat.mul_le_mul_right p (Nat.mul_le_mul_left 2 hfac))
    have hpr : (0:ℝ) < p := by exact_mod_cast hp.pos
    rw [← mul_div_assoc, div_le_iff₀ hpr]
    nlinarith [mul_le_mul_of_nonneg_right hnr (Real.log_natCast_nonneg p)]
  have hl : Real.log (n.factorial:ℝ) ≤ (n:ℝ)*Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.factorial_le_pow n)
  have ht : (n:ℝ)*(∑ p ∈ n.primesLE, Real.log p / p) ≤ (n:ℝ)*(2 * Real.log n) := by
    calc _ = _ := Finset.mul_sum ..
         _ ≤ _ := Finset.sum_le_sum bound
         _ = _ := (Finset.mul_sum ..).symm
         _ ≤ 2 * (∑ p ∈ S, (n.factorial.factorization p:ℝ)*Real.log p) := by
           gcongr
         _ ≤ _ := by rw [logfac]; linarith
  exact le_of_mul_le_mul_left ht (by exact_mod_cast hn)

private def primes (h : ℕ) := (2^h-1 : ℕ).primeFactors.filter (fun p => 2<p)
private def pool (m : ℕ) := (Finset.Icc 1 m).biUnion primes
private noncomputable def w (p : ℕ) : ℝ := 1/((p:ℝ)-2)
private noncomputable def weight (s : Finset ℕ) := ∏ p ∈ s, w p
private noncomputable def mass (s : Finset ℕ) := ∏ p ∈ s, (1+w p)
private noncomputable def ord (p : ℕ) := orderOf (2 : ZMod p)
private noncomputable def period (s : Finset ℕ) := s.lcm ord

private theorem info {m p : ℕ} (h : p ∈ pool m) : p.Prime ∧ 2 < p := by
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp h
  exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hj).1,(Finset.mem_filter.mp hj).2⟩

private theorem powpred (p h : ℕ) : ord p ∣ h ↔ p ∣ 2^h-1 := by
  have h1 : 1 ≤ (2:ℕ)^h := Nat.one_le_pow _ _ (by decide)
  rw [ord,orderOf_dvd_iff_pow_eq_one,← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1]
  simp [sub_eq_zero]

private theorem mem_pr {L p h : ℕ} (hp : p ∈ pool L) (hh : 0 < h) :
    p ∈ primes h ↔ ord p ∣ h := by
  have hpos : 1 < (2:ℕ)^h := one_lt_pow₀ (by decide) (by omega)
  simp only [primes,Finset.mem_filter,Nat.mem_primeFactors,powpred]
  have hi := info hp
  have : (2:ℕ)^h-1 ≠ 0 := by omega
  tauto

private theorem ord_pos {L p : ℕ} (hp : p ∈ pool L) : 0 < ord p := by
  obtain ⟨j,hj,hm⟩ := Finset.mem_biUnion.mp hp
  have h1 := (Finset.mem_Icc.mp hj).1
  exact Nat.pos_of_dvd_of_pos ((mem_pr hp h1).mp hm) h1

private theorem pool_card (m : ℕ) : (pool m).card ≤ m*m := by
  apply Finset.card_biUnion_le.trans
  calc _ ≤ ∑ _h ∈ Finset.Icc 1 m, m := by
         apply Finset.sum_le_sum
         intro h hh
         have h1 := (Finset.mem_Icc.mp hh).1
         let n : ℕ := 2^h-1
         have hpow : 1 < (2:ℕ)^h := one_lt_pow₀ (by decide) (by omega)
         have hprod := Nat.le_of_dvd (show 0<n by dsimp [n]; omega) (Nat.prod_primeFactors_dvd n)
         have h2 : 2^n.primeFactors.card ≤ ∏ p ∈ n.primeFactors,p := by
           calc _ = ∏ _p ∈ n.primeFactors, 2 := by simp
                _ ≤ _ := Finset.prod_le_prod fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
         have hpow' : 2^n.primeFactors.card ≤ (2:ℕ)^h := (h2.trans hprod).trans (Nat.sub_le ..)
         exact (Finset.card_filter_le ..).trans (((Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hpow').trans (Finset.mem_Icc.mp hh).2)
       _ = _ := by simp [Nat.card_Icc]

private theorem wpos {m p : ℕ} (hp : p ∈ pool m) : 0 ≤ w p := by
  have h : (2:ℝ)<p := by exact_mod_cast (info hp).2
  dsimp [w]; positivity

/-- Up to exponent 4^k the union has at most 16^k primes. The small primes
cost at most a fixed constant times 2^k; the rest cost a bounded factor. -/
private theorem pool_growth :
    ∃ C : ℝ, 0<C ∧ ∀ k : ℕ, mass (pool (4^k)) ≤ C*2^k := by
  obtain ⟨K,hK⟩ := exists_nat_gt (Real.exp 16+4)
  let D := ∑ p ∈ K.primesLE, |w p|
  refine ⟨Real.exp (D+2)*2,by positivity,?_⟩
  intro k
  let m : ℕ := 4^k
  let y : ℕ := 16^(k+1)
  let S := pool m
  have hy : 0<y := by dsimp [y]; positivity
  have hYr : (0:ℝ) < y := by exact_mod_cast hy
  have hm : m*m ≤ y := by
    dsimp [m,y]; rw [← mul_pow, pow_succ]; norm_num
  have point (p : ℕ) (_hp : p ∈ S) : w p ≤
      (if p ≤ K then |w p| else 0) +
      (if p ≤ y then Real.log p / p / 8 else 0) + 2/(y:ℝ) := by
    by_cases h : p ≤ K
    · rw [ite_eq_left h]
      apply (le_abs_self _).trans
      apply (le_add_of_nonneg_right ?_).trans (le_add_of_nonneg_right (by positivity))
      split_ifs <;> positivity
    rw [ite_eq_right h,zero_add]
    have hpr : (K:ℝ) < p := by exact_mod_cast (lt_of_not_ge h)
    have h4 : (4:ℝ)<p := by linarith [Real.exp_pos 16]
    have hw : w p ≤ 2/p := by
      dsimp [w]; apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr; linarith
    by_cases hpy : p ≤ y
    · rw [ite_eq_left hpy]
      have hlog : 16 ≤ Real.log p := by
        rw [← Real.exp_le_exp,Real.exp_log (by positivity : (0:ℝ)<p)]
        linarith
      apply hw.trans
      have hterm : (2:ℝ)/p ≤ Real.log p / p /8 := by
        rw [div_div]; apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg (α:=ℝ) p)]
      exact hterm.trans (le_add_of_nonneg_right (by positivity))
    · rw [ite_eq_right hpy,zero_add]
      exact hw.trans (div_le_div_of_nonneg_left (by norm_num) hYr (by exact_mod_cast (le_of_not_ge hpy)))
  have hs := Finset.sum_le_sum point
  simp only [Finset.sum_add_distrib,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,← Finset.sum_div] at hs
  have hD : (∑ p ∈ S.filter (fun p => p ≤ K), |w p|) ≤ D :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => Nat.mem_primesLE.mpr
      ⟨(Finset.mem_filter.mp hp).2,(info (Finset.mem_filter.mp hp).1).1⟩) (fun _ _ _ => abs_nonneg _)
  have hY : (∑ p ∈ S.filter (fun p => p ≤ y), Real.log p / p) ≤ 2*Real.log y := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (t:=y.primesLE) ?_ (by intros; positivity)).trans (prime_log_sum_le hy)
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Finset.mem_filter.mp hp).2,(info (Finset.mem_filter.mp hp).1).1⟩
  have hc : (S.card:ℝ) ≤ y := by exact_mod_cast (pool_card m).trans hm
  have hc' : (S.card:ℝ)*(2/y) ≤ 2 := by rw [← mul_div_assoc,div_le_iff₀ hYr]; linarith
  have hprod : mass S ≤ Real.exp (∑ p ∈ S,w p) := by
    rw [Real.exp_sum]; exact Finset.prod_le_prod₀ (fun p hp => by linarith [wpos hp])
      (fun p _ => by linarith [Real.add_one_le_exp (w p)])
  have hly : Real.log (y:ℝ) = (k+1:ℕ)*4*Real.log 2 := by
    dsimp [y]; push_cast; rw [Real.log_pow,show (16:ℝ)=2^4 by norm_num,Real.log_pow]; push_cast; ring
  apply hprod.trans
  calc _ ≤ Real.exp (D+2+((k+1:ℕ):ℝ)*Real.log 2) := Real.exp_le_exp.mpr (by linarith only [hs,hD,hY,hc',hly])
       _ = _ := by rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2),pow_succ]; ring

private theorem expansion (s : Finset ℕ) : mass s = ∑ t ∈ s.powerset, weight t :=
  Finset.prod_one_add s

private theorem period_pos {s : Finset ℕ} {L : ℕ} (h : s ⊆ pool L) : 0 < period s :=
  Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun _ hp => (ord_pos (h hp)).ne'))

private theorem contained {s : Finset ℕ} {L h : ℕ} (hs : s ⊆ pool L) (hh : 0<h) :
    s ⊆ primes h ↔ period s ∣ h := by
  rw [period,Finset.lcm_dvd_iff]
  exact ⟨fun h p hp => (mem_pr (hs hp) hh).mp (h hp),
    fun h p hp => (mem_pr (hs hp) hh).mpr (h p hp)⟩

private theorem hits (L d : ℕ) : ((Finset.Icc 1 L).filter (fun h => d ∣ h)).card = L/d := by
  rw [← Nat.card_multiples' L d]
  congr 1
  ext h
  simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
  omega

/-- Expand before averaging. Each subset occurs precisely at the positive
multiples of its period, including the empty subset with period one. -/
private theorem count_identity (L : ℕ) :
    ∑ h ∈ Finset.Icc 1 L, mass (primes h) =
      ∑ s ∈ (pool L).powerset, ((L/period s:ℕ):ℝ)*weight s := by
  classical
  let P := (pool L).powerset
  have row (h : ℕ) (hh : h ∈ Finset.Icc 1 L) : mass (primes h) =
      ∑ s ∈ P, if period s ∣ h then weight s else 0 := by
    rw [expansion,← Finset.sum_filter]
    congr 1
    ext s
    simp only [P,Finset.mem_filter,Finset.mem_powerset]
    have hsub : primes h ⊆ pool L := fun p hp => Finset.mem_biUnion.mpr ⟨h,hh,hp⟩
    constructor
    · intro hs
      exact ⟨hs.trans hsub,(contained (hs.trans hsub) (Finset.mem_Icc.mp hh).1).mp hs⟩
    · rintro ⟨hs,hd⟩
      exact (contained hs (Finset.mem_Icc.mp hh).1).mpr hd
  rw [Finset.sum_congr rfl row, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,hits]

private theorem average : ∃ A : ℝ, 0<A ∧ ∀ L : ℕ,
    ∑ h ∈ Finset.Icc 1 L, mass (primes h) ≤ A*(L:ℝ) := by
  classical
  obtain ⟨C,hC,growth⟩ := pool_growth
  refine ⟨5*C,by positivity,?_⟩
  intro L
  let P := (pool L).powerset
  let U (k : ℕ) := P.filter (fun s => period s ≤ 4^k)
  let v (s : Finset ℕ) := ((L/period s:ℕ):ℝ)*weight s
  have wt {m : ℕ} {s : Finset ℕ} (hs : s ⊆ pool m) : 0 ≤ weight s :=
    Finset.prod_nonneg fun p hp => wpos (hs hp)
  have band {S : Finset (Finset ℕ)} {b k : ℕ} (hb : 0 < b) (hS : S ⊆ U k)
      (hlo : ∀ s ∈ S, b ≤ period s) :
      ∑ s ∈ S, v s ≤ ((L:ℝ)/b)*(C*(2:ℝ)^k) := by
    have sub (s : Finset ℕ) (hs : s ∈ S) : s ⊆ pool L :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp (hS hs)).1
    have sub' : S ⊆ (pool (4^k)).powerset := by
      intro s hs
      apply Finset.mem_powerset.mpr
      have hp := period_pos (sub s hs)
      have hupper := (Finset.mem_filter.mp (hS hs)).2
      have hin := (contained (sub s hs) hp).mpr (dvd_refl (period s))
      intro p hps
      exact Finset.mem_biUnion.mpr ⟨period s,Finset.mem_Icc.mpr ⟨hp,hupper⟩,hin hps⟩
    calc _ ≤ ∑ s ∈ S, ((L:ℝ)/b)*weight s := by
           apply Finset.sum_le_sum
           intro s hs
           apply mul_le_mul_of_nonneg_right _ (wt (sub s hs))
           exact Nat.cast_div_le.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg L)
             (by exact_mod_cast hb) (by exact_mod_cast hlo s hs))
         _ = ((L:ℝ)/b) * ∑ s ∈ S, weight s := (Finset.mul_sum ..).symm
         _ ≤ _ := by
           apply mul_le_mul_of_nonneg_left _ (by positivity)
           apply (Finset.sum_le_sum_of_subset_of_nonneg sub'
             (fun s hs _ => wt (Finset.mem_powerset.mp hs))).trans
           rw [← expansion]; exact growth k
  have cumulative (k : ℕ) : ∑ s ∈ U k, v s ≤ C*L*(5-4/(2:ℝ)^k) := by
    induction k with
    | zero =>
      have h := band (k:=0) (b:=1) (S:=U 0) (by decide) (fun _ h => h)
        (fun s hs => period_pos (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1))
      norm_num [mul_comm] at h ⊢
      exact h
    | succ k ih =>
      let T := U (k+1) \ U k
      have hu : U k ⊆ U (k+1) := by
        intro s hs
        obtain ⟨hp,hl⟩ := Finset.mem_filter.mp hs
        exact Finset.mem_filter.mpr ⟨hp,hl.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩
      have h := band (k:=k+1) (b:=4^k) (S:=T) (by positivity) Finset.sdiff_subset (by
        intro s hs
        obtain ⟨hmem,hn⟩ := Finset.mem_sdiff.mp hs
        have hP := (Finset.mem_filter.mp hmem).1
        exact le_of_lt (lt_of_not_ge fun hle => hn (Finset.mem_filter.mpr ⟨hP,hle⟩)))
      have he : (∑ s ∈ T, v s) + (∑ s ∈ U k, v s) = ∑ s ∈ U (k+1), v s := by
        exact Finset.sum_sdiff hu
      rw [← he]
      apply (add_le_add h ih).trans_eq
      push_cast
      rw [show (4:ℝ)^k = (2:ℝ)^k*(2:ℝ)^k by rw [← mul_pow]; norm_num,pow_succ]
      field_simp; ring
  rw [count_identity]
  change (∑ s ∈ P, v s) ≤ _
  have eq : ∑ s ∈ U L, v s = ∑ s ∈ P, v s := by
    apply Finset.sum_subset (Finset.filter_subset ..)
    intro s hs hnot
    have hlt : 4^L < period s := lt_of_not_ge fun h => hnot (Finset.mem_filter.mpr ⟨hs,h⟩)
    have hL := L.lt_two_pow_self.trans_le (Nat.pow_le_pow_left (by decide : 2 ≤ 4) L)
    simp [v,Nat.div_eq_of_lt (hL.trans hlt)]
  rw [← eq]
  have hrem := mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg (α:=ℝ) L))
    (show 0 ≤ 4/(2:ℝ)^L by positivity)
  exact (cumulative L).trans (by linarith only [hrem])

end BinaryShiftCost

theorem Conjectures.Goldbach.BinaryShiftSieveCost :
    let A := fun h : ℕ => ∏ p ∈ (2^h-1 : ℕ).primeFactors.filter (fun p => 2<p), (1 + 1/((p:ℝ)-2));
    ∃ C : ℝ, 0<C ∧ ∀ L : ℕ, (∑ h ∈ Finset.Icc 1 L, A h) ≤ C*(L:ℝ) :=
  BinaryShiftCost.average
