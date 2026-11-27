import Mathlib

noncomputable section

namespace Conjectures.Goldbach.PacketShortPeriodLargePrimeWeight_aux

def gridQ (n : ℕ) := (Nat.log 2 (n+2))^2

abbrev lowOrderTest (n q : ℕ) := q % 2 = 1 ∧
  ((Finset.Icc 1 ((Nat.log 2 (gridQ n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty

abbrev smoothTest (n q : ℕ) :=
  ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (gridQ n))^8
def denominatorWeight (n q : ℕ) := min (1:ℝ) ((q:ℝ)/(gridQ n:ℝ))/(q.totient:ℝ)

theorem periodPrimeBudget (H Y : ℕ) (hY : 0<Y) :
    (∑ j ∈ Finset.Icc 1 H, ∑ p ∈ ((2^j-1:ℕ).primeFactors.filter (fun p => Y<p)),
      1/((p:ℝ)-1)) ≤ (H:ℝ)^2/Y := by
  have one (j : ℕ) (hj : j ∈ Finset.Icc 1 H) :
      (∑ p ∈ ((2^j-1:ℕ).primeFactors.filter (fun p => Y<p)), 1/((p:ℝ)-1)) ≤ (H:ℝ)/(Y:ℝ) := by
    let M : ℕ := 2^j-1
    let primes := M.primeFactors
    let T := primes.filter (fun p => Y<p)
    have jpos := (Finset.mem_Icc.mp hj).1
    have jle := (Finset.mem_Icc.mp hj).2
    have Mpos : 0<M := by
      have two : 2 ≤ 2^j := by simpa using Nat.pow_le_pow_right (by decide : 0<2) jpos
      dsimp [M]; omega
    have hc : 2^primes.card ≤ M := by
      calc
        _ = ∏ _p ∈ primes, (2:ℕ) := by simp
        _ ≤ ∏ p ∈ primes, p := Finset.prod_le_prod' (fun p h => (Nat.prime_of_mem_primeFactors h).two_le)
        _ ≤ M := Nat.le_of_dvd Mpos (Nat.prod_primeFactors_dvd M)
    have card : primes.card ≤ j := by
      by_contra! hh
      have lower := Nat.pow_le_pow_right (by decide : 0<2) (show j+1 ≤ primes.card by omega)
      rw [pow_succ] at lower
      dsimp [M] at hc
      omega
    have cr : (T.card:ℝ) ≤ (H:ℝ) := by exact_mod_cast
      ((Finset.card_le_card (Finset.filter_subset _ primes)).trans card).trans jle
    change (∑ p ∈ T, _) ≤ _
    calc
      _ ≤ ∑ _p ∈ T, 1/(Y:ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hi : (Y:ℝ)+1 ≤ (p:ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = (T.card:ℝ)/(Y:ℝ) := by simp [div_eq_mul_inv]
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 H, (H:ℝ)/(Y:ℝ) := Finset.sum_le_sum one
    _ = _ := by simp [pow_two] <;> ring

theorem fractionProduct (S : Finset ℕ) (hs : ∀ p ∈ S, 2≤p) :
    (∏ p ∈ S, (p:ℝ)/((p:ℝ)-1)) ≤ (S.card:ℝ)+1 := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hmax ih =>
    have ha := hs a (Finset.mem_insert_self ..)
    have old (p : ℕ) (hp : p∈S) := hs p (Finset.mem_insert_of_mem hp)
    have ha' : 0 < (a:ℝ)-1 := by
      have h : (2:ℝ) ≤ a := by exact_mod_cast ha
      linarith
    have notMem : a ∉ S := fun h => (lt_irrefl a) (hmax a h)
    have sub : S ⊆ Finset.Ico 2 a := fun p hp => Finset.mem_Ico.mpr ⟨old p hp,hmax p hp⟩
    have count := Finset.card_le_card sub
    rw [Nat.card_Ico] at count
    have cr : (S.card:ℝ)+2 ≤ (a:ℝ) := by exact_mod_cast (show S.card+2≤a by omega)
    rw [Finset.prod_insert notMem,Finset.card_insert_of_notMem notMem,Nat.cast_add,Nat.cast_one]
    apply (mul_le_mul_of_nonneg_left (ih old) (div_nonneg (Nat.cast_nonneg _) ha'.le)).trans
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ ha').mpr
    linarith

theorem totientLogLower (q : ℕ) (hq : 0<q) :
    (q:ℝ)/(q.totient:ℝ) ≤ (Nat.log 2 q:ℝ)+1 := by
  let S := q.primeFactors
  have hs (p : ℕ) (hp : p∈S) := (Nat.prime_of_mem_primeFactors hp).two_le
  have card : S.card ≤ Nat.log 2 q := by
    apply Nat.le_log_of_pow_le (by decide)
    calc
      _ = ∏ _p ∈ S, (2:ℕ) := by simp
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod' hs
      _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hf : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have id : (q:ℝ)/(q.totient:ℝ) = ∏ p ∈ S, (p:ℝ)/((p:ℝ)-1) := by
    rw [Finset.prod_div_distrib]
    have pos : 0 < ∏ p ∈ S, ((p:ℝ)-1) := Finset.prod_pos (fun p hp => by
      have h : (2:ℝ)≤p := by exact_mod_cast hs p hp
      linarith)
    apply (div_eq_div_iff hf.ne' pos.ne').mpr
    have formula := congrArg (fun k : ℕ => (k:ℝ)) (Nat.totient_mul_prod_primeFactors q)
    simp only [Nat.cast_mul,Nat.cast_prod] at formula
    change (q:ℝ)*_ = _*(q.totient:ℝ)
    rw [mul_comm _ (q.totient:ℝ)]
    dsimp [S]
    rw [formula]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (by have h := hs p hp; omega),Nat.cast_one]
  rw [id]
  exact (fractionProduct S hs).trans (by exact_mod_cast (show S.card+1≤Nat.log 2 q+1 by omega))

theorem harmonicBlock (k : ℕ) :
    (∑ m ∈ Finset.range (2^k), 1/((m:ℝ)+1)) ≤ (k:ℝ)+1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
    have block : (∑ j ∈ Finset.range (2^k), 1/(((2^k+j:ℕ):ℝ)+1)) ≤ 1 := by
      calc
        _ ≤ ∑ _j ∈ Finset.range (2^k), 1/((2:ℝ)^k) := by
          apply Finset.sum_le_sum
          intro j _
          apply one_div_le_one_div_of_le (by positivity)
          push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]
        _ = _ := by simp
    push_cast at block ⊢
    linarith only [ih,block]

theorem reciprocalTotientLogBound (X : ℕ) (hX : 0<X) :
    (∑ m ∈ Finset.Icc 1 X, 1/(m.totient:ℝ)) ≤ ((Nat.log 2 X:ℝ)+2)^2 := by
  let k := Nat.log 2 X
  have idx : Finset.Icc 1 X = (Finset.range X).map (addRightEmbedding 1) := by
    ext m
    simp only [Finset.mem_Icc,Finset.mem_map,Finset.mem_range,addRightEmbedding_apply]
    constructor
    · intro h; exact ⟨m-1,by omega,by omega⟩
    · rintro ⟨j,h,rfl⟩; omega
  have upper := (Nat.lt_pow_succ_log_self (by decide : 1<2) X).le
  have harm : (∑ m ∈ Finset.range X, 1/((m:ℝ)+1)) ≤ (k:ℝ)+2 := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono upper) (fun m _ _ => by positivity)).trans
    convert harmonicBlock (k+1) using 1 <;> push_cast <;> ring
  rw [idx,Finset.sum_map]
  calc
    _ ≤ ∑ j ∈ Finset.range X, ((k:ℝ)+1)*(1/((j:ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have le : j+1 ≤ X := Finset.mem_range.mp hj
      have hk : Nat.log 2 (j+1) ≤ k := Nat.log_mono_right le
      have b := totientLogLower (j+1) (by omega)
      have h : (((j+1:ℕ):ℝ)/((j+1).totient:ℝ)) ≤ (k:ℝ)+1 := b.trans (by exact_mod_cast (Nat.add_le_add_right hk 1))
      change 1/((j+1).totient:ℝ) ≤ _
      rw [mul_one_div]
      apply (le_div_iff₀ (by positivity)).mpr
      push_cast at h
      simpa only [one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm] using h
    _ = ((k:ℝ)+1)*_ := (Finset.mul_sum ..).symm
    _ ≤ ((k:ℝ)+1)*((k:ℝ)+2) := mul_le_mul_of_nonneg_left harm (by positivity)
    _ ≤ _ := by dsimp [k]; nlinarith only [Nat.cast_nonneg (α := ℝ) (Nat.log 2 X)]

theorem chargeWitnesses {α β : Type*} [DecidableEq β]
    (S : Finset β) (T : Finset α) (key : α → β) (w : β → ℝ) (v : α → ℝ)
    (pos : ∀ a∈T, 0≤v a) (charge : ∀ b∈S, ∃ a∈T, key a=b ∧ w b≤v a) :
    (∑ b ∈ S, w b) ≤ ∑ a ∈ T, v a := by
  calc
    _ ≤ ∑ b ∈ S, ∑ a ∈ T, if key a=b then v a else 0 := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨a,ha,e,h⟩ := charge b hb
      apply h.trans
      simpa only [e,if_true] using Finset.single_le_sum
        (s := T) (f := fun x => if key x=b then v x else 0)
        (fun x hx => by split <;> first | exact pos x hx | exact le_rfl) ha
    _ = ∑ a ∈ T, ∑ b ∈ S, if key a=b then v a else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : key a ∈ S <;> simp [h,pos a ha]

theorem largePeriodWeightFinite (n : ℕ) :
    (∑ q ∈ (Finset.Icc 1 ((gridQ n)^2)).filter (fun q => lowOrderTest n q ∧ ¬smoothTest n q),
      denominatorWeight n q) ≤
      (∑ m ∈ Finset.Icc 1 ((gridQ n)^2), 1/(m.totient:ℝ)) *
        (((1+Nat.log 2 (gridQ n):ℕ):ℝ)^4 / ((1+Nat.log 2 (gridQ n):ℕ):ℝ)^8) := by
  classical
  let u := 1+Nat.log 2 (gridQ n)
  let H := u^2
  let Y := u^8
  let X := (gridQ n)^2
  let D := Finset.Icc 1 X
  let J := Finset.Icc 1 H
  let Ps := fun j : ℕ => (2^j-1:ℕ).primeFactors.filter (fun p => Y<p)
  let T : Finset (Σ _j : ℕ, ℕ × ℕ) := J.sigma (fun j => Ps j ×ˢ D)
  let S := D.filter (fun q => lowOrderTest n q ∧ ¬smoothTest n q)
  let v := fun a : (Σ _j : ℕ, ℕ × ℕ) => (1/((a.2.1:ℝ)-1))*(1/(a.2.2.totient:ℝ))
  let M := ∑ m ∈ D, 1/(m.totient:ℝ)
  have vpos (a : Σ _j : ℕ, ℕ × ℕ) (ha : a∈T) : 0≤v a := by
    have h := (Finset.mem_product.mp (Finset.mem_sigma.mp ha).2).1
    have hp := (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp h).1).two_le
    have hp' : (2:ℝ)≤a.2.1 := by exact_mod_cast hp
    exact mul_nonneg (one_div_nonneg.mpr (by linarith)) (one_div_nonneg.mpr (Nat.cast_nonneg _))
  have witnesses (q : ℕ) (hq : q∈S) : ∃ a∈T, a.2.1*a.2.2=q ∧ denominatorWeight n q≤v a := by
    obtain ⟨hd,hshort,hnsm⟩ := Finset.mem_filter.mp hq
    change ¬∀ p ∈ q.primeFactors, p≤Y at hnsm
    push_neg at hnsm
    obtain ⟨p,hp,hY⟩ := hnsm
    obtain ⟨j,hj⟩ := hshort.2
    obtain ⟨hjrange,dvd⟩ := Finset.mem_filter.mp hj
    have hj' : j ∈ J := by simpa only [J,H,u,Nat.add_comm 1] using hjrange
    have pPrime := Nat.prime_of_mem_primeFactors hp
    have dp := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨m,eq⟩ := dp
    have qpos : 0<q := (Finset.mem_Icc.mp hd).1
    have mpos : 0< m := Nat.pos_of_ne_zero (fun e => (Nat.ne_of_gt qpos) (by simp [eq,e]))
    have mQ : m≤q := Nat.le_of_dvd qpos ⟨p,by simpa only [mul_comm] using eq⟩
    have hpos : 0<(2^j-1:ℕ) := by
      have two : 2≤2^j := by simpa using Nat.pow_le_pow_right (by decide : 0<2) (Finset.mem_Icc.mp hj').1
      omega
    have pm : p∈Ps j := Finset.mem_filter.mpr ⟨pPrime.mem_primeFactors ((Nat.dvd_of_mem_primeFactors hp).trans dvd) hpos.ne',hY⟩
    refine ⟨⟨j,(p,m)⟩, Finset.mem_sigma.mpr ⟨hj', Finset.mem_product.mpr ⟨pm,Finset.mem_Icc.mpr ⟨mpos,mQ.trans (Finset.mem_Icc.mp hd).2⟩⟩⟩,eq.symm, ?_⟩
    have phip : 0<(p.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr pPrime.pos
    have phim : 0<(m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr mpos
    have phi : (p.totient:ℝ)*(m.totient:ℝ) ≤ (q.totient:ℝ) := by rw [eq]; exact_mod_cast Nat.totient_super_multiplicative p m
    have phiq : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr qpos
    have primeId : (p.totient:ℝ)=(p:ℝ)-1 := by
      rw [Nat.totient_prime pPrime,Nat.cast_sub (by have := pPrime.two_le; omega),Nat.cast_one]
    calc
      _ ≤ 1/(q.totient:ℝ) := div_le_div_of_nonneg_right (min_le_left ..) phiq.le
      _ ≤ 1/((p.totient:ℝ)*(m.totient:ℝ)) := one_div_le_one_div_of_le (mul_pos phip phim) phi
      _ = _ := by dsimp [v]; rw [primeId]; simp only [one_div,mul_inv_rev,mul_comm]
  have eq : (∑ a ∈ T, v a) = M*(∑ j ∈ J, ∑ p ∈ Ps j, 1/((p:ℝ)-1)) := by
    dsimp only [T]
    rw [Finset.sum_sigma,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_product,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [v]
    rw [← Finset.mul_sum,mul_comm]
  have ub := periodPrimeBudget H Y (by dsimp [H,Y,u]; positivity)
  have conv : (H:ℝ)^2/(Y:ℝ) = (u:ℝ)^4/(u:ℝ)^8 := by dsimp [H,Y]; push_cast; ring
  rw [conv] at ub
  apply (chargeWitnesses S T (fun a => a.2.1*a.2.2) (denominatorWeight n) v vpos witnesses).trans
  rw [eq]
  exact mul_le_mul_of_nonneg_left ub (Finset.sum_nonneg fun _ _ => by positivity)

theorem shortPeriodLargePrimeWeight : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
    (∑ q ∈ (Finset.Icc 1 ((gridQ n)^2)).filter (fun q => lowOrderTest n q ∧ ¬smoothTest n q),
      denominatorWeight n q) ≤ ε := by
  intro ε hε
  obtain ⟨M,hM⟩ := exists_nat_ge (16/ε)
  refine ⟨2^(2^M), ?_⟩
  intro n hn
  let Q := gridQ n
  let u := 1+Nat.log 2 Q
  have hlog : 2^M ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have hQ : 2^M ≤ Q := by dsimp [Q,gridQ]; nlinarith [Nat.le_mul_self (Nat.log 2 (n+2))]
  have qpos : 0<Q := lt_of_lt_of_le (by positivity : 0<2^M) hQ
  have hu : M ≤ u := by have h := Nat.le_log_of_pow_le (by decide : 1<2) hQ; dsimp [u]; omega
  have u1 : (1:ℝ) ≤ u := by exact_mod_cast (show 1≤u by dsimp [u]; omega)
  have upos : (0:ℝ)<u := by linarith
  have cap := Nat.lt_pow_succ_log_self (by decide : 1<2) Q
  have cap' : Q < 2^u := by simpa only [u,Nat.add_comm 1] using cap
  have both : Q^2 < 2^(2*u) := by
    rw [mul_comm 2 u,pow_mul]
    exact Nat.pow_lt_pow_left cap' (by decide)
  have hL : Nat.log 2 (Q^2) < 2*u := by
    by_contra! hh
    have power := Nat.pow_le_pow_right (by decide : 0<2) hh
    have b := Nat.pow_log_le_self 2 (by positivity : Q^2≠0)
    omega
  have hR : (Nat.log 2 (Q^2):ℝ)+2 ≤ 4*(u:ℝ) := by exact_mod_cast (show Nat.log 2 (Q^2)+2≤4*u by omega)
  have hb := (reciprocalTotientLogBound (Q^2) (by positivity)).trans (pow_le_pow_left₀ (by positivity) hR 2)
  apply (largePeriodWeightFinite n).trans
  change _ * ((u:ℝ)^4/(u:ℝ)^8) ≤ ε
  apply (mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ (u:ℝ)^4/(u:ℝ)^8)).trans
  have limit : 16 ≤ ε*(u:ℝ) := by
    have h := (div_le_iff₀ hε).mp (hM.trans (by exact_mod_cast hu : (M:ℝ) ≤ u))
    linarith
  calc
    _ = 16/(u:ℝ)^2 := by field_simp <;> ring
    _ ≤ 16/(u:ℝ) := div_le_div_of_nonneg_left (by norm_num) upos (by nlinarith [sq_nonneg ((u:ℝ)-1)])
    _ ≤ ε := (div_le_iff₀ upos).mpr limit

end Conjectures.Goldbach.PacketShortPeriodLargePrimeWeight_aux

theorem Conjectures.Goldbach.PacketShortPeriodLargePrimeWeight : let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty; let smooth := fun n q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^8; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q ∧ ¬smooth n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ))/(Nat.totient q:ℝ)) ≤ ε := by
  intro Q o smooth ε hε
  exact Conjectures.Goldbach.PacketShortPeriodLargePrimeWeight_aux.shortPeriodLargePrimeWeight ε hε
