import Mathlib
import Conjectures.Cuts.Taskba08eb3c3998330911d98843


namespace SharpBaseLimit
open Finset Filter Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc
open scoped Topology
noncomputable section

def base (q : ℕ) : ℝ := (coefficient q 2).re

def factor (p : ℕ) : ℝ := if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p:ℝ)-1)^2 else 1

private theorem cz (m : ℕ) : coefficient 0 m=0 := by simp [coefficient]

private theorem imag (q : ℕ) : (coefficient q 2).im=0 := by
  rcases Nat.eq_zero_or_pos q with rfl|qp
  · simp [cz]
  · exact Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc.coefficient_im_zero 2 qp

theorem base_one : base 1 = 1 := by simp [base,coefficient_one]

theorem base_zero : base 0 = 0 := by simp [base,cz]

theorem base_mul {i j : ℕ} (sep : i.Coprime j) : base (i*j)=base i*base j := by
  rcases Nat.eq_zero_or_pos i with rfl|ip
  · simp [base_zero]
  rcases Nat.eq_zero_or_pos j with rfl|jp
  · simp [base_zero]
  simp [base,coefficient_mul ip jp sep,Complex.mul_re,imag]

private theorem prime_base {p : ℕ} (hp : p.Prime) :
    base p=if p=2 then 1 else -(1/((p:ℝ)-1)^2) := by
  unfold base
  rw [coefficient_prime hp,Complex.ofReal_re]
  by_cases two:p=2
  · subst p;norm_num [localCoefficient]
  · have nd: ¬p ∣ 2 := fun d=>two ((Nat.dvd_prime Nat.prime_two).mp d |>.resolve_left hp.ne_one)
    simp [localCoefficient,two,nd]

private theorem base_higher {p : ℕ} (hp : p.Prime) (k : ℕ) : base (p^(k+2))=0 := by simp [base,coefficient_higher_power hp]

theorem weighted_bound (q : ℕ) : |base q| *(q.totient:ℝ)^2≤1 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => simp [base_zero]
  | one => simp [base_one]
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero =>
        rw [pow_one,prime_base hp,Nat.totient_prime hp,Nat.cast_sub hp.one_le,Nat.cast_one]
        by_cases e:p=2
        · subst p;norm_num
        · have pp:(1:ℝ)<p := by exact_mod_cast hp.one_lt
          rw [ite_eq_right e,abs_neg,abs_of_nonneg (by positivity),div_mul_cancel₀ _ (by positivity)]
      | succ k =>
        rw [base_higher hp k,abs_zero,zero_mul];norm_num
  | coprime a b ha hb sep ia ib =>
    rw [base_mul sep,abs_mul,Nat.totient_mul sep,Nat.cast_mul,mul_pow]
    calc _ = (|base a| *(a.totient:ℝ)^2)*(|base b| *(b.totient:ℝ)^2) := by ring
         _ ≤ 1*1 := mul_le_mul ia ib (by positivity) (by norm_num)
         _ = _ := one_mul _

/- The finite harmonic-product and reciprocal-totient estimates are adapted from
DeepThreeQuartersExceptionalZeroCriterion, based on Goldbach Research PR #1810. -/
private theorem harm_prod (s : Finset ℕ) :
    (∀ p ∈ s, 2 ≤ p) → ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1) ≤ (s.card : ℝ) + 1 := by
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s hlt ih =>
    intro h2
    have ha : a ∉ s := fun h => lt_irrefl _ (hlt a h)
    have ha2 : 2 ≤ a := h2 a (Finset.mem_insert_self _ _)
    have ih' := ih (fun p hp => h2 p (Finset.mem_insert_of_mem hp))
    have hsub : s ⊆ Finset.Ico 2 a := by
      intro x hx
      rw [Finset.mem_Ico]
      exact ⟨h2 x (Finset.mem_insert_of_mem hx), hlt x hx⟩
    have hk : s.card ≤ a - 2 := by
      have := Finset.card_le_card hsub
      simpa using this
    have hk' : (s.card : ℝ) + 2 ≤ a := by
      have : s.card + 2 ≤ a := by omega
      exact_mod_cast this
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    push_cast
    have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha2
    have hpos : (0:ℝ) < (a:ℝ) - 1 := by linarith
    have hP : 0 ≤ ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1) := by
      apply Finset.prod_nonneg
      intro p hp
      have : (2:ℝ) ≤ p := by exact_mod_cast h2 p (Finset.mem_insert_of_mem hp)
      apply div_nonneg <;> linarith
    have hfrac : (a:ℝ) / ((a:ℝ) - 1) * ((s.card : ℝ) + 1) ≤ (s.card : ℝ) + 1 + 1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith [Nat.cast_nonneg (α := ℝ) s.card]
    calc (a:ℝ) / ((a:ℝ) - 1) * ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1)
        ≤ (a:ℝ) / ((a:ℝ) - 1) * ((s.card : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left ih' (by positivity)
      _ ≤ _ := hfrac

theorem totient_ratio_le_four_log (q : ℕ) (hq : 0 < q) :
    (q:ℝ) / (q.totient : ℝ) ≤ 4 * Real.log ((q + 2 : ℕ) : ℝ) := by
  have hprime : ∀ p ∈ q.primeFactors, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hh := harm_prod q.primeFactors hprime
  have hid := Nat.totient_mul_prod_primeFactors q
  have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hP : (0:ℝ) < ∏ p ∈ q.primeFactors, (p:ℝ) := by
    apply Finset.prod_pos
    intro p hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hprime p hp
    linarith
  have hP1 : (0:ℝ) < ∏ p ∈ q.primeFactors, ((p:ℝ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hprime p hp
    linarith
  have hid' : (q.totient : ℝ) * ∏ p ∈ q.primeFactors, (p:ℝ)
      = (q:ℝ) * ∏ p ∈ q.primeFactors, ((p:ℝ) - 1) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hid
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [this]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
    simp
  have heq : (q:ℝ) / (q.totient : ℝ) = ∏ p ∈ q.primeFactors, (p:ℝ) / ((p:ℝ) - 1) := by
    rw [Finset.prod_div_distrib, div_eq_div_iff hφ.ne' hP1.ne']
    linarith
  have hpow : 2 ^ q.primeFactors.card ≤ q := by
    calc 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
          Finset.pow_card_le_prod _ _ _ hprime
      _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hlog2 : (1:ℝ) / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at this
    linarith
  have hk : (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log ((q + 2 : ℕ) : ℝ) := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    have : ((2 ^ q.primeFactors.card : ℕ) : ℝ) ≤ ((q + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 ^ q.primeFactors.card ≤ q + 2)
    simpa using this
  have hL : (1:ℝ) / 2 ≤ Real.log ((q + 2 : ℕ) : ℝ) := by
    refine hlog2.trans (Real.log_le_log (by norm_num) ?_)
    exact_mod_cast (by omega : 2 ≤ q + 2)
  have hc : (0:ℝ) ≤ q.primeFactors.card := Nat.cast_nonneg _
  rw [heq]
  have : (q.primeFactors.card : ℝ) * (1 / 2) ≤ q.primeFactors.card * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2 hc
  linarith

/-- A modulus-uniform bound for every positive exponent, with an explicit constant. -/
theorem totient_ratio_le_rpow {ε : ℝ} (hε : 0 < ε) (q : ℕ) (hq : 0 < q) :
    (q : ℝ) / (q.totient : ℝ) ≤ (8 + 4 / ε) * (q : ℝ) ^ ε := by
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpow : 1 ≤ (q : ℝ) ^ ε := Real.one_le_rpow hq₁ hε.le
  have hlog : Real.log ((q + 2 : ℕ) : ℝ) ≤ Real.log 3 + Real.log q := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have hthree : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
  calc
    (q : ℝ) / (q.totient : ℝ) ≤ 4 * Real.log ((q + 2 : ℕ) : ℝ) :=
      totient_ratio_le_four_log q hq
    _ ≤ 8 + 4 * ((q : ℝ) ^ ε / ε) := by
      linarith [Real.log_natCast_le_rpow_div q hε]
    _ ≤ 8 * (q : ℝ) ^ ε + 4 * ((q : ℝ) ^ ε / ε) := by linarith
    _ = (8 + 4 / ε) * (q : ℝ) ^ ε := by ring

private theorem totient_weight {d : ℕ} (hd : 0 < d) :
    1/(d.totient:ℝ)^2 ≤ 576 * (d:ℝ)^(-(3/2):ℝ) := by
  have h := totient_ratio_le_rpow (show (0:ℝ)<1/4 by norm_num) d hd
  norm_num at h
  have dp : (0:ℝ)<d := by exact_mod_cast hd
  have hp : (0:ℝ)<d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have invbound : 1/(d.totient:ℝ) ≤ 24*(d:ℝ)^(-(3/4):ℝ) := by
    calc
      _ = ((d:ℝ)/d.totient)/d := by field_simp
      _ ≤ (24*(d:ℝ)^(1/4:ℝ))/d := div_le_div_of_nonneg_right h dp.le
      _ = _ := by rw [show (-(3/4):ℝ)=1/4-1 by norm_num,Real.rpow_sub dp,Real.rpow_one];ring
  have square := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1/d.totient) invbound 2
  rw [div_pow,one_pow,mul_pow,← Real.rpow_mul_natCast dp.le] at square
  norm_num at square ⊢
  exact square

theorem abs_summable : Summable (fun q=>‖base q‖) := by
  have sr : Summable (fun d:ℕ=>(d:ℝ)^(-(3/2):ℝ)) := Real.summable_nat_rpow.mpr (by norm_num)
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ (sr.mul_left (576:ℝ))
  intro q
  rcases Nat.eq_zero_or_pos q with rfl|qp
  · simp [base_zero,Real.zero_rpow (by norm_num : (-(3/2):ℝ)≠0)]
  · have hφ:(0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr qp
    exact ((le_div_iff₀ (sq_pos_of_pos hφ)).mpr (weighted_bound q)).trans (totient_weight qp)

private theorem local_sum {p : ℕ} (hp : p.Prime) :
    (∑' e:ℕ,base (p^e))=1+base p := by
  rw [tsum_eq_sum (s:={0,1})]
  · simp [base_one]
  · intro e he
    have h:2≤e := by by_contra! z; interval_cases e <;> simp_all
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm,base_higher hp]

theorem euler : (∑' q:ℕ,base q)=2*∏' p:ℕ,factor p := by
  have eul := EulerProduct.eulerProduct_hasProd_mulIndicator base_one (fun {_ _} h=>base_mul h)
    abs_summable base_zero
  have half : HasProd (fun p:ℕ=> if p=2 then (1/2:ℝ) else 1) (1/2) := by
    simpa only [eq_comm] using (hasProd_ite_eq (2:ℕ) (1/2:ℝ))
  have product := half.mul eul
  have same : (fun p:ℕ=> (if p=2 then (1/2:ℝ) else 1) *
      Set.mulIndicator {p:ℕ|p.Prime} (fun p=>∑' e:ℕ,base (p^e)) p) = factor := by
    funext p
    by_cases hp:p.Prime
    · rw [Set.mulIndicator_of_mem hp,local_sum hp,prime_base hp]
      by_cases two:p=2
      · subst p;norm_num [factor]
      · have gt : 2<p := lt_of_le_of_ne hp.two_le (Ne.symm two)
        simp [factor,hp,two,gt,sub_eq_add_neg]
    · have nt : p≠2 := by rintro rfl;exact hp Nat.prime_two
      rw [Set.mulIndicator_of_notMem hp];simp [factor,hp,nt]
  change HasProd (fun p:ℕ=> (if p=2 then (1/2:ℝ) else 1) *
      Set.mulIndicator {p:ℕ|p.Prime} (fun p=>∑' e:ℕ,base (p^e)) p) _ at product
  rw [same] at product
  rw [product.tprod_eq];ring

theorem base_limit : Tendsto (fun L : ℕ=>∑q∈Icc 1 L,(coefficient q 2).re) atTop
    (𝓝 (2*∏' p:ℕ,if Nat.Prime p ∧ 2<p then 1-1/((p:ℝ)-1)^2 else 1)) := by
  change Tendsto (fun L : ℕ=>∑q∈Icc 1 L,base q) atTop (𝓝 (2*∏' p:ℕ,factor p))
  rw [←euler]
  have h:=abs_summable.of_norm.hasSum.tendsto_sum_nat
  have hs := h.comp (tendsto_add_atTop_nat 1)
  apply hs.congr'
  filter_upwards with L
  change (∑q∈range (L+1),base q)=_
  rw [show range (L+1)=insert 0 (Icc 1 L) by ext q;simp;omega,sum_insert (by simp),base_zero,zero_add]
end
end SharpBaseLimit

namespace SharpArcTransfer
open Finset Filter MeasureTheory Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachEstermannKernel
noncomputable section

theorem model_tail (N B m:ℕ) (np:0<N) (bp:1≤B) (half:2*B^3≤N) (ml:N ≤ m) (mu:m≤2*N):
    ‖GoldbachBa08Approx.scaledModel N m B (B^3)-
      (((2*N-m:ℕ):ℂ)+1)*∑q∈Icc 1 B,GoldbachMajorArc.coefficient q m‖≤8*(N:ℝ)/B:=by
  let v:ℂ:=((2*N-m:ℕ):ℂ)+1
  let C (q:ℕ):=GoldbachMajorArc.coefficient q m
  let w (q:ℕ):ℝ:=(B:ℝ)^3/((q:ℝ)*N)
  let J (q:ℕ):ℂ:=∫t in -(w q)..w q,twisted N m t
  have br:0<(B:ℝ):=by exact_mod_cast bp
  have nn:0<(N:ℝ):=by exact_mod_cast np
  have each (q:ℕ) (hq:q∈Icc 1 B):‖J q-v‖≤2*(N:ℝ)/((B:ℝ)^2):=by
    have q1:(1:ℝ)≤q:=by exact_mod_cast (mem_Icc.mp hq).1
    have qb:(q:ℝ)≤B:=by exact_mod_cast (mem_Icc.mp hq).2
    have wp:0<w q:=by dsimp [w];positivity
    have wh:w q≤1/2:=by
      dsimp [w];apply (div_le_iff₀ (by positivity)).mpr
      have hh:(2:ℝ)*(B:ℝ)^3≤N:=by exact_mod_cast half
      nlinarith only [hh,mul_le_mul_of_nonneg_right q1 nn.le]
    apply (GoldbachBa08Kernel.norm_twisted_tail_upper N m wp wh ml mu).trans
    calc
      2/w q = 2*((q:ℝ)*N)/(B:ℝ)^3:=by dsimp [w];rw [div_div_eq_mul_div]
      _ ≤ 2*((B:ℝ)*N)/(B:ℝ)^3:=by gcongr
      _ = _:=by field_simp
  have shape:GoldbachBa08Approx.scaledModel N m B (B^3)=∑q∈Icc 1 B,C q*J q:=by
    simp only [GoldbachBa08Approx.scaledModel,GoldbachBlockGeometry.width,Nat.cast_pow,C,J,w]
  rw [shape]
  change ‖(∑q∈Icc 1 B,C q*J q)-v*∑q∈Icc 1 B,C q‖≤_
  rw [mul_sum,←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑q∈Icc 1 B,‖C q‖*(2*(N:ℝ)/(B:ℝ)^2):=by
      apply sum_le_sum;intro q hq
      rw [show C q*J q-v*C q=C q*(J q-v) by ring,norm_mul]
      exact mul_le_mul_of_nonneg_left (each q hq) (norm_nonneg _)
    _ = (∑q∈Icc 1 B,‖C q‖)*(2*(N:ℝ)/(B:ℝ)^2):=by rw [sum_mul]
    _ ≤ (4*(B:ℝ))*(2*(N:ℝ)/(B:ℝ)^2):=by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (GoldbachMajorArc.sum_norm_coefficient_le_sqrt B m).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast bp))) (by norm_num))
    _ = _:=by field_simp;ring

theorem transfer (ε:ℝ) (he:0<ε) :
    ∀ᶠ N:ℕ in atTop,∀m:ℕ,N ≤ m → m≤2*N →
    let B:=Nat.log 2 (N+2)
    ‖GoldbachBa08Approx.coefficient N m B (B^3)-(((2*N-m:ℕ):ℂ)+1)*
      ∑q∈Icc 1 B,GoldbachMajorArc.coefficient q m‖≤ε*N:=by
  let k:ℕ:=⌈16/ε⌉₊
  filter_upwards [GoldbachBa08Approx.eventually_approx (show 0<ε/2 by positivity),
    GoldbachBa08Approx.eventually_geometry,eventually_ge_atTop (2^k),eventually_ge_atTop (1:ℕ)] with N approx geom huge np
  intro m ml mu B
  obtain ⟨bp,_,sep⟩:=geom
  have half:2*B^3≤N:=by
    have one:1≤B^3:=Nat.one_le_pow 3 B bp
    nlinarith only [Nat.mul_le_mul_left (2*B^3) one,sep]
  have top:16/ε≤(B:ℝ):=(Nat.le_ceil _).trans (Nat.cast_le.mpr
    (Nat.le_log_of_pow_le (by decide : 1<2) (huge.trans (Nat.le_add_right N 2))))
  have bpos:0<(B:ℝ):=by exact_mod_cast bp
  have scalar:8/(B:ℝ)≤ε/2:=by
    apply (div_le_iff₀ bpos).mpr
    have :=(div_le_iff₀ he).mp top
    linarith only [this]
  apply (norm_sub_le_norm_sub_add_norm_sub _ (GoldbachBa08Approx.scaledModel N m B (B^3)) _).trans
  apply (add_le_add (approx m) (model_tail N B m np bp half ml mu)).trans
  have right:8*(N:ℝ)/B≤ε/2*N:=by rw [show 8*(N:ℝ)/B=(8/(B:ℝ))*N by ring];exact mul_le_mul_of_nonneg_right scalar (Nat.cast_nonneg _)
  linarith only [right]

end
end SharpArcTransfer

open Finset Filter Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc
open scoped BigOperators Topology

namespace SharpAssembly

theorem powers {q : ℕ} (hq : 0 < q) (j : ℕ) (hj : j ≠ 0) :
    coefficient q (2^j) = coefficient q 2 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => simp [coefficient_one]
  | prime_pow p k hp hk =>
    cases k with
    | zero => simp [coefficient_one]
    | succ k =>
      cases k with
      | zero =>
        simp only [zero_add, pow_one, coefficient_prime hp, localCoefficient]
        have iff : p ∣ 2^j ↔ p ∣ 2 := ⟨hp.dvd_of_dvd_pow, fun h => h.trans (dvd_pow_self _ hj)⟩
        simp only [iff]
      | succ k => simp [coefficient_higher_power hp]
  | coprime a b ha hb hc ia ib =>
    rw [coefficient_mul (by omega) (by omega) hc, coefficient_mul (by omega) (by omega) hc,
      ia (by omega), ib (by omega)]

noncomputable def row (L m : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 L, (coefficient q m).re

def band (N m : ℕ) : Prop := 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m

theorem powrow (L j : ℕ) (hj : j ≠ 0) : row L (2^j) = row L 2 := by
  unfold row
  apply sum_congr rfl
  intro q hq
  rw [powers (mem_Icc.mp hq).1 j hj]

theorem eventually_model {C : ℝ} {A : ℕ → ℕ → ℝ}
    (limBase : Tendsto (fun L => row L 2) atTop (𝓝 C))
    (cmp : ∀ L m, Even m → row L 2 ≤ row L m)
    (approx : ∀ e : ℝ, 0 < e → ∀ᶠ N : ℕ in atTop, ∀ m, band N m →
      |A N m - (2*(N:ℝ)-(m:ℝ)+1)*row (Nat.log 2 (N+2)) m| ≤ e*N)
    (ε : ℝ) (hε : 0 < ε) :
    (∃ T : ℕ, ∀ N m : ℕ, T ≤ N → band N m →
        (C-ε)*(2*(N:ℝ)-(m:ℝ)) ≤ A N m) ∧
    (∀ T : ℕ, ∃ N m : ℕ, T ≤ N ∧ 1 ≤ N ∧ band N m ∧
        A N m ≤ (C+ε)*(2*(N:ℝ)-(m:ℝ))) := by
  let e := ε/8
  have he : 0 < e := by dsimp [e]; positivity
  have bas := (Metric.tendsto_atTop.mp limBase) e he
  obtain ⟨L, hL⟩ := bas
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (approx e he)
  obtain ⟨K, hK⟩ := exists_nat_gt ((|C|+ε+1)/e)
  let T := max (max T₀ (2^L)) K
  have estimates (N m : ℕ) (hn : T ≤ N) (hb : band N m) :
      (C-ε)*(2*(N:ℝ)-(m:ℝ)) ≤ A N m ∧
      (row (Nat.log 2 (N+2)) m = row (Nat.log 2 (N+2)) 2 →
        A N m ≤ (C+ε)*(2*(N:ℝ)-(m:ℝ))) := by
    obtain ⟨blo,bhi,ev⟩ := hb
    have h₀ : T₀ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
    have h₁ : 2^L ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
    have h₂ : K ≤ N := (le_max_right _ _).trans hn
    let b := Nat.log 2 (N+2)
    let w : ℝ := 2*(N:ℝ)-(m:ℝ)
    have wid : (N:ℝ) ≤ 2*w := by
      dsimp [w]
      have : 2*(m:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast bhi
      linarith
    have wp : 0 ≤ w := by linarith [Nat.cast_nonneg (α:=ℝ) N]
    have long : |C|+ε+1 ≤ e*N := by
      have hn' : (K:ℝ) ≤ N := by exact_mod_cast h₂
      have h := ((div_lt_iff₀ he).mp hK).le
      nlinarith [mul_le_mul_of_nonneg_left hn' he.le]
    have close : |row b 2-C| < e := by
      simpa only [Real.dist_eq] using hL b (Nat.le_log_of_pow_le (by decide) (by omega))
    have ar := abs_le.mp (hT₀ N h₀ m ⟨blo,bhi,ev⟩)
    change -(e*(N:ℝ)) ≤ A N m - (w+1)*row b m ∧ _ at ar
    have eb := abs_lt.mp close
    have scale : e*(N:ℝ) ≤ 2*(e*w) := by nlinarith [mul_le_mul_of_nonneg_left wid he.le]
    have mainlo : (w+1)*(C-e) ≤ (w+1)*row b m :=
      mul_le_mul_of_nonneg_left (le_trans (by linarith [eb.1]) (cmp b m ev)) (by linarith)
    have loC := neg_abs_le C
    have hiC := le_abs_self C
    have eps8 : ε = 8*e := by dsimp [e]; ring
    constructor
    · change (C-ε)*w ≤ A N m
      nlinarith only [mainlo, ar.1, loC, long, scale, he, eps8,
        show ε*w = 8*(e*w) by rw [eps8]; ring]
    · intro hs
      change row b m = row b 2 at hs
      have mainhi : (w+1)*row b m ≤ (w+1)*(C+e) :=
        mul_le_mul_of_nonneg_left (by rw [hs]; linarith [eb.2]) (by linarith)
      change A N m ≤ (C+ε)*w
      nlinarith only [mainhi, ar.2, hiC, long, scale, he, eps8,
        show ε*w = 8*(e*w) by rw [eps8]; ring]
  refine ⟨⟨T, fun N m h hb => (estimates N m h hb).1⟩, ?_⟩
  intro T'
  let s := max T T'
  let v := 2^s
  have hv : 1 ≤ v := Nat.one_le_pow _ _ (by decide)
  have hs : s ≤ v := by exact Nat.le_of_lt (Nat.lt_two_pow_self)
  have band' : band (3*v) (4*v) := ⟨by omega, by omega, ⟨2*v, by omega⟩⟩
  have ht : T ≤ 3*v := by have := le_max_left T T'; omega
  refine ⟨3*v, 4*v, ?_, by omega, band', (estimates _ _ ht band').2 ?_⟩
  · have := le_max_right T T'; omega
  · have val : 4*v = 2^(s+2) := by simp [v, pow_add, mul_comm]
    rw [val, powrow _ _ (by omega)]

end SharpAssembly

open Finset
namespace SharpFloorComparison
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc
noncomputable section
open scoped Classical

def localFactor (G : Finset ℕ) (p : ℕ) : ℝ :=
  if p ∈ G then 1 / ((p : ℝ) - 1) else -badFactor p

def score (B G : Finset ℕ) (W : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ t ∈ (G ∪ B).powerset, (∏ p ∈ t, localFactor G p) * W (d * ∏ p ∈ t, p)

theorem score_floor (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k)
    (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i)
    (B G : Finset ℕ) (hB : ∀ p ∈ B, p.Prime ∧ 2 < p)
    (hG : ∀ p ∈ G, p.Prime ∧ 2 < p) (hdisj : Disjoint B G)
    (d : ℕ) (hd : 0 < d) : W d / 3 ≤ score B G W d := by
  classical
  induction G using Finset.induction_on generalizing d with
  | empty =>
    simpa [score, localFactor] using negative_factors_lower hB W hnonneg hmono hd
  | @insert p G hp ih =>
    have hp' : p.Prime ∧ 2 < p := hG p (mem_insert_self _ _)
    have hG' : ∀ q ∈ G, q.Prime ∧ 2 < q :=
      fun q hq => hG q (mem_insert_of_mem hq)
    have hdisj' : Disjoint B G := hdisj.mono_right (subset_insert p G)
    have hpB : p ∉ B := by
      intro h
      exact (disjoint_left.mp hdisj h (mem_insert_self p G))
    have hpGB : p ∉ G ∪ B := by simp [hp, hpB]
    have hpReal : (1:ℝ) < p := by exact_mod_cast (show 1<p by omega)
    have hsign : 0 ≤ 1 / ((p : ℝ)-1) := by positivity
    have hbase := ih hG' hdisj' d hd
    have hshift := ih hG' hdisj' (d*p) (Nat.mul_pos hd hp'.1.pos)
    have hsecond : 0 ≤ (1 / ((p:ℝ)-1)) * score B G W (d*p) :=
      mul_nonneg hsign ((div_nonneg (hnonneg _) (by norm_num)).trans hshift)
    have hpart : score B (insert p G) W d =
        score B G W d + (1 / ((p:ℝ)-1)) * score B G W (d*p) := by
      unfold score
      rw [insert_union, sum_powerset_insert hpGB]
      congr 1
      · apply sum_congr rfl
        intro t ht
        congr 1
        apply prod_congr rfl
        intro q hq
        have ne : q ≠ p := fun e => hpGB (mem_powerset.mp ht (e ▸ hq))
        simp [localFactor, ne]
      · rw [mul_sum]
        apply sum_congr rfl
        intro t ht
        have hpt : p ∉ t := fun h => hpGB (mem_powerset.mp ht h)
        rw [prod_insert hpt, prod_insert hpt]
        have eq : (∏ q ∈ t, localFactor (insert p G) q) = ∏ q ∈ t, localFactor G q := by
          apply prod_congr rfl
          intro q hq
          have ne : q ≠ p := fun e => hpt (e ▸ hq)
          simp [localFactor, ne]
        rw [eq]
        simp [localFactor, hp]
        ring
    rw [hpart]
    linarith only [hbase, hsecond]

theorem score_insert_positive (B G : Finset ℕ) (p : ℕ) (W : ℕ → ℝ) (d : ℕ)
    (hp : p ∉ G ∪ B) :
    score B (insert p G) W d = score B G W d +
      (1 / ((p:ℝ)-1)) * score B G W (d*p) := by
  classical
  unfold score
  rw [insert_union, sum_powerset_insert hp]
  congr 1
  · apply sum_congr rfl
    intro t ht
    congr 1
    apply prod_congr rfl
    intro q hq
    have ne : q ≠ p := fun e => hp (mem_powerset.mp ht (e ▸ hq))
    simp [localFactor, ne]
  · rw [mul_sum]
    apply sum_congr rfl
    intro t ht
    have hpt : p ∉ t := fun h => hp (mem_powerset.mp ht h)
    rw [prod_insert hpt, prod_insert hpt]
    have eq : (∏ q ∈ t, localFactor (insert p G) q) = ∏ q ∈ t, localFactor G q := by
      apply prod_congr rfl
      intro q hq
      have ne : q ≠ p := fun e => hpt (e ▸ hq)
      simp [localFactor, ne]
    rw [eq]
    simp [localFactor]
    ring

theorem score_insert_negative (B G : Finset ℕ) (p : ℕ) (W : ℕ → ℝ) (d : ℕ)
    (hp : p ∉ G ∪ B) :
    score (insert p B) G W d = score B G W d -
      badFactor p * score B G W (d*p) := by
  classical
  unfold score
  rw [union_insert, sum_powerset_insert hp]
  congr 1
  rw [mul_sum, ← sum_neg_distrib]
  apply sum_congr rfl
  intro t ht
  have hpt : p ∉ t := fun h => hp (mem_powerset.mp ht h)
  rw [prod_insert hpt, prod_insert hpt]
  have hpG : p ∉ G := fun h => hp (mem_union_left B h)
  simp [localFactor, hpG]
  ring

theorem score_step (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k)
    (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i)
    (B G : Finset ℕ) (hB : ∀ q ∈ B, q.Prime ∧ 2 < q)
    (hG : ∀ q ∈ G, q.Prime ∧ 2 < q) (hdisj : Disjoint B G)
    (p : ℕ) (hp : p.Prime ∧ 2 < p) (hnew : p ∉ G ∪ B)
    (d : ℕ) (hd : 0 < d) :
    score (insert p B) G W d ≤ score B (insert p G) W d := by
  rw [score_insert_negative B G p W d hnew,
    score_insert_positive B G p W d hnew]
  have hs := score_floor W hnonneg hmono B G hB hG hdisj (d*p)
    (Nat.mul_pos hd hp.1.pos)
  have hsn : 0 ≤ score B G W (d*p) :=
    (div_nonneg (hnonneg _) (by norm_num)).trans hs
  have hpReal : (1:ℝ) < p := by exact_mod_cast (show 1<p by omega)
  have hfac : 0 ≤ (1 / ((p:ℝ)-1)) + badFactor p := by
    unfold badFactor
    positivity
  nlinarith only [mul_nonneg hfac hsn]

theorem score_compare_all (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k)
    (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i)
    (B G : Finset ℕ) (hB : ∀ p ∈ B, p.Prime ∧ 2 < p)
    (hG : ∀ p ∈ G, p.Prime ∧ 2 < p) (hdisj : Disjoint B G)
    (d : ℕ) (hd : 0 < d) :
    score (B ∪ G) ∅ W d ≤ score B G W d := by
  classical
  induction G using Finset.induction_on generalizing B d with
  | empty => simp [score]
  | @insert p G hp ih =>
    have hp' : p.Prime ∧ 2 < p := hG p (mem_insert_self _ _)
    have hG' : ∀ q ∈ G, q.Prime ∧ 2 < q :=
      fun q hq => hG q (mem_insert_of_mem hq)
    have hdisj' : Disjoint B G := hdisj.mono_right (subset_insert p G)
    have hpB : p ∉ B := by
      intro h
      exact disjoint_left.mp hdisj h (mem_insert_self p G)
    have hnew : p ∉ G ∪ B := by simp [hp, hpB]
    have hBnext : ∀ q ∈ insert p B, q.Prime ∧ 2 < q := by
      intro q hq
      rcases mem_insert.mp hq with rfl | hqB
      · exact hp'
      · exact hB q hqB
    have hdisjnext : Disjoint (insert p B) G := by
      apply disjoint_left.mpr
      intro q hq hqG
      rcases mem_insert.mp hq with rfl | hqB
      · exact hp hqG
      · exact disjoint_left.mp hdisj hqB (mem_insert_of_mem hqG)
    have cmp := ih (insert p B) hBnext hG' hdisjnext d hd
    have step := score_step W hnonneg hmono B G hB hG' hdisj'
      p hp' hnew d hd
    calc
      score (B ∪ insert p G) ∅ W d = score (insert p B ∪ G) ∅ W d := by
        congr 1
        ext q
        simp [or_comm, or_left_comm, or_assoc]
      _ ≤ score (insert p B) G W d := cmp
      _ ≤ score B (insert p G) W d := step


end
end SharpFloorComparison

namespace SharpScoreReindex
open Finset SharpFloorComparison
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc
noncomputable section
open scoped Classical

/- Squarefree denominator reindexing from the verified EstermannAlmostAllPolylog module. -/
private theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : coefficient q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact coefficient_higher_power hp j n
  | coprime a b ha hb hab ia ib =>
    rw [coefficient_mul (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h,h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]

private theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    coefficient (∏ p ∈ s, p) n = ((∏ p ∈ s, localCoefficient p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [prod_insert hp, prod_insert hp, coefficient_mul hprime.pos (prod_pos fun r hr => (hs' r hr).pos) hcop,
      coefficient_prime hprime, ih hs', Complex.ofReal_mul]

private theorem reindex_denominators (Q n : ℕ) (W : ℕ → ℝ) (hcut : ∀ q, Q < q → W q = 0) :
    (∑ q ∈ Icc 1 Q, (coefficient q n).re * W q) =
    ∑ t ∈ ((range (Q + 1)).filter Nat.Prime).powerset, (∏ p ∈ t, localCoefficient p n) * W (∏ p ∈ t, p) := by
  classical
  let P := (range (Q + 1)).filter Nat.Prime
  have hprime {t : Finset ℕ} (ht : t ∈ P.powerset) : ∀ p ∈ t, p.Prime :=
    fun p hp => (mem_filter.mp (mem_powerset.mp ht hp)).2
  symm
  apply sum_bij_ne_zero (fun t _ _ => ∏ p ∈ t, p)
  · intro t ht hnz
    exact mem_Icc.mpr ⟨prod_pos fun p hp => (hprime ht p hp).pos, le_of_not_gt fun h => hnz (by rw [hcut _ h, mul_zero])⟩
  · intro s hs _ t ht _ he
    exact (Nat.primeFactors_prod (hprime hs)).symm.trans ((congrArg Nat.primeFactors he).trans (Nat.primeFactors_prod (hprime ht)))
  · intro q hq hnz
    have hq' := mem_Icc.mp hq
    have hsq : Squarefree q := by
      by_contra hh
      exact hnz (by rw [coefficient_not_squarefree n hq'.1 hh]; simp)
    have hprod := Nat.prod_primeFactors_of_squarefree hsq
    have hsub : q.primeFactors ∈ P.powerset := by
      apply mem_powerset.mpr
      intro p hp
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans hq'.2)),
        Nat.prime_of_mem_primeFactors hp⟩
    have hc := coefficient_prime_product n q.primeFactors (hprime hsub)
    rw [hprod] at hc
    exact ⟨q.primeFactors, hsub, fun hh => hnz (by rw [hprod] at hh; simpa only [hc, Complex.ofReal_re] using hh), hprod⟩
  · intro t ht _
    rw [coefficient_prime_product n t (hprime ht), Complex.ofReal_re]

def oddPrimes (Q : ℕ) := ((range (Q+1)).filter Nat.Prime).erase 2
def good (Q m : ℕ) := (oddPrimes Q).filter (· ∣ m)
def bad (Q m : ℕ) := (oddPrimes Q).filter fun p=> ¬p∣m
def weight (Q k : ℕ) : ℝ := if k≤Q then 1 else 0

theorem odd_characterization {Q p : ℕ} : p∈oddPrimes Q ↔ p.Prime ∧ 2<p ∧ p≤Q := by
  simp only [oddPrimes,mem_erase,mem_filter,mem_range]
  constructor
  · rintro ⟨ne,le,pr⟩
    exact ⟨pr,by have := pr.two_le;omega,by omega⟩
  · rintro ⟨pr,lt,le⟩;exact ⟨by omega,by omega,pr⟩

theorem partition (Q m : ℕ) : good Q m ∪ bad Q m=oddPrimes Q := by
  ext p;simp [good,bad];tauto

theorem score_reindex {Q m : ℕ} (hQ : 2≤Q) (hm : Even m) :
    (∑q∈Icc 1 Q,(coefficient q m).re) =
      score (bad Q m) (good Q m) (weight Q) 1 + score (bad Q m) (good Q m) (weight Q) 2 := by
  let P := (range (Q+1)).filter Nat.Prime
  let O := oddPrimes Q
  have h2 : 2∈P := mem_filter.mpr ⟨mem_range.mpr (by omega),Nat.prime_two⟩
  have sub : P=insert 2 O := (insert_erase h2).symm
  have nt : 2∉O := notMem_erase 2 P
  have equiv {p} (hp:p∈O) : localCoefficient p m=localFactor (good Q m) p := by
    change p∈oddPrimes Q at hp
    by_cases h : p∣m <;> simp [good,localFactor,localCoefficient,badFactor,h,hp]
  have changeFactors {t:Finset ℕ} (ht:t∈O.powerset) :
      (∏p∈t,localCoefficient p m)=(∏p∈t,localFactor (good Q m) p) :=
    prod_congr rfl (fun p hp=>equiv (mem_powerset.mp ht hp))
  have two : localCoefficient 2 m=1 := by
    have dv : 2∣m := even_iff_two_dvd.mp hm
    norm_num [localCoefficient,dv]
  trans ∑q∈Icc 1 Q,(coefficient q m).re*weight Q q
  · apply sum_congr rfl;intro q hq;simp [weight,(mem_Icc.mp hq).2]
  rw [reindex_denominators Q m (weight Q) (fun _ hi=>ite_eq_right (by omega))]
  change (∑t∈P.powerset,_) = _
  rw [sub,sum_powerset_insert nt]
  unfold score
  rw [partition]
  apply congrArg₂ (·+·)
  · apply sum_congr rfl;intro t ht
    rw [changeFactors ht,one_mul]
  · apply sum_congr rfl;intro t ht
    have offs : 2∉t := fun h=>nt (mem_powerset.mp ht h)
    rw [prod_insert offs,prod_insert offs,changeFactors ht,two,one_mul]

theorem cutoff_small {Q : ℕ} (hQ : Q≤1) (m:ℕ) :
    (∑q∈Icc 1 Q,(coefficient q 2).re) = ∑q∈Icc 1 Q,(coefficient q m).re := by
  interval_cases Q <;> simp [coefficient_one]

theorem good_two (Q : ℕ) : good Q 2=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨odd,dv⟩:=mem_filter.mp hp
  have z:=odd_characterization.mp odd
  exact (not_le_of_gt z.2.1) (Nat.le_of_dvd (by decide) dv)

theorem bad_two (Q : ℕ) : bad Q 2=oddPrimes Q := by
  simpa only [good_two,empty_union] using partition Q 2

theorem base_reindex {Q : ℕ} (hQ : 2≤Q) :
    (∑q∈Icc 1 Q,(coefficient q 2).re)=
      score (oddPrimes Q) ∅ (weight Q) 1 + score (oddPrimes Q) ∅ (weight Q) 2 := by
  simpa only [good_two,bad_two] using score_reindex (m:=2) hQ (by decide)
end
end SharpScoreReindex

open SharpFloorComparison SharpScoreReindex in
private theorem compare_row (L m : ℕ) (hm : Even m) : SharpAssembly.row L 2 ≤ SharpAssembly.row L m := by
  classical
  by_cases hl : 2 ≤ L
  · unfold SharpAssembly.row
    rw [base_reindex hl, score_reindex hl hm]
    have nonneg (k : ℕ) : 0 ≤ weight L k := by unfold weight; split <;> norm_num
    have mono (i j : ℕ) (_ : 0 < i) (h : i ≤ j) : weight L j ≤ weight L i := by
      unfold weight
      split_ifs <;> norm_num <;> omega
    have bg : Disjoint (bad L m) (good L m) := by
      apply Finset.disjoint_left.mpr
      intro p hb hg
      exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hg).2
    have bp : ∀ p ∈ bad L m, p.Prime ∧ 2 < p := by
      intro p h
      have h' := odd_characterization.mp (Finset.mem_filter.mp h).1
      exact ⟨h'.1,h'.2.1⟩
    have gp : ∀ p ∈ good L m, p.Prime ∧ 2 < p := by
      intro p h
      have h' := odd_characterization.mp (Finset.mem_filter.mp h).1
      exact ⟨h'.1,h'.2.1⟩
    have dst (d : ℕ) (hd : 0 < d) : score (oddPrimes L) ∅ (weight L) d ≤
        score (bad L m) (good L m) (weight L) d := by
      rw [← partition L m]
      simpa only [Finset.union_comm (bad L m) (good L m)] using
        score_compare_all (weight L) nonneg mono (bad L m) (good L m) bp gp bg d hd
    exact add_le_add (dst 1 (by decide)) (dst 2 (by decide))
  · have : L = 0 ∨ L = 1 := by omega
    rcases this with rfl | rfl <;> simp [SharpAssembly.row, GoldbachMajorArc.coefficient_one]

namespace SharpAssembly

private noncomputable def actual (N m : ℕ) : ℝ :=
  let k := Nat.log 2 (N+2)
  (GoldbachBa08Approx.coefficient N m k (k^3)).re

private theorem approxReal (e : ℝ) (he : 0 < e) : ∀ᶠ N : ℕ in atTop, ∀ m, band N m →
    |actual N m - (2*(N:ℝ)-(m:ℝ)+1)*row (Nat.log 2 (N+2)) m| ≤ e*N := by
  filter_upwards [SharpArcTransfer.transfer e he] with N hN
  intro m ⟨hb,ht,hev⟩
  have hm : m ≤ 2*N := by omega
  let k := Nat.log 2 (N+2)
  let z := ((2*N-m:ℕ):ℂ)+1
  let s := ∑ q ∈ Icc 1 k, GoldbachMajorArc.coefficient q m
  have err : |(GoldbachBa08Approx.coefficient N m k (k^3)-z*s).re| ≤ e*N :=
    (Complex.abs_re_le_norm _).trans (hN m (by omega) hm)
  have hv : z = ((2*(N:ℝ)-(m:ℝ)+1 : ℝ) : ℂ) := by
    dsimp [z]
    push_cast [hm]
    ring
  rw [hv, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at err
  simpa only [actual, k, row, s, Complex.re_sum] using err

end SharpAssembly

theorem Conjectures.Goldbach.ReflectedMajorSharpFloor : (by
  classical
  let e := fun t : ℝ => Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I)
  let S := fun (N : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e ((p : ℝ)*t)
  let arcs := fun N : ℕ => let k := Nat.log 2 (N+2); {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ k ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤ ((k^3 : ℕ) : ℝ)/((q : ℝ)*(N : ℝ))}
  let A := fun N m : ℕ => (intervalIntegral ((arcs N).indicator (fun t : ℝ => (S N t)^2 * e (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume).re
  let C₂ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1/((p : ℝ)-1)^2 else 1
  let band := fun N m : ℕ => 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m
  exact ∀ ε : ℝ, 0 < ε →
    (∃ T : ℕ, ∀ N m : ℕ, T ≤ N → band N m → (2*C₂-ε)*(2*(N : ℝ)-(m : ℝ)) ≤ A N m) ∧
    (∀ T : ℕ, ∃ N m : ℕ, T ≤ N ∧ 1 ≤ N ∧ band N m ∧ A N m ≤ (2*C₂+ε)*(2*(N : ℝ)-(m : ℝ)))) := by
  classical
  dsimp only
  intro ε hε
  have h := SharpAssembly.eventually_model SharpBaseLimit.base_limit compare_row SharpAssembly.approxReal ε hε
  simpa only [SharpAssembly.actual, SharpAssembly.band, GoldbachBa08Approx.coefficient,
    GoldbachBa08Approx.arcs, GoldbachBlockGeometry.width, GoldbachBa08Approx.primeSum_eq,
    GoldbachMajorArc.phase] using h
