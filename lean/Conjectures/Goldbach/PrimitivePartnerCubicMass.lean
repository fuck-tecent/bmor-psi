import Mathlib
import Conjectures.Goldbach.SharpSingularSeriesRatios

/-! Local cubic row bounds and their product over a common conductor.
The Jacobi sum and product formulas come from zxg0623, Goldbach PR 4023,
commit 0bd49cea808431f7bb6aa773c3095c39bf609ad7 (Apache-2.0).
The primitive-character injection follows the idea of Qmhou in PR 4164.
JiangZhexin proposed the local split and telescoping product in PR 4206.
Here we prove the full local row bounds and sum over every partner. -/
namespace CubicPartnerResearch
open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open scoped ComplexConjugate BigOperators Classical

private theorem restricted {q : ℕ} [NeZero q] (A B : DirichletCharacter ℂ q) (m : ZMod q) :
    J A B m = ∑ x ∈ univ.filter (admissible m), A x * B (m-x) := by
  symm
  apply sum_subset (filter_subset ..)
  intro x _ no
  have h : ¬(IsUnit x ∧ IsUnit (m-x)) := by simpa [admissible] using no
  by_cases hx : IsUnit x
  · rw [MulChar.map_nonunit B (fun H => h ⟨hx,H⟩),mul_zero]
  · rw [MulChar.map_nonunit A hx,zero_mul]

private theorem conj_at_unit {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ZMod q} (hx : IsUnit x) :
    conj (χ x) = χ x⁻¹ := by
  obtain ⟨u,rfl⟩ := hx
  rw [ZMod.inv_coe_unit]
  change star (χ (u:ZMod q)) = _
  rw [MulChar.star_apply',MulChar.inv_apply,Ring.inverse_unit]

theorem row_plancherel {q : ℕ} [NeZero q] (A : DirichletCharacter ℂ q) (m : ZMod q) :
    ∑ B : DirichletCharacter ℂ q, ‖J A B m‖^2 =
      (q.totient:ℝ)*‖J (1 : DirichletCharacter ℂ q) 1 m‖ := by
  classical
  let H := univ.filter (admissible m)
  let T (B : DirichletCharacter ℂ q) (x : ZMod q) := A x * B (m-x)
  have ortho (x y : ZMod q) (hx : x ∈ H) :
      (∑ B : DirichletCharacter ℂ q, conj (T B x) * T B y) =
      if x=y then (q.totient:ℂ) else 0 := by
    have u := (mem_filter.mp hx).2
    have eq : (∑ B : DirichletCharacter ℂ q, conj (T B x) * T B y) =
        (conj (A x)*A y)*(∑ B : DirichletCharacter ℂ q, B (m-x)⁻¹ * B (m-y)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro B _
      dsimp only [T]; rw [map_mul,conj_at_unit B u.2]; ring
    rw [eq,DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.2 (m-y)]
    by_cases e : x=y
    · subst y
      have norm1 : ‖A x‖=1 := A.unit_norm_eq_one u.1.unit
      simp [Complex.conj_mul',norm1]
    · simp [e]
  have normSqSum : (∑ B : DirichletCharacter ℂ q, (‖J A B m‖^2 : ℝ)) =
      (∑ x ∈ H, ∑ y ∈ H, if x=y then (q.totient:ℝ) else 0) := by
    apply Complex.ofReal_injective
    push_cast
    calc
      _ = ∑ B : DirichletCharacter ℂ q, (∑ x ∈ H, conj (T B x))*(∑ y ∈ H, T B y) := by
        apply sum_congr rfl
        intro B _
        rw [← Complex.conj_mul',restricted, map_sum]
      _ = ∑ x ∈ H, ∑ y ∈ H, ∑ B : DirichletCharacter ℂ q, conj (T B x)*T B y := by
        simp_rw [sum_mul,mul_sum]
        rw [sum_comm]
        apply sum_congr rfl; intro x _; rw [sum_comm]
      _ = _ := by
        apply sum_congr rfl; intro x hx
        apply sum_congr rfl; intro y _
        by_cases eq : x=y <;> simpa [eq] using ortho x y hx
  rw [normSqSum,principal_card,Complex.norm_natCast]
  change (∑ x ∈ H, ∑ y ∈ H, if x=y then (q.totient:ℝ) else 0) = (q.totient:ℝ)*H.card
  calc
    _ = ∑ _x ∈ H, (q.totient:ℝ) := by
      apply sum_congr rfl; intro x hx; simp [hx]
    _ = _ := by simp [mul_comm]

theorem divisible_row {p : ℕ} [Fact p.Prime] (e m : ℕ) (hp : p ∣ m)
    (A : DirichletCharacter ℂ (p*p^e)) :
    let q := p*p^e
    let W := ‖J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖
    (∑ B : DirichletCharacter ℂ q, ‖J A B (m:ZMod q)‖^3) ≤ W^3 := by
  intro q W
  have ph : p.Prime := Fact.out
  have ordinary : W = (q.totient:ℝ) := by
    dsimp only [W,q]
    rw [ordinary_prime_power,ite_eq_left hp,← pow_succ',Nat.totient_prime_pow_succ ph]
    push_cast [Nat.cast_sub ph.one_le]
    ring
  calc
    _ ≤ ∑ B : DirichletCharacter ℂ q, W*‖J A B (m:ZMod q)‖^2 := by
      apply sum_le_sum; intro B _
      rw [pow_succ, mul_comm]
      exact mul_le_mul_of_nonneg_right (TwistedGoldbachSingularSeries.chars_le_units A B _) (sq_nonneg _)
    _ = _ := by rw [← mul_sum,row_plancherel]; change W*((q.totient:ℝ)*W)=W^3; rw [← ordinary]; ring

open PrimePowerTwistedGoldbachDensity

private theorem swap_J {q : ℕ} [NeZero q] (A B : DirichletCharacter ℂ q) (m : ZMod q) :
    J A B m = J B A m := by
  unfold J
  rw [← Equiv.sum_comp (Equiv.subLeft m) (fun x : ZMod q => A x*B (m-x))]
  simp [mul_comm]

private theorem descend {p d : ℕ} [Fact p.Prime] (e : ℕ) (hd : d=p^(e+1)) [NeZero (d*p)]
    (A : DirichletCharacter ℂ (d*p)) (ha : ¬ A.IsPrimitive) :
    ∃ a : DirichletCharacter ℂ d, changeLevel (dvd_mul_right d p) a=A := by
  have hp : p.Prime := Fact.out
  have eqQ : d*p=p^(e+2) := by rw [hd,pow_succ p (e+1)]
  have dvQ := A.conductor_dvd_level
  conv at dvQ => rhs; rw [eqQ]
  obtain ⟨b,hb,eqb⟩ := (Nat.dvd_prime_pow hp).mp dvQ
  have small : b≤e+1 := by
    by_contra! hn
    have eq : b=e+2 := by omega
    exact ha (show A.conductor=d*p by rw [eqb,eq,eqQ])
  have dvd : A.conductor ∣ d := by rw [eqb,hd]; exact pow_dvd_pow p small
  refine ⟨changeLevel dvd A.primitiveCharacter,?_⟩
  rw [← changeLevel_trans,changeLevel_primitiveCharacter]

private theorem unit_step {p d m : ℕ} [Fact p.Prime] [NeZero d] [NeZero (d*p)]
    (e : ℕ) (hd : d=p^(e+1))
    (ih : ∀ A B : DirichletCharacter ℂ d, ¬(A=1 ∧ B=1) →
      ‖J A B (m:ZMod d)‖ ≤ (p:ℝ)^e*(if A=1 ∨ B=1 then 1 else Real.sqrt p))
    (primitive : ∀ A B : DirichletCharacter ℂ (d*p), A.IsPrimitive → B.IsPrimitive →
      ‖J A B (m:ZMod (d*p))‖ ≤ (p:ℝ)^(e+1)*Real.sqrt p)
    (A B : DirichletCharacter ℂ (d*p)) (out : ¬(A=1 ∧ B=1)) :
    ‖J A B (m:ZMod (d*p))‖ ≤ (p:ℝ)^(e+1)*(if A=1 ∨ B=1 then 1 else Real.sqrt p) := by
  have hp : p.Prime := Fact.out
  have support (a : ℕ) (h : a.Coprime d) : a.Coprime p := h.coprime_dvd_right
    (hd ▸ dvd_pow_self p (by omega))
  have not1 (C : DirichletCharacter ℂ (d*p)) (hC : C.IsPrimitive) : C≠1 := by
    rintro rfl
    change (1 : DirichletCharacter ℂ (d*p)).conductor=d*p at hC
    rw [conductor_one] at hC
    have h := Nat.le_mul_of_pos_left p (NeZero.pos d)
    have := hp.one_lt
    omega
  by_cases hA : A.IsPrimitive
  · by_cases hB : B.IsPrimitive
    · simpa [not1 A hA,not1 B hB] using primitive A B hA hB
    · obtain ⟨b,rfl⟩ := descend e hd B hB
      have z := mixed_vanishes hp.one_lt support hA b (m:ZMod (d*p))
      change J A _ _ = 0 at z
      rw [z,norm_zero]; split_ifs <;> positivity
  · obtain ⟨a,rfl⟩ := descend e hd A hA
    by_cases hB : B.IsPrimitive
    · have z := mixed_vanishes hp.one_lt support hB a (m:ZMod (d*p))
      change J B _ _ = 0 at z
      rw [swap_J,z,norm_zero]; split_ifs <;> positivity
    · obtain ⟨b,rfl⟩ := descend e hd B hB
      have h (c : DirichletCharacter ℂ d) : changeLevel (dvd_mul_right d p) c = 1 ↔ c=1 := by
        simp
      have out' : ¬(a=1 ∧ b=1) := by simpa only [h] using out
      have lift := both_lifted support a b (m:ZMod (d*p))
      change J _ _ _ = (p:ℂ)*J a b _ at lift
      rw [lift, norm_mul, Complex.norm_natCast, map_natCast,pow_succ' (p:ℝ) e,mul_assoc]
      simp only [h]
      exact mul_le_mul_of_nonneg_left (ih a b out') (Nat.cast_nonneg _)

private def BoundAt (q p m : ℕ) (w : ℝ) : Prop :=
  ∀ [NeZero q] (A B : DirichletCharacter ℂ q), ¬(A=1 ∧ B=1) →
     ‖J A B (m:ZMod q)‖ ≤ w*(if A=1 ∨ B=1 then 1 else Real.sqrt p)

private def PrimAt (q p m : ℕ) (w : ℝ) : Prop :=
  ∀ [NeZero q] (A B : DirichletCharacter ℂ q), A.IsPrimitive → B.IsPrimitive →
     ‖J A B (m:ZMod q)‖ ≤ w*Real.sqrt p

theorem unit_pointwise {p : ℕ} [Fact p.Prime] (e m : ℕ) (mp : ¬p ∣ m)
    (A B : DirichletCharacter ℂ (p*p^e)) (out : ¬(A=1 ∧ B=1)) :
    ‖J A B (m:ZMod (p*p^e))‖ ≤ (p:ℝ)^e*(if A=1 ∨ B=1 then 1 else Real.sqrt p) := by
  have hp : p.Prime := Fact.out
  induction e with
  | zero =>
    suffices H : BoundAt (p*p^0) p m ((p:ℝ)^0) from H A B out
    rw [show p*p^0=p by simp,pow_zero]
    intro _ A B out
    have table := SquarefreeTwistedGoldbachDensity.local_norm A B (m:ZMod p)
    change ‖J A B (m:ZMod p)‖ = _ at table
    have hn : (m:ZMod p)≠0 := mt (ZMod.natCast_eq_zero_iff m p).mp mp
    rw [table,ite_eq_right hn,ite_eq_right out,one_mul]
    split_ifs <;> first | exact le_rfl | exact Real.one_le_sqrt.mpr (by exact_mod_cast hp.one_le) | tauto
  | succ e ih =>
    have primitive (a b : DirichletCharacter ℂ (p*p^(e+1))) (ha : a.IsPrimitive) (hb : b.IsPrimitive) :
        ‖J a b (m:ZMod (p*p^(e+1)))‖ ≤ (p:ℝ)^(e+1)*Real.sqrt p := by
      let Q := p*p^(e+1)
      have mc : m.Coprime Q := (hp.coprime_iff_not_dvd.mpr mp).symm.mul_right
        ((hp.coprime_iff_not_dvd.mpr mp).symm.pow_right _)
      have qpos : 1<Q := hp.one_lt.trans_le (Nat.le_mul_of_pos_right p (pow_pos hp.pos _))
      have bound := TwistedGoldbachExceptionalGap.prime_power_bound (e+1) m ha hb
      dsimp only at bound
      change (1<Q/m.gcd Q → ‖J a b _‖*Real.sqrt (Q/m.gcd Q:ℕ) ≤ (Q:ℝ)) at bound
      rw [mc.gcd_eq_one,Nat.div_one] at bound
      have top : ‖J a b (m:ZMod Q)‖ ≤ Real.sqrt Q := by
        apply le_of_mul_le_mul_right (a := Real.sqrt Q) _ (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0<Q)))
        rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]; exact bound qpos
      apply top.trans
      apply (Real.sqrt_le_iff).2
      refine ⟨by positivity,?_⟩
      dsimp [Q]; push_cast; rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
      have hs : (1:ℝ)≤(p:ℝ)^(e+1) := one_le_pow₀ (by exact_mod_cast hp.one_le)
      nlinarith only [mul_nonneg (show (0:ℝ)≤(p:ℝ)*(p:ℝ)^(e+1) by positivity) (sub_nonneg.mpr hs)]
    have ident : p*p^(e+1)=(p*p^e)*p := by ring
    have PP : PrimAt (p*p^(e+1)) p m ((p:ℝ)^(e+1)) := by
      unfold PrimAt; intro inst; exact primitive
    rw [ident] at PP
    suffices H : BoundAt (p*p^(e+1)) p m ((p:ℝ)^(e+1)) from H A B out
    rw [ident]
    intro _ a b hab
    exact unit_step e (by rw [pow_succ']) ih (fun x y => PP x y) a b hab

private theorem sqrt_arith {p : ℕ} (hp : 5≤p) :
    Real.sqrt p * ((p:ℝ)-1) ≤ ((p:ℝ)-2)^2+1 := by
  have ge : (5:ℝ)≤p := by exact_mod_cast hp
  have sp : Real.sqrt p ≤ ((p:ℝ)+4)/4 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg p),sq_nonneg (Real.sqrt p-2)]
  have h := mul_le_mul_of_nonneg_right sp (show 0≤(p:ℝ)-1 by linarith)
  nlinarith [mul_nonneg (sub_nonneg.mpr ge) (show 0≤3*(p:ℝ)-4 by linarith)]

private theorem cube_reduction {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι)
    (X : ι → ℝ) (nn : ∀ i, 0≤X i) (p : ℕ) (hp : p.Prime) (odd : 3≤p)
    (mass : ∑ i, (X i)^2 = ((p:ℝ)-1)/((p:ℝ)-2))
    (contract : ∀ i, X i ≤ 1)
    (shape : (X i₀=1 ∧ ∀ i, i≠i₀ → X i≤1/((p:ℝ)-2)) ∨
       (∀ i, X i ≤ Real.sqrt p / ((p:ℝ)-2))) :
    (∑ i, (X i)^3) ≤ 1 + 1/((p:ℝ)-2)^2 := by
  have dpos : 0<(p:ℝ)-2 := by
    have h : (3:ℝ)≤p := by exact_mod_cast odd
    linarith
  rcases eq_or_ne p 3 with rfl | ne
  · calc
      _ ≤ ∑ i, (X i)^2 := sum_le_sum (fun i _ => by
        simpa [pow_succ (X i) 2] using mul_le_mul_of_nonneg_left (contract i) (sq_nonneg (X i)))
      _ = _ := by rw [mass]; norm_num
  have big : 5≤p := by
    by_contra! hh
    have : p=4 := by omega
    subst p
    norm_num at hp
  rcases shape with ⟨one,cap⟩ | cap
  · let c := 1/((p:ℝ)-2)
    have term (i : ι) : (X i)^3 ≤ c*(X i)^2 + if i=i₀ then 1-c else 0 := by
      by_cases e : i=i₀
      · simp [e,one]
      · rw [ite_eq_right e,add_zero,pow_succ,mul_comm]; exact mul_le_mul_of_nonneg_right (cap i e) (sq_nonneg _)
    calc
      _ ≤ ∑ i, (c*(X i)^2+if i=i₀ then 1-c else 0) := sum_le_sum (fun i _ => term i)
      _ = _ := by rw [sum_add_distrib,← mul_sum,mass]; simp [c]; field_simp [dpos.ne']; ring
  · calc
      _ ≤ ∑ i, (Real.sqrt p/((p:ℝ)-2))*(X i)^2 := sum_le_sum (fun i _ => by
        rw [pow_succ,mul_comm]; exact mul_le_mul_of_nonneg_right (cap i) (sq_nonneg _))
      _ = Real.sqrt p*((p:ℝ)-1)/((p:ℝ)-2)^2 := by rw [← mul_sum,mass]; field_simp [dpos.ne']
      _ ≤ _ := by
        apply (div_le_iff₀ (sq_pos_of_pos dpos)).2
        have cut := sqrt_arith big
        field_simp [dpos.ne']
        linarith only [cut]

theorem unit_row {p : ℕ} [Fact p.Prime] (odd : 3≤p) (e m : ℕ) (mp : ¬p ∣ m)
    (A : DirichletCharacter ℂ (p*p^e)) :
    let q := p*p^e
    let W := ‖J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖
    (∑ B : DirichletCharacter ℂ q, (‖J A B (m:ZMod q)‖ / W)^3) ≤ 1+1/((p:ℝ)-2)^2 := by
  intro q W
  let X (B : DirichletCharacter ℂ q) := ‖J A B (m:ZMod q)‖ / W
  have hp : p.Prime := Fact.out
  have pp : (0:ℝ)<p := by exact_mod_cast hp.pos
  have dpos : 0<(p:ℝ)-2 := by
    have ge : (3:ℝ)≤p := by exact_mod_cast odd
    linarith
  have we : W=(p:ℝ)^e*((p:ℝ)-2) := by dsimp only [W,q]; rw [ordinary_prime_power,ite_eq_right mp,Nat.cast_pow]
  have wp : 0<W := we ▸ mul_pos (pow_pos pp e) dpos
  have phie : (q.totient:ℝ)=(p:ℝ)^e*((p:ℝ)-1) := by
    dsimp only [q]; rw [← pow_succ',Nat.totient_prime_pow_succ hp]; push_cast [Nat.cast_sub hp.one_le]; ring
  apply cube_reduction (1 : DirichletCharacter ℂ q) X (fun B => div_nonneg (norm_nonneg _) wp.le) p hp odd
  · simp only [X,div_pow, ← sum_div, row_plancherel]
    change (q.totient:ℝ)*W/W^2=_
    rw [phie,we]; field_simp [dpos.ne',pp.ne']
  · intro B; apply (div_le_one wp).2; exact TwistedGoldbachSingularSeries.chars_le_units A B _
  · have cap (B : DirichletCharacter ℂ q) (h : ¬(A=1 ∧ B=1)) :
        X B ≤ (if A=1 ∨ B=1 then 1 else Real.sqrt p)/((p:ℝ)-2) := by
      apply (div_le_iff₀ wp).2
      rw [we]
      convert unit_pointwise e m mp A B h using 1
      field_simp [dpos.ne']
    by_cases a : A=1
    · left
      refine ⟨?_,fun B bn => ?_⟩
      · dsimp only [X]; rw [a]; exact div_self wp.ne'
      · simpa [a] using cap B (by tauto)
    · right; intro B
      have h := cap B (by tauto)
      by_cases b : B=1
      · simp only [b,or_true,ite_true] at h ⊢
        exact h.trans (div_le_div_of_nonneg_right (Real.one_le_sqrt.mpr (by exact_mod_cast hp.one_le)) dpos.le)
      · simpa [a,b] using h

end CubicPartnerResearch


namespace CubicPartnerResearch
open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open scoped BigOperators Classical

private noncomputable def envelope (p : ℕ) : ℝ :=
  if p=3 then 2 else if 5≤p then ((p:ℝ)-2)^2/(((p:ℝ)-2)^2-1) else 1

private theorem tail_dom {p : ℕ} (hp : 5≤p) : 1+1/((p:ℝ)-2)^2 ≤ envelope p := by
  have ge : (5:ℝ)≤p := by exact_mod_cast hp
  have den : 1<((p:ℝ)-2)^2 := by nlinarith [sq_nonneg ((p:ℝ)-5)]
  rw [envelope,ite_eq_right (by omega : p≠3),ite_eq_left hp,le_div_iff₀ (by linarith)]
  let d := ((p:ℝ)-2)^2
  have hd : 0<d := by dsimp [d]; linarith
  change (1+1/d)*(d-1) ≤ d
  have eq : (1+1/d)*(d-1) = d-1/d := by field_simp [hd.ne']; ring
  rw [eq]; linarith [one_div_pos.mpr hd]

private theorem one_le_env (p : ℕ) : 1≤envelope p := by
  by_cases h : 5≤p
  · exact (show (1:ℝ)≤1+1/((p:ℝ)-2)^2 by linarith [one_div_nonneg.mpr (sq_nonneg ((p:ℝ)-2))]).trans (tail_dom h)
  · unfold envelope; split_ifs <;> norm_num

private theorem envelope_prefix (k : ℕ) : ∏ p ∈ range (k+5), envelope p =
    3*((k:ℝ)+2)/((k:ℝ)+3) := by
  induction k with
  | zero => norm_num [envelope,prod_range_succ]
  | succ k ih =>
    rw [show k+1+5=k+5+1 by omega,prod_range_succ,ih,envelope,
      ite_eq_right (by omega : k+5≠3),ite_eq_left (by omega : 5≤k+5)]
    push_cast
    have hn : (0:ℝ)≤k := Nat.cast_nonneg _
    have hd : 0<((k:ℝ)+5-2)^2-1 := by nlinarith [sq_nonneg (k:ℝ)]
    field_simp [hd.ne']; ring

theorem product_budget (S : Finset ℕ) : (∏ p ∈ S, envelope p) ≤ 3 := by
  let k := S.sup id
  let U := range (k+5)
  have sub : S ⊆ U := by
    intro p hp
    have bound : p≤k := le_sup (f := id) hp
    exact mem_range.mpr (by omega)
  have eq : U.filter (fun p => p ∈ S) = S := by ext p; simp only [mem_filter]; tauto_set
  calc
    _ = ∏ p ∈ U, (if p ∈ S then envelope p else 1) := by rw [← prod_filter,eq]
    _ ≤ ∏ p ∈ U, envelope p := Finset.prod_le_prod₀ (fun i _ => by split_ifs <;> first | exact zero_le_one | exact zero_le_one.trans (one_le_env i)) (fun i _ => by split_ifs <;> first | exact le_rfl | exact one_le_env i)
    _ = _ := envelope_prefix k
    _ ≤ _ := (div_le_iff₀ (by positivity)).2 (by linarith)

private theorem local_budget {p q : ℕ} [Fact p.Prime] [NeZero q] (k m : ℕ)
    (eqQ : q=p*p^k) (he : Even m) (A : DirichletCharacter ℂ q) :
    (∑ B : DirichletCharacter ℂ q, ‖J A B (m:ZMod q)/J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖^3)
      ≤ envelope p := by
  subst q
  let W := ‖J (1 : DirichletCharacter ℂ (p*p^k)) 1 (m:ZMod (p*p^k))‖
  have wp : 0<W := norm_pos_iff.mpr (principal_ne_zero _ m he)
  have hp : p.Prime := Fact.out
  simp only [norm_div]
  by_cases pm : p ∣ m
  · simp only [div_pow,← sum_div]
    apply le_trans _ (one_le_env p)
    apply (div_le_one (pow_pos wp 3)).2
    exact divisible_row k m pm A
  · have odd : 3≤p := by
      have := hp.two_le
      by_contra! small
      exact pm ((show p=2 by omega) ▸ (even_iff_two_dvd.mp he))
    apply (unit_row odd k m pm A).trans
    by_cases p3 : p=3
    · subst p; norm_num [envelope]
    · apply tail_dom
      by_contra! small
      have : p=4 := by omega
      subst p; norm_num at hp


private theorem assemble {r : ℕ} [NeZero r] (α : DirichletCharacter ℂ r) (hα : α.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) (F : Finset (Σ s : ℕ, DirichletCharacter ℂ s))
    (hf : ∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive) :
    (∑ b ∈ F, ‖series α b.2 m‖^3) ≤ 3 * ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖^3 := by
  classical
  let L := r * ∏ b ∈ F, b.1
  have lpos : 0 < L := Nat.mul_pos (NeZero.pos r) (prod_pos (fun b hb => Nat.pos_of_ne_zero (hf b hb).1))
  letI : NeZero L := ⟨lpos.ne'⟩
  let I := ↥L.primeFactors
  let Q (i : I) := (i:ℕ)^L.factorization i
  letI (i : I) : NeZero (Q i) := ⟨(Nat.ordProj_pos L i).ne'⟩
  let e := ZMod.equivPi L lpos.ne'
  let hr : r ∣ L := dvd_mul_right r _
  have divides (b : F) : b.val.1 ∣ L :=
    (dvd_prod_of_mem (fun z : Σ s : ℕ, DirichletCharacter ℂ s => z.1) b.property).trans (dvd_mul_left _ r)
  let B (b : F) := changeLevel (divides b) b.val.2
  let loc (b : F) (i : I) := component e (B b) i
  have inj : Function.Injective loc := by
    intro b c eq
    have same : B b=B c := by
      apply MulChar.ext
      intro u
      rw [reassemble e (B b) (u:ZMod L), reassemble e (B c) (u:ZMod L)]
      exact prod_congr rfl (fun i _ => congrArg (fun χ : DirichletCharacter ℂ (Q i) => χ (e u i)) (congrFun eq i))
    have core {s t : ℕ} (a : DirichletCharacter ℂ s) (b : DirichletCharacter ℂ t)
        (hs : s ∣ L) (ht : t ∣ L) (ha : a.IsPrimitive) (hb : b.IsPrimitive)
        (h : changeLevel hs a = changeLevel ht b) :
        (⟨s,a⟩ : Σ n : ℕ, DirichletCharacter ℂ n) = ⟨t,b⟩ := by
      have eqst := congrArg DirichletCharacter.conductor h
      rw [conductor_changeLevel,conductor_changeLevel,ha,hb] at eqst
      subst t
      exact congrArg (Sigma.mk s) (changeLevel_injective hs h)
    exact Subtype.ext (core _ _ _ _ (hf _ b.property).2 (hf _ c.property).2 same)
  let A (i : I) := component e (changeLevel hr α) i
  let W (i : I) (b : DirichletCharacter ℂ (Q i)) : ℝ :=
    ‖J (A i) b (m:ZMod (Q i))/J (1 : DirichletCharacter ℂ (Q i)) 1 (m:ZMod (Q i))‖^3
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖^3
  have on (b : F) : ‖series α b.val.2 m‖^3 = O*(∏ i, W i (loc b i)) := by
    letI : NeZero b.val.1 := ⟨(hf _ b.property).1⟩
    rw [full_product e hα (hf _ b.property).2 hr (divides b) m hm he,norm_mul,norm_prod,mul_pow]
    dsimp only [W,loc,B,A,O]; rw [prod_pow]
  have nn (f : ∀ i, DirichletCharacter ℂ (Q i)) : 0 ≤ ∏ i, W i (f i) :=
    prod_nonneg (fun i _ => pow_nonneg (norm_nonneg _) _)
  have totals : (∑ b : F, ∏ i, W i (loc b i)) ≤ ∏ i, ∑ c, W i c := by
    rw [Fintype.prod_sum]
    let g (f : ∀ i, DirichletCharacter ℂ (Q i)) := ∏ i, W i (f i)
    change (∑ b : F, g (loc b)) ≤ ∑ f, g f
    rw [← sum_image (f := g) inj.injOn]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun f _ _ => nn f)
  have each (i : I) : (∑ c, W i c) ≤ envelope i := by
    have h := Nat.mem_primeFactors.mp i.property
    letI : Fact (i:ℕ).Prime := ⟨h.1⟩
    obtain ⟨a,ha⟩ : ∃ a, L.factorization i=a+1 := by
      have := (h.1.dvd_iff_one_le_factorization lpos.ne').mp h.2.1
      exact ⟨L.factorization i-1,by omega⟩
    exact local_budget (p := (i:ℕ)) (q := Q i) a m (by change (i:ℕ)^L.factorization i = _; rw [ha,pow_succ']) he (A i)
  have bound : (∏ i, ∑ c, W i c) ≤ 3 := calc
    _ ≤ ∏ i : I, envelope i := prod_le_prod₀ (fun i _ => sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _)) (fun i _ => each i)
    _ = ∏ j ∈ L.primeFactors, envelope j := prod_coe_sort _ _
    _ ≤ 3 := product_budget _
  rw [← sum_coe_sort F]
  calc
    _ = O*∑ b : F, ∏ i, W i (loc b i) := by rw [mul_sum]; exact sum_congr rfl (fun b _ => on b)
    _ ≤ O*3 := mul_le_mul_of_nonneg_left (totals.trans bound) (pow_nonneg (norm_nonneg _) _)
    _ = _ := mul_comm _ _

end CubicPartnerResearch

theorem Conjectures.Goldbach.PrimitivePartnerCubicMass :
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  exact ∀ (r : ℕ) [NeZero r] (α : DirichletCharacter ℂ r), α.IsPrimitive →
    ∀ m : ℕ, 0 < m → Even m →
    ∀ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
    (∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive) →
    (∑ b ∈ F, ‖S α b.2 m‖^3) ≤ 3 * ‖O m‖^3 := by
  classical
  dsimp only
  intro r inst α hα m hm he F hF
  exact CubicPartnerResearch.assemble α hα m hm he F hF
