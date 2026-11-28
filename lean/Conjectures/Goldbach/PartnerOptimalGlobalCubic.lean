import Mathlib
import Conjectures.Goldbach.PrimitivePartnerCubicMass

/-! Optimal global cubic mass for primitive partners.
The upper CRT assembly is adapted from 26day, Goldbach PR 4245, revision
9a67baf6e7d0deb619280bc82b66dc962de432cd, licensed under Apache-2.0.
It uses the Jacobi formulas of zxg0623, PR 4023, revision
0bd49cea808431f7bb6aa773c3095c39bf609ad7, and the character-injection
argument of Qmhou, PR 4164, revision 2fd7e92cee761261e587c6e9e33b3286fe6d1ec9.
The prime-level evaluation also draws on SaladDay, PR 4301, revision
9519616349a4495ad0ca3af1c2030368869973e7, under Apache-2.0.
Here we retain the exact local budgets, construct a simultaneous lower
witness through CRT and passage to primitive sources, and bound the
infinite product by a telescoping estimate over the odd tail. -/

namespace OptimalPartner
open Finset Filter
open scoped BigOperators Topology Classical
noncomputable def weight (p : ℕ) : ℝ :=
  if p.Prime ∧ 3 ≤ p then 1+1/((p:ℝ)-2)^2 else 1
theorem one_le_weight (p : ℕ) : 1 ≤ weight p := by unfold weight; split_ifs <;> simp [sq_nonneg]
noncomputable def cap : ℝ := 2*(10/9)*(26/25)*(16/15)
private noncomputable def growth (k : ℕ) : ℝ := 1-1/(16+4*(k:ℝ))
private theorem step (k : ℕ) :
    growth k * weight (11+2*k) ≤ growth (k+1) := by
  have h := one_le_weight (11+2*k)
  have up : weight (11+2*k) ≤ 1+1/((11+2*(k:ℝ))-2)^2 := by
    unfold weight; split_ifs <;> push_cast <;> first | rfl | simp [sq_nonneg]
  have gn : 0 ≤ growth k := by
    unfold growth; have := (div_le_one (show (0:ℝ)<16+4*k by positivity)).2 (show (1:ℝ)≤16+4*k by linarith [Nat.cast_nonneg (α:=ℝ) k])
    linarith
  apply (mul_le_mul_of_nonneg_left up gn).trans
  unfold growth; push_cast
  have h1 : (0:ℝ) < 16+4*k := by positivity
  have h2 : (0:ℝ) < 16+4*(k+1) := by positivity
  have h3 : (0:ℝ) < 11+2*k-2 := by linarith
  rw [show 11+2*(k:ℝ)-2=9+2*k by ring]
  field_simp [(show (0:ℝ)<9+2*k by positivity)]
  nlinarith [sq_nonneg (k:ℝ)]
private theorem budget_range (k : ℕ) : ∏ p ∈ range (11+2*k), weight p ≤ cap*growth k := by
  induction k with
  | zero => norm_num [prod_range_succ,weight,cap,growth]
  | succ k ih =>
    have evenP : ¬ (11+2*k+1).Prime := by
      intro pr
      have dv : 2 ∣ 11+2*k+1 := ⟨6+k,by omega⟩
      rcases (Nat.dvd_prime pr).mp dv with h|h <;> omega
    rw [show 11+2*(k+1)=(11+2*k)+1+1 by omega,prod_range_succ,prod_range_succ]
    have w : weight (11+2*k+1)=1 := by simp [weight,evenP]
    rw [w,mul_one]
    calc
      _ ≤ cap*growth k*weight (11+2*k) := mul_le_mul_of_nonneg_right ih (le_trans zero_le_one (one_le_weight _))
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (step _) (by norm_num [cap])
theorem budget_all (T : Finset ℕ) : ∏ p ∈ T, weight p ≤ cap := by
  let k := T.sup id
  have sub : T ⊆ range (11+2*k) := by
    intro p hp; exact mem_range.mpr (by have h : p≤k := le_sup (f:=id) hp; omega)
  calc
    _ ≤ ∏ p ∈ range (11+2*k), weight p := prod_le_prod_of_subset_of_one_le₀ sub (fun i _=>zero_le_one.trans (one_le_weight i)) (fun _ _ _=>one_le_weight _)
    _ ≤ cap*growth k := budget_range k
    _ ≤ cap*1 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num [cap]); unfold growth; simp; positivity
    _ = _ := mul_one _
noncomputable def constant : ℝ := ⨆ T : Finset ℕ, ∏ p ∈ T, weight p
theorem bounded : BddAbove (Set.range (fun T : Finset ℕ=>∏ p ∈ T,weight p)) :=
  ⟨cap,fun _ ⟨T,h⟩=>h ▸ budget_all T⟩
theorem hasProduct : HasProd weight constant :=
  tendsto_atTop_ciSup (fun _ _ h=>prod_le_prod_of_subset_of_one_le₀ h (fun i _=>zero_le_one.trans (one_le_weight i)) (fun _ _ _=>one_le_weight _)) bounded
theorem le_constant (T : Finset ℕ) : (∏ p ∈ T,weight p) ≤ constant := le_ciSup bounded T
theorem constant_le : constant ≤ cap := ciSup_le budget_all
end OptimalPartner

namespace OptimalPartner
open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open scoped BigOperators Classical
private theorem local_budget {p q : ℕ} [Fact p.Prime] [NeZero q] (k m : ℕ)
    (eqQ : q=p*p^k) (he : Even m) (A : DirichletCharacter ℂ q) :
    (∑ B : DirichletCharacter ℂ q, ‖J A B (m:ZMod q)/J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖^3)
      ≤ weight p := by
  subst q
  let W := ‖J (1 : DirichletCharacter ℂ (p*p^k)) 1 (m:ZMod (p*p^k))‖
  have wp : 0<W := norm_pos_iff.mpr (principal_ne_zero _ m he)
  have hp : p.Prime := Fact.out
  simp only [norm_div]
  by_cases pm : p ∣ m
  · simp only [div_pow,← sum_div]
    apply le_trans _ (one_le_weight p)
    apply (div_le_one (pow_pos wp 3)).2
    exact CubicPartnerResearch.divisible_row k m pm A
  · have odd : 3≤p := by
      have := hp.two_le
      by_contra! small
      exact pm ((show p=2 by omega) ▸ (even_iff_two_dvd.mp he))
    rw [weight,ite_eq_left ⟨hp,odd⟩]
    exact CubicPartnerResearch.unit_row odd k m pm A

theorem upper {r : ℕ} [NeZero r] (α : DirichletCharacter ℂ r) (hα : α.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) (F : Finset (Σ s : ℕ, DirichletCharacter ℂ s))
    (hf : ∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive) :
    (∑ b ∈ F, ‖series α b.2 m‖^3) ≤ constant * ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖^3 := by
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
  have each (i : I) : (∑ c, W i c) ≤ weight i := by
    have h := Nat.mem_primeFactors.mp i.property
    letI : Fact (i:ℕ).Prime := ⟨h.1⟩
    obtain ⟨a,ha⟩ : ∃ a, L.factorization i=a+1 := by
      have := (h.1.dvd_iff_one_le_factorization lpos.ne').mp h.2.1
      exact ⟨L.factorization i-1,by omega⟩
    exact local_budget (p := (i:ℕ)) (q := Q i) a m (by change (i:ℕ)^L.factorization i = _; rw [ha,pow_succ']) he (A i)
  have bound : (∏ i, ∑ c, W i c) ≤ constant := calc
    _ ≤ ∏ i : I, weight i := prod_le_prod₀ (fun i _ => sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _)) (fun i _ => each i)
    _ = ∏ j ∈ L.primeFactors, weight j := prod_coe_sort _ _
    _ ≤ constant := le_constant _
  rw [← sum_coe_sort F]
  calc
    _ = O*∑ b : F, ∏ i, W i (loc b i) := by rw [mul_sum]; exact sum_congr rfl (fun b _ => on b)
    _ ≤ O*constant := mul_le_mul_of_nonneg_left (totals.trans bound) (pow_nonneg (norm_nonneg _) _)
    _ = _ := mul_comm _ _


end OptimalPartner

namespace OptimalPartner
open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open SquarefreeTwistedGoldbachDensity TwistedGoldbachMixedPrincipal
open scoped BigOperators Classical
private theorem prime_row (p : ℕ) (hp : p.Prime) (odd : 3 ≤ p) [NeZero p] :
    (∑ B : DirichletCharacter ℂ p, ‖J (1 : DirichletCharacter ℂ p) B (2:ZMod p) /
       J (1 : DirichletCharacter ℂ p) 1 (2:ZMod p)‖^3) = weight p := by
  letI : Fact p.Prime := ⟨hp⟩
  have two : (2 : ZMod p)≠0 := by
    intro eq
    have dv := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using eq)
    have := Nat.le_of_dvd (by decide : 0<2) dv
    omega
  have denominator := local_norm (1 : DirichletCharacter ℂ p) (1 : DirichletCharacter ℂ p) (2:ZMod p)
  change ‖J (1 : DirichletCharacter ℂ p) 1 (2:ZMod p)‖ = _ at denominator
  simp [two] at denominator
  let E := (univ : Finset (DirichletCharacter ℂ p)).erase 1
  have cardE : E.card=p-2 := by
    dsimp [E]; rw [card_erase_of_mem (mem_univ _),card_univ,←Nat.card_eq_fintype_card,
      card_eq_totient_of_hasEnoughRootsOfUnity ℂ p,Nat.totient_prime hp]; omega
  have den : (0:ℝ) < (p:ℝ)-2 := by
    have h : (3:ℝ) ≤ p := by exact_mod_cast odd
    linarith
  rw [←add_sum_erase _ _ (mem_univ (1 : DirichletCharacter ℂ p))]
  simp only [norm_div,denominator,div_self (ne_of_gt den),one_pow]
  have other (B : DirichletCharacter ℂ p) (hb : B∈E) :
      (‖J (1 : DirichletCharacter ℂ p) B (2:ZMod p)‖ / ((p:ℝ)-2))^3 = (1/((p:ℝ)-2))^3 := by
    have ne := (mem_erase.mp hb).1
    have eq := local_norm (1 : DirichletCharacter ℂ p) B (2:ZMod p)
    change ‖J (1 : DirichletCharacter ℂ p) B (2:ZMod p)‖ = _ at eq
    simp [two,ne] at eq
    rw [eq]
  change 1 + (∑ B ∈ E, _) = _
  rw [sum_congr rfl other,sum_const,nsmul_eq_mul,cardE,weight,ite_eq_left ⟨hp,odd⟩,Nat.cast_sub (by omega : 2≤p)]
  push_cast; field_simp <;> ring

section Tuple
variable {I : Type*} [Fintype I] [DecidableEq I] {q : I → ℕ}
variable {L : ℕ} (e : ZMod L ≃+* ∀ i, ZMod (q i))
private noncomputable def pack (b : ∀ i, DirichletCharacter ℂ (q i)) : DirichletCharacter ℂ L where
  toFun x := ∏ i, b i (e x i)
  map_one' := by simp
  map_mul' x y := by simp [prod_mul_distrib]
  map_nonunit' x hx := by
    obtain ⟨i,hi⟩ : ∃ i, ¬ IsUnit (e x i) := by
      by_contra! hs
      exact hx (by simpa using (Pi.isUnit_iff.mpr hs).map e.symm)
    exact prod_eq_zero (mem_univ i) ((b i).map_nonunit hi)
private theorem unpack (b : ∀ i, DirichletCharacter ℂ (q i)) (i : I) :
    component e (pack e b) i = b i := by
  apply MulChar.ext; intro u
  change (∏ j, b j (e (e.symm (Pi.mulSingle i (u:ZMod (q i)))) j))=_
  rw [e.apply_symm_apply,prod_eq_single i]
  · simp
  · intro j _ h; simp [Pi.mulSingle_eq_of_ne h]
  · simp
end Tuple

abbrev Partner := Σ n : ℕ, DirichletCharacter ℂ n
noncomputable abbrev triv := (1 : DirichletCharacter ℂ 1)
private theorem ordinary_pos (m : ℕ) (hm : 0 < m) (he : Even m) : 0 < ‖series triv triv m‖ := by
  have h := (ordinary_at_least_one m hm he).trans (Complex.re_le_norm _)
  exact lt_of_lt_of_le zero_lt_one h
set_option maxHeartbeats 1700000 in
theorem finite_sharp (T : Finset ℕ) (good : ∀ p ∈ T,p.Prime ∧ 3≤p) :
    ∃ F : Finset Partner, (∀ b ∈ F,b.1≠0 ∧ b.2.IsPrimitive) ∧
    (∑ b ∈ F, ‖series triv b.2 2‖^3)= (∏ p ∈ T,weight p)*‖series triv triv 2‖^3 := by
  classical
  let I := ↥T
  let q (i : I) : ℕ := i.val
  have hp (i : I) : (q i).Prime := (good _ i.property).1
  letI (i : I) : NeZero (q i) := ⟨(hp i).ne_zero⟩
  let L := ∏ i : I,q i
  letI : NeZero L := ⟨(prod_pos (fun i _=>(hp i).pos)).ne'⟩
  have cop : Pairwise (fun i j=> (q i).Coprime (q j)) := by
    intro i j ne
    exact (Nat.coprime_primes (hp i) (hp j)).mpr fun h=>ne (Subtype.ext h)
  let e : ZMod L ≃+* ∀ i,ZMod (q i) := ZMod.prodEquivPi q cop
  let Tuple := ∀ i, DirichletCharacter ℂ (q i)
  let global (b : Tuple) := pack e b
  let source (b : Tuple) : Partner := ⟨(global b).conductor,(global b).primitiveCharacter⟩
  have recover (b : Tuple) : changeLevel (global b).conductor_dvd_level (source b).2 = global b :=
    (global b).changeLevel_primitiveCharacter
  let lift (z : Partner) : DirichletCharacter ℂ L := if h : z.1 ∣ L then changeLevel h z.2 else 1
  have inverse (b : Tuple) : lift (source b)=global b := by
    dsimp only [lift]; rw [dif_pos (global b).conductor_dvd_level]; exact recover b
  have inj : Function.Injective source := by
    intro b c eq
    have same := congrArg lift eq
    rw [inverse,inverse] at same
    funext i
    exact (unpack e b i).symm.trans ((congrArg (fun χ=>component e χ i) same).trans (unpack e c i))
  let W (i : I) (B : DirichletCharacter ℂ (q i)) :=
    ‖J (1 : DirichletCharacter ℂ (q i)) B (2:ZMod (q i)) / J (1 : DirichletCharacter ℂ (q i)) 1 (2:ZMod (q i))‖^3
  let O := ‖series triv triv 2‖^3
  have on (b : Tuple) : ‖series triv (source b).2 2‖^3= O*∏ i,W i (b i) := by
    have nz : (global b).conductor≠0 := fun eq=>NeZero.ne L (conductor_eq_zero_iff_level_eq_zero.mp eq)
    letI : NeZero (source b).1 := ⟨nz⟩
    rw [full_product e isPrimitive_one_level_one (global b).primitiveCharacter_isPrimitive
      (one_dvd L) (global b).conductor_dvd_level 2 (by decide) (by decide),
      norm_mul,norm_prod,mul_pow,←prod_pow]
    apply congrArg (fun z : ℝ=>O*z)
    apply prod_congr rfl; intro i _
    rw [changeLevel_primitiveCharacter,map_one,component_one]
    change ‖J 1 (component e (pack e b) i) _ / J 1 1 _‖^3 = _
    rw [unpack]
    rfl
  refine ⟨univ.image source,?_,?_⟩
  · intro z hz
    obtain ⟨b,_,rfl⟩ := mem_image.mp hz
    exact ⟨fun eq=>NeZero.ne L (conductor_eq_zero_iff_level_eq_zero.mp eq),(global b).primitiveCharacter_isPrimitive⟩
  · rw [sum_image (fun _ _ _ _ h=>inj h)]
    simp_rw [on]
    rw [←mul_sum,←Fintype.prod_sum]
    calc
      O*∏ i : I, ∑ B, W i B = O*∏ i : I,weight (q i) := by
        congr 1; apply prod_congr rfl; intro i _; exact prime_row _ (hp i) (good _ i.property).2
      _ = _ := by rw [mul_comm]; congr 1; exact prod_coe_sort T weight
theorem necessary {K : ℝ} (h :
    ∀ F : Finset Partner, (∀ b ∈ F,b.1≠0 ∧ b.2.IsPrimitive) →
      (∑ b ∈ F, ‖series triv b.2 2‖^3) ≤ K*‖series triv triv 2‖^3) : constant ≤ K := by
  apply ciSup_le
  intro T
  let U := T.filter fun p=>p.Prime ∧ 3≤p
  have good (p) (hp : p∈U) := (mem_filter.mp hp).2
  obtain ⟨F,hF,e⟩ := finite_sharp U good
  have le := h F hF
  rw [e] at le
  have eq : ∏ p ∈ U,weight p = ∏ p ∈ T, weight p := by
    apply prod_subset (filter_subset ..)
    intro p hp hn
    have ng : ¬ (p.Prime ∧ 3≤p) := fun g=>hn (mem_filter.mpr ⟨hp,g⟩)
    simp [weight,ng]
  rw [eq] at le
  exact le_of_mul_le_mul_right le (pow_pos (ordinary_pos 2 (by decide) (by decide)) 3)
end OptimalPartner

namespace OptimalPartner
open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct TwistedGoldbachMixedPrincipal
open scoped Classical BigOperators
theorem countRows {r : ℕ} [NeZero r] (α : DirichletCharacter ℂ r) (pa : α.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) (F : Finset Partner)
    (eligible : ∀ b ∈ F,b.1≠0 ∧ b.2.IsPrimitive) :
    (F.filter (fun b=> ‖series triv triv m‖ < Real.sqrt 2*‖series α b.2 m‖)).card ≤ 6 := by
  let O := ‖series triv triv m‖
  let S := F.filter (fun b=>O < Real.sqrt 2*‖series α b.2 m‖)
  have op : 0 < O := zero_lt_one.trans_le ((ordinary_at_least_one m hm he).trans (Complex.re_le_norm _))
  have pos := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)
  have ht := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have bound : cap*(Real.sqrt 2)^3 < 7 := by
    have h : Real.sqrt 2 < 17/12 := by nlinarith [sq_nonneg (Real.sqrt 2-17/12)]
    rw [pow_succ,ht]; norm_num [cap] at *; linarith
  have up := upper α pa m hm he S (fun b hb=>eligible b (mem_filter.mp hb).1)
  have prod : (S.card:ℝ)*O^3 ≤ (Real.sqrt 2)^3*∑ b ∈ S, ‖series α b.2 m‖^3 := calc
    _ = ∑ _b ∈ S,O^3 := by simp
    _ ≤ ∑ b ∈ S, (Real.sqrt 2*‖series α b.2 m‖)^3 := by
      apply sum_le_sum; intro b hb
      exact pow_le_pow_left₀ op.le ((mem_filter.mp hb).2.le) 3
    _ = _ := by simp only [mul_pow,mul_sum]
  have capBound : (S.card:ℝ)*O^3 ≤ ((Real.sqrt 2)^3*cap)*O^3 := calc
    _ ≤ _ := prod
    _ ≤ (Real.sqrt 2)^3*(constant*O^3) := mul_le_mul_of_nonneg_left up (pow_nonneg pos.le 3)
    _ ≤ (Real.sqrt 2)^3*(cap*O^3) := by gcongr; exact constant_le
    _ = _ := by ring
  have lt : (S.card:ℝ)<7 := (le_of_mul_le_mul_right capBound (pow_pos op 3)).trans_lt (by simpa [mul_comm] using bound)
  have : S.card < 7 := by exact_mod_cast lt
  exact Nat.le_of_lt_succ this
end OptimalPartner

theorem Conjectures.Goldbach.PartnerOptimalGlobalCubic :
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
  let B := Σ s : ℕ, DirichletCharacter ℂ s
  let primitive := fun b : B => b.1 ≠ 0 ∧ b.2.IsPrimitive
  let f := fun p : ℕ => if p.Prime ∧ 3 ≤ p then 1 + 1 / ((p : ℝ) - 2)^2 else 1
  exact ∃ C : ℝ, HasProd f C ∧
    (∀ K : ℝ, (∀ (r : ℕ) [NeZero r] (α : DirichletCharacter ℂ r), α.IsPrimitive →
      ∀ m : ℕ, 0 < m → Even m → ∀ F : Finset B, (∀ b ∈ F, primitive b) →
      (∑ b ∈ F, ‖S α b.2 m‖^3) ≤ K * ‖O m‖^3) ↔ C ≤ K) ∧
    (∀ (r : ℕ) [NeZero r] (α : DirichletCharacter ℂ r), α.IsPrimitive →
      ∀ m : ℕ, 0 < m → Even m → ∀ F : Finset B, (∀ b ∈ F, primitive b) →
      (F.filter (fun b => ‖O m‖ < Real.sqrt 2 * ‖S α b.2 m‖)).card ≤ 6) := by
  classical
  dsimp only
  refine ⟨OptimalPartner.constant,OptimalPartner.hasProduct,?_,?_⟩
  · intro K
    constructor
    · intro all
      apply OptimalPartner.necessary
      exact all 1 OptimalPartner.triv DirichletCharacter.isPrimitive_one_level_one 2 (by decide) (by decide)
    · intro hk r inst α hα m hm he F hF
      apply (OptimalPartner.upper α hα m hm he F hF).trans
      exact mul_le_mul_of_nonneg_right hk (pow_nonneg (norm_nonneg _) 3)
  · exact fun _ _ α hα m hm he F hF=>OptimalPartner.countRows α hα m hm he F hF
