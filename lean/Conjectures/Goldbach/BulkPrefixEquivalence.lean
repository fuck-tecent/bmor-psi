import Mathlib

noncomputable section

namespace Conjectures.Goldbach.BulkPrefixEquivalence_aux

namespace GoldbachMinor

set_option maxHeartbeats 4000000 in
def catalogueArcs (Q n : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / q| ≤ (Q : ℝ) / ((q : ℝ) * n)}

set_option maxHeartbeats 4000000 in
def catalogueCutoff (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

end GoldbachMinor

open Filter

set_option maxHeartbeats 4000000 in
theorem arcDisjoint :
    ∀ (a b q r Q n : ℕ) (t : ℝ), 0<q → 0<r → q≤Q → r≤Q → 2*Q^2<n → a*r ≠ b*q → |t-(a:ℝ)/(q:ℝ)|≤(Q:ℝ)/((q:ℝ)*n) → (Q:ℝ)/((r:ℝ)*n) < |t-(b:ℝ)/(r:ℝ)| := by
  intro a b q r Q n t hq hr hqQ hrQ hn hdistinct ha
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsmall : Q * r + Q * q < n := by
    nlinarith [Nat.mul_le_mul_left Q hrQ, Nat.mul_le_mul_left Q hqQ]
  have hradii : (Q : ℝ) / (q * n) + Q / (r * n) < 1 / (q * r) := calc
    _ = ((Q : ℝ) * r + Q * q) / (q * r * n) := by field_simp
    _ < (n : ℝ) / (q * r * n) :=
      (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
    _ = 1 / (q * r) := by field_simp
  have hsep : 1 / ((q : ℝ) * r) ≤ |(a : ℝ) / q - b / r| := by
    have hdiff : (a : ℝ) / q - b / r = (a * r - b * q) / (q * r) := by
      field_simp
    rw [hdiff, abs_div, abs_of_pos (mul_pos hqr hrr)]
    apply (div_le_div_iff_of_pos_right (mul_pos hqr hrr)).mpr
    rcases lt_or_gt_of_ne hdistinct with hab | hba
    · have hgap : (a : ℝ) * r + 1 ≤ b * q := by exact_mod_cast Nat.succ_le_of_lt hab
      linarith [neg_le_abs ((a : ℝ) * r - b * q)]
    · have hgap : (b : ℝ) * q + 1 ≤ a * r := by exact_mod_cast Nat.succ_le_of_lt hba
      linarith [le_abs_self ((a : ℝ) * r - b * q)]
  have htriangle := abs_sub_le ((a : ℝ) / q) t ((b : ℝ) / r)
  rw [abs_sub_comm ((a : ℝ) / q) t] at htriangle
  linarith

set_option maxHeartbeats 4000000 in
theorem arcCutoffScale :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 2 * ((Nat.log 2 (n + 2)) ^ 2) ^ 2 < n := by
  let C : ℝ := 2 * (2 / Real.log 2) ^ 4
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTail : ∀ᶠ n : ℕ in atTop,
      ‖Real.log (n : ℝ)‖ ≤ (1 : ℝ) * ‖(n : ℝ) ^ (1 / 8 : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 8 : ℝ))).bound zero_lt_one)
  have hpowerTail : ∀ᶠ n : ℕ in atTop, C < (n : ℝ) ^ (1 / 2 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop C
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlogTail.and hpowerTail)
  refine ⟨max 2 N, ?_⟩
  intro n hn
  have hn₂ : 2 ≤ n := (max_le_iff.mp hn).1
  obtain ⟨hlogBound, hC⟩ := hN n (max_le_iff.mp hn).2
  have hx₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn₂
  have hx : (0 : ℝ) < n := by linarith
  let p : ℝ := (n : ℝ) ^ (1 / 8 : ℝ)
  have hp : 0 ≤ p := Real.rpow_nonneg hx.le _
  have hlog : Real.log (n : ℝ) ≤ p := by
    change ‖Real.log (n : ℝ)‖ ≤ (1 : ℝ) * ‖p‖ at hlogBound
    simpa only [Real.norm_of_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ n)),
      Real.norm_of_nonneg hp, one_mul] using hlogBound
  have hadd : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith)
      (show 0 ≤ (n : ℝ) + 1 by linarith)]
  let L := Nat.log 2 (n + 2)
  have hpowNat : 2 ^ L ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
  have hpowReal : (2 : ℝ) ^ L ≤ (n : ℝ) + 2 := by exact_mod_cast hpowNat
  have hlogPow := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ L) hpowReal
  have hlogAdd := Real.log_le_log (by positivity : 0 < (n : ℝ) + 2) hadd
  rw [Real.log_pow] at hlogPow hlogAdd
  have hL : (L : ℝ) ≤ 2 * p / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr
      (hlogPow.trans (hlogAdd.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))))
  have hp4 : p ^ 4 = (n : ℝ) ^ (1 / 2 : ℝ) := by
    dsimp only [p]
    rw [← Real.rpow_mul_natCast hx.le]
    norm_num
  have hineq : 2 * (((L : ℝ) ^ 2) ^ 2) < (n : ℝ) := by
    calc
      _ ≤ 2 * ((2 * p / Real.log 2) ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2) 2)
          (by norm_num)
      _ = C * p ^ 4 := by dsimp [C]; ring
      _ = C * (n : ℝ) ^ (1 / 2 : ℝ) := by rw [hp4]
      _ < (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) :=
        mul_lt_mul_of_pos_right hC (Real.rpow_pos_of_pos hx _)
      _ = n := by
        rw [← Real.rpow_add hx, show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
  change 2 * (L ^ 2) ^ 2 < n
  exact_mod_cast hineq

namespace GoldbachMinor

open Finset Set MeasureTheory


set_option maxHeartbeats 4000000 in
private noncomputable def radius (Q n q : ℕ) : ℝ := (Q : ℝ) / ((q : ℝ) * n)

set_option maxHeartbeats 4000000 in
private noncomputable def cell (Q n q a : ℕ) : Set ℝ :=
  Icc ((a:ℝ)/q - radius Q n q) ((a:ℝ)/q + radius Q n q)

set_option maxHeartbeats 4000000 in
private theorem in_cell {Q n q a : ℕ} {t : ℝ} :
    t ∈ cell Q n q a ↔ |t - (a:ℝ)/q| ≤ radius Q n q := by
  rw [abs_le]
  change (_ ≤ t ∧ t ≤ _) ↔ _
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

set_option maxHeartbeats 4000000 in
private theorem same_center {a b q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (ha : a.Coprime q) (hb : b.Coprime r) (he : a*r=b*q) : q=r ∧ a=b := by
  have h₁ : q ∣ a*r := he ▸ Nat.dvd_mul_left q b
  have h₂ : r ∣ b*q := he.symm ▸ Nat.dvd_mul_left r a
  have eq := Nat.dvd_antisymm (ha.symm.dvd_of_dvd_mul_left h₁) (hb.symm.dvd_of_dvd_mul_left h₂)
  subst r
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

set_option maxHeartbeats 4000000 in
private theorem unique_cell {a b q r Q n : ℕ} {t : ℝ}
    (hq : q ∈ Finset.Icc 1 Q) (hr : r ∈ Finset.Icc 1 Q)
    (ha : a.Coprime q) (hb : b.Coprime r) (hscale : 2*Q^2<n)
    (ht₁ : t ∈ cell Q n q a) (ht₂ : t ∈ cell Q n r b) : q=r ∧ a=b := by
  obtain ⟨hq₁,hq₂⟩ := Finset.mem_Icc.mp hq
  obtain ⟨hr₁,hr₂⟩ := Finset.mem_Icc.mp hr
  apply same_center hq₁ hr₁ ha hb
  by_contra h
  have hsep := arcDisjoint a b q r Q n t hq₁ hr₁ hq₂ hr₂ hscale h
    (in_cell.mp ht₁)
  exact (not_lt_of_ge (in_cell.mp ht₂)) hsep

set_option maxHeartbeats 4000000 in
private def numerators (q : ℕ) : Finset ℕ := ((range (q+1)).filter (·.Coprime q))

set_option maxHeartbeats 4000000 in
private theorem split_indicator (f : ℝ → ℂ) (Q n : ℕ) (hscale : 2*Q^2<n) (t : ℝ) :
    (catalogueArcs Q n).indicator f t = ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ numerators q,
      (cell Q n q a).indicator f t := by
  classical
  by_cases ht : t ∈ catalogueArcs Q n
  · obtain ⟨q,a,hq,hqQ,ha,hca,hm⟩ := ht
    have hqr : q ∈ Finset.Icc 1 Q := Finset.mem_Icc.mpr ⟨hq,hqQ⟩
    have har : a ∈ numerators q := mem_filter.mpr ⟨mem_range.mpr (by omega),hca⟩
    have he : t ∈ cell Q n q a := in_cell.mpr hm
    rw [Set.indicator_of_mem (show t ∈ catalogueArcs Q n from ⟨q,a,hq,hqQ,ha,hca,hm⟩)]
    rw [sum_eq_single_of_mem q hqr]
    · rw [sum_eq_single_of_mem a har, Set.indicator_of_mem he]
      intro b hb hba
      apply Set.indicator_of_notMem
      exact fun h => hba (unique_cell hqr hqr (mem_filter.mp hb).2 hca hscale h he).2
    · intro r hr hrq
      apply sum_eq_zero
      intro b hb
      apply Set.indicator_of_notMem
      exact fun h => hrq (unique_cell hr hqr (mem_filter.mp hb).2 hca hscale h he).1
  · rw [Set.indicator_of_notMem ht]
    symm
    apply sum_eq_zero
    intro q hq
    apply sum_eq_zero
    intro a ha
    apply Set.indicator_of_notMem
    intro h
    exact ht ⟨q,a,(Finset.mem_Icc.mp hq).1,(Finset.mem_Icc.mp hq).2,
      by have := mem_range.mp (mem_filter.mp ha).1; omega,(mem_filter.mp ha).2,in_cell.mp h⟩

set_option maxHeartbeats 4000000 in
private noncomputable def clipped (x R : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ t in (Icc 0 1 ∩ Icc (x-R) (x+R)), f t

set_option maxHeartbeats 4000000 in
private theorem major_clipped (Q n : ℕ) (hscale : 2*Q^2<n)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n).indicator f t) =
    ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ numerators q, clipped ((a:ℝ)/q) (radius Q n q) f := by
  have hi (q a : ℕ) : IntegrableOn ((cell Q n q a).indicator f) (Icc (0:ℝ) 1) :=
    hf.integrableOn_Icc.indicator measurableSet_Icc
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  simp_rw [split_indicator f Q n hscale]
  rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ (fun a _ => hi q a))]
  apply sum_congr rfl
  intro q _
  rw [integral_finsetSum _ (fun a _ => hi q a)]
  apply sum_congr rfl
  intro a _
  exact setIntegral_indicator measurableSet_Icc

set_option maxHeartbeats 4000000 in
private theorem integral_closed {l u : ℝ} (h : l ≤ u) (f : ℝ → ℂ) :
    (∫ t in Icc l u, f t) = ∫ t in l..u, f t := by
  rw [intervalIntegral.integral_of_le h, integral_Icc_eq_integral_Ioc]

set_option maxHeartbeats 4000000 in
private theorem interior (f : ℝ → ℂ) {x R : ℝ} (hR : 0 ≤ R) (hl : 0 ≤ x-R)
    (hu : x+R ≤ 1) : clipped x R f = ∫ t in (x-R)..(x+R), f t := by
  unfold clipped
  rw [Set.inter_eq_right.mpr (Icc_subset_Icc hl hu), integral_closed (by linarith)]

set_option maxHeartbeats 4000000 in
private theorem boundary (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1)
    {R : ℝ} (hR : 0 ≤ R) (hR₁ : R ≤ 1) :
    clipped 0 R f + clipped 1 R f = ∫ t in -R..R, f t := by
  have hl : (Icc (0:ℝ) 1 ∩ Icc (0-R) (0+R)) = Icc 0 R := by
    ext t; simp only [mem_inter_iff, Set.mem_Icc]; constructor <;> intro h <;> grind
  have hr : (Icc (0:ℝ) 1 ∩ Icc (1-R) (1+R)) = Icc (1-R) 1 := by
    ext t; simp only [mem_inter_iff, Set.mem_Icc]; constructor <;> intro h <;> grind
  have trans := intervalIntegral.integral_comp_add_right (a := -R) (b := 0) f 1
  simp only [hp _,zero_add] at trans
  rw [show -R+1 = 1-R by ring] at trans
  unfold clipped
  rw [hl,hr,integral_closed hR,integral_closed (by linarith),← trans,add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)

set_option maxHeartbeats 4000000 in
private theorem normalize (q : ℕ) (hq : 0 < q) (f : ℝ → ℂ) (hf : Continuous f)
    (hp : Function.Periodic f 1) {R : ℝ} (hR : 0 ≤ R) (hsmall : R ≤ 1/(q:ℝ)) :
    (∑ a ∈ numerators q, clipped ((a:ℝ)/q) R f) =
      ∑ a ∈ (range q).filter (·.Coprime q),
        ∫ t in ((a:ℝ)/q-R)..((a:ℝ)/q+R), f t := by
  by_cases h : q=1
  · subst q
    simpa [numerators, sum_filter, sum_range_succ] using boundary f hf hp hR (by simpa using hsmall)
  have hqc : ¬ q.Coprime q := by simpa using h
  unfold numerators
  rw [range_add_one, Finset.filter_insert]; simp only [hqc, ite_false]
  apply sum_congr rfl
  intro a ha
  obtain ⟨har,hac⟩ := mem_filter.mp ha
  have hlt := mem_range.mp har
  have hap : 0 < a := by
    by_contra! hz; have : a=0 := by omega
    simp_all
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast hap
  have hsucc : (a:ℝ)+1 ≤ q := by exact_mod_cast hlt
  apply interior f hR
  · have := div_le_div_of_nonneg_right ha' hq'.le
    linarith
  · have hbound : (a:ℝ)/q + 1/q ≤ 1 := by
      rw [← add_div, div_le_one hq']; exact hsucc
    linarith

set_option maxHeartbeats 4000000 in
theorem catalogue_major_periodic (Q n : ℕ) (hscale : 2*Q^2<n)
    (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n).indicator f t) =
      ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (range q).filter (·.Coprime q),
        ∫ t in ((a:ℝ)/q-(Q:ℝ)/(q*n))..((a:ℝ)/q+(Q:ℝ)/(q*n)), f t := by
  rw [major_clipped Q n hscale f hf]
  apply sum_congr rfl
  intro q hq
  have pos := (Finset.mem_Icc.mp hq).1
  have hq' : (0:ℝ) < q := by exact_mod_cast pos
  have hn : Q ≤ n := by nlinarith [Nat.le_self_pow (by decide : 2≠0) Q]
  have hn' : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  apply normalize q pos f hf hp (by unfold radius; positivity)
  unfold radius
  rw [div_le_div_iff₀ (mul_pos hq' hn') hq']
  have h : (Q:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [mul_le_mul_of_nonneg_left h hq'.le]

end GoldbachMinor

namespace GoldbachRamanujan

open Finset Polynomial
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

set_option maxHeartbeats 4000000 in
private noncomputable def primitiveTrace (k : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun q => ∑ z ∈ primitiveRoots q ℂ, z ^ k, by simp [primitiveRoots_zero]⟩

set_option maxHeartbeats 4000000 in
private def divisibleTrace (k : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun q => if q ∣ k then (q : ℂ) else 0, by simp⟩

set_option maxHeartbeats 4000000 in
private theorem all_roots_trace {q : ℕ} (hq : 0 < q) (k : ℕ) :
    (∑ z ∈ nthRootsFinset q (1 : ℂ), z ^ k) = divisibleTrace k q := by
  let _ : NeZero q := ⟨hq.ne'⟩
  let u := Complex.exp (2 * Real.pi * Complex.I / q)
  have hu : IsPrimitiveRoot u q := Complex.isPrimitiveRoot_exp q hq.ne'
  have param : (∑ i ∈ range q, (u^k)^i) = ∑ z ∈ nthRootsFinset q (1 : ℂ), z ^ k := by
    apply sum_bij (fun i _ => u ^ i)
    · intro i _
      apply (Polynomial.mem_nthRootsFinset hq _).mpr
      rw [← pow_mul, Nat.mul_comm, pow_mul, hu.pow_eq_one, one_pow]
    · intro i hi j hj heq
      exact hu.pow_inj (mem_range.mp hi) (mem_range.mp hj) heq
    · intro z hz
      obtain ⟨i, hi, heq⟩ := hu.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hq _).mp hz)
      exact ⟨i, mem_range.mpr hi, heq⟩
    · intro i _
      rw [← pow_mul, Nat.mul_comm, pow_mul]
  rw [← param]
  change _ = if q ∣ k then (q : ℂ) else 0
  by_cases h : q ∣ k
  · simp [(hu.pow_eq_one_iff_dvd k).2 h, h]
  · have hne := (hu.pow_eq_one_iff_dvd k).not.mpr h
    have hp : (u^k)^q = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hu.pow_eq_one, one_pow]
    simp [geom_sum_eq hne, hp, h]

set_option maxHeartbeats 4000000 in
private theorem invert_trace (k : ℕ) :
    primitiveTrace k = divisibleTrace k * (μ : ArithmeticFunction ℂ) := by
  classical
  have conv : primitiveTrace k * (ζ : ArithmeticFunction ℂ) = divisibleTrace k := by
    ext q
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    change (∑ d ∈ q.divisors, ∑ z ∈ primitiveRoots d ℂ, z ^ k) = _
    rw [← sum_biUnion (fun _ _ _ _ hd => IsPrimitiveRoot.disjoint (R := ℂ) hd),
      ← IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
    rcases q with _ | q
    · simp
    · exact all_roots_trace (Nat.succ_pos _) k
  calc
    _ = primitiveTrace k * ((ζ : ArithmeticFunction ℂ) * (μ : ArithmeticFunction ℂ)) := by simp
    _ = (primitiveTrace k * (ζ : ArithmeticFunction ℂ)) * (μ : ArithmeticFunction ℂ) :=
      (mul_assoc ..).symm
    _ = _ := by rw [conv]

set_option maxHeartbeats 4000000 in
theorem all_frequencies {q : ℕ} (hq : 0 < q) (k : ℕ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      Complex.exp (((2*Real.pi*(k:ℝ)*a/q : ℝ):ℂ)*Complex.I)) =
        ∑ d ∈ q.divisors, (if d ∣ k then (d : ℂ) else 0) *
          (ArithmeticFunction.moebius (q/d) : ℂ) := by
  let _ : NeZero q := ⟨hq.ne'⟩
  let u := Complex.exp (2 * Real.pi * Complex.I / q)
  have hu : IsPrimitiveRoot u q := Complex.isPrimitiveRoot_exp q hq.ne'
  calc
    _ = ∑ z ∈ primitiveRoots q ℂ, z^k := by
      apply sum_bij (fun a _ => u ^ a)
      · intro a ha
        exact (mem_primitiveRoots hq).mpr (hu.pow_of_coprime a (mem_filter.mp ha).2)
      · intro i hi j hj heq
        exact hu.pow_inj (mem_range.mp (mem_filter.mp hi).1) (mem_range.mp (mem_filter.mp hj).1) heq
      · intro z hz
        obtain ⟨a, ha, hc, heq⟩ := hu.isPrimitiveRoot_iff.mp ((mem_primitiveRoots hq).mp hz)
        exact ⟨a, mem_filter.mpr ⟨mem_range.mpr ha, hc⟩, heq⟩
      · intro a _
        dsimp [u]
        rw [← pow_mul, ← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
    _ = _ := by
      change primitiveTrace k q = _
      rw [invert_trace, ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal (fun x y => divisibleTrace k x * (μ : ArithmeticFunction ℂ) y)]
      rfl

end GoldbachRamanujan

namespace GoldbachRamanujan

set_option maxHeartbeats 4000000 in
private noncomputable def wave (ω t : ℝ) : ℂ := Complex.exp (((ω*t : ℝ) : ℂ)*Complex.I)

set_option maxHeartbeats 4000000 in
private theorem wave_add (ω x y : ℝ) : wave ω (x+y) = wave ω x * wave ω y := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

set_option maxHeartbeats 4000000 in
private theorem interval_wave (ω x R : ℝ) (hω : ω ≠ 0) :
    (∫ t in (x-R)..(x+R), wave ω t) = wave ω x * ((2*Real.sin (ω*R)/ω : ℝ) : ℂ) := by
  have translate := intervalIntegral.integral_comp_add_left (a := -R) (b := R) (wave ω) x
  rw [← sub_eq_add_neg] at translate
  rw [← translate]
  simp_rw [wave_add]
  rw [intervalIntegral.integral_const_mul]
  apply congrArg (fun z : ℂ => wave ω x * z)
  change (∫ t in -R..R, (fun y : ℝ => Complex.exp ((y : ℂ)*Complex.I)) (ω*t)) = _
  rw [intervalIntegral.integral_comp_mul_left (a := -R) (b := R)
    (fun y : ℝ => Complex.exp ((y : ℂ)*Complex.I)) hω, mul_neg, integral_exp_mul_I_eq_sin]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_ofNat, div_eq_mul_inv]
  ring

set_option maxHeartbeats 4000000 in
theorem arcs_at_denominator {q k : ℕ} (hq : 0 < q) (hk : 0 < k) (R : ℝ) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ∫ t in ((a:ℝ)/q-R)..((a:ℝ)/q+R),
        Complex.exp (((2*Real.pi*(k:ℝ)*t : ℝ):ℂ)*Complex.I)) =
      (∑ d ∈ q.divisors, (if d ∣ k then (d:ℂ) else 0) *
        (ArithmeticFunction.moebius (q/d):ℂ)) *
      ((Real.sin (2*Real.pi*(k:ℝ)*R)/(Real.pi*k) : ℝ):ℂ) := by
  let ω := 2*Real.pi*(k:ℝ)
  have hω : ω ≠ 0 := by dsimp [ω]; positivity
  have factor : 2*Real.sin (ω*R)/ω = Real.sin (2*Real.pi*(k:ℝ)*R)/(Real.pi*k) := by
    dsimp [ω]
    ring
  change (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    ∫ t in ((a:ℝ)/q-R)..((a:ℝ)/q+R), wave ω t) = _
  simp_rw [interval_wave _ _ _ hω, factor]
  rw [← Finset.sum_mul, ← all_frequencies hq k]
  apply congrArg (fun z : ℂ => z * ((Real.sin (2*Real.pi*(k:ℝ)*R)/(Real.pi*k):ℝ):ℂ))
  apply Finset.sum_congr rfl
  intro a _
  unfold wave ω
  rw [← mul_div_assoc]

end GoldbachRamanujan

namespace GoldbachMinor

open Finset

set_option maxHeartbeats 4000000 in
noncomputable def ram (q k : ℕ) : ℝ :=
  ∑ d ∈ q.divisors, (if d ∣ k then (d:ℝ) else 0) * (ArithmeticFunction.moebius (q/d):ℝ)

set_option maxHeartbeats 4000000 in
noncomputable def arcLength (Q n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, q.totient * (2*(Q:ℝ)/(q*n))

set_option maxHeartbeats 4000000 in
noncomputable def majorCoefficient (Q n k : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ram q k *
    (Real.sin (2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n))) / (Real.pi*k))

set_option maxHeartbeats 4000000 in
noncomputable def minorCoefficient (Q n k : ℕ) : ℝ :=
  if k=0 then 1 - arcLength Q n else -majorCoefficient Q n k

end GoldbachMinor

namespace GoldbachMinor
open Finset

set_option maxHeartbeats 4000000 in
noncomputable def harmonicCutoff (Q : ℕ) : ℝ := ∑ d ∈ Finset.Icc 1 Q, 1/(d:ℝ)

set_option maxHeartbeats 4000000 in
private theorem harmonic_divisors (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (q.divisors.card:ℝ)/(q:ℝ)) ≤ harmonicCutoff Q ^ 2 := by
  classical
  let F (p : ℕ × ℕ) : ℝ := (1/(p.1:ℝ))*(1/(p.2:ℝ))
  let S := Finset.Icc 1 Q
  have eq (q : ℕ) (hq : q ∈ S) :
      (q.divisors.card:ℝ)/q = ∑ p ∈ q.divisorsAntidiagonal, F p := by
    change _ = ∑ p ∈ q.divisorsAntidiagonal, 1/(p.1:ℝ)*(1/(p.2:ℝ))
    rw [Nat.sum_divisorsAntidiagonal (fun x y => 1/(x:ℝ)*(1/(y:ℝ)))]
    calc
      _ = ∑ _d ∈ q.divisors, 1/(q:ℝ) := by simp [div_eq_mul_inv,nsmul_eq_mul]
      _ = _ := by
        apply sum_congr rfl
        intro d hd
        have hprod : (d:ℝ)*((q/d:ℕ):ℝ) = q := by exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1
        rw [one_div_mul_one_div,hprod]
  have disj : (S:Set ℕ).PairwiseDisjoint Nat.divisorsAntidiagonal := by
    intro q _ r _ hqr
    apply disjoint_left.mpr
    intro p hp hp'
    exact hqr ((Nat.mem_divisorsAntidiagonal.mp hp).1.symm.trans (Nat.mem_divisorsAntidiagonal.mp hp').1)
  have sub : S.biUnion Nat.divisorsAntidiagonal ⊆ S ×ˢ S := by
    intro p hp
    obtain ⟨q,hq,hp⟩ := mem_biUnion.mp hp
    obtain ⟨h1,h2⟩ := mem_Icc.mp hq
    obtain ⟨e,_⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hpos : 0 < p.1*p.2 := e ▸ h1
    have ha : 0 < p.1 := Nat.pos_of_ne_zero (left_ne_zero_of_mul hpos.ne')
    have hb : 0 < p.2 := Nat.pos_of_ne_zero (right_ne_zero_of_mul hpos.ne')
    have ha' : p.1≤q := by rw [←e]; exact Nat.le_mul_of_pos_right _ hb
    have hb' : p.2≤q := by rw [←e,mul_comm]; exact Nat.le_mul_of_pos_right _ ha
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨ha,ha'.trans h2⟩,mem_Icc.mpr ⟨hb,hb'.trans h2⟩⟩
  calc
    _ = ∑ q ∈ S, ∑ p ∈ q.divisorsAntidiagonal, F p := sum_congr rfl eq
    _ = ∑ p ∈ S.biUnion Nat.divisorsAntidiagonal, F p := (sum_biUnion disj).symm
    _ ≤ ∑ p ∈ S ×ˢ S, F p := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by dsimp [F]; positivity)
    _ = _ := by simp [F, S, harmonicCutoff, sq, sum_product, sum_mul, mul_sum]; rw [sum_comm]

set_option maxHeartbeats 4000000 in
private theorem ram_frequency_sum (q K : ℕ) : (∑ k ∈ Finset.Icc 1 K, |ram q k|) ≤
    (K:ℝ)*q.divisors.card := by
  have one (k : ℕ) : |ram q k| ≤ ∑ d ∈ q.divisors, if d ∣ k then (d:ℝ) else 0 := by
    refine (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum (fun d _ => ?_))
    split_ifs <;> rcases ArithmeticFunction.moebius_eq_or (q/d) with h|h|h <;> simp [h]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ∑ d ∈ q.divisors, if d ∣ k then (d:ℝ) else 0 :=
      sum_le_sum (fun k _ => one k)
    _ = ∑ d ∈ q.divisors, ∑ k ∈ Finset.Icc 1 K, if d ∣ k then (d:ℝ) else 0 := sum_comm
    _ ≤ ∑ _d ∈ q.divisors, (K:ℝ) := by
      apply sum_le_sum
      intro d _
      have same : Finset.Icc 1 K = Finset.Ioc 0 K := by ext k; simp only [mem_Icc,mem_Ioc]; omega
      rw [same, ← sum_filter, sum_const, Nat.Ioc_filter_dvd_card_eq_div,nsmul_eq_mul]
      exact_mod_cast Nat.div_mul_le_self K d
    _ = _ := by simp [mul_comm]

set_option maxHeartbeats 4000000 in
theorem coefficient_mean (Q n K : ℕ) (hn : 0<n) :
    (∑ k ∈ Finset.Icc 1 K, |majorCoefficient Q n k|) ≤
      (2*(Q:ℝ)/n)*K*(harmonicCutoff Q)^2 := by
  let A := 2*(Q:ℝ)/n
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have term (k : ℕ) (hk : k ∈ Finset.Icc 1 K) : |majorCoefficient Q n k| ≤
      ∑ q ∈ Finset.Icc 1 Q, (A/(q:ℝ))*|ram q k| := by
    have hkp : 0<(k:ℝ) := by exact_mod_cast (mem_Icc.mp hk).1
    have hp : 0<Real.pi*(k:ℝ) := mul_pos Real.pi_pos hkp
    refine (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum (fun q hq => ?_))
    have hq' : 0<(q:ℝ) := by exact_mod_cast (mem_Icc.mp hq).1
    have hx : 0≤2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n)) := by positivity
    have hs := Real.abs_sin_le_abs (x:=2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n)))
    rw [abs_of_nonneg hx] at hs
    rw [abs_mul,abs_div,abs_of_pos hp,mul_comm (A/(q:ℝ))]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    refine (div_le_div_of_nonneg_right hs hp.le).trans_eq ?_
    dsimp [A]
    field_simp
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ∑ q ∈ Finset.Icc 1 Q, (A/(q:ℝ))*|ram q k| := sum_le_sum term
    _ = ∑ q ∈ Finset.Icc 1 Q, (A/(q:ℝ)) * (∑ k ∈ Finset.Icc 1 K, |ram q k|) := by
      rw [sum_comm]; simp_rw [mul_sum]
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, (A/(q:ℝ))*((K:ℝ)*q.divisors.card) := by
      apply sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_left (ram_frequency_sum q K) (by positivity)
    _ = A*K*(∑ q ∈ Finset.Icc 1 Q, (q.divisors.card:ℝ)/q) := by
      rw [mul_sum]; apply sum_congr rfl; intro q _; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_divisors Q) (mul_nonneg hA (by positivity))

end GoldbachMinor

namespace GoldbachMinor

open Finset Set MeasureTheory
open scoped ComplexConjugate

set_option maxHeartbeats 4000000 in
noncomputable def mode (k : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (((2*Real.pi*(k:ℝ)*t : ℝ):ℂ)*Complex.I)

set_option maxHeartbeats 4000000 in
theorem measurable_catalogue (Q n : ℕ) : MeasurableSet (catalogueArcs Q n) := by
  have eq : catalogueArcs Q n = ⋃ (q : ℕ) (a : ℕ)
      (_ : 1≤q ∧ q≤Q ∧ a≤q ∧ a.Coprime q),
      Icc ((a:ℝ)/q - (Q:ℝ)/(q*n)) ((a:ℝ)/q + (Q:ℝ)/(q*n)) := by
    ext t
    simp only [mem_iUnion, Set.mem_Icc, catalogueArcs, Set.mem_ofPred_eq, abs_le]
    constructor
    · rintro ⟨q,a,h₁,h₂,h₃,h₄,hl,hr⟩
      exact ⟨q,a,⟨h₁,h₂,h₃,h₄⟩,by linarith,by linarith⟩
    · rintro ⟨q,a,⟨h₁,h₂,h₃,h₄⟩,hl,hr⟩
      exact ⟨q,a,h₁,h₂,h₃,h₄,by linarith,by linarith⟩
  rw [eq]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun _ => measurableSet_Icc

set_option maxHeartbeats 4000000 in
theorem integral_complement (A : Set ℝ) (hA : MeasurableSet A) (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ t in (0:ℝ)..1, Aᶜ.indicator f t) = (∫ t in (0:ℝ)..1, f t) -
      ∫ t in (0:ℝ)..1, A.indicator f t := by
  have hi : IntervalIntegrable (A.indicator f) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self).indicator hA
  rw [← intervalIntegral.integral_sub (hf.intervalIntegrable ..) hi]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases ht : t ∈ A <;> simp [ht]

set_option maxHeartbeats 4000000 in
theorem mode_continuous (k : ℤ) : Continuous (mode k) := by unfold mode; fun_prop

set_option maxHeartbeats 4000000 in
private theorem mode_periodic (k : ℤ) : Function.Periodic (mode k) 1 := by
  intro t
  unfold mode
  calc
    _ = Complex.exp (((2*Real.pi*(k:ℝ)*t : ℝ):ℂ)*Complex.I) *
        Complex.exp ((k:ℂ)*(2*Real.pi*Complex.I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    _ = _ := by rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]

set_option maxHeartbeats 4000000 in
private theorem mode_neg (k : ℤ) (t : ℝ) : mode (-k) t = conj (mode k t) := by
  unfold mode
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

set_option maxHeartbeats 4000000 in
private theorem full_mode (k : ℕ) (hk : 0 < k) : (∫ t in (0:ℝ)..1, mode (k:ℤ) t) = 0 := by
  let c : ℂ := (k:ℂ)*(2*Real.pi*Complex.I)
  have hc : c ≠ 0 := by
    dsimp [c]; exact mul_ne_zero (by exact_mod_cast hk.ne') (mul_ne_zero (by exact_mod_cast (mul_ne_zero (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero)) Complex.I_ne_zero)
  have he (t : ℝ) : mode (k:ℤ) t = Complex.exp (c*t) := by
    unfold mode c; congr 1; push_cast; ring
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [c, Complex.exp_nat_mul_two_pi_mul_I]

set_option maxHeartbeats 4000000 in
private theorem ram_cast (q k : ℕ) : (ram q k : ℂ) = ∑ d ∈ q.divisors,
    (if d ∣ k then (d:ℂ) else 0) * (ArithmeticFunction.moebius (q/d):ℂ) := by
  unfold ram
  push_cast
  apply sum_congr rfl
  intro d _
  split_ifs <;> simp

set_option maxHeartbeats 4000000 in
private theorem major_pos_mode (Q n k : ℕ) (hscale : 2*Q^2<n) (hk : 0<k) :
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n).indicator (mode (k:ℤ)) t) =
      (majorCoefficient Q n k:ℂ) := by
  rw [catalogue_major_periodic _ _ hscale _ (mode_continuous _) (mode_periodic _)]
  unfold majorCoefficient
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro q hq
  rw [Complex.ofReal_mul, ram_cast]
  simpa only [mode, Int.cast_natCast] using GoldbachRamanujan.arcs_at_denominator
    (Finset.mem_Icc.mp hq).1 hk ((Q:ℝ)/(q*n))

set_option maxHeartbeats 4000000 in
private theorem major_zero (Q n : ℕ) (hscale : 2*Q^2<n) :
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n).indicator (mode 0) t) = (arcLength Q n:ℂ) := by
  rw [catalogue_major_periodic _ _ hscale _ (mode_continuous _) (mode_periodic _)]
  unfold arcLength
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro q _
  have hcard : ((range q).filter (·.Coprime q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]; congr 1; ext a; simp only [mem_filter]; exact and_congr_right fun _ => Nat.coprime_comm
  have hint (a : ℕ) : (∫ t in ((a:ℝ)/q-(Q:ℝ)/(q*n))..((a:ℝ)/q+(Q:ℝ)/(q*n)), mode 0 t)
      = ((2*(Q:ℝ)/(q*n):ℝ):ℂ) := by
    simp [mode, intervalIntegral.integral_const, Complex.real_smul]
    ring
  simp_rw [hint]
  simp [hcard, nsmul_eq_mul]

set_option maxHeartbeats 4000000 in
theorem minor_mode (Q n : ℕ) (hscale : 2*Q^2<n) (k : ℤ) :
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n)ᶜ.indicator (mode k) t) =
      (minorCoefficient Q n k.natAbs:ℂ) := by
  have nat_mode (j : ℕ) : (∫ t in (0:ℝ)..1, (catalogueArcs Q n)ᶜ.indicator (mode (j:ℤ)) t) =
      (minorCoefficient Q n j:ℂ) := by
    rw [integral_complement _ (measurable_catalogue ..) _ (mode_continuous _)]
    rcases j with _ | j
    · rw [Nat.cast_zero,major_zero Q n hscale]
      simp [mode, minorCoefficient, intervalIntegral.integral_const]
    · rw [full_mode _ (Nat.succ_pos _), major_pos_mode _ _ _ hscale (Nat.succ_pos _)]
      simp [minorCoefficient]
  cases k with
  | ofNat j => exact nat_mode j
  | negSucc j =>
    change (∫ t in (0:ℝ)..1, (catalogueArcs Q n)ᶜ.indicator (mode (-((j+1:ℕ):ℤ))) t) = _
    have hm (t : ℝ) : (catalogueArcs Q n)ᶜ.indicator (mode (-((j+1:ℕ):ℤ))) t =
        conj ((catalogueArcs Q n)ᶜ.indicator (mode ((j+1:ℕ):ℤ)) t) := by
      by_cases h : t ∈ (catalogueArcs Q n)ᶜ
      · simp only [Set.indicator_of_mem h]; exact mode_neg _ t
      · simp only [Set.indicator_of_notMem h, map_zero]
    simp_rw [hm]
    rw [intervalIntegral.intervalIntegral_conj, nat_mode, Complex.conj_ofReal]
    rfl

end GoldbachMinor

namespace GoldbachWeight

open Finset

set_option maxHeartbeats 4000000 in
noncomputable def high (n k : ℕ) : ℝ :=
  if k ^ 3 ≤ n then 0 else if k.Prime then Real.log k else 0

set_option maxHeartbeats 4000000 in
noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

set_option maxHeartbeats 4000000 in
noncomputable def spectrum (n : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n+1), (w k : ℂ) * phase ((k : ℝ)*t)

end GoldbachWeight

namespace GoldbachMinor

open Finset Set MeasureTheory GoldbachWeight

set_option maxHeartbeats 4000000 in
def offset (n p r : ℕ) : ℤ := (p:ℤ)+r-n

set_option maxHeartbeats 4000000 in
noncomputable def arithmeticBulk (Q n : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ range (n+1), ∑ r ∈ range (n+1),
    w p * w r * minorCoefficient Q n (offset n p r).natAbs

set_option maxHeartbeats 4000000 in
private theorem expand_spectrum (n : ℕ) (w : ℕ → ℝ) (t : ℝ) :
    GoldbachWeight.spectrum n w t * GoldbachWeight.spectrum n w t * phase (-(n:ℝ)*t) =
    ∑ p ∈ range (n+1), ∑ r ∈ range (n+1), (↑(w p*w r):ℂ)*mode (offset n p r) t := by
  unfold GoldbachWeight.spectrum
  simp only [sum_mul,mul_sum]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro r _
  have hph : phase ((p:ℝ)*t) * phase ((r:ℝ)*t) * phase (-(n:ℝ)*t) = mode (offset n p r) t := by
    unfold phase mode offset
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  push_cast
  rw [← hph]
  ring

set_option maxHeartbeats 4000000 in
private theorem integrate_sum {ι : Type*} (s : Finset ι) (A : Set ℝ) (hA : MeasurableSet A)
    (f : ι → ℝ → ℂ) (hc : ∀ i ∈ s, Continuous (f i)) :
    (∫ t in (0:ℝ)..1, A.indicator (fun u => ∑ i ∈ s, f i u) t) =
      ∑ i ∈ s, ∫ t in (0:ℝ)..1, A.indicator (f i) t := by
  have point (t : ℝ) : A.indicator (fun u => ∑ i ∈ s, f i u) t = ∑ i ∈ s, A.indicator (f i) t := by
    by_cases h : t ∈ A <;> simp [h]
  simp_rw [point]
  apply intervalIntegral.integral_finsetSum
  intro i hi
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact ((hc i hi).integrableOn_Icc.mono_set Ioc_subset_Icc_self).indicator hA

set_option maxHeartbeats 4000000 in
theorem integral_eq_arithmeticBulk (Q n : ℕ) (hn : 2*Q^2<n) (w : ℕ → ℝ) :
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n)ᶜ.indicator (fun u =>
      GoldbachWeight.spectrum n w u * GoldbachWeight.spectrum n w u * phase (-(n:ℝ)*u)) t)
      = (arithmeticBulk Q n w:ℂ) := by
  have hA := (measurable_catalogue Q n).compl
  have hc (p r : ℕ) : Continuous (fun t => (↑(w p*w r):ℂ)*mode (offset n p r) t) :=
    continuous_const.mul (mode_continuous _)
  simp_rw [expand_spectrum]
  rw [integrate_sum _ _ hA _ (fun p _ => continuous_finsetSum _ (fun r _ => hc p r))]
  unfold arithmeticBulk
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro p _
  rw [integrate_sum _ _ hA _ (fun r _ => hc p r), Complex.ofReal_sum]
  apply sum_congr rfl
  intro r _
  simp_rw [Set.indicator_const_mul,intervalIntegral.integral_const_mul,minor_mode Q n hn]
  push_cast
  rfl

end GoldbachMinor

namespace GoldbachMinor

open Finset GoldbachWeight

set_option maxHeartbeats 4000000 in
private def neighbours (n p K : ℕ) : Finset ℕ :=
  (range (n+1)).filter fun r => offset n p r ≠ 0 ∧ (offset n p r).natAbs ≤ K

set_option maxHeartbeats 4000000 in
noncomputable def nearBulk (Q n K : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ range (n+1), ∑ r ∈ neighbours n p K,
    w p*w r*minorCoefficient Q n (offset n p r).natAbs

set_option maxHeartbeats 4000000 in
noncomputable def trimmedBulk (Q n K : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ range (n+1), ∑ r ∈ range (n+1), if offset n p r = 0 ∨ K < (offset n p r).natAbs then
    w p*w r*minorCoefficient Q n (offset n p r).natAbs else 0

set_option maxHeartbeats 4000000 in
theorem split_near (Q n K : ℕ) (w : ℕ → ℝ) :
    arithmeticBulk Q n w = nearBulk Q n K w + trimmedBulk Q n K w := by
  unfold arithmeticBulk nearBulk trimmedBulk neighbours
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rw [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro r _
  by_cases h : offset n p r ≠ 0 ∧ (offset n p r).natAbs ≤ K
  · simp [h]
  · have h' : offset n p r = 0 ∨ K < (offset n p r).natAbs := by omega
    simp [h,h']

set_option maxHeartbeats 4000000 in
def logWidth (n : ℕ) : ℕ := Nat.log 2 (n+2) + 1

end GoldbachMinor

namespace GoldbachMinor
open Finset GoldbachWeight

set_option maxHeartbeats 4000000 in
private theorem row_modes (n p K : ℕ) (f : ℕ → ℝ) (hf : ∀ k, 0≤f k) :
    (∑ r ∈ (range (n+1)).filter (fun r => offset n p r ≠ 0 ∧ (offset n p r).natAbs ≤ K),
      f (offset n p r).natAbs) ≤ 2 * ∑ k ∈ Finset.Icc 1 K, f k := by
  classical
  let S := (range (n+1)).filter (fun r => offset n p r ≠ 0 ∧ (offset n p r).natAbs ≤ K)
  let tag (r : ℕ) : ℕ × ℕ := (if offset n p r < 0 then 0 else 1,(offset n p r).natAbs)
  have inj : Set.InjOn tag S := by
    intro x _ y _ h
    have hs := congrArg Prod.fst h
    have hm := Int.natAbs_eq_natAbs_iff.mp (congrArg Prod.snd h : (offset n p x).natAbs = (offset n p y).natAbs)
    dsimp only [tag] at hs
    by_cases hx : offset n p x < 0 <;> by_cases hy : offset n p y < 0 <;>
      simp [hx,hy] at hs <;> unfold offset at * <;> omega
  have sub : S.image tag ⊆ range 2 ×ˢ Finset.Icc 1 K := by
    intro x hx
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hx
    obtain ⟨_,hz,hm⟩ := mem_filter.mp hr
    exact mem_product.mpr ⟨mem_range.mpr (by dsimp [tag]; split <;> decide),mem_Icc.mpr ⟨Int.natAbs_pos.mpr hz,hm⟩⟩
  calc
    _ ≤ ∑ x ∈ range 2 ×ˢ Finset.Icc 1 K, f x.2 :=
      sum_le_sum_of_injOn tag inj sub (fun _ _ => le_rfl) (fun a _ _ => hf a.2)
    _ = _ := by simp [sum_product,two_mul]

set_option maxHeartbeats 4000000 in
private theorem near_mass_bound (Q n K : ℕ) (hn : 0<n) (w : ℕ → ℝ) (W : ℝ)
    (hW : 0≤W) (hw : ∀ p ≤ n, |w p| ≤ W) :
    |nearBulk Q n K w| ≤ (∑ p ∈ range (n+1), |w p|) * W * 2 *
      ((2*(Q:ℝ)/n)*K*(harmonicCutoff Q)^2) := by
  let B := (2*(Q:ℝ)/n)*K*(harmonicCutoff Q)^2
  let C (k : ℕ) := |majorCoefficient Q n k|
  let S (p : ℕ) := (range (n+1)).filter (fun r => offset n p r ≠ 0 ∧ (offset n p r).natAbs ≤ K)
  have row (p : ℕ) : |∑ r ∈ S p, w p*w r*minorCoefficient Q n (offset n p r).natAbs| ≤
      |w p| *(W*2*B) := by
    calc
      _ ≤ _ := Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ r ∈ S p, (|w p| *W)*C (offset n p r).natAbs := by
        apply sum_le_sum
        intro r hr
        obtain ⟨hrn,hne,_⟩ := mem_filter.mp hr
        have hk := Int.natAbs_pos.mpr hne
        simp only [minorCoefficient,ne_of_gt hk,ite_false,abs_mul,abs_neg,C]
        gcongr
        exact hw r (by have := mem_range.mp hrn; omega)
      _ = (|w p| *W)* ∑ r ∈ S p, C (offset n p r).natAbs := (mul_sum ..).symm
      _ ≤ (|w p| *W)*(2*∑ k ∈ Finset.Icc 1 K, C k) := by
        apply mul_le_mul_of_nonneg_left (row_modes n p K C (fun _ => abs_nonneg _)) (by positivity)
      _ ≤ (|w p| *W)*(2*B) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (coefficient_mean Q n K hn) (by norm_num)
      _ = _ := by ring
  unfold nearBulk
  refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun p _ => row p)).trans_eq ?_)
  rw [← sum_mul]; ring

set_option maxHeartbeats 4000000 in
private theorem high_nonneg (n p : ℕ) : 0≤high n p := by
  unfold high
  split_ifs <;> positivity

set_option maxHeartbeats 4000000 in
private theorem high_mass (n : ℕ) : (∑ p ∈ range (n+1), |high n p|) ≤ Real.log 4*n := by
  refine le_trans ?_ (Chebyshev.theta_le_log4_mul_x (show 0≤(n:ℝ) by positivity))
  rw [Chebyshev.theta_eq_sum_Icc,Nat.floor_natCast,sum_filter]
  have eq : Finset.Icc 0 n = range (n+1) := by ext k; simp
  rw [eq]
  apply sum_le_sum
  intro p _
  rw [abs_of_nonneg (high_nonneg n p)]
  unfold high
  split_ifs <;> first | exact le_rfl | positivity

set_option maxHeartbeats 4000000 in
private theorem high_le_log (n p : ℕ) (hn : 0<n) (hp : p≤n) : |high n p| ≤ Real.log n := by
  rw [abs_of_nonneg (high_nonneg n p)]
  unfold high
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  split_ifs with _ h
  · exact hlog
  · exact Real.log_le_log (by exact_mod_cast h.pos) (by exact_mod_cast hp)
  · exact hlog

set_option maxHeartbeats 4000000 in
theorem prime_band_bound (Q n K : ℕ) (hn : 0<n) :
    |nearBulk Q n K (high n)| ≤ 4*Real.log 4*Real.log n*Q*K*(harmonicCutoff Q)^2 := by
  have hlog : 0≤Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hp : 0<(n:ℝ) := by exact_mod_cast hn
  calc
    _ ≤ _ := near_mass_bound Q n K hn (high n) _ hlog (fun p h => high_le_log n p hn h)
    _ ≤ (Real.log 4*n)*Real.log n*2*((2*(Q:ℝ)/n)*K*(harmonicCutoff Q)^2) := by
      gcongr
      exact high_mass n
    _ = _ := by field_simp; ring

end GoldbachMinor

namespace FrozenBulk

set_option maxHeartbeats 4000000 in
noncomputable def deskW (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k:ℝ) else 0

set_option maxHeartbeats 4000000 in
noncomputable def deskE (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

set_option maxHeartbeats 4000000 in
noncomputable def deskS (n : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*deskE ((k:ℝ)*t))

set_option maxHeartbeats 4000000 in
noncomputable def deskArcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤(Nat.log 2 (n+2))^2 ∧ a≤q ∧ Nat.Coprime a q ∧
    |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ))}

set_option maxHeartbeats 4000000 in
noncomputable def deskLow (n k : ℕ) : ℝ := if k^3≤n then deskW k else 0

set_option maxHeartbeats 4000000 in
noncomputable def deskHigh (n k : ℕ) : ℝ := deskW k - deskLow n k

set_option maxHeartbeats 4000000 in
noncomputable def deskI (n:ℕ) (a b:ℕ→ℝ) : ℂ :=
  intervalIntegral (fun t => (deskArcs n)ᶜ.indicator
    (fun u => deskS n a u*deskS n b u*deskE (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume

set_option maxHeartbeats 4000000 in
def BulkFloor : Prop :=
  ∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n≥N, Even n → -(e*(n:ℝ)) ≤ (deskI n (deskHigh n) (deskHigh n)).re

set_option maxHeartbeats 4000000 in
theorem deskE_eq (x : ℝ) : deskE x = GoldbachWeight.phase x := rfl

set_option maxHeartbeats 4000000 in
theorem deskS_eq (n : ℕ) (w : ℕ → ℝ) (t : ℝ) :
    deskS n w t = GoldbachWeight.spectrum n w t := rfl

set_option maxHeartbeats 4000000 in
theorem deskArcs_eq (n : ℕ) :
    deskArcs n = GoldbachMinor.catalogueArcs (GoldbachMinor.catalogueCutoff n) n := rfl

set_option maxHeartbeats 4000000 in
theorem deskI_eq (n : ℕ) (a b : ℕ → ℝ) :
    deskI n a b = intervalIntegral
      (fun t => (GoldbachMinor.catalogueArcs (GoldbachMinor.catalogueCutoff n) n)ᶜ.indicator
        (fun u => GoldbachWeight.spectrum n a u * GoldbachWeight.spectrum n b u *
          GoldbachWeight.phase (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume := by
  simp only [deskI, deskArcs_eq, deskS_eq, deskE_eq]

end FrozenBulk

namespace GoldbachMinor

open Filter GoldbachWeight FrozenBulk
open scoped Topology

set_option maxHeartbeats 4000000 in
def primeBandWidth (n : ℕ) : ℕ := n/(logWidth n)^4

set_option maxHeartbeats 4000000 in
theorem logWidth_tends : Tendsto logWidth atTop atTop := by
  apply tendsto_atTop.mpr
  intro K
  filter_upwards [eventually_ge_atTop (2^K)] with n hn
  have h := Nat.le_log_of_pow_le (by decide : 1<2) (show 2^K ≤ n+2 by omega)
  unfold logWidth
  omega

set_option maxHeartbeats 4000000 in
theorem primeBandWidth_tends : Tendsto primeBandWidth atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  have hb : 0 < 4*((B:ℝ)+1) := by positivity
  have htail := (tendsto_pow_const_div_const_pow_of_one_lt 4 (by norm_num : (1:ℝ)<2)).eventually_lt_const
    (one_div_pos.mpr hb)
  filter_upwards [logWidth_tends.eventually htail, eventually_ge_atTop 2] with n h hn
  have hpow := Nat.pow_log_le_self 2 (show n+2≠0 by omega)
  have h2 : 2^(logWidth n) ≤ 4*n := by
    unfold logWidth
    rw [pow_succ]
    omega
  have hexp : (2:ℝ)^(logWidth n) ≤ 4*(n:ℝ) := by exact_mod_cast h2
  have h1 := (div_lt_div_iff₀ (by positivity : 0<(2:ℝ)^(logWidth n)) hb).1 h
  have hnon : 0 ≤ (logWidth n:ℝ)^4 := by positivity
  have hmul : (B:ℝ)*(logWidth n:ℝ)^4 ≤ n := by nlinarith only [h1,hexp,hnon]
  exact (Nat.le_div_iff_mul_le (pow_pos (by dsimp [logWidth]; omega) 4)).2 (by exact_mod_cast hmul)

set_option maxHeartbeats 4000000 in
private theorem high_matches : deskHigh = high := by
  funext n k
  simp only [deskHigh, deskLow, deskW, high]
  split_ifs <;> ring

set_option maxHeartbeats 4000000 in
theorem catalogue_bulk_arithmetic (n : ℕ) (hn : 2*(catalogueCutoff n)^2<n) :
    (deskI n (deskHigh n) (deskHigh n)).re = arithmeticBulk (catalogueCutoff n) n (high n) := by
  have h : deskI n (deskHigh n) (deskHigh n) = (arithmeticBulk (catalogueCutoff n) n (deskHigh n):ℂ) := by
    rw [FrozenBulk.deskI_eq]
    exact integral_eq_arithmeticBulk (catalogueCutoff n) n hn (deskHigh n)
  rw [h,high_matches,Complex.ofReal_re]

set_option maxHeartbeats 4000000 in
theorem catalogue_trimmed_iff_of_negligible (width : ℕ → ℕ)
    (small : ∀ ε : ℝ, 0<ε → ∃ M : ℕ, ∀ n ≥ M,
      |nearBulk (catalogueCutoff n) n (width n) (high n)| ≤ ε*n) : BulkFloor ↔ ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
    -(ε*(n:ℝ)) ≤ trimmedBulk (catalogueCutoff n) n (width n) (high n) := by
  obtain ⟨S,hS⟩ : ∃ S:ℕ, ∀ n≥S, 2*(catalogueCutoff n)^2<n :=
    arcCutoffScale
  change (∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
    -(ε*(n:ℝ)) ≤ (deskI n (deskHigh n) (deskHigh n)).re) ↔ _
  constructor <;> intro h ε hε <;>
    obtain ⟨N,hN⟩ := h (ε/2) (half_pos hε) <;>
    obtain ⟨M,hM⟩ := small (ε/2) (half_pos hε) <;>
    refine ⟨max S (max N M), fun n hn heven => ?_⟩ <;>
    have hi := catalogue_bulk_arithmetic n (hS n (by omega)) <;>
    have hs := split_near (catalogueCutoff n) n (width n) (high n) <;>
    obtain ⟨hl,hu⟩ := abs_le.mp (hM n (by omega)) <;>
    linarith only [hi,hs,hl,hu,hN n (by omega) heven]

set_option maxHeartbeats 4000000 in
private theorem width_pos (n : ℕ) : 0 < logWidth n := Nat.succ_pos _

set_option maxHeartbeats 4000000 in
private theorem log_n_le_width (n : ℕ) (hn : 0<n) : Real.log n ≤ (logWidth n:ℝ) := by
  have h := Nat.lt_pow_succ_log_self (by decide : 1<2) (n+2)
  have hpow : (n:ℝ) ≤ (2:ℝ)^(logWidth n) := by
    exact_mod_cast (show n ≤ 2^(logWidth n) by unfold logWidth; omega)
  have hh := Real.log_le_log (by exact_mod_cast hn) hpow
  rw [Real.log_pow] at hh
  have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  exact hh.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans_eq (mul_one _))

set_option maxHeartbeats 4000000 in
private theorem harmonic_le_log (Q : ℕ) : harmonicCutoff Q ≤ 1+Real.log Q := by
  simpa only [harmonicCutoff,one_div,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    using harmonic_le_one_add_log Q

set_option maxHeartbeats 4000000 in
theorem prime_band_uniform (n : ℕ) (hn : 0<n) :
    |nearBulk (catalogueCutoff n) n (primeBandWidth n) (high n)| ≤
    (4*Real.log 4)*n*((1+2*Real.log (logWidth n:ℝ))^2/(logWidth n:ℝ)) := by
  let L := (logWidth n:ℝ)
  have hL : 0<L := by dsimp only [L]; exact_mod_cast width_pos n
  have hL1 : 1≤L := by dsimp only [L]; exact_mod_cast (show 1≤logWidth n from width_pos n)
  have hq : (catalogueCutoff n:ℝ) ≤ L^2 := by
    dsimp [catalogueCutoff,L,logWidth]
    push_cast
    nlinarith [show 0≤(Nat.log 2 (n+2):ℝ) by positivity]
  have hm := Nat.le_log_of_pow_le (by decide : 1<2) (show 2^1 ≤ n+2 by omega)
  have hQ : 0 < (catalogueCutoff n:ℝ) := by unfold catalogueCutoff; positivity
  have hhl : harmonicCutoff (catalogueCutoff n) ≤ 1+2*Real.log L := by
    have hlog := Real.log_le_log hQ hq
    rw [Real.log_pow] at hlog
    exact (harmonic_le_log _).trans (add_le_add_right (by simpa using hlog) _)
  have hh : 0 ≤ harmonicCutoff (catalogueCutoff n) := by unfold harmonicCutoff; positivity
  have hK : (primeBandWidth n:ℝ)*L^4 ≤ n := by
    dsimp [primeBandWidth,L]
    exact_mod_cast Nat.div_mul_le_self n ((logWidth n)^4)
  calc
    _ ≤ _ := prime_band_bound _ _ _ hn
    _ ≤ 4*Real.log 4*L*(L^2)*(primeBandWidth n:ℝ)*(1+2*Real.log L)^2 := by
      gcongr
      exact log_n_le_width n hn
    _ = (4*Real.log 4)*((primeBandWidth n:ℝ)*L^4)*((1+2*Real.log L)^2/L) := by
      field_simp
    _ ≤ _ := by gcongr

set_option maxHeartbeats 4000000 in
private theorem log_bound_ratio :
    Tendsto (fun x : ℝ => (1+2*Real.log x)^2/x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => 1/Real.sqrt x) atTop (𝓝 0) := by
    simpa [one_div,Function.comp_def] using (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop)
  have h2 : Tendsto (fun x : ℝ => Real.log x/Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
  have hc : Tendsto (fun x : ℝ => (1/Real.sqrt x+2*(Real.log x/Real.sqrt x))^2) atTop (𝓝 0) := by
    simpa using (h1.add (h2.const_mul 2)).pow 2
  refine hc.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  calc
    _ = ((1+2*Real.log x)/Real.sqrt x)^2 := by ring
    _ = _ := by rw [div_pow,Real.sq_sqrt hx]

set_option maxHeartbeats 4000000 in
theorem prime_band_negligible (ε : ℝ) (hε : 0<ε) : ∃ N:ℕ, ∀ n ≥ N,
    |nearBulk (catalogueCutoff n) n (primeBandWidth n) (high n)| ≤ ε*n := by
  have hl : Tendsto (fun n : ℕ => (logWidth n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp logWidth_tends
  have lim := (log_bound_ratio.comp hl).const_mul (4*Real.log 4)
  rw [mul_zero] at lim
  obtain ⟨N,hN⟩ := eventually_atTop.mp (lim.eventually_lt_const hε)
  refine ⟨max 1 N,fun n hn => (prime_band_uniform n (by omega)).trans ?_⟩
  have h := mul_le_mul_of_nonneg_right (hN n (by omega)).le (show 0≤(n:ℝ) by positivity)
  dsimp only [Function.comp_apply] at h
  convert h using 1; ring

set_option maxHeartbeats 4000000 in
theorem catalogue_prime_band_iff : FrozenBulk.BulkFloor ↔
    ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      -(ε*(n:ℝ)) ≤ trimmedBulk (catalogueCutoff n) n (primeBandWidth n) (high n) :=
  catalogue_trimmed_iff_of_negligible primeBandWidth prime_band_negligible

end GoldbachMinor

namespace GoldbachMinor

open Finset GoldbachWeight

set_option maxHeartbeats 4000000 in
noncomputable def pairMass (n k : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ range (n+1), ∑ r ∈ range (n+1),
    if (offset n p r).natAbs = k then w p * w r else 0

set_option maxHeartbeats 4000000 in
noncomputable def tailWave (Q n k : ℕ) (w : ℕ → ℝ) : ℝ :=
  pairMass n k w * ∑ q ∈ Icc 1 Q, ram q k *
    Real.sin (2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n)))

set_option maxHeartbeats 4000000 in
private theorem wave_quotient (Q n k : ℕ) (w : ℕ → ℝ) :
    (Real.pi * k)⁻¹ * tailWave Q n k w = pairMass n k w * majorCoefficient Q n k := by
  unfold tailWave majorCoefficient
  simp_rw [div_eq_mul_inv, ← mul_assoc]
  rw [← sum_mul]
  ring

set_option maxHeartbeats 4000000 in
private theorem group_modes (n : ℕ) (w f : ℕ → ℝ) :
    ∑ k ∈ range (n+1), pairMass n k w * f k =
    ∑ p ∈ range (n+1), ∑ r ∈ range (n+1), w p * w r * f (offset n p r).natAbs := by
  unfold pairMass
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  have hb : (offset n p r).natAbs ∈ range (n+1) := by
    simp only [mem_range] at *
    unfold offset
    omega
  simp_rw [ite_mul, zero_mul]
  simp [hb]

set_option maxHeartbeats 4000000 in
theorem trimmed_frequency_sum (Q n K : ℕ) (w : ℕ → ℝ) :
    trimmedBulk Q n K w =
      pairMass n 0 w * (1 - arcLength Q n) -
        ∑ k ∈ Ioc K n, (Real.pi*k)⁻¹ * tailWave Q n k w := by
  let f (k : ℕ) := if k = 0 ∨ K < k then minorCoefficient Q n k else 0
  have hg := group_modes n w f
  have ht : trimmedBulk Q n K w = ∑ k ∈ range (n+1), pairMass n k w * f k := by
    rw [hg]
    unfold trimmedBulk
    simp only [f, mul_ite, mul_zero, Int.natAbs_eq_zero]
  rw [ht]
  have split (k : ℕ) : pairMass n k w * f k =
      (if k = 0 then pairMass n 0 w * (1-arcLength Q n) else 0) -
      (if K < k then (Real.pi*k)⁻¹ * tailWave Q n k w else 0) := by
    rw [wave_quotient]
    by_cases hz : k = 0
    · subst k; simp [f,minorCoefficient]
    · by_cases hk : K < k <;> simp [f,minorCoefficient,hz,hk]
  simp_rw [split, sum_sub_distrib]
  simp only [sum_ite_eq', mem_range, Nat.zero_lt_succ, ite_true]
  rw [← sum_filter]
  congr 2
  ext k
  simp [and_comm]

set_option maxHeartbeats 4000000 in
noncomputable def tailPrefix (Q n K t : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Ioc K t, tailWave Q n k w

set_option maxHeartbeats 4000000 in
private theorem harmonic_prefix_identity (a : ℕ → ℝ) (K n : ℕ) :
    let S := fun t => ∑ k ∈ Ioc K t, a k
    (∑ k ∈ Ioc K n, (k:ℝ)⁻¹ * a k) =
      (n:ℝ)⁻¹ * S n + ∑ k ∈ Ioo K n, ((k:ℝ)⁻¹ - ((k+1:ℕ):ℝ)⁻¹) * S k := by
  dsimp only
  by_cases hn : K < n
  · induction n, hn using Nat.le_induction with
    | base =>
      simp [show Ioc K (K+1) = {K+1} by ext; simp,
        show Ioo K (K+1) = ∅ by ext; simp]
    | succ t ht ih =>
      have hc : Ioc K (t+1) = insert (t+1) (Ioc K t) := by ext; simp; omega
      have ho : Ioo K (t+1) = insert t (Ioo K t) := by ext; simp; omega
      rw [hc,ho]
      simp only [mem_Ioc,mem_Ioo,not_lt_of_ge le_rfl,Nat.not_succ_le_self,
        and_false,not_false_eq_true,sum_insert]
      rw [ih]
      ring
  · have hc := Ioc_eq_empty_of_le (Nat.le_of_not_gt hn)
    have ho : Ioo K n = ∅ := by ext; simp; omega
    simp [hc,ho]

set_option maxHeartbeats 4000000 in
noncomputable def prefixLoss (Q n K : ℕ) (w : ℕ → ℝ) : ℝ :=
  Real.pi⁻¹ * ((n:ℝ)⁻¹ * tailPrefix Q n K n w +
    ∑ k ∈ Ioo K n, ((k:ℝ)⁻¹ - ((k+1:ℕ):ℝ)⁻¹) * tailPrefix Q n K k w)

set_option maxHeartbeats 4000000 in
theorem trimmed_prefix_identity (Q n K : ℕ) (w : ℕ → ℝ) :
    trimmedBulk Q n K w = pairMass n 0 w * (1-arcLength Q n) - prefixLoss Q n K w := by
  rw [trimmed_frequency_sum]
  unfold prefixLoss tailPrefix
  rw [← harmonic_prefix_identity, mul_sum]
  simp only [mul_inv, mul_assoc]

set_option maxHeartbeats 4000000 in
theorem catalogue_prefix_loss_iff : FrozenBulk.BulkFloor ↔
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Even n →
      let Q := catalogueCutoff n
      prefixLoss Q n (primeBandWidth n) (high n) ≤
        pairMass n 0 (high n) * (1-arcLength Q n) + ε*n := by
  rw [catalogue_prime_band_iff]
  simp_rw [trimmed_prefix_identity]
  constructor <;> intro h ε he <;> obtain ⟨N,hN⟩ := h ε he <;>
    refine ⟨N,fun n hn hev => ?_⟩ <;> have h' := hN n hn hev <;>
    linarith only [h']

set_option maxHeartbeats 4000000 in
private theorem harmonic_prefix_bound (a : ℕ → ℝ) (K m : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (h : ∀ t ∈ Ioc K m, (∑ k ∈ Ioc K t, a k) ≤ B) :
    (∑ k ∈ Ioc K m, (k:ℝ)⁻¹ * a k) ≤ ((K:ℝ)+1)⁻¹ * B := by
  let S (t : ℕ) := ∑ k ∈ Ioc K t, a k
  have step : ∀ t, K < t → (∀ j ∈ Ioc K t, S j ≤ B) →
      (∑ k ∈ Ioc K t, (k:ℝ)⁻¹ * a k) ≤
      ((K:ℝ)+1)⁻¹ * B + (t:ℝ)⁻¹ * (S t - B) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      intro _
      simp [S, show Ioc K (K+1) = {K+1} by ext; simp]
      ring_nf
      exact le_rfl
    | succ t ht ih =>
      intro hst
      have hp := ih (fun j hj => hst j (mem_Ioc.mpr ⟨(mem_Ioc.mp hj).1,(mem_Ioc.mp hj).2.trans (Nat.le_succ _)⟩))
      have hs := hst t (mem_Ioc.mpr ⟨ht, Nat.le_succ _⟩)
      have hd : ((t+1:ℕ):ℝ)⁻¹ ≤ (t:ℝ)⁻¹ := by
        apply inv_anti₀ <;> exact_mod_cast (by omega : _)
      have hx := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hd) (sub_nonpos.mpr hs)
      have hrec : Ioc K (t+1) = insert (t+1) (Ioc K t) := by ext; simp; omega
      have hnot : t+1 ∉ Ioc K t := by simp
      have heq : S (t+1) = a (t+1) + S t := by simp [S,hrec,hnot]
      rw [hrec,sum_insert hnot,heq]
      nlinarith only [hx,hp]
  by_cases ht : K < m
  · have hx := step m ht h
    have hs := h m (mem_Ioc.mpr ⟨ht,le_rfl⟩)
    have hneg : (m:ℝ)⁻¹ * (S m - B) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hs)
    exact hx.trans (by linarith)
  · simp only [Ioc_eq_empty_of_le (Nat.le_of_not_gt ht), sum_empty]
    positivity

set_option maxHeartbeats 4000000 in
theorem trimmed_of_prefix (Q n K : ℕ) (w : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ t ∈ Ioc K n, tailPrefix Q n K t w ≤ B) :
    pairMass n 0 w * (1-arcLength Q n) - B / (Real.pi*((K:ℝ)+1)) ≤
      trimmedBulk Q n K w := by
  rw [trimmed_frequency_sum]
  have hh := harmonic_prefix_bound (fun k => tailWave Q n k w) K n B hB h
  have key := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr Real.pi_pos.le)
  rw [mul_sum] at key
  simp_rw [← mul_assoc, ← mul_inv] at key
  convert sub_le_sub_left key (pairMass n 0 w * (1-arcLength Q n)) using 1
  simp only [div_eq_mul_inv]
  ring

set_option maxHeartbeats 4000000 in
theorem catalogue_bulk_of_prefix_budget
    (bound : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Even n →
      let K := primeBandWidth n
      let Q := catalogueCutoff n
      ∀ t ∈ Icc K n, tailPrefix Q n K t (high n) ≤
        Real.pi * ((K:ℝ)+1) * (pairMass n 0 (high n) * (1-arcLength Q n) + ε*n)) :
    FrozenBulk.BulkFloor := by
  apply catalogue_prime_band_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := bound ε hε
  refine ⟨N,fun n hn heven => ?_⟩
  let K := primeBandWidth n
  let Q := catalogueCutoff n
  let D := pairMass n 0 (high n) * (1-arcLength Q n)
  let B := Real.pi * ((K:ℝ)+1) * (D+ε*n)
  have hK : K ≤ n := Nat.div_le_self _ _
  have hp : ∀ t ∈ Icc K n, tailPrefix Q n K t (high n) ≤ B := hN n hn heven
  have hz := hp K (mem_Icc.mpr ⟨le_rfl,hK⟩)
  have hB : 0 ≤ B := by simpa [tailPrefix] using hz
  have htail := trimmed_of_prefix Q n K (high n) B hB (fun t ht =>
    hp t (mem_Icc.mpr ⟨(mem_Ioc.mp ht).1.le,(mem_Ioc.mp ht).2⟩))
  have cancel : B / (Real.pi*((K:ℝ)+1)) = D+ε*n := by
    dsimp only [B]
    field_simp [Real.pi_ne_zero,show (K:ℝ)+1 ≠ 0 by positivity]
  rw [cancel] at htail
  change -(ε*(n:ℝ)) ≤ trimmedBulk Q n K (high n)
  change D - (D + ε*n) ≤ _ at htail
  linarith only [htail]

end GoldbachMinor

end Conjectures.Goldbach.BulkPrefixEquivalence_aux

open Conjectures.Goldbach.BulkPrefixEquivalence_aux

set_option maxHeartbeats 4000000 in
theorem Conjectures.Goldbach.BulkPrefixEquivalence :
(let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e:ℝ,0<e → ∃ N:ℕ,∀ n≥N, Even n → -(e*(n:ℝ))≤(I n (high n) (high n)).re) ↔ (
  let Q (n : ℕ) := (Nat.log 2 (n+2))^2
  let K (n : ℕ) := n / (Nat.log 2 (n+2) + 1)^4
  let high (n p : ℕ) : ℝ := if p^3 ≤ n then 0 else if p.Prime then Real.log p else 0
  let mass (n k : ℕ) : ℝ := ∑ p ∈ Finset.range (n+1), ∑ r ∈ Finset.range (n+1),
    if ((p:ℤ) + r - n).natAbs = k then high n p * high n r else 0
  let ram (q k : ℕ) : ℝ := ∑ d ∈ q.divisors,
    (if d ∣ k then (d:ℝ) else 0) * (ArithmeticFunction.moebius (q/d):ℝ)
  let length (n : ℕ) : ℝ := ∑ q ∈ Finset.Icc 1 (Q n),
    q.totient * (2*(Q n:ℝ) / ((q:ℝ)*n))
  let prefixSum (n t : ℕ) : ℝ := ∑ k ∈ Finset.Ioc (K n) t,
    mass n k * ∑ q ∈ Finset.Icc 1 (Q n),
      ram q k * Real.sin (2*Real.pi*(k:ℝ)*((Q n:ℝ)/((q:ℝ)*n)))
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Even n →
    Real.pi⁻¹ * ((n:ℝ)⁻¹ * prefixSum n n + ∑ k ∈ Finset.Ioo (K n) n,
      ((k:ℝ)⁻¹ - ((k+1:ℕ):ℝ)⁻¹) * prefixSum n k) ≤
    mass n 0 * (1-length n) + ε*n) := by
  constructor
  · intro h
    have hB : FrozenBulk.BulkFloor := by
      intro e he
      obtain ⟨N, hN⟩ := h e he
      refine ⟨N, fun n hn hev => ?_⟩
      have hx := hN n hn hev
      simpa only [FrozenBulk.deskI, FrozenBulk.deskArcs, FrozenBulk.deskS, FrozenBulk.deskE,
        FrozenBulk.deskHigh, FrozenBulk.deskLow, FrozenBulk.deskW] using hx
    exact GoldbachMinor.catalogue_prefix_loss_iff.mp hB
  · intro h
    have hR : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Even n →
        GoldbachMinor.prefixLoss (GoldbachMinor.catalogueCutoff n) n
          (GoldbachMinor.primeBandWidth n) (GoldbachWeight.high n) ≤
        GoldbachMinor.pairMass n 0 (GoldbachWeight.high n) *
          (1 - GoldbachMinor.arcLength (GoldbachMinor.catalogueCutoff n) n) + ε * n := by
      intro ε hε
      obtain ⟨N, hN⟩ := h ε hε
      refine ⟨N, fun n hn hev => ?_⟩
      have hx := hN n hn hev
      convert hx using 1 <;>
        simp only [GoldbachMinor.prefixLoss, GoldbachMinor.tailPrefix, GoldbachMinor.tailWave,
          GoldbachMinor.pairMass, GoldbachMinor.ram, GoldbachMinor.arcLength,
          GoldbachMinor.catalogueCutoff, GoldbachMinor.primeBandWidth, GoldbachMinor.logWidth,
          GoldbachMinor.offset, GoldbachWeight.high] <;> rfl
    exact GoldbachMinor.catalogue_prefix_loss_iff.mpr hR
