import Mathlib

/- Standalone adaptation of the proof by ChiyodaMomo01, proposal 1923,
research/reference-proofs/prime-band at b0820ebb68754bebd52ee5512cbdf2ebd85677dd.
The analytic estimate is DFQDZZ's contribution 316, e4ab24712555ae8c2c926adf19d368a9fb392c35;
it incorporates OpenAI openai/math revision f5702854040e97fa7675c21ba37a9608f5f92dd3
and the finite Ramanujan calculations of XianWu18 and wzhxzkk in contributions 207 and 203.
Separation uses wzhxzkk, 93d33090fdfc93fb272dde08cb463f3bff3c64ce.
Cutoff separation also uses pwzlyx, 4a29eb4239368944efb5c486fe59e10d85629cbd.
All sources are Apache-2.0. The contributor adaptations inline local source modules,
retain the exact arc geometry, and omit unused endpoint conclusions. -/


section

theorem frontierSpatialDisjoint :
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

end

section

open Filter

/-- The logarithmic cutoff eventually satisfies the separation inequality
for major arcs. -/
theorem frontierSpatialCutoff :
    let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2
    let arcs := fun n : ℕ =>
      {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))}
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 2 * (Q n) ^ 2 < n := by
  intro Q arcs
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

end
section

namespace GoldbachMinor
open Finset Set MeasureTheory
def catalogueArcs (Q n : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / q| ≤ (Q : ℝ) / ((q : ℝ) * n)}
def catalogueCutoff (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2
private noncomputable def BandGeometryRadius (Q n q : ℕ) : ℝ := (Q : ℝ) / ((q : ℝ) * n)
private noncomputable def BandGeometryCell (Q n q a : ℕ) : Set ℝ :=
  Icc ((a:ℝ)/q - BandGeometryRadius Q n q) ((a:ℝ)/q + BandGeometryRadius Q n q)
private theorem BandGeometryIn_cell {Q n q a : ℕ} {t : ℝ} :
    t ∈ BandGeometryCell Q n q a ↔ |t - (a:ℝ)/q| ≤ BandGeometryRadius Q n q := by
  rw [abs_le]
  change (_ ≤ t ∧ t ≤ _) ↔ _
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
private theorem BandGeometrySame_center {a b q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (ha : a.Coprime q) (hb : b.Coprime r) (he : a*r=b*q) : q=r ∧ a=b := by
  have h₁ : q ∣ a*r := he ▸ Nat.dvd_mul_left q b
  have h₂ : r ∣ b*q := he.symm ▸ Nat.dvd_mul_left r a
  have eq := Nat.dvd_antisymm (ha.symm.dvd_of_dvd_mul_left h₁) (hb.symm.dvd_of_dvd_mul_left h₂)
  subst r
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩
private theorem BandGeometryUnique_cell {a b q r Q n : ℕ} {t : ℝ}
    (hq : q ∈ Finset.Icc 1 Q) (hr : r ∈ Finset.Icc 1 Q)
    (ha : a.Coprime q) (hb : b.Coprime r) (hscale : 2*Q^2<n)
    (ht₁ : t ∈ BandGeometryCell Q n q a) (ht₂ : t ∈ BandGeometryCell Q n r b) : q=r ∧ a=b := by
  obtain ⟨hq₁,hq₂⟩ := Finset.mem_Icc.mp hq
  obtain ⟨hr₁,hr₂⟩ := Finset.mem_Icc.mp hr
  apply BandGeometrySame_center hq₁ hr₁ ha hb
  by_contra h
  have hsep := frontierSpatialDisjoint a b q r Q n t hq₁ hr₁ hq₂ hr₂ hscale h
    (BandGeometryIn_cell.mp ht₁)
  exact (not_lt_of_ge (BandGeometryIn_cell.mp ht₂)) hsep
private def BandGeometryNumerators (q : ℕ) : Finset ℕ := ((range (q+1)).filter (·.Coprime q))
private theorem BandGeometrySplit_indicator (f : ℝ → ℂ) (Q n : ℕ) (hscale : 2*Q^2<n) (t : ℝ) :
    (catalogueArcs Q n).indicator f t = ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ BandGeometryNumerators q,
      (BandGeometryCell Q n q a).indicator f t := by
  classical
  by_cases ht : t ∈ catalogueArcs Q n
  · obtain ⟨q,a,hq,hqQ,ha,hca,hm⟩ := ht
    have hqr : q ∈ Finset.Icc 1 Q := Finset.mem_Icc.mpr ⟨hq,hqQ⟩
    have har : a ∈ BandGeometryNumerators q := mem_filter.mpr ⟨mem_range.mpr (by omega),hca⟩
    have he : t ∈ BandGeometryCell Q n q a := BandGeometryIn_cell.mpr hm
    rw [Set.indicator_of_mem (show t ∈ catalogueArcs Q n from ⟨q,a,hq,hqQ,ha,hca,hm⟩)]
    rw [sum_eq_single_of_mem q hqr]
    · rw [sum_eq_single_of_mem a har, Set.indicator_of_mem he]
      intro b hb hba
      apply Set.indicator_of_notMem
      exact fun h => hba (BandGeometryUnique_cell hqr hqr (mem_filter.mp hb).2 hca hscale h he).2
    · intro r hr hrq
      apply sum_eq_zero
      intro b hb
      apply Set.indicator_of_notMem
      exact fun h => hrq (BandGeometryUnique_cell hr hqr (mem_filter.mp hb).2 hca hscale h he).1
  · rw [Set.indicator_of_notMem ht]
    symm
    apply sum_eq_zero
    intro q hq
    apply sum_eq_zero
    intro a ha
    apply Set.indicator_of_notMem
    intro h
    exact ht ⟨q,a,(Finset.mem_Icc.mp hq).1,(Finset.mem_Icc.mp hq).2,
      by have := mem_range.mp (mem_filter.mp ha).1; omega,(mem_filter.mp ha).2,BandGeometryIn_cell.mp h⟩
private noncomputable def BandGeometryClipped (x R : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ t in (Icc 0 1 ∩ Icc (x-R) (x+R)), f t
private theorem BandGeometryMajor_clipped (Q n : ℕ) (hscale : 2*Q^2<n)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n).indicator f t) =
    ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ BandGeometryNumerators q, BandGeometryClipped ((a:ℝ)/q) (BandGeometryRadius Q n q) f := by
  have hi (q a : ℕ) : IntegrableOn ((BandGeometryCell Q n q a).indicator f) (Icc (0:ℝ) 1) :=
    hf.integrableOn_Icc.indicator measurableSet_Icc
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  simp_rw [BandGeometrySplit_indicator f Q n hscale]
  rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ (fun a _ => hi q a))]
  apply sum_congr rfl
  intro q _
  rw [integral_finsetSum _ (fun a _ => hi q a)]
  apply sum_congr rfl
  intro a _
  exact setIntegral_indicator measurableSet_Icc
private theorem BandGeometryIntegral_closed {l u : ℝ} (h : l ≤ u) (f : ℝ → ℂ) :
    (∫ t in Icc l u, f t) = ∫ t in l..u, f t := by
  rw [intervalIntegral.integral_of_le h, integral_Icc_eq_integral_Ioc]
private theorem BandGeometryInterior (f : ℝ → ℂ) {x R : ℝ} (hR : 0 ≤ R) (hl : 0 ≤ x-R)
    (hu : x+R ≤ 1) : BandGeometryClipped x R f = ∫ t in (x-R)..(x+R), f t := by
  unfold BandGeometryClipped
  rw [Set.inter_eq_right.mpr (Icc_subset_Icc hl hu), BandGeometryIntegral_closed (by linarith)]
private theorem BandGeometryBoundary (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1)
    {R : ℝ} (hR : 0 ≤ R) (hR₁ : R ≤ 1) :
    BandGeometryClipped 0 R f + BandGeometryClipped 1 R f = ∫ t in -R..R, f t := by
  have hl : (Icc (0:ℝ) 1 ∩ Icc (0-R) (0+R)) = Icc 0 R := by
    ext t; simp only [mem_inter_iff, Set.mem_Icc]; constructor <;> intro h <;> grind
  have hr : (Icc (0:ℝ) 1 ∩ Icc (1-R) (1+R)) = Icc (1-R) 1 := by
    ext t; simp only [mem_inter_iff, Set.mem_Icc]; constructor <;> intro h <;> grind
  have trans := intervalIntegral.integral_comp_add_right (a := -R) (b := 0) f 1
  simp only [hp _,zero_add] at trans
  rw [show -R+1 = 1-R by ring] at trans
  unfold BandGeometryClipped
  rw [hl,hr,BandGeometryIntegral_closed hR,BandGeometryIntegral_closed (by linarith),← trans,add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)
private theorem BandGeometryNormalize (q : ℕ) (hq : 0 < q) (f : ℝ → ℂ) (hf : Continuous f)
    (hp : Function.Periodic f 1) {R : ℝ} (hR : 0 ≤ R) (hsmall : R ≤ 1/(q:ℝ)) :
    (∑ a ∈ BandGeometryNumerators q, BandGeometryClipped ((a:ℝ)/q) R f) =
      ∑ a ∈ (range q).filter (·.Coprime q),
        ∫ t in ((a:ℝ)/q-R)..((a:ℝ)/q+R), f t := by
  by_cases h : q=1
  · subst q
    simpa [BandGeometryNumerators, sum_filter, sum_range_succ] using BandGeometryBoundary f hf hp hR (by simpa using hsmall)
  have hqc : ¬ q.Coprime q := by simpa using h
  unfold BandGeometryNumerators
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
  apply BandGeometryInterior f hR
  · have := div_le_div_of_nonneg_right ha' hq'.le
    linarith
  · have hbound : (a:ℝ)/q + 1/q ≤ 1 := by
      rw [← add_div, div_le_one hq']; exact hsucc
    linarith
theorem catalogue_major_periodic (Q n : ℕ) (hscale : 2*Q^2<n)
    (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n).indicator f t) =
      ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (range q).filter (·.Coprime q),
        ∫ t in ((a:ℝ)/q-(Q:ℝ)/(q*n))..((a:ℝ)/q+(Q:ℝ)/(q*n)), f t := by
  rw [BandGeometryMajor_clipped Q n hscale f hf]
  apply sum_congr rfl
  intro q hq
  have pos := (Finset.mem_Icc.mp hq).1
  have hq' : (0:ℝ) < q := by exact_mod_cast pos
  have hn : Q ≤ n := by nlinarith [Nat.le_self_pow (by decide : 2≠0) Q]
  have hn' : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  apply BandGeometryNormalize q pos f hf hp (by unfold BandGeometryRadius; positivity)
  unfold BandGeometryRadius
  rw [div_le_div_iff₀ (mul_pos hq' hn') hq']
  have h : (Q:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [mul_le_mul_of_nonneg_left h hq'.le]
end GoldbachMinor

end

section

namespace GoldbachRamanujan
open Finset Polynomial
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius
private noncomputable def BandArithmeticPrimitiveTrace (k : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun q => ∑ z ∈ primitiveRoots q ℂ, z ^ k, by simp [primitiveRoots_zero]⟩
private def BandArithmeticDivisibleTrace (k : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun q => if q ∣ k then (q : ℂ) else 0, by simp⟩
private theorem BandArithmeticAll_roots_trace {q : ℕ} (hq : 0 < q) (k : ℕ) :
    (∑ z ∈ nthRootsFinset q (1 : ℂ), z ^ k) = BandArithmeticDivisibleTrace k q := by
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
private theorem BandArithmeticInvert_trace (k : ℕ) :
    BandArithmeticPrimitiveTrace k = BandArithmeticDivisibleTrace k * (μ : ArithmeticFunction ℂ) := by
  classical
  have conv : BandArithmeticPrimitiveTrace k * (ζ : ArithmeticFunction ℂ) = BandArithmeticDivisibleTrace k := by
    ext q
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    change (∑ d ∈ q.divisors, ∑ z ∈ primitiveRoots d ℂ, z ^ k) = _
    rw [← sum_biUnion (fun _ _ _ _ hd => IsPrimitiveRoot.disjoint (R := ℂ) hd),
      ← IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
    rcases q with _ | q
    · simp
    · exact BandArithmeticAll_roots_trace (Nat.succ_pos _) k
  calc
    _ = BandArithmeticPrimitiveTrace k * ((ζ : ArithmeticFunction ℂ) * (μ : ArithmeticFunction ℂ)) := by simp
    _ = (BandArithmeticPrimitiveTrace k * (ζ : ArithmeticFunction ℂ)) * (μ : ArithmeticFunction ℂ) :=
      (mul_assoc ..).symm
    _ = _ := by rw [conv]
theorem primitive_power_sum (q k : ℕ) :
    (∑ z ∈ primitiveRoots q ℂ, z^k) = ∑ d ∈ q.divisors,
      (if d ∣ k then (d:ℂ) else 0) * (ArithmeticFunction.moebius (q/d):ℂ) := by
  change BandArithmeticPrimitiveTrace k q = _
  rw [BandArithmeticInvert_trace, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => BandArithmeticDivisibleTrace k x * (μ : ArithmeticFunction ℂ) y)]
  rfl
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
    _ = _ := primitive_power_sum q k
end GoldbachRamanujan
namespace GoldbachRamanujan
private noncomputable def BandArithmeticWave (ω t : ℝ) : ℂ := Complex.exp (((ω*t : ℝ) : ℂ)*Complex.I)
private theorem BandArithmeticWave_add (ω x y : ℝ) : BandArithmeticWave ω (x+y) = BandArithmeticWave ω x * BandArithmeticWave ω y := by
  unfold BandArithmeticWave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
private theorem BandArithmeticInterval_wave (ω x R : ℝ) (hω : ω ≠ 0) :
    (∫ t in (x-R)..(x+R), BandArithmeticWave ω t) = BandArithmeticWave ω x * ((2*Real.sin (ω*R)/ω : ℝ) : ℂ) := by
  have translate := intervalIntegral.integral_comp_add_left (a := -R) (b := R) (BandArithmeticWave ω) x
  rw [← sub_eq_add_neg] at translate
  rw [← translate]
  simp_rw [BandArithmeticWave_add]
  rw [intervalIntegral.integral_const_mul]
  apply congrArg (fun z : ℂ => BandArithmeticWave ω x * z)
  change (∫ t in -R..R, (fun y : ℝ => Complex.exp ((y : ℂ)*Complex.I)) (ω*t)) = _
  rw [intervalIntegral.integral_comp_mul_left (a := -R) (b := R)
    (fun y : ℝ => Complex.exp ((y : ℂ)*Complex.I)) hω, mul_neg, integral_exp_mul_I_eq_sin]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_ofNat, div_eq_mul_inv]
  ring
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
    ∫ t in ((a:ℝ)/q-R)..((a:ℝ)/q+R), BandArithmeticWave ω t) = _
  simp_rw [BandArithmeticInterval_wave _ _ _ hω, factor]
  rw [← Finset.sum_mul, ← all_frequencies hq k]
  apply congrArg (fun z : ℂ => z * ((Real.sin (2*Real.pi*(k:ℝ)*R)/(Real.pi*k):ℝ):ℂ))
  apply Finset.sum_congr rfl
  intro a _
  unfold BandArithmeticWave ω
  rw [← mul_div_assoc]
end GoldbachRamanujan
namespace GoldbachMinor
open Finset
noncomputable def ram (q k : ℕ) : ℝ :=
  ∑ d ∈ q.divisors, (if d ∣ k then (d:ℝ) else 0) * (ArithmeticFunction.moebius (q/d):ℝ)
noncomputable def arcLength (Q n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, q.totient * (2*(Q:ℝ)/(q*n))
noncomputable def majorCoefficient (Q n k : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ram q k *
    (Real.sin (2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n))) / (Real.pi*k))
noncomputable def minorCoefficient (Q n k : ℕ) : ℝ :=
  if k=0 then 1 - arcLength Q n else -majorCoefficient Q n k
end GoldbachMinor
namespace GoldbachMinor
open Finset
end GoldbachMinor

end

section

namespace GoldbachMinor
open Finset Set MeasureTheory
open scoped ComplexConjugate
noncomputable def mode (k : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (((2*Real.pi*(k:ℝ)*t : ℝ):ℂ)*Complex.I)
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
theorem mode_continuous (k : ℤ) : Continuous (mode k) := by unfold mode; fun_prop
private theorem BandMaskMode_periodic (k : ℤ) : Function.Periodic (mode k) 1 := by
  intro t
  unfold mode
  calc
    _ = Complex.exp (((2*Real.pi*(k:ℝ)*t : ℝ):ℂ)*Complex.I) *
        Complex.exp ((k:ℂ)*(2*Real.pi*Complex.I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    _ = _ := by rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]
private theorem BandMaskMode_neg (k : ℤ) (t : ℝ) : mode (-k) t = conj (mode k t) := by
  unfold mode
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring
private theorem BandMaskFull_mode (k : ℕ) (hk : 0 < k) : (∫ t in (0:ℝ)..1, mode (k:ℤ) t) = 0 := by
  let c : ℂ := (k:ℂ)*(2*Real.pi*Complex.I)
  have hc : c ≠ 0 := by
    dsimp [c]; exact mul_ne_zero (by exact_mod_cast hk.ne') (mul_ne_zero (by exact_mod_cast (mul_ne_zero (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero)) Complex.I_ne_zero)
  have he (t : ℝ) : mode (k:ℤ) t = Complex.exp (c*t) := by
    unfold mode c; congr 1; push_cast; ring
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [c, Complex.exp_nat_mul_two_pi_mul_I]
theorem BandMaskRam_cast (q k : ℕ) : (ram q k : ℂ) = ∑ d ∈ q.divisors,
    (if d ∣ k then (d:ℂ) else 0) * (ArithmeticFunction.moebius (q/d):ℂ) := by
  unfold ram
  push_cast
  apply sum_congr rfl
  intro d _
  split_ifs <;> simp
private theorem BandMaskMajor_pos_mode (Q n k : ℕ) (hscale : 2*Q^2<n) (hk : 0<k) :
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n).indicator (mode (k:ℤ)) t) =
      (majorCoefficient Q n k:ℂ) := by
  rw [catalogue_major_periodic _ _ hscale _ (mode_continuous _) (BandMaskMode_periodic _)]
  unfold majorCoefficient
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro q hq
  rw [Complex.ofReal_mul, BandMaskRam_cast]
  simpa only [mode, Int.cast_natCast] using GoldbachRamanujan.arcs_at_denominator
    (Finset.mem_Icc.mp hq).1 hk ((Q:ℝ)/(q*n))
private theorem BandMaskMajor_zero (Q n : ℕ) (hscale : 2*Q^2<n) :
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n).indicator (mode 0) t) = (arcLength Q n:ℂ) := by
  rw [catalogue_major_periodic _ _ hscale _ (mode_continuous _) (BandMaskMode_periodic _)]
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
theorem minor_mode (Q n : ℕ) (hscale : 2*Q^2<n) (k : ℤ) :
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n)ᶜ.indicator (mode k) t) =
      (minorCoefficient Q n k.natAbs:ℂ) := by
  have nat_mode (j : ℕ) : (∫ t in (0:ℝ)..1, (catalogueArcs Q n)ᶜ.indicator (mode (j:ℤ)) t) =
      (minorCoefficient Q n j:ℂ) := by
    rw [integral_complement _ (measurable_catalogue ..) _ (mode_continuous _)]
    rcases j with _ | j
    · rw [Nat.cast_zero,BandMaskMajor_zero Q n hscale]
      simp [mode, minorCoefficient, intervalIntegral.integral_const]
    · rw [BandMaskFull_mode _ (Nat.succ_pos _), BandMaskMajor_pos_mode _ _ _ hscale (Nat.succ_pos _)]
      simp [minorCoefficient]
  cases k with
  | ofNat j => exact nat_mode j
  | negSucc j =>
    change (∫ t in (0:ℝ)..1, (catalogueArcs Q n)ᶜ.indicator (mode (-((j+1:ℕ):ℤ))) t) = _
    have hm (t : ℝ) : (catalogueArcs Q n)ᶜ.indicator (mode (-((j+1:ℕ):ℤ))) t =
        conj ((catalogueArcs Q n)ᶜ.indicator (mode ((j+1:ℕ):ℤ)) t) := by
      by_cases h : t ∈ (catalogueArcs Q n)ᶜ
      · simp only [Set.indicator_of_mem h]; exact BandMaskMode_neg _ t
      · simp only [Set.indicator_of_notMem h, map_zero]
    simp_rw [hm]
    rw [intervalIntegral.intervalIntegral_conj, nat_mode, Complex.conj_ofReal]
    rfl
end GoldbachMinor

end

section

namespace GoldbachWeight
open Finset
noncomputable def high (n k : ℕ) : ℝ :=
  if k ^ 3 ≤ n then 0 else if k.Prime then Real.log k else 0
noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
noncomputable def spectrum (n : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n+1), (w k : ℂ) * phase ((k : ℝ)*t)
end GoldbachWeight
namespace GoldbachMinor
open Finset Set MeasureTheory GoldbachWeight
def offset (n p r : ℕ) : ℤ := (p:ℤ)+r-n
noncomputable def arithmeticBulk (Q n : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ range (n+1), ∑ r ∈ range (n+1),
    w p * w r * minorCoefficient Q n (offset n p r).natAbs
private theorem BandPairsExpand_spectrum (n : ℕ) (w : ℕ → ℝ) (t : ℝ) :
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
private theorem BandPairsIntegrate_sum {ι : Type*} (s : Finset ι) (A : Set ℝ) (hA : MeasurableSet A)
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
theorem integral_eq_arithmeticBulk (Q n : ℕ) (hn : 2*Q^2<n) (w : ℕ → ℝ) :
    (∫ t in (0:ℝ)..1, (catalogueArcs Q n)ᶜ.indicator (fun u =>
      GoldbachWeight.spectrum n w u * GoldbachWeight.spectrum n w u * phase (-(n:ℝ)*u)) t)
      = (arithmeticBulk Q n w:ℂ) := by
  have hA := (measurable_catalogue Q n).compl
  have hc (p r : ℕ) : Continuous (fun t => (↑(w p*w r):ℂ)*mode (offset n p r) t) :=
    continuous_const.mul (mode_continuous _)
  simp_rw [BandPairsExpand_spectrum]
  rw [BandPairsIntegrate_sum _ _ hA _ (fun p _ => continuous_finsetSum _ (fun r _ => hc p r))]
  unfold arithmeticBulk
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro p _
  rw [BandPairsIntegrate_sum _ _ hA _ (fun r _ => hc p r), Complex.ofReal_sum]
  apply sum_congr rfl
  intro r _
  simp_rw [Set.indicator_const_mul,intervalIntegral.integral_const_mul,minor_mode Q n hn]
  push_cast
  rfl
end GoldbachMinor
namespace GoldbachMinor
open Finset GoldbachWeight
end GoldbachMinor
namespace GoldbachMinor
open Finset GoldbachWeight
end GoldbachMinor

end
open Finset MeasureTheory GoldbachMinor

private noncomputable def spatialKernel (Q n q : ℕ) (m : ℤ) : ℝ :=
  (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), Real.cos (2*Real.pi*(m:ℝ)*(a:ℝ)/(q:ℝ))) *
  (Real.sin (2*Real.pi*(m:ℝ)*((Q:ℝ)/((q:ℝ)*(n:ℝ)))) / (Real.pi*(m:ℝ)))

private theorem spatial_even (Q n q : ℕ) (m : ℤ) :
    spatialKernel Q n q (-m) = spatialKernel Q n q m := by
  simp [spatialKernel, mul_neg, neg_mul, neg_div, div_neg]

private theorem spatial_terms (Q n q : ℕ) (hq : 0 < q) (m : ℤ) :
    spatialKernel Q n q m = ram q m.natAbs *
      (Real.sin (2*Real.pi*(m.natAbs:ℝ)*((Q:ℝ)/(q*n))) / (Real.pi*m.natAbs)) := by
  have natCase (k : ℕ) : spatialKernel Q n q (k:ℤ) = ram q k *
      (Real.sin (2*Real.pi*(k:ℝ)*((Q:ℝ)/(q*n))) / (Real.pi*k)) := by
    unfold spatialKernel
    simp only [Int.cast_natCast]
    congr 1
    have h := (GoldbachRamanujan.all_frequencies hq k).trans (BandMaskRam_cast q k).symm
    have he := congrArg Complex.re h
    simpa only [Complex.re_sum,Complex.exp_ofReal_mul_I_re, Complex.ofReal_re] using he
  cases m with
  | ofNat k => exact natCase k
  | negSucc k =>
    change spatialKernel Q n q (-((k+1:ℕ):ℤ)) = _
    rw [spatial_even]
    exact natCase (k+1)

private theorem spatial_zero (Q n : ℕ) (hs : 2*Q^2<n) :
    minorCoefficient Q n 0 = (volume ((catalogueArcs Q n)ᶜ ∩ Set.Ioc (0:ℝ) 1)).toReal := by
  have hi := minor_mode Q n hs (0:ℤ)
  have hmode : mode 0 = (fun _ : ℝ => (1:ℂ)) := by ext; simp [mode]
  rw [hmode,intervalIntegral.integral_of_le zero_le_one,
    integral_indicator_const 1 (measurable_catalogue Q n).compl, Complex.real_smul, mul_one] at hi
  have he := congrArg Complex.re hi.symm
  simpa only [Complex.ofReal_re,Int.natAbs_zero,Measure.real, Measure.restrict_apply (measurable_catalogue Q n).compl] using he

private theorem spatial_partition (L Q : ℕ) (hL : L ≤ Q) (f : ℕ → ℝ) :
    (∑ q ∈ Icc 1 Q, f q) = (∑ q ∈ Icc 1 L, f q) + ∑ q ∈ Ioc L Q, f q := by
  have hu : Icc 1 Q = Icc 1 L ∪ Ioc L Q := by
    ext q
    simp only [mem_Icc,mem_union,mem_Ioc]
    omega
  rw [hu,sum_union]
  exact Finset.disjoint_left.mpr (fun _ h₁ h₂ => (not_lt_of_ge (mem_Icc.mp h₁).2) (mem_Ioc.mp h₂).1)
theorem PEqualNP.Outside.L_goldbach_frontier_spatial_exact_split :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let minor := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let L₀ := fun n : ℕ => Nat.log 2 (n + 2); let M₀ := fun n : ℕ => ⌊(n:ℝ) / Real.sqrt (L₀ n : ℝ)⌋₊; let diagTerm := fun n : ℕ => (MeasureTheory.volume ((arcs n)ᶜ ∩ Set.Ioc (0:ℝ) 1)).toReal * (∑ p ∈ Finset.range (n+1), w p * w (n - p)); let sincKernel := fun (n q : ℕ) (m : ℤ) => (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), Real.cos (2 * Real.pi * (m:ℝ) * (a:ℝ) / (q:ℝ))) * (Real.sin (2 * Real.pi * (m:ℝ) * ((Q n:ℝ) / ((q:ℝ)*(n:ℝ)))) / (Real.pi * (m:ℝ))); let offLowNear := fun n : ℕ => ∑ j ∈ Finset.range (n+1), ∑ k ∈ (Finset.range (n+1)).filter (fun k : ℕ => j + k ≠ n ∧ Int.natAbs ((j:ℤ) + (k:ℤ) - (n:ℤ)) ≤ M₀ n), w j * w k * ∑ q ∈ Finset.Icc 1 (L₀ n), sincKernel n q ((j:ℤ) + (k:ℤ) - (n:ℤ)); let offLowFar := fun n : ℕ => ∑ j ∈ Finset.range (n+1), ∑ k ∈ (Finset.range (n+1)).filter (fun k : ℕ => M₀ n < Int.natAbs ((j:ℤ) + (k:ℤ) - (n:ℤ))), w j * w k * ∑ q ∈ Finset.Icc 1 (L₀ n), sincKernel n q ((j:ℤ) + (k:ℤ) - (n:ℤ)); let offHighMod := fun n : ℕ => ∑ j ∈ Finset.range (n+1), ∑ k ∈ (Finset.range (n+1)).filter (fun k : ℕ => j + k ≠ n), w j * w k * ∑ q ∈ Finset.Ioc (L₀ n) (Q n), sincKernel n q ((j:ℤ) + (k:ℤ) - (n:ℤ)); ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (minor n).re = diagTerm n - offLowNear n - offLowFar n - offHighMod n := by
  classical
  intro w E S Q arcs f minor L M D kernel near far high
  obtain ⟨N,hN⟩ := frontierSpatialCutoff
  use N
  intro n hn
  have hs : 2*(Q n)^2 < n := hN n hn
  have hL : L n ≤ Q n := by change L n ≤ (L n)^2; exact Nat.le_self_pow (by decide) _
  let T := range (n+1)
  let Z (j k : ℕ) := offset n j k
  let A (j k : ℕ) := w j*w k
  let V := (volume ((arcs n)ᶜ ∩ Set.Ioc (0:ℝ) 1)).toReal
  let Low (j k : ℕ) := A j k * ∑ q ∈ Icc 1 (L n), kernel n q (Z j k)
  let High (j k : ℕ) := A j k * ∑ q ∈ Ioc (L n) (Q n), kernel n q (Z j k)
  have ho (j k : ℕ) : (Z j k).natAbs = 0 ↔ j+k=n := by
    simp only [Int.natAbs_eq_zero, Z, offset]; omega
  have hterm (j k : ℕ) :
      A j k * minorCoefficient (Q n) n (Z j k).natAbs =
      (if j+k=n then V * A j k else 0) -
      (if j+k≠n ∧ (Z j k).natAbs ≤ M n then Low j k else 0) -
      (if M n < (Z j k).natAbs then Low j k else 0) -
      (if j+k≠n then High j k else 0) := by
    by_cases h : j+k=n
    · have hz := (ho j k).2 h
      simp [h,hz,spatial_zero (Q n) n hs,V,mul_comm,arcs,catalogueArcs]
    · have hz := (ho j k).not.mpr h
      have he : majorCoefficient (Q n) n (Z j k).natAbs =
          ∑ q ∈ Icc 1 (Q n), kernel n q (Z j k) := by
        unfold majorCoefficient
        apply Finset.sum_congr rfl
        intro q hq
        exact (spatial_terms (Q n) n q (mem_Icc.mp hq).1 (Z j k)).symm
      rw [minorCoefficient, if_neg hz,he,spatial_partition (L n) (Q n) hL]
      by_cases hnear : (Z j k).natAbs ≤ M n <;>
        simp [h,hnear,not_lt_of_ge,lt_of_not_ge,Low,High] <;> ring
  have hd : (∑ j ∈ T, ∑ k ∈ T, if j+k=n then V*A j k else 0) = D n := by
    change _ = V * ∑ j ∈ T, w j * w (n-j)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ n := by have := mem_range.mp hj; omega
    rw [Finset.sum_eq_single (n-j)]
    · simp [A, Nat.add_sub_of_le hj']
    · intro k _ hk
      rw [if_neg (by omega)]
    · intro ha
      exact (ha (mem_range.mpr (by omega))).elim
  have hm := integral_eq_arithmeticBulk (Q n) n hs w
  have ident : (minor n).re = arithmeticBulk (Q n) n w := by
    simpa only [minor,f,S,E,arcs,catalogueArcs, GoldbachWeight.spectrum, GoldbachWeight.phase, pow_two,
      Complex.ofReal_re] using congrArg Complex.re hm
  rw [ident]
  change (∑ j ∈ T, ∑ k ∈ T, A j k * minorCoefficient (Q n) n (Z j k).natAbs) = _
  simp_rw [hterm,Finset.sum_sub_distrib]
  rw [hd]
  simp only [near,far,high,Finset.sum_filter]
  rfl
