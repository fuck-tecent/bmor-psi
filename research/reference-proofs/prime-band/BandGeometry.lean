import UpstreamDisjoint

/-! Decompose the registered major arcs, including the two endpoint halves at denominator one. -/

namespace GoldbachMinor

open Finset Set MeasureTheory

def catalogueArcs (Q n : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / q| ≤ (Q : ℝ) / ((q : ℝ) * n)}

def catalogueCutoff (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

private noncomputable def radius (Q n q : ℕ) : ℝ := (Q : ℝ) / ((q : ℝ) * n)

private noncomputable def cell (Q n q a : ℕ) : Set ℝ :=
  Icc ((a:ℝ)/q - radius Q n q) ((a:ℝ)/q + radius Q n q)

private theorem in_cell {Q n q a : ℕ} {t : ℝ} :
    t ∈ cell Q n q a ↔ |t - (a:ℝ)/q| ≤ radius Q n q := by
  rw [abs_le]
  change (_ ≤ t ∧ t ≤ _) ↔ _
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

private theorem same_center {a b q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (ha : a.Coprime q) (hb : b.Coprime r) (he : a*r=b*q) : q=r ∧ a=b := by
  have h₁ : q ∣ a*r := he ▸ Nat.dvd_mul_left q b
  have h₂ : r ∣ b*q := he.symm ▸ Nat.dvd_mul_left r a
  have eq := Nat.dvd_antisymm (ha.symm.dvd_of_dvd_mul_left h₁) (hb.symm.dvd_of_dvd_mul_left h₂)
  subst r
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

private theorem unique_cell {a b q r Q n : ℕ} {t : ℝ}
    (hq : q ∈ Finset.Icc 1 Q) (hr : r ∈ Finset.Icc 1 Q)
    (ha : a.Coprime q) (hb : b.Coprime r) (hscale : 2*Q^2<n)
    (ht₁ : t ∈ cell Q n q a) (ht₂ : t ∈ cell Q n r b) : q=r ∧ a=b := by
  obtain ⟨hq₁,hq₂⟩ := Finset.mem_Icc.mp hq
  obtain ⟨hr₁,hr₂⟩ := Finset.mem_Icc.mp hr
  apply same_center hq₁ hr₁ ha hb
  by_contra h
  have hsep := PEqualNP.Outside.L_goldbach_arc_disjoint a b q r Q n t hq₁ hr₁ hq₂ hr₂ hscale h
    (in_cell.mp ht₁)
  exact (not_lt_of_ge (in_cell.mp ht₂)) hsep

private def numerators (q : ℕ) : Finset ℕ := ((range (q+1)).filter (·.Coprime q))

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

private noncomputable def clipped (x R : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ t in (Icc 0 1 ∩ Icc (x-R) (x+R)), f t

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

private theorem integral_closed {l u : ℝ} (h : l ≤ u) (f : ℝ → ℂ) :
    (∫ t in Icc l u, f t) = ∫ t in l..u, f t := by
  rw [intervalIntegral.integral_of_le h, integral_Icc_eq_integral_Ioc]

private theorem interior (f : ℝ → ℂ) {x R : ℝ} (hR : 0 ≤ R) (hl : 0 ≤ x-R)
    (hu : x+R ≤ 1) : clipped x R f = ∫ t in (x-R)..(x+R), f t := by
  unfold clipped
  rw [Set.inter_eq_right.mpr (Icc_subset_Icc hl hu), integral_closed (by linarith)]

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

/-- Exact reduction for the catalogue's closed major arcs on [0,1], with both endpoint halves. -/
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
