import Mathlib

/-!
The lower bound comes from disjoint windows at squarefree denominators between the
square-root cutoff divided by the fourth power of the binary logarithm and the square-root scale. Each factor-eight block contributes a
fixed amount to the sum of reciprocal denominators. The masked second moment then
gains one such contribution per block.

The project window and residue-energy lemmas are from PR 2519. The Ramanujan-sum
evaluations below are adapted from PRs 183 and 207 with attribution at their definitions.
-/

namespace Conjectures.Goldbach.SqrtArcSecondMomentFloor

section
namespace GoldbachSupport

/-- A one-sided interval at a distinct reduced rational stays outside the
    closed major arc about `b/r`. The shift `h` is an arbitrary real number. -/
theorem deepArcWindow (a b q r : ℕ) (H n h : ℝ)
    (hq : 0 < (q : ℝ)) (hr : 0 < (r : ℝ)) (hn : 0 < n)
    (hne : a * r ≠ b * q) (hh : 0 ≤ h) (hwidth : h ≤ 1 / (6 * n))
    (hmask : (q : ℝ) * H + (q : ℝ) * r / 6 < n) :
    H / ((r : ℝ) * n) < |(a : ℝ) / q + h - (b : ℝ) / r| := by
  have hqr := mul_pos hq hr
  have hscale := mul_pos hqr hn
  have hcap : H / ((r : ℝ) * n) * ((q : ℝ) * r * n) = q * H := by
    field_simp [hr.ne', hn.ne']
  have hcenter : ((a : ℝ) / q + h - (b : ℝ) / r) * ((q : ℝ) * r * n) =
      ((a : ℝ) * r - (b : ℝ) * q) * n + h * ((q : ℝ) * r * n) := by
    field_simp [hq.ne', hr.ne']
    ring
  have hw := (le_div_iff₀ (show 0 < 6 * n by linarith)).mp hwidth
  have hwscaled := mul_le_mul_of_nonneg_right hw hqr.le
  have hshift : h * ((q : ℝ) * r * n) ≤ (q : ℝ) * r / 6 := by
    nlinarith only [hwscaled]
  apply lt_of_not_ge
  intro hbad
  obtain ⟨hl, hu⟩ := abs_le.mp hbad
  have hleft := mul_le_mul_of_nonneg_right hl hscale.le
  have hright := mul_le_mul_of_nonneg_right hu hscale.le
  rw [neg_mul, hcap, hcenter] at hleft
  rw [hcap, hcenter] at hright
  rcases Nat.lt_or_gt_of_ne hne with lt | gt
  · have hi : a * r + 1 ≤ b * q := lt
    have hi' : (a : ℝ) * r + 1 ≤ (b : ℝ) * q := by exact_mod_cast hi
    have hgap := mul_le_mul_of_nonneg_right hi' hn.le
    nlinarith only [hleft, hgap, hshift, hmask]
  · have hi : b * q + 1 ≤ a * r := gt
    have hi' : (b : ℝ) * q + 1 ≤ (a : ℝ) * r := by exact_mod_cast hi
    have hgap := mul_le_mul_of_nonneg_right hi' hn.le
    have hpositive := mul_nonneg hh hscale.le
    nlinarith only [hright, hgap, hpositive, hmask, hqr.le]

/-- With a reduced numerator, a denominator larger than `Q` excludes
    coincidences with every center in the frozen wide-arc mask. -/
theorem outsideWideArcs (a q Q H n : ℕ) (h : ℝ) (ha : Nat.Coprime a q)
    (hq : Q < q) (hn : 0 < n) (hh : 0 ≤ h) (hwidth : h ≤ 1 / (6 * (n : ℝ)))
    (hmask : (q : ℝ) * H + (q : ℝ) * Q / 6 < n) :
    (a : ℝ) / q + h ∉ {t : ℝ | ∃ r b : ℕ, 1 ≤ r ∧ r ≤ Q ∧ b ≤ r ∧
      Nat.Coprime b r ∧ |t - (b : ℝ) / r| ≤ (H : ℝ) / ((r : ℝ) * n)} := by
  rintro ⟨r, b, hr, hrQ, _, _, hnear⟩
  have hrpos : 0 < r := hr
  have hqpos : 0 < q := Nat.zero_lt_of_lt hq
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hcross : a * r ≠ b * q := by
    intro heq
    have hd : q ∣ a * r := heq ▸ Nat.dvd_mul_left q b
    have hle := Nat.le_of_dvd hrpos (ha.symm.dvd_of_dvd_mul_left hd)
    exact (not_lt_of_ge hle) (lt_of_le_of_lt hrQ hq)
  have hrQ' : (r : ℝ) ≤ Q := by exact_mod_cast hrQ
  have hmask' : (q : ℝ) * H + (q : ℝ) * r / 6 < n := by
    linarith only [hmask, mul_le_mul_of_nonneg_left hrQ' hqr.le]
  exact (not_lt_of_ge hnear) (deepArcWindow a b q r H n h hqr (by exact_mod_cast hrpos)
    (by exact_mod_cast hn) hcross hh hwidth hmask')

/-- The two closed one-sided intervals of width `1/(6n)` do not meet
    if their denominator product is strictly below `6n`. -/
theorem deepArcWindowsDisjoint (a b q r : ℕ) (n u v : ℝ)
    (hq : 0 < (q : ℝ)) (hr : 0 < (r : ℝ)) (hn : 0 < n)
    (hne : a * r ≠ b * q) (hsize : (q : ℝ) * r < 6 * n)
    (hu : 0 ≤ u) (hU : u ≤ 1 / (6 * n)) (hv : 0 ≤ v) (hV : v ≤ 1 / (6 * n)) :
    (a : ℝ) / q + u ≠ (b : ℝ) / r + v := by
  intro heq
  rcases le_total v u with huv | hvu
  · have h := deepArcWindow a b q r 0 n (u - v) hq hr hn hne
      (sub_nonneg.mpr huv) (by linarith only [hU, hv]) (by linarith only [hsize])
    have hz : (a : ℝ) / q + (u - v) - (b : ℝ) / r = 0 := by linarith only [heq]
    simp [hz] at h
  · have hsize' : (r : ℝ) * q < 6 * n := by rwa [mul_comm]
    have h := deepArcWindow b a r q 0 n (v - u) hr hq hn (Ne.symm hne)
      (sub_nonneg.mpr hvu) (by linarith only [hV, hu]) (by linarith only [hsize'])
    have hz : (b : ℝ) / r + (v - u) - (a : ℝ) / q = 0 := by linarith only [heq]
    simp [hz] at h

end GoldbachSupport


open scoped BigOperators Interval

namespace GoldbachSupport

/-- A lower bound on the unweighted sum of the residue amplitudes gives a
lower bound on their second moment. The cardinality bound may be strict. -/
theorem residueEnergy {ι : Type*} (s : Finset ι) (z : ι → ℂ) {n : ℝ} {q : ℕ}
    (hn : 0 ≤ n) (hq : 0 < q) (hcard : s.card ≤ q)
    (hamp : n / 8 ≤ ‖∑ a ∈ s, z a‖) :
    n ^ 2 / (64 * (q : ℝ)) ≤ ∑ a ∈ s, ‖z a‖ ^ 2 := by
  have hsum := hamp.trans (norm_sum_le s z)
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ n / 8) hsum 2
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := fun a => ‖z a‖)
  have hc : (s.card : ℝ) ≤ q := by exact_mod_cast hcard
  have henergy : 0 ≤ ∑ a ∈ s, ‖z a‖ ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  apply (div_le_iff₀ (by positivity : 0 < 64 * (q : ℝ))).2
  nlinarith only [hsq, hcs, mul_le_mul_of_nonneg_right hc henergy]

/-- Integrating the pointwise estimate along each residue window of width
`1 / (6*n)` gives the contribution `n / (384*q)` for one denominator. -/
theorem residueWindowEnergy {ι : Type*} (s : Finset ι) (z : ι → ℝ → ℂ) {n : ℝ} {q : ℕ}
    (hn : 0 < n) (hq : 0 < q) (hcard : s.card ≤ q)
    (hz : ∀ a ∈ s, Continuous (z a))
    (hamp : ∀ h ∈ Set.Icc 0 (1 / (6 * n)), n / 8 ≤ ‖∑ a ∈ s, z a h‖) :
    n / (384 * (q : ℝ)) ≤ ∑ a ∈ s, ∫ h in (0 : ℝ)..1 / (6 * n), ‖z a h‖ ^ 2 := by
  have hcont : Continuous (fun h => ∑ a ∈ s, ‖z a h‖ ^ 2) :=
    continuous_finsetSum _ fun a ha => (hz a ha).norm.pow 2
  calc
    n / (384 * (q : ℝ)) = ∫ _ in (0 : ℝ)..1 / (6 * n), n ^ 2 / (64 * (q : ℝ)) := by
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      field_simp
      ring
    _ ≤ ∫ h in (0 : ℝ)..1 / (6 * n), ∑ a ∈ s, ‖z a h‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on (by positivity) intervalIntegrable_const
        (hcont.intervalIntegrable ..)
      exact fun h hh => residueEnergy s (fun a => z a h) hn.le hq hcard (hamp h hh)
    _ = _ := intervalIntegral.integral_finsetSum fun a ha =>
      ((hz a ha).norm.pow 2).intervalIntegrable ..

end GoldbachSupport
end

section
open MeasureTheory Set
open scoped BigOperators Interval

namespace GoldbachSupport

def publishedWideArcs (D H n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ r b : ℕ, 1 ≤ r ∧ r ≤ D ∧ b ≤ r ∧ Nat.Coprime b r ∧
    |t - (b : ℝ) / r| ≤ (H : ℝ) / ((r : ℝ) * n)}

theorem measurable_publishedWideArcs (D H n : ℕ) : MeasurableSet (publishedWideArcs D H n) := by
  unfold publishedWideArcs
  simp_rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.iUnion
  intro b
  by_cases h : 1 ≤ r ∧ r ≤ D ∧ b ≤ r ∧ Nat.Coprime b r
  · rcases h with ⟨hr, hrD, hb, hc⟩
    have he : {t : ℝ | 1 ≤ r ∧ r ≤ D ∧ b ≤ r ∧ Nat.Coprime b r ∧
        |t - (b : ℝ) / r| ≤ (H : ℝ) / ((r : ℝ) * n)} =
        {t : ℝ | |t - (b : ℝ) / r| ≤ (H : ℝ) / ((r : ℝ) * n)} := by
      ext t
      exact ⟨fun h => h.2.2.2.2, fun h => ⟨hr, hrD, hb, hc, h⟩⟩
    rw [he]
    exact (isClosed_le (show Continuous (fun t : ℝ => |t - (b : ℝ) / r|) by fun_prop)
      (show Continuous (fun _ : ℝ => (H : ℝ) / ((r : ℝ) * n)) by fun_prop)).measurableSet
  · have he : {t : ℝ | 1 ≤ r ∧ r ≤ D ∧ b ≤ r ∧ Nat.Coprime b r ∧
        |t - (b : ℝ) / r| ≤ (H : ℝ) / ((r : ℝ) * n)} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h₁,h₂,h₃,h₄,_⟩
      exact h ⟨h₁,h₂,h₃,h₄⟩
    rw [he]
    exact MeasurableSet.empty

private theorem reduced_centers_unique {q r a b : ℕ} (hq : 0 < q)
    (ha : Nat.Coprime a q) (hb : Nat.Coprime b r) (he : a * r = b * q) :
    q = r ∧ a = b := by
  have hdq : q ∣ a * r := he ▸ Nat.dvd_mul_left q b
  have hdr : r ∣ b * q := he.symm ▸ Nat.dvd_mul_left r a
  have hqr := Nat.dvd_antisymm (ha.symm.dvd_of_dvd_mul_left hdq) (hb.symm.dvd_of_dvd_mul_left hdr)
  subst r
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

/-- Sum the disjoint shifted intervals at reduced fractions and keep only their
contribution to the integral over the complement of the published arc family. -/
theorem assembleWindows (s : Finset ℕ) (D H n : ℕ) (S : ℝ → ℂ) (hS : Continuous S)
    (hn : 0 < n)
    (hden : ∀ q ∈ s, D < q)
    (hend : ∀ q ∈ s, (q : ℝ) ≤ 6 * n)
    (hmask : ∀ q ∈ s, (q : ℝ) * H + (q : ℝ) * D / 6 < n)
    (hpair : ∀ q ∈ s, ∀ r ∈ s, (q : ℝ) * r < 6 * n)
    (hamp : ∀ q ∈ s, ∀ h ∈ Icc (0 : ℝ) (1 / (6 * n)),
      (n : ℝ) / 8 ≤ ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          S ((a : ℝ) / q + h)‖) :
    ∑ q ∈ s, (n : ℝ) / (384 * (q : ℝ)) ≤
      ∫ t in (0 : ℝ)..1, (publishedWideArcs D H n)ᶜ.indicator (fun x => ‖S x‖ ^ 2) t := by
  classical
  let A := fun q : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q)
  let indices := s.sigma A
  let w : ℝ := 1 / (6 * (n : ℝ))
  let f : ℝ → ℝ := fun t => ‖S t‖ ^ 2
  let c : (Σ _ : ℕ, ℕ) → ℝ := fun i => (i.2 : ℝ) / i.1
  let W := fun i => Ioc (c i) (c i + w)
  let target := Ioc (0 : ℝ) 1 ∩ (publishedWideArcs D H n)ᶜ
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hc : Continuous f := hS.norm.pow 2
  have hindex {i : Σ _ : ℕ, ℕ} (hi : i ∈ indices) :
      i.1 ∈ s ∧ i.2 < i.1 ∧ Nat.Coprime i.2 i.1 := by
    simpa [indices, A] using hi
  have hqpos {q : ℕ} (hq : q ∈ s) : 0 < q := Nat.zero_lt_of_lt (hden q hq)
  have hge {q : ℕ} (hq : q ∈ s) : 0 < (q : ℝ) := by exact_mod_cast hqpos hq
  have hsubset {i : Σ _ : ℕ, ℕ} (hi : i ∈ indices) : W i ⊆ target := by
    rcases hindex hi with ⟨hq, ha, hcop⟩
    intro t ht
    change c i < t ∧ t ≤ c i + w at ht
    have hfirst : 0 ≤ c i := by dsimp [c]; positivity
    have hq := hge hq
    have ha1 : (i.2 : ℝ) + 1 ≤ i.1 := by exact_mod_cast ha
    have hsmall : w ≤ 1 / (i.1 : ℝ) := one_div_le_one_div_of_le hq (hend _ (hindex hi).1)
    have hlast : t ≤ 1 := calc
      t ≤ (i.2 : ℝ) / i.1 + 1 / i.1 := by change t ≤ c i + 1 / i.1; linarith only [ht.2, hsmall]
      _ = ((i.2 : ℝ) + 1) / i.1 := by ring
      _ ≤ 1 := (div_le_one hq).2 ha1
    refine ⟨⟨hfirst.trans_lt ht.1, hlast⟩, ?_⟩
    have hout := outsideWideArcs i.2 i.1 D H n (t - c i) hcop
      (hden _ (hindex hi).1) hn (sub_nonneg.mpr ht.1.le)
      (by change t - c i ≤ w; linarith only [ht.2]) (hmask _ (hindex hi).1)
    change t ∉ publishedWideArcs D H n
    change c i + (t - c i) ∉ publishedWideArcs D H n at hout
    rwa [add_sub_cancel] at hout
  have hdisj : Set.Pairwise (↑indices) (fun i j => Disjoint (W i) (W j)) := by
    intro i hi j hj hne
    rcases hindex hi with ⟨hqi, hai, hci⟩
    rcases hindex hj with ⟨hqj, haj, hcj⟩
    have hcross : i.2 * j.1 ≠ j.2 * i.1 := by
      intro he
      obtain ⟨h₁,h₂⟩ := reduced_centers_unique (hqpos hqi) hci hcj he
      apply hne
      cases i
      cases j
      simp_all
    apply Set.disjoint_left.mpr
    intro t ht hu
    change c i < t ∧ t ≤ c i + w at ht
    change c j < t ∧ t ≤ c j + w at hu
    have h := deepArcWindowsDisjoint i.2 j.2 i.1 j.1 n (t - c i) (t - c j)
      (hge hqi) (hge hqj) hn' hcross (hpair _ hqi _ hqj)
      (sub_nonneg.mpr ht.1.le) (by change t - c i ≤ w; linarith only [ht.2])
      (sub_nonneg.mpr hu.1.le) (by change t - c j ≤ w; linarith only [hu.2])
    apply h
    change c i + (t - c i) = c j + (t - c j)
    abel
  have hint {a b : ℝ} : IntegrableOn f (Ioc a b) volume := by
    exact (hc.integrableOn_Icc (a := a) (b := b)).mono_set Ioc_subset_Icc_self
  have htarget : IntegrableOn f target volume := hint.mono_set (Set.inter_subset_left ..)
  have hshift (i : Σ _ : ℕ, ℕ) : (∫ h in (0 : ℝ)..w, f (c i + h)) = ∫ x in W i, f x := by
    rw [intervalIntegral.integral_comp_add_left, add_zero, intervalIntegral.integral_of_le]
    exact le_add_of_nonneg_right hw
  calc
    ∑ q ∈ s, (n : ℝ) / (384 * (q : ℝ)) ≤
        ∑ q ∈ s, ∑ a ∈ A q, ∫ h in (0 : ℝ)..w, f ((a : ℝ) / q + h) := by
      apply Finset.sum_le_sum
      intro q hq
      have hcard : (A q).card ≤ q :=
        (Finset.card_filter_le ..).trans_eq (Finset.card_range q)
      exact residueWindowEnergy (A q) (fun a h => S ((a : ℝ) / q + h))
        hn' (hqpos hq) hcard (fun a _ => hS.comp (continuous_const.add continuous_id)) (hamp q hq)
    _ = ∑ i ∈ indices, ∫ h in (0 : ℝ)..w, f (c i + h) :=
      Finset.sum_sigma' s A _
    _ = ∑ i ∈ indices, ∫ x in W i, f x := Finset.sum_congr rfl fun i _ => hshift i
    _ = ∫ x in ⋃ i ∈ indices, W i, f x :=
      (integral_biUnion_finset indices (fun _ _ => measurableSet_Ioc) hdisj (fun _ _ => hint)).symm
    _ ≤ ∫ x in target, f x := by
      apply setIntegral_mono_set htarget (Filter.Eventually.of_forall fun x => sq_nonneg ‖S x‖)
      exact Filter.Eventually.of_forall fun _ hx => by
        rcases Set.mem_iUnion₂.mp hx with ⟨i,hi,ht⟩
        exact hsubset hi ht
    _ = ∫ t in (0 : ℝ)..1, (publishedWideArcs D H n)ᶜ.indicator (fun x => ‖S x‖ ^ 2) t := by
      rw [intervalIntegral.integral_of_le (by norm_num), setIntegral_indicator (measurable_publishedWideArcs ..).compl]

end GoldbachSupport
end

section
/-! Prime and CRT evaluations adapted from the Apache-2.0 Goldbach project,
PRs #183 (TranswarpDrive) and #207 (XianWu18), respectively. -/
namespace GoldbachL2Arithmetic

private def unitsBelow (m : ℕ) := (Finset.range m).filter (fun a => Nat.Coprime a m)

private theorem unitsBelow_card (m : ℕ) : (unitsBelow m).card = m.totient := by
  unfold unitsBelow
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun _ => Nat.coprime_comm)

private noncomputable def phase (m h a : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((h : ℝ) * a / m) : ℝ) : ℂ) * Complex.I)

private theorem phase_character (m h a : ℕ) [NeZero m] :
    phase m h a = ZMod.stdAddChar ((h : ZMod m) * (a : ZMod m)) := by
  have ch := ZMod.stdAddChar_coe (N := m) ((h * a : ℕ) : ℤ)
  push_cast at ch
  rw [ch]
  unfold phase
  push_cast
  congr 1
  ring

private theorem phase_modulus (m h a : ℕ) [NeZero m] :
    phase m h (a % m) = phase m h a := by
  simp only [phase_character, ZMod.natCast_mod]

private theorem phase_pair (q r h a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    phase (q*r) h ((r*a + q*b) % (q*r)) = phase q h a * phase r h b := by
  have : NeZero (q*r) := ⟨Nat.ne_of_gt (Nat.mul_pos hq hr)⟩
  rw [phase_modulus]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have qnz : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have rnz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

theorem ram_crt :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ q r h, 0<q → 0<r → Nat.Coprime q r → ram (q*r) h=ram q h*ram r h := by
  dsimp only
  intro q r h hq hr cop
  let combine (x : ℕ × ℕ) := (r*x.1 + q*x.2) % (q*r)
  let pairs := unitsBelow q ×ˢ unitsBelow r
  have member {m a : ℕ} : a ∈ unitsBelow m ↔ a < m ∧ Nat.Coprime a m := by
    simp only [unitsBelow, Finset.mem_filter, Finset.mem_range]
  have maps : pairs.image combine ⊆ unitsBelow (q*r) := by
    intro z hz
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    apply member.mpr
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hq hr), ?_⟩
    change Nat.gcd ((r*a + q*b) % (q*r)) (q*r) = 1
    rw [← Nat.gcd_rec]
    change Nat.Coprime (q*r) (r*a + q*b)
    apply Nat.coprime_mul_iff_left.mpr
    constructor
    · rw [Nat.coprime_add_mul_left_right]
      exact cop.mul_right (member.mp ha).2.symm
    · rw [add_comm, Nat.coprime_add_mul_left_right]
      exact cop.symm.mul_right (member.mp hb).2.symm
  have injective : Set.InjOn combine (↑pairs) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    have congruence : r*a + q*b ≡ r*c + q*d [MOD q*r] := he
    apply Prod.ext
    · have hmod := congruence.of_dvd (dvd_mul_right q r)
      have reduced : r*a ≡ r*c [MOD q] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop reduced).eq_of_lt_of_lt
        (member.mp ha).1 (member.mp hc).1
    · have hmod := congruence.of_dvd (dvd_mul_left r q)
      have reduced : q*b ≡ q*d [MOD r] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop.symm reduced).eq_of_lt_of_lt
        (member.mp hb).1 (member.mp hd).1
  have covers : pairs.image combine = unitsBelow (q*r) := by
    apply Finset.eq_of_subset_of_card_le maps
    rw [Finset.card_image_of_injOn injective, unitsBelow_card, Nat.totient_mul cop]
    simp only [pairs, Finset.card_product, unitsBelow_card]
    exact le_rfl
  change (∑ z ∈ unitsBelow (q*r), phase (q*r) h z) =
    (∑ a ∈ unitsBelow q, phase q h a) * ∑ b ∈ unitsBelow r, phase r h b
  rw [← covers, Finset.sum_image injective, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  exact Finset.sum_congr rfl (fun x _ => phase_pair q r h x.1 x.2 hq hr)

namespace PrimeRam

noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def ram (q h : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    phase ((h : ℝ) * (a : ℝ) / (q : ℝ))

theorem prime_sum (p h : ℕ) (hp : Nat.Prime p) :
    ram p h = if p ∣ h then (p : ℂ) - 1 else -1 := by
  let z := Complex.exp (2 * Real.pi * Complex.I / (p : ℂ))
  have hz : IsPrimitiveRoot z p := Complex.isPrimitiveRoot_exp p hp.ne_zero
  have he (a : ℕ) : phase ((h : ℝ) * (a : ℝ) / (p : ℝ)) = (z ^ h) ^ a := by
    unfold phase z
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have filt : (Finset.range p).filter (fun a => Nat.Coprime a p) = (Finset.range p).erase 0 := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    constructor
    · rintro ⟨ha, ham⟩
      exact ⟨fun ha0 => (hp.coprime_iff_not_dvd.mp ham.symm) (ha0 ▸ dvd_zero p), ha⟩
    · rintro ⟨han, ha⟩
      exact ⟨ha, (hp.coprime_iff_not_dvd.mpr (fun hd =>
        (not_le_of_gt ha) (Nat.le_of_dvd (Nat.pos_of_ne_zero han) hd))).symm⟩
  unfold ram
  rw [filt]
  simp_rw [he]
  have rem := Finset.sum_erase_add (Finset.range p) (fun a : ℕ => (z ^ h) ^ a)
    (Finset.mem_range.mpr hp.pos)
  rw [pow_zero] at rem
  by_cases hd : p ∣ h
  · rw [ite_eq_left hd]
    rw [(hz.pow_eq_one_iff_dvd h).mpr hd] at rem ⊢
    simp at rem
    simpa using eq_sub_of_add_eq rem
  · rw [ite_eq_right hd]
    rw [(hz.pow_of_coprime h (hp.coprime_iff_not_dvd.mpr hd).symm).geom_sum_eq_zero hp.one_lt] at rem
    exact eq_neg_of_add_eq_zero_left rem


end PrimeRam
end GoldbachL2Arithmetic
end

section
namespace GoldbachL2Arithmetic

open Finset
open PrimeRam (ram)

noncomputable abbrev E (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

noncomputable def primeTerm (p : ℕ) (h : ℝ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) * E ((p : ℝ) * h)

noncomputable def primeSum (n : ℕ) (h : ℝ) : ℂ :=
  ∑ p ∈ n.primesLE, primeTerm p h

theorem primeSum_eq_catalogue (n : ℕ) (h : ℝ) :
    primeSum n h = ∑ p ∈ range (n + 1),
      ((if p.Prime then Real.log (p : ℝ) else 0 : ℝ) : ℂ) * E ((p : ℝ) * h) := by
  rw [primeSum, Nat.primesLE_eq_filter_range, sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp : p.Prime <;> simp [hp, primeTerm]

private theorem ram_primeFactors_product (s : Finset ℕ) (hs : ∀ r ∈ s, r.Prime)
    (p : ℕ) (hp : p.Prime) :
    ram (∏ r ∈ s, r) p = (-1 : ℂ) ^ s.card * (if p ∈ s then 1 - (p : ℂ) else 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ram, PrimeRam.phase]
  | @insert r s hrs ih =>
    have hr : r.Prime := hs _ (mem_insert_self ..)
    have hs' : ∀ j ∈ s, Nat.Prime j := fun j hj => hs j (mem_insert_of_mem hj)
    have hprod : 0 < ∏ j ∈ s, j := Finset.prod_pos fun j hj => (hs' j hj).pos
    have hcop : r.Coprime (∏ j ∈ s, j) := Nat.Coprime.prod_right fun j hj =>
      (Nat.coprime_primes hr (hs' j hj)).2 (fun he => hrs (he ▸ hj))
    rw [prod_insert hrs, card_insert_of_notMem hrs, pow_succ]
    have hf : ram (r * ∏ j ∈ s, j) p = ram r p * ram (∏ j ∈ s, j) p :=
      ram_crt r _ p hr.pos hprod hcop
    rw [hf, PrimeRam.prime_sum _ _ hr, ih hs']
    by_cases he : p = r
    · subst p
      simp [hrs]
      ring
    · have hn : ¬ r ∣ p := fun hd => he ((hp.dvd_iff_eq hr.ne_one).mp hd)
      by_cases hm : p ∈ s <;> simp [hn, he, hm]

theorem ram_at_prime_of_squarefree (q p : ℕ) (hq : Squarefree q) (hp : p.Prime) :
    ram q p = (-1 : ℂ) ^ q.primeFactors.card *
      (if p ∈ q.primeFactors then 1 - (p : ℂ) else 1) := by
  simpa only [Nat.prod_primeFactors_of_squarefree hq] using
    ram_primeFactors_product q.primeFactors (fun _ ha => Nat.prime_of_mem_primeFactors ha) p hp

private theorem term_shift (p a q : ℕ) (h : ℝ) :
    primeTerm p ((a : ℝ) / q + h) =
      primeTerm p h * PrimeRam.phase ((p : ℝ) * a / q) := by
  unfold primeTerm E PrimeRam.phase
  rw [mul_assoc ((Real.log (p : ℝ) : ℂ)) _ _, ← Complex.exp_add]
  congr 2
  push_cast
  ring

noncomputable def correction (n q : ℕ) (h : ℝ) : ℂ :=
  ∑ p ∈ n.primesLE.filter (fun p => p ∈ q.primeFactors), (p : ℂ) * primeTerm p h

theorem sum_reduced_shifts (n q : ℕ) (sq : Squarefree q) (h : ℝ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), primeSum n ((a : ℝ) / q + h)) =
      (-1 : ℂ) ^ q.primeFactors.card * (primeSum n h - correction n q h) := by
  classical
  unfold primeSum correction
  rw [sum_comm, sum_filter, ← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro p hp
  simp_rw [term_shift]
  rw [← mul_sum]
  change primeTerm p h * ram q p = _
  rw [ram_at_prime_of_squarefree _ _ sq (Nat.prime_of_mem_primesLE hp)]
  by_cases hm : p ∈ q.primeFactors <;> simp [hm] <;> ring

theorem bound_correction (n q : ℕ) (sq : Squarefree q) (h : ℝ) :
    ‖correction n q h‖ ≤ (q : ℝ) * Real.log q := by
  classical
  let fs := n.primesLE.filter (fun p => p ∈ q.primeFactors)
  have hlog (p : ℕ) (hp : p ∈ q.primeFactors) : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)
  calc
    _ ≤ ∑ p ∈ fs, ‖(p : ℂ) * primeTerm p h‖ := norm_sum_le ..
    _ ≤ ∑ p ∈ fs, (q : ℝ) * Real.log (p : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hm := (mem_filter.mp hp).2
      have hle : p ≤ q := Nat.le_of_dvd sq.ne_zero.bot_lt (Nat.dvd_of_mem_primeFactors hm)
      simp only [primeTerm, E, norm_mul, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hlog p hm), Complex.norm_exp_ofReal_mul_I, mul_one]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (hlog p hm)
    _ ≤ ∑ p ∈ q.primeFactors, (q : ℝ) * Real.log (p : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg (fun p hp => (mem_filter.mp hp).2)
      exact fun p hp _ => mul_nonneg (by positivity) (hlog p hp)
    _ = _ := by
      rw [← mul_sum, ← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree sq]

theorem lower_norm_small_shift (n : ℕ) (hn : 0 < n) (h : ℝ) (hh : 0 ≤ h)
    (hmax : h ≤ 1 / (6 * (n : ℝ))) :
    Chebyshev.theta n / 2 ≤ ‖primeSum n h‖ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  apply le_trans _ (Complex.re_le_norm _)
  rw [Chebyshev.theta_eq_sum_primesLE_log, sum_div, primeSum, Complex.re_sum]
  apply sum_le_sum
  intro p hp
  have hp' : Nat.Prime p := Nat.prime_of_mem_primesLE hp
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp'.one_le)
  have hpn : (p : ℝ) ≤ n := by exact_mod_cast Nat.le_of_mem_primesLE hp
  have hnh : 6 * (n : ℝ) * h ≤ 1 := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 6 * n)).mp hmax
    linarith
  have hz : (p : ℝ) * h ≤ 1 / 6 := by
    have := mul_le_mul_of_nonneg_right hpn hh
    nlinarith only [hnh, this]
  have hangle : 2 * Real.pi * ((p : ℝ) * h) ≤ Real.pi / 3 := by
    nlinarith only [mul_le_mul_of_nonneg_left hz Real.pi_pos.le]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ 2 * Real.pi * ((p : ℝ) * h))
    (by linarith [Real.pi_pos] : Real.pi / 3 ≤ Real.pi) hangle
  rw [Real.cos_pi_div_three] at hcos
  simp only [primeTerm, E, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.exp_ofReal_mul_I_re]
  linarith only [mul_le_mul_of_nonneg_left hcos hlog]

theorem reduced_amplitude (n q : ℕ) (hn : 0 < n) (sq : Squarefree q)
    (hθ : (n : ℝ) / 2 ≤ Chebyshev.theta n)
    (hsmall : (q : ℝ) * Real.log q ≤ (n : ℝ) / 8)
    (h : ℝ) (hh : 0 ≤ h) (hmax : h ≤ 1 / (6 * (n : ℝ))) :
    (n : ℝ) / 8 ≤ ‖∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      primeSum n ((a : ℝ) / q + h)‖ := by
  rw [sum_reduced_shifts _ _ sq, norm_mul, norm_pow]
  simp only [norm_neg, norm_one, one_pow, one_mul]
  apply le_trans _ (norm_sub_norm_le ..)
  linarith only [hθ, lower_norm_small_shift n hn h hh hmax, (bound_correction n q sq h).trans hsmall]

end GoldbachL2Arithmetic
end

section
open Filter
open scoped Topology

namespace GoldbachSupport

theorem primeAmplitudeBounds : ∀ᶠ n : ℕ in atTop,
    2 ≤ n ∧
    (n : ℝ) / 2 ≤ Chebyshev.theta n ∧
    ∀ q : ℕ, q ≤ ⌊Real.sqrt n / 4⌋₊ → (q : ℝ) * Real.log q ≤ n / 8 := by
  have smallLog (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
      ∀ᶠ n : ℕ in atTop, Real.log n ≤ c * (n : ℝ) ^ a := by
    have h := ((isLittleO_log_rpow_atTop ha).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).bound hc
    filter_upwards [h] with n hn
    simpa [Function.comp_def, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) a)] using hn
  have htheta := ((Chebyshev.tendsto_theta_div_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (lt_mem_nhds (by norm_num : (1:ℝ)/2 < 1)))
  filter_upwards [eventually_ge_atTop 2, htheta, smallLog (1/2) (1/8) (by norm_num) (by norm_num)] with n hn hθ hsmall
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  change (1:ℝ)/2 < Chebyshev.theta n / (n : ℝ) at hθ
  refine ⟨hn, by linarith [(lt_div_iff₀ hnpos).mp hθ], ?_⟩
  intro q hq
  have hq' : (q:ℝ) ≤ Real.sqrt n / 4 :=
    (by exact_mod_cast hq : (q:ℝ) ≤ (⌊Real.sqrt n / 4⌋₊ : ℕ)).trans (Nat.floor_le (by positivity))
  have hsq := Real.sq_sqrt hnpos.le
  have hsn : Real.sqrt n ≤ n := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hqn : (q:ℝ) ≤ n := by linarith [Real.sqrt_nonneg (n:ℝ)]
  rcases Nat.eq_zero_or_pos q with rfl | hqp
  · simp; positivity
  · have hlogq := Real.log_le_log (by exact_mod_cast hqp : 0 < (q:ℝ)) hqn
    rw [← Real.sqrt_eq_rpow] at hsmall
    calc
      _ ≤ Real.sqrt n * ((1/8) * Real.sqrt n) := by
        apply mul_le_mul (by linarith [Real.sqrt_nonneg (n:ℝ)]) (hlogq.trans hsmall)
          (Real.log_natCast_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by nlinarith

end GoldbachSupport
end

section
open Finset Real Filter
open scoped BigOperators

namespace GoldbachCount

/-- Isolate the term at two and telescope the reciprocal-square tail. -/
private theorem inv_square_budget (X : ℕ) :
    ∑ d ∈ Ioc 1 X, ((d : ℝ) ^ 2)⁻¹ ≤ 3 / 4 := by
  by_cases h : 2 ≤ X
  · have hh := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 2) (n := X) (by decide) h
    rw [← sum_Ioc_consecutive _ (by decide : 1 ≤ 2) h]
    simp only [show Ioc 1 2 = {2} by decide, sum_singleton, Nat.cast_ofNat]
    have hp : 0 ≤ (↑X : ℝ)⁻¹ := by positivity
    norm_num at hh ⊢
    linarith
  · have : X ≤ 1 := by omega
    norm_num [Ioc_eq_empty_of_le this]

private theorem castDivSum (X : ℕ) (s : Finset ℕ) :
    ((∑ d ∈ s, X / d^2 : ℕ) : ℝ) ≤ ∑ d ∈ s, (X : ℝ) / (d : ℝ)^2 := by
  calc
    _ = ∑ d ∈ s, ((X/d^2:ℕ):ℝ) := Nat.cast_sum (R:=ℝ) s (fun d => X/d^2)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d _
      calc
        _ ≤ (X : ℝ) / (↑(d^2 : ℕ) : ℝ) := @Nat.cast_div_le ℝ _ _ _ X (d^2)
        _ = _ := by rw [Nat.cast_pow]

/-- Every nonsquarefree positive integer is a multiple of a prime square. Counting from
zero makes the count for each divisor exactly a quotient, without an endpoint loss. -/
private theorem squarefree_count_from_zero (X : ℕ) :
    (X : ℝ) / 4 ≤ (((Ioc 0 X).filter Squarefree).card : ℝ) := by
  classical
  let B := (Ioc 0 X).filter (fun k => ¬Squarefree k)
  let M := fun d : ℕ => (Ioc 0 X).filter (fun k => d^2 ∣ k)
  have sub : B ⊆ (Ioc 1 X).biUnion M := by
    intro k hk
    obtain ⟨hkI, hns⟩ := mem_filter.mp hk
    rw [Nat.squarefree_iff_prime_squarefree] at hns
    push Not at hns
    obtain ⟨p, hp, hd⟩ := hns
    apply mem_biUnion.mpr
    refine ⟨p, mem_Ioc.mpr ⟨hp.one_lt, ?_⟩, mem_filter.mpr ⟨hkI, by simpa [pow_two] using hd⟩⟩
    exact (Nat.le_of_dvd (mem_Ioc.mp hkI).1 (dvd_trans (dvd_mul_right p p) hd)).trans
      (mem_Ioc.mp hkI).2
  have hbN : B.card ≤ ∑ d ∈ Ioc 1 X, X / d^2 := by
    calc
      B.card ≤ ((Ioc 1 X).biUnion M).card := card_le_card sub
      _ ≤ ∑ d ∈ Ioc 1 X, (M d).card := card_biUnion_le
      _ = _ := by simp [M, Nat.Ioc_filter_dvd_card_eq_div]
  have hb : (B.card : ℝ) ≤ (X : ℝ) * (3 / 4) := by
    calc
      (B.card : ℝ) ≤ ((∑ d ∈ Ioc 1 X, X / d^2 : ℕ) : ℝ) := Nat.cast_le.mpr hbN
      _ ≤ ∑ d ∈ Ioc 1 X, (X : ℝ) / (d:ℝ)^2 := castDivSum X (Ioc 1 X)
      _ = (X : ℝ) * ∑ d ∈ Ioc 1 X, ((d : ℝ)^2)⁻¹ := by simp_rw [div_eq_mul_inv, mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (inv_square_budget X) (by positivity)
  have part : ((Ioc 0 X).filter Squarefree).card + B.card = X := by
    simpa [B] using (card_filter_add_card_filter_not (s := Ioc 0 X) Squarefree)
  have pp : (((Ioc 0 X).filter Squarefree).card : ℝ) + B.card = X := by exact_mod_cast part
  linarith

/-- At least one quarter of the first `8*T` integers are squarefree, and at most
`T` of these are at or below the lower endpoint of this block. -/
private theorem block_count (T : ℕ) :
    T ≤ ((Ioc T (8*T)).filter Squarefree).card := by
  classical
  have h := squarefree_count_from_zero (8*T)
  have part : ((Ioc 0 T).filter Squarefree).card + ((Ioc T (8*T)).filter Squarefree).card =
      ((Ioc 0 (8*T)).filter Squarefree).card := by
    rw [← Ioc_union_Ioc_eq_Ioc (Nat.zero_le T) (show T ≤ 8*T by omega), filter_union,
      card_union_of_disjoint]
    exact (Ioc_disjoint_Ioc_of_le (by rfl : T ≤ T)).mono (filter_subset ..) (filter_subset ..)
  have hleft : ((Ioc 0 T).filter Squarefree).card ≤ T := by
    simpa using card_le_card (filter_subset Squarefree (Ioc 0 T))
  push_cast at h
  have hb : 2*T ≤ ((Ioc 0 (8*T)).filter Squarefree).card := by
    have : (2:ℝ)*T ≤ ((Ioc 0 (8*T)).filter Squarefree).card := by linarith
    exact_mod_cast this
  omega

/-- Reciprocal mass of squarefree denominators in the half-open interval `(a,b]`. -/
noncomputable def mass (a b : ℕ) : ℝ :=
  ∑ q ∈ (Ioc a b).filter Squarefree, 1 / (q : ℝ)

private theorem block_mass (T : ℕ) (hT : 0 < T) :
    (1:ℝ)/8 ≤ mass T (8*T) := by
  classical
  obtain hcount := block_count T
  let s := (Ioc T (8*T)).filter Squarefree
  have hc : (T : ℝ) ≤ s.card := by exact_mod_cast hcount
  have hpos : 0 < (T : ℝ) := by exact_mod_cast hT
  calc
    (1:ℝ)/8 = T * (1/(8*(T:ℝ))) := by field_simp
    _ ≤ s.card * (1/(8*(T:ℝ))) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = ∑ q ∈ s, 1/(8*(T:ℝ)) := by simp
    _ ≤ mass T (8*T) := by
      apply sum_le_sum
      intro q hq
      obtain ⟨hlo,hhi⟩ := mem_Ioc.mp (mem_filter.mp hq).1
      have qpos : 0 < (q:ℝ) := by exact_mod_cast hT.trans hlo
      exact one_div_le_one_div_of_le qpos (by exact_mod_cast hhi)

/-- Every complete factor-of-eight block contributes at least `1/8`. -/
theorem mass_blocks (D J : ℕ) (hd : 0 < D) :
    (J:ℝ)/8 ≤ mass D (8^J*D) := by
  classical
  induction J with
  | zero => simp [mass]
  | succ j ih =>
    let T := 8^j * D
    have ht : 0<T := by dsimp [T]; positivity
    have hdT : D ≤ T := Nat.le_mul_of_pos_left D (by positivity)
    have hsplit : mass D T + mass T (8*T) = mass D (8*T) := by
      simp only [mass, sum_filter]
      exact sum_Ioc_consecutive _ hdT (by omega)
    have hb := block_mass T ht
    have ht8 : 8^(j+1)*D = 8*T := by dsimp [T]; ring
    rw [ht8]
    change (j:ℝ)/8 ≤ mass D T at ih
    push_cast
    linarith

end GoldbachCount
end

section
namespace GoldbachSupport

theorem denominatorWindowLimits (n D H : ℕ) (hn : 2 ≤ n)
    (hden : (D : ℝ) ≤ Real.sqrt n) (hH : (H : ℝ) ≤ Real.sqrt n) :
    (∀ q : ℕ, q ≤ ⌊Real.sqrt n / 4⌋₊ → (q : ℝ) ≤ 6 * n) ∧
    (∀ q : ℕ, q ≤ ⌊Real.sqrt n / 4⌋₊ → (q : ℝ) * H + (q:ℝ) * D / 6 < n) ∧
    (∀ q r : ℕ, q ≤ ⌊Real.sqrt n / 4⌋₊ → r ≤ ⌊Real.sqrt n / 4⌋₊ →
      (q:ℝ) * r < 6 * n) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hx := Real.sqrt_nonneg (n:ℝ)
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hsle := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith : (1:ℝ) ≤ n))
  have hqbound (q : ℕ) (hq : q ≤ ⌊Real.sqrt n / 4⌋₊) : (q:ℝ) ≤ Real.sqrt n / 4 :=
    (by exact_mod_cast hq : (q:ℝ) ≤ (⌊Real.sqrt n / 4⌋₊ : ℕ)).trans (Nat.floor_le (by positivity))
  refine ⟨fun q hq => by linarith [hqbound q hq], ?_, ?_⟩
  · intro q hq
    have h₁ := mul_le_mul (hqbound q hq) hH (Nat.cast_nonneg H) (by positivity)
    have h₂ := mul_le_mul (hqbound q hq) hden (Nat.cast_nonneg D) (by positivity)
    nlinarith only [h₁, h₂, hs, hn']
  · intro q r hq hr
    have hm := mul_le_mul (hqbound q hq) (hqbound r hr) (Nat.cast_nonneg r) (by positivity)
    nlinarith only [hm, hs, hn']

theorem scaleDenominatorMass (s : Finset ℕ) (n : ℕ) (c growth : ℝ)
    (h : c * growth ≤ ∑ q ∈ s, 1 / (q : ℝ)) :
    (c / 384) * (n : ℝ) * growth ≤ ∑ q ∈ s, (n : ℝ) / (384 * (q : ℝ)) := by
  calc
    _ = (n / 384 : ℝ) * (c * growth) := by ring
    _ ≤ (n / 384 : ℝ) * ∑ q ∈ s, 1 / (q : ℝ) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

end GoldbachSupport
end

section
open Filter
open scoped Topology

namespace GoldbachSupport

theorem primeMassFloor_of_density (D H : ℕ → ℕ) (growth : ℕ → ℝ)
    (hcuts : ∀ᶠ n : ℕ in atTop, (D n : ℝ) ≤ Real.sqrt n ∧ (H n : ℝ) ≤ Real.sqrt n)
    (d : ℝ) (hd : 0 < d)
    (hdens : ∀ᶠ n : ℕ in atTop, d * growth n ≤
      ∑ q ∈ (Finset.Ioc (D n) ⌊Real.sqrt n / 4⌋₊).filter Squarefree,
        1 / (q : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * (n : ℝ) * growth n ≤ intervalIntegral (fun t =>
        (publishedWideArcs (D n) (H n) n)ᶜ.indicator
          (fun u => ‖GoldbachL2Arithmetic.primeSum n u‖ ^ 2) t) 0 1 MeasureTheory.volume := by
  classical
  refine ⟨d/384, by positivity, Filter.eventually_atTop.1 ?_⟩
  filter_upwards [hdens, hcuts, primeAmplitudeBounds] with n hden ⟨hD, hH⟩ ⟨hn, hθ, hqlog⟩
  let L := ⌊Real.sqrt n / 4⌋₊
  let s := (Finset.Ioc (D n) L).filter Squarefree
  have hs {q : ℕ} (hq : q ∈ s) : (D n < q ∧ q ≤ L) ∧ Squarefree q :=
    by simpa [s] using hq
  obtain ⟨hend, hmask, hpair⟩ := denominatorWindowLimits n (D n) (H n) hn hD hH
  have hc : Continuous (GoldbachL2Arithmetic.primeSum n) := by
    unfold GoldbachL2Arithmetic.primeSum GoldbachL2Arithmetic.primeTerm GoldbachL2Arithmetic.E
    fun_prop
  apply (scaleDenominatorMass s n d (growth n) hden).trans
  exact assembleWindows s (D n) (H n) n _ hc (by omega)
    (fun _ hq => (hs hq).1.1)
    (fun q hq => hend q (hs hq).1.2)
    (fun q hq => hmask q (hs hq).1.2)
    (fun q hq r hr => hpair q r (hs hq).1.2 (hs hr).1.2)
    (fun q hq h hh => GoldbachL2Arithmetic.reduced_amplitude n q (by omega)
      (hs hq).2 hθ (hqlog q (hs hq).1.2) h hh.1 hh.2)

end GoldbachSupport
end

section
open Filter Finset
open scoped BigOperators

namespace GoldbachCount

noncomputable def sqrtCutoff (n : ℕ) : ℕ :=
  ⌊Real.sqrt n / (Nat.log 2 (n + 2) : ℝ) ^ 4⌋₊

private theorem square_le_geometric {m : ℕ} (hm : 16 ≤ m) : 32 * m^2 ≤ 2^m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ 2 k]
    have hquad := Nat.mul_le_mul_left k (show 3 ≤ k by omega)
    nlinarith only [ih, hquad, hk]

private theorem sqrtMaskNumerics (n : ℕ) (hn : 2^16 ≤ n) :
    16 ≤ Nat.log 2 (n+2) ∧ (Nat.log 2 (n+2) : ℝ) ≤ Real.sqrt n / 4 := by
  let l := Nat.log 2 (n+2)
  have hl : 16 ≤ l := Nat.le_log_of_pow_le (by decide) (by omega)
  have hl2 := square_le_geometric hl
  have hp : 2^l ≤ n+2 := Nat.pow_log_le_self _ (by omega)
  have h : 16*l^2 ≤ n := by omega
  have hh : (16:ℝ) * (l:ℝ)^2 ≤ n := by exact_mod_cast h
  have hroot := Real.le_sqrt_of_sq_le (show (4*(l:ℝ))^2 ≤ n by nlinarith only [hh])
  exact ⟨hl, by change (l:ℝ) ≤ Real.sqrt n / 4; linarith only [hroot]⟩

theorem sqrtMaskScales : ∀ᶠ n : ℕ in atTop,
    (sqrtCutoff n : ℝ) ≤ Real.sqrt n ∧
    (256 * sqrtCutoff n * (Nat.log 2 (n+2))^2 : ℕ) ≤ Real.sqrt n := by
  filter_upwards [eventually_ge_atTop (2^16 : ℕ)] with n hn
  let l := Nat.log 2 (n+2)
  let D := sqrtCutoff n
  have hl : (16:ℝ) ≤ l := by exact_mod_cast (sqrtMaskNumerics n hn).1
  have hlpos : (0:ℝ) < l := by linarith
  have hd : (D:ℝ) * (l:ℝ)^4 ≤ Real.sqrt n := by
    apply (le_div_iff₀ (by positivity)).mp
    exact Nat.floor_le (by positivity)
  have h256 : (256:ℝ) ≤ (l:ℝ)^2 := by
    exact (show (256:ℝ) = 16^2 by norm_num) ▸ pow_le_pow_left₀ (by norm_num) hl 2
  have h1 : (1:ℝ) ≤ (l:ℝ)^4 := one_le_pow₀ (by linarith)
  constructor
  · exact (le_mul_of_one_le_right (Nat.cast_nonneg D) h1).trans hd
  · push_cast
    change 256 * (D:ℝ) * (l:ℝ)^2 ≤ Real.sqrt n
    calc
      _ = (D:ℝ) * (l:ℝ)^2 * 256 := by ring
      _ ≤ (D:ℝ) * (l:ℝ)^2 * (l:ℝ)^2 :=
        mul_le_mul_of_nonneg_left h256 (by positivity)
      _ = (D:ℝ) * (l:ℝ)^4 := by ring
      _ ≤ _ := hd

theorem sqrtDenominatorMass :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * Real.log (Real.log n) ≤
        ∑ q ∈ (Ioc (sqrtCutoff n) ⌊Real.sqrt n / 4⌋₊).filter Squarefree, 1 / (q : ℝ) := by
  classical
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  refine ⟨1/(16*Real.log 8), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2^16 : ℕ)] with n hn
  let l := Nat.log 2 (n+2)
  let D := sqrtCutoff n
  let J := Nat.log 8 l
  obtain ⟨hle, hls⟩ := sqrtMaskNumerics n hn
  change 16 ≤ l at hle
  change (l:ℝ) ≤ Real.sqrt n / 4 at hls
  have hle' : (16:ℝ) ≤ l := by exact_mod_cast hle
  have hlpos : (0:ℝ) < l := by linarith only [hle']
  have hp : 8^J ≤ l := Nat.pow_log_le_self _ (by omega)
  have hp' : (8:ℝ)^J ≤ l := by exact_mod_cast hp
  have hJ : 1 ≤ J := Nat.le_log_of_pow_le (by decide) (by omega)
  have hnr : (1:ℝ) < n := by exact_mod_cast (show 1<n by omega)
  have hlogn : Real.log (n:ℝ) ≤ (l:ℝ)+1 := by
    have hp2 : n ≤ 2^(l+1) := by
      have hh := Nat.lt_pow_succ_log_self (by decide : 1<2) (n+2)
      change n + 2 < 2 ^ (l + 1) at hh
      omega
    have hz := Real.log_le_log (by linarith only [hnr] : (0:ℝ)<n)
      (by exact_mod_cast hp2 : (n:ℝ) ≤ (2:ℝ)^(l+1))
    rw [Real.log_pow] at hz
    push_cast at hz
    have h2 : Real.log 2 ≤ 1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      _ ≤ ((l:ℝ)+1)*Real.log 2 := hz
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left h2 (show 0 ≤ (l:ℝ)+1 by positivity)
  have hjlog : Real.log (Real.log n) ≤ ((J:ℝ)+1)*Real.log 8 := by
    have hle8 : l+1 ≤ 8^(J+1) := Nat.lt_pow_succ_log_self (by decide : 1<8) l
    have hle8' : (l:ℝ)+1 ≤ (8:ℝ)^(J+1) := by exact_mod_cast hle8
    have ht := Real.log_le_log (Real.log_pos hnr) (hlogn.trans hle8')
    simpa [Real.log_pow] using ht
  have hjfloor : 1 / (16 * Real.log 8) * Real.log (Real.log n) ≤ (J:ℝ)/8 := by
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    have hge : (1:ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith only [hjlog, mul_le_mul_of_nonneg_right hge h8.le]
  have hfit : 8^J * max D 1 ≤ ⌊Real.sqrt n / 4⌋₊ := by
    by_cases hzero : D = 0
    · simp only [hzero, Nat.zero_max, mul_one]
      exact Nat.le_floor (by exact_mod_cast hp'.trans hls)
    · rw [max_eq_left (show 1 ≤ D by omega)]
      apply Nat.le_floor
      push_cast
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).2
      have hd : (D:ℝ) * (l:ℝ)^4 ≤ Real.sqrt n := by
        apply (le_div_iff₀ (by positivity)).mp
        exact Nat.floor_le (by positivity)
      have h3 := pow_le_pow_left₀ (by norm_num : 0 ≤ (16:ℝ)) hle' 3
      have h4 : (l:ℝ)*4 ≤ (l:ℝ)^4 := by
        nlinarith only [mul_le_mul_of_nonneg_left
          (show (4:ℝ) ≤ (l:ℝ)^3 by linarith only [h3]) hlpos.le]
      calc
        _ ≤ (l:ℝ) * D * 4 := by gcongr
        _ ≤ (D:ℝ)*(l:ℝ)^4 := by nlinarith only [mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg D)]
        _ ≤ _ := hd
  refine (hjfloor.trans (mass_blocks (max D 1) J (by omega))).trans ?_
  apply sum_le_sum_of_subset_of_nonneg
  · exact filter_subset_filter _ (Ioc_subset_Ioc (le_max_left D _) hfit)
  · intro q _ _
    positivity

end GoldbachCount
end

end Conjectures.Goldbach.SqrtArcSecondMomentFloor

open Conjectures.Goldbach.SqrtArcSecondMomentFloor in
/-- Exterior second moment for the square-root cutoff divided by the fourth power of the binary logarithm. -/
theorem Conjectures.Goldbach.SqrtArcSecondMomentFloor :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₂ := fun n : ℕ => ⌊Real.sqrt (n : ℝ) / ((Nat.log 2 (n + 2) : ℝ) ^ 4)⌋₊; let sqrtArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q₂ n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ ((256 * Q₂ n * Q n : ℕ) : ℝ) / ((q : ℝ) * (n : ℝ))}; ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * (n : ℝ) * Real.log (Real.log (n : ℝ)) ≤ intervalIntegral (fun t => (sqrtArcs n)ᶜ.indicator (fun u => ‖S n w u‖ ^ 2) t) (0 : ℝ) 1 MeasureTheory.volume := by
  let D := GoldbachCount.sqrtCutoff
  let H := fun n : ℕ => 256 * D n * (Nat.log 2 (n+2))^2
  obtain ⟨d, hd, hm⟩ := GoldbachCount.sqrtDenominatorMass
  simpa only [D, H, GoldbachCount.sqrtCutoff, GoldbachL2Arithmetic.primeSum_eq_catalogue,
    GoldbachL2Arithmetic.E, GoldbachSupport.publishedWideArcs] using
    GoldbachSupport.primeMassFloor_of_density D H (fun n => Real.log (Real.log n))
      GoldbachCount.sqrtMaskScales d hd hm
