import Conjectures.Goldbach.SqrtArcSecondMomentFloor

/-!
The reduced-residue amplitude bound yields the fourth moment by a second application
of Cauchy–Schwarz. The disjoint window argument adapts the corresponding second
moment proof from SqrtArcSecondMomentFloor, Goldbach PR #3727 (Apache-2.0).
-/

open Set MeasureTheory Filter
open scoped BigOperators Interval Topology

namespace GoldbachDenominatorCutoffFourthMoment
open Conjectures.Goldbach.SqrtArcSecondMomentFloor
open GoldbachSupport

private theorem residueFourthEnergy {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    {n : ℝ} {q : ℕ} (hn : 0 ≤ n) (hq : 0 < q) (hcard : s.card ≤ q)
    (hamp : n / 8 ≤ ‖∑ a ∈ s, z a‖) :
    n ^ 4 / (4096 * (q : ℝ) ^ 3) ≤ ∑ a ∈ s, ‖z a‖ ^ 4 := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have h2 := residueEnergy s z hn hq hcard hamp
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ n ^ 2 / (64 * (q : ℝ))) h2 2
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := fun a => ‖z a‖ ^ 2)
  simp only [← pow_mul, Nat.reduceMul] at hcs
  have hc : (s.card : ℝ) ≤ q := by exact_mod_cast hcard
  have hpos : 0 ≤ ∑ a ∈ s, ‖z a‖ ^ 4 := Finset.sum_nonneg fun a _ => by positivity
  have hm := hsq.trans (hcs.trans (mul_le_mul_of_nonneg_right hc hpos))
  calc
    _ = (n ^ 2 / (64 * (q : ℝ))) ^ 2 / (q : ℝ) := by
      field_simp
      ring
    _ ≤ _ := (div_le_iff₀ hqR).2 (by simpa only [mul_comm] using hm)

private theorem residueWindowFourthEnergy {ι : Type*} (s : Finset ι) (z : ι → ℝ → ℂ)
    {n : ℝ} {q : ℕ} (hn : 0 < n) (hq : 0 < q) (hcard : s.card ≤ q)
    (hz : ∀ a ∈ s, Continuous (z a))
    (hamp : ∀ h ∈ Set.Icc 0 (1 / (6 * n)), n / 8 ≤ ‖∑ a ∈ s, z a h‖) :
    n ^ 3 / (24576 * (q : ℝ) ^ 3) ≤
      ∑ a ∈ s, ∫ h in (0 : ℝ)..1 / (6 * n), ‖z a h‖ ^ 4 := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hcont : Continuous (fun h => ∑ a ∈ s, ‖z a h‖ ^ 4) :=
    continuous_finsetSum _ fun a ha => (hz a ha).norm.pow 4
  calc
    n ^ 3 / (24576 * (q : ℝ) ^ 3) =
        ∫ _ in (0 : ℝ)..1 / (6 * n), n ^ 4 / (4096 * (q : ℝ) ^ 3) := by
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      field_simp
      ring
    _ ≤ ∫ h in (0 : ℝ)..1 / (6 * n), ∑ a ∈ s, ‖z a h‖ ^ 4 := by
      apply intervalIntegral.integral_mono_on (by positivity) intervalIntegrable_const
        (hcont.intervalIntegrable ..)
      exact fun h hh => residueFourthEnergy s (fun a => z a h) hn.le hq hcard (hamp h hh)
    _ = _ := intervalIntegral.integral_finsetSum fun a ha =>
      ((hz a ha).norm.pow 4).intervalIntegrable ..

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
private theorem assembleFourthWindows (s : Finset ℕ) (D H n : ℕ) (S : ℝ → ℂ) (hS : Continuous S)
    (hn : 0 < n)
    (hden : ∀ q ∈ s, D < q)
    (hend : ∀ q ∈ s, (q : ℝ) ≤ 6 * n)
    (hmask : ∀ q ∈ s, (q : ℝ) * H + (q : ℝ) * D / 6 < n)
    (hpair : ∀ q ∈ s, ∀ r ∈ s, (q : ℝ) * r < 6 * n)
    (hamp : ∀ q ∈ s, ∀ h ∈ Icc (0 : ℝ) (1 / (6 * n)),
      (n : ℝ) / 8 ≤ ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          S ((a : ℝ) / q + h)‖) :
    ∑ q ∈ s, (n : ℝ) ^ 3 / (24576 * (q : ℝ) ^ 3) ≤
      ∫ t in (0 : ℝ)..1, (publishedWideArcs D H n)ᶜ.indicator (fun x => ‖S x‖ ^ 4) t := by
  classical
  let A := fun q : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q)
  let indices := s.sigma A
  let w : ℝ := 1 / (6 * (n : ℝ))
  let f : ℝ → ℝ := fun t => ‖S t‖ ^ 4
  let c : (Σ _ : ℕ, ℕ) → ℝ := fun i => (i.2 : ℝ) / i.1
  let W := fun i => Ioc (c i) (c i + w)
  let target := Ioc (0 : ℝ) 1 ∩ (publishedWideArcs D H n)ᶜ
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hc : Continuous f := hS.norm.pow 4
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
    have hout := GoldbachSupport.outsideWideArcs i.2 i.1 D H n (t - c i) hcop
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
    have h := GoldbachSupport.deepArcWindowsDisjoint i.2 j.2 i.1 j.1 n (t - c i) (t - c j)
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
    ∑ q ∈ s, (n : ℝ) ^ 3 / (24576 * (q : ℝ) ^ 3) ≤
        ∑ q ∈ s, ∑ a ∈ A q, ∫ h in (0 : ℝ)..w, f ((a : ℝ) / q + h) := by
      apply Finset.sum_le_sum
      intro q hq
      have hcard : (A q).card ≤ q :=
        (Finset.card_filter_le ..).trans_eq (Finset.card_range q)
      exact residueWindowFourthEnergy (A q) (fun a h => S ((a : ℝ) / q + h))
        hn' (hqpos hq) hcard (fun a _ => hS.comp (continuous_const.add continuous_id)) (hamp q hq)
    _ = ∑ i ∈ indices, ∫ h in (0 : ℝ)..w, f (c i + h) :=
      Finset.sum_sigma' s A _
    _ = ∑ i ∈ indices, ∫ x in W i, f x := Finset.sum_congr rfl fun i _ => hshift i
    _ = ∫ x in ⋃ i ∈ indices, W i, f x :=
      (integral_biUnion_finset indices (fun _ _ => measurableSet_Ioc) hdisj (fun _ _ => hint)).symm
    _ ≤ ∫ x in target, f x := by
      apply setIntegral_mono_set htarget (Filter.Eventually.of_forall fun x => by positivity)
      exact Filter.Eventually.of_forall fun _ hx => by
        rcases Set.mem_iUnion₂.mp hx with ⟨i,hi,ht⟩
        exact hsubset hi ht
    _ = ∫ t in (0 : ℝ)..1, (publishedWideArcs D H n)ᶜ.indicator (fun x => ‖S x‖ ^ 4) t := by
      rw [intervalIntegral.integral_of_le (by norm_num), setIntegral_indicator (measurable_publishedWideArcs ..).compl]


private theorem fourthDenominatorMass (n D : ℕ) (hD : 0 < D) :
    (n : ℝ) ^ 3 / (12582912 * (D : ℝ) ^ 2) ≤
      ∑ q ∈ (Finset.Ioc D (8 * D)).filter Squarefree,
        (n : ℝ) ^ 3 / (24576 * (q : ℝ) ^ 3) := by
  classical
  let s := (Finset.Ioc D (8 * D)).filter Squarefree
  let c : ℝ := (n : ℝ) ^ 3 / (24576 * (64 * (D : ℝ) ^ 2))
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast hD
  have hm : (1 : ℝ) / 8 ≤ ∑ q ∈ s, 1 / (q : ℝ) := by
    simpa [s, GoldbachCount.mass] using GoldbachCount.mass_blocks D 1 hD
  calc
    _ = c * (1 / 8) := by dsimp [c]; ring
    _ ≤ c * ∑ q ∈ s, 1 / (q : ℝ) := mul_le_mul_of_nonneg_left hm (by dsimp [c]; positivity)
    _ = ∑ q ∈ s, c * (1 / (q : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      have hi := Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1
      have hqpos : 0 < (q : ℝ) := by exact_mod_cast hD.trans hi.1
      have hqle : (q : ℝ) ≤ 8 * (D : ℝ) := by exact_mod_cast hi.2
      have hsquare : (q : ℝ) ^ 2 ≤ 64 * (D : ℝ) ^ 2 := by
        nlinarith [pow_le_pow_left₀ hqpos.le hqle 2]
      have hden : 24576 * (q : ℝ) ^ 3 ≤ 24576 * (64 * (D : ℝ) ^ 2) * (q : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_right hsquare hqpos.le]
      calc
        _ = (n : ℝ) ^ 3 / (24576 * (64 * (D : ℝ) ^ 2) * (q : ℝ)) := by
          dsimp [c]
          field_simp
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hden

theorem integral_bound :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ D H : ℕ, 0 < D →
      32 * (D : ℝ) ≤ Real.sqrt n → (H : ℝ) ≤ Real.sqrt n →
      (n : ℝ) ^ 3 ≤ 12582912 * (D : ℝ) ^ 2 *
        intervalIntegral (fun t => (publishedWideArcs D H n)ᶜ.indicator
          (fun u => ‖GoldbachL2Arithmetic.primeSum n u‖ ^ 4) t) 0 1 MeasureTheory.volume := by
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 primeAmplitudeBounds
  refine ⟨N, ?_⟩
  intro n hn D H hD hDlimit hH
  obtain ⟨hn2, hθ, hqlog⟩ := hN n hn
  let s := (Finset.Ioc D (8 * D)).filter Squarefree
  have hs {q : ℕ} (hq : q ∈ s) : (D < q ∧ q ≤ 8 * D) ∧ Squarefree q := by
    simpa [s] using hq
  have hqfloor {q : ℕ} (hq : q ∈ s) : q ≤ ⌊Real.sqrt n / 4⌋₊ := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ Real.sqrt n / 4)).2
    have hq8 : (q : ℝ) ≤ 8 * (D : ℝ) := by exact_mod_cast (hs hq).1.2
    linarith
  have hDnonneg : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hDlimit' : (D : ℝ) ≤ Real.sqrt n := by linarith only [hDlimit, hDnonneg]
  obtain ⟨hend, hmask, hpair⟩ := denominatorWindowLimits n D H hn2 hDlimit' hH
  have hc : Continuous (GoldbachL2Arithmetic.primeSum n) := by
    unfold GoldbachL2Arithmetic.primeSum GoldbachL2Arithmetic.primeTerm GoldbachL2Arithmetic.E
    fun_prop
  have hwindows := assembleFourthWindows s D H n _ hc (by omega)
    (fun _ hq => (hs hq).1.1)
    (fun q hq => hend q (hqfloor hq))
    (fun q hq => hmask q (hqfloor hq))
    (fun q hq r hr => hpair q r (hqfloor hq) (hqfloor hr))
    (fun q hq h hh => GoldbachL2Arithmetic.reduced_amplitude n q (by omega)
      (hs hq).2 hθ (hqlog q (hqfloor hq)) h hh.1 hh.2)
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast hD
  have result := (div_le_iff₀ (by positivity : 0 < 12582912 * (D : ℝ) ^ 2)).1
    ((fourthDenominatorMass n D hD).trans hwindows)
  simpa only [mul_comm] using result

end GoldbachDenominatorCutoffFourthMoment

open Conjectures.Goldbach.SqrtArcSecondMomentFloor in
theorem Conjectures.Goldbach.DenominatorCutoffFourthMomentFloor :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S := fun (n : ℕ) (t : ℝ) => Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * E ((k : ℝ) * t)); let arcs := fun (n D H : ℕ) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n)}; ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ D H : ℕ, 0 < D → 32 * (D : ℝ) ≤ Real.sqrt n → (H : ℝ) ≤ Real.sqrt n → (n : ℝ) ^ 3 ≤ 12582912 * (D : ℝ) ^ 2 * intervalIntegral (fun t => (arcs n D H)ᶜ.indicator (fun u => ‖S n u‖ ^ 4) t) (0 : ℝ) 1 MeasureTheory.volume := by
  simpa only [GoldbachL2Arithmetic.primeSum_eq_catalogue, GoldbachL2Arithmetic.E,
    GoldbachSupport.publishedWideArcs] using GoldbachDenominatorCutoffFourthMoment.integral_bound
