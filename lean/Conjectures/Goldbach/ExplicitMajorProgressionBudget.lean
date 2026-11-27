import Mathlib

open Finset MeasureTheory Real Complex Set
open scoped BigOperators Interval
open scoped ComplexConjugate

namespace Conjectures.Goldbach.ExplicitMajorProgressionBudget_aux

noncomputable section

def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
def Q (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2
def width (n q : ℕ) : ℝ := (Q n : ℝ) / ((q : ℝ) * n)
def K (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ Finset.range (n + 1), E ((k : ℝ) * β)
def ram (q h : ℕ) : ℂ := ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), E ((h : ℝ) * a / q)
def kernelMass (n : ℕ) (b : ℝ) : ℝ := intervalIntegral (fun β => ‖K n β‖ ^ 2) (-b) b MeasureTheory.volume
def modeledMajor (n : ℕ) : ℂ := ∑ q ∈ Finset.Icc 1 (Q n), ((ram q 1 / (q.totient : ℂ)) ^ 2 * (starRingEnd ℂ) (ram q n)) * (kernelMass n (width n q) : ℂ)
def w (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0
def S (n : ℕ) (t : ℝ) : ℂ := ∑ k ∈ Finset.range (n + 1), (w k : ℂ) * E ((k : ℝ) * t)
def center (q a : ℕ) : ℝ := (a : ℝ) / q
def arcs (n : ℕ) : Set ℝ := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - center q a| ≤ width n q}
def major (n : ℕ) : ℂ := intervalIntegral ((arcs n).indicator (fun t => (S n t) ^ 2 * E (-(n : ℝ) * t))) (0 : ℝ) 1 MeasureTheory.volume
def classError (m q b : ℕ) : ℝ := (∑ k ∈ (Finset.range m).filter (fun k => k % q = b), w k) - (if Nat.Coprime b q then (m : ℝ) / q.totient else 0)
def discrepancy (n q a : ℕ) : ℝ := (Finset.range (n + 2)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ (n + 1))⟩ (fun m => ‖∑ b ∈ Finset.range q, (classError m q b : ℂ) * E ((b : ℝ) * center q a)‖)
def unitMean (q a : ℕ) : ℂ := (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), E ((r : ℝ) * center q a)) / (q.totient : ℂ)
def leftEnd (n q a : ℕ) : ℝ := max (center q a - width n q) 0 - center q a
def rightEnd (n q a : ℕ) : ℝ := min (center q a + width n q) 1 - center q a
def amplified (n : ℕ) (D β : ℝ) : ℝ := D * (1 + 2 * Real.pi * n * |β|)
def prefixCost (n q a : ℕ) (D β : ℝ) : ℝ := amplified n D β * (2 * ‖unitMean q a * K n β‖ + amplified n D β)
def progressionBudget (n : ℕ) : ℝ := ∑ q ∈ Finset.Icc 1 (Q n), ∑ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q), intervalIntegral (prefixCost n q a (discrepancy n q a)) (leftEnd n q a) (rightEnd n q a) MeasureTheory.volume

def phase (x : ℝ) : ℂ := E x
def primeWeight (k : ℕ) : ℝ := w k
def primeSum (n : ℕ) (t : ℝ) : ℂ := S n t
def integrand (n : ℕ) (t : ℝ) : ℂ := (S n t) ^ 2 * E (-(n : ℝ) * t)
def kernel (n : ℕ) (β : ℝ) : ℂ := K n β
def numerators (q : ℕ) : Finset ℕ := (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q)
def window (n q a : ℕ) : Set ℝ := Set.Icc (center q a - width n q) (center q a + width n q)
def centerErrorTerm (r : ℝ) (A : ℂ) (k : ℕ) : ℂ := (primeWeight k : ℂ) * phase ((k : ℝ) * r) - A
def prefixError (n : ℕ) (r : ℝ) (A : ℂ) : ℝ :=
  (Finset.range (n + 2)).sup' ⟨0, by simp⟩ (fun m => ‖∑ k ∈ Finset.range m, centerErrorTerm r A k‖)
def classMass (m q b : ℕ) : ℝ := ∑ k ∈ (Finset.range m).filter (fun k => k % q = b), primeWeight k
def modelPoint (n q a : ℕ) (β : ℝ) : ℂ :=
  (unitMean q a * kernel n β) ^ 2 * phase (-(n : ℝ) * (center q a + β))
def modelPiece (n q a : ℕ) : ℂ :=
  (unitMean q a ^ 2 * phase (-(n : ℝ) * center q a)) *
    ((∫ β in leftEnd n q a..rightEnd n q a, ‖kernel n β‖ ^ 2 : ℝ) : ℂ)
def actualPiece (n q a : ℕ) : ℂ :=
  ∫ β in leftEnd n q a..rightEnd n q a, integrand n (center q a + β)
def coefficient (q n : ℕ) : ℂ :=
  (ram q 1 / (q.totient : ℂ)) ^ 2 * (starRingEnd ℂ) (ram q n)
def modeledContribution (n : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 (Q n), coefficient q n * (kernelMass n (width n q) : ℂ)

private noncomputable instance unitsFintype (q : ℕ) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase E
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

private theorem continuous_integrand (n : ℕ) : Continuous (integrand n) := by
  unfold integrand S E
  fun_prop

private theorem primeWeight_nonneg (k : ℕ) : 0 ≤ primeWeight k := by
  unfold primeWeight w
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_le)
  · exact le_rfl

private theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

private theorem phase_step (k : ℕ) (β : ℝ) :
    ‖phase (((k + 1 : ℕ) : ℝ) * β) - phase ((k : ℝ) * β)‖ ≤ 2 * Real.pi * |β| := by
  have shift : ((k + 1 : ℕ) : ℝ) * β = k * β + β := by push_cast; ring
  rw [shift, phase_add, ← mul_sub_one, norm_mul, norm_phase, one_mul]
  unfold phase E
  rw [mul_comm _ Complex.I]
  calc
    _ ≤ ‖2 * Real.pi * β‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

theorem shifted_sum_error (n : ℕ) (r β : ℝ) (A : ℂ) :
    ‖primeSum n (r + β) - A * kernel n β‖ ≤
      prefixError n r A * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by
  let g := centerErrorTerm r A
  let v := fun k : ℕ => phase ((k : ℝ) * β)
  let D := prefixError n r A
  have hD : 0 ≤ D := (norm_nonneg _).trans (Finset.le_sup'
    (fun m => ‖∑ k ∈ Finset.range m, centerErrorTerm r A k‖)
    (Finset.mem_range.mpr (Nat.zero_lt_succ (n + 1))))
  have expand : primeSum n (r + β) - A * kernel n β =
      ∑ k ∈ Finset.range (n + 1), v k * g k := by
    unfold primeSum kernel S K
    rw [mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp [v, g, centerErrorTerm, primeWeight]
    have hp : E ((k : ℝ) * (r + β)) = E ((k : ℝ) * r) * E ((k : ℝ) * β) := by
      unfold E
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hp]
    simp only [phase]
    ring
  have habel := Finset.sum_range_by_parts (M := ℂ) v g (n + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at habel
  have hfirst : ‖v n * ∑ k ∈ Finset.range (n + 1), g k‖ ≤ D := by
    rw [norm_mul, show ‖v n‖ = 1 from norm_phase _, one_mul]
    exact Finset.le_sup' (fun m => ‖∑ k ∈ Finset.range m, centerErrorTerm r A k‖)
      (Finset.mem_range.mpr (by omega))
  have htail : ‖∑ i ∈ Finset.range n,
      (v (i + 1) - v i) * ∑ k ∈ Finset.range (i + 1), g k‖ ≤
      (n : ℝ) * (2 * Real.pi * |β| * D) := by
    calc
      _ ≤ ∑ i ∈ Finset.range n,
          ‖(v (i + 1) - v i) * ∑ k ∈ Finset.range (i + 1), g k‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range n, 2 * Real.pi * |β| * D := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul]
        exact mul_le_mul (phase_step i β)
          (Finset.le_sup' (fun m => ‖∑ k ∈ Finset.range m, centerErrorTerm r A k‖)
            (Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega)))
          (norm_nonneg _) (by positivity)
      _ = _ := by simp
  rw [expand, habel]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ D + n * (2 * Real.pi * |β| * D) := add_le_add hfirst htail
    _ = _ := by dsimp [D]; ring

private theorem phase_modulo {q : ℕ} (hq : 0 < q) (k a : ℕ) :
    phase ((k : ℝ) * ((a : ℝ) / q)) =
      phase (((k % q : ℕ) : ℝ) * ((a : ℝ) / q)) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hk : (k : ℝ) = ((k % q : ℕ) : ℝ) + q * ((k / q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div k q).symm
  have harg : (k : ℝ) * ((a : ℝ) / q) =
      ((k % q : ℕ) : ℝ) * ((a : ℝ) / q) + (((k / q * a : ℕ) : ℝ)) := by
    push_cast
    nth_rw 1 [hk]
    field_simp
  rw [harg, phase_add]
  have hnat : phase (((k / q * a : ℕ) : ℝ)) = 1 := by
    unfold phase E
    convert Complex.exp_nat_mul_two_pi_mul_I (k / q * a) using 2 <;> push_cast <;> ring
  rw [hnat, mul_one]

private theorem center_prefix_eq {q : ℕ} (hq : 0 < q) (a m : ℕ) :
    ∑ k ∈ Finset.range m, centerErrorTerm ((a : ℝ) / q) (unitMean q a) k =
      ∑ b ∈ Finset.range q, (classError m q b : ℂ) *
        phase ((b : ℝ) * ((a : ℝ) / q)) := by
  let e := fun k : ℕ => phase ((k : ℝ) * ((a : ℝ) / q))
  have masses : (∑ k ∈ Finset.range m, (primeWeight k : ℂ) * e k) =
      ∑ b ∈ Finset.range q, (classMass m q b : ℂ) * e b := by
    symm
    calc
      _ = ∑ b ∈ Finset.range q, ∑ k ∈ (Finset.range m).filter (fun k => k % q = b),
          (primeWeight k : ℂ) * e k := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [classMass, Complex.ofReal_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k hk => ?_
        have he : e k = e b := by
          dsimp [e]
          rw [phase_modulo hq k a, (Finset.mem_filter.mp hk).2]
        rw [he]
      _ = _ := Finset.sum_fiberwise_of_maps_to
        (fun k _ => Finset.mem_range.mpr (Nat.mod_lt k hq)) _
  have model : (m : ℂ) * unitMean q a =
      ∑ b ∈ Finset.range q,
        (↑(if b.Coprime q then (m : ℝ) / q.totient else 0) : ℂ) * e b := by
    calc
      _ = ((m : ℂ) / q.totient) *
          ∑ b ∈ (Finset.range q).filter (fun b => b.Coprime q), e b := by
        have hsum :
            (∑ b ∈ (Finset.range q).filter (fun b => b.Coprime q),
              E ((b : ℝ) * ((a : ℝ) / q))) =
            ∑ b ∈ (Finset.range q).filter (fun b => b.Coprime q),
              E ((b : ℝ) * (a : ℝ) / q) := by
          apply Finset.sum_congr rfl
          intro b hb
          congr 1
          ring
        unfold unitMean
        dsimp [e, center, phase]
        rw [hsum]
        ring
      _ = _ := by
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases h : b.Coprime q
        · rw [ite_eq_left h, ite_eq_left h, Complex.ofReal_div,
            Complex.ofReal_natCast, Complex.ofReal_natCast]
        · rw [ite_eq_right h, ite_eq_right h, Complex.ofReal_zero, zero_mul]
  change (∑ k ∈ Finset.range m, ((primeWeight k : ℂ) * e k - unitMean q a)) = _
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    masses, model, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← sub_mul, classError, Complex.ofReal_sub]
  simp [classMass, primeWeight, w, e, phase]

theorem discrepancy_eq_prefixError (n q a : ℕ) (hq : 0 < q) :
    discrepancy n q a = prefixError n (center q a) (unitMean q a) := by
  unfold discrepancy prefixError
  apply Finset.sup'_congr
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ (n + 1))⟩ rfl
  intro m hm
  apply congrArg norm
  simpa [center, phase] using (center_prefix_eq hq a m).symm

private theorem discrepancy_nonneg (n q a : ℕ) : 0 ≤ discrepancy n q a := by
  unfold discrepancy
  exact (norm_nonneg _).trans (Finset.le_sup'
    (fun m => ‖∑ b ∈ Finset.range q,
      (classError m q b : ℂ) * E ((b : ℝ) * center q a)‖)
    (Finset.mem_range.mpr (Nat.zero_lt_succ (n + 1))))

private theorem pointwise_error_le_cost {n q a : ℕ} (hq : 0 < q) (β : ℝ) :
    ‖integrand n (center q a + β) - modelPoint n q a β‖ ≤
      prefixCost n q a (discrepancy n q a) β := by
  let D := discrepancy n q a
  have hD : 0 ≤ D := discrepancy_nonneg n q a
  have hshift : ‖S n (center q a + β) - unitMean q a * K n β‖ ≤ amplified n D β := by
    have h := shifted_sum_error n (center q a) β (unitMean q a)
    dsimp [D] at h ⊢
    rw [← discrepancy_eq_prefixError n q a hq] at h
    simpa [amplified, primeSum, kernel, S, K] using h
  have hamp : 0 ≤ amplified n D β := by
    unfold amplified
    positivity
  have hplus : ‖S n (center q a + β) + unitMean q a * K n β‖ ≤
      2 * ‖unitMean q a * K n β‖ + amplified n D β := by
    let B := unitMean q a * K n β
    have heq : S n (center q a + β) + B =
        (S n (center q a + β) - B) + (B + B) := by ring
    rw [heq]
    calc
      _ ≤ ‖S n (center q a + β) - B‖ + ‖B + B‖ := norm_add_le _ _
      _ ≤ amplified n D β + 2 * ‖B‖ := by
        apply add_le_add hshift
        calc
          ‖B + B‖ ≤ ‖B‖ + ‖B‖ := norm_add_le _ _
          _ = 2 * ‖B‖ := by ring
      _ = _ := by ring
  unfold integrand modelPoint prefixCost
  change ‖(S n (center q a + β)) ^ 2 * E (-(n : ℝ) * (center q a + β)) -
      (unitMean q a * K n β) ^ 2 * E (-(n : ℝ) * (center q a + β))‖ ≤ _
  have hEn : ‖E (-(n : ℝ) * (center q a + β))‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  rw [← sub_mul, norm_mul, hEn, mul_one,
    show (S n (center q a + β)) ^ 2 - (unitMean q a * K n β) ^ 2 =
      (S n (center q a + β) - unitMean q a * K n β) *
        (S n (center q a + β) + unitMean q a * K n β) by ring,
    norm_mul]
  simpa using mul_le_mul hshift hplus (norm_nonneg _) hamp

private theorem quartic_growth (k : ℕ) (hk : 19 ≤ k) :
    2 * k ^ 4 + 3 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hkR : (19 : ℝ) ≤ k := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < k := by linarith
    have hquarticR : ((k : ℝ) + 1) ^ 4 ≤ 2 * (k : ℝ) ^ 4 := by
      have hquot : ((k : ℝ) + 1) / (k : ℝ) ≤ 11 / 10 := by
        rw [div_le_iff₀ hkpos]
        linarith
      have hpow : (((k : ℝ) + 1) / (k : ℝ)) ^ 4 ≤ ((11 : ℝ) / 10) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hquot 4
      have htwo : (((11 : ℝ) / 10) ^ 4) ≤ 2 := by norm_num
      have hkey : (((k : ℝ) + 1) ^ 4) / (k : ℝ) ^ 4 ≤ 2 := by
        rw [← div_pow]
        exact hpow.trans htwo
      have hmul := mul_le_mul_of_nonneg_right hkey (pow_nonneg hkpos.le 4)
      rwa [div_mul_cancel₀ _ (pow_ne_zero 4 hkpos.ne')] at hmul
    have hquartic : (k + 1) ^ 4 ≤ 2 * k ^ 4 := by
      exact_mod_cast hquarticR
    calc
      2 * (k + 1) ^ 4 + 3 ≤ 4 * k ^ 4 + 3 := by omega
      _ ≤ 2 * (2 * k ^ 4 + 3) := by omega
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring

private theorem cutoff_separated (n : ℕ) (hn : 1000000 ≤ n) :
    2 * (Q n) ^ 2 < n := by
  let k := Nat.log 2 (n + 2)
  have hk : 19 ≤ k := by
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    have hpow : (2 : ℕ) ^ 19 = 524288 := by norm_num
    omega
  have hgrowth : 2 * k ^ 4 + 3 ≤ 2 ^ k := quartic_growth k hk
  have hlogpow : 2 ^ k ≤ n + 2 := by
    exact Nat.pow_log_le_self 2 (by omega)
  have hbudget : 2 * (k ^ 2) ^ 2 + 3 ≤ n + 2 := by
    calc
      2 * (k ^ 2) ^ 2 + 3 = 2 * k ^ 4 + 3 := by ring
      _ ≤ 2 ^ k := hgrowth
      _ ≤ n + 2 := hlogpow
  dsimp [Q, k] at hbudget ⊢
  omega

private theorem width_nonneg (n q : ℕ) : 0 ≤ width n q := by
  unfold width
  positivity

private theorem center_in_unit {q a : ℕ} (hq : 0 < q) (ha : a ≤ q) :
    0 ≤ center q a ∧ center q a ≤ 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  exact ⟨by unfold center; positivity, (div_le_one hq').mpr (by exact_mod_cast ha)⟩

private theorem mem_window (n q a : ℕ) (t : ℝ) :
    t ∈ window n q a ↔ |t - center q a| ≤ width n q := by
  change _ ∧ _ ↔ _
  rw [abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

private theorem clipped_order {n q a : ℕ} (hq : 0 < q) (ha : a ≤ q) :
    -width n q ≤ leftEnd n q a ∧ leftEnd n q a ≤ rightEnd n q a ∧
      rightEnd n q a ≤ width n q := by
  obtain ⟨h₁,h₂⟩ := center_in_unit hq ha
  have hw := width_nonneg n q
  unfold leftEnd rightEnd
  constructor
  · linarith [le_max_left (center q a - width n q) 0]
  constructor
  · apply sub_le_sub_right
    exact max_le (le_min (by linarith) (by linarith)) (le_min (by linarith) zero_le_one)
  · linarith [min_le_left (center q a + width n q) 1]

private theorem indicator_clipped {n q a : ℕ} (hq : 0 < q) (ha : a ≤ q) (F : ℝ → ℂ) :
    (∫ t in (0 : ℝ)..1, (window n q a).indicator F t) =
      ∫ β in leftEnd n q a..rightEnd n q a, F (center q a + β) := by
  rw [intervalIntegral.integral_comp_add_left]
  have h := (clipped_order (n := n) hq ha).2.1
  unfold leftEnd rightEnd at h ⊢
  simp only [add_sub_cancel]
  rw [intervalIntegral.integral_of_le zero_le_one, ← MeasureTheory.integral_Icc_eq_integral_Ioc,
    window, MeasureTheory.integral_indicator measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc, Set.Icc_inter_Icc,
    intervalIntegral.integral_of_le
      (by linarith : max (center q a - width n q) 0 ≤ min (center q a + width n q) 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

private theorem cross_eq_of_overlap {n q r a b : ℕ} {t : ℝ}
    (hn : 2 * (Q n) ^ 2 < n)
    (hq : q ∈ Finset.Icc 1 (Q n)) (hr : r ∈ Finset.Icc 1 (Q n))
    (ha : t ∈ window n q a) (hb : t ∈ window n r b) : a * r = b * q := by
  obtain ⟨hq₁,hqQ⟩ := Finset.mem_Icc.mp hq
  obtain ⟨hr₁,hrQ⟩ := Finset.mem_Icc.mp hr
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq₁
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr₁
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let QQ := Q n
  have hsmall : QQ * r + QQ * q < n := by
    nlinarith only [hn, Nat.mul_le_mul_left QQ hrQ, Nat.mul_le_mul_left QQ hqQ]
  have hradii : (QQ : ℝ) / (q * n) + QQ / (r * n) < 1 / (q * r) := by
    calc
      _ = ((QQ : ℝ) * r + QQ * q) / (q * r * n) := by field_simp
      _ < (n : ℝ) / (q * r * n) :=
        (div_lt_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hsmall)
      _ = _ := by field_simp
  by_contra hne
  have hsep : 1 / ((q : ℝ) * r) ≤ |(a : ℝ) / q - b / r| := by
    rw [show (a : ℝ) / q - b / r = (a * r - b * q) / (q * r) by field_simp,
      abs_div, abs_of_pos (mul_pos hqr hrr)]
    apply (div_le_div_iff_of_pos_right (mul_pos hqr hrr)).mpr
    rcases lt_or_gt_of_ne hne with hab | hba
    · have hgap : (a : ℝ) * r + 1 ≤ b * q := by
        exact_mod_cast Nat.succ_le_of_lt hab
      linarith [neg_le_abs ((a : ℝ) * r - b * q)]
    · have hgap : (b : ℝ) * q + 1 ≤ a * r := by
        exact_mod_cast Nat.succ_le_of_lt hba
      linarith [le_abs_self ((a : ℝ) * r - b * q)]
  have ht := abs_sub_le ((a : ℝ) / q) t ((b : ℝ) / r)
  rw [abs_sub_comm ((a : ℝ) / q) t] at ht
  have h₁ := (mem_window n q a t).mp ha
  have h₂ := (mem_window n r b t).mp hb
  change |t - (a : ℝ) / q| ≤ (QQ : ℝ) / (q * n) at h₁
  change |t - (b : ℝ) / r| ≤ (QQ : ℝ) / (r * n) at h₂
  dsimp [QQ] at hradii
  linarith

private theorem center_unique {n q r a b : ℕ} {t : ℝ}
    (hn : 2 * (Q n) ^ 2 < n)
    (hq : q ∈ Finset.Icc 1 (Q n)) (hr : r ∈ Finset.Icc 1 (Q n))
    (ha : a ∈ numerators q) (hb : b ∈ numerators r)
    (hta : t ∈ window n q a) (htb : t ∈ window n r b) : q = r ∧ a = b := by
  have he := cross_eq_of_overlap hn hq hr hta htb
  have hc := (Finset.mem_filter.mp ha).2
  have hc' := (Finset.mem_filter.mp hb).2
  have hqr : q ∣ r := hc.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hrq : r ∣ q := hc'.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hqr hrq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (Finset.mem_Icc.mp hq).1 he⟩

private theorem arc_indicator_sum {n : ℕ} (hn : 2 * (Q n) ^ 2 < n) (t : ℝ) :
    (arcs n).indicator (integrand n) t =
      ∑ q ∈ Finset.Icc 1 (Q n), ∑ a ∈ numerators q,
        (window n q a).indicator (integrand n) t := by
  classical
  by_cases ht : t ∈ arcs n
  · rw [Set.indicator_of_mem ht]
    obtain ⟨q,a,hq₁,hqQ,ha,hc,habs⟩ := ht
    have hq := Finset.mem_Icc.mpr ⟨hq₁,hqQ⟩
    have ha' : a ∈ numerators q :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hc⟩
    have hw := (mem_window n q a t).mpr habs
    symm
    calc
      _ = ∑ b ∈ numerators q, (window n q b).indicator (integrand n) t := by
        apply Finset.sum_eq_single_of_mem q hq
        intro r hr hrq
        exact Finset.sum_eq_zero fun b hb =>
          Set.indicator_of_notMem
            (fun ht' => hrq (center_unique hn hr hq hb ha' ht' hw).1) _
      _ = (window n q a).indicator (integrand n) t := by
        exact Finset.sum_eq_single_of_mem a ha' fun b hb hba =>
          Set.indicator_of_notMem
            (fun ht' => hba (center_unique hn hq hq hb ha' ht' hw).2) _
      _ = _ := Set.indicator_of_mem hw _
  · rw [Set.indicator_of_notMem ht]
    symm
    apply Finset.sum_eq_zero
    intro q hq
    apply Finset.sum_eq_zero
    intro a ha
    exact Set.indicator_of_notMem (fun hw => ht ⟨q,a,(Finset.mem_Icc.mp hq).1,
      (Finset.mem_Icc.mp hq).2, Nat.le_of_lt_succ (Finset.mem_range.mp
        (Finset.mem_filter.mp ha).1), (Finset.mem_filter.mp ha).2,
      (mem_window n q a t).mp hw⟩) _

private theorem conj_phase (x : ℝ) : conj (phase x) = phase (-x) := by
  unfold phase E
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem kernel_square_twist (n : ℕ) (β : ℝ) :
    kernel n β ^ 2 * phase (-(n : ℝ) * β) = ((‖kernel n β‖ ^ 2 : ℝ) : ℂ) := by
  have hsym : kernel n β * phase (-(n : ℝ) * β) = conj (kernel n β) := by
    unfold kernel K
    rw [Finset.sum_mul, map_sum]
    calc
      _ = ∑ k ∈ Finset.range (n + 1),
          conj (phase (((n - k : ℕ) : ℝ) * β)) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [conj_phase]
        change phase ((k : ℝ) * β) * phase (-(n : ℝ) * β) =
          phase (-( ((n - k : ℕ) : ℝ) * β))
        rw [← phase_add, Nat.cast_sub (Nat.lt_succ_iff.mp
          (Finset.mem_range.mp hk))]
        congr 1
        ring
      _ = _ := by
        simpa only [Nat.add_sub_cancel, phase] using
          (Finset.sum_range_reflect
            (fun k => conj (phase ((k : ℝ) * β))) (n + 1))
  calc
    _ = kernel n β * (kernel n β * phase (-(n : ℝ) * β)) := by ring
    _ = _ := by rw [hsym, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem continuous_kernel (n : ℕ) : Continuous (kernel n) := by
  unfold kernel K E
  fun_prop

private theorem continuous_phase : Continuous phase := by
  unfold phase E
  fun_prop

theorem model_piece_eq (n q a : ℕ) :
    (∫ β in leftEnd n q a..rightEnd n q a, modelPoint n q a β) = modelPiece n q a := by
  have h (β : ℝ) : modelPoint n q a β =
      (unitMean q a ^ 2 * phase (-(n : ℝ) * center q a)) *
        ((‖kernel n β‖ ^ 2 : ℝ) : ℂ) := by
    rw [modelPoint, ← kernel_square_twist, mul_add, phase_add]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  rfl

private theorem piece_error_le_cost {n q a : ℕ} (hq : 0 < q) (ha : a ≤ q) :
    ‖actualPiece n q a - modelPiece n q a‖ ≤
      ∫ β in leftEnd n q a..rightEnd n q a,
        prefixCost n q a (discrepancy n q a) β := by
  have hi : Continuous (fun β => integrand n (center q a + β)) := by
    exact (continuous_integrand n).comp (by fun_prop)
  have hm : Continuous (modelPoint n q a) := by
    unfold modelPoint
    exact ((continuous_const.mul (continuous_kernel n)).pow 2).mul
      (continuous_phase.comp (by fun_prop))
  have hdiff : Continuous (fun β => integrand n (center q a + β) - modelPoint n q a β) :=
    hi.sub hm
  have hcost : Continuous (fun β => prefixCost n q a (discrepancy n q a) β) := by
    unfold prefixCost amplified
    have hk : Continuous (fun β => ‖unitMean q a * kernel n β‖) :=
      (continuous_const.mul (continuous_kernel n)).norm
    have ha : Continuous (fun β : ℝ => discrepancy n q a *
        (1 + 2 * Real.pi * (n : ℝ) * |β|)) := by fun_prop
    exact ha.mul ((continuous_const.mul hk).add ha)
  have horder := (clipped_order (n := n) hq ha).2.1
  rw [actualPiece, ← model_piece_eq,
    ← intervalIntegral.integral_sub (hi.intervalIntegrable _ _)
      (hm.intervalIntegrable _ _)]
  calc
    _ ≤ ∫ β in leftEnd n q a..rightEnd n q a,
        ‖integrand n (center q a + β) - modelPoint n q a β‖ :=
      intervalIntegral.norm_integral_le_integral_norm horder
    _ ≤ _ := intervalIntegral.integral_mono_on horder
      (hdiff.norm.intervalIntegrable _ _) (hcost.intervalIntegrable _ _)
      (fun β _ => pointwise_error_le_cost hq β)

private theorem phase_character {q : ℕ} [NeZero q] (h a : ℕ) :
    E ((h : ℝ) * a / q) = ZMod.stdAddChar ((h : ZMod q) * (a : ZMod q)) := by
  have ch := ZMod.stdAddChar_coe (N := q) ((h * a : ℕ) : ℤ)
  push_cast at ch
  rw [ch]
  unfold E
  push_cast
  congr 1
  ring

private theorem ram_eq_unit_sum (q h : ℕ) (hq : 0 < q) :
    ram q h = ∑ u : (ZMod q)ˣ, E ((h : ℝ) * (u : ZMod q).val / q) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  unfold ram
  apply Finset.sum_bij (s := (Finset.range q).filter (fun a => Nat.Coprime a q))
    (t := (Finset.univ : Finset (ZMod q)ˣ))
    (fun a ha => ZMod.unitOfCoprime a (Finset.mem_filter.mp ha).2)
  · intro a ha
    exact Finset.mem_univ _
  · intro a ha b hb hab
    have hval := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q).val) hab
    have ha' := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hb' := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    simpa [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt ha',
      ZMod.val_natCast_of_lt hb'] using hval
  · intro u hu
    let a := (u : ZMod q).val
    have ha : a < q := ZMod.val_lt _
    have hunit : IsUnit (a : ZMod q) := by
      rw [ZMod.natCast_zmod_val]
      exact u.isUnit
    have hac : Nat.Coprime a q := (ZMod.isUnit_iff_coprime a q).mp hunit
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, hac⟩, ?_⟩
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime]
    exact ZMod.natCast_zmod_val (u : ZMod q)
  · intro a ha
    have ha' := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hval : ((ZMod.unitOfCoprime a (Finset.mem_filter.mp ha).2 : (ZMod q)ˣ) : ZMod q).val = a := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt ha']
    simp [hval, Nat.mod_eq_of_lt ha']

private theorem ram_unit (q h : ℕ) (hq : 0 < q) (hc : h.Coprime q) :
    ram q h = ram q 1 := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  rw [ram_eq_unit_sum q h hq, ram_eq_unit_sum q 1 hq]
  let v : (ZMod q)ˣ := ZMod.unitOfCoprime h hc
  let e : (ZMod q)ˣ ≃ (ZMod q)ˣ :=
    Equiv.ofBijective (fun u => v * u) (Group.mulLeft_bijective v)
  have hphase (u : (ZMod q)ˣ) :
      E ((h : ℝ) * (u : ZMod q).val / q) =
        E ((1 : ℝ) * ((e u : (ZMod q)ˣ) : ZMod q).val / q) := by
    calc
      E ((h : ℝ) * (u : ZMod q).val / q) =
          ZMod.stdAddChar ((h : ZMod q) * (u : ZMod q)) :=
        by
          simpa only [ZMod.natCast_zmod_val] using
            (phase_character (q := q) h (u : ZMod q).val)
      _ = ZMod.stdAddChar (((1 : ℕ) : ZMod q) *
          ((e u : (ZMod q)ˣ) : ZMod q)) := by
        congr 1
        simp only [Nat.cast_one, one_mul]
        change (h : ZMod q) * (u : ZMod q) = ((v * u : (ZMod q)ˣ) : ZMod q)
        simp [v, ZMod.coe_unitOfCoprime]
      _ = E ((1 : ℝ) * ((e u : (ZMod q)ˣ) : ZMod q).val / q) := by
        symm
        simpa using (phase_character (q := q) (h := 1)
          ((e u : (ZMod q)ˣ) : ZMod q).val)
  calc
    (∑ u : (ZMod q)ˣ, E ((h : ℝ) * (u : ZMod q).val / q)) =
        ∑ u : (ZMod q)ˣ, E ((1 : ℝ) * ((e u : (ZMod q)ˣ) : ZMod q).val / q) := by
          apply Fintype.sum_congr
          intro u
          exact hphase u
    _ = ∑ u : (ZMod q)ˣ, E ((1 : ℝ) * (u : ZMod q).val / q) := by
      exact Equiv.sum_comp e (fun u : (ZMod q)ˣ => E ((1 : ℝ) * (u : ZMod q).val / q))

private theorem unitMean_eq_ram {q a : ℕ} (hq : 0 < q) (h : a.Coprime q) :
    unitMean q a = ram q 1 / (q.totient : ℂ) := by
  calc
    _ = ram q a / (q.totient : ℂ) := by
      apply congrArg (fun z : ℂ => z / (q.totient : ℂ))
      unfold ram
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      dsimp [center]
      ring
    _ = _ := congrArg (fun z : ℂ => z / (q.totient : ℂ)) (ram_unit q a hq h)

private theorem sum_centers_eq_coefficient (q n : ℕ) :
    (∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
      (unitMean q a) ^ 2 * phase (-(n : ℝ) * ((a : ℝ) / q))) = coefficient q n := by
  unfold coefficient ram
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [unitMean_eq_ram (by
    have := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    omega) (Finset.mem_filter.mp ha).2]
  congr 1
  unfold phase E
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

private theorem width_le_unit {n q : ℕ} (hn : 2 * (Q n) ^ 2 < n) (hq : 0 < q) :
    width n q ≤ 1 / (q : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hQn : Q n ≤ n := by
    have hsep : (2 : ℝ) * (Q n : ℝ) ^ 2 < (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hQ : (Q n : ℝ) ≤ n := by nlinarith [sq_nonneg (Q n : ℝ)]
    exact_mod_cast hQ
  calc
    width n q = ((Q n : ℝ) / n) / q := by unfold width; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right
      · exact (div_le_one hn').mpr (by exact_mod_cast hQn)
      · exact hq'.le

private theorem interior_order {q a : ℕ} (hq : 1 < q) (ha : a ∈ numerators q) :
    0 < a ∧ a < q := by
  obtain ⟨h,hc⟩ := Finset.mem_filter.mp ha
  have hle : a ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp h)
  have ha0 : a ≠ 0 := by rintro rfl; simp [Nat.Coprime] at hc; omega
  have hne : a ≠ q := by rintro rfl; simp [Nat.Coprime] at hc; omega
  omega

private theorem uncut {n q a : ℕ} (hn : 2 * (Q n) ^ 2 < n) (hq : 1 < q)
    (ha : a ∈ numerators q) :
    leftEnd n q a = -(width n q) ∧ rightEnd n q a = width n q := by
  obtain ⟨ha₁,haq⟩ := interior_order hq ha
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hw := width_le_unit hn (by omega : 0 < q)
  have hc₁ : 1 / (q : ℝ) ≤ center q a :=
    div_le_div_of_nonneg_right (by exact_mod_cast ha₁) hq'.le
  have hc₂ : center q a + 1 / q ≤ 1 := by
    rw [center, ← add_div, div_le_one hq']
    exact_mod_cast (Nat.succ_le_of_lt haq)
  unfold leftEnd rightEnd
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  constructor <;> ring

private theorem denom_one_phase (n : ℕ) : phase (-(n : ℝ)) = 1 := by
  unfold phase E
  convert Complex.exp_int_mul_two_pi_mul_I (-(n : ℤ)) using 2
  push_cast
  ring

private theorem endpoint_models {n : ℕ} (hn : 2 * (Q n) ^ 2 < n) :
    (∑ a ∈ numerators 1, modelPiece n 1 a) = (kernelMass n (width n 1) : ℂ) := by
  let ww := width n 1
  have hw : 0 ≤ ww := width_nonneg _ _
  have hw1 : ww ≤ 1 := by simpa [ww] using width_le_unit hn (by decide : 0 < 1)
  have h0 : leftEnd n 1 0 = 0 ∧ rightEnd n 1 0 = ww := by
    change max (0 / (1 : ℝ) - ww) 0 - 0 / 1 = 0 ∧ min (0 / 1 + ww) 1 - 0 / 1 = ww
    simp [hw, hw1]
  have h1 : leftEnd n 1 1 = -ww ∧ rightEnd n 1 1 = 0 := by
    change max (1 / (1 : ℝ) - ww) 0 - 1 / 1 = -ww ∧ min (1 / 1 + ww) 1 - 1 / 1 = 0
    rw [one_div_one, max_eq_left (by linarith), min_eq_right (by linarith)]
    constructor <;> ring
  have hu (a : ℕ) : unitMean 1 a = 1 := by
    rw [unitMean_eq_ram (by decide) (by simp)]
    simp [ram, E]
  have hker : Continuous (fun β => ‖kernel n β‖ ^ 2) :=
    (continuous_kernel n).norm.pow 2
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hker.intervalIntegrable (μ := MeasureTheory.volume) (-ww) 0)
    (hker.intervalIntegrable 0 ww)
  have hnSet : numerators 1 = {0,1} := by decide
  rw [hnSet]
  simp only [Finset.sum_insert (by decide : (0 : ℕ) ∉ {1}), Finset.sum_singleton,
    modelPiece, h0.1, h0.2, h1.1, h1.2, hu, center, Nat.cast_zero, Nat.cast_one,
    div_one, mul_zero, mul_one, one_pow, one_mul, denom_one_phase]
  have hz : phase 0 = 1 := by simp [phase, E]
  rw [hz, one_mul, add_comm, ← Complex.ofReal_add, hadd]
  rfl

theorem model_by_denominator {n q : ℕ} (hn : 2 * (Q n) ^ 2 < n) (hq : 0 < q) :
    (∑ a ∈ numerators q, modelPiece n q a) =
      coefficient q n * (kernelMass n (width n q) : ℂ) := by
  rcases eq_or_lt_of_le (show 1 ≤ q by omega) with h | h
  · subst q
    have hc : coefficient 1 n = 1 := by simp [coefficient, ram, E]
    rw [hc, one_mul]
    exact endpoint_models hn
  · have hs : numerators q = (Finset.range q).filter (fun a => a.Coprime q) := by
      ext a
      constructor
      · intro ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (interior_order h ha).2,
          (Finset.mem_filter.mp ha).2⟩
      · intro ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
          have := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
          omega), (Finset.mem_filter.mp ha).2⟩
    rw [← sum_centers_eq_coefficient q n, ← hs, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    obtain ⟨hl,hr⟩ := uncut hn h ha
    simp only [modelPiece, hl, hr, kernelMass, center]
    rfl

private theorem continuous_arc_integrand (n : ℕ) : Continuous (integrand n) :=
  continuous_integrand n

theorem major_split {n : ℕ} (hn : 2 * (Q n) ^ 2 < n) :
    major n = ∑ q ∈ Finset.Icc 1 (Q n), ∑ a ∈ numerators q, actualPiece n q a := by
  have hcont := continuous_arc_integrand n
  have hInt (q a : ℕ) : IntervalIntegrable ((window n q a).indicator (integrand n))
      MeasureTheory.volume 0 1 :=
    ⟨(hcont.intervalIntegrable 0 1).1.indicator measurableSet_Icc,
      (hcont.intervalIntegrable 0 1).2.indicator measurableSet_Icc⟩
  unfold major
  change intervalIntegral (fun t : ℝ => (arcs n).indicator (integrand n) t) (0 : ℝ) 1
    MeasureTheory.volume = _
  rw [show (fun t : ℝ => (arcs n).indicator (integrand n) t) =
      (fun t : ℝ => ∑ q ∈ Finset.Icc 1 (Q n), ∑ a ∈ numerators q,
        (window n q a).indicator (integrand n) t) from
    funext (arc_indicator_sum hn)]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_finsetSum (fun a _ => hInt q a)]
    exact Finset.sum_congr rfl fun a ha => indicator_clipped
      (Finset.mem_Icc.mp hq).1
      (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)) _
  · intro q _
    exact ⟨MeasureTheory.integrable_finsetSum _ (fun a _ => (hInt q a).1),
      MeasureTheory.integrable_finsetSum _ (fun a _ => (hInt q a).2)⟩

theorem major_error {n : ℕ} (hn : 2 * (Q n) ^ 2 < n) :
    ‖major n - modeledContribution n‖ ≤ progressionBudget n := by
  have hmodels : modeledContribution n =
      ∑ q ∈ Finset.Icc 1 (Q n), ∑ a ∈ numerators q, modelPiece n q a :=
    Finset.sum_congr rfl fun q hq =>
      (model_by_denominator hn (Finset.mem_Icc.mp hq).1).symm
  rw [major_split hn, hmodels, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  unfold progressionBudget
  apply Finset.sum_le_sum
  intro q hq
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ numerators q,
        ∫ β in leftEnd n q a..rightEnd n q a,
          prefixCost n q a (discrepancy n q a) β := by
      apply Finset.sum_le_sum
      intro a ha
      exact piece_error_le_cost (Finset.mem_Icc.mp hq).1
        (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp ha).1))
    _ = _ := by rfl

theorem main_claim (n : ℕ) (hn : 1000000 ≤ n) :
    ‖major n - modeledMajor n‖ ≤ progressionBudget n := by
  have hm : modeledContribution n = modeledMajor n := by
    rfl
  rw [← hm]
  exact major_error (cutoff_separated n hn)

end
end Conjectures.Goldbach.ExplicitMajorProgressionBudget_aux

theorem Conjectures.Goldbach.ExplicitMajorProgressionBudget :
let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let Q (n : ℕ) := (Nat.log 2 (n + 2)) ^ 2; let width (n q : ℕ) := (Q n : ℝ) / ((q : ℝ) * n); let K (n : ℕ) (β : ℝ) := ∑ k ∈ Finset.range (n + 1), E ((k : ℝ) * β); let ram (q h : ℕ) := ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), E ((h : ℝ) * a / q); let kernelMass (n : ℕ) (b : ℝ) := intervalIntegral (fun β => ‖K n β‖ ^ 2) (-b) b MeasureTheory.volume; let modeledMajor (n : ℕ) := ∑ q ∈ Finset.Icc 1 (Q n), ((ram q 1 / (q.totient : ℂ)) ^ 2 * (starRingEnd ℂ) (ram q n)) * (kernelMass n (width n q) : ℂ); let w (k : ℕ) := if Nat.Prime k then Real.log (k : ℝ) else 0; let S (n : ℕ) (t : ℝ) := ∑ k ∈ Finset.range (n + 1), (w k : ℂ) * E ((k : ℝ) * t); let center (q a : ℕ) := (a : ℝ) / q; let arcs (n : ℕ) := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - center q a| ≤ width n q}; let major (n : ℕ) := intervalIntegral ((arcs n).indicator (fun t => (S n t) ^ 2 * E (-(n : ℝ) * t))) (0 : ℝ) 1 MeasureTheory.volume; let classError (m q b : ℕ) := (∑ k ∈ (Finset.range m).filter (fun k => k % q = b), w k) - (if Nat.Coprime b q then (m : ℝ) / q.totient else 0); let discrepancy (n q a : ℕ) := (Finset.range (n + 2)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ (n + 1))⟩ (fun m => ‖∑ b ∈ Finset.range q, (classError m q b : ℂ) * E ((b : ℝ) * center q a)‖); let unitMean (q a : ℕ) := (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), E ((r : ℝ) * center q a)) / (q.totient : ℂ); let leftEnd (n q a : ℕ) := max (center q a - width n q) 0 - center q a; let rightEnd (n q a : ℕ) := min (center q a + width n q) 1 - center q a; let amplified (n : ℕ) (D β : ℝ) := D * (1 + 2 * Real.pi * n * |β|); let prefixCost (n q a : ℕ) (D β : ℝ) := amplified n D β * (2 * ‖unitMean q a * K n β‖ + amplified n D β); let progressionBudget (n : ℕ) := ∑ q ∈ Finset.Icc 1 (Q n), ∑ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q), intervalIntegral (prefixCost n q a (discrepancy n q a)) (leftEnd n q a) (rightEnd n q a) MeasureTheory.volume; ∀ n : ℕ, 1000000 ≤ n → ‖major n - modeledMajor n‖ ≤ progressionBudget n := by
  dsimp only
  exact Conjectures.Goldbach.ExplicitMajorProgressionBudget_aux.main_claim
