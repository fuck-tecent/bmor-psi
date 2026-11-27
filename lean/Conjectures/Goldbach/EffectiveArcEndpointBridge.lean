import Mathlib

open Finset MeasureTheory

private noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

/-- Over one period the zero frequency has integral one and every other
integer frequency has integral zero. -/
private theorem integral_integer_frequency (m : ℤ) :
    (∫ t in (0 : ℝ)..1, phase ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · simp [hm, phase]
  · let a : ℂ := (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ha : a ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hm)
        (mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero)
    have hexp (t : ℝ) : phase ((m : ℝ) * t) = Complex.exp (a * (t : ℂ)) := by
      unfold phase
      dsimp only [a]
      push_cast
      congr 1
      ring
    have hend : Complex.exp a = 1 := Complex.exp_int_mul_two_pi_mul_I m
    simp_rw [hexp]
    rw [integral_exp_mul_complex ha]
    simp [hm, hend]

private noncomputable def exponentialSum (n : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), (w k : ℂ) * phase ((k : ℝ) * t)

/-- The coefficient at n of the squared exponential sum counts the weighted pairs
with index sum n. -/
private theorem square_coefficient (n : ℕ) (w : ℕ → ℝ) :
    (∫ t in (0 : ℝ)..1, (exponentialSum n w t) ^ 2 * phase (-(n : ℝ) * t)) =
      ((∑ k ∈ range (n + 1), w k * w (n - k) : ℝ) : ℂ) := by
  let indices := range (n + 1)
  let frequency (i j : ℕ) : ℤ := (i : ℤ) + j - n
  let term (i j : ℕ) (t : ℝ) : ℂ :=
    ((w i : ℂ) * (w j : ℂ)) * phase ((frequency i j : ℝ) * t)
  have expand (t : ℝ) :
      (exponentialSum n w t) ^ 2 * phase (-(n : ℝ) * t) =
        ∑ i ∈ indices, ∑ j ∈ indices, term i j t := by
    rw [pow_two]
    change (∑ i ∈ indices, (w i : ℂ) * phase ((i : ℝ) * t)) *
      (∑ j ∈ indices, (w j : ℂ) * phase ((j : ℝ) * t)) * phase (-(n : ℝ) * t) = _
    rw [sum_mul_sum, sum_mul]
    apply sum_congr rfl
    intro i _
    rw [sum_mul]
    apply sum_congr rfl
    intro j _
    have shift : (i : ℝ) * t + (j : ℝ) * t + -(n : ℝ) * t = (frequency i j : ℝ) * t := by
      dsimp [frequency]
      push_cast
      ring
    dsimp only [term]
    rw [← shift, phase_add, phase_add]
    ring
  have hcont (i j : ℕ) : Continuous (term i j) := by
    dsimp [term, phase]
    fun_prop
  have row (i : ℕ) (hi : i ∈ indices) :
      (∫ t in (0 : ℝ)..1, ∑ j ∈ indices, term i j t) = (w i : ℂ) * w (n - i) := by
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hmem : n - i ∈ indices := mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le n i))
    have hfreq (j : ℕ) : frequency i j = 0 ↔ j = n - i := by
      dsimp [frequency]
      omega
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont i j).intervalIntegrable 0 1)]
    simp [term, intervalIntegral.integral_const_mul, integral_integer_frequency, hfreq, mul_ite, hmem]
  calc
    _ = ∫ t in (0 : ℝ)..1, ∑ i ∈ indices, ∑ j ∈ indices, term i j t := by simp_rw [expand]
    _ = ∑ i ∈ indices, ∫ t in (0 : ℝ)..1, ∑ j ∈ indices, term i j t :=
      intervalIntegral.integral_finsetSum (fun i _ =>
        (continuous_finsetSum indices (fun j _ => hcont i j)).intervalIntegrable 0 1)
    _ = ∑ i ∈ indices, (w i : ℂ) * w (n - i) := sum_congr rfl row
    _ = _ := by simp [indices]

private theorem measurable_arcs (Q n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / ((q : ℝ) * (n : ℝ))} := by
  simp only [Set.ofPred_exists, Set.ofPred_and]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  repeat' apply (MeasurableSet.const _).inter
  exact (isClosed_le (continuous_id.sub continuous_const).abs continuous_const).measurableSet

private theorem split_arc_integral {A : Set ℝ} {g : ℝ → ℂ}
    (hA : MeasurableSet A) (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, A.indicator g t) + (∫ t in (0 : ℝ)..1, Aᶜ.indicator g t) =
      ∫ t in (0 : ℝ)..1, g t := by
  have hint : IntegrableOn g (Set.Ioc (0 : ℝ) 1) volume :=
    (hg.intervalIntegrable (μ := volume) 0 1).1
  simp only [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  rw [MeasureTheory.integral_indicator hA, MeasureTheory.integral_indicator hA.compl]
  exact MeasureTheory.integral_add_compl hA hint

theorem Conjectures.Goldbach.EffectiveArcEndpointBridge :
let w (k : ℕ) := if Nat.Prime k then Real.log (k : ℝ) else 0; let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S (n : ℕ) (t : ℝ) := ∑ k ∈ Finset.range (n+1), (w k : ℂ) * E ((k : ℝ)*t); let Q (n : ℕ) := (Nat.log 2 (n+2))^2; let arcs (n : ℕ) := {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f (n : ℕ) (t : ℝ) := (S n t)^2 * E (-(n:ℝ)*t); let major (n : ℕ) := intervalIntegral ((arcs n).indicator (f n)) (0:ℝ) 1 MeasureTheory.volume; let minor (n : ℕ) := intervalIntegral ((arcs n)ᶜ.indicator (f n)) (0:ℝ) 1 MeasureTheory.volume; ∀ (B : ℕ) (c : ℝ), 4 ≤ B → 0 < c → (∀ n : ℕ, 4 ≤ n → n ≤ B → Even n → 0 < Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p))) → (∀ n : ℕ, B < n → Even n → c * (n : ℝ) ≤ (major n).re) → (∀ n : ℕ, B < n → Even n → -(c / 2 * (n : ℝ)) ≤ (minor n).re) → ∀ n : ℕ, 4 ≤ n → Even n → let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0; 0 < Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p))
:= by
  intro w E S Q arcs f major minor B c hB hc hfin hmaj hmin n hn hev
  by_cases hBn : n ≤ B
  · exact hfin n hn hBn hev
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hm := hmaj n (by omega) hev
    have hmi := hmin n (by omega) hev
    have hcont : Continuous (f n) := by
      dsimp only [f, S, E]
      fun_prop
    have hcoeff : major n + minor n = ((∑ k ∈ range (n + 1), w k * w (n - k) : ℝ) : ℂ) := by
      calc major n + minor n = ∫ t in (0 : ℝ)..1, f n t :=
            split_arc_integral (measurable_arcs (Q n) n) hcont
        _ = ((∑ k ∈ range (n + 1), w k * w (n - k) : ℝ) : ℂ) := square_coefficient n w
    have htotal : 0 < (major n + minor n).re := by
      rw [Complex.add_re]
      nlinarith only [hm, hmi, mul_pos hc hnpos]
    rw [hcoeff, Complex.ofReal_re] at htotal
    exact htotal
