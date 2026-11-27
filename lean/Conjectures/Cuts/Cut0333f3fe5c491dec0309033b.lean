import Mathlib
import PEqualNP.Outside.L_twin_primes_unconditional_short

open Filter

-- child 1 en: Reuse the strict-window weighted twin-prime mass lower bound already on the desk.
-- child 1 zh: 复用题台现有严格短窗孪生素数加权质量下界。
-- child 2 en: Reuse the verified medium-divisor cancellation between the frozen cutoffs.
-- child 2 zh: 复用已核的冻结两截断之间中段除数抵消。

theorem Conjectures.Cuts.Cut0333f3fe5c491dec0309033b
    (hMass : (∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∀ (x2 : ℕ), ∃ (x3 : ℕ), x2 < x3 ∧ x1 * ↑x3 ≤ ∑ x4 ∈ Finset.range ((2 : ℕ) * x3 + (1 : ℕ)), if x3 < x4 ∧ (50 : ℕ) * x4 < (51 : ℕ) * x3 ∧ Nat.Prime x4 ∧ Nat.Prime (x4 + (2 : ℕ)) then Real.log ↑x4 * Real.log ↑(x4 + (2 : ℕ)) else (0 : ℝ)))
    (hMedium : (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) | x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1}; have x2 : ℕ → ℝ := fun (x2 : ℕ) => -(↑((ArithmeticFunction.moebius : ℕ → ℤ) x2) : ℝ) * Real.log (↑x2 : ℝ); have x3 : ℕ → ℕ := fun (x3 : ℕ) => ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x4 : ℕ → ℕ := fun (x4 : ℕ) => ⌊√(↑x4 : ℝ) / Real.log ((2 : ℝ) + (↑x4 : ℝ)) ^ (5 : ℕ)⌋₊; have x5 : ℕ → ℝ := fun (x5 : ℕ) => (∑ x6 ∈ x1 x5 with Nat.Prime x6, Real.log (↑x6 : ℝ) * {x7 ∈ (x6 + (2 : ℕ)).divisors | x3 x5 < x7 ∧ x7 ≤ x4 x5}.sum x2) / (↑x5 : ℝ); Filter.Tendsto x5 Filter.atTop (nhds (0 : ℝ)))) :
    (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range ((2 : ℕ) * x1 + (1 : ℕ)) | x1 < x2 ∧ (50 : ℕ) * x2 < (51 : ℕ) * x1}; have x2 : ℕ → ℝ := fun (x2 : ℕ) => -(↑((ArithmeticFunction.moebius : ℕ → ℤ) x2) : ℝ) * Real.log (↑x2 : ℝ); have x3 : ℕ → ℕ := fun (x3 : ℕ) => ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x4 : ℕ → ℕ := fun (x4 : ℕ) => ⌊√(↑x4 : ℝ) / Real.log ((2 : ℝ) + (↑x4 : ℝ)) ^ (5 : ℕ)⌋₊; have x5 : ℝ := ∏' (x5 : ℕ), if Nat.Prime x5 ∧ (2 : ℕ) < x5 then (1 : ℝ) - (1 : ℝ) / ((↑x5 : ℝ) - (1 : ℝ)) ^ (2 : ℕ) else (1 : ℝ); have x6 : ℕ → ℝ := fun (x6 : ℕ) => (∑ x7 ∈ x1 x6 with Nat.Prime x7, Real.log (↑x7 : ℝ) * {x8 ∈ (x7 + (2 : ℕ)).divisors | x3 x6 < x8 ∧ x4 x6 < x8}.sum x2) / (↑x6 : ℝ); ∃ (x7 : ℝ), (0 : ℝ) < x7 ∧ ∀ (x8 : ℕ), ∃ (x9 : ℕ), x8 < x9 ∧ (-2 : ℝ) * x5 / (50 : ℝ) + x7 < x6 x9) := by
  let window := fun X : ℕ => (Finset.range (2 * X + 1)).filter
    (fun p => X < p ∧ 50 * p < 51 * X)
  let primes := fun X : ℕ => (window X).filter Nat.Prime
  let weight := fun d : ℕ => -(ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)
  let lower := fun X : ℕ => ⌊(X : ℝ) ^ (1 / 3 : ℝ)⌋₊
  let upper := fun X : ℕ => ⌊Real.sqrt (X : ℝ) / Real.log (2 + (X : ℝ)) ^ 5⌋₊
  let C := ∏' p : ℕ, if p.Prime ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1
  let short := fun X : ℕ =>
    (∑ p ∈ primes X, Real.log (p : ℝ) *
      ∑ d ∈ (p + 2).divisors.filter (fun d => d ≤ lower X), weight d) / (X : ℝ)
  let middle := fun X : ℕ =>
    (∑ p ∈ primes X, Real.log (p : ℝ) *
      ∑ d ∈ (p + 2).divisors.filter (fun d => lower X < d ∧ d ≤ upper X), weight d) / (X : ℝ)
  let tail := fun X : ℕ =>
    (∑ p ∈ primes X, Real.log (p : ℝ) *
      ∑ d ∈ (p + 2).divisors.filter (fun d => lower X < d ∧ upper X < d), weight d) / (X : ℝ)
  let total := fun X : ℕ =>
    (∑ p ∈ primes X, Real.log (p : ℝ) * ArithmeticFunction.vonMangoldt (p + 2)) / (X : ℝ)
  let mass := fun X : ℕ => ∑ p ∈ Finset.range (2 * X + 1),
    if X < p ∧ 50 * p < 51 * X ∧ p.Prime ∧ (p + 2).Prime then
      Real.log (p : ℝ) * Real.log ((p + 2 : ℕ) : ℝ)
    else 0
  have hS : Tendsto short atTop (nhds (2 * C / 50)) :=
    PEqualNP.Outside.L_twin_primes_unconditional_short
  have hM : Tendsto middle atTop (nhds 0) := hMedium
  have hSM : Tendsto (fun X => short X + middle X) atTop (nhds (2 * C / 50)) := by
    simpa only [add_zero] using hS.add hM
  have hWeight (n : ℕ) : (∑ d ∈ n.divisors, weight d) =
      ArithmeticFunction.vonMangoldt n := by
    have h := ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
    dsimp only [weight]
    simp only [neg_mul, Finset.sum_neg_distrib]
    change -(∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) *
      ArithmeticFunction.log d) = ArithmeticFunction.vonMangoldt n
    rw [h, neg_neg]
  have hPartition (X p : ℕ) :
      (∑ d ∈ (p + 2).divisors, weight d) =
        (∑ d ∈ (p + 2).divisors.filter (fun d => d ≤ lower X), weight d) +
        (∑ d ∈ (p + 2).divisors.filter (fun d => lower X < d ∧ d ≤ upper X), weight d) +
        ∑ d ∈ (p + 2).divisors.filter (fun d => lower X < d ∧ upper X < d), weight d := by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hlo : d ≤ lower X
    · simp [hlo, not_lt_of_ge hlo]
    · have hAbove : lower X < d := lt_of_not_ge hlo
      by_cases hup : d ≤ upper X
      · simp [hlo, hAbove, hup, not_lt_of_ge hup]
      · simp [hlo, hAbove, hup, lt_of_not_ge hup]
  have hTotal (X : ℕ) : total X = short X + middle X + tail X := by
    dsimp only [total, short, middle, tail]
    rw [← add_div, ← add_div]
    congr 1
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← mul_add, ← mul_add, ← hPartition X p, hWeight]
  have hMassUpper (X : ℕ) : mass X ≤ ∑ p ∈ primes X,
      Real.log (p : ℝ) * ArithmeticFunction.vonMangoldt (p + 2) := by
    dsimp only [mass, primes, window]
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro p hpRange
    by_cases hw : X < p ∧ 50 * p < 51 * X
    · by_cases hp : p.Prime
      · by_cases h2 : (p + 2).Prime
        · simp [hw.1, hw.2, hp, h2, ArithmeticFunction.vonMangoldt_apply_prime h2]
        · have hNN : 0 ≤ Real.log (p : ℝ) * ArithmeticFunction.vonMangoldt (p + 2) :=
            mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le))
              ArithmeticFunction.vonMangoldt_nonneg
          simpa [hw.1, hw.2, hp, h2] using hNN
      · simp [hw.1, hw.2, hp]
    · have hNo : ¬ (X < p ∧ 50 * p < 51 * X ∧ p.Prime ∧ (p + 2).Prime) :=
        fun h => hw ⟨h.1, h.2.1⟩
      simp [hw, hNo]
  have hMassWords : ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ c * (X : ℝ) ≤ mass X := hMass
  obtain ⟨c, hc, hCounts⟩ := hMassWords
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hSM.eventually
    (Iio_mem_nhds (show 2 * C / 50 < 2 * C / 50 + c / 2 by linarith)))
  change ∃ k : ℝ, 0 < k ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ (-2 : ℝ) * C / 50 + k < tail X
  refine ⟨c / 2, by positivity, fun B => ?_⟩
  obtain ⟨X, hBX, hXMass⟩ := hCounts (max B N)
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hNX : N ≤ X := (le_max_right B N).trans hBX.le
  have hBound : short X + middle X < 2 * C / 50 + c / 2 := hN X hNX
  have hLower : c ≤ total X :=
    (le_div_iff₀ hXpos).mpr (hXMass.trans (hMassUpper X))
  refine ⟨X, (le_max_left B N).trans_lt hBX, ?_⟩
  linarith [hTotal X]
