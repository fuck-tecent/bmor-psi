import Mathlib

open ArithmeticFunction Finset
open scoped BigOperators

-- child 1 zh: 反向 Chen 粗糙候选的数量最终至少为正的常数倍 X/(log X)^2。
-- child 1 en: The count of rough reversed-shift candidates is eventually at least a positive constant times X/(log X)^2.
-- child 2 zh: 同一粗糙集合中，素数或两个不同素数乘积最终至少占固定正比例。
-- child 2 en: Primes and products of two distinct primes eventually make up a fixed positive proportion of the same rough set.
theorem Conjectures.Cuts.Cut00aa7a26e0f3f7f89fe472fd
    (hLower : let rough := fun X : ℕ => (Finset.range (X + 1)).filter fun n =>
      1 < n ∧ (n + 2).Prime ∧ ∀ p ∈ n.divisors, p.Prime → X ≤ p^10
      ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        c * (X : ℝ) ≤ ((rough X).card : ℝ) * (Real.log (X : ℝ))^2)
    (hPenalty : let rough := fun X : ℕ => (Finset.range (X + 1)).filter fun n =>
      1 < n ∧ (n + 2).Prime ∧ ∀ p ∈ n.divisors, p.Prime → X ≤ p^10
      let good := fun n : ℕ => n.Prime ∨ ∃ d ∈ n.divisors,
      d.Prime ∧ (n / d).Prime ∧ d ≠ n / d
      ∃ δ : ℝ, 0 < δ ∧ ∃ X₁ : ℕ, ∀ X : ℕ, X₁ ≤ X →
        (((rough X).filter fun n => ¬ good n).card : ℝ) ≤ (1 - δ) * ((rough X).card : ℝ)) :
    ∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∃ (x2 : ℕ), ∀ (x3 : ℕ), x2 ≤ x3 → x1 * ↑x3 * Real.log ↑x3 ≤ ∑ x5 ∈ Finset.range (x3 + (1 : ℕ)), ↑(ArithmeticFunction.moebius x5) ^ (2 : ℕ) * (ArithmeticFunction.vonMangoldt x5 * Real.log ↑x5 + ∑ x6 ∈ x5.divisors, ArithmeticFunction.vonMangoldt x6 * ArithmeticFunction.vonMangoldt (x5 / x6)) * if Nat.Prime (x5 + (2 : ℕ)) then Real.log (↑x5 + (2 : ℝ)) else (0 : ℝ) := by
  classical
  let ReverseRoughChenAt (X n : ℕ) : Prop :=
    (n + 2).Prime ∧
      ((n.Prime ∧ X ≤ n^10) ∨
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q ∧ X ≤ p^10 ∧ X ≤ q^10)

  let reverseRoughChenSet (X : ℕ) : Finset ℕ := by
    classical
    exact (range (X + 1)).filter (ReverseRoughChenAt X)


  let ReverseRoughChenCountBound : Prop :=
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) ≤ (reverseRoughChenSet X).card * (Real.log (X : ℝ))^2

  let selbergSecond (n : ℕ) : ℝ :=
    vonMangoldt n * Real.log (n : ℝ) +
      ∑ d ∈ n.divisors, vonMangoldt d * vonMangoldt (n / d)

  let unsignedShiftedSelberg (n : ℕ) : ℝ :=
    ((moebius n : ℤ) : ℝ)^2 * selbergSecond n *
      (if (n + 2).Prime then Real.log ((n : ℝ) + 2) else 0)

  have log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
    by_cases hn : n = 0
    · simp [hn]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)

  have selberg_second_nonneg (n : ℕ) : 0 ≤ selbergSecond n := by
    unfold selbergSecond
    exact add_nonneg (mul_nonneg vonMangoldt_nonneg (log_nat_nonneg n))
      (sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)

  have unsigned_shifted_selberg_nonneg (n : ℕ) : 0 ≤ unsignedShiftedSelberg n := by
    unfold unsignedShiftedSelberg
    apply mul_nonneg (mul_nonneg (sq_nonneg _) (selberg_second_nonneg n))
    split_ifs
    · have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      exact Real.log_nonneg (by linarith only [hn])
    · exact le_rfl

  have log_of_tenth_power_ge {X p : ℕ} (hX : 2 ≤ X) (hp : X ≤ p^10) :
      Real.log (X : ℝ) / 10 ≤ Real.log (p : ℝ) := by
    have hXp : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
    have hpow : (X : ℝ) ≤ (p : ℝ)^10 := by exact_mod_cast hp
    have hlog := Real.log_le_log hXp hpow
    rw [Real.log_pow] at hlog
    norm_num at hlog
    linarith only [hlog]

  have divisors_second_remainder_nonneg (n : ℕ) :
      0 ≤ ∑ d ∈ n.divisors, vonMangoldt d * vonMangoldt (n / d) :=
    sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg

  have unsigned_shifted_selberg_ge_rough_weight {X n : ℕ} (hX : 2 ≤ X)
      (h : ReverseRoughChenAt X n) :
      (Real.log (X : ℝ) / 10)^3 ≤ unsignedShiftedSelberg n := by
    let L := Real.log (X : ℝ) / 10
    have hL : 0 ≤ L := by
      dsimp [L]
      positivity [log_nat_nonneg X]
    obtain ⟨hShift, hCases⟩ := h
    have hParts : ((moebius n : ℤ) : ℝ)^2 = 1 ∧
        L^2 ≤ selbergSecond n ∧ L ≤ Real.log ((n : ℝ) + 2) := by
      rcases hCases with ⟨hn, hnPow⟩ | ⟨p, q, hp, hq, hpq, rfl, hpPow, hqPow⟩
      · have hnLog : L ≤ Real.log (n : ℝ) := log_of_tenth_power_ge hX hnPow
        have hMu : ((moebius n : ℤ) : ℝ)^2 = 1 := by
          rw [moebius_apply_prime hn]
          norm_num
        have hSecond : L^2 ≤ selbergSecond n := calc
          _ ≤ (Real.log (n : ℝ))^2 := pow_le_pow_left₀ hL hnLog 2
          _ ≤ _ := by
            rw [pow_two]
            unfold selbergSecond
            rw [vonMangoldt_apply_prime hn]
            exact le_add_of_nonneg_right (divisors_second_remainder_nonneg n)
        have hLogShift := hnLog.trans
          (Real.log_le_log (Nat.cast_pos.mpr hn.pos) (by linarith : (n : ℝ) ≤ (n : ℝ) + 2))
        exact ⟨hMu, hSecond, hLogShift⟩
      · have hCoprime : p.Coprime q := hp.coprime_iff_not_dvd.mpr
          (fun hd => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd))
        have hMul : moebius (p * q) = moebius p * moebius q :=
          isMultiplicative_moebius.map_mul_of_coprime hCoprime
        have hMu : ((moebius (p * q) : ℤ) : ℝ)^2 = 1 := by
          rw [hMul, moebius_apply_prime hp, moebius_apply_prime hq]
          norm_num
        have hDiv : p ∣ p * q := ⟨q, rfl⟩
        have hpD : p ∈ (p * q).divisors := Nat.mem_divisors.mpr
          ⟨hDiv, mul_ne_zero hp.ne_zero hq.ne_zero⟩
        have hQuot : p * q / p = q :=
          Nat.eq_of_mul_eq_mul_left hp.pos (Nat.mul_div_cancel' hDiv)
        have hP : L ≤ Real.log (p : ℝ) := log_of_tenth_power_ge hX hpPow
        have hQ : L ≤ Real.log (q : ℝ) := log_of_tenth_power_ge hX hqPow
        have hSingle := single_le_sum (f := fun d : ℕ =>
          vonMangoldt d * vonMangoldt (p * q / d))
          (fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg) hpD
        rw [hQuot, vonMangoldt_apply_prime hp, vonMangoldt_apply_prime hq] at hSingle
        have hSecond : L^2 ≤ selbergSecond (p * q) := calc
          _ ≤ Real.log (p : ℝ) * Real.log (q : ℝ) := by
            rw [pow_two]
            exact mul_le_mul hP hQ hL (log_nat_nonneg p)
          _ ≤ ∑ d ∈ (p * q).divisors, vonMangoldt d * vonMangoldt (p * q / d) := hSingle
          _ ≤ _ := le_add_of_nonneg_left (mul_nonneg vonMangoldt_nonneg (log_nat_nonneg (p * q)))
        have hpLe : p ≤ p * q := by simpa using Nat.mul_le_mul_left p hq.one_lt.le
        have hpLeR : (p : ℝ) ≤ ((p * q : ℕ) : ℝ) := by exact_mod_cast hpLe
        have hLogShift := hP.trans
          (Real.log_le_log (Nat.cast_pos.mpr hp.pos)
            (by linarith only [hpLeR] : (p : ℝ) ≤ ((p * q : ℕ) : ℝ) + 2))
        exact ⟨hMu, hSecond, hLogShift⟩
    obtain ⟨hMu, hSecond, hLogShift⟩ := hParts
    change L^3 ≤ unsignedShiftedSelberg n
    unfold unsignedShiftedSelberg
    rw [hMu, one_mul, ite_eq_left hShift, pow_succ]
    exact mul_le_mul hSecond hLogShift hL (selberg_second_nonneg n)

  have shifted_selberg_lower_of_reverse_rough_count (hCount : ReverseRoughChenCountBound) :
      ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        c * (X : ℝ) * Real.log (X : ℝ) ≤
          ∑ n ∈ range (X + 1), unsignedShiftedSelberg n := by
    classical
    obtain ⟨c, hc, X₀, hCount⟩ := hCount
    refine ⟨c / 1000, by positivity, max X₀ 2, ?_⟩
    intro X hX
    have hTwo : 2 ≤ X := (le_max_right X₀ 2).trans hX
    have hCut := (le_max_left X₀ 2).trans hX
    let L := Real.log (X : ℝ)
    let s := reverseRoughChenSet X
    have hL : 0 ≤ L := log_nat_nonneg X
    have hCard : c * (X : ℝ) ≤ (s.card : ℝ) * L^2 := hCount X hCut
    have hSubset : s ⊆ range (X + 1) := by
      unfold s reverseRoughChenSet
      exact filter_subset _ _
    have hPoint (n : ℕ) (hn : n ∈ s) : (L / 10)^3 ≤ unsignedShiftedSelberg n := by
      change n ∈ (range (X + 1)).filter (ReverseRoughChenAt X) at hn
      exact unsigned_shifted_selberg_ge_rough_weight hTwo (mem_filter.mp hn).2
    calc
      _ = (c * (X : ℝ)) * (L / 1000) := by change c / 1000 * (X : ℝ) * L = _; ring
      _ ≤ ((s.card : ℝ) * L^2) * (L / 1000) :=
        mul_le_mul_of_nonneg_right hCard (by positivity)
      _ = (s.card : ℝ) * (L / 10)^3 := by ring
      _ = ∑ _ ∈ s, (L / 10)^3 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ s, unsignedShiftedSelberg n := sum_le_sum hPoint
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hSubset (fun n _ _ => unsigned_shifted_selberg_nonneg n)


  have e724_frozen_of_reverse_rough_count (hCount : ReverseRoughChenCountBound) :
      ∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∃ (x2 : ℕ), ∀ (x3 : ℕ), x2 ≤ x3 → x1 * ↑x3 * Real.log ↑x3 ≤ ∑ x5 ∈ Finset.range (x3 + (1 : ℕ)), ↑(ArithmeticFunction.moebius x5) ^ (2 : ℕ) * (ArithmeticFunction.vonMangoldt x5 * Real.log ↑x5 + ∑ x6 ∈ x5.divisors, ArithmeticFunction.vonMangoldt x6 * ArithmeticFunction.vonMangoldt (x5 / x6)) * if Nat.Prime (x5 + (2 : ℕ)) then Real.log (↑x5 + (2 : ℝ)) else (0 : ℝ) :=
    shifted_selberg_lower_of_reverse_rough_count hCount
  apply e724_frozen_of_reverse_rough_count
  let rough := fun X : ℕ => (Finset.range (X + 1)).filter fun n =>
      1 < n ∧ (n + 2).Prime ∧ ∀ p ∈ n.divisors, p.Prime → X ≤ p^10
  let good := fun n : ℕ => n.Prime ∨ ∃ d ∈ n.divisors,
      d.Prime ∧ (n / d).Prime ∧ d ≠ n / d
  change ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) ≤ ((rough X).card : ℝ) * (Real.log (X : ℝ))^2 at hLower
  change ∃ δ : ℝ, 0 < δ ∧ ∃ X₁ : ℕ, ∀ X : ℕ, X₁ ≤ X →
      (((rough X).filter fun n => ¬ good n).card : ℝ) ≤ (1 - δ) * ((rough X).card : ℝ)
    at hPenalty
  have hGoodSubset (X : ℕ) : (rough X).filter good ⊆ reverseRoughChenSet X := by
    intro n hn
    obtain ⟨hnRough, hnGood⟩ := Finset.mem_filter.mp hn
    change n ∈ (Finset.range (X + 1)).filter (fun n =>
      1 < n ∧ (n + 2).Prime ∧ ∀ p ∈ n.divisors, p.Prime → X ≤ p^10) at hnRough
    obtain ⟨hnRange, hnL, hShift, hnR⟩ := Finset.mem_filter.mp hnRough
    change n ∈ (Finset.range (X + 1)).filter (ReverseRoughChenAt X)
    refine Finset.mem_filter.mpr ⟨hnRange, hShift, ?_⟩
    rcases hnGood with hnP | ⟨d, hd, hdP, hqP, hNe⟩
    · have hd : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl _, hnP.ne_zero⟩
      exact Or.inl ⟨hnP, hnR n hd hnP⟩
    · have hDiv := Nat.dvd_of_mem_divisors hd
      have hn0 : n ≠ 0 := by omega
      have hq := Nat.mem_divisors.mpr
        ⟨Nat.div_dvd_of_dvd hDiv, hn0⟩
      exact Or.inr ⟨d, n / d, hdP, hqP, hNe, (Nat.mul_div_cancel' hDiv).symm,
        hnR d hd hdP, hnR (n / d) hq hqP⟩
  obtain ⟨c, hc, X₀, hCount⟩ := hLower
  obtain ⟨δ, hδ, X₁, hBad⟩ := hPenalty
  refine ⟨c * δ, mul_pos hc hδ, max X₀ X₁, ?_⟩
  intro X hX
  have hX₀ := (le_max_left X₀ X₁).trans hX
  have hX₁ := (le_max_right X₀ X₁).trans hX
  have hPart := Finset.card_filter_add_card_filter_not (s := rough X) good
  have hPartR : (((rough X).filter good).card : ℝ) +
      (((rough X).filter fun n => ¬ good n).card : ℝ) = ((rough X).card : ℝ) := by
    exact_mod_cast hPart
  have hRemaining : δ * ((rough X).card : ℝ) ≤ (((rough X).filter good).card : ℝ) := by
    nlinarith only [hPartR, hBad X hX₁]
  have hAllR : δ * ((rough X).card : ℝ) ≤ ((reverseRoughChenSet X).card : ℝ) :=
    hRemaining.trans (by exact_mod_cast Finset.card_le_card (hGoodSubset X))
  let L := Real.log (X : ℝ)
  change (c * δ) * (X : ℝ) ≤ ((reverseRoughChenSet X).card : ℝ) * L^2
  calc
    _ = δ * (c * (X : ℝ)) := by ring
    _ ≤ δ * (((rough X).card : ℝ) * L^2) := mul_le_mul_of_nonneg_left (hCount X hX₀) hδ.le
    _ = (δ * ((rough X).card : ℝ)) * L^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hAllR (sq_nonneg L)
