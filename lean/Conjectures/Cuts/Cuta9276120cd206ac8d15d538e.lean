import Mathlib

-- Twin primes from Chen's theorem plus one-sided parity cancellation (Selberg's weight).
-- With L2(n) = Λ(n) log n + ∑_{d ∣ n} Λ(d) Λ(n/d) and w(m) = [m prime] log m:
--   μ(n)^2 L2(n) - μ(n) L2(n) = 2 (log n)^2 if n is prime, and 0 otherwise,
-- so child 1 minus child 2 leaves twice the weighted count of twin primes up to X.
-- child 1 zh: 陈景润定理的 Selberg 加权形式：对充分大的 X，∑_{n≤X} μ(n)²Λ₂(n)·[n+2 为素数]·log(n+2) ≥ c·X·log X，其中 Λ₂(n)=Λ(n)log n+∑_{d|n}Λ(d)Λ(n/d)，μ²Λ₂ 只在素数和两个不同素数之积上非零。可由陈景润 1973 年定理（素数 q 使 q−2 为无小素因子的 P₂）推出。
-- child 1 en: Chen's theorem in Selberg-weighted form: for all large X, the sum over n ≤ X of μ(n)²Λ₂(n)·[n+2 prime]·log(n+2) is at least c·X·log X, where Λ₂(n)=Λ(n)log n+∑_{d|n}Λ(d)Λ(n/d) and μ²Λ₂ lives on primes and products of two distinct primes. Follows from Chen (1973) applied to primes q with q−2 a P₂ free of small prime factors.
-- child 2 zh: 奇偶性抵消（单侧、沿无界尺度）：对每个 ε>0，存在任意大的 X 使 ∑_{n≤X} μ(n)Λ₂(n)·[n+2 为素数]·log(n+2) ≤ ε·X·log X，即半素数 n=pq 的加权质量至多比素数 n=p 的质量多 o(X log X)。Hardy–Littlewood 启发预测该和为 O(X)；这是筛法奇偶性障碍的纯粹形式。
-- child 2 en: Parity cancellation (one-sided, along unbounded scales): for every ε>0 there are arbitrarily large X with the sum over n ≤ X of μ(n)Λ₂(n)·[n+2 prime]·log(n+2) at most ε·X·log X, i.e. the weighted mass of semiprimes n=pq exceeds that of primes n=p by at most o(X log X). Hardy–Littlewood heuristics predict O(X); this isolates the sieve parity barrier.

theorem Conjectures.Cuts.Cuta9276120cd206ac8d15d538e
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) * Real.log (X : ℝ) ≤
        ∑ n ∈ Finset.range (X + 1),
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 *
            (ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) +
              ∑ d ∈ n.divisors,
                ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d)) *
            (if Nat.Prime (n + 2) then Real.log ((n : ℝ) + 2) else 0))
    (h₂ : ∀ ε : ℝ, 0 < ε → ∀ B : ℕ, ∃ X : ℕ, B < X ∧
      ∑ n ∈ Finset.range (X + 1),
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            (ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) +
              ∑ d ∈ n.divisors,
                ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d)) *
            (if Nat.Prime (n + 2) then Real.log ((n : ℝ) + 2) else 0)
        ≤ ε * (X : ℝ) * Real.log (X : ℝ)) :
    ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧ (p+2).Prime := by
  intro B
  by_contra hno
  have hno2 : ∀ p : ℕ, B < p → p.Prime → ¬ (p + 2).Prime := by
    intro p hp hpp hp2
    exact hno ⟨p, hp, hpp, hp2⟩
  obtain ⟨c, hc, X₀, hS⟩ := h₁
  -- Selberg weight vanishes on squarefree non-primes with an odd number of prime factors
  have hL2 : ∀ n : ℕ, Squarefree n → Odd (ArithmeticFunction.cardFactors n) → ¬ n.Prime →
      ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) +
        ∑ d ∈ n.divisors,
          ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d) = 0 := by
    intro n hsq hodd hnp
    have h1 : ArithmeticFunction.vonMangoldt n = 0 := by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
      intro hpp
      exact hnp (Nat.squarefree_and_prime_pow_iff_prime.1 ⟨hsq, hpp⟩)
    have h2 : ∀ d ∈ n.divisors,
        ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d) = 0 := by
      intro d hd
      by_contra hne
      have hd1 : ArithmeticFunction.vonMangoldt d ≠ 0 := left_ne_zero_of_mul hne
      have hd2 : ArithmeticFunction.vonMangoldt (n / d) ≠ 0 := right_ne_zero_of_mul hne
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hp : d.Prime := Nat.squarefree_and_prime_pow_iff_prime.1
        ⟨hsq.squarefree_of_dvd hdvd, ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hd1⟩
      have hq : (n / d).Prime := Nat.squarefree_and_prime_pow_iff_prime.1
        ⟨hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdvd), ArithmeticFunction.vonMangoldt_ne_zero_iff.1 hd2⟩
      have hn : n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
      have hΩ : ArithmeticFunction.cardFactors n = 2 := by
        rw [hn, ArithmeticFunction.cardFactors_mul hp.ne_zero hq.ne_zero,
          ArithmeticFunction.cardFactors_apply_prime hp, ArithmeticFunction.cardFactors_apply_prime hq]
      rw [hΩ] at hodd
      exact absurd hodd (by decide)
    rw [h1, zero_mul, zero_add, Finset.sum_eq_zero h2]
  -- beyond B the two weights agree termwise
  have hkey : ∀ n : ℕ, B < n →
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 *
            (ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) +
              ∑ d ∈ n.divisors,
                ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d)) *
            (if Nat.Prime (n + 2) then Real.log ((n : ℝ) + 2) else 0) -
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            (ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) +
              ∑ d ∈ n.divisors,
                ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d)) *
            (if Nat.Prime (n + 2) then Real.log ((n : ℝ) + 2) else 0) = 0 := by
    intro n hn
    by_cases hsq : Squarefree n
    · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
      rcases Nat.even_or_odd (ArithmeticFunction.cardFactors n) with he | ho
      · rw [he.neg_one_pow]; push_cast; ring
      · rw [ho.neg_one_pow]
        by_cases hp : n.Prime
        · have hw : ¬ (n + 2).Prime := hno2 n hn hp
          simp [hw]
        · rw [hL2 n hsq ho hp]; ring
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; push_cast; ring
  -- the finite head
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∑ n ∈ Finset.range (B + 1),
      (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 *
            (ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) +
              ∑ d ∈ n.divisors,
                ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d)) *
            (if Nat.Prime (n + 2) then Real.log ((n : ℝ) + 2) else 0) -
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            (ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) +
              ∑ d ∈ n.divisors,
                ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d)) *
            (if Nat.Prime (n + 2) then Real.log ((n : ℝ) + 2) else 0)) := ⟨_, rfl⟩
  obtain ⟨X, hX, hD⟩ := h₂ (c / 2) (by positivity) (B + X₀ + 3 + ⌈2 * G / c⌉₊)
  have hXB : B + 1 ≤ X + 1 := by omega
  have hsub := Finset.sum_subset (Finset.range_subset_range.2 hXB)
    (f := fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 *
            (ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) +
              ∑ d ∈ n.divisors,
                ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d)) *
            (if Nat.Prime (n + 2) then Real.log ((n : ℝ) + 2) else 0) -
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
            (ArithmeticFunction.vonMangoldt n * Real.log (n : ℝ) +
              ∑ d ∈ n.divisors,
                ArithmeticFunction.vonMangoldt d * ArithmeticFunction.vonMangoldt (n / d)) *
            (if Nat.Prime (n + 2) then Real.log ((n : ℝ) + 2) else 0))
    (fun n _ hn => hkey n (by
      have := Finset.mem_range.not.1 hn
      omega))
  rw [← hG, Finset.sum_sub_distrib] at hsub
  have hS' := hS X (by omega)
  have hXr : (B : ℝ) + X₀ + 3 + ⌈2 * G / c⌉₊ < X := by exact_mod_cast hX
  have hceil : 2 * G / c ≤ ⌈2 * G / c⌉₊ := Nat.le_ceil _
  have hX3 : (3 : ℝ) ≤ X := by
    have h0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (⌈2 * G / c⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith
  have hlog : 1 ≤ Real.log (X : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hX3
  have hGX : G < c / 2 * X := by
    have h0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
    have : 2 * G / c < X := by linarith
    rw [div_lt_iff₀ hc] at this
    linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have : c / 2 * X ≤ c / 2 * X * Real.log X := by
    have : 0 < c / 2 * X := by positivity
    nlinarith
  nlinarith
