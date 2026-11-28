import Mathlib

/-!
# Cut of `L-goldbach-binary-shift-thirteen`

The frozen task asks, for every sufficiently large even `n`, for primes `p, q` and thirteen
positive binary exponents with `n = p + q + ∑ j, 2 ^ (e j + 1)`.

Two independent inputs are isolated.

* `h1` (analytic): for every sufficiently large even `n` the number of admissible pairs
  `(p, e)` is positive; here `p` is prime, every exponent is at most `n`, and
  `n - (p + ∑ j, 2 ^ (e j + 1))` is prime.  This positivity of the weighted
  representation count is the circle-method input (major-arc main term against the
  deep-minor arcs) and is the true obstruction.
* `h2` (combinatorial): a positive admissible count yields an actual witness together with
  its exponent tuple.  It only reads one member of a finite set and rewrites a
  natural-number equation, so no analysis enters.

The bridge below only converts positivity into the witness.
-/

-- child 1 zh: 解析输入：每个充分大偶数 n 的可容许 (p, e) 对数（p 素、指数不超过 n、n−(p+Σ2^(e_j+1)) 为素数）为正；即圆法给出的加权表示数正性。
-- child 1 en: Analytic input: for every sufficiently large even n, the number of admissible pairs (p, e) with p prime, every exponent at most n, and n - (p + Σ_j 2^(e_j+1)) prime is positive; this is the circle-method positivity of the weighted representation count.
-- child 2 zh: 组合提取：可容许对数为正时取出一个见证 (p, q, e) 并核对 n = p + q + Σ_j 2^(e_j+1)。
-- child 2 en: Combinatorial extraction: a positive admissible count yields a witness (p, q, e) with n = p + q + Σ_j 2^(e_j+1).

theorem Conjectures.Cuts.Cutf930a9d94564d80c6a24cd87
    (h1 : ∃ (N₀ : ℕ), ∀ (n : ℕ), N₀ ≤ n → Even n →
      0 < ((((Finset.range (n + 1)).product
          (Fintype.piFinset fun _ : Fin 13 => Finset.range (n + 1))).filter
          (fun pa => Nat.Prime pa.1 ∧
            Nat.Prime (n - (pa.1 + ∑ j : Fin 13, 2 ^ (pa.2 j + 1))))).card : ℝ))
    (h2 : ∀ (n : ℕ), 0 < ((((Finset.range (n + 1)).product
        (Fintype.piFinset fun _ : Fin 13 => Finset.range (n + 1))).filter
        (fun pa => Nat.Prime pa.1 ∧
          Nat.Prime (n - (pa.1 + ∑ j : Fin 13, 2 ^ (pa.2 j + 1))))).card : ℝ) →
      ∃ (p q : ℕ) (e : Fin 13 → ℕ), Nat.Prime p ∧ Nat.Prime q ∧ n = p+q+∑ j, 2^(e j+1)) :
    (∃ N : ℕ, ∀ n ≥ N, Even n → ∃ (p q : ℕ) (e : Fin 13 → ℕ),
      Nat.Prime p ∧ Nat.Prime q ∧ n = p+q+∑ j, 2^(e j+1)) := by
  classical
  obtain ⟨N₀, hN⟩ := h1
  exact ⟨N₀, fun n hn hEven => h2 n (hN n hn hEven)⟩
