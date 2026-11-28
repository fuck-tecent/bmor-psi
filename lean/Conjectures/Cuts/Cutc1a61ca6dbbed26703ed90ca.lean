import Mathlib

/-!
# Cut of `L-goldbach-fixed-shift-sextic-goldbach`

The frozen task asks, for every sufficiently large `n`, primes `p, q` with
`p + q = 2 * n ^ 6`.

Two independent inputs are isolated.

* `h1` (analytic): for every sufficiently large `n` the number of primes `p ≤ 2 * n ^ 6`
  with `2 * n ^ 6 - p` also prime is positive.  Positivity of this weighted representation
  count is what the circle method supplies for the sextic shift and is the true
  obstruction.
* `h2` (combinatorial): a positive count of such primes yields the witness pair.  It only
  reads one member of a finite set and rewrites a natural-number equation.

The bridge converts positivity into the witness.
-/

-- child 1 zh: 解析输入：每个充分大的 n 中，满足 p <= 2n^6 且 2n^6 - p 也为素数的 p 的个数为正；即圆法给出的加权表示数正性。
-- child 1 en: Analytic input: for every sufficiently large n the number of primes p <= 2n^6 with 2n^6 - p prime is positive; this is the circle-method positivity of the weighted representation count for the sextic shift.
-- child 2 zh: 组合提取：该类 p 的个数为正时取出见证 p, q 并核对 p + q = 2n^6。
-- child 2 en: Combinatorial extraction: a positive count of such primes yields a witness pair p, q with p + q = 2n^6.

theorem Conjectures.Cuts.Cutc1a61ca6dbbed26703ed90ca
    (h1 : ∃ (N₀ : ℕ), ∀ (n : ℕ), N₀ ≤ n →
      0 < ({p ∈ Finset.range (2 * n ^ 6 + 1) | Nat.Prime p ∧ Nat.Prime (2 * n ^ 6 - p)}).card)
    (h2 : ∀ (n : ℕ), 0 < ({p ∈ Finset.range (2 * n ^ 6 + 1) |
      Nat.Prime p ∧ Nat.Prime (2 * n ^ 6 - p)}).card →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * n ^ 6) :
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * n ^ 6) := by
  classical
  obtain ⟨N₀, hN⟩ := h1
  exact ⟨N₀, fun n hn => h2 n (hN n hn)⟩
