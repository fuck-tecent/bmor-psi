import Mathlib
import PEqualNP.Outside.L_twin_primes_divisor_bridge
import PEqualNP.Outside.L_twin_primes_unconditional_short
import PEqualNP.Outside.L_twin_primes_window_contamination

-- child 1 zh: 无条件证明立方根至平方根除以对数五次方的有符号除数带趋于零。
-- child 1 en: Prove unconditionally that the signed divisor strip from cube root to square root divided by log^5 tends to zero.
-- child 2 zh: 在无界尺度上证明两个截点之外的长除数余项有统一正裕量。
-- child 2 en: Establish a fixed positive margin above the negative short-divisor main term for divisors past both cutoffs on unbounded scales.

theorem Conjectures.Cuts.Cut8069e77f51c8aaf0e37513d6 :
    (let W := fun X : ℕ => (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)
     let c := fun d : ℕ => -(ArithmeticFunction.moebius d : ℝ) * Real.log d
     let A := fun X : ℕ => Nat.floor ((X : ℝ) ^ (1/3 : ℝ))
     let D := fun X : ℕ => Nat.floor (Real.sqrt X / (Real.log (2 + (X : ℝ))) ^ 5)
     let S := fun X : ℕ => ((W X).filter Nat.Prime).sum (fun p => Real.log p *
       (((p + 2).divisors.filter (fun d => A X < d ∧ d ≤ D X)).sum c)) / (X : ℝ)
     Filter.Tendsto S Filter.atTop (nhds 0)) →
    (let W := fun X : ℕ => (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)
     let c := fun d : ℕ => -(ArithmeticFunction.moebius d : ℝ) * Real.log d
     let A := fun X : ℕ => Nat.floor ((X : ℝ) ^ (1/3 : ℝ))
     let D := fun X : ℕ => Nat.floor (Real.sqrt X / (Real.log (2 + (X : ℝ))) ^ 5)
     let C := ∏' p : ℕ, if p.Prime ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1)^2 else 1
     let R := fun X : ℕ => ((W X).filter Nat.Prime).sum (fun p => Real.log p *
       (((p + 2).divisors.filter (fun d => A X < d ∧ D X < d)).sum c)) / (X : ℝ)
     ∃ δ : ℝ, 0 < δ ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ -2 * C / 50 + δ < R X) →
    (∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧ (p+2).Prime) := by
  intro hStrip hTail
  let W := fun X : ℕ => (Finset.range (2 * X + 1)).filter (fun n => X < n ∧ 50 * n < 51 * X)
  let c := fun d : ℕ => -(ArithmeticFunction.moebius d : ℝ) * Real.log d
  let A := fun X : ℕ => Nat.floor ((X : ℝ) ^ (1/3 : ℝ))
  let D := fun X : ℕ => Nat.floor (Real.sqrt X / (Real.log (2 + (X : ℝ))) ^ 5)
  let C := ∏' p : ℕ, if p.Prime ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1)^2 else 1
  let mass := fun (keep : ℕ → ℕ → Prop) [DecidableRel keep] (X : ℕ) =>
    ((W X).filter Nat.Prime).sum (fun p => Real.log p *
      (((p + 2).divisors.filter (keep X)).sum c)) / (X : ℝ)
  let S := mass (fun X d => A X < d ∧ d ≤ D X)
  let R := mass (fun X d => A X < d ∧ D X < d)
  let L := mass (fun X d => A X < d)
  have partition (X : ℕ) : S X + R X = L X := by
    have splitAt (p : ℕ) :
        ((p+2).divisors.filter (fun d => A X < d ∧ d ≤ D X)).sum c +
        ((p+2).divisors.filter (fun d => A X < d ∧ D X < d)).sum c =
        ((p+2).divisors.filter (fun d => A X < d)).sum c := by
      simpa only [Finset.filter_filter, and_comm, not_le] using
        Finset.sum_filter_add_sum_filter_not
          (s := ((p+2).divisors.filter (fun d => A X < d))) (p := fun d => d ≤ D X) (f := c)
    dsimp only [S, R, L, mass]
    rw [← add_div]
    apply congrArg (fun r : ℝ => r / (X : ℝ))
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← mul_add, splitAt]
  change Filter.Tendsto S Filter.atTop (nhds 0) at hStrip
  change ∃ δ : ℝ, 0 < δ ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ -2 * C / 50 + δ < R X at hTail
  obtain ⟨δ, hδ, hTail⟩ := hTail
  have hSmall : ∀ᶠ X in Filter.atTop, S X ∈ Set.Ioi (-(δ / 2)) :=
    hStrip.eventually (Ioi_mem_nhds (neg_lt_zero.mpr (half_pos hδ)))
  -- Take the long-tail witness beyond the strip's eventual threshold.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hSmall
  have hl : ∃ κ : ℝ, 0 < κ ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ -2 * C / 50 + κ < L X := by
    refine ⟨δ / 2, half_pos hδ, fun B => ?_⟩
    obtain ⟨X, hX, hr⟩ := hTail (max N B)
    have hs : -(δ / 2) < S X := hN X (le_trans (le_max_left N B) hX.le)
    refine ⟨X, lt_of_le_of_lt (le_max_right N B) hX, ?_⟩
    rw [← partition X]
    linarith
  exact PEqualNP.Outside.L_twin_primes_divisor_bridge
    PEqualNP.Outside.L_twin_primes_unconditional_short hl
    PEqualNP.Outside.L_twin_primes_window_contamination
