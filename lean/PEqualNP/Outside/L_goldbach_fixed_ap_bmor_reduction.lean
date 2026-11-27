import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Complex.ExponentialBounds

namespace FR7022.BmorReduction

open Finset
open ArithmeticFunction (vonMangoldt)

noncomputable def psi (q a n : ℕ) : ℝ :=
  ∑ k ∈ (range (n + 1)).filter (fun k => k % q = a % q), vonMangoldt k

private theorem zero_on_sixes (k : ℕ) (h : 6 ∣ k) : vonMangoldt k = 0 := by
  apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
  intro hk
  obtain ⟨p, e, hp, _, rfl⟩ := (isPrimePow_nat_iff k).mp hk
  have h₂ : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow (dvd_trans (by decide : 2 ∣ 6) h))
  have h₃ : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
    (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by decide : 3 ∣ 6) h))
  omega

private def hit (q a k : ℕ) : ℕ := if k % q = a % q then 1 else 0

-- One period of all the classes involved. 'decide' checks each of the twelve rows.
private theorem periodTable : ∀ r : Fin 12,
    hit 2 1 r = hit 4 1 r + hit 4 3 r ∧
    1 + hit 6 1 r + hit 6 5 r =
      hit 4 1 r + hit 4 3 r + hit 3 1 r + hit 3 2 r + hit 6 0 r := by decide

private theorem hits_periodic (q a k : ℕ) (hq : q ∣ 12) :
    hit q a (k % 12) = hit q a k := by simp [hit, Nat.mod_mod_of_dvd _ hq]

private theorem tableAt (k : ℕ) :
    hit 2 1 k = hit 4 1 k + hit 4 3 k ∧
    1 + hit 6 1 k + hit 6 5 k =
      hit 4 1 k + hit 4 3 k + hit 3 1 k + hit 3 2 k + hit 6 0 k := by
  have h := periodTable ⟨k % 12, Nat.mod_lt _ (by decide)⟩
  simpa only [hits_periodic 2 _ _ (by decide), hits_periodic 3 _ _ (by decide),
    hits_periodic 4 _ _ (by decide), hits_periodic 6 _ _ (by decide)] using h

private theorem psi_eq (q a n : ℕ) :
    psi q a n = ∑ k ∈ range (n+1), (hit q a k : ℝ) * vonMangoldt k := by
  rw [psi, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : k % q = a % q <;> simp [hit, h]

theorem split_two (a n : ℕ) (ha : a.Coprime 2) :
    psi 2 a n = psi 4 1 n + psi 4 3 n := by
  obtain ⟨j, hj⟩ := Nat.coprime_two_right.mp ha
  have ha' : a % 2 = 1 := by omega
  simp only [psi_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have he : hit 2 a k = hit 2 1 k := by simp [hit, ha']
  rw [he, (tableAt k).1, Nat.cast_add, add_mul]

theorem split_one (a n : ℕ) :
    psi 1 a n + psi 6 1 n + psi 6 5 n =
      psi 4 1 n + psi 4 3 n + psi 3 1 n + psi 3 2 n := by
  simp only [psi_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hz : (hit 6 0 k : ℝ) * vonMangoldt k = 0 := by
    by_cases h : k % 6 = 0
    · simp [zero_on_sixes k (Nat.dvd_of_mod_eq_zero h)]
    · simp [hit, h]
  have h := congrArg (fun t : ℕ => (t : ℝ) * vonMangoldt k) (tableAt k).2
  have hone : hit 1 a k = 1 := by
    have hmod : k % 1 = a % 1 := by omega
    simp [hit, hmod]
  simpa only [hone, Nat.cast_add, Nat.cast_one, add_mul, hz, add_zero] using h

/-- The elementary implication. The remaining analytic work is the explicit
    uniform bound for ordinary moduli, supplied here only as a premise. -/
theorem reduce (n : ℕ)
    (h : ∀ q a : ℕ, 3 ≤ q → q ≤ 105 → a.Coprime q →
      |psi q a n - (n : ℝ) / q.totient| ≤ (n : ℝ) / 600)
    (q a : ℕ) (hpos : 1 ≤ q) (hle : q ≤ 105) (ha : a.Coprime q) :
    |psi q a n - (n : ℝ) / q.totient| ≤ (n : ℝ) / 100 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have small (b m : ℕ) (hm : 3 ≤ m) (hm' : m ≤ 105) (hb : b.Coprime m)
      (ht : m.totient = 2) :
      -(↑n / 600 : ℝ) ≤ psi m b n - (n : ℝ) / 2 ∧
       psi m b n - (n : ℝ) / 2 ≤ (n : ℝ) / 600 := by
    have hi := abs_le.mp (h m b hm hm' hb)
    rw [ht] at hi
    simpa only [Nat.cast_ofNat] using hi
  have h41 := small 1 4 (by decide) (by decide) (by decide) (by decide)
  have h43 := small 3 4 (by decide) (by decide) (by decide) (by decide)
  rcases (show q = 1 ∨ q = 2 ∨ 3 ≤ q by omega) with rfl | rfl | hthree
  · have h31 := small 1 3 (by decide) (by decide) (by decide) (by decide)
    have h32 := small 2 3 (by decide) (by decide) (by decide) (by decide)
    have h61 := small 1 6 (by decide) (by decide) (by decide) (by decide)
    have h65 := small 5 6 (by decide) (by decide) (by decide) (by decide)
    have he := split_one a n
    rw [show Nat.totient 1 = 1 by decide]
    push_cast at *
    rw [abs_le]
    constructor <;> linarith only [he, h41.1, h41.2, h43.1, h43.2,
      h31.1, h31.2, h32.1, h32.2, h61.1, h61.2, h65.1, h65.2]
  · have he := split_two a n ha
    rw [show Nat.totient 2 = 1 by decide]
    push_cast at *
    rw [abs_le]
    constructor <;> linarith only [he, hn, h41.1, h41.2, h43.1, h43.2]
  · exact (h q a hthree hle ha).trans (by linarith)

/-- This is the portion of Bennett–Martin–O'Bryant–Rechnitzer, Thm 1.1,
    needed here. We use ≤ instead of the paper's strict inequality. -/
def ExplicitAPBound : Prop :=
  ∀ q a n : ℕ, 3 ≤ q → q ≤ 105 → a.Coprime q → 8 * 10^9 ≤ n →
    |psi q a n - (n : ℝ) / q.totient| ≤ (n : ℝ) / (840 * Real.log n)

/-- Same conclusion as the frozen task, conditional on the named analytic input. -/
theorem from_explicit_estimate (analytic : ExplicitAPBound) :
    ∀ (q a n : ℕ), 1 ≤ q → q ≤ 105 → Nat.Coprime a q → 10^16 ≤ n →
    (n : ℝ) < Real.exp (Real.exp (19/5)) →
    |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
      ArithmeticFunction.vonMangoldt k) - (n : ℝ) / Nat.totient q| ≤ (n : ℝ) / 100 := by
  intro q a n hq hle ha hn _
  apply reduce n _ q a hq hle ha
  intro m b hm hm' hb
  have h4 : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
  have hlog := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4)
  norm_num at hlog
  have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 4) h4
  exact (analytic m b n hm hm' hb (by omega)).trans
    (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (by linarith))

end FR7022.BmorReduction

theorem PEqualNP.Outside.L_goldbach_fixed_ap_bmor_reduction :
    (∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 8000000000 ≤ n → |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q| ≤ (n:ℝ)/(840 * Real.log (n:ℝ))) → (∀ q n : ℕ, 1 ≤ q → 1 ≤ n → (∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q), ArithmeticFunction.vonMangoldt k) ≤ (q.primeFactors.card:ℝ)*Real.log n) → (∀ (q a n : ℕ), 1 ≤ q → q ≤ 105 → Nat.Coprime a q → 10^16 ≤ n → (n:ℝ) < Real.exp (Real.exp (19/5)) → |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q| ≤ (n:ℝ)/100) := by
  intro analytic _
  apply FR7022.BmorReduction.from_explicit_estimate
  intro q a n hq hle ha hn
  have reduced : (a % q).Coprime q := (Nat.mod_modEq a q).gcd_eq.trans ha
  have h := analytic q (a % q) n hq hle (Nat.mod_lt a (by omega)) reduced hn
  simpa only [FR7022.BmorReduction.psi, Nat.mod_mod] using h
