import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-
The elementary divisor_progression helper is adapted from the public proof
PEqualNP.Outside.L_goldbach_reflected_divisor_unit_progression,
public check 45628303960, source SHA256
4767099eb1a047738a9ac78080c0ec9477bbdb7be89568aed93eac9c49c2e918.
The weighted finite partition and transposition below keep all original
cutoffs and arbitrary real weights, including empty boundary cases.
-/

open scoped BigOperators

private lemma divisor_progression (n p d : ℕ)
    (hpn : p < n) (hcop : Nat.Coprime p n) (hd : d ∣ n - p) :
    Nat.Coprime n d ∧ p % d = n % d := by
  have hmod : p % d = n % d := by
    have heq : n = p + (n - p) := (Nat.add_sub_of_le hpn.le).symm
    rw [heq, Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, add_zero, Nat.mod_mod]
  have hcop_sub : Nat.Coprime n (n - p) :=
    (Nat.coprime_self_sub_right hpn.le).mpr hcop.symm
  exact ⟨hcop_sub.coprime_dvd_right hd, hmod⟩

private lemma split_finite_sum (A : Finset ℕ) (D : ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ A, f d) =
      (∑ d ∈ A.filter (fun d => d ≤ D), f d) +
      (∑ d ∈ A.filter (fun d => D < d), f d) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : d ≤ D
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_ge h]

private lemma swap_filtered_sums (A B : Finset ℕ) (R : ℕ → ℕ → Prop)
    [DecidableRel R] (f g : ℕ → ℝ) :
    (∑ p ∈ A, f p * ∑ d ∈ B.filter (fun d => R p d), g d) =
      ∑ d ∈ B, g d * ∑ p ∈ A.filter (fun p => R p d), f p := by
  simp only [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : R p d <;> simp [h, mul_comm]

theorem Conjectures.Goldbach.ReflectedDivisorExactSplit :
∀ (N D : ℕ) (η : ℕ → ℝ), let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let Λ := ArithmeticFunction.vonMangoldt; let P := (Finset.range N).filter (fun p => Nat.Prime p ∧ Nat.Coprime p N); (∑ p ∈ P, η p * Λ (N - p)) = (-(∑ d ∈ (Finset.Icc 1 D).filter (fun d => Nat.Coprime d N), μ d * Real.log (d : ℝ) * ∑ p ∈ P.filter (fun p => p % d = N % d), η p)) + (-(∑ p ∈ P, η p * ∑ d ∈ (Nat.divisors (N - p)).filter (fun d => D < d), μ d * Real.log (d : ℝ))) := by
  classical
  intro N D η μ Λ P
  let f : ℕ → ℝ := fun d => μ d * Real.log (d : ℝ)
  let B : Finset ℕ := (Finset.Icc 1 D).filter (fun d => Nat.Coprime d N)
  have hΛ (m : ℕ) : Λ m = -(∑ d ∈ m.divisors, f d) := by
    have hs : (∑ d ∈ m.divisors, f d) = -Λ m :=
      ArithmeticFunction.sum_moebius_mul_log_eq
    rw [hs, neg_neg]
  have hsets (p : ℕ) (hp : p ∈ P) :
      (N - p).divisors.filter (fun d => d ≤ D) =
        B.filter (fun d => p % d = N % d) := by
    have hp' := Finset.mem_filter.mp hp
    have hpn : p < N := Finset.mem_range.mp hp'.1
    have hcop : Nat.Coprime p N := hp'.2.2
    ext d
    constructor
    · intro hd
      rcases Finset.mem_filter.mp hd with ⟨hdmem, hdD⟩
      have hdiv := Nat.dvd_of_mem_divisors hdmem
      have hunit := divisor_progression N p d hpn hcop hdiv
      have hdpos : 1 ≤ d := Nat.pos_of_mem_divisors hdmem
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdpos, hdD⟩, hunit.1.symm⟩,
          hunit.2⟩
    · intro hd
      rcases Finset.mem_filter.mp hd with ⟨hdB, hmod⟩
      rcases Finset.mem_filter.mp hdB with ⟨hdI, _⟩
      have hdiv : d ∣ N - p := (Nat.modEq_iff_dvd' hpn.le).mp hmod
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hdiv, (Nat.sub_pos_of_lt hpn).ne'⟩,
          (Finset.mem_Icc.mp hdI).2⟩
  have hsmall :
      (∑ p ∈ P, η p * ∑ d ∈ (N - p).divisors.filter (fun d => d ≤ D), f d) =
        ∑ d ∈ B, f d * ∑ p ∈ P.filter (fun p => p % d = N % d), η p := by
    calc
      _ = ∑ p ∈ P, η p * ∑ d ∈ B.filter (fun d => p % d = N % d), f d := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [hsets p hp]
      _ = _ := swap_filtered_sums P B (fun p d => p % d = N % d) η f
  change (∑ p ∈ P, η p * Λ (N - p)) =
    (-(∑ d ∈ B, f d * ∑ p ∈ P.filter (fun p => p % d = N % d), η p)) +
    (-(∑ p ∈ P, η p * ∑ d ∈ (N - p).divisors.filter (fun d => D < d), f d))
  calc
    _ = ∑ p ∈ P,
        ((-(η p * ∑ d ∈ (N - p).divisors.filter (fun d => d ≤ D), f d)) +
         (-(η p * ∑ d ∈ (N - p).divisors.filter (fun d => D < d), f d))) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hΛ, split_finite_sum (N - p).divisors D f]
      ring
    _ = (-(∑ p ∈ P, η p * ∑ d ∈ (N - p).divisors.filter (fun d => d ≤ D), f d)) +
        (-(∑ p ∈ P, η p * ∑ d ∈ (N - p).divisors.filter (fun d => D < d), f d)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = _ := by rw [hsmall]
