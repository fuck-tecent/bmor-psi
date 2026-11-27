import Mathlib

namespace Conjectures.Goldbach.FiniteMajorPhaseReducedParseval_aux

noncomputable def ph (M j k : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((j : ℝ) * (k : ℝ) / M) : ℝ) : ℂ) * Complex.I)

theorem parseval_range (M : ℕ) (f : ℕ → ℂ) :
    (∑ j ∈ Finset.range M, ‖∑ k ∈ Finset.range M, f k * ph M j k‖ ^ 2)
      = (M : ℝ) * ∑ k ∈ Finset.range M, ‖f k‖ ^ 2 := by
  by_cases hM : M = 0
  · subst M
    simp
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / M)
  have hζ : IsPrimitiveRoot ζ M := Complex.isPrimitiveRoot_exp M hM
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have phase (j k : ℕ) : ph M j k = (ζ ^ k) ^ j := by
    unfold ph
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have unit (j k : ℕ) : ‖ph M j k‖ = 1 := by
    unfold ph
    exact Complex.norm_exp_ofReal_mul_I _
  have orth (k l : ℕ) (hk : k < M) (hl : l < M) :
      ∑ j ∈ Finset.range M, ph M j k * (starRingEnd ℂ) (ph M j l) =
        if k = l then (M : ℂ) else 0 := by
    have term (j : ℕ) : ph M j k * (starRingEnd ℂ) (ph M j l) = (ζ ^ k / ζ ^ l) ^ j := by
      rw [← Complex.inv_eq_conj (unit j l), phase, phase, div_pow, div_eq_mul_inv]
    simp_rw [term]
    by_cases hkl : k = l
    · subst l
      simp [div_self (pow_ne_zero k hζ0)]
    · rw [ite_eq_right hkl, geom_sum_eq]
      · have hpow (i : ℕ) : (ζ ^ i) ^ M = 1 := by
          rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
        simp [div_pow, hpow]
      · exact fun h => hkl (hζ.pow_inj hk hl ((div_eq_one_iff_eq (pow_ne_zero _ hζ0)).mp h))
  have expand (j : ℕ) :
      (∑ k ∈ Finset.range M, f k * ph M j k) * (starRingEnd ℂ) (∑ k ∈ Finset.range M, f k * ph M j k) =
        ∑ k ∈ Finset.range M, ∑ l ∈ Finset.range M,
          f k * (starRingEnd ℂ) (f l) * (ph M j k * (starRingEnd ℂ) (ph M j l)) := by
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [map_mul]
    ring
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', expand]
  change (∑ j ∈ Finset.range M, ∑ k ∈ Finset.range M, ∑ l ∈ Finset.range M, _) = _
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  have inner (l : ℕ) (hl : l ∈ Finset.range M) :
      ∑ j ∈ Finset.range M, f k * (starRingEnd ℂ) (f l) * (ph M j k * (starRingEnd ℂ) (ph M j l)) =
        if k = l then (M : ℂ) * (f k * (starRingEnd ℂ) (f k)) else 0 := by
    rw [← Finset.mul_sum, orth k l (Finset.mem_range.mp hk) (Finset.mem_range.mp hl)]
    split_ifs with h
    · rw [h, mul_comm]
    · exact mul_zero _
  rw [Finset.sum_congr rfl inner]
  simp [hk]

end Conjectures.Goldbach.FiniteMajorPhaseReducedParseval_aux

open Conjectures.Goldbach.FiniteMajorPhaseReducedParseval_aux

theorem Conjectures.Goldbach.FiniteMajorPhaseReducedParseval :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ (q : ℕ) (f : ℕ → ℂ), 0<q → (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), f r*E ((a:ℝ)*(r:ℝ)/q)‖^2) ≤ (q:ℝ)*(∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), ‖f r‖^2) := by
  intro E q f hq
  have hph (a r : ℕ) : E ((a:ℝ)*(r:ℝ)/q) = ph q a r := by
    unfold ph
    rfl
  simp_rw [hph]
  have hinner (a : ℕ) :
      (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), f r * ph q a r)
        = ∑ r ∈ Finset.range q, (if Nat.Coprime r q then f r else 0) * ph q a r := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : Nat.Coprime r q <;> simp [h]
  have hstep1 :
      (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), f r * ph q a r‖ ^ 2)
        = ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            ‖∑ r ∈ Finset.range q, (if Nat.Coprime r q then f r else 0) * ph q a r‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hinner a]
  rw [hstep1]
  calc (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ‖∑ r ∈ Finset.range q, (if Nat.Coprime r q then f r else 0) * ph q a r‖ ^ 2)
      ≤ ∑ a ∈ Finset.range q,
          ‖∑ r ∈ Finset.range q, (if Nat.Coprime r q then f r else 0) * ph q a r‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => sq_nonneg _)
    _ = (q : ℝ) * ∑ r ∈ Finset.range q, ‖(if Nat.Coprime r q then f r else 0)‖ ^ 2 :=
        parseval_range q (fun r => if Nat.Coprime r q then f r else 0)
    _ = (q : ℝ) * (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), ‖f r‖ ^ 2) := by
        congr 1
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro r _
        split_ifs with h
        · rfl
        · rw [norm_zero]
          ring
