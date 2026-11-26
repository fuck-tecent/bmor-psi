import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

noncomputable section

def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (u k : ℂ) * E ((k : ℝ) * t)

def U (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 16 : ℝ)⌋₊

def B1 (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊

def mu (d : ℕ) : ℝ := ((ArithmeticFunction.moebius d : ℤ) : ℝ)

def tau1 (n m : ℕ) : ℝ :=
  ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B1 n ∧ U n < m / a),
    (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), mu d) *
      ArithmeticFunction.vonMangoldt (m / a)

lemma tau1_eq_sum_Icc (n m : ℕ) :
    tau1 n m =
      ∑ a ∈ Finset.Icc (U n + 1) (B1 n),
        if a ∣ m ∧ U n < m / a then
          (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), mu d) *
            ArithmeticFunction.vonMangoldt (m / a)
        else 0 := by
  classical
  unfold tau1
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext a
    by_cases hm : m = 0
    · subst m
      rw [Nat.divisors_zero]
      simp
    · rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      simp [hm]
      constructor
      · intro h
        rcases h with ⟨ha_div, hUa, haB, hma⟩
        exact ⟨⟨by omega, haB⟩, ha_div, hma⟩
      · intro h
        rcases h with ⟨⟨hUa, haB⟩, ha_div, hma⟩
        exact ⟨ha_div, by omega, haB, hma⟩
  · intro a ha
    rfl

end

end PEqualNP.Outside

namespace PEqualNP.Outside

noncomputable section

lemma inner_reindex (n a : ℕ) (ha : 1 ≤ a) (t : ℝ) :
    (∑ m ∈ Finset.range (n + 1),
        if a ∣ m ∧ U n < m / a then
          ArithmeticFunction.vonMangoldt (m / a) * E ((m : ℝ) * t)
        else 0) =
      ∑ r ∈ Finset.Icc (U n + 1) (n / a),
        ArithmeticFunction.vonMangoldt r * E (((a * r : ℕ) : ℝ) * t) := by
  classical
  have ha0 : 0 < a := by omega
  let s : Finset ℕ := (Finset.range (n + 1)).filter (fun m => a ∣ m ∧ U n < m / a)
  let tset : Finset ℕ := Finset.Icc (U n + 1) (n / a)
  have hsum : (∑ m ∈ Finset.range (n + 1),
        if a ∣ m ∧ U n < m / a then
          ArithmeticFunction.vonMangoldt (m / a) * E ((m : ℝ) * t)
        else 0) =
      ∑ m ∈ s, ArithmeticFunction.vonMangoldt (m / a) * E ((m : ℝ) * t) := by
    simp only [s, Finset.sum_filter]
  rw [hsum]
  refine Finset.sum_bij' (fun m _ => m / a) (fun r _ => a * r) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    simp only [s, Finset.mem_filter, Finset.mem_range] at hm
    rcases hm with ⟨hmn, hdvd, hU⟩
    rw [Finset.mem_Icc]
    exact ⟨by omega, (Nat.div_le_div_right (by omega : m ≤ n))⟩
  · intro r hr
    simp only [tset, Finset.mem_Icc] at hr
    rcases hr with ⟨hUr, hrn⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · have hmul : a * r ≤ a * (n / a) := Nat.mul_le_mul_left a hrn
      have hle : a * (n / a) ≤ n := Nat.mul_div_le n a
      omega
    · exact ⟨dvd_mul_right a r, by rw [Nat.mul_div_right r ha0]; omega⟩
  · intro m hm
    simp only [s, Finset.mem_filter, Finset.mem_range] at hm
    rcases hm with ⟨_, hdvd, _⟩
    exact Nat.mul_div_cancel' hdvd
  · intro r hr
    exact Nat.mul_div_right r ha0
  · intro m hm
    simp only [s, Finset.mem_filter, Finset.mem_range] at hm
    rcases hm with ⟨_, hdvd, _⟩
    rw [Nat.mul_div_cancel' hdvd]

end

end PEqualNP.Outside

namespace PEqualNP.Outside

noncomputable section

lemma S_tau1_expand (n : ℕ) (t : ℝ) :
    S n (tau1 n) t =
      ∑ a ∈ Finset.Icc (U n + 1) (B1 n),
        (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), mu d) *
          ∑ r ∈ Finset.Icc (U n + 1) (n / a),
            ArithmeticFunction.vonMangoldt r * E (((a * r : ℕ) : ℝ) * t) := by
  classical
  unfold S
  simp_rw [tau1_eq_sum_Icc]
  push_cast
  simp_rw [apply_ite (fun z : ℝ => (z : ℂ))]
  push_cast
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have ha1 : 1 ≤ a := by
    rw [Finset.mem_Icc] at ha
    omega
  have hfactor :
      (∑ m ∈ Finset.range (n + 1),
          (if a ∣ m ∧ U n < m / a then
            (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), ((mu d : ℝ) : ℂ)) *
              ((ArithmeticFunction.vonMangoldt (m / a) : ℝ) : ℂ)
          else 0) * E ((m : ℝ) * t)) =
        (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), ((mu d : ℝ) : ℂ)) *
          ∑ m ∈ Finset.range (n + 1),
            if a ∣ m ∧ U n < m / a then
              ((ArithmeticFunction.vonMangoldt (m / a) : ℝ) : ℂ) * E ((m : ℝ) * t)
            else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases h : a ∣ m ∧ U n < m / a <;> simp [h, mul_assoc]
  rw [hfactor, inner_reindex n a ha1 t]
  push_cast
  rfl

end

end PEqualNP.Outside

namespace PEqualNP.Outside

noncomputable section

theorem L_goldbach_frontier_type2_b1_b1_bilinear_expansion :
    (let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
     let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) =>
       Finset.sum (Finset.range (n + 1)) (fun k => (u k : ℂ) * E ((k : ℝ) * t));
     let U := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 16 : ℝ)⌋₊;
     let B₁ := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊;
     let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ);
     let τ₁ := fun (n m : ℕ) =>
       ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a),
         (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) *
           ArithmeticFunction.vonMangoldt (m / a);
     ∀ (n : ℕ) (t : ℝ),
       S n (τ₁ n) t =
         ∑ a ∈ Finset.Icc (U n + 1) (B₁ n),
           (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) *
             ∑ r ∈ Finset.Icc (U n + 1) (n / a),
               ArithmeticFunction.vonMangoldt r * E (((a * r : ℕ) : ℝ) * t)) := by
  dsimp only
  intro n t
  exact S_tau1_expand n t

end

end PEqualNP.Outside

