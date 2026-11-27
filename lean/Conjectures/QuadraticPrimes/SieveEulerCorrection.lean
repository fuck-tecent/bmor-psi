import Mathlib

namespace Conjectures.QuadraticPrimes.SieveEulerCorrection_aux

noncomputable def fac : ℕ → ℝ := fun p => (1 - 2 / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 2

lemma cast_lower (p : ℕ) (hp : 2 ≤ p) : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp

lemma fac_eq (p : ℕ) (hp : 2 ≤ p) : fac p = 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  have h2 := cast_lower p hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  simp only [fac]
  field_simp
  ring

lemma one_le_sq (p : ℕ) (hp : 2 ≤ p) : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by
  have h1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by have := cast_lower p hp; linarith
  nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) h1]

lemma fac_nonneg (p : ℕ) (hp : 3 ≤ p) : 0 ≤ fac p := by
  have hsq := one_le_sq p (by omega)
  rw [fac_eq p (by omega)]
  have hle : (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 1 :=
    (div_le_one (lt_of_lt_of_le one_pos hsq)).mpr hsq
  linarith

lemma fac_le_one (p : ℕ) (hp : 2 ≤ p) : fac p ≤ 1 := by
  rw [fac_eq p hp]
  have h : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
  linarith

lemma prod_Icc_fac : ∀ z : ℕ, 5 ≤ z →
    ∏ p ∈ Finset.Icc 5 z, fac p = 3 * (z : ℝ) / (4 * ((z : ℝ) - 1)) := by
  intro z
  induction z with
  | zero => intro h; omega
  | succ z ih =>
    intro hz
    by_cases h5 : 5 ≤ z
    · have hstep : ∏ p ∈ Finset.Icc 5 (z + 1), fac p
          = (∏ p ∈ Finset.Icc 5 z, fac p) * fac (z + 1) :=
        Finset.prod_Icc_succ_top (by omega) fac
      rw [hstep, ih h5, fac_eq (z + 1) (by omega)]
      push_cast
      have hz5 : (5 : ℝ) ≤ (z : ℝ) := by exact_mod_cast h5
      have hne0 : (z : ℝ) ≠ 0 := by linarith
      have hne1 : (z : ℝ) - 1 ≠ 0 := by linarith
      have hne2 : (z : ℝ) + 1 ≠ 0 := by linarith
      have hne3 : (z : ℝ) + 1 - 1 ≠ 0 := by linarith
      field_simp
      ring
    · have hz4 : z = 4 := by omega
      subst hz4
      have hIcc : Finset.Icc 5 (4 + 1) = {5} := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_singleton]
        omega
      rw [hIcc, Finset.prod_singleton, fac_eq 5 (by norm_num)]
      push_cast
      norm_num

lemma exists_pos_limit (S : ℕ → Finset ℕ)
    (hanti : Antitone fun z => ∏ p ∈ S z, fac p)
    (hlb : ∀ z, (3 : ℝ) / 4 ≤ ∏ p ∈ S z, fac p) :
    ∃ c : ℝ, 0 < c ∧ Filter.Tendsto (fun z => ∏ p ∈ S z, fac p) Filter.atTop (nhds c) := by
  refine ⟨⨅ z, ∏ p ∈ S z, fac p, ?_, ?_⟩
  · have h := le_ciInf hlb
    exact lt_of_lt_of_le (by norm_num) h
  · exact tendsto_atTop_ciInf hanti ⟨(3 : ℝ) / 4, by rintro _ ⟨z, rfl⟩; exact hlb z⟩

end Conjectures.QuadraticPrimes.SieveEulerCorrection_aux

open Conjectures.QuadraticPrimes.SieveEulerCorrection_aux

theorem Conjectures.QuadraticPrimes.SieveEulerCorrection :
    let split := fun z : ℕ => (Finset.Icc 5 z).filter (fun p => Nat.Prime p ∧ p % 4 = 1); let correction := fun z : ℕ => ∏ p ∈ split z, (1 - 2/(p : ℝ)) / (1 - 1/(p : ℝ))^2;
    ∃ c : ℝ, 0<c ∧ Filter.Tendsto correction Filter.atTop (nhds c) := by
  have hanti : Antitone fun z : ℕ =>
      ∏ p ∈ (Finset.Icc 5 z).filter (fun p => Nat.Prime p ∧ p % 4 = 1), fac p := by
    intro a b hab
    have hsub : (Finset.Icc 5 a).filter (fun p => Nat.Prime p ∧ p % 4 = 1)
        ⊆ (Finset.Icc 5 b).filter (fun p => Nat.Prime p ∧ p % 4 = 1) := by
      intro p hp
      have hpa : p ∈ Finset.Icc 5 a := (Finset.mem_filter.mp hp).1
      refine Finset.mem_filter.mpr ⟨?_, (Finset.mem_filter.mp hp).2⟩
      have hpa' := Finset.mem_Icc.mp hpa
      exact Finset.mem_Icc.mpr ⟨hpa'.1, by omega⟩
    refine Finset.prod_le_prod_of_subset_of_le_one₀ hsub ?_ ?_
    · intro i hi
      exact fac_nonneg i (by have := Finset.mem_Icc.mp (Finset.filter_subset _ _ hi); omega)
    · intro i hi _
      exact fac_le_one i (by have := Finset.mem_Icc.mp (Finset.filter_subset _ _ hi); omega)
  have hlb : ∀ z : ℕ, (3 : ℝ) / 4 ≤
      ∏ p ∈ (Finset.Icc 5 z).filter (fun p => Nat.Prime p ∧ p % 4 = 1), fac p := by
    intro z
    by_cases hz : 5 ≤ z
    · have h1 : ∏ p ∈ Finset.Icc 5 z, fac p
          ≤ ∏ p ∈ (Finset.Icc 5 z).filter (fun p => Nat.Prime p ∧ p % 4 = 1), fac p := by
        refine Finset.prod_le_prod_of_subset_of_le_one₀ (Finset.filter_subset _ _) ?_ ?_
        · intro i hi
          exact fac_nonneg i (by have := Finset.mem_Icc.mp hi; omega)
        · intro i hi _
          exact fac_le_one i (by have := Finset.mem_Icc.mp hi; omega)
      have h2 : ∏ p ∈ Finset.Icc 5 z, fac p = 3 * (z : ℝ) / (4 * ((z : ℝ) - 1)) :=
        prod_Icc_fac z hz
      have h3 : (3 : ℝ) / 4 ≤ 3 * (z : ℝ) / (4 * ((z : ℝ) - 1)) := by
        have hz5 : (5 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
        have hpos : (0 : ℝ) < 4 * ((z : ℝ) - 1) := by linarith
        rw [le_div_iff₀ hpos]
        linarith
      linarith
    · have hIcc : Finset.Icc 5 z = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
      rw [hIcc, Finset.filter_empty, Finset.prod_empty]
      norm_num
  exact exists_pos_limit _ hanti hlb
