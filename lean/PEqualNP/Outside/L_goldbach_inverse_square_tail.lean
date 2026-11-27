import Mathlib

open scoped BigOperators

private lemma telescoping_Icc (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    (∑ k ∈ Finset.Icc a b, (f (k - 1) - f k)) = f (a - 1) - f b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      have hb : b + 1 - 1 = b := by omega
      rw [hb]
      ring

namespace PEqualNP.Outside

theorem L_goldbach_inverse_square_tail :
    ∀ a b : ℕ, 2≤a → Finset.sum (Finset.Icc a b) (fun k => 1/(k:ℝ)^2) ≤ 1/((a:ℝ)-1) := by
  intro a b ha
  let f : ℕ → ℝ := fun k => 1 / (k : ℝ)
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have haDen : 0 < (a : ℝ) - 1 := by linarith
  have hterm : ∀ k ∈ Finset.Icc a b, 1 / (k : ℝ) ^ 2 ≤ f (k - 1) - f k := by
    intro k hk
    have hk2 : 2 ≤ k := ha.trans (Finset.mem_Icc.mp hk).1
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      norm_num
    simp only [f, hcast]
    field_simp [hk0.ne', hk1.ne']
    nlinarith
  by_cases hab : a ≤ b
  · calc
      (∑ k ∈ Finset.Icc a b, 1 / (k : ℝ) ^ 2) ≤
          ∑ k ∈ Finset.Icc a b, (f (k - 1) - f k) := Finset.sum_le_sum hterm
      _ = f (a - 1) - f b := telescoping_Icc f a b hab
      _ ≤ f (a - 1) := by
        have hfb : 0 ≤ f b := by positivity
        linarith
      _ = 1 / ((a : ℝ) - 1) := by
        have hcast : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ a)]
          norm_num
        simp only [f, hcast]
  · have hempty : Finset.Icc a b = ∅ := by
      ext k
      simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and]
      intro hk _
      omega
    rw [hempty, Finset.sum_empty]
    positivity

end PEqualNP.Outside
