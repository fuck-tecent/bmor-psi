import Mathlib

namespace ApLogSumLowerAux

open Finset Real

noncomputable def f (n : ℕ) : ℝ := if n.Prime ∧ n % 4 = 1 then Real.log n else 0

noncomputable def A (n : ℕ) : ℝ := ∑ k ∈ range (n+1), f k

private lemma f_nonneg (n : ℕ) : 0 ≤ f n := by
  unfold f; split_ifs
  · exact Real.log_natCast_nonneg n
  · exact le_rfl

private lemma A_nonneg (n : ℕ) : 0 ≤ A n := Finset.sum_nonneg fun k _ => f_nonneg k

private lemma A_succ (n : ℕ) : A (n+1) = A n + f (n+1) := by
  unfold A; rw [Finset.sum_range_succ _ (n+1)]

private lemma abel (x : ℕ) (hx : 1 ≤ x) :
    ∑ n ∈ range (x+1), f n / n = A x / x + ∑ n ∈ Ico 1 x, A n / (n * (n+1)) := by
  induction x, hx using Nat.le_induction with
  | base => simp [A, f, Finset.sum_range_succ]
  | succ x hx ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Ico_succ_top hx, A_succ]
    have : (x:ℝ) ≠ 0 := by positivity
    have h2 : (x:ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

private lemma log_tel (N : ℕ) (x : ℕ) (h : N ≤ x) :
    Real.log ((x:ℝ)+1) - Real.log ((N:ℝ)+1) ≤ ∑ n ∈ Ico N x, (1 / ((n:ℝ)+1)) := by
  induction x, h using Nat.le_induction with
  | base => simp
  | succ x hx ih =>
    rw [Finset.sum_Ico_succ_top hx]
    have hp : (0:ℝ) < (x:ℝ) + 1 := by positivity
    have h1 : Real.log (((x+1:ℕ):ℝ)+1) - Real.log ((x:ℝ)+1) ≤ 1 / ((x:ℝ)+1) := by
      have := Real.log_le_sub_one_of_pos (x := (((x+1:ℕ):ℝ)+1) / ((x:ℝ)+1)) (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at this
      have e : (((x+1:ℕ):ℝ)+1) / ((x:ℝ)+1) - 1 = 1 / ((x:ℝ)+1) := by
        push_cast; field_simp; ring
      linarith
    linarith

private lemma aux (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 1 ≤ x → (1/2 - ε) * Real.log (x:ℝ) - C ≤
      Finset.sum ((Finset.range (x+1)).filter (fun p => Nat.Prime p ∧ p % 4 = 1))
        (fun p => Real.log (p:ℝ) / ((p:ℝ) - 1)) := by
  have hpnt := Chebyshev.tendsto_sum_log_prime_modEq_div_atTop (q := 4) (a := 1)
    (by norm_num)
  have ht : Nat.totient 4 = 2 := by decide
  rw [ht] at hpnt
  have hlt : (1/2 - ε) < ((2:ℕ):ℝ)⁻¹ := by push_cast; linarith
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 (hpnt.eventually (lt_mem_nhds hlt))
  set N : ℕ := max 1 ⌈X⌉₊ with hN
  have hN1 : 1 ≤ N := le_max_left _ _
  have hA : ∀ n : ℕ, N ≤ n → (1/2 - ε) * n ≤ A n := by
    intro n hn
    have hXn : X ≤ (n:ℝ) := by
      have : ⌈X⌉₊ ≤ n := le_trans (le_max_right _ _) hn
      exact (Nat.ceil_le).1 this
    have h := hX n hXn
    have hn0 : (0:ℝ) < n := by
      have : 1 ≤ n := le_trans hN1 hn
      exact_mod_cast this
    rw [Nat.floor_natCast] at h
    rw [lt_div_iff₀ hn0] at h
    have e : (∑ p ∈ Ioc 0 n with p.Prime ∧ p ≡ 1 [MOD 4], Real.log p) = A n := by
      unfold A f
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      refine Finset.ext fun k => ?_
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
      unfold Nat.ModEq
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨by omega, h3, by omega⟩
      · rintro ⟨h1, h3, h4⟩
        exact ⟨⟨h3.pos, by omega⟩, h3, by omega⟩
    rw [e] at h
    push_cast at h
    nlinarith
  refine ⟨Real.log ((N:ℝ)+1), Real.log_nonneg (by have : (0:ℝ) ≤ N := by positivity
                                                  linarith), ?_⟩
  intro x hx
  have hS0 : 0 ≤ Finset.sum ((Finset.range (x+1)).filter (fun p => Nat.Prime p ∧ p % 4 = 1))
        (fun p => Real.log (p:ℝ) / ((p:ℝ) - 1)) := by
    apply Finset.sum_nonneg
    intro p hp
    simp only [Finset.mem_filter] at hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hp.2.1.two_le
    apply div_nonneg (Real.log_natCast_nonneg p) (by linarith)
  by_cases hxN : x < N
  · have h1 : Real.log (x:ℝ) ≤ Real.log ((N:ℝ)+1) := by
      apply Real.log_le_log (by exact_mod_cast hx)
      have : (x:ℝ) ≤ N := by exact_mod_cast hxN.le
      linarith
    have : (1/2 - ε) * Real.log (x:ℝ) ≤ Real.log (x:ℝ) := by
      have := Real.log_natCast_nonneg x
      nlinarith
    linarith
  · push Not at hxN
    have hcmp : ∑ n ∈ range (x+1), f n / n ≤ Finset.sum ((Finset.range (x+1)).filter
        (fun p => Nat.Prime p ∧ p % 4 = 1)) (fun p => Real.log (p:ℝ) / ((p:ℝ) - 1)) := by
      unfold f
      simp_rw [ite_div, zero_div]
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum
      intro p hp
      simp only [Finset.mem_filter] at hp
      have : (2:ℝ) ≤ p := by exact_mod_cast hp.2.1.two_le
      apply div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by linarith) (by linarith)
    rw [abel x hx] at hcmp
    have hx0 : (0:ℝ) < x := by exact_mod_cast hx
    have h2 : (1/2 - ε) * ∑ n ∈ Ico N x, (1 / ((n:ℝ)+1)) ≤ ∑ n ∈ Ico N x, A n / (n * (n+1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      simp only [Finset.mem_Ico] at hn
      have hn0 : (0:ℝ) < n := by
        have : 1 ≤ n := le_trans hN1 hn.1
        exact_mod_cast this
      have := hA n hn.1
      have e2 : (1/2 - ε) * (1 / ((n:ℝ)+1)) = ((1/2 - ε) * n) / (n * (n+1)) := by
        field_simp
      rw [e2]
      gcongr
    have h3 : ∑ n ∈ Ico N x, A n / (n * (n+1)) ≤ ∑ n ∈ Ico 1 x, A n / (n * (n+1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        simp only [Finset.mem_Ico] at hn ⊢
        exact ⟨le_trans hN1 hn.1, hn.2⟩
      · intro n _ _
        exact div_nonneg (A_nonneg n) (by positivity)
    have h4 : 0 ≤ A x / x := div_nonneg (A_nonneg x) hx0.le
    have h5 := log_tel N x hxN
    have h6 : Real.log (x:ℝ) ≤ Real.log ((x:ℝ)+1) := Real.log_le_log hx0 (by linarith)
    have h7 : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by
      have : (0:ℝ) ≤ N := by positivity
      linarith)
    have hc : 0 ≤ 1/2 - ε := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h5 hc]

end ApLogSumLowerAux

theorem Conjectures.QuadraticPrimes.ApLogSumLower :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 2 ≤ x → (1/2 - η) * (Real.log (x:ℝ) - 4) - C ≤ Finset.sum ((Finset.range (x+1)).filter (fun p => Nat.Prime p ∧ p % 4 = 1)) (fun p => Real.log (p:ℝ) / ((p:ℝ) - 1)) := by
  intro η hη
  by_cases h : η ≤ 1/2
  · obtain ⟨C, hC, hx⟩ := ApLogSumLowerAux.aux η hη h
    refine ⟨C, hC, fun x hx2 => ?_⟩
    have := hx x (by omega)
    nlinarith
  · push Not at h
    refine ⟨4 * (η - 1/2), by linarith, fun x hx2 => ?_⟩
    have hS0 : 0 ≤ Finset.sum ((Finset.range (x+1)).filter (fun p => Nat.Prime p ∧ p % 4 = 1))
        (fun p => Real.log (p:ℝ) / ((p:ℝ) - 1)) := by
      apply Finset.sum_nonneg
      intro p hp
      simp only [Finset.mem_filter] at hp
      have : (2:ℝ) ≤ p := by exact_mod_cast hp.2.1.two_le
      apply div_nonneg (Real.log_natCast_nonneg p) (by linarith)
    have hl := Real.log_natCast_nonneg x
    nlinarith
