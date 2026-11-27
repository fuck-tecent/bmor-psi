import Mathlib

open scoped BigOperators

namespace Conjectures.Goldbach

theorem DyadicExceptionDensityTransfer :
    (let reps (n : ℕ) := (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p));
     let D (X : ℕ) := (Finset.Ico X (2 * X)).filter (fun n => 4 ≤ n ∧ Even n);
     let bad (X : ℕ) := (D X).filter (fun n => (reps n).card = 0);
     let exc (N : ℕ) := (Finset.range (N + 1)).filter (fun n => 4 ≤ n ∧ Even n ∧ (reps n).card = 0);
     ∀ (K N : ℕ) (ε : ℝ), 0 ≤ ε →
       (∀ n : ℕ, 4 ≤ n → n < 2 ^ K → Even n → (reps n).Nonempty) →
       (∀ j : ℕ, K ≤ j → ((bad (2 ^ j)).card : ℝ) ≤ ε * ((2 ^ j : ℕ) : ℝ)) →
       ((exc N).card : ℝ) ≤ 2 * ε * (N : ℝ)) := by
  dsimp only
  intro K N ε hε hsmall hblock
  classical
  let reps : ℕ → Finset ℕ := fun n =>
    (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))
  let D : ℕ → Finset ℕ := fun X =>
    (Finset.Ico X (2 * X)).filter (fun n => 4 ≤ n ∧ Even n)
  let bad : ℕ → Finset ℕ := fun X => (D X).filter (fun n => (reps n).card = 0)
  let exc : ℕ → Finset ℕ := fun N =>
    (Finset.range (N + 1)).filter (fun n => 4 ≤ n ∧ Even n ∧ (reps n).card = 0)
  change ((exc N).card : ℝ) ≤ 2 * ε * (N : ℝ)
  by_cases hN : N < 2 ^ K
  · have hexc_empty : exc N = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro n hn
      simp only [exc, Finset.mem_filter] at hn
      rcases hn with ⟨hn_range, hn_ge, hn_even, hcard⟩
      have hnN : n ≤ N := by
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hn_range)
      have hn_lt : n < 2 ^ K := lt_of_le_of_lt hnN hN
      have hnonempty : (reps n).Nonempty := hsmall n hn_ge hn_lt hn_even
      have hpos : 0 < (reps n).card := Finset.card_pos.mpr hnonempty
      omega
    simp [hexc_empty]
    positivity
  · have hpow_le_N : 2 ^ K ≤ N := by omega
    have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hpow_le_N
    let J : ℕ := Nat.log 2 N + 1
    have hN_lt_pow : N < 2 ^ J := by
      dsimp [J]
      exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
    have hK_le_log : K ≤ Nat.log 2 N := by
      rw [Nat.le_log_iff_pow_le (by norm_num : 1 < 2) (by omega : N ≠ 0)]
      exact hpow_le_N
    have hJpos : 0 < J := by dsimp [J]; omega
    have hKJ : K ≤ J := by dsimp [J]; omega
    have hpow_le_twoN : 2 ^ J ≤ 2 * N := by
      have hlog_le : 2 ^ (J - 1) ≤ N := by
        dsimp [J]
        simpa using Nat.pow_log_le_self 2 (by omega : N ≠ 0)
      have hJeq : J = (J - 1) + 1 := by omega
      have hpow_succ : 2 ^ J = 2 ^ (J - 1) * 2 := by
        have h := pow_succ (2 : ℕ) (J - 1)
        rw [← hJeq] at h
        exact h
      calc
        2 ^ J = 2 ^ (J - 1) * 2 := hpow_succ
        _ ≤ N * 2 := Nat.mul_le_mul_right 2 hlog_le
        _ = 2 * N := by ring
    have hsub : exc N ⊆ (Finset.Ico K J).biUnion (fun j => bad (2 ^ j)) := by
      intro n hn
      simp only [exc, Finset.mem_filter] at hn
      rcases hn with ⟨hn_range, hn_ge, hn_even, hcard⟩
      have hnN : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn_range)
      have hn_powK : 2 ^ K ≤ n := by
        by_contra hlt
        have hn_lt : n < 2 ^ K := by omega
        have hne : (reps n).Nonempty := hsmall n hn_ge hn_lt hn_even
        have hpos : 0 < (reps n).card := Finset.card_pos.mpr hne
        omega
      have hnpos : n ≠ 0 := by omega
      let j : ℕ := Nat.log 2 n
      have hjK : K ≤ j := by
        dsimp [j]
        rw [Nat.le_log_iff_pow_le (by norm_num : 1 < 2) hnpos]
        exact hn_powK
      have hjJ : j < J := by
        dsimp [j]
        have hn_lt_powJ : n < 2 ^ J := lt_of_le_of_lt hnN hN_lt_pow
        exact (Nat.log_lt_iff_lt_pow (b := 2) (by norm_num : 1 < 2) (x := J) hnpos).mpr hn_lt_powJ
      have hjIco : j ∈ Finset.Ico K J := Finset.mem_Ico.mpr ⟨hjK, hjJ⟩
      rw [Finset.mem_biUnion]
      refine ⟨j, hjIco, ?_⟩
      dsimp only [bad]
      rw [Finset.mem_filter]
      constructor
      · dsimp only [D]
        rw [Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨?_, ?_⟩, hn_ge, hn_even⟩
        · dsimp [j]
          exact Nat.pow_log_le_self 2 hnpos
        · change n < 2 * 2 ^ Nat.log 2 n
          have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
          simpa [pow_succ, Nat.mul_comm] using h
      · exact hcard
    have hcard_le : ((exc N).card : ℝ) ≤
        ∑ j ∈ Finset.Ico K J, ((bad (2 ^ j)).card : ℝ) := by
      calc
        ((exc N).card : ℝ) ≤
            (((Finset.Ico K J).biUnion (fun j => bad (2 ^ j))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        _ ≤ ∑ j ∈ Finset.Ico K J, ((bad (2 ^ j)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
    have hblock_sum : (∑ j ∈ Finset.Ico K J, ((bad (2 ^ j)).card : ℝ)) ≤
        ε * (2 : ℝ) ^ J := by
      calc
        (∑ j ∈ Finset.Ico K J, ((bad (2 ^ j)).card : ℝ)) ≤
            ∑ j ∈ Finset.Ico K J, ε * ((2 ^ j : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          exact hblock j (Finset.mem_Ico.mp hj).1
        _ = ε * ∑ j ∈ Finset.Ico K J, ((2 ^ j : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
        _ = ε * ∑ j ∈ Finset.Ico K J, (2 : ℝ) ^ j := by
          norm_num
        _ ≤ ε * (2 : ℝ) ^ J := by
          apply mul_le_mul_of_nonneg_left _ hε
          have hgeom : (∑ j ∈ Finset.Ico K J, (2 : ℝ) ^ j) ≤ (2 : ℝ) ^ J := by
            rw [Finset.sum_Ico_eq_sub (fun j => (2 : ℝ) ^ j) hKJ]
            rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1),
              geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
            norm_num
          exact hgeom
    have htwoJ_le : (2 : ℝ) ^ J ≤ 2 * (N : ℝ) := by
      exact_mod_cast hpow_le_twoN
    calc
      ((exc N).card : ℝ) ≤ ∑ j ∈ Finset.Ico K J, ((bad (2 ^ j)).card : ℝ) := hcard_le
      _ ≤ ε * (2 : ℝ) ^ J := hblock_sum
      _ ≤ ε * (2 * (N : ℝ)) := mul_le_mul_of_nonneg_left htwoJ_le hε
      _ = 2 * ε * (N : ℝ) := by ring

end Conjectures.Goldbach
