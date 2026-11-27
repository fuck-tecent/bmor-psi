import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.FixedCutoffArcShell :
    ∀ (Q N n : ℕ), 1 ≤ N → N ≤ n → let r := fun (x q : ℕ) => (Q : ℝ) / ((q : ℝ) * (x : ℝ)); let A := fun (x : ℕ) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ r x q}; A n ⊆ A N ∧ (∀ t ∈ A N \ A n, ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧ r n q < |t - (a : ℝ) / (q : ℝ)| ∧ |t - (a : ℝ) / (q : ℝ)| ≤ r N q) ∧ (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) + 1) * (2 * (r N q - r n q))) ≤ 4 * (Q : ℝ)^2 * ((n : ℝ) - (N : ℝ)) / ((N : ℝ) * (n : ℝ)) := by
  intro Q N n hN hn
  dsimp only
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hnr : (0:ℝ) < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hNn : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hN0 : (N:ℝ) ≠ 0 := ne_of_gt hNr
  have hn0 : (n:ℝ) ≠ 0 := ne_of_gt hnr
  have hNn0 : (0:ℝ) < (N:ℝ) * (n:ℝ) := mul_pos hNr hnr
  have hNn0ne : (N:ℝ) * (n:ℝ) ≠ 0 := ne_of_gt hNn0
  have hsub : (0:ℝ) ≤ (n:ℝ) - (N:ℝ) := by linarith
  have hQ0 : (0:ℝ) ≤ (Q:ℝ) := Nat.cast_nonneg Q
  have hmid : (0:ℝ) ≤ (Q:ℝ) * ((n:ℝ) - (N:ℝ)) := mul_nonneg hQ0 hsub
  have hbase : (0:ℝ) ≤ 4 * (Q:ℝ) * ((n:ℝ) - (N:ℝ)) / ((N:ℝ) * (n:ℝ)) :=
    div_nonneg (mul_nonneg (by positivity) hsub) (le_of_lt hNn0)
  have hrad : ∀ q : ℕ, 1 ≤ q → (Q:ℝ) / ((q:ℝ) * (n:ℝ)) ≤ (Q:ℝ) / ((q:ℝ) * (N:ℝ)) := by
    intro q hq
    have hqr : (0:ℝ) < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
    exact div_le_div_of_nonneg_left hQ0 (mul_pos hqr hNr)
      (mul_le_mul_of_nonneg_left hNn (le_of_lt hqr))
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, a, hq1, hqQ, haq, hcop, hdist⟩ := ht
    exact ⟨q, a, hq1, hqQ, haq, hcop, le_trans hdist (hrad q hq1)⟩
  · intro t ht
    obtain ⟨q, a, hq1, hqQ, haq, hcop, hdist⟩ := ht.1
    refine ⟨q, a, hq1, hqQ, haq, hcop, ?_, hdist⟩
    refine lt_of_not_ge ?_
    intro hle
    exact ht.2 ⟨q, a, hq1, hqQ, haq, hcop, hle⟩
  · have hterm : ∀ q ∈ Finset.Icc (1:ℕ) Q,
        ((q:ℝ) + 1) * (2 * ((Q:ℝ) / ((q:ℝ) * (N:ℝ)) - (Q:ℝ) / ((q:ℝ) * (n:ℝ))))
          ≤ 4 * (Q:ℝ) * ((n:ℝ) - (N:ℝ)) / ((N:ℝ) * (n:ℝ)) := by
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hqr : (0:ℝ) < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
      have hq0 : (q:ℝ) ≠ 0 := ne_of_gt hqr
      have hqN : (q:ℝ) * (N:ℝ) ≠ 0 := mul_ne_zero hq0 hN0
      have hqn : (q:ℝ) * (n:ℝ) ≠ 0 := mul_ne_zero hq0 hn0
      have hqNn : (q:ℝ) * (N:ℝ) * (n:ℝ) ≠ 0 := mul_ne_zero hqN hn0
      have hq1r : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
      have hfrac : ((q:ℝ) + 1) / (q:ℝ) ≤ 2 := by
        rw [div_le_iff₀ hqr]
        linarith
      have hnn : (0:ℝ) ≤ 2 * ((Q:ℝ) * ((n:ℝ) - (N:ℝ)) / ((N:ℝ) * (n:ℝ))) :=
        mul_nonneg (by positivity) (div_nonneg hmid (le_of_lt hNn0))
      calc ((q:ℝ) + 1) * (2 * ((Q:ℝ) / ((q:ℝ) * (N:ℝ)) - (Q:ℝ) / ((q:ℝ) * (n:ℝ))))
          = (((q:ℝ) + 1) / (q:ℝ)) * (2 * ((Q:ℝ) * ((n:ℝ) - (N:ℝ)) / ((N:ℝ) * (n:ℝ)))) := by
            field_simp [hq0, hN0, hn0, hqN, hqn, hNn0ne, hqNn]
        _ ≤ 2 * (2 * ((Q:ℝ) * ((n:ℝ) - (N:ℝ)) / ((N:ℝ) * (n:ℝ)))) :=
            mul_le_mul_of_nonneg_right hfrac hnn
        _ = 4 * (Q:ℝ) * ((n:ℝ) - (N:ℝ)) / ((N:ℝ) * (n:ℝ)) := by ring
    have hcard : ((Finset.Icc (1:ℕ) Q).card : ℝ) ≤ (Q:ℝ) := by
      rw [Nat.card_Icc]
      exact_mod_cast (show Q + 1 - 1 ≤ Q by omega)
    calc (∑ q ∈ Finset.Icc 1 Q, ((q:ℝ) + 1) * (2 * ((Q:ℝ) / ((q:ℝ) * (N:ℝ)) - (Q:ℝ) / ((q:ℝ) * (n:ℝ)))))
        ≤ ∑ q ∈ Finset.Icc 1 Q, (4 * (Q:ℝ) * ((n:ℝ) - (N:ℝ)) / ((N:ℝ) * (n:ℝ))) :=
          Finset.sum_le_sum hterm
      _ = ((Finset.Icc 1 Q).card : ℝ) * (4 * (Q:ℝ) * ((n:ℝ) - (N:ℝ)) / ((N:ℝ) * (n:ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Q:ℝ) * (4 * (Q:ℝ) * ((n:ℝ) - (N:ℝ)) / ((N:ℝ) * (n:ℝ))) :=
          mul_le_mul_of_nonneg_right hcard hbase
      _ = 4 * (Q:ℝ)^2 * ((n:ℝ) - (N:ℝ)) / ((N:ℝ) * (n:ℝ)) := by ring
