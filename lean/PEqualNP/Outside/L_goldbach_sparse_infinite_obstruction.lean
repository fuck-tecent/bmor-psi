import Mathlib

theorem PEqualNP.Outside.L_goldbach_sparse_infinite_obstruction :
    ∃ s : ℕ → Bool,
      (∀ n : ℕ, s n = true → 4 ≤ n ∧ Even n) ∧
        (∀ M : ℕ, ∃ n : ℕ, M < n ∧ s n = true) ∧
          ∀ X : ℕ,
            ((Finset.range (X + 1)).filter (fun n => s n = true)).card ≤
              Nat.sqrt X + 1 := by
  classical
  let s : ℕ → Bool := fun n => decide (4 ≤ n ∧ Even n ∧ ∃ k : ℕ, n = 2 * k * k)
  refine ⟨s, ?_, ?_, ?_⟩
  · intro n hn
    have h := of_decide_eq_true (by simpa [s] using hn)
    exact ⟨h.1, h.2.1⟩
  · intro M
    refine ⟨2 * (M + 2) * (M + 2), ?_, ?_⟩
    · nlinarith
    · change decide (4 ≤ 2 * (M + 2) * (M + 2) ∧
          Even (2 * (M + 2) * (M + 2)) ∧ ∃ k : ℕ, 2 * (M + 2) * (M + 2) = 2 * k * k) = true
      rw [decide_eq_true_eq]
      refine ⟨by nlinarith, ?_, ⟨M + 2, rfl⟩⟩
      exact ⟨(M + 2) * (M + 2), by ring_nf⟩
  · intro X
    let T := (Finset.range (X + 1)).filter (fun n => s n = true)
    have hsub : T ⊆ Finset.image (fun k : ℕ => 2 * k * k) (Finset.range (Nat.sqrt X + 1)) := by
      intro n hn
      simp only [T, Finset.mem_filter, Finset.mem_range] at hn
      obtain ⟨hnX, hns⟩ := hn
      obtain ⟨h4, heven, k, hk⟩ := of_decide_eq_true (by simpa [s] using hns)
      refine Finset.mem_image.mpr ⟨k, ?_, hk.symm⟩
      simp only [Finset.mem_range]
      have hkX : k * k ≤ X := by
        have h2 : 2 * (k * k) ≤ X := by
          calc
            2 * (k * k) = 2 * k * k := by ring
            _ = n := hk.symm
            _ ≤ X := by omega
        omega
      have hsqrt : k ≤ Nat.sqrt X := by
        rw [← Nat.sqrt_eq k]
        exact Nat.sqrt_le_sqrt hkX
      exact Nat.lt_succ_of_le hsqrt
    calc
      T.card ≤ (Finset.image (fun k : ℕ => 2 * k * k) (Finset.range (Nat.sqrt X + 1))).card :=
        Finset.card_le_card hsub
      _ ≤ (Finset.range (Nat.sqrt X + 1)).card := Finset.card_image_le
      _ = Nat.sqrt X + 1 := Finset.card_range _
