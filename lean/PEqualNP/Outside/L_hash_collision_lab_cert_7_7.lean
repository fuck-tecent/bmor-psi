import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_7_7 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*1)+7*(∑ i,b i)≤(∑ i,Nat.choose (b i) 7)+q*49 := by
  intro q b
  have hstepK : ∀ k : ℕ, Nat.choose k 7 + Nat.choose k 6 = Nat.choose (k + 1) 7 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hstepK' : ∀ k : ℕ, Nat.choose k 6 + Nat.choose k 5 = Nat.choose (k + 1) 6 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hmono : ∀ y : ℕ, 7 ≤ Nat.choose (7 + y) 6 := by
    intro y
    induction y with
    | zero => decide
    | succ y ih =>
      have hs := hstepK' (7 + y)
      show 7 ≤ Nat.choose (7 + y + 1) 6
      omega
  have hpw : ∀ x : ℕ, 1 + 7 * x ≤ Nat.choose x 7 + 49 := by
    intro x
    rcases Nat.lt_or_ge x 7 with hlt | hge
    · interval_cases x <;> decide
    · obtain ⟨y, rfl⟩ : ∃ y, x = 7 + y := ⟨x - 7, by omega⟩
      clear hge
      induction y with
      | zero => decide
      | succ y ih =>
        have hsK := hstepK (7 + y)
        have hm := hmono y
        show 1 + 7 * (7 + y + 1) ≤ Nat.choose (7 + y + 1) 7 + 49
        calc 1 + 7 * (7 + y + 1)
            = (1 + 7 * (7 + y)) + 7 := by ring
          _ ≤ (Nat.choose (7 + y) 7 + 49) + 7 :=
              Nat.add_le_add_right ih 7
          _ ≤ (Nat.choose (7 + y) 7 + 49) + Nat.choose (7 + y) 6 :=
              Nat.add_le_add_left hm _
          _ = Nat.choose (7 + y + 1) 7 + 49 := by
              rw [Nat.add_right_comm, hsK]
  calc q * 1 + 7 * ∑ i, b i
      = ∑ i, (1 + 7 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 7 + 49) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 7 + q * 49 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
