import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_6_9 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*84)+126*(∑ i,b i)≤(∑ i,Nat.choose (b i) 6)+q*1134 := by
  intro q b
  have hstepK : ∀ k : ℕ, Nat.choose k 6 + Nat.choose k 5 = Nat.choose (k + 1) 6 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hstepK' : ∀ k : ℕ, Nat.choose k 5 + Nat.choose k 4 = Nat.choose (k + 1) 5 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hmono : ∀ y : ℕ, 126 ≤ Nat.choose (9 + y) 5 := by
    intro y
    induction y with
    | zero => decide
    | succ y ih =>
      have hs := hstepK' (9 + y)
      show 126 ≤ Nat.choose (9 + y + 1) 5
      omega
  have hpw : ∀ x : ℕ, 84 + 126 * x ≤ Nat.choose x 6 + 1134 := by
    intro x
    rcases Nat.lt_or_ge x 9 with hlt | hge
    · interval_cases x <;> decide
    · obtain ⟨y, rfl⟩ : ∃ y, x = 9 + y := ⟨x - 9, by omega⟩
      clear hge
      induction y with
      | zero => decide
      | succ y ih =>
        have hsK := hstepK (9 + y)
        have hm := hmono y
        show 84 + 126 * (9 + y + 1) ≤ Nat.choose (9 + y + 1) 6 + 1134
        calc 84 + 126 * (9 + y + 1)
            = (84 + 126 * (9 + y)) + 126 := by ring
          _ ≤ (Nat.choose (9 + y) 6 + 1134) + 126 :=
              Nat.add_le_add_right ih 126
          _ ≤ (Nat.choose (9 + y) 6 + 1134) + Nat.choose (9 + y) 5 :=
              Nat.add_le_add_left hm _
          _ = Nat.choose (9 + y + 1) 6 + 1134 := by
              rw [Nat.add_right_comm, hsK]
  calc q * 84 + 126 * ∑ i, b i
      = ∑ i, (84 + 126 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 6 + 1134) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 6 + q * 1134 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
