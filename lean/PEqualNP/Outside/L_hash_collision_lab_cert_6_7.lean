import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_6_7 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*7)+21*(∑ i,b i)≤(∑ i,Nat.choose (b i) 6)+q*147 := by
  intro q b
  have hstepK : ∀ k : ℕ, Nat.choose k 6 + Nat.choose k 5 = Nat.choose (k + 1) 6 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hstepK' : ∀ k : ℕ, Nat.choose k 5 + Nat.choose k 4 = Nat.choose (k + 1) 5 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hmono : ∀ y : ℕ, 21 ≤ Nat.choose (7 + y) 5 := by
    intro y
    induction y with
    | zero => decide
    | succ y ih =>
      have hs := hstepK' (7 + y)
      show 21 ≤ Nat.choose (7 + y + 1) 5
      omega
  have hpw : ∀ x : ℕ, 7 + 21 * x ≤ Nat.choose x 6 + 147 := by
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
        show 7 + 21 * (7 + y + 1) ≤ Nat.choose (7 + y + 1) 6 + 147
        calc 7 + 21 * (7 + y + 1)
            = (7 + 21 * (7 + y)) + 21 := by ring
          _ ≤ (Nat.choose (7 + y) 6 + 147) + 21 :=
              Nat.add_le_add_right ih 21
          _ ≤ (Nat.choose (7 + y) 6 + 147) + Nat.choose (7 + y) 5 :=
              Nat.add_le_add_left hm _
          _ = Nat.choose (7 + y + 1) 6 + 147 := by
              rw [Nat.add_right_comm, hsK]
  calc q * 7 + 21 * ∑ i, b i
      = ∑ i, (7 + 21 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 6 + 147) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 6 + q * 147 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
