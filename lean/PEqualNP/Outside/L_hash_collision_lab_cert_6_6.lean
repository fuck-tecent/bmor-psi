import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_6_6 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*1)+6*(∑ i,b i)≤(∑ i,Nat.choose (b i) 6)+q*36 := by
  intro q b
  have hstepK : ∀ k : ℕ, Nat.choose k 6 + Nat.choose k 5 = Nat.choose (k + 1) 6 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hstepK' : ∀ k : ℕ, Nat.choose k 5 + Nat.choose k 4 = Nat.choose (k + 1) 5 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hmono : ∀ y : ℕ, 6 ≤ Nat.choose (6 + y) 5 := by
    intro y
    induction y with
    | zero => decide
    | succ y ih =>
      have hs := hstepK' (6 + y)
      show 6 ≤ Nat.choose (6 + y + 1) 5
      omega
  have hpw : ∀ x : ℕ, 1 + 6 * x ≤ Nat.choose x 6 + 36 := by
    intro x
    rcases Nat.lt_or_ge x 6 with hlt | hge
    · interval_cases x <;> decide
    · obtain ⟨y, rfl⟩ : ∃ y, x = 6 + y := ⟨x - 6, by omega⟩
      clear hge
      induction y with
      | zero => decide
      | succ y ih =>
        have hsK := hstepK (6 + y)
        have hm := hmono y
        show 1 + 6 * (6 + y + 1) ≤ Nat.choose (6 + y + 1) 6 + 36
        calc 1 + 6 * (6 + y + 1)
            = (1 + 6 * (6 + y)) + 6 := by ring
          _ ≤ (Nat.choose (6 + y) 6 + 36) + 6 :=
              Nat.add_le_add_right ih 6
          _ ≤ (Nat.choose (6 + y) 6 + 36) + Nat.choose (6 + y) 5 :=
              Nat.add_le_add_left hm _
          _ = Nat.choose (6 + y + 1) 6 + 36 := by
              rw [Nat.add_right_comm, hsK]
  calc q * 1 + 6 * ∑ i, b i
      = ∑ i, (1 + 6 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 6 + 36) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 6 + q * 36 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
