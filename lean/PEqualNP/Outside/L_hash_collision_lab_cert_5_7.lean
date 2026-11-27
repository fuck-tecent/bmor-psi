import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_5_7 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*21)+35*(∑ i,b i)≤(∑ i,Nat.choose (b i) 5)+q*245 := by
  intro q b
  have hstepK : ∀ k : ℕ, Nat.choose k 5 + Nat.choose k 4 = Nat.choose (k + 1) 5 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hstepK' : ∀ k : ℕ, Nat.choose k 4 + Nat.choose k 3 = Nat.choose (k + 1) 4 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hmono : ∀ y : ℕ, 35 ≤ Nat.choose (7 + y) 4 := by
    intro y
    induction y with
    | zero => decide
    | succ y ih =>
      have hs := hstepK' (7 + y)
      show 35 ≤ Nat.choose (7 + y + 1) 4
      omega
  have hpw : ∀ x : ℕ, 21 + 35 * x ≤ Nat.choose x 5 + 245 := by
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
        show 21 + 35 * (7 + y + 1) ≤ Nat.choose (7 + y + 1) 5 + 245
        calc 21 + 35 * (7 + y + 1)
            = (21 + 35 * (7 + y)) + 35 := by ring
          _ ≤ (Nat.choose (7 + y) 5 + 245) + 35 :=
              Nat.add_le_add_right ih 35
          _ ≤ (Nat.choose (7 + y) 5 + 245) + Nat.choose (7 + y) 4 :=
              Nat.add_le_add_left hm _
          _ = Nat.choose (7 + y + 1) 5 + 245 := by
              rw [Nat.add_right_comm, hsK]
  calc q * 21 + 35 * ∑ i, b i
      = ∑ i, (21 + 35 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 5 + 245) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 5 + q * 245 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
