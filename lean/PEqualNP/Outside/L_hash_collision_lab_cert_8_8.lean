import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_8_8 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*1)+8*(∑ i,b i)≤(∑ i,Nat.choose (b i) 8)+q*64 := by
  intro q b
  have hstepK : ∀ k : ℕ, Nat.choose k 8 + Nat.choose k 7 = Nat.choose (k + 1) 8 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hstepK' : ∀ k : ℕ, Nat.choose k 7 + Nat.choose k 6 = Nat.choose (k + 1) 7 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hmono : ∀ y : ℕ, 8 ≤ Nat.choose (8 + y) 7 := by
    intro y
    induction y with
    | zero => decide
    | succ y ih =>
      have hs := hstepK' (8 + y)
      show 8 ≤ Nat.choose (8 + y + 1) 7
      omega
  have hpw : ∀ x : ℕ, 1 + 8 * x ≤ Nat.choose x 8 + 64 := by
    intro x
    rcases Nat.lt_or_ge x 8 with hlt | hge
    · interval_cases x <;> decide
    · obtain ⟨y, rfl⟩ : ∃ y, x = 8 + y := ⟨x - 8, by omega⟩
      clear hge
      induction y with
      | zero => decide
      | succ y ih =>
        have hsK := hstepK (8 + y)
        have hm := hmono y
        show 1 + 8 * (8 + y + 1) ≤ Nat.choose (8 + y + 1) 8 + 64
        calc 1 + 8 * (8 + y + 1)
            = (1 + 8 * (8 + y)) + 8 := by ring
          _ ≤ (Nat.choose (8 + y) 8 + 64) + 8 :=
              Nat.add_le_add_right ih 8
          _ ≤ (Nat.choose (8 + y) 8 + 64) + Nat.choose (8 + y) 7 :=
              Nat.add_le_add_left hm _
          _ = Nat.choose (8 + y + 1) 8 + 64 := by
              rw [Nat.add_right_comm, hsK]
  calc q * 1 + 8 * ∑ i, b i
      = ∑ i, (1 + 8 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 8 + 64) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 8 + q * 64 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
