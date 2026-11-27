import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_7_8 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*8)+28*(∑ i,b i)≤(∑ i,Nat.choose (b i) 7)+q*224 := by
  intro q b
  have hstepK : ∀ k : ℕ, Nat.choose k 7 + Nat.choose k 6 = Nat.choose (k + 1) 7 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hstepK' : ∀ k : ℕ, Nat.choose k 6 + Nat.choose k 5 = Nat.choose (k + 1) 6 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hmono : ∀ y : ℕ, 28 ≤ Nat.choose (8 + y) 6 := by
    intro y
    induction y with
    | zero => decide
    | succ y ih =>
      have hs := hstepK' (8 + y)
      show 28 ≤ Nat.choose (8 + y + 1) 6
      omega
  have hpw : ∀ x : ℕ, 8 + 28 * x ≤ Nat.choose x 7 + 224 := by
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
        show 8 + 28 * (8 + y + 1) ≤ Nat.choose (8 + y + 1) 7 + 224
        calc 8 + 28 * (8 + y + 1)
            = (8 + 28 * (8 + y)) + 28 := by ring
          _ ≤ (Nat.choose (8 + y) 7 + 224) + 28 :=
              Nat.add_le_add_right ih 28
          _ ≤ (Nat.choose (8 + y) 7 + 224) + Nat.choose (8 + y) 6 :=
              Nat.add_le_add_left hm _
          _ = Nat.choose (8 + y + 1) 7 + 224 := by
              rw [Nat.add_right_comm, hsK]
  calc q * 8 + 28 * ∑ i, b i
      = ∑ i, (8 + 28 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 7 + 224) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 7 + q * 224 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
