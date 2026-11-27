import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_6_8 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*28)+56*(∑ i,b i)≤(∑ i,Nat.choose (b i) 6)+q*448 := by
  intro q b
  have hstepK : ∀ k : ℕ, Nat.choose k 6 + Nat.choose k 5 = Nat.choose (k + 1) 6 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hstepK' : ∀ k : ℕ, Nat.choose k 5 + Nat.choose k 4 = Nat.choose (k + 1) 5 := by
    intro k
    rw [Nat.choose_succ_succ']
    exact Nat.add_comm _ _
  have hmono : ∀ y : ℕ, 56 ≤ Nat.choose (8 + y) 5 := by
    intro y
    induction y with
    | zero => decide
    | succ y ih =>
      have hs := hstepK' (8 + y)
      show 56 ≤ Nat.choose (8 + y + 1) 5
      omega
  have hpw : ∀ x : ℕ, 28 + 56 * x ≤ Nat.choose x 6 + 448 := by
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
        show 28 + 56 * (8 + y + 1) ≤ Nat.choose (8 + y + 1) 6 + 448
        calc 28 + 56 * (8 + y + 1)
            = (28 + 56 * (8 + y)) + 56 := by ring
          _ ≤ (Nat.choose (8 + y) 6 + 448) + 56 :=
              Nat.add_le_add_right ih 56
          _ ≤ (Nat.choose (8 + y) 6 + 448) + Nat.choose (8 + y) 5 :=
              Nat.add_le_add_left hm _
          _ = Nat.choose (8 + y + 1) 6 + 448 := by
              rw [Nat.add_right_comm, hsK]
  calc q * 28 + 56 * ∑ i, b i
      = ∑ i, (28 + 56 * b i) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ i, (Nat.choose (b i) 6 + 448) := Finset.sum_le_sum fun i _ => hpw (b i)
    _ = ∑ i, Nat.choose (b i) 6 + q * 448 := by
          simp [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin]
