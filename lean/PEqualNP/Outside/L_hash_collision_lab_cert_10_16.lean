import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_10_16 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*8008)+11440*(∑ i,b i)≤(∑ i,Nat.choose (b i) 10)+q*183040 := by
  intro q b
  have key : ∀ x : ℕ, 8008 + 11440*x ≤ Nat.choose x 10 + 183040 := by
    intro x
    by_cases hx : x < 16
    · interval_cases x <;> decide
    · have hx2 : 16 ≤ x := by omega
      refine Nat.le_induction ?_ ?_ x hx2
      · decide
      · intro n hn ih
        have hmono : 11440 ≤ Nat.choose n 9 := by
          have hC : Nat.choose 16 9 = 11440 := by decide
          have h := Nat.choose_le_choose 9 hn
          linarith
        have hch : Nat.choose (n+1) 10 = Nat.choose n 9 + Nat.choose n 10 :=
          Nat.choose_succ_succ' n 9
        linarith
  calc (q*8008)+11440*(∑ i, b i) = ∑ i : Fin q, (8008 + 11440*(b i)) := by
        rw [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp [smul_eq_mul]
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 10 + 183040) := Finset.sum_le_sum (fun i _ => key (b i))
    _ = (∑ i, Nat.choose (b i) 10)+q*183040 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
