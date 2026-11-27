import Mathlib

private lemma choose_14_4 : Nat.choose 14 4 = 1001 := by
  have h0 : Nat.choose 14 0 = 1 := Nat.choose_zero_right 14
  have h1 : Nat.choose 14 1 * 1 = Nat.choose 14 0 * 14 := Nat.choose_succ_right_eq 14 0
  have h2 : Nat.choose 14 2 * 2 = Nat.choose 14 1 * 13 := Nat.choose_succ_right_eq 14 1
  have h3 : Nat.choose 14 3 * 3 = Nat.choose 14 2 * 12 := Nat.choose_succ_right_eq 14 2
  have h4 : Nat.choose 14 4 * 4 = Nat.choose 14 3 * 11 := Nat.choose_succ_right_eq 14 3
  omega

private lemma choose_14_5 : Nat.choose 14 5 = 2002 := by
  have h4 : Nat.choose 14 4 = 1001 := choose_14_4
  have h5 : Nat.choose 14 5 * 5 = Nat.choose 14 4 * 10 := Nat.choose_succ_right_eq 14 4
  omega

private lemma choose_13_5 : Nat.choose 13 5 = 1287 := by
  have h0 : Nat.choose 13 0 = 1 := Nat.choose_zero_right 13
  have h1 : Nat.choose 13 1 * 1 = Nat.choose 13 0 * 13 := Nat.choose_succ_right_eq 13 0
  have h2 : Nat.choose 13 2 * 2 = Nat.choose 13 1 * 12 := Nat.choose_succ_right_eq 13 1
  have h3 : Nat.choose 13 3 * 3 = Nat.choose 13 2 * 11 := Nat.choose_succ_right_eq 13 2
  have h4 : Nat.choose 13 4 * 4 = Nat.choose 13 3 * 10 := Nat.choose_succ_right_eq 13 3
  have h5 : Nat.choose 13 5 * 5 = Nat.choose 13 4 * 9 := Nat.choose_succ_right_eq 13 4
  omega

private lemma point_bound (x : ℕ) : 2002 + 1001 * x ≤ Nat.choose x 5 + 14014 := by
  by_cases h12 : x ≤ 12
  · omega
  · by_cases h13 : x = 13
    · subst h13
      have h : Nat.choose 13 5 = 1287 := choose_13_5
      omega
    · have hx : 14 ≤ x := by omega
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hx
      induction m with
      | zero =>
        simp only [Nat.add_zero]
        have h : Nat.choose 14 5 = 2002 := choose_14_5
        omega
      | succ m ih =>
        have hstep : Nat.choose (14 + (m + 1)) 5 = Nat.choose (14 + m) 4 + Nat.choose (14 + m) 5 := by
          rw [← Nat.add_assoc]
          exact Nat.choose_succ_succ' (14 + m) 4
        have hmono : Nat.choose 14 4 ≤ Nat.choose (14 + m) 4 :=
          Nat.choose_le_choose 4 (Nat.le_add_right 14 m)
        have h14 : Nat.choose 14 4 = 1001 := choose_14_4
        omega

theorem PEqualNP.Outside.L_hash_collision_lab_cert_5_14 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*2002)+1001*(∑ i,b i)≤(∑ i,Nat.choose (b i) 5)+q*14014 := by
  intro q b
  have hsum : ∑ i : Fin q, (2002 + 1001 * b i) ≤ ∑ i : Fin q, (Nat.choose (b i) 5 + 14014) :=
    Finset.sum_le_sum fun i _ => point_bound (b i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum] at hsum
  exact hsum
