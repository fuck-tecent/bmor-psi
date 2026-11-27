import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_3_9 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*84)+36*(∑ i,b i)≤(∑ i,Nat.choose (b i) 3)+q*324 := by
  have small : ∀ x, x < 9 → 84 + 36*x ≤ x.descFactorial 3 / Nat.factorial 3 + 324 := by
    decide +kernel
  have base1 : 36 ≤ Nat.choose 9 2 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have base2 : 84 + 36*9 ≤ Nat.choose 9 3 + 324 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have pt : ∀ x : ℕ, 84 + 36*x ≤ Nat.choose x 3 + 324 := by
    intro x
    rcases Nat.lt_or_ge x 9 with hx | hx
    · rw [Nat.choose_eq_descFactorial_div_factorial]; exact small x hx
    · induction x, hx using Nat.le_induction with
      | base => exact base2
      | succ m hm ih =>
        have e : Nat.choose (m+1) 3 = Nat.choose m 2 + Nat.choose m 3 :=
          Nat.choose_succ_succ' m 2
        have hc : 36 ≤ Nat.choose m 2 := le_trans base1 (Nat.choose_le_choose 2 hm)
        generalize Nat.choose (m+1) 3 = A at e ⊢
        generalize Nat.choose m 2 = B at e hc
        generalize Nat.choose m 3 = C at e ih
        linarith
  intro q b
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => pt (b i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum] at h
  generalize (∑ i, Nat.choose (b i) 3) = A at h ⊢
  generalize (∑ i, b i) = B at h ⊢
  omega
