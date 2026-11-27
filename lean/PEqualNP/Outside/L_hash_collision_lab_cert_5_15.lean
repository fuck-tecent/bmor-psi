import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_5_15 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*3003)+1365*(∑ i,b i)≤(∑ i,Nat.choose (b i) 5)+q*20475 := by
  have small : ∀ x, x < 15 → 3003 + 1365*x ≤ x.descFactorial 5 / Nat.factorial 5 + 20475 := by
    decide +kernel
  have base1 : 1365 ≤ Nat.choose 15 4 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have base2 : 3003 + 1365*15 ≤ Nat.choose 15 5 + 20475 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have pt : ∀ x : ℕ, 3003 + 1365*x ≤ Nat.choose x 5 + 20475 := by
    intro x
    rcases Nat.lt_or_ge x 15 with hx | hx
    · rw [Nat.choose_eq_descFactorial_div_factorial]; exact small x hx
    · induction x, hx using Nat.le_induction with
      | base => exact base2
      | succ m hm ih =>
        have e : Nat.choose (m+1) 5 = Nat.choose m 4 + Nat.choose m 5 :=
          Nat.choose_succ_succ' m 4
        have hc : 1365 ≤ Nat.choose m 4 := le_trans base1 (Nat.choose_le_choose 4 hm)
        generalize Nat.choose (m+1) 5 = A at e ⊢
        generalize Nat.choose m 4 = B at e hc
        generalize Nat.choose m 5 = C at e ih
        linarith
  intro q b
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => pt (b i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum] at h
  generalize (∑ i, Nat.choose (b i) 5) = A at h ⊢
  generalize (∑ i, b i) = B at h ⊢
  omega
