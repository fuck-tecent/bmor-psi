import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_6_11 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*462)+462*(∑ i,b i)≤(∑ i,Nat.choose (b i) 6)+q*5082 := by
  have small : ∀ x, x < 11 → 462 + 462*x ≤ x.descFactorial 6 / Nat.factorial 6 + 5082 := by
    decide +kernel
  have base1 : 462 ≤ Nat.choose 11 5 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have base2 : 462 + 462*11 ≤ Nat.choose 11 6 + 5082 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have pt : ∀ x : ℕ, 462 + 462*x ≤ Nat.choose x 6 + 5082 := by
    intro x
    rcases Nat.lt_or_ge x 11 with hx | hx
    · rw [Nat.choose_eq_descFactorial_div_factorial]; exact small x hx
    · induction x, hx using Nat.le_induction with
      | base => exact base2
      | succ m hm ih =>
        have e : Nat.choose (m+1) 6 = Nat.choose m 5 + Nat.choose m 6 :=
          Nat.choose_succ_succ' m 5
        have hc : 462 ≤ Nat.choose m 5 := le_trans base1 (Nat.choose_le_choose 5 hm)
        generalize Nat.choose (m+1) 6 = A at e ⊢
        generalize Nat.choose m 5 = B at e hc
        generalize Nat.choose m 6 = C at e ih
        linarith
  intro q b
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => pt (b i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum] at h
  generalize (∑ i, Nat.choose (b i) 6) = A at h ⊢
  generalize (∑ i, b i) = B at h ⊢
  omega
