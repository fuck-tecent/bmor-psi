import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_7_20 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*77520)+38760*(∑ i,b i)≤(∑ i,Nat.choose (b i) 7)+q*775200 := by
  have small : ∀ x, x < 20 → 77520 + 38760*x ≤ x.descFactorial 7 / Nat.factorial 7 + 775200 := by
    decide +kernel
  have base1 : 38760 ≤ Nat.choose 20 6 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have base2 : 77520 + 38760*20 ≤ Nat.choose 20 7 + 775200 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have pt : ∀ x : ℕ, 77520 + 38760*x ≤ Nat.choose x 7 + 775200 := by
    intro x
    rcases Nat.lt_or_ge x 20 with hx | hx
    · rw [Nat.choose_eq_descFactorial_div_factorial]; exact small x hx
    · induction x, hx using Nat.le_induction with
      | base => exact base2
      | succ m hm ih =>
        have e : Nat.choose (m+1) 7 = Nat.choose m 6 + Nat.choose m 7 :=
          Nat.choose_succ_succ' m 6
        have hc : 38760 ≤ Nat.choose m 6 := le_trans base1 (Nat.choose_le_choose 6 hm)
        generalize Nat.choose (m+1) 7 = A at e ⊢
        generalize Nat.choose m 6 = B at e hc
        generalize Nat.choose m 7 = C at e ih
        linarith
  intro q b
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => pt (b i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum] at h
  generalize (∑ i, Nat.choose (b i) 7) = A at h ⊢
  generalize (∑ i, b i) = B at h ⊢
  omega
