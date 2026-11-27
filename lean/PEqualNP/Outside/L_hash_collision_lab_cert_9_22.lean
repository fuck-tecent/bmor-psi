import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_9_22 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*497420)+319770*(∑ i,b i)≤(∑ i,Nat.choose (b i) 9)+q*7034940 := by
  have small : ∀ x, x < 22 → 497420 + 319770*x ≤ x.descFactorial 9 / Nat.factorial 9 + 7034940 := by
    decide +kernel
  have base1 : 319770 ≤ Nat.choose 22 8 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have base2 : 497420 + 319770*22 ≤ Nat.choose 22 9 + 7034940 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have pt : ∀ x : ℕ, 497420 + 319770*x ≤ Nat.choose x 9 + 7034940 := by
    intro x
    rcases Nat.lt_or_ge x 22 with hx | hx
    · rw [Nat.choose_eq_descFactorial_div_factorial]; exact small x hx
    · induction x, hx using Nat.le_induction with
      | base => exact base2
      | succ m hm ih =>
        have e : Nat.choose (m+1) 9 = Nat.choose m 8 + Nat.choose m 9 :=
          Nat.choose_succ_succ' m 8
        have hc : 319770 ≤ Nat.choose m 8 := le_trans base1 (Nat.choose_le_choose 8 hm)
        generalize Nat.choose (m+1) 9 = A at e ⊢
        generalize Nat.choose m 8 = B at e hc
        generalize Nat.choose m 9 = C at e ih
        linarith
  intro q b
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => pt (b i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum] at h
  generalize (∑ i, Nat.choose (b i) 9) = A at h ⊢
  generalize (∑ i, b i) = B at h ⊢
  omega
