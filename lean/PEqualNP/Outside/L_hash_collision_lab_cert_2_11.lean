import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_2_11 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*55)+11*(∑ i,b i)≤(∑ i,Nat.choose (b i) 2)+q*121 := by
  have small : ∀ x, x < 11 → 55 + 11*x ≤ x.descFactorial 2 / Nat.factorial 2 + 121 := by
    decide +kernel
  have base1 : 11 ≤ Nat.choose 11 1 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have base2 : 55 + 11*11 ≤ Nat.choose 11 2 + 121 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have pt : ∀ x : ℕ, 55 + 11*x ≤ Nat.choose x 2 + 121 := by
    intro x
    rcases Nat.lt_or_ge x 11 with hx | hx
    · rw [Nat.choose_eq_descFactorial_div_factorial]; exact small x hx
    · induction x, hx using Nat.le_induction with
      | base => exact base2
      | succ m hm ih =>
        have e : Nat.choose (m+1) 2 = Nat.choose m 1 + Nat.choose m 2 :=
          Nat.choose_succ_succ' m 1
        have hc : 11 ≤ Nat.choose m 1 := le_trans base1 (Nat.choose_le_choose 1 hm)
        generalize Nat.choose (m+1) 2 = A at e ⊢
        generalize Nat.choose m 1 = B at e hc
        generalize Nat.choose m 2 = C at e ih
        linarith
  intro q b
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => pt (b i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum] at h
  generalize (∑ i, Nat.choose (b i) 2) = A at h ⊢
  generalize (∑ i, b i) = B at h ⊢
  omega
