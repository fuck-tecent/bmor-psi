import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_5_18 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*8568)+3060*(∑ i,b i)≤(∑ i,Nat.choose (b i) 5)+q*55080 := by
  have small : ∀ x, x < 18 → 8568 + 3060*x ≤ x.descFactorial 5 / Nat.factorial 5 + 55080 := by
    decide +kernel
  have base1 : 3060 ≤ Nat.choose 18 4 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have base2 : 8568 + 3060*18 ≤ Nat.choose 18 5 + 55080 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have pt : ∀ x : ℕ, 8568 + 3060*x ≤ Nat.choose x 5 + 55080 := by
    intro x
    rcases Nat.lt_or_ge x 18 with hx | hx
    · rw [Nat.choose_eq_descFactorial_div_factorial]; exact small x hx
    · induction x, hx using Nat.le_induction with
      | base => exact base2
      | succ m hm ih =>
        have e : Nat.choose (m+1) 5 = Nat.choose m 4 + Nat.choose m 5 :=
          Nat.choose_succ_succ' m 4
        have hc : 3060 ≤ Nat.choose m 4 := le_trans base1 (Nat.choose_le_choose 4 hm)
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
