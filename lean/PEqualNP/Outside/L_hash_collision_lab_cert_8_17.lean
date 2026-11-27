import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_8_17 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*24310)+19448*(∑ i,b i)≤(∑ i,Nat.choose (b i) 8)+q*330616 := by
  have small : ∀ x, x < 17 → 24310 + 19448*x ≤ x.descFactorial 8 / Nat.factorial 8 + 330616 := by
    decide +kernel
  have base1 : 19448 ≤ Nat.choose 17 7 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have base2 : 24310 + 19448*17 ≤ Nat.choose 17 8 + 330616 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have pt : ∀ x : ℕ, 24310 + 19448*x ≤ Nat.choose x 8 + 330616 := by
    intro x
    rcases Nat.lt_or_ge x 17 with hx | hx
    · rw [Nat.choose_eq_descFactorial_div_factorial]; exact small x hx
    · induction x, hx using Nat.le_induction with
      | base => exact base2
      | succ m hm ih =>
        have e : Nat.choose (m+1) 8 = Nat.choose m 7 + Nat.choose m 8 :=
          Nat.choose_succ_succ' m 7
        have hc : 19448 ≤ Nat.choose m 7 := le_trans base1 (Nat.choose_le_choose 7 hm)
        generalize Nat.choose (m+1) 8 = A at e ⊢
        generalize Nat.choose m 7 = B at e hc
        generalize Nat.choose m 8 = C at e ih
        linarith
  intro q b
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => pt (b i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum] at h
  generalize (∑ i, Nat.choose (b i) 8) = A at h ⊢
  generalize (∑ i, b i) = B at h ⊢
  omega
