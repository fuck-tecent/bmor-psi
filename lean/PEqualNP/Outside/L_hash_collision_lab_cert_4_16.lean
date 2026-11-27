import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_4_16 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*1820)+560*(∑ i,b i)≤(∑ i,Nat.choose (b i) 4)+q*8960 := by
  have small : ∀ x, x < 16 → 1820 + 560*x ≤ x.descFactorial 4 / Nat.factorial 4 + 8960 := by
    decide +kernel
  have base1 : 560 ≤ Nat.choose 16 3 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have base2 : 1820 + 560*16 ≤ Nat.choose 16 4 + 8960 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have pt : ∀ x : ℕ, 1820 + 560*x ≤ Nat.choose x 4 + 8960 := by
    intro x
    rcases Nat.lt_or_ge x 16 with hx | hx
    · rw [Nat.choose_eq_descFactorial_div_factorial]; exact small x hx
    · induction x, hx using Nat.le_induction with
      | base => exact base2
      | succ m hm ih =>
        have e : Nat.choose (m+1) 4 = Nat.choose m 3 + Nat.choose m 4 :=
          Nat.choose_succ_succ' m 3
        have hc : 560 ≤ Nat.choose m 3 := le_trans base1 (Nat.choose_le_choose 3 hm)
        generalize Nat.choose (m+1) 4 = A at e ⊢
        generalize Nat.choose m 3 = B at e hc
        generalize Nat.choose m 4 = C at e ih
        linarith
  intro q b
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => pt (b i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum] at h
  generalize (∑ i, Nat.choose (b i) 4) = A at h ⊢
  generalize (∑ i, b i) = B at h ⊢
  omega
