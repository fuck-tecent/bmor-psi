import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_10_22 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*646646)+497420*(∑ i,b i)≤(∑ i,Nat.choose (b i) 10)+q*10943240 := by
  have small : ∀ x, x < 22 → 646646 + 497420*x ≤ x.descFactorial 10 / Nat.factorial 10 + 10943240 := by
    decide +kernel
  have base1 : 497420 ≤ Nat.choose 22 9 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have base2 : 646646 + 497420*22 ≤ Nat.choose 22 10 + 10943240 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have pt : ∀ x : ℕ, 646646 + 497420*x ≤ Nat.choose x 10 + 10943240 := by
    intro x
    rcases Nat.lt_or_ge x 22 with hx | hx
    · rw [Nat.choose_eq_descFactorial_div_factorial]; exact small x hx
    · induction x, hx using Nat.le_induction with
      | base => exact base2
      | succ m hm ih =>
        have e : Nat.choose (m+1) 10 = Nat.choose m 9 + Nat.choose m 10 :=
          Nat.choose_succ_succ' m 9
        have hc : 497420 ≤ Nat.choose m 9 := le_trans base1 (Nat.choose_le_choose 9 hm)
        generalize Nat.choose (m+1) 10 = A at e ⊢
        generalize Nat.choose m 9 = B at e hc
        generalize Nat.choose m 10 = C at e ih
        linarith
  intro q b
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => pt (b i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum] at h
  generalize (∑ i, Nat.choose (b i) 10) = A at h ⊢
  generalize (∑ i, b i) = B at h ⊢
  omega
