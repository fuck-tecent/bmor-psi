import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_9_19 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*92378)+75582*(∑ i,b i)≤(∑ i,Nat.choose (b i) 9)+q*1436058 := by
  intro q b
  have slope : Nat.choose 19 8 = 75582 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    decide
  have atLoad : 92378 + 75582 * 19 ≤ Nat.choose 19 9 + 1436058 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    decide
  have pascal (k : ℕ) : Nat.choose (k + 1) 9 = Nat.choose k 8 + Nat.choose k 9 :=
    Nat.choose_succ_succ k 8
  have pointwise (n : ℕ) : 92378 + 75582 * n ≤ Nat.choose n 9 + 1436058 := by
    rcases le_total n 19 with h | h
    · induction h using Nat.decreasingInduction with
      | self => exact atLoad
      | of_succ k hk ih =>
        have hdiff := Nat.choose_le_choose 8 hk.le
        rw [slope] at hdiff
        rw [pascal] at ih
        omega
    · induction n, h using Nat.le_induction with
      | base => exact atLoad
      | succ k hk ih =>
        have hdiff := Nat.choose_le_choose 8 hk
        rw [slope] at hdiff
        calc
          92378 + 75582 * (k + 1) = (92378 + 75582 * k) + 75582 := by
            rw [Nat.mul_succ, Nat.add_assoc]
          _ ≤ (Nat.choose k 9 + 1436058) + Nat.choose k 8 := Nat.add_le_add ih hdiff
          _ = Nat.choose (k + 1) 9 + 1436058 := by rw [pascal]; ac_rfl
  simpa [Finset.sum_add_distrib, ← Finset.mul_sum] using
    (Finset.sum_le_sum (s := Finset.univ) fun i _ => pointwise (b i))
