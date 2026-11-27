import Mathlib

/-- Order-8 occupancy support bound with the supporting line anchored at load 9.

The line `9 + 36 * load` is the tangent line of `load |-> choose load 8` at
load 9: it agrees with the binomial coefficient there and stays below it on both
sides, since `choose · 7` is monotone and the recurrence
`choose (m+1) 8 = choose m 7 + choose m 8` converts the excess over the line
into a sum of non-negative increments. Summing over the q buckets gives the bound. -/
theorem PEqualNP.Outside.L_hash_collision_lab_cert_8_9 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*9)+36*(∑ i,b i)≤(∑ i,Nat.choose (b i) 8)+q*324 := by
  -- Finite region below the anchor: settled by kernel evaluation.
  have small : ∀ x, x < 9 → 9 + 36*x ≤ x.descFactorial 8 / Nat.factorial 8 + 324 := by
    decide +kernel
  -- The anchor point itself is where the line touches the binomial coefficient.
  have base1 : 36 ≤ Nat.choose 9 7 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have base2 : 9 + 36*9 ≤ Nat.choose 9 8 + 324 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  -- Per-bucket supporting-line inequality.
  have pt : ∀ x : ℕ, 9 + 36*x ≤ Nat.choose x 8 + 324 := by
    intro x
    rcases Nat.lt_or_ge x 9 with hx | hx
    · rw [Nat.choose_eq_descFactorial_div_factorial]; exact small x hx
    · induction x, hx using Nat.le_induction with
      | base => exact base2
      | succ m hm ih =>
        have e : Nat.choose (m+1) 8 = Nat.choose m 7 + Nat.choose m 8 :=
          Nat.choose_succ_succ' m 7
        have hc : 36 ≤ Nat.choose m 7 := le_trans base1 (Nat.choose_le_choose 7 hm)
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
