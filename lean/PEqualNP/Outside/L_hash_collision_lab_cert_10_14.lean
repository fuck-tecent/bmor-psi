import Mathlib

/-- Order-10 occupancy support bound with the supporting line anchored at load 14.

The line `1001 + 2002 * load` is the tangent line of `load |-> choose load 10` at
load 14: it agrees with the binomial coefficient there and stays below it on both
sides, since `choose · 9` is monotone and the recurrence
`choose (m+1) 10 = choose m 9 + choose m 10` converts the excess over the line
into a sum of non-negative increments. Summing over the q buckets gives the bound. -/
theorem PEqualNP.Outside.L_hash_collision_lab_cert_10_14 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*1001)+2002*(∑ i,b i)≤(∑ i,Nat.choose (b i) 10)+q*28028 := by
  -- Finite region below the anchor: settled by kernel evaluation.
  have small : ∀ x, x < 14 → 1001 + 2002*x ≤ x.descFactorial 10 / Nat.factorial 10 + 28028 := by
    decide +kernel
  -- The anchor point itself is where the line touches the binomial coefficient.
  have base1 : 2002 ≤ Nat.choose 14 9 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have base2 : 1001 + 2002*14 ≤ Nat.choose 14 10 + 28028 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  -- Per-bucket supporting-line inequality.
  have pt : ∀ x : ℕ, 1001 + 2002*x ≤ Nat.choose x 10 + 28028 := by
    intro x
    rcases Nat.lt_or_ge x 14 with hx | hx
    · rw [Nat.choose_eq_descFactorial_div_factorial]; exact small x hx
    · induction x, hx using Nat.le_induction with
      | base => exact base2
      | succ m hm ih =>
        have e : Nat.choose (m+1) 10 = Nat.choose m 9 + Nat.choose m 10 :=
          Nat.choose_succ_succ' m 9
        have hc : 2002 ≤ Nat.choose m 9 := le_trans base1 (Nat.choose_le_choose 9 hm)
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
