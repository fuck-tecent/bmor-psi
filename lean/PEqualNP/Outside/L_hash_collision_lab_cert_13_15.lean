import Mathlib

/-- Order-13 occupancy support bound with the supporting line anchored at load 15.

The line `105 + 455 * load` is the tangent line of `load |-> choose load 13` at
load 15: it agrees with the binomial coefficient there and stays below it on both
sides, since `choose · 12` is monotone and the recurrence
`choose (m+1) 13 = choose m 12 + choose m 13` converts the excess over the line
into a sum of non-negative increments. Summing over the q buckets gives the bound. -/
theorem PEqualNP.Outside.L_hash_collision_lab_cert_13_15 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*105)+455*(∑ i,b i)≤(∑ i,Nat.choose (b i) 13)+q*6825 := by
  -- Finite region below the anchor: settled by kernel evaluation.
  have small : ∀ x, x < 15 → 105 + 455*x ≤ x.descFactorial 13 / Nat.factorial 13 + 6825 := by
    decide +kernel
  -- The anchor point itself is where the line touches the binomial coefficient.
  have base1 : 455 ≤ Nat.choose 15 12 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have base2 : 105 + 455*15 ≤ Nat.choose 15 13 + 6825 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  -- Per-bucket supporting-line inequality.
  have pt : ∀ x : ℕ, 105 + 455*x ≤ Nat.choose x 13 + 6825 := by
    intro x
    rcases Nat.lt_or_ge x 15 with hx | hx
    · rw [Nat.choose_eq_descFactorial_div_factorial]; exact small x hx
    · induction x, hx using Nat.le_induction with
      | base => exact base2
      | succ m hm ih =>
        have e : Nat.choose (m+1) 13 = Nat.choose m 12 + Nat.choose m 13 :=
          Nat.choose_succ_succ' m 12
        have hc : 455 ≤ Nat.choose m 12 := le_trans base1 (Nat.choose_le_choose 12 hm)
        generalize Nat.choose (m+1) 13 = A at e ⊢
        generalize Nat.choose m 12 = B at e hc
        generalize Nat.choose m 13 = C at e ih
        linarith
  intro q b
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => pt (b i))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum] at h
  generalize (∑ i, Nat.choose (b i) 13) = A at h ⊢
  generalize (∑ i, b i) = B at h ⊢
  omega
