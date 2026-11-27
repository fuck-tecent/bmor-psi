import Mathlib

/-- Order-2 occupancy support bound at load 2.

Each bucket contributes at least the discrete supporting line
`1 + 2 * load ≤ choose load 2 + 4`; summing this over all buckets
gives the stated inequality. -/
theorem PEqualNP.Outside.L_hash_collision_lab_cert_2_2 :
    ∀ (q : ℕ) (b : Fin q → ℕ),
      (q * 1) + 2 * (∑ i, b i) ≤ (∑ i, Nat.choose (b i) 2) + q * 4 := by
  intro q b
  -- The per-bucket supporting-line inequality.
  have hterm : ∀ m : ℕ, 1 + 2 * m ≤ Nat.choose m 2 + 4 := by
    intro m
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m <;> decide
    · refine Nat.le_induction ?base ?step m hm
      · decide
      · intro k hk ih
        have hc : Nat.choose (k + 1) 2 = Nat.choose k 2 + k := by
          have h : Nat.choose (k + 1) 2 = Nat.choose k 1 + Nat.choose k 2 :=
            Nat.choose_succ_succ k 1
          rw [h, Nat.choose_one_right]
          omega
        rw [hc]
        omega
  calc
    (q * 1) + 2 * (∑ i, b i) = ∑ i : Fin q, (1 + 2 * b i) := by
      rw [Finset.mul_sum]
      conv_rhs => rw [Finset.sum_add_distrib]
      simp
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 2 + 4) :=
      Finset.sum_le_sum (fun i _ => hterm (b i))
    _ = (∑ i : Fin q, Nat.choose (b i) 2) + q * 4 := by
      rw [Finset.sum_add_distrib]
      simp
