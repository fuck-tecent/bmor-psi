import Mathlib

theorem Conjectures.Goldbach.AlmostPrimeParityDetector :
    ∀ (N M : ℕ), let Adm := (Finset.range N).filter (fun p => Nat.Prime p ∧ M < N - p ∧ (Nat.Prime (N - p) ∨ ∃ r ∈ Finset.Icc 2 N, ∃ q ∈ Finset.Icc 2 N, Nat.Prime r ∧ Nat.Prime q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q)); let D : ℤ := (Adm.card : ℤ); let J : ℤ := ∑ p ∈ Adm, (-1 : ℤ) ^ (N - p).primeFactorsList.length; let R : ℤ := ((Adm.filter (fun p => Nat.Prime (N - p))).card : ℤ); let Semi := (Finset.Icc 2 N).filter (fun r => Nat.Prime r); D - J = 2 * R ∧ J + R = ∑ r ∈ Semi, ((Adm.filter (fun p => ∃ q ∈ Finset.Icc 2 N, Nat.Prime q ∧ r < q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q)).card : ℤ) := by
  intro N M Adm D J R Semi
  have hmem : ∀ p, p ∈ Adm ↔ (p ∈ Finset.range N ∧ Nat.Prime p ∧ M < N - p ∧ (Nat.Prime (N - p) ∨ ∃ r ∈ Finset.Icc 2 N, ∃ q ∈ Finset.Icc 2 N, Nat.Prime r ∧ Nat.Prime q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q)) := by
    intro p
    dsimp only [Adm]
    rw [Finset.mem_filter]
  have hJform : J = ∑ p ∈ Adm, (if Nat.Prime (N - p) then (-1 : ℤ) else 1) := by
    dsimp only [J]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hmem p] at hp
    obtain ⟨-, hpp, hlt, hdisj⟩ := hp
    by_cases hnp : Nat.Prime (N - p)
    · rw [Nat.primeFactorsList_prime hnp]
      simp [hnp]
    · obtain hpr | ⟨r, -, q, -, hpr, hpq, -, hEq⟩ := hdisj
      · exact absurd hpr hnp
      · have hlen : (N - p).primeFactorsList.length = 2 := by
          rw [hEq, (Nat.perm_primeFactorsList_mul (Nat.Prime.pos hpr).ne' (Nat.Prime.pos hpq).ne').length_eq]
          rw [Nat.primeFactorsList_prime hpr, Nat.primeFactorsList_prime hpq]
          rfl
        rw [hlen]
        simp [hnp]
  have hRform : R = ∑ p ∈ Adm, (if Nat.Prime (N - p) then (1 : ℤ) else 0) := by
    dsimp only [R]
    rw [Finset.natCast_card_filter]
  constructor
  · have hD : D = ∑ p ∈ Adm, (1 : ℤ) := by
      dsimp only [D]
      rw [Finset.card_eq_sum_ones]
      push_cast
      rfl
    rw [hD, hJform, ← Finset.sum_sub_distrib]
    have hpt : ∀ p ∈ Adm, (1 : ℤ) - (if Nat.Prime (N - p) then (-1 : ℤ) else 1) = (if Nat.Prime (N - p) then (2 : ℤ) else 0) := by
      intro p hp
      by_cases h : Nat.Prime (N - p) <;> simp [h]
    rw [Finset.sum_congr rfl hpt]
    have hmul : ∑ p ∈ Adm, (if Nat.Prime (N - p) then (2 : ℤ) else 0) = 2 * ∑ p ∈ Adm, (if Nat.Prime (N - p) then (1 : ℤ) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      by_cases h : Nat.Prime (N - p) <;> simp [h]
    rw [hmul]
    congr 1
    exact hRform.symm
  · rw [hJform, hRform, ← Finset.sum_add_distrib]
    have hpt2 : ∀ p ∈ Adm, (if Nat.Prime (N - p) then (-1 : ℤ) else 1) + (if Nat.Prime (N - p) then (1 : ℤ) else 0) = (if Nat.Prime (N - p) then (0 : ℤ) else 1) := by
      intro p hp
      by_cases h : Nat.Prime (N - p) <;> simp [h]
    rw [Finset.sum_congr rfl hpt2]
    have hRHS : (∑ r ∈ Semi, ((Adm.filter (fun p => ∃ q ∈ Finset.Icc 2 N, Nat.Prime q ∧ r < q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q)).card : ℤ))
        = ∑ p ∈ Adm, ∑ r ∈ Semi, (if (∃ q ∈ Finset.Icc 2 N, Nat.Prime q ∧ r < q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q) then (1 : ℤ) else 0) := by
      rw [show (∑ r ∈ Semi, ((Adm.filter (fun p => ∃ q ∈ Finset.Icc 2 N, Nat.Prime q ∧ r < q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q)).card : ℤ))
          = ∑ r ∈ Semi, ∑ p ∈ Adm, (if (∃ q ∈ Finset.Icc 2 N, Nat.Prime q ∧ r < q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q) then (1 : ℤ) else 0) from
        Finset.sum_congr rfl (fun r hr => Finset.natCast_card_filter (fun p => ∃ q ∈ Finset.Icc 2 N, Nat.Prime q ∧ r < q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q) Adm)]
      rw [Finset.sum_comm]
    rw [hRHS]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hmem p] at hp
    obtain ⟨-, hpp, hlt, hdisj⟩ := hp
    by_cases hnp : Nat.Prime (N - p)
    · have hzero : (∑ r ∈ Semi, (if (∃ q ∈ Finset.Icc 2 N, Nat.Prime q ∧ r < q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q) then (1 : ℤ) else 0)) = 0 := by
        refine Finset.sum_eq_zero (fun r hr => ?_)
        have hfalse : ¬ (∃ q ∈ Finset.Icc 2 N, Nat.Prime q ∧ r < q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q) := by
          rintro ⟨q, hqIcc, hqprime, hrq, hr10, hEq⟩
          have hrprime : Nat.Prime r := (Finset.mem_filter.1 hr).2
          have hr2 : 2 ≤ r := (Finset.mem_Icc.1 (Finset.mem_filter.1 hr).1).1
          have hq2 : 2 ≤ q := (Finset.mem_Icc.1 hqIcc).1
          have hdvd : r ∣ N - p := by
            rw [hEq]
            exact dvd_mul_right r q
          rcases hnp.eq_one_or_self_of_dvd r hdvd with h1 | h2
          · omega
          · have hq1 : q = 1 := by
              have hNp : 0 < N - p := hnp.pos
              have hmul : (N - p) * 1 = (N - p) * q := by
                rw [Nat.mul_one]
                rw [h2] at hEq
                exact hEq
              exact Nat.eq_of_mul_eq_mul_left hNp hmul.symm
            omega
        rw [if_neg hfalse]
      rw [if_pos hnp, hzero]
    · obtain hpr | ⟨r0, hr0Icc, q0, hq0Icc, hpr0, hpq0, hr10, hEq0⟩ := hdisj
      · exact absurd hpr hnp
      · have hr0ltq0 : r0 < q0 := by
          by_contra hle
          push_neg at hle
          have h1 : q0 ^ 9 ≤ r0 ^ 9 := Nat.pow_le_pow_left hle 9
          have h2 : r0 ^ 9 < r0 ^ 10 := by
            simpa using Nat.pow_lt_pow_succ (a := r0) (n := 9) hpr0.one_lt
          exact absurd (le_trans hr10 h1) (not_le.mpr h2)
        have hr0Semi : r0 ∈ Semi := by
          dsimp only [Semi]
          rw [Finset.mem_filter]
          exact ⟨hr0Icc, hpr0⟩
        have hcond : (∃ q ∈ Finset.Icc 2 N, Nat.Prime q ∧ r0 < q ∧ r0 ^ 10 ≤ q ^ 9 ∧ N - p = r0 * q) :=
          ⟨q0, hq0Icc, hpq0, hr0ltq0, hr10, hEq0⟩
        have huniq : ∀ r ∈ Semi, (∃ q ∈ Finset.Icc 2 N, Nat.Prime q ∧ r < q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q) → r = r0 := by
          intro r hrSemi hq
          obtain ⟨q, hqIcc, hqprime, hrq, hr10', hEq⟩ := hq
          have hrprime : Nat.Prime r := (Finset.mem_filter.1 hrSemi).2
          have hr2 : 2 ≤ r := (Finset.mem_Icc.1 (Finset.mem_filter.1 hrSemi).1).1
          have hdvd : r ∣ r0 * q0 := by
            have h1 : r ∣ N - p := by
              rw [hEq]
              exact dvd_mul_right r q
            rwa [hEq0] at h1
          rcases (Nat.Prime.dvd_mul hrprime).mp hdvd with h | h
          · exact (hpr0.eq_one_or_self_of_dvd r h).resolve_left (by omega)
          · have hrq0 : r = q0 := (hpq0.eq_one_or_self_of_dvd r h).resolve_left (by omega)
            have hqeq : q = r0 := by
              have hmul : q0 * q = q0 * r0 := by
                calc q0 * q = r * q := by rw [hrq0]
                  _ = N - p := by rw [hEq]
                  _ = r0 * q0 := hEq0
                  _ = q0 * r0 := by rw [mul_comm]
              exact Nat.eq_of_mul_eq_mul_left hpq0.pos hmul
            rw [hrq0] at hr10'
            rw [hqeq] at hr10'
            have h1 : r0 ^ 9 < q0 ^ 9 := Nat.pow_lt_pow_left hr0ltq0 (by norm_num)
            have h2 : q0 ^ 9 < q0 ^ 10 := Nat.pow_lt_pow_right hpq0.one_lt (by norm_num)
            exact absurd (lt_trans h2 (lt_of_le_of_lt hr10' h1)) (lt_irrefl (q0 ^ 9))
        have hsum1 : (∑ r ∈ Semi, (if (∃ q ∈ Finset.Icc 2 N, Nat.Prime q ∧ r < q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q) then (1 : ℤ) else 0)) = 1 := by
          rw [Finset.sum_eq_single r0]
          · rw [if_pos hcond]
          · intro r hr hrne
            have hfalse : ¬ (∃ q ∈ Finset.Icc 2 N, Nat.Prime q ∧ r < q ∧ r ^ 10 ≤ q ^ 9 ∧ N - p = r * q) := fun h => hrne (huniq r hr h)
            rw [if_neg hfalse]
          · intro hnot
            exact absurd hr0Semi hnot
        rw [if_neg hnp, hsum1]
