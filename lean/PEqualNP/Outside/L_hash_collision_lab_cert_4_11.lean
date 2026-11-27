import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_4_11 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*330)+165*(∑ i,b i)≤(∑ i,Nat.choose (b i) 4)+q*1815 := by
  intro q b
  have hT : Nat.choose 11 3 = 165 := by
    rw [Nat.choose_eq_factorial_div_factorial] <;> norm_num
  have hT' : Nat.choose 11 4 = 330 := by
    rw [Nat.choose_eq_factorial_div_factorial] <;> norm_num
  have hle : 330 ≤ 1815 := by norm_num
  have key : ∀ x : ℕ, 165 * x ≤ Nat.choose x 4 + (1815 - 330) := by
    intro x
    by_cases hx : x ≤ 11
    · have head : ∀ n, ∀ y, 11 - y = n → y ≤ 11 → 165 * y ≤ Nat.choose y 4 + (1815 - 330) := by
        intro n
        induction n with
        | zero =>
          intro y hy _
          have hyT : y = 11 := by omega
          subst hyT
          norm_num [hT', hT]
        | succ n ih =>
          intro y hy hleB
          have hstep : 165 * (y + 1) ≤ Nat.choose (y + 1) 4 + (1815 - 330) :=
            ih (y + 1) (by omega) (by omega)
          have hpas : Nat.choose (y + 1) 4 = Nat.choose y 3 + Nat.choose y 4 :=
            Nat.choose_succ_succ y 3
          have hmono : Nat.choose y 3 ≤ 165 := by
            have h1 : Nat.choose y 3 ≤ Nat.choose 11 3 :=
              Nat.choose_le_choose 3 hleB
            omega
          rw [hpas] at hstep
          have hmul : 165 * (y + 1) = 165 * y + 165 := by ring
          rw [hmul] at hstep
          omega
      exact head (11 - x) x rfl hx
    · have hxB : 11 ≤ x := by omega
      have tail : ∀ x, 11 ≤ x → 165 * x ≤ Nat.choose x 4 + (1815 - 330) := by
        intro x hx2
        induction x, hx2 using Nat.le_induction with
        | base => norm_num [hT', hT]
        | succ y hy ih =>
          have hmono : 165 ≤ Nat.choose y 3 := by
            have h1 : Nat.choose 11 3 ≤ Nat.choose y 3 :=
              Nat.choose_le_choose 3 hy
            omega
          have hpas : Nat.choose (y + 1) 4 = Nat.choose y 3 + Nat.choose y 4 :=
            Nat.choose_succ_succ y 3
          rw [hpas]
          have hmul : 165 * (y + 1) = 165 * y + 165 := by ring
          rw [hmul]
          omega
      exact tail x hxB
  have h1 : 165 * (∑ i, b i) ≤ ∑ i, (Nat.choose (b i) 4 + (1815 - 330)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => key (b i))
  have h2 : ∑ i, (Nat.choose (b i) 4 + (1815 - 330))
      = (∑ i, Nat.choose (b i) 4) + q * (1815 - 330) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [h2] at h1
  have h3 : q * 330 + q * (1815 - 330) = q * 1815 := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hle]
  omega
