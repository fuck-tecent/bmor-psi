import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_3_15 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*455)+105*(∑ i,b i)≤(∑ i,Nat.choose (b i) 3)+q*1575 := by
  intro q b
  have hT : Nat.choose 15 2 = 105 := by
    rw [Nat.choose_eq_factorial_div_factorial] <;> norm_num
  have hT' : Nat.choose 15 3 = 455 := by
    rw [Nat.choose_eq_factorial_div_factorial] <;> norm_num
  have hle : 455 ≤ 1575 := by norm_num
  have key : ∀ x : ℕ, 105 * x ≤ Nat.choose x 3 + (1575 - 455) := by
    intro x
    by_cases hx : x ≤ 15
    · have head : ∀ n, ∀ y, 15 - y = n → y ≤ 15 → 105 * y ≤ Nat.choose y 3 + (1575 - 455) := by
        intro n
        induction n with
        | zero =>
          intro y hy _
          have hyT : y = 15 := by omega
          subst hyT
          norm_num [hT', hT]
        | succ n ih =>
          intro y hy hleB
          have hstep : 105 * (y + 1) ≤ Nat.choose (y + 1) 3 + (1575 - 455) :=
            ih (y + 1) (by omega) (by omega)
          have hpas : Nat.choose (y + 1) 3 = Nat.choose y 2 + Nat.choose y 3 :=
            Nat.choose_succ_succ y 2
          have hmono : Nat.choose y 2 ≤ 105 := by
            have h1 : Nat.choose y 2 ≤ Nat.choose 15 2 :=
              Nat.choose_le_choose 2 hleB
            omega
          rw [hpas] at hstep
          have hmul : 105 * (y + 1) = 105 * y + 105 := by ring
          rw [hmul] at hstep
          omega
      exact head (15 - x) x rfl hx
    · have hxB : 15 ≤ x := by omega
      have tail : ∀ x, 15 ≤ x → 105 * x ≤ Nat.choose x 3 + (1575 - 455) := by
        intro x hx2
        induction x, hx2 using Nat.le_induction with
        | base => norm_num [hT', hT]
        | succ y hy ih =>
          have hmono : 105 ≤ Nat.choose y 2 := by
            have h1 : Nat.choose 15 2 ≤ Nat.choose y 2 :=
              Nat.choose_le_choose 2 hy
            omega
          have hpas : Nat.choose (y + 1) 3 = Nat.choose y 2 + Nat.choose y 3 :=
            Nat.choose_succ_succ y 2
          rw [hpas]
          have hmul : 105 * (y + 1) = 105 * y + 105 := by ring
          rw [hmul]
          omega
      exact tail x hxB
  have h1 : 105 * (∑ i, b i) ≤ ∑ i, (Nat.choose (b i) 3 + (1575 - 455)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => key (b i))
  have h2 : ∑ i, (Nat.choose (b i) 3 + (1575 - 455))
      = (∑ i, Nat.choose (b i) 3) + q * (1575 - 455) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [h2] at h1
  have h3 : q * 455 + q * (1575 - 455) = q * 1575 := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hle]
  omega
