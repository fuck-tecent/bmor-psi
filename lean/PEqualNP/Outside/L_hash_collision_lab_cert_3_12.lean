import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_3_12 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*220)+66*(∑ i,b i)≤(∑ i,Nat.choose (b i) 3)+q*792 := by
  intro q b
  have hT : Nat.choose 12 2 = 66 := by
    rw [Nat.choose_eq_factorial_div_factorial] <;> norm_num
  have hT' : Nat.choose 12 3 = 220 := by
    rw [Nat.choose_eq_factorial_div_factorial] <;> norm_num
  have hle : 220 ≤ 792 := by norm_num
  have key : ∀ x : ℕ, 66 * x ≤ Nat.choose x 3 + (792 - 220) := by
    intro x
    by_cases hx : x ≤ 12
    · have head : ∀ n, ∀ y, 12 - y = n → y ≤ 12 → 66 * y ≤ Nat.choose y 3 + (792 - 220) := by
        intro n
        induction n with
        | zero =>
          intro y hy _
          have hyT : y = 12 := by omega
          subst hyT
          norm_num [hT', hT]
        | succ n ih =>
          intro y hy hleB
          have hstep : 66 * (y + 1) ≤ Nat.choose (y + 1) 3 + (792 - 220) :=
            ih (y + 1) (by omega) (by omega)
          have hpas : Nat.choose (y + 1) 3 = Nat.choose y 2 + Nat.choose y 3 :=
            Nat.choose_succ_succ y 2
          have hmono : Nat.choose y 2 ≤ 66 := by
            have h1 : Nat.choose y 2 ≤ Nat.choose 12 2 :=
              Nat.choose_le_choose 2 hleB
            omega
          rw [hpas] at hstep
          have hmul : 66 * (y + 1) = 66 * y + 66 := by ring
          rw [hmul] at hstep
          omega
      exact head (12 - x) x rfl hx
    · have hxB : 12 ≤ x := by omega
      have tail : ∀ x, 12 ≤ x → 66 * x ≤ Nat.choose x 3 + (792 - 220) := by
        intro x hx2
        induction x, hx2 using Nat.le_induction with
        | base => norm_num [hT', hT]
        | succ y hy ih =>
          have hmono : 66 ≤ Nat.choose y 2 := by
            have h1 : Nat.choose 12 2 ≤ Nat.choose y 2 :=
              Nat.choose_le_choose 2 hy
            omega
          have hpas : Nat.choose (y + 1) 3 = Nat.choose y 2 + Nat.choose y 3 :=
            Nat.choose_succ_succ y 2
          rw [hpas]
          have hmul : 66 * (y + 1) = 66 * y + 66 := by ring
          rw [hmul]
          omega
      exact tail x hxB
  have h1 : 66 * (∑ i, b i) ≤ ∑ i, (Nat.choose (b i) 3 + (792 - 220)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => key (b i))
  have h2 : ∑ i, (Nat.choose (b i) 3 + (792 - 220))
      = (∑ i, Nat.choose (b i) 3) + q * (792 - 220) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [h2] at h1
  have h3 : q * 220 + q * (792 - 220) = q * 792 := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hle]
  omega
