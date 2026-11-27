import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_4_4 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*1)+4*(∑ i,b i)≤(∑ i,Nat.choose (b i) 4)+q*16 := by
  intro q b
  have hT : Nat.choose 4 3 = 4 := by
    rw [Nat.choose_eq_factorial_div_factorial] <;> norm_num
  have hT' : Nat.choose 4 4 = 1 := by
    rw [Nat.choose_eq_factorial_div_factorial] <;> norm_num
  have hle : 1 ≤ 16 := by norm_num
  have key : ∀ x : ℕ, 4 * x ≤ Nat.choose x 4 + (16 - 1) := by
    intro x
    by_cases hx : x ≤ 4
    · have head : ∀ n, ∀ y, 4 - y = n → y ≤ 4 → 4 * y ≤ Nat.choose y 4 + (16 - 1) := by
        intro n
        induction n with
        | zero =>
          intro y hy _
          have hyT : y = 4 := by omega
          subst hyT
          norm_num [hT', hT]
        | succ n ih =>
          intro y hy hleB
          have hstep : 4 * (y + 1) ≤ Nat.choose (y + 1) 4 + (16 - 1) :=
            ih (y + 1) (by omega) (by omega)
          have hpas : Nat.choose (y + 1) 4 = Nat.choose y 3 + Nat.choose y 4 :=
            Nat.choose_succ_succ y 3
          have hmono : Nat.choose y 3 ≤ 4 := by
            have h1 : Nat.choose y 3 ≤ Nat.choose 4 3 :=
              Nat.choose_le_choose 3 hleB
            omega
          rw [hpas] at hstep
          have hmul : 4 * (y + 1) = 4 * y + 4 := by ring
          rw [hmul] at hstep
          omega
      exact head (4 - x) x rfl hx
    · have hxB : 4 ≤ x := by omega
      have tail : ∀ x, 4 ≤ x → 4 * x ≤ Nat.choose x 4 + (16 - 1) := by
        intro x hx2
        induction x, hx2 using Nat.le_induction with
        | base => norm_num [hT', hT]
        | succ y hy ih =>
          have hmono : 4 ≤ Nat.choose y 3 := by
            have h1 : Nat.choose 4 3 ≤ Nat.choose y 3 :=
              Nat.choose_le_choose 3 hy
            omega
          have hpas : Nat.choose (y + 1) 4 = Nat.choose y 3 + Nat.choose y 4 :=
            Nat.choose_succ_succ y 3
          rw [hpas]
          have hmul : 4 * (y + 1) = 4 * y + 4 := by ring
          rw [hmul]
          omega
      exact tail x hxB
  have h1 : 4 * (∑ i, b i) ≤ ∑ i, (Nat.choose (b i) 4 + (16 - 1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => key (b i))
  have h2 : ∑ i, (Nat.choose (b i) 4 + (16 - 1))
      = (∑ i, Nat.choose (b i) 4) + q * (16 - 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [h2] at h1
  have h3 : q * 1 + q * (16 - 1) = q * 16 := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hle]
  omega
