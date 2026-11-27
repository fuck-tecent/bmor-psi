import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_3_10 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*120)+45*(∑ i,b i)≤(∑ i,Nat.choose (b i) 3)+q*450 := by
  intro q b
  have hT : Nat.choose 10 2 = 45 := by
    rw [Nat.choose_eq_factorial_div_factorial] <;> norm_num
  have hT' : Nat.choose 10 3 = 120 := by
    rw [Nat.choose_eq_factorial_div_factorial] <;> norm_num
  have hle : 120 ≤ 450 := by norm_num
  have key : ∀ x : ℕ, 45 * x ≤ Nat.choose x 3 + (450 - 120) := by
    intro x
    by_cases hx : x ≤ 10
    · have head : ∀ n, ∀ y, 10 - y = n → y ≤ 10 → 45 * y ≤ Nat.choose y 3 + (450 - 120) := by
        intro n
        induction n with
        | zero =>
          intro y hy _
          have hyT : y = 10 := by omega
          subst hyT
          norm_num [hT', hT]
        | succ n ih =>
          intro y hy hleB
          have hstep : 45 * (y + 1) ≤ Nat.choose (y + 1) 3 + (450 - 120) :=
            ih (y + 1) (by omega) (by omega)
          have hpas : Nat.choose (y + 1) 3 = Nat.choose y 2 + Nat.choose y 3 :=
            Nat.choose_succ_succ y 2
          have hmono : Nat.choose y 2 ≤ 45 := by
            have h1 : Nat.choose y 2 ≤ Nat.choose 10 2 :=
              Nat.choose_le_choose 2 hleB
            omega
          rw [hpas] at hstep
          have hmul : 45 * (y + 1) = 45 * y + 45 := by ring
          rw [hmul] at hstep
          omega
      exact head (10 - x) x rfl hx
    · have hxB : 10 ≤ x := by omega
      have tail : ∀ x, 10 ≤ x → 45 * x ≤ Nat.choose x 3 + (450 - 120) := by
        intro x hx2
        induction x, hx2 using Nat.le_induction with
        | base => norm_num [hT', hT]
        | succ y hy ih =>
          have hmono : 45 ≤ Nat.choose y 2 := by
            have h1 : Nat.choose 10 2 ≤ Nat.choose y 2 :=
              Nat.choose_le_choose 2 hy
            omega
          have hpas : Nat.choose (y + 1) 3 = Nat.choose y 2 + Nat.choose y 3 :=
            Nat.choose_succ_succ y 2
          rw [hpas]
          have hmul : 45 * (y + 1) = 45 * y + 45 := by ring
          rw [hmul]
          omega
      exact tail x hxB
  have h1 : 45 * (∑ i, b i) ≤ ∑ i, (Nat.choose (b i) 3 + (450 - 120)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => key (b i))
  have h2 : ∑ i, (Nat.choose (b i) 3 + (450 - 120))
      = (∑ i, Nat.choose (b i) 3) + q * (450 - 120) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [h2] at h1
  have h3 : q * 120 + q * (450 - 120) = q * 450 := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hle]
  omega
