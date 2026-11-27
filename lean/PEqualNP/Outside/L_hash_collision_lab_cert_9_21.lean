import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_9_21 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*293930)+203490*(∑ i,b i)≤(∑ i,Nat.choose (b i) 9)+q*4273290 := by
  have h21_9 : Nat.choose 21 9 = 293930 := by decide
  have h21_8 : Nat.choose 21 8 = 203490 := by decide
  have hge : ∀ k : ℕ, 293930 + 203490 * (21 + k) ≤ Nat.choose (21 + k) 9 + 4273290 := by
    intro k
    induction k with
    | zero =>
      rw [Nat.add_zero, h21_9]
    | succ k ih =>
      have hsucc : Nat.choose (21 + (k + 1)) 9 = Nat.choose (21 + k) 8 + Nat.choose (21 + k) 9 := by
        rw [show 21 + (k + 1) = (21 + k) + 1 by omega]
        exact Nat.choose_succ_succ' (21 + k) 8
      have hmono : 203490 ≤ Nat.choose (21 + k) 8 := by
        rw [← h21_8]
        exact Nat.choose_le_choose 8 (Nat.le_add_right 21 k)
      calc 293930 + 203490 * (21 + (k + 1))
        _ = (293930 + 203490 * (21 + k)) + 203490 := by ring
        _ ≤ (Nat.choose (21 + k) 9 + 4273290) + Nat.choose (21 + k) 8 := Nat.add_le_add ih hmono
        _ = Nat.choose (21 + (k + 1)) 9 + 4273290 := by rw [hsucc]; ring
  have hle : ∀ k : ℕ, k ≤ 21 → 293930 + 203490 * (21 - k) ≤ Nat.choose (21 - k) 9 + 4273290 := by
    intro k hk
    induction k with
    | zero =>
      rw [Nat.sub_zero, h21_9]
    | succ k ih =>
      have ih' := ih (Nat.le_of_succ_le hk)
      have hsub : 21 - k = (21 - (k + 1)) + 1 := by omega
      have hsucc : Nat.choose (21 - k) 9 = Nat.choose (21 - (k + 1)) 8 + Nat.choose (21 - (k + 1)) 9 := by
        rw [hsub]
        exact Nat.choose_succ_succ' (21 - (k + 1)) 8
      have hmono : Nat.choose (21 - (k + 1)) 8 ≤ 203490 := by
        rw [← h21_8]
        exact Nat.choose_le_choose 8 (Nat.sub_le 21 (k + 1))
      have hmul : 203490 * (21 - k) = 203490 * (21 - (k + 1)) + 203490 := by
        rw [hsub, Nat.mul_add, Nat.mul_one]
      rw [hsucc, hmul] at ih'
      omega
  have hpt : ∀ n : ℕ, 293930 + 203490 * n ≤ Nat.choose n 9 + 4273290 := by
    intro n
    by_cases hn : 21 ≤ n
    · have h := hge (n - 21)
      rwa [show 21 + (n - 21) = n by omega] at h
    · have h := hle (21 - n) (Nat.sub_le 21 n)
      rwa [show 21 - (21 - n) = n by omega] at h
  intro q b
  have hsum : ∑ i : Fin q, (293930 + 203490 * b i) ≤ ∑ i : Fin q, (Nat.choose (b i) 9 + 4273290) :=
    Finset.sum_le_sum (fun i _ => hpt (b i))
  have hlhs : q * 293930 + 203490 * (∑ i : Fin q, b i) = ∑ i : Fin q, (293930 + 203490 * b i) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul, Finset.mul_sum]
  have hrhs : (∑ i : Fin q, Nat.choose (b i) 9) + q * 4273290 = ∑ i : Fin q, (Nat.choose (b i) 9 + 4273290) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul]
  rw [hlhs, hrhs]
  exact hsum
