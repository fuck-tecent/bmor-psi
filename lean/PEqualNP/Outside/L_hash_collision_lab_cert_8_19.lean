import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_8_19 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*75582)+50388*(∑ i,b i)≤(∑ i,Nat.choose (b i) 8)+q*957372 := by
  have h19_8 : Nat.choose 19 8 = 75582 := by decide
  have h19_7 : Nat.choose 19 7 = 50388 := by decide
  have hge : ∀ k : ℕ, 75582 + 50388 * (19 + k) ≤ Nat.choose (19 + k) 8 + 957372 := by
    intro k
    induction k with
    | zero =>
      rw [Nat.add_zero, h19_8]
    | succ k ih =>
      have hsucc : Nat.choose (19 + (k + 1)) 8 = Nat.choose (19 + k) 7 + Nat.choose (19 + k) 8 := by
        rw [show 19 + (k + 1) = (19 + k) + 1 by omega]
        exact Nat.choose_succ_succ' (19 + k) 7
      have hmono : 50388 ≤ Nat.choose (19 + k) 7 := by
        rw [← h19_7]
        exact Nat.choose_le_choose 7 (Nat.le_add_right 19 k)
      calc 75582 + 50388 * (19 + (k + 1))
        _ = (75582 + 50388 * (19 + k)) + 50388 := by ring
        _ ≤ (Nat.choose (19 + k) 8 + 957372) + Nat.choose (19 + k) 7 := Nat.add_le_add ih hmono
        _ = Nat.choose (19 + (k + 1)) 8 + 957372 := by rw [hsucc]; ring
  have hle : ∀ k : ℕ, k ≤ 19 → 75582 + 50388 * (19 - k) ≤ Nat.choose (19 - k) 8 + 957372 := by
    intro k hk
    induction k with
    | zero =>
      rw [Nat.sub_zero, h19_8]
    | succ k ih =>
      have ih' := ih (Nat.le_of_succ_le hk)
      have hsub : 19 - k = (19 - (k + 1)) + 1 := by omega
      have hsucc : Nat.choose (19 - k) 8 = Nat.choose (19 - (k + 1)) 7 + Nat.choose (19 - (k + 1)) 8 := by
        rw [hsub]
        exact Nat.choose_succ_succ' (19 - (k + 1)) 7
      have hmono : Nat.choose (19 - (k + 1)) 7 ≤ 50388 := by
        rw [← h19_7]
        exact Nat.choose_le_choose 7 (Nat.sub_le 19 (k + 1))
      have hmul : 50388 * (19 - k) = 50388 * (19 - (k + 1)) + 50388 := by
        rw [hsub, Nat.mul_add, Nat.mul_one]
      rw [hsucc, hmul] at ih'
      omega
  have hpt : ∀ n : ℕ, 75582 + 50388 * n ≤ Nat.choose n 8 + 957372 := by
    intro n
    by_cases hn : 19 ≤ n
    · have h := hge (n - 19)
      rwa [show 19 + (n - 19) = n by omega] at h
    · have h := hle (19 - n) (Nat.sub_le 19 n)
      rwa [show 19 - (19 - n) = n by omega] at h
  intro q b
  have hsum : ∑ i : Fin q, (75582 + 50388 * b i) ≤ ∑ i : Fin q, (Nat.choose (b i) 8 + 957372) :=
    Finset.sum_le_sum (fun i _ => hpt (b i))
  have hlhs : q * 75582 + 50388 * (∑ i : Fin q, b i) = ∑ i : Fin q, (75582 + 50388 * b i) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul, Finset.mul_sum]
  have hrhs : (∑ i : Fin q, Nat.choose (b i) 8) + q * 957372 = ∑ i : Fin q, (Nat.choose (b i) 8 + 957372) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul]
  rw [hlhs, hrhs]
  exact hsum
