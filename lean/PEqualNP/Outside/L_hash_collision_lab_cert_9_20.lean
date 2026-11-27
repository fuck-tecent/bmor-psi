import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_9_20 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*167960)+125970*(∑ i,b i)≤(∑ i,Nat.choose (b i) 9)+q*2519400 := by
  have h20_9 : Nat.choose 20 9 = 167960 := by decide
  have h20_8 : Nat.choose 20 8 = 125970 := by decide
  have hge : ∀ k : ℕ, 167960 + 125970 * (20 + k) ≤ Nat.choose (20 + k) 9 + 2519400 := by
    intro k
    induction k with
    | zero =>
      rw [Nat.add_zero, h20_9]
    | succ k ih =>
      have hsucc : Nat.choose (20 + (k + 1)) 9 = Nat.choose (20 + k) 8 + Nat.choose (20 + k) 9 := by
        rw [show 20 + (k + 1) = (20 + k) + 1 by omega]
        exact Nat.choose_succ_succ' (20 + k) 8
      have hmono : 125970 ≤ Nat.choose (20 + k) 8 := by
        rw [← h20_8]
        exact Nat.choose_le_choose 8 (Nat.le_add_right 20 k)
      calc 167960 + 125970 * (20 + (k + 1))
        _ = (167960 + 125970 * (20 + k)) + 125970 := by ring
        _ ≤ (Nat.choose (20 + k) 9 + 2519400) + Nat.choose (20 + k) 8 := Nat.add_le_add ih hmono
        _ = Nat.choose (20 + (k + 1)) 9 + 2519400 := by rw [hsucc]; ring
  have hle : ∀ k : ℕ, k ≤ 20 → 167960 + 125970 * (20 - k) ≤ Nat.choose (20 - k) 9 + 2519400 := by
    intro k hk
    induction k with
    | zero =>
      rw [Nat.sub_zero, h20_9]
    | succ k ih =>
      have ih' := ih (Nat.le_of_succ_le hk)
      have hsub : 20 - k = (20 - (k + 1)) + 1 := by omega
      have hsucc : Nat.choose (20 - k) 9 = Nat.choose (20 - (k + 1)) 8 + Nat.choose (20 - (k + 1)) 9 := by
        rw [hsub]
        exact Nat.choose_succ_succ' (20 - (k + 1)) 8
      have hmono : Nat.choose (20 - (k + 1)) 8 ≤ 125970 := by
        rw [← h20_8]
        exact Nat.choose_le_choose 8 (Nat.sub_le 20 (k + 1))
      have hmul : 125970 * (20 - k) = 125970 * (20 - (k + 1)) + 125970 := by
        rw [hsub, Nat.mul_add, Nat.mul_one]
      rw [hsucc, hmul] at ih'
      omega
  have hpt : ∀ n : ℕ, 167960 + 125970 * n ≤ Nat.choose n 9 + 2519400 := by
    intro n
    by_cases hn : 20 ≤ n
    · have h := hge (n - 20)
      rwa [show 20 + (n - 20) = n by omega] at h
    · have h := hle (20 - n) (Nat.sub_le 20 n)
      rwa [show 20 - (20 - n) = n by omega] at h
  intro q b
  have hsum : ∑ i : Fin q, (167960 + 125970 * b i) ≤ ∑ i : Fin q, (Nat.choose (b i) 9 + 2519400) :=
    Finset.sum_le_sum (fun i _ => hpt (b i))
  have hlhs : q * 167960 + 125970 * (∑ i : Fin q, b i) = ∑ i : Fin q, (167960 + 125970 * b i) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul, Finset.mul_sum]
  have hrhs : (∑ i : Fin q, Nat.choose (b i) 9) + q * 2519400 = ∑ i : Fin q, (Nat.choose (b i) 9 + 2519400) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul]
  rw [hlhs, hrhs]
  exact hsum
