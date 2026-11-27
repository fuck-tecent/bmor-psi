import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_10_20 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*184756)+167960*(∑ i,b i)≤(∑ i,Nat.choose (b i) 10)+q*3359200 := by
  have h20_10 : Nat.choose 20 10 = 184756 := by decide
  have h20_9 : Nat.choose 20 9 = 167960 := by decide
  have hge : ∀ k : ℕ, 184756 + 167960 * (20 + k) ≤ Nat.choose (20 + k) 10 + 3359200 := by
    intro k
    induction k with
    | zero =>
      rw [Nat.add_zero, h20_10]
    | succ k ih =>
      have hsucc : Nat.choose (20 + (k + 1)) 10 = Nat.choose (20 + k) 9 + Nat.choose (20 + k) 10 := by
        rw [show 20 + (k + 1) = (20 + k) + 1 by omega]
        exact Nat.choose_succ_succ' (20 + k) 9
      have hmono : 167960 ≤ Nat.choose (20 + k) 9 := by
        rw [← h20_9]
        exact Nat.choose_le_choose 9 (Nat.le_add_right 20 k)
      calc 184756 + 167960 * (20 + (k + 1))
        _ = (184756 + 167960 * (20 + k)) + 167960 := by ring
        _ ≤ (Nat.choose (20 + k) 10 + 3359200) + Nat.choose (20 + k) 9 := Nat.add_le_add ih hmono
        _ = Nat.choose (20 + (k + 1)) 10 + 3359200 := by rw [hsucc]; ring
  have hle : ∀ k : ℕ, k ≤ 20 → 184756 + 167960 * (20 - k) ≤ Nat.choose (20 - k) 10 + 3359200 := by
    intro k hk
    induction k with
    | zero =>
      rw [Nat.sub_zero, h20_10]
    | succ k ih =>
      have ih' := ih (Nat.le_of_succ_le hk)
      have hsub : 20 - k = (20 - (k + 1)) + 1 := by omega
      have hsucc : Nat.choose (20 - k) 10 = Nat.choose (20 - (k + 1)) 9 + Nat.choose (20 - (k + 1)) 10 := by
        rw [hsub]
        exact Nat.choose_succ_succ' (20 - (k + 1)) 9
      have hmono : Nat.choose (20 - (k + 1)) 9 ≤ 167960 := by
        rw [← h20_9]
        exact Nat.choose_le_choose 9 (Nat.sub_le 20 (k + 1))
      have hmul : 167960 * (20 - k) = 167960 * (20 - (k + 1)) + 167960 := by
        rw [hsub, Nat.mul_add, Nat.mul_one]
      rw [hsucc, hmul] at ih'
      omega
  have hpt : ∀ n : ℕ, 184756 + 167960 * n ≤ Nat.choose n 10 + 3359200 := by
    intro n
    by_cases hn : 20 ≤ n
    · have h := hge (n - 20)
      rwa [show 20 + (n - 20) = n by omega] at h
    · have h := hle (20 - n) (Nat.sub_le 20 n)
      rwa [show 20 - (20 - n) = n by omega] at h
  intro q b
  have hsum : ∑ i : Fin q, (184756 + 167960 * b i) ≤ ∑ i : Fin q, (Nat.choose (b i) 10 + 3359200) :=
    Finset.sum_le_sum (fun i _ => hpt (b i))
  have hlhs : q * 184756 + 167960 * (∑ i : Fin q, b i) = ∑ i : Fin q, (184756 + 167960 * b i) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul, Finset.mul_sum]
  have hrhs : (∑ i : Fin q, Nat.choose (b i) 10) + q * 3359200 = ∑ i : Fin q, (Nat.choose (b i) 10 + 3359200) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul]
  rw [hlhs, hrhs]
  exact hsum
