import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_8_21 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*203490)+116280*(∑ i,b i)≤(∑ i,Nat.choose (b i) 8)+q*2441880 := by
  have h21_8 : Nat.choose 21 8 = 203490 := by decide
  have h21_7 : Nat.choose 21 7 = 116280 := by decide
  have hge : ∀ k : ℕ, 203490 + 116280 * (21 + k) ≤ Nat.choose (21 + k) 8 + 2441880 := by
    intro k
    induction k with
    | zero =>
      rw [Nat.add_zero, h21_8]
    | succ k ih =>
      have hsucc : Nat.choose (21 + (k + 1)) 8 = Nat.choose (21 + k) 7 + Nat.choose (21 + k) 8 := by
        rw [show 21 + (k + 1) = (21 + k) + 1 by omega]
        exact Nat.choose_succ_succ' (21 + k) 7
      have hmono : 116280 ≤ Nat.choose (21 + k) 7 := by
        rw [← h21_7]
        exact Nat.choose_le_choose 7 (Nat.le_add_right 21 k)
      calc 203490 + 116280 * (21 + (k + 1))
        _ = (203490 + 116280 * (21 + k)) + 116280 := by ring
        _ ≤ (Nat.choose (21 + k) 8 + 2441880) + Nat.choose (21 + k) 7 := Nat.add_le_add ih hmono
        _ = Nat.choose (21 + (k + 1)) 8 + 2441880 := by rw [hsucc]; ring
  have hle : ∀ k : ℕ, k ≤ 21 → 203490 + 116280 * (21 - k) ≤ Nat.choose (21 - k) 8 + 2441880 := by
    intro k hk
    induction k with
    | zero =>
      rw [Nat.sub_zero, h21_8]
    | succ k ih =>
      have ih' := ih (Nat.le_of_succ_le hk)
      have hsub : 21 - k = (21 - (k + 1)) + 1 := by omega
      have hsucc : Nat.choose (21 - k) 8 = Nat.choose (21 - (k + 1)) 7 + Nat.choose (21 - (k + 1)) 8 := by
        rw [hsub]
        exact Nat.choose_succ_succ' (21 - (k + 1)) 7
      have hmono : Nat.choose (21 - (k + 1)) 7 ≤ 116280 := by
        rw [← h21_7]
        exact Nat.choose_le_choose 7 (Nat.sub_le 21 (k + 1))
      have hmul : 116280 * (21 - k) = 116280 * (21 - (k + 1)) + 116280 := by
        rw [hsub, Nat.mul_add, Nat.mul_one]
      rw [hsucc, hmul] at ih'
      omega
  have hpt : ∀ n : ℕ, 203490 + 116280 * n ≤ Nat.choose n 8 + 2441880 := by
    intro n
    by_cases hn : 21 ≤ n
    · have h := hge (n - 21)
      rwa [show 21 + (n - 21) = n by omega] at h
    · have h := hle (21 - n) (Nat.sub_le 21 n)
      rwa [show 21 - (21 - n) = n by omega] at h
  intro q b
  have hsum : ∑ i : Fin q, (203490 + 116280 * b i) ≤ ∑ i : Fin q, (Nat.choose (b i) 8 + 2441880) :=
    Finset.sum_le_sum (fun i _ => hpt (b i))
  have hlhs : q * 203490 + 116280 * (∑ i : Fin q, b i) = ∑ i : Fin q, (203490 + 116280 * b i) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul, Finset.mul_sum]
  have hrhs : (∑ i : Fin q, Nat.choose (b i) 8) + q * 2441880 = ∑ i : Fin q, (Nat.choose (b i) 8 + 2441880) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul]
  rw [hlhs, hrhs]
  exact hsum
