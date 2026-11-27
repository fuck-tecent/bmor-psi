import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_8_13 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*1287)+1716*(∑ i,b i)≤(∑ i,Nat.choose (b i) 8)+q*22308 := by
  have h13_8 : Nat.choose 13 8 = 1287 := by decide
  have h13_7 : Nat.choose 13 7 = 1716 := by decide
  have hge : ∀ k : ℕ, 1287 + 1716 * (13 + k) ≤ Nat.choose (13 + k) 8 + 22308 := by
    intro k
    induction k with
    | zero =>
      rw [Nat.add_zero, h13_8]
    | succ k ih =>
      have hsucc : Nat.choose (13 + (k + 1)) 8 = Nat.choose (13 + k) 7 + Nat.choose (13 + k) 8 := by
        rw [show 13 + (k + 1) = (13 + k) + 1 by omega]
        exact Nat.choose_succ_succ' (13 + k) 7
      have hmono : 1716 ≤ Nat.choose (13 + k) 7 := by
        rw [← h13_7]
        exact Nat.choose_le_choose 7 (Nat.le_add_right 13 k)
      calc 1287 + 1716 * (13 + (k + 1))
        _ = (1287 + 1716 * (13 + k)) + 1716 := by ring
        _ ≤ (Nat.choose (13 + k) 8 + 22308) + Nat.choose (13 + k) 7 := Nat.add_le_add ih hmono
        _ = Nat.choose (13 + (k + 1)) 8 + 22308 := by rw [hsucc]; ring
  have hle : ∀ k : ℕ, k ≤ 13 → 1287 + 1716 * (13 - k) ≤ Nat.choose (13 - k) 8 + 22308 := by
    intro k hk
    induction k with
    | zero =>
      rw [Nat.sub_zero, h13_8]
    | succ k ih =>
      have ih' := ih (Nat.le_of_succ_le hk)
      have hsub : 13 - k = (13 - (k + 1)) + 1 := by omega
      have hsucc : Nat.choose (13 - k) 8 = Nat.choose (13 - (k + 1)) 7 + Nat.choose (13 - (k + 1)) 8 := by
        rw [hsub]
        exact Nat.choose_succ_succ' (13 - (k + 1)) 7
      have hmono : Nat.choose (13 - (k + 1)) 7 ≤ 1716 := by
        rw [← h13_7]
        exact Nat.choose_le_choose 7 (Nat.sub_le 13 (k + 1))
      have hmul : 1716 * (13 - k) = 1716 * (13 - (k + 1)) + 1716 := by
        rw [hsub, Nat.mul_add, Nat.mul_one]
      rw [hsucc, hmul] at ih'
      omega
  have hpt : ∀ n : ℕ, 1287 + 1716 * n ≤ Nat.choose n 8 + 22308 := by
    intro n
    by_cases hn : 13 ≤ n
    · have h := hge (n - 13)
      rwa [show 13 + (n - 13) = n by omega] at h
    · have h := hle (13 - n) (Nat.sub_le 13 n)
      rwa [show 13 - (13 - n) = n by omega] at h
  intro q b
  have hsum : ∑ i : Fin q, (1287 + 1716 * b i) ≤ ∑ i : Fin q, (Nat.choose (b i) 8 + 22308) :=
    Finset.sum_le_sum (fun i _ => hpt (b i))
  have hlhs : q * 1287 + 1716 * (∑ i : Fin q, b i) = ∑ i : Fin q, (1287 + 1716 * b i) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul, Finset.mul_sum]
  have hrhs : (∑ i : Fin q, Nat.choose (b i) 8) + q * 22308 = ∑ i : Fin q, (Nat.choose (b i) 8 + 22308) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul]
  rw [hlhs, hrhs]
  exact hsum
