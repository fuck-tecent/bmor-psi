import Mathlib

namespace PEqualNP.Outside

theorem L_hash_collision_lab_cert_9_9 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*1)+9*(∑ i,b i)≤(∑ i,Nat.choose (b i) 9)+q*81 := by
  intro q b
  have hc98 : ∀ d : ℕ, 9 ≤ Nat.choose (9 + d) 8 := by
    intro d
    induction d with
    | zero =>
      rw [add_zero]
      have h0 : Nat.choose 9 8 = 9 := rfl
      omega
    | succ d ih =>
      have hstep : Nat.choose (9 + (d + 1)) 8 = Nat.choose (9 + d) 7 + Nat.choose (9 + d) 8 :=
        Nat.choose_succ_succ (9 + d) 7
      omega
  have hc99 : ∀ k : ℕ, 1 + 9 * (9 + k) ≤ Nat.choose (9 + k) 9 + 81 := by
    intro k
    induction k with
    | zero =>
      rw [add_zero]
      have h0 : Nat.choose 9 9 = 1 := rfl
      omega
    | succ k ih =>
      have hstep : Nat.choose (9 + (k + 1)) 9 = Nat.choose (9 + k) 8 + Nat.choose (9 + k) 9 :=
        Nat.choose_succ_succ (9 + k) 8
      have hlow : 9 ≤ Nat.choose (9 + k) 8 := hc98 k
      omega
  have hpt : ∀ m : ℕ, 1 + 9 * m ≤ Nat.choose m 9 + 81 := by
    intro m
    by_cases hm : 9 ≤ m
    · have heq : 9 + (m - 9) = m := by omega
      have h := hc99 (m - 9)
      rw [heq] at h
      exact h
    · omega
  have hsum : ∑ i : Fin q, (1 + 9 * b i) ≤ ∑ i : Fin q, (Nat.choose (b i) 9 + 81) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hlhs : (∑ i : Fin q, (1 + 9 * b i)) = q * 1 + 9 * ∑ i : Fin q, b i := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hrhs : (∑ i : Fin q, (Nat.choose (b i) 9 + 81)) = (∑ i : Fin q, Nat.choose (b i) 9) + q * 81 := by
    rw [Finset.sum_add_distrib]
    simp
  omega

end PEqualNP.Outside
