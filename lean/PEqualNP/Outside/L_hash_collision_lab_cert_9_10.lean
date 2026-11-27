import Mathlib

namespace PEqualNP.Outside

theorem L_hash_collision_lab_cert_9_10 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*10)+45*(∑ i,b i)≤(∑ i,Nat.choose (b i) 9)+q*450 := by
  intro q b
  have hc1 : ∀ d : ℕ, 45 ≤ Nat.choose (10 + d) 8 := by
    intro d
    induction d with
    | zero =>
      rw [add_zero]
      have h0 : Nat.choose 10 8 = 45 := rfl
      omega
    | succ d ih =>
      have hstep : Nat.choose (10 + (d + 1)) 8 = Nat.choose (10 + d) 7 + Nat.choose (10 + d) 8 :=
        Nat.choose_succ_succ (10 + d) 7
      omega
  have hc2 : ∀ k : ℕ, 10 + 45 * (10 + k) ≤ Nat.choose (10 + k) 9 + 450 := by
    intro k
    induction k with
    | zero =>
      rw [add_zero]
      have h0 : Nat.choose 10 9 = 10 := rfl
      omega
    | succ k ih =>
      have hstep : Nat.choose (10 + (k + 1)) 9 = Nat.choose (10 + k) 8 + Nat.choose (10 + k) 9 :=
        Nat.choose_succ_succ (10 + k) 8
      have hlow : 45 ≤ Nat.choose (10 + k) 8 := hc1 k
      omega
  have hpt : ∀ m : ℕ, 10 + 45 * m ≤ Nat.choose m 9 + 450 := by
    intro m
    by_cases hm : 10 ≤ m
    · have heq : 10 + (m - 10) = m := by omega
      have h := hc2 (m - 10)
      rw [heq] at h
      exact h
    · omega
  have hsum : ∑ i : Fin q, (10 + 45 * b i) ≤ ∑ i : Fin q, (Nat.choose (b i) 9 + 450) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hlhs : (∑ i : Fin q, (10 + 45 * b i)) = q * 10 + 45 * ∑ i : Fin q, b i := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hrhs : (∑ i : Fin q, (Nat.choose (b i) 9 + 450)) = (∑ i : Fin q, Nat.choose (b i) 9) + q * 450 := by
    rw [Finset.sum_add_distrib]
    simp
  omega

end PEqualNP.Outside
