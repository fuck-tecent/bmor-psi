import Mathlib

namespace PEqualNP.Outside

theorem L_hash_collision_lab_cert_12_12 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*1)+12*(∑ i,b i)≤(∑ i,Nat.choose (b i) 12)+q*144 := by
  intro q b
  have hc1 : ∀ d : ℕ, 12 ≤ Nat.choose (12 + d) 11 := by
    intro d
    induction d with
    | zero =>
      rw [add_zero]
      have h0 : Nat.choose 12 11 = 12 := rfl
      omega
    | succ d ih =>
      have hstep : Nat.choose (12 + (d + 1)) 11 = Nat.choose (12 + d) 10 + Nat.choose (12 + d) 11 :=
        Nat.choose_succ_succ (12 + d) 10
      omega
  have hc2 : ∀ k : ℕ, 1 + 12 * (12 + k) ≤ Nat.choose (12 + k) 12 + 144 := by
    intro k
    induction k with
    | zero =>
      rw [add_zero]
      have h0 : Nat.choose 12 12 = 1 := rfl
      omega
    | succ k ih =>
      have hstep : Nat.choose (12 + (k + 1)) 12 = Nat.choose (12 + k) 11 + Nat.choose (12 + k) 12 :=
        Nat.choose_succ_succ (12 + k) 11
      have hlow : 12 ≤ Nat.choose (12 + k) 11 := hc1 k
      omega
  have hpt : ∀ m : ℕ, 1 + 12 * m ≤ Nat.choose m 12 + 144 := by
    intro m
    by_cases hm : 12 ≤ m
    · have heq : 12 + (m - 12) = m := by omega
      have h := hc2 (m - 12)
      rw [heq] at h
      exact h
    · omega
  have hsum : ∑ i : Fin q, (1 + 12 * b i) ≤ ∑ i : Fin q, (Nat.choose (b i) 12 + 144) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hlhs : (∑ i : Fin q, (1 + 12 * b i)) = q * 1 + 12 * ∑ i : Fin q, b i := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hrhs : (∑ i : Fin q, (Nat.choose (b i) 12 + 144)) = (∑ i : Fin q, Nat.choose (b i) 12) + q * 144 := by
    rw [Finset.sum_add_distrib]
    simp
  omega

end PEqualNP.Outside
