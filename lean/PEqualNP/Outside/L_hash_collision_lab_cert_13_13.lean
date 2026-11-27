import Mathlib

namespace PEqualNP.Outside

theorem L_hash_collision_lab_cert_13_13 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*1)+13*(∑ i,b i)≤(∑ i,Nat.choose (b i) 13)+q*169 := by
  intro q b
  have hc1 : ∀ d : ℕ, 13 ≤ Nat.choose (13 + d) 12 := by
    intro d
    induction d with
    | zero =>
      rw [add_zero]
      have h0 : Nat.choose 13 12 = 13 := rfl
      omega
    | succ d ih =>
      have hstep : Nat.choose (13 + (d + 1)) 12 = Nat.choose (13 + d) 11 + Nat.choose (13 + d) 12 :=
        Nat.choose_succ_succ (13 + d) 11
      omega
  have hc2 : ∀ k : ℕ, 1 + 13 * (13 + k) ≤ Nat.choose (13 + k) 13 + 169 := by
    intro k
    induction k with
    | zero =>
      rw [add_zero]
      have h0 : Nat.choose 13 13 = 1 := rfl
      omega
    | succ k ih =>
      have hstep : Nat.choose (13 + (k + 1)) 13 = Nat.choose (13 + k) 12 + Nat.choose (13 + k) 13 :=
        Nat.choose_succ_succ (13 + k) 12
      have hlow : 13 ≤ Nat.choose (13 + k) 12 := hc1 k
      omega
  have hpt : ∀ m : ℕ, 1 + 13 * m ≤ Nat.choose m 13 + 169 := by
    intro m
    by_cases hm : 13 ≤ m
    · have heq : 13 + (m - 13) = m := by omega
      have h := hc2 (m - 13)
      rw [heq] at h
      exact h
    · omega
  have hsum : ∑ i : Fin q, (1 + 13 * b i) ≤ ∑ i : Fin q, (Nat.choose (b i) 13 + 169) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hlhs : (∑ i : Fin q, (1 + 13 * b i)) = q * 1 + 13 * ∑ i : Fin q, b i := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hrhs : (∑ i : Fin q, (Nat.choose (b i) 13 + 169)) = (∑ i : Fin q, Nat.choose (b i) 13) + q * 169 := by
    rw [Finset.sum_add_distrib]
    simp
  omega

end PEqualNP.Outside
