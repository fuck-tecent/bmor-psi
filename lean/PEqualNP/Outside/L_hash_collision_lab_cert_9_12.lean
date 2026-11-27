import Mathlib

namespace PEqualNP.Outside

theorem L_hash_collision_lab_cert_9_12 :
    ∀ (q:ℕ) (b:Fin q→ℕ), (q*220)+495*(∑ i,b i)≤(∑ i,Nat.choose (b i) 9)+q*5940 := by
  intro q b
  have hc1 : ∀ d : ℕ, 495 ≤ Nat.choose (12 + d) 8 := by
    intro d
    induction d with
    | zero =>
      rw [add_zero]
      have e1 := Nat.add_one_mul_choose_eq 8 0
      have e2 := Nat.add_one_mul_choose_eq 9 1
      have e3 := Nat.add_one_mul_choose_eq 10 2
      have e4 := Nat.add_one_mul_choose_eq 11 3
      have hsym := Nat.choose_symm (by norm_num : 4 ≤ 12)
      norm_num [Nat.choose_zero_right] at e1 e2 e3 e4 hsym
      linarith
    | succ d ih =>
      have hstep : Nat.choose (12 + (d + 1)) 8 = Nat.choose (12 + d) 7 + Nat.choose (12 + d) 8 :=
        Nat.choose_succ_succ (12 + d) 7
      linarith
  have hc2 : ∀ k : ℕ, 220 + 495 * (12 + k) ≤ Nat.choose (12 + k) 9 + 5940 := by
    intro k
    induction k with
    | zero =>
      rw [add_zero]
      have e1 := Nat.add_one_mul_choose_eq 9 0
      have e2 := Nat.add_one_mul_choose_eq 10 1
      have e3 := Nat.add_one_mul_choose_eq 11 2
      have hsym := Nat.choose_symm (by norm_num : 3 ≤ 12)
      norm_num [Nat.choose_zero_right] at e1 e2 e3 hsym
      linarith
    | succ k ih =>
      have hstep : Nat.choose (12 + (k + 1)) 9 = Nat.choose (12 + k) 8 + Nat.choose (12 + k) 9 :=
        Nat.choose_succ_succ (12 + k) 8
      have hlow : 495 ≤ Nat.choose (12 + k) 8 := hc1 k
      linarith
  have hpt : ∀ m : ℕ, 220 + 495 * m ≤ Nat.choose m 9 + 5940 := by
    intro m
    by_cases hm : 12 ≤ m
    · have heq : 12 + (m - 12) = m := by omega
      have h := hc2 (m - 12)
      rw [heq] at h
      exact h
    · have hm11 : m ≤ 11 := by omega
      linarith
  have hsum : ∑ i : Fin q, (220 + 495 * b i) ≤ ∑ i : Fin q, (Nat.choose (b i) 9 + 5940) :=
    Finset.sum_le_sum fun i _ => hpt (b i)
  have hlhs : (∑ i : Fin q, (220 + 495 * b i)) = q * 220 + 495 * ∑ i : Fin q, b i := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hrhs : (∑ i : Fin q, (Nat.choose (b i) 9 + 5940)) = (∑ i : Fin q, Nat.choose (b i) 9) + q * 5940 := by
    rw [Finset.sum_add_distrib]
    simp
  linarith

end PEqualNP.Outside
