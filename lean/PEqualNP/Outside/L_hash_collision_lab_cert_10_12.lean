import Mathlib

namespace PEqualNP.Outside

theorem L_hash_collision_lab_cert_10_12 :
(
∀ (q:ℕ) (b:Fin q→ℕ), (q*66)+220*(∑ i,b i)≤(∑ i,Nat.choose (b i) 10)+q*2640
) := by
  have h_ge220 : ∀ t : ℕ, 220 ≤ Nat.choose (12 + t) 9 := by
    intro t
    induction t with
    | zero =>
      rw [Nat.add_zero]
      decide
    | succ t ih =>
      have hstep : Nat.choose ((12 + t) + 1) 9 =
          Nat.choose (12 + t) 8 + Nat.choose (12 + t) 9 := Nat.choose_succ_succ (12 + t) 8
      have heq : 12 + (t + 1) = (12 + t) + 1 := by omega
      rw [heq]
      omega
  have h_ind : ∀ d : ℕ, 66 + 220 * (12 + d) ≤ Nat.choose (12 + d) 10 + 2640 := by
    intro d
    induction d with
    | zero =>
      decide
    | succ t ih =>
      have hstep : Nat.choose ((12 + t) + 1) 10 =
          Nat.choose (12 + t) 9 + Nat.choose (12 + t) 10 := Nat.choose_succ_succ (12 + t) 9
      have hlow := h_ge220 t
      have heq : 12 + (t + 1) = (12 + t) + 1 := by omega
      rw [heq]
      omega
  have h_pt : ∀ m : ℕ, 66 + 220 * m ≤ Nat.choose m 10 + 2640 := by
    intro m
    by_cases hm : m < 12
    · omega
    · have hdecomp : m = 12 + (m - 12) := by omega
      rw [hdecomp]
      exact h_ind (m - 12)
  intro q b
  have hsum : (∑ i : Fin q, (66 + 220 * b i)) ≤ ∑ i : Fin q, (Nat.choose (b i) 10 + 2640) :=
    Finset.sum_le_sum (fun i _ => h_pt (b i))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  exact hsum

end PEqualNP.Outside
