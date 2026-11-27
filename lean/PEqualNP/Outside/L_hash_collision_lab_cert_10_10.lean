import Mathlib

namespace PEqualNP.Outside

private theorem choose_succ_self_10 (n : ℕ) : Nat.choose (n + 1) n = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Nat.choose_succ_succ, ih, Nat.choose_self]

theorem L_hash_collision_lab_cert_10_10 :
    (∀ (q:ℕ) (b:Fin q→ℕ), (q*1)+10*(∑ i,b i)≤(∑ i,Nat.choose (b i) 10)+q*100) := by
  have h_ge10 : ∀ t : ℕ, 10 ≤ Nat.choose (10 + t) 9 := by
    intro t
    induction t with
    | zero =>
      rw [Nat.add_zero, choose_succ_self_10 9]
    | succ t ih =>
      have hstep : Nat.choose ((10 + t) + 1) 9 =
          Nat.choose (10 + t) 8 + Nat.choose (10 + t) 9 := Nat.choose_succ_succ (10 + t) 8
      have heq : 10 + (t + 1) = (10 + t) + 1 := by omega
      rw [heq]
      omega
  have h_ind : ∀ d : ℕ, 1 + 10 * (10 + d) ≤ Nat.choose (10 + d) 10 + 100 := by
    intro d
    induction d with
    | zero =>
      rw [Nat.add_zero, Nat.choose_self 10]
    | succ t ih =>
      have hstep : Nat.choose ((10 + t) + 1) 10 =
          Nat.choose (10 + t) 9 + Nat.choose (10 + t) 10 := Nat.choose_succ_succ (10 + t) 9
      have hlow := h_ge10 t
      have heq : 10 + (t + 1) = (10 + t) + 1 := by omega
      rw [heq]
      omega
  have h_pt : ∀ m : ℕ, 1 + 10 * m ≤ Nat.choose m 10 + 100 := by
    intro m
    by_cases hm : m < 10
    · omega
    · have hdecomp : m = 10 + (m - 10) := by omega
      rw [hdecomp]
      exact h_ind (m - 10)
  intro q b
  have hsum : (∑ i : Fin q, (1 + 10 * b i)) ≤ ∑ i : Fin q, (Nat.choose (b i) 10 + 100) :=
    Finset.sum_le_sum (fun i _ => h_pt (b i))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  exact hsum

end PEqualNP.Outside
