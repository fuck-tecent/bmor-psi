import Mathlib

namespace PEqualNP.Outside

private theorem choose_succ_self_11 (n : ℕ) : Nat.choose (n + 1) n = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Nat.choose_succ_succ, ih, Nat.choose_self]

theorem L_hash_collision_lab_cert_11_11 :
    (∀ (q:ℕ) (b:Fin q→ℕ), (q*1)+11*(∑ i,b i)≤(∑ i,Nat.choose (b i) 11)+q*121) := by
  have h_ge11 : ∀ t : ℕ, 11 ≤ Nat.choose (11 + t) 10 := by
    intro t
    induction t with
    | zero =>
      rw [Nat.add_zero, choose_succ_self_11 10]
    | succ t ih =>
      have hstep : Nat.choose ((11 + t) + 1) 10 =
          Nat.choose (11 + t) 9 + Nat.choose (11 + t) 10 := Nat.choose_succ_succ (11 + t) 9
      have heq : 11 + (t + 1) = (11 + t) + 1 := by omega
      rw [heq]
      omega
  have h_ind : ∀ d : ℕ, 1 + 11 * (11 + d) ≤ Nat.choose (11 + d) 11 + 121 := by
    intro d
    induction d with
    | zero =>
      rw [Nat.add_zero, Nat.choose_self 11]
    | succ t ih =>
      have hstep : Nat.choose ((11 + t) + 1) 11 =
          Nat.choose (11 + t) 10 + Nat.choose (11 + t) 11 := Nat.choose_succ_succ (11 + t) 10
      have hlow := h_ge11 t
      have heq : 11 + (t + 1) = (11 + t) + 1 := by omega
      rw [heq]
      omega
  have h_pt : ∀ m : ℕ, 1 + 11 * m ≤ Nat.choose m 11 + 121 := by
    intro m
    by_cases hm : m < 11
    · omega
    · have hdecomp : m = 11 + (m - 11) := by omega
      rw [hdecomp]
      exact h_ind (m - 11)
  intro q b
  have hsum : (∑ i : Fin q, (1 + 11 * b i)) ≤ ∑ i : Fin q, (Nat.choose (b i) 11 + 121) :=
    Finset.sum_le_sum (fun i _ => h_pt (b i))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  exact hsum

end PEqualNP.Outside
