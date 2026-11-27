import Mathlib

namespace PEqualNP.Outside

private theorem choose_succ_self_12_13 (n : ℕ) : Nat.choose (n + 1) n = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Nat.choose_succ_succ, ih, Nat.choose_self]

private theorem two_mul_choose_add_two_12_13 (n : ℕ) :
    2 * Nat.choose (n + 2) n = (n + 2) * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hstep : Nat.choose ((k + 2) + 1) (k + 1) =
        Nat.choose (k + 2) k + Nat.choose (k + 2) (k + 1) :=
      Nat.choose_succ_succ (k + 2) k
    have hc1 : Nat.choose (k + 2) (k + 1) = k + 2 := choose_succ_self_12_13 (k + 1)
    calc 2 * Nat.choose ((k + 1) + 2) (k + 1)
        = 2 * (Nat.choose (k + 2) k + Nat.choose (k + 2) (k + 1)) := by rw [← hstep]
      _ = 2 * Nat.choose (k + 2) k + 2 * Nat.choose (k + 2) (k + 1) := by ring
      _ = (k + 2) * (k + 1) + 2 * (k + 2) := by rw [ih, hc1]
      _ = ((k + 1) + 2) * ((k + 1) + 1) := by ring

theorem L_hash_collision_lab_cert_12_13 :
    (∀ (q:ℕ) (b:Fin q→ℕ), (q*13)+78*(∑ i,b i)≤(∑ i,Nat.choose (b i) 12)+q*1014) := by
  have h_ge78 : ∀ t : ℕ, 78 ≤ Nat.choose (13 + t) 11 := by
    intro t
    induction t with
    | zero =>
      rw [Nat.add_zero]
      have h2 := two_mul_choose_add_two_12_13 11
      norm_num at h2
      omega
    | succ t ih =>
      have hstep : Nat.choose ((13 + t) + 1) 11 =
          Nat.choose (13 + t) 10 + Nat.choose (13 + t) 11 := Nat.choose_succ_succ (13 + t) 10
      have heq : 13 + (t + 1) = (13 + t) + 1 := by omega
      rw [heq]
      omega
  have h_ind : ∀ d : ℕ, 13 + 78 * (13 + d) ≤ Nat.choose (13 + d) 12 + 1014 := by
    intro d
    induction d with
    | zero =>
      rw [Nat.add_zero, choose_succ_self_12_13 12]
    | succ t ih =>
      have hstep : Nat.choose ((13 + t) + 1) 12 =
          Nat.choose (13 + t) 11 + Nat.choose (13 + t) 12 := Nat.choose_succ_succ (13 + t) 11
      have hlow := h_ge78 t
      have heq : 13 + (t + 1) = (13 + t) + 1 := by omega
      rw [heq]
      omega
  have h_pt : ∀ m : ℕ, 13 + 78 * m ≤ Nat.choose m 12 + 1014 := by
    intro m
    by_cases hm : m < 13
    · omega
    · have hdecomp : m = 13 + (m - 13) := by omega
      rw [hdecomp]
      exact h_ind (m - 13)
  intro q b
  have hsum : (∑ i : Fin q, (13 + 78 * b i)) ≤ ∑ i : Fin q, (Nat.choose (b i) 12 + 1014) :=
    Finset.sum_le_sum (fun i _ => h_pt (b i))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  exact hsum

end PEqualNP.Outside
