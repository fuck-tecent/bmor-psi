import Mathlib

namespace PEqualNP.Outside

private theorem choose_succ_self_13_14 (n : ℕ) : Nat.choose (n + 1) n = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Nat.choose_succ_succ, ih, Nat.choose_self]

private theorem two_mul_choose_add_two_13_14 (n : ℕ) :
    2 * Nat.choose (n + 2) n = (n + 2) * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hstep : Nat.choose ((k + 2) + 1) (k + 1) =
        Nat.choose (k + 2) k + Nat.choose (k + 2) (k + 1) :=
      Nat.choose_succ_succ (k + 2) k
    have hc1 : Nat.choose (k + 2) (k + 1) = k + 2 := choose_succ_self_13_14 (k + 1)
    calc 2 * Nat.choose ((k + 1) + 2) (k + 1)
        = 2 * (Nat.choose (k + 2) k + Nat.choose (k + 2) (k + 1)) := by rw [← hstep]
      _ = 2 * Nat.choose (k + 2) k + 2 * Nat.choose (k + 2) (k + 1) := by ring
      _ = (k + 2) * (k + 1) + 2 * (k + 2) := by rw [ih, hc1]
      _ = ((k + 1) + 2) * ((k + 1) + 1) := by ring

theorem L_hash_collision_lab_cert_13_14 :
    (∀ (q:ℕ) (b:Fin q→ℕ), (q*14)+91*(∑ i,b i)≤(∑ i,Nat.choose (b i) 13)+q*1274) := by
  have h_ge91 : ∀ t : ℕ, 91 ≤ Nat.choose (14 + t) 12 := by
    intro t
    induction t with
    | zero =>
      rw [Nat.add_zero]
      have h2 := two_mul_choose_add_two_13_14 12
      norm_num at h2
      omega
    | succ t ih =>
      have hstep : Nat.choose ((14 + t) + 1) 12 =
          Nat.choose (14 + t) 11 + Nat.choose (14 + t) 12 := Nat.choose_succ_succ (14 + t) 11
      have heq : 14 + (t + 1) = (14 + t) + 1 := by omega
      rw [heq]
      omega
  have h_ind : ∀ d : ℕ, 14 + 91 * (14 + d) ≤ Nat.choose (14 + d) 13 + 1274 := by
    intro d
    induction d with
    | zero =>
      rw [Nat.add_zero, choose_succ_self_13_14 13]
    | succ t ih =>
      have hstep : Nat.choose ((14 + t) + 1) 13 =
          Nat.choose (14 + t) 12 + Nat.choose (14 + t) 13 := Nat.choose_succ_succ (14 + t) 12
      have hlow := h_ge91 t
      have heq : 14 + (t + 1) = (14 + t) + 1 := by omega
      rw [heq]
      omega
  have h_pt : ∀ m : ℕ, 14 + 91 * m ≤ Nat.choose m 13 + 1274 := by
    intro m
    by_cases hm : m < 14
    · omega
    · have hdecomp : m = 14 + (m - 14) := by omega
      rw [hdecomp]
      exact h_ind (m - 14)
  intro q b
  have hsum : (∑ i : Fin q, (14 + 91 * b i)) ≤ ∑ i : Fin q, (Nat.choose (b i) 13 + 1274) :=
    Finset.sum_le_sum (fun i _ => h_pt (b i))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  exact hsum

end PEqualNP.Outside
