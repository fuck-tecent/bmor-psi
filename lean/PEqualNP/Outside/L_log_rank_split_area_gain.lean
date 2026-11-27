import Mathlib

namespace PEqualNP.Outside

theorem L_log_rank_split_area_gain :
    ∀ n r c s : ℕ, r ≤ s → s < n → c ≤ n-(s+1) →
      let F := fun t => Nat.choose t r * Nat.choose (n-t) c;
      (F s  ≤  F (s+1) ↔ (s+1)*c  ≤  r*(n-s)) := by
  intro n r c s hrs hsn hcn F
  have habs : ∀ {m k : ℕ}, k ≤ m → (m + 1 - k) * Nat.choose (m + 1) k = (m + 1) * Nat.choose m k := by
    intro m k hkm
    have h1 : Nat.choose m k = Nat.choose m (m - k) := by simp [Nat.choose_symm hkm]
    have hsub : m + 1 - k = m - k + 1 := by omega
    have hkm1 : k ≤ m + 1 := by omega
    have h2 : Nat.choose (m + 1) k = Nat.choose (m + 1) (m - k + 1) := by
      rw [← hsub]
      simp [Nat.choose_symm hkm1]
    rw [h1, h2, hsub, mul_comm, ← Nat.add_one_mul_choose_eq m (m - k)]
  have heq1 : (s + 1 - r) * Nat.choose (s + 1) r = (s + 1) * Nat.choose s r := habs hrs
  have heq2 : (n - s - c) * Nat.choose (n - s) c = (n - s) * Nat.choose (n - (s + 1)) c := by
    have h := habs hcn
    have hns : n - (s + 1) + 1 = n - s := by omega
    rw [hns] at h
    exact h
  have hrec : (s + 1 - r) * (n - s) * F (s + 1) = (s + 1) * (n - s - c) * F s := by
    change (s + 1 - r) * (n - s) * (Nat.choose (s + 1) r * Nat.choose (n - (s + 1)) c) =
        (s + 1) * (n - s - c) * (Nat.choose s r * Nat.choose (n - s) c)
    calc (s + 1 - r) * (n - s) * (Nat.choose (s + 1) r * Nat.choose (n - (s + 1)) c)
        = ((s + 1 - r) * Nat.choose (s + 1) r) * ((n - s) * Nat.choose (n - (s + 1)) c) := by ring
      _ = ((s + 1) * Nat.choose s r) * ((n - s - c) * Nat.choose (n - s) c) := by rw [heq1, ← heq2]
      _ = (s + 1) * (n - s - c) * (Nat.choose s r * Nat.choose (n - s) c) := by ring
  set A := (s + 1 - r) * (n - s)
  set B := (s + 1) * (n - s - c)
  have hA_pos : 0 < A := Nat.mul_pos (by omega) (by omega)
  have hFs_pos : 0 < F s :=
    Nat.mul_pos (Nat.choose_pos hrs) (Nat.choose_pos (by omega))
  have hstep1 : F s ≤ F (s + 1) ↔ A ≤ B := by
    constructor
    · intro hle
      have hmul : A * F s ≤ A * F (s + 1) := Nat.mul_le_mul_left A hle
      rw [hrec] at hmul
      by_contra hgt
      have hlt : B * F s < A * F s := Nat.mul_lt_mul_of_pos_right (by omega) hFs_pos
      omega
    · intro hle
      have hmul : A * F s ≤ B * F s := Nat.mul_le_mul_right (F s) hle
      rw [← hrec] at hmul
      by_contra hgt
      have hlt : A * F (s + 1) < A * F s := Nat.mul_lt_mul_of_pos_left (by omega) hA_pos
      omega
  rw [hstep1]
  have hL : A + r * (n - s) = (s + 1) * (n - s) := by
    have h1 : (s + 1 - r) + r = s + 1 := by omega
    calc (s + 1 - r) * (n - s) + r * (n - s) = ((s + 1 - r) + r) * (n - s) := by ring
      _ = (s + 1) * (n - s) := by rw [h1]
  have hR : B + (s + 1) * c = (s + 1) * (n - s) := by
    have h2 : (n - s - c) + c = n - s := by omega
    calc (s + 1) * (n - s - c) + (s + 1) * c = (s + 1) * ((n - s - c) + c) := by ring
      _ = (s + 1) * (n - s) := by rw [h2]
  omega

end PEqualNP.Outside
