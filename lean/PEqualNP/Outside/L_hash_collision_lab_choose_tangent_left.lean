import Mathlib

/-- Pascal's rule in the form used by the telescoping sums below. -/
private lemma pascal (j k : ℕ) (hk : 1 ≤ k) : (j+1).choose k = j.choose k + j.choose (k-1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k-1, (Nat.sub_add_cancel hk).symm⟩
  have h := Nat.choose_succ_succ j k'
  rw [Nat.add_comm] at h
  simpa using h

/-- Telescoped lower tangent bound: `C(m+r,k) ≤ C(m,k) + r*C(m+r,k-1)`. -/
private lemma tangent_left (k m r : ℕ) (hk : 1 ≤ k) :
    (m+r).choose k ≤ m.choose k + r * (m+r).choose (k-1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hstep : m + (r+1) = m + r + 1 := by omega
    rw [hstep]
    have hp : (m+r+1).choose k = (m+r).choose k + (m+r).choose (k-1) := pascal (m+r) k hk
    have hmono : (m+r).choose (k-1) ≤ (m+r+1).choose (k-1) := Nat.choose_le_choose _ (by omega)
    have hkey : r * (m+r).choose (k-1) + (m+r).choose (k-1) = (r+1) * (m+r).choose (k-1) := by
      rw [Nat.succ_mul]
    calc (m+r+1).choose k = (m+r).choose k + (m+r).choose (k-1) := hp
      _ ≤ (m.choose k + r * (m+r).choose (k-1)) + (m+r).choose (k-1) := Nat.add_le_add ih le_rfl
      _ = m.choose k + (r * (m+r).choose (k-1) + (m+r).choose (k-1)) := Nat.add_assoc _ _ _
      _ = m.choose k + (r+1) * (m+r).choose (k-1) := by rw [hkey]
      _ ≤ m.choose k + (r+1) * (m+r+1).choose (k-1) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ hmono) _

theorem PEqualNP.Outside.L_hash_collision_lab_choose_tangent_left : ∀ k t m : ℕ, 1≤k → m≤t → Nat.choose t k ≤ Nat.choose m k+(t-m)*Nat.choose t (k-1) := by
  intro k t m hk hmt
  have h := tangent_left k m (t - m) hk
  rwa [Nat.add_sub_of_le hmt] at h
