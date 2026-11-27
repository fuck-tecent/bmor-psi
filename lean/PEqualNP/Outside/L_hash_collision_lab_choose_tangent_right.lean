import Mathlib

/-- Pascal's rule in the form used by the telescoping sums below. -/
private lemma pascal (j k : ℕ) (hk : 1 ≤ k) : (j+1).choose k = j.choose k + j.choose (k-1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k-1, (Nat.sub_add_cancel hk).symm⟩
  have h := Nat.choose_succ_succ j k'
  rw [Nat.add_comm] at h
  simpa using h

/-- Telescoped upper tangent bound: `C(t,k) + r*C(t,k-1) ≤ C(t+r,k)`. -/
private lemma tangent_right (k t r : ℕ) (hk : 1 ≤ k) :
    t.choose k + r * t.choose (k-1) ≤ (t+r).choose k := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hstep : t + (r+1) = t + r + 1 := by omega
    rw [hstep]
    have hp : (t+r+1).choose k = (t+r).choose k + (t+r).choose (k-1) := pascal (t+r) k hk
    have hmono : t.choose (k-1) ≤ (t+r).choose (k-1) := Nat.choose_le_choose _ (by omega)
    calc t.choose k + (r+1) * t.choose (k-1)
        = t.choose k + (r * t.choose (k-1) + t.choose (k-1)) := by rw [Nat.succ_mul]
      _ = (t.choose k + r * t.choose (k-1)) + t.choose (k-1) := (Nat.add_assoc _ _ _).symm
      _ ≤ (t+r).choose k + (t+r).choose (k-1) := Nat.add_le_add ih hmono
      _ = (t+r+1).choose k := hp.symm

theorem PEqualNP.Outside.L_hash_collision_lab_choose_tangent_right : ∀ k t m : ℕ, 1 ≤ k → t ≤ m → Nat.choose t k+(m-t)*Nat.choose t (k-1)  ≤  Nat.choose m k := by
  intro k t m hk htm
  have h := tangent_right k t (m - t) hk
  rwa [Nat.add_sub_of_le htm] at h
