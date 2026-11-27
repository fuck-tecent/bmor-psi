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

/-- Per-index tangent inequality, valid for every `b` (no case split on the caller side). -/
private lemma per_index (k t : ℕ) (hk : 1 ≤ k) (b : ℕ) :
    t.choose k + b * t.choose (k-1) ≤ b.choose k + t * t.choose (k-1) := by
  by_cases h : b ≤ t
  · have hl := tangent_left k b (t - b) hk
    rw [Nat.add_sub_of_le h] at hl
    refine le_trans (Nat.add_le_add_right hl (b * t.choose (k-1))) (le_of_eq ?_)
    rw [Nat.add_assoc, ← Nat.add_mul, Nat.sub_add_cancel h]
  · have hlt : t < b := not_le.mp h
    have hr := tangent_right k t (b - t) hk
    rw [Nat.add_sub_of_le (le_of_lt hlt)] at hr
    refine le_trans (le_of_eq ?_) (Nat.add_le_add_right hr (t * t.choose (k-1)))
    rw [Nat.add_assoc, ← Nat.add_mul, Nat.sub_add_cancel (le_of_lt hlt)]

theorem PEqualNP.Outside.L_hash_collision_lab_choose_tangent_aggregate : ∀ k t q : ℕ, 1≤k → ∀ b : Fin q → ℕ, q*Nat.choose t k+Nat.choose t (k-1)*(∑ i,b i) ≤ (∑ i,Nat.choose (b i) k)+q*t*Nat.choose t (k-1) := by
  intro k t q hk b
  have hsum : (∑ i : Fin q, (Nat.choose t k + b i * Nat.choose t (k-1))) ≤
      (∑ i : Fin q, (Nat.choose (b i) k + t * Nat.choose t (k-1))) :=
    Finset.sum_le_sum (fun i _ => per_index k t hk (b i))
  have hL : (∑ i : Fin q, (Nat.choose t k + b i * Nat.choose t (k-1)))
      = q * Nat.choose t k + Nat.choose t (k-1) * (∑ i : Fin q, b i) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, Nat.nsmul_eq_mul]
    ring
  have hR : (∑ i : Fin q, (Nat.choose (b i) k + t * Nat.choose t (k-1)))
      = (∑ i : Fin q, Nat.choose (b i) k) + q * t * Nat.choose t (k-1) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul]
    ring
  rw [hL, hR] at hsum
  exact hsum
