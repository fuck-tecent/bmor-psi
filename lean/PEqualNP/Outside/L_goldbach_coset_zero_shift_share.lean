import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_zero_shift_share :
    let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let B := fun n s : ℕ => ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k*w (s-k); let Z := fun n q : ℕ => ∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q = n % q), B n s; ∀ n q : ℕ, 0<q → Z n q-B n n = (∑ h ∈ Finset.Icc 1 (n/q), (B n (n-h*q)+B n (n+h*q))) := by
  dsimp only
  intro n q hq
  let S := (Finset.range (2 * n + 1)).filter (fun s => s % q = n % q)
  let J := Finset.Icc 1 (n / q)
  let shift : ℕ ⊕ ℕ → ℕ := Sum.elim (fun h => n - h * q) (fun h => n + h * q)
  have hn : n ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), rfl⟩
  have hS {s : ℕ} : s ∈ S.erase n ↔ s ≠ n ∧ s ≤ 2 * n ∧ s ≡ n [MOD q] := by
    simp [S, Nat.ModEq]
  have hJ {h : ℕ} : h ∈ J ↔ 0 < h * q ∧ h * q ≤ n := by
    have hpos : 1 ≤ h ↔ 0 < h * q := by
      constructor
      · intro hh
        exact Nat.mul_pos hh hq
      · intro hh
        by_contra! hzero
        have : h = 0 := by omega
        simp [this] at hh
    rw [show J = Finset.Icc 1 (n / q) from rfl, Finset.mem_Icc,
      Nat.le_div_iff_mul_le hq, hpos]
  have hmap : ∀ z ∈ J.disjSum J, shift z ∈ S.erase n := by
    intro z hz
    apply hS.mpr
    cases z with
    | inl h =>
      obtain ⟨hpos, hle⟩ := hJ.mp (Finset.inl_mem_disjSum.mp hz)
      change n - h * q ≠ n ∧ n - h * q ≤ 2 * n ∧ n - h * q ≡ n [MOD q]
      refine ⟨by omega, by omega, (Nat.modEq_iff_exists_eq_add (Nat.sub_le ..)).mpr ?_⟩
      exact ⟨h, by rw [mul_comm q h, Nat.sub_add_cancel hle]⟩
    | inr h =>
      obtain ⟨hpos, hle⟩ := hJ.mp (Finset.inr_mem_disjSum.mp hz)
      change n + h * q ≠ n ∧ n + h * q ≤ 2 * n ∧ n + h * q ≡ n [MOD q]
      refine ⟨by omega, by omega, Nat.ModEq.symm ?_⟩
      exact (Nat.modEq_iff_exists_eq_add (Nat.le_add_right ..)).mpr ⟨h, by rw [mul_comm q h]⟩
  have hinj : (↑(J.disjSum J) : Set (ℕ ⊕ ℕ)).InjOn shift := by
    rintro (h | h) hh (k | k) hk he
    all_goals
      have hh' := hJ.mp (by simpa using hh : h ∈ J)
      have hk' := hJ.mp (by simpa using hk : k ∈ J)
      dsimp [shift] at he
    · exact congrArg Sum.inl (Nat.eq_of_mul_eq_mul_right hq (by omega))
    · omega
    · omega
    · exact congrArg Sum.inr (Nat.eq_of_mul_eq_mul_right hq (by omega))
  have hsurj : (↑(J.disjSum J) : Set (ℕ ⊕ ℕ)).SurjOn shift (↑(S.erase n) : Set ℕ) := by
    intro s hs
    obtain ⟨hne, hle, hres⟩ := hS.mp hs
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨h, hh⟩ := (Nat.modEq_iff_exists_eq_add hlt.le).mp hres
      rw [mul_comm q h] at hh
      refine ⟨Sum.inl h, Finset.inl_mem_disjSum.mpr (hJ.mpr ⟨by omega, by omega⟩), ?_⟩
      change n - h * q = s
      omega
    · obtain ⟨h, hh⟩ := (Nat.modEq_iff_exists_eq_add hgt.le).mp hres.symm
      rw [mul_comm q h] at hh
      refine ⟨Sum.inr h, Finset.inr_mem_disjSum.mpr (hJ.mpr ⟨by omega, by omega⟩), ?_⟩
      exact hh.symm
  have hsum (A : ℕ → ℝ) :
      (∑ s ∈ S, A s) - A n = ∑ h ∈ J, (A (n - h * q) + A (n + h * q)) := by
    rw [← Finset.sum_erase_add S A hn, add_sub_cancel_right]
    calc
      _ = ∑ z ∈ J.disjSum J, A (shift z) :=
        (Finset.sum_nbij shift hmap hinj hsurj (fun _ _ => rfl)).symm
      _ = _ := by rw [Finset.sum_disjSum, Finset.sum_add_distrib]; rfl
  exact hsum _
