import Mathlib

/- Adapted from RagdollSandrone's Goldbach PR 1665, authoritative run 45583536797.
Source commit 35c8d8e6585977b8a59d4d40c22410082edbd4a0 in RagdollSandrone/goldbach-proofs.
Licensed under Apache-2.0 (see LICENSE). Only the declaration name and visibility were changed. -/
private theorem zeroShift :
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

private theorem rootFilter {L : ℕ} {z : ℂ} (hz : IsPrimitiveRoot z L) (h : ℕ) :
    (∑ j ∈ Finset.range L, (z^j)^h) = if L ∣ h then (L:ℂ) else 0 := by
  have swap (j : ℕ) : (z^j)^h = (z^h)^j := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  simp_rw [swap]
  by_cases hd : L ∣ h
  · simp [hd, (hz.pow_eq_one_iff_dvd h).2 hd]
  · have hne : z^h ≠ 1 := fun he => hd ((hz.pow_eq_one_iff_dvd h).1 he)
    have top : (z^h)^L = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
    rw [ite_eq_right hd, geom_sum_eq hne, top, sub_self, zero_div]

private theorem selectMultiples (H L : ℕ) (hL : 0 < L) (A : ℕ → ℂ) :
    (∑ j ∈ Finset.Icc 1 (H/L), A (j*L)) =
      ∑ h ∈ (Finset.Icc 1 H).filter (fun h => L ∣ h), A h := by
  apply Finset.sum_nbij (fun j => j*L)
  · intro j hj
    obtain ⟨hj1,hjH⟩ := Finset.mem_Icc.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hj1 hL,
      (Nat.le_div_iff_mul_le hL).mp hjH⟩, dvd_mul_left _ _⟩
  · intro a _ b _ he
    exact Nat.eq_of_mul_eq_mul_right hL he
  · intro h hh
    obtain ⟨hI, hd⟩ := Finset.mem_filter.mp hh
    obtain ⟨h1,hH⟩ := Finset.mem_Icc.mp hI
    have he := Nat.div_mul_cancel hd
    have hpos : 0 < h/L := Nat.div_pos (Nat.le_of_dvd h1 hd) hL
    exact ⟨h/L, Finset.mem_Icc.mpr ⟨hpos, Nat.div_le_div_right hH⟩, he⟩
  · intro j _
    rfl

private theorem sumPhases {z : ℂ} {L : ℕ} (hz : IsPrimitiveRoot z L) (hL : 0<L)
    (H : ℕ) (A : ℕ → ℂ) :
    (∑ j ∈ Finset.range L, ∑ h ∈ Finset.Icc 1 H, A h*(z^j)^h) =
      (L:ℂ)*∑ j ∈ Finset.Icc 1 (H/L), A (j*L) := by
  rw [Finset.sum_comm, selectMultiples H L hL A, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.mul_sum, rootFilter hz]
  split_ifs <;> ring

theorem PEqualNP.Outside.L_goldbach_coset_phase_decimation :
    let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0; let B := fun n s : ℕ => ∑ k ∈ (Finset.range (n+1)).filter (fun k => k ≤ s ∧ s-k ≤ n), w k*w (s-k); let Z := fun n q : ℕ => ∑ s ∈ (Finset.range (2*n+1)).filter (fun s => s % q = n % q), B n s; let Y := fun (n q : ℕ) (z : ℂ) => (B n n:ℂ) + ∑ h ∈ Finset.Icc 1 (n/q), ((B n (n+h*q):ℂ)*z^h + (B n (n-h*q):ℂ)*(z⁻¹)^h); ∀ (n q L : ℕ) (z : ℂ), 0<q → 0<L → IsPrimitiveRoot z L → (∑ j ∈ Finset.range L, Y n q (z^j))/(L:ℂ)=(Z n (q*L):ℂ) := by
  intro w B Z Y n q L z hq hL hz
  let A (h : ℕ) : ℂ := B n (n+h*q)
  let C (h : ℕ) : ℂ := B n (n-h*q)
  have splitSum (j : ℕ) : Y n q (z^j) =
      (B n n : ℂ) + ((∑ h ∈ Finset.Icc 1 (n/q), A h*(z^j)^h) +
        ∑ h ∈ Finset.Icc 1 (n/q), C h*(z⁻¹^j)^h) := by
    dsimp only [Y,A,C]
    rw [Finset.sum_add_distrib]
    simp only [inv_pow]
  have hshift := zeroShift n (q*L) (Nat.mul_pos hq hL)
  change Z n (q*L)-B n n = ∑ j ∈ Finset.Icc 1 (n/(q*L)),
    (B n (n-j*(q*L))+B n (n+j*(q*L))) at hshift
  have regroup : ((B n n:ℝ):ℂ) + ((∑ j ∈ Finset.Icc 1 (n/q/L), A (j*L)) +
      ∑ j ∈ Finset.Icc 1 (n/q/L), C (j*L)) = (Z n (q*L):ℂ) := by
    rw [Nat.div_div_eq_div_mul, ← Finset.sum_add_distrib]
    have he : Z n (q*L) = B n n + ∑ j ∈ Finset.Icc 1 (n/(q*L)),
        (B n (n-j*(q*L))+B n (n+j*(q*L))) := by linarith
    rw [he]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [A,C, Nat.mul_assoc, Nat.mul_comm L q, add_comm]
  simp_rw [splitSum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sumPhases hz hL, sumPhases hz.inv hL]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  apply (div_eq_iff (by exact_mod_cast hL.ne' : (L:ℂ) ≠ 0)).2
  rw [← regroup]
  ring
