import Mathlib

namespace Conjectures.Goldbach.ReflectionPartialInvolution_aux

variable {m : ℕ} [NeZero m] {N : ZMod m}

theorem key (A F : Finset (ZMod m)) (K D : Matrix (ZMod m) (ZMod m) ℂ)
    (hA : A = (Finset.univ : Finset (ZMod m)).filter (fun x => IsUnit x ∧ IsUnit (N - x)))
    (hF : F = A.filter (fun x => N - x = x))
    (hK : K = fun x y => if x ∈ A ∧ y = N - x then 1 else 0)
    (hD : D = Matrix.diagonal (fun x => if x ∈ A then (1 : ℂ) else 0)) :
    (K * K = D) ∧
      2 * Module.finrank ℂ (Module.End.eigenspace K.mulVecLin 1) = A.card + F.card ∧
      2 * Module.finrank ℂ (Module.End.eigenspace K.mulVecLin (-1)) = A.card - F.card := by
  have hAmem : ∀ x : ZMod m, x ∈ A ↔ (IsUnit x ∧ IsUnit (N - x)) := by
    intro x; rw [hA, Finset.mem_filter]; simp
  have hK' : ∀ x y : ZMod m, K x y = if x ∈ A ∧ y = N - x then 1 else 0 := by
    intro x y; rw [hK]
  have hsymm : ∀ x : ZMod m, x ∈ A → N - x ∈ A := by
    intro x hx
    rw [hAmem] at hx ⊢
    exact ⟨hx.2, by simpa using hx.1⟩
  have hsub : ∀ x : ZMod m, N - (N - x) = x := fun x => sub_sub_cancel N x
  -- Step 1 : the square of K
  have hKK : K * K = D := by
    ext x z
    rw [hD, Matrix.diagonal_apply]
    simp only [Matrix.mul_apply, hK']
    by_cases hx : x ∈ A
    · have hx' : N - x ∈ A := hsymm x hx
      rw [Finset.sum_eq_single (N - x) (fun y _ hy => by simp [hy]) (by simp)]
      simp [hx, hx', hsub, eq_comm]
    · simp [hx]
  -- Step 2 : pointwise description of the two linear maps
  have hT : ∀ (v : ZMod m → ℂ) (y : ZMod m),
      K.mulVecLin v y = if y ∈ A then v (N - y) else 0 := by
    intro v y
    rw [Matrix.mulVecLin_apply]
    simp only [Matrix.mulVec, dotProduct, hK']
    by_cases hy : y ∈ A <;> simp [hy, Finset.sum_ite_eq']
  set Pm : Module.End ℂ (ZMod m → ℂ) := D.mulVecLin with hPmdef
  have hP : ∀ (v : ZMod m → ℂ) (y : ZMod m), Pm v y = if y ∈ A then v y else 0 := by
    intro v y
    rw [hPmdef, Matrix.mulVecLin_apply]
    simp only [Matrix.mulVec, dotProduct, hD, Matrix.diagonal_apply]
    by_cases hy : y ∈ A <;> simp [hy, Finset.sum_ite_eq]
  -- Step 3 : the two spectral projections
  set Qp : Module.End ℂ (ZMod m → ℂ) := (1 / 2 : ℂ) • (Pm + K.mulVecLin) with hQpdef
  set Qm : Module.End ℂ (ZMod m → ℂ) := (1 / 2 : ℂ) • (Pm - K.mulVecLin) with hQmdef
  have hQp : ∀ (v : ZMod m → ℂ) (y : ZMod m),
      Qp v y = if y ∈ A then (1 / 2 : ℂ) * (v y + v (N - y)) else 0 := by
    intro v y
    have h1 : Qp v = (1 / 2 : ℂ) • (Pm v + K.mulVecLin v) := by
      rw [hQpdef, LinearMap.smul_apply, LinearMap.add_apply]
    have h2 : Qp v y = (1 / 2 : ℂ) * (Pm v y + K.mulVecLin v y) := by
      have h3 := congrFun h1 y
      simpa using h3
    rw [h2, hP, hT]
    by_cases hy : y ∈ A <;> simp [hy]
  have hQm : ∀ (v : ZMod m → ℂ) (y : ZMod m),
      Qm v y = if y ∈ A then (1 / 2 : ℂ) * (v y - v (N - y)) else 0 := by
    intro v y
    have h1 : Qm v = (1 / 2 : ℂ) • (Pm v - K.mulVecLin v) := by
      rw [hQmdef, LinearMap.smul_apply, LinearMap.sub_apply]
    have h2 : Qm v y = (1 / 2 : ℂ) * (Pm v y - K.mulVecLin v y) := by
      have h3 := congrFun h1 y
      simpa using h3
    rw [h2, hP, hT]
    by_cases hy : y ∈ A <;> simp [hy]
  have hQpproj : LinearMap.IsProj (Module.End.eigenspace K.mulVecLin 1) Qp := by
    constructor
    · intro v
      rw [Module.End.mem_eigenspace_iff, one_smul]
      funext y
      rw [hT]
      by_cases hy : y ∈ A
      · have h1 : N - y ∈ A := hsymm y hy
        simp only [hQp, if_pos hy, if_pos h1, hsub]
        ring
      · simp only [hQp, if_neg hy]
    · intro v hv
      rw [Module.End.mem_eigenspace_iff, one_smul] at hv
      funext y
      rw [hQp]
      by_cases hy : y ∈ A
      · rw [if_pos hy]
        have h2 := congrFun hv (N - y)
        rw [hT, if_pos (hsymm y hy), hsub] at h2
        rw [h2.symm]
        ring
      · rw [if_neg hy]
        have h2 := congrFun hv y
        rw [hT, if_neg hy] at h2
        exact h2
  have hQmproj : LinearMap.IsProj (Module.End.eigenspace K.mulVecLin (-1)) Qm := by
    constructor
    · intro v
      rw [Module.End.mem_eigenspace_iff, neg_smul, one_smul]
      funext y
      rw [hT]
      by_cases hy : y ∈ A
      · have h1 : N - y ∈ A := hsymm y hy
        simp only [hQm, if_pos hy, if_pos h1, hsub, Pi.neg_apply]
        ring
      · simp only [hQm, if_neg hy, Pi.neg_apply, neg_zero]
    · intro v hv
      rw [Module.End.mem_eigenspace_iff] at hv
      have hv' : K.mulVecLin v = -v := by rw [hv, neg_smul, one_smul]
      funext y
      rw [hQm]
      by_cases hy : y ∈ A
      · rw [if_pos hy]
        have h2 := congrFun hv' (N - y)
        rw [hT, if_pos (hsymm y hy), hsub] at h2
        have h3 : v (N - y) = -(v y) := by
          have h4 := congrArg Neg.neg h2
          simpa using h4.symm
        rw [h3]
        ring
      · rw [if_neg hy]
        have h2 := congrFun hv' y
        rw [hT, if_neg hy] at h2
        exact (neg_eq_zero.mp h2.symm).symm
  -- Step 4 : traces
  have hAeq : (Finset.univ : Finset (ZMod m)).filter (fun x => x ∈ A) = A := by
    ext x; simp
  have htrP : LinearMap.trace ℂ (ZMod m → ℂ) Pm = (A.card : ℂ) := by
    rw [hPmdef, ← Matrix.toLin'_apply' D, Matrix.trace_toLin'_eq, hD, Matrix.trace_diagonal]
    have hsum : (∑ x : ZMod m, (if x ∈ A then (1 : ℂ) else 0))
        = (((Finset.univ : Finset (ZMod m)).filter (fun x => x ∈ A)).card : ℂ) :=
      Finset.sum_boole _ _
    rw [hAeq] at hsum
    exact hsum
  have htrT : LinearMap.trace ℂ (ZMod m → ℂ) K.mulVecLin = (F.card : ℂ) := by
    rw [← Matrix.toLin'_apply' K, Matrix.trace_toLin'_eq]
    have hFilt : (Finset.univ : Finset (ZMod m)).filter (fun x => x ∈ A ∧ x = N - x)
        = A.filter (fun x => N - x = x) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hc; exact ⟨hc.1, hc.2.symm⟩
      · intro hc; exact ⟨hc.1, hc.2.symm⟩
    calc K.trace = ∑ x : ZMod m, (if x ∈ A ∧ x = N - x then (1 : ℂ) else 0) := by
          simp only [Matrix.trace, Matrix.diag_apply, hK']
      _ = (((Finset.univ : Finset (ZMod m)).filter
              (fun x => x ∈ A ∧ x = N - x)).card : ℂ) := Finset.sum_boole _ _
      _ = ((A.filter (fun x => N - x = x)).card : ℂ) := by rw [hFilt]
      _ = (F.card : ℂ) := by rw [hF]
  have htrQp : LinearMap.trace ℂ (ZMod m → ℂ) Qp
      = (1 / 2 : ℂ) * ((A.card : ℂ) + (F.card : ℂ)) := by
    rw [hQpdef, map_smul, map_add, htrP, htrT]
    simp [smul_eq_mul]
  have htrQm : LinearMap.trace ℂ (ZMod m → ℂ) Qm
      = (1 / 2 : ℂ) * ((A.card : ℂ) - (F.card : ℂ)) := by
    rw [hQmdef, map_smul, map_sub, htrP, htrT]
    simp [smul_eq_mul]
  have hfinp : LinearMap.trace ℂ (ZMod m → ℂ) Qp
      = (Module.finrank ℂ (Module.End.eigenspace K.mulVecLin 1) : ℂ) := hQpproj.trace
  have hfinm : LinearMap.trace ℂ (ZMod m → ℂ) Qm
      = (Module.finrank ℂ (Module.End.eigenspace K.mulVecLin (-1)) : ℂ) := hQmproj.trace
  have hFsub : F.card ≤ A.card := by rw [hF]; exact Finset.card_filter_le _ _
  refine ⟨hKK, ?_, ?_⟩
  · have h2 : (2 : ℂ) * (Module.finrank ℂ (Module.End.eigenspace K.mulVecLin 1) : ℂ)
        = (A.card : ℂ) + (F.card : ℂ) := by
      rw [← hfinp, htrQp]
      ring
    have hz : (2 : ℤ) * ((Module.finrank ℂ (Module.End.eigenspace K.mulVecLin 1) : ℕ) : ℤ)
        = (A.card : ℤ) + (F.card : ℤ) := by
      exact_mod_cast h2
    omega
  · have h2 : (2 : ℂ) * (Module.finrank ℂ (Module.End.eigenspace K.mulVecLin (-1)) : ℂ)
        = (A.card : ℂ) - (F.card : ℂ) := by
      rw [← hfinm, htrQm]
      ring
    have hz : (2 : ℤ) * ((Module.finrank ℂ (Module.End.eigenspace K.mulVecLin (-1)) : ℕ) : ℤ)
        = (A.card : ℤ) - (F.card : ℤ) := by
      exact_mod_cast h2
    omega

end Conjectures.Goldbach.ReflectionPartialInvolution_aux

theorem Conjectures.Goldbach.ReflectionPartialInvolution :
  ∀ (m : ℕ) [NeZero m] (N : ZMod m),
  let A := (Finset.univ : Finset (ZMod m)).filter (fun x => IsUnit x ∧ IsUnit (N-x))
  let F := A.filter (fun x => N-x=x)
  let K : Matrix (ZMod m) (ZMod m) ℂ := fun x y => if x ∈ A ∧ y=N-x then 1 else 0
  (K*K = Matrix.diagonal (fun x => if x ∈ A then (1 : ℂ) else 0)) ∧
    2 * Module.finrank ℂ (Module.End.eigenspace K.mulVecLin 1) = A.card+F.card ∧
    2 * Module.finrank ℂ (Module.End.eigenspace K.mulVecLin (-1)) = A.card-F.card := by
  intro m _ N
  dsimp only
  exact Conjectures.Goldbach.ReflectionPartialInvolution_aux.key _ _ _ _ rfl rfl rfl rfl
