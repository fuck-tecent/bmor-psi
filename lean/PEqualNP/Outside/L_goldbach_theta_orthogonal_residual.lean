import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring

theorem PEqualNP.Outside.L_goldbach_theta_orthogonal_residual :
    ∀ (m r : ℕ) (c : Fin m → Fin r) (R : Fin m ≃ Fin m) (S : Fin r ≃ Fin r)
      (a : Fin m → ℝ), (∀ i, c (R i) = S (c i)) →
      let F := fun j => Finset.univ.filter (fun i => c i = j)
      let b := fun i => (∑ k ∈ F (c i), a k) / ((F (c i)).card : ℝ)
      (∑ i, a i * a (R i)) - (∑ i, b i * b (R i)) =
        ∑ i, (a i - b i) * (a (R i) - b (R i)) := by
  intro m r c R S a equivariant F b
  let avg (j : Fin r) := (∑ k ∈ F j, a k) / ((F j).card : ℝ)
  have centered (j : Fin r) : (∑ i ∈ F j, (a i - avg j)) = 0 := by
    by_cases empty : F j = ∅
    · simp [empty]
    · have hcard : ((F j).card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr empty))
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      simp [avg, hcard, mul_comm ((F j).card : ℝ)]
  have orthogonal (g : Fin r → ℝ) : (∑ i, (a i - b i) * g (c i)) = 0 := by
    rw [← Finset.sum_fiberwise Finset.univ c]
    apply Finset.sum_eq_zero
    intro j _
    change (∑ i ∈ F j, (a i - avg (c i)) * g (c i)) = 0
    calc
      _ = ∑ i ∈ F j, (a i - avg j) * g j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ = 0 := by rw [← Finset.sum_mul, centered, zero_mul]
  have leftCross : (∑ i, (a i - b i) * b (R i)) = 0 := by
    simpa only [b, avg, equivariant] using orthogonal (fun j => avg (S j))
  have rightCross : (∑ i, (a (R i) - b (R i)) * b i) = 0 := by
    let f (i : Fin m) := (a i - b i) * avg (S.symm (c i))
    have hr : (∑ i, f (R i)) = ∑ i, f i := R.sum_comp f
    have hz : (∑ i, f i) = 0 := orthogonal (fun j => avg (S.symm j))
    simpa only [f, equivariant, Equiv.symm_apply_apply, avg, b] using hr.trans hz
  have expand (i : Fin m) :
      (a i - b i) * (a (R i) - b (R i)) =
        (a i * a (R i) - b i * b (R i)) - (a i - b i) * b (R i) -
          (a (R i) - b (R i)) * b i := by ring
  simp only [expand, Finset.sum_sub_distrib, leftCross, rightCross, sub_zero]
