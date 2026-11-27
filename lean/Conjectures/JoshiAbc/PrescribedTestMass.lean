import Mathlib

open scoped BigOperators ComplexConjugate

namespace Conjectures.JoshiAbc.PrescribedTestMass_aux

variable {N : ℕ} [NeZero N]

lemma dft_conj (Φ : ZMod N → ℂ) (k : ZMod N) :
    conj (ZMod.dft Φ k) = ∑ j : ZMod N, ZMod.stdAddChar (j * k) * conj (Φ j) := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← AddChar.map_neg_eq_conj, neg_neg]

lemma dft_dft_mul (Φ : ZMod N → ℂ) (j : ZMod N) :
    ∑ k : ZMod N, ZMod.stdAddChar (j * k) * ZMod.dft Φ k = (N : ℂ) * Φ j := by
  have h := congrFun (ZMod.dft_dft Φ) (-j)
  rw [ZMod.dft_apply] at h
  simp only [smul_eq_mul, neg_neg] at h
  calc ∑ k : ZMod N, ZMod.stdAddChar (j * k) * ZMod.dft Φ k
      = ∑ k : ZMod N, ZMod.stdAddChar (-(k * -j)) * ZMod.dft Φ k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have hk : j * k = -(k * -j) := by ring
        rw [hk]
    _ = (N : ℂ) * Φ j := h

lemma parseval (Φ : ZMod N → ℂ) :
    ∑ k : ZMod N, ‖ZMod.dft Φ k‖ ^ 2 = (N : ℝ) * ∑ j : ZMod N, ‖Φ j‖ ^ 2 := by
  have hC : (∑ k : ZMod N, ZMod.dft Φ k * conj (ZMod.dft Φ k))
      = (N : ℂ) * ∑ j : ZMod N, conj (Φ j) * Φ j := by
    have step1 : ∀ k : ZMod N, ZMod.dft Φ k * conj (ZMod.dft Φ k)
        = ∑ j : ZMod N, ZMod.dft Φ k * (ZMod.stdAddChar (j * k) * conj (Φ j)) := by
      intro k
      rw [dft_conj, Finset.mul_sum]
    simp_rw [step1]
    rw [Finset.sum_comm]
    have step2 : ∀ j : ZMod N,
        ∑ k : ZMod N, ZMod.dft Φ k * (ZMod.stdAddChar (j * k) * conj (Φ j))
          = conj (Φ j) * ((N : ℂ) * Φ j) := by
      intro j
      calc ∑ k : ZMod N, ZMod.dft Φ k * (ZMod.stdAddChar (j * k) * conj (Φ j))
          = (∑ k : ZMod N, ZMod.stdAddChar (j * k) * ZMod.dft Φ k) * conj (Φ j) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun k _ => by ring
        _ = conj (Φ j) * ((N : ℂ) * Φ j) := by
            rw [dft_dft_mul]
            ring
    simp_rw [step2]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have key : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = conj z * z := by
    intro z
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  have e1 : ((∑ k : ZMod N, ‖ZMod.dft Φ k‖ ^ 2 : ℝ) : ℂ)
      = ∑ k : ZMod N, ZMod.dft Φ k * conj (ZMod.dft Φ k) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm, key]
  have e2 : ((∑ j : ZMod N, ‖Φ j‖ ^ 2 : ℝ) : ℂ) = ∑ j : ZMod N, conj (Φ j) * Φ j := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ => key _
  apply Complex.ofReal_injective
  rw [e1, Complex.ofReal_mul, e2]
  exact hC

lemma indicator_sum (S : Finset (ZMod N)) :
    ∑ j : ZMod N, ‖(if j ∈ S then (1:ℂ) else 0)‖ ^ 2 = (S.card : ℝ) := by
  have h1 : ∀ j : ZMod N, ‖(if j ∈ S then (1:ℂ) else 0)‖ ^ 2 = if j ∈ S then (1:ℝ) else 0 := by
    intro j
    by_cases hj : j ∈ S
    · simp [hj]
    · simp [hj]
  simp_rw [h1]
  have hb := Finset.sum_boole (R := ℝ) (fun j : ZMod N => j ∈ S) (Finset.univ : Finset (ZMod N))
  have hf : ((Finset.univ : Finset (ZMod N)).filter (fun j : ZMod N => j ∈ S)).card = S.card := by
    congr 1
    ext x
    simp
  calc (∑ j : ZMod N, if j ∈ S then (1:ℝ) else 0)
      = (((Finset.univ : Finset (ZMod N)).filter (fun j : ZMod N => j ∈ S)).card : ℝ) := hb
    _ = (S.card : ℝ) := by rw [hf]

end Conjectures.JoshiAbc.PrescribedTestMass_aux

theorem Conjectures.JoshiAbc.PrescribedTestMass : ∀ (N : ℕ) [NeZero N] (S : Finset (ZMod N)), let u := fun x : ZMod N => if x ∈ S then (1:ℂ) else 0; (∑ k : ZMod N, ‖ZMod.dft u k‖^2)/(N:ℝ)^2 = (S.card:ℝ)/N := by
  intro N _ S
  show (∑ k : ZMod N, ‖ZMod.dft (fun x : ZMod N => if x ∈ S then (1:ℂ) else 0) k‖ ^ 2)
      / ((N : ℝ)) ^ 2 = (S.card : ℝ) / (N : ℝ)
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hpar := Conjectures.JoshiAbc.PrescribedTestMass_aux.parseval
    (N := N) (Φ := fun x : ZMod N => if x ∈ S then (1:ℂ) else 0)
  rw [Conjectures.JoshiAbc.PrescribedTestMass_aux.indicator_sum] at hpar
  rw [hpar]
  field_simp
