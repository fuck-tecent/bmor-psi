import Mathlib

-- The character integral and conjugation laws are adapted from the Apache-2.0
-- BinaryShiftFourierFourth proof in this repository.
open Finset MeasureTheory
open scoped ComplexConjugate

namespace GoldbachTripleFiberCharacter

noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma phase_add (u v : ℝ) : E (u + v) = E u * E v := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma fourier_mode (m : ℤ) :
    (∫ t in (0 : ℝ)..1, E ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [E]
  let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : E ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold E c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hm)
      (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]


theorem eneg (x : ℝ) : conj (E x) = E (-x) := by
  unfold E
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,map_ofNat]
  ring

end GoldbachTripleFiberCharacter

open GoldbachTripleFiberCharacter in
private theorem genericMomentForFiber : (by
  classical
  let S := fun (f : ℕ → ℤ) (A : Finset ℕ) (t : ℝ) => ∑ j : (↥A), Complex.exp (2*(Real.pi:ℂ)*Complex.I*(f j:ℂ)*(t:ℂ))
  exact ∀ (f : ℕ → ℤ) (A : Finset ℕ) (r : ℕ),
    let w := fun u : Fin r → (↥A) => ∑ j : Fin r, f (u j)
    (∫ t in (0:ℝ)..1, ‖S f A t‖^(2*r)) = (((Finset.univ : Finset ((Fin r → (↥A)) × (Fin r → (↥A)))).filter (fun z => w z.1 = w z.2)).card : ℝ)) := by
  classical
  intro S f A r F
  let T := (Finset.univ : Finset (Fin r → (↥A)))
  have term (j : ℕ) (t : ℝ) :
      Complex.exp (2*(Real.pi:ℂ)*Complex.I*(f j:ℂ)*(t:ℂ)) = E ((f j:ℝ)*t) := by
    unfold E
    congr 1
    push_cast
    ring
  have expansion (t : ℝ) : (S f A t)^r = ∑ u ∈ T, E ((F u:ℝ)*t) := by
    change (∑ j : (↥A), Complex.exp (2*(Real.pi:ℂ)*Complex.I*(f j:ℂ)*(t:ℂ)))^r = _
    simp_rw [term]
    calc
      _ = ∏ _i : Fin r, (∑ j : (↥A), E ((f j:ℝ)*t)) := by simp
      _ = ∑ u ∈ T, ∏ i : Fin r, E ((f (u i):ℝ)*t) :=
        Fintype.prod_sum (fun (_ : Fin r) (j : (↥A)) => E ((f j:ℝ)*t))
      _ = _ := by
        apply sum_congr rfl
        intro u _
        unfold E
        rw [← Complex.exp_sum]
        congr 1
        dsimp [F]
        push_cast
        simp only [Finset.sum_mul, Finset.mul_sum]
  let W := T.product T
  let M := fun (w : (Fin r → (↥A)) × (Fin r → (↥A))) (t : ℝ) => E (((F w.1 - F w.2 : ℤ):ℝ)*t)
  have ortho (w) : (∫ t in (0:ℝ)..1, M w t) = if F w.1 = F w.2 then 1 else 0 := by
    simp only [M,fourier_mode,sub_eq_zero]
  have point (t : ℝ) : ((‖S f A t‖^(2*r):ℝ):ℂ) = ∑ w ∈ W, M w t := by
    have sqnorm : ((‖S f A t‖^(2*r):ℝ):ℂ) = (S f A t)^r * conj ((S f A t)^r) := by
      rw [Complex.mul_conj', norm_pow, show 2*r=r*2 by omega, pow_mul]; push_cast; ring
    rw [sqnorm, expansion, map_sum, sum_mul, show W = T ×ˢ T by rfl, sum_product]
    apply sum_congr rfl
    intro u _
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    rw [eneg, ← phase_add]
    dsimp [M]
    push_cast
    ring_nf
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [point]
  rw [intervalIntegral.integral_finsetSum (fun w _ =>
    (show Continuous (M w) by dsimp [M,E]; fun_prop).intervalIntegrable ..)]
  simp_rw [ortho]
  push_cast
  rw [← Finset.sum_filter]
  simp [W,T]

set_option maxHeartbeats 600000 in
theorem Conjectures.Cuts.Task49bb68140c74b1acd0c4723f : (by
  classical
  let S := fun (P : Polynomial ℤ) (A : Finset ℕ) (t : ℝ) => ∑ j : (↥A), Complex.exp (2*(Real.pi:ℂ)*Complex.I*((P.eval (j.val:ℤ):ℤ):ℂ)*(t:ℂ))
  exact ∀ (P : Polynomial ℤ), 1 ≤ P.natDegree → ∀ A : Finset ℕ,
   (∫ t in (0:ℝ)..1, ‖S P A t‖^2) ≤ (P.natDegree:ℝ) * A.card) := by
  classical
  intro S P hd A
  let I := Fin 1 → (↥A)
  let F := fun u : I => ∑ j : Fin 1, P.eval ((u j).val : ℤ)
  let Q : Finset (I × I) := Finset.univ.filter (fun z => F z.1 = F z.2)
  have orth := genericMomentForFiber (fun n : ℕ => P.eval (n:ℤ)) A 1
  change (∫ t in (0:ℝ)..1, ‖S P A t‖^2) = (Q.card:ℝ) at orth
  rw [orth]
  have fiber (x : I) : (Q.filter (fun z => z.1 = x)).card ≤ P.natDegree := by
    let v : ℤ := P.eval ((x 0).val:ℤ)
    let H := P - Polynomial.C v
    have hr : (Q.filter (fun z => z.1 = x)).card ≤ H.roots.toFinset.card := by
      apply Finset.card_le_card_of_injOn (fun z : I × I => ((z.2 0).val:ℤ))
      · intro z hz
        obtain ⟨hz,hx⟩ := Finset.mem_filter.mp hz
        have he := (Finset.mem_filter.mp hz).2
        rw [hx] at he
        apply Multiset.mem_toFinset.mpr
        apply (Polynomial.mem_roots_sub_C (Polynomial.natDegree_pos_iff_degree_pos.mp hd)).mpr
        simpa [F,v,Fin.sum_univ_one] using he.symm
      · intro z hz w hw eq
        have h₁ := (Finset.mem_filter.mp hz).2
        have h₂ := (Finset.mem_filter.mp hw).2
        apply Prod.ext (h₁.trans h₂.symm)
        funext j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        apply Subtype.ext
        change (((z.2 0).val : ℕ) : ℤ) = ((w.2 0).val : ℤ) at eq
        exact Int.ofNat_inj.mp eq
    calc
      _ ≤ _ := hr
      _ ≤ _ := Multiset.toFinset_card_le _
      _ ≤ H.natDegree := Polynomial.card_roots' _
      _ = P.natDegree := Polynomial.natDegree_sub_C
  have card : Q.card ≤ A.card * P.natDegree := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := (Finset.univ : Finset I)) (by intro x _; apply Finset.mem_univ)]
    exact (Finset.sum_le_sum (fun x _ => fiber x)).trans_eq (by simp [I])
  exact_mod_cast (show Q.card ≤ P.natDegree*A.card by simpa [Nat.mul_comm] using card)
