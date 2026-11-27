import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Ring

open scoped BigOperators Classical

namespace GoldbachOddMoment

variable {N : ℕ} [NeZero N]

private theorem allKernel (a b : (ZMod N)ˣ) :
    (∑ χ : DirichletCharacter ℂ N, star (χ (a : ZMod N)) * χ (b : ZMod N)) =
      if a = b then (N.totient : ℂ) else 0 := by
  have h (χ : DirichletCharacter ℂ N) :
      star (χ (a : ZMod N)) = χ (a : ZMod N)⁻¹ := by
    rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
  simp_rw [h]
  simpa only [Units.val_inj] using
    (DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit (b : ZMod N))

/-- Odd-character orthogonality for one fixed modulus, including imprimitive characters. -/
theorem oddKernel (a b : (ZMod N)ˣ) :
    2 * (∑ χ : DirichletCharacter ℂ N with χ.Odd,
      star (χ (a : ZMod N)) * χ (b : ZMod N)) =
    (if a = b then (N.totient : ℂ) else 0) -
      (if a = -b then (N.totient : ℂ) else 0) := by
  classical
  rw [← allKernel a b, ← allKernel a (-b), ← Finset.sum_sub_distrib,
    Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  rcases χ.even_or_odd with he | ho
  · simp [he.not_odd, he.eval_neg]
  · simp [ho, ho.eval_neg]
    ring

/-- The mixed moment tests two different weights at equal and opposite residues. -/
theorem oddMixedMoment (F G : (ZMod N)ˣ → ℂ) :
    2 * (∑ χ : DirichletCharacter ℂ N with χ.Odd,
      star (∑ a, F a * χ (a : ZMod N)) * (∑ b, G b * χ (b : ZMod N))) =
    (N.totient : ℂ) * ∑ a, star (F a) * (G a - G (-a)) := by
  classical
  let oddChars := Finset.univ.filter (DirichletCharacter.Odd (m := N) (S := ℂ))
  change 2 * (∑ χ ∈ oddChars, _) = _
  have expand (χ : DirichletCharacter ℂ N) :
      star (∑ a : (ZMod N)ˣ, F a * χ (a : ZMod N)) * (∑ b, G b * χ (b : ZMod N)) =
        ∑ a, ∑ b, (star (F a) * G b) * (star (χ (a : ZMod N)) * χ (b : ZMod N)) := by
    rw [star_sum, Finset.sum_mul]
    simp only [star_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have negTest (a b : (ZMod N)ˣ) : a = -b ↔ -a = b := by
    constructor <;> intro h
    · simp [h]
    · rw [← h, neg_neg]
  calc
    _ = ∑ a, ∑ b, (star (F a) * G b) *
        (2 * ∑ χ ∈ oddChars, star (χ (a : ZMod N)) * χ (b : ZMod N)) := by
      rw [Finset.sum_congr rfl (fun χ _ => expand χ), Finset.sum_comm]
      simp_rw [Finset.sum_comm (s := oddChars)]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := by
      simp only [oddChars, oddKernel, negTest, mul_sub, mul_ite, mul_zero,
        Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp only [← Finset.sum_mul]
      ring

end GoldbachOddMoment

theorem PEqualNP.Outside.L_goldbach_odd_character_mixed_moment :
    ∀ (N : ℕ) [NeZero N] (F G : (ZMod N)ˣ → ℂ), let oddChars := @Finset.filter (DirichletCharacter ℂ N) (fun χ => χ.Odd) (fun χ => Classical.propDecidable χ.Odd) Finset.univ; let T := fun (W : (ZMod N)ˣ → ℂ) (χ : DirichletCharacter ℂ N) => Finset.univ.sum (fun a : (ZMod N)ˣ => W a * χ (a : ZMod N)); 2 * oddChars.sum (fun χ => star (T F χ) * T G χ) = (N.totient : ℂ) * Finset.univ.sum (fun a : (ZMod N)ˣ => star (F a) * (G a - G (-a))) := by
  intro N inst F G
  exact GoldbachOddMoment.oddMixedMoment F G
