import Mathlib
import Conjectures.Goldbach.SharpSingularSeriesRatios

/-!
At every odd prime p, the p − 2 nonprincipal characters are primitive.
At target two their combined squared mass is the ordinary squared mass
times 1/(p − 2). Summing over prime conductors already gives an
unbounded family, by divergence of the sum of reciprocals of the primes.

The prime-level ratio calculation adapts zxg0623's proof in PR #4023
(Apache-2.0), using the exact ratio and finite-field Jacobi sum norms.
-/

namespace PartnerPrimeSum

open Finset

theorem arbitrarily_large (K : ℝ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ 3 ≤ p) ∧
      K < ∑ p ∈ P, 1 / ((p : ℝ) - 2) := by
  classical
  let f := Set.indicator {p : ℕ | Nat.Prime p} (fun n : ℕ ↦ (1 : ℝ) / n)
  have hu : ∃ s : Finset ℕ, K + 1 < ∑ p ∈ s, f p := by
    by_contra! h
    apply not_summable_one_div_on_primes
    exact summable_of_sum_le (c := K + 1)
      (Set.indicator_nonneg (fun _ _ => by positivity)) h
  obtain ⟨s, hs⟩ := hu
  let Q := s.filter Nat.Prime
  let P := Q.erase 2
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ 3 ≤ p := by
    have hpr := (mem_filter.mp (mem_erase.mp hp).2).2
    exact ⟨hpr, by have := hpr.two_le; have := (mem_erase.mp hp).1; omega⟩
  refine ⟨P, hP, ?_⟩
  have hq : ∑ p ∈ s, f p = ∑ p ∈ Q, (1:ℝ)/p := by
    simp [Q, f, sum_filter, Set.indicator_apply]
  rw [hq] at hs
  have hsum : ∑ p ∈ Q, (1:ℝ)/p ≤ (∑ p ∈ P, (1:ℝ)/p) + 1 := by
    by_cases hh : 2 ∈ Q
    · have eqn := sum_erase_add Q (fun p : ℕ => (1:ℝ)/p) hh
      change ∑ p ∈ Q, (1:ℝ)/p ≤ (∑ p ∈ Q.erase 2, (1:ℝ)/p) + 1
      rw [← eqn]
      norm_num
    · simp [P, erase_eq_of_notMem hh]
  have hcomp : (∑ p ∈ P, (1:ℝ)/p) ≤ ∑ p ∈ P, 1 / ((p:ℝ)-2) := by
    apply sum_le_sum
    intro p hp
    have h : (3:ℝ) ≤ p := by exact_mod_cast (hP p hp).2
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  linarith

end PartnerPrimeSum

namespace PartnerQuadratic
open DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct SquarefreeTwistedGoldbachDensity

theorem prime_char_primitive (p : ℕ) (hp : p.Prime)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) : χ.IsPrimitive := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  rcases (Nat.dvd_prime hp).mp χ.conductor_dvd_level with h | h
  · exact False.elim (hχ (eq_one_iff_conductor_eq_one.mpr h))
  · exact h

theorem prime_partner_norm (p : ℕ) (hp : p.Prime) (ho : 3 ≤ p)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    ‖series (1 : DirichletCharacter ℂ 1) χ 2‖ =
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖ / ((p:ℝ)-2) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : NeZero p := ⟨hp.ne_zero⟩
  have hn : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast (mt (ZMod.natCast_eq_zero_iff 2 p).mp
      (Nat.not_dvd_of_pos_of_lt (by decide) (by omega : 2 < p)))
  have hden : ‖J (1 : DirichletCharacter ℂ p) 1 (2 : ZMod p)‖ = (p:ℝ) - 2 := by
    change ‖localSum (1 : DirichletCharacter ℂ p) 1 (2 : ZMod p)‖ = _
    simpa [hn] using local_norm (1 : DirichletCharacter ℂ p) 1 (2 : ZMod p)
  have hnum : ‖J (1 : DirichletCharacter ℂ p) χ (2 : ZMod p)‖ = 1 := by
    change ‖localSum (1 : DirichletCharacter ℂ p) χ (2 : ZMod p)‖ = _
    simpa [hn,hχ] using local_norm (1 : DirichletCharacter ℂ p) χ (2 : ZMod p)
  have he := exact_ratio isPrimitive_one_level_one (prime_char_primitive p hp χ hχ)
    (one_dvd p) (dvd_refl p) 2 (by decide) (by decide)
  rw [map_one, changeLevel_self, ← principal_card] at he
  change series (1 : DirichletCharacter ℂ 1) χ 2 =
    series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2 *
      (J 1 χ (2:ZMod p) / J 1 1 (2:ZMod p)) at he
  rw [he, norm_mul, norm_div, hnum, hden]
  ring

end PartnerQuadratic

namespace PartnerQuadratic

open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachLocalProduct

theorem ordinary_norm_pos :
    0 < ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖ :=
  lt_of_lt_of_le zero_lt_one
    ((TwistedGoldbachMixedPrincipal.ordinary_at_least_one 2 (by decide) (by decide)).trans
      (Complex.re_le_norm _))

/-- At a prime conductor all p−2 nonprincipal partners contribute the same
squared magnitude; summing gives exactly the reciprocal factor 1/(p−2). -/
theorem prime_row (p : ℕ) (hp : p.Prime) (ho : 3 ≤ p) :
    ∃ T : Finset (DirichletCharacter ℂ p), (∀ χ ∈ T, χ.IsPrimitive) ∧
      (∑ χ ∈ T, ‖series (1 : DirichletCharacter ℂ 1) χ 2‖ ^ 2) =
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖ ^ 2 *
        (1 / ((p : ℝ) - 2)) := by
  classical
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let T := (univ : Finset (DirichletCharacter ℂ p)).erase 1
  have hcard : T.card = p - 2 := by
    dsimp only [T]
    rw [card_erase_of_mem (mem_univ _), card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, Nat.totient_prime hp]
    omega
  refine ⟨T, fun χ hχ => prime_char_primitive p hp χ (mem_erase.mp hχ).1, ?_⟩
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖
  calc
    _ = ∑ _χ ∈ T, (O / ((p : ℝ)-2))^2 := by
      apply sum_congr rfl
      intro χ hχ
      rw [prime_partner_norm p hp ho χ (mem_erase.mp hχ).1]
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, hcard, Nat.cast_sub (by omega : 2 ≤ p)]
      have hpos : 0 < (p : ℝ)-2 := by linarith only [show (3 : ℝ) ≤ p by exact_mod_cast ho]
      change ((p : ℝ)-(2 : ℕ)) * (O / ((p : ℝ)-2))^2 = O^2 * (1 / ((p : ℝ)-2))
      push_cast
      field_simp

end PartnerQuadratic

open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachLocalProduct

theorem Conjectures.Goldbach.PartnerQuadraticObstruction : (
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  exact ∀ K : ℝ, ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s), (∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive ∧ Squarefree b.1) ∧ K * ‖O 2‖ ^ 2 < ∑ b ∈ F, ‖S (1 : DirichletCharacter ℂ 1) b.2 2‖ ^ 2
) := by
  classical
  dsimp only
  intro K
  obtain ⟨P, hP, hlarge⟩ := PartnerPrimeSum.arbitrarily_large K
  let mass := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) 2‖^2
  have hm : 0 < mass := pow_pos PartnerQuadratic.ordinary_norm_pos _
  let row (p : ℕ) : Finset (DirichletCharacter ℂ p) :=
    if h : p.Prime ∧ 3 ≤ p then (PartnerQuadratic.prime_row p h.1 h.2).choose else ∅
  have row_spec (p : ℕ) (hp : p ∈ P) :
      (∀ χ ∈ row p, χ.IsPrimitive) ∧
      (∑ χ ∈ row p, ‖series (1 : DirichletCharacter ℂ 1) χ 2‖ ^ 2) =
        mass * (1 / ((p : ℝ) - 2)) := by
    have h := hP p hp
    simpa only [row, dite_eq_left h, mass] using (PartnerQuadratic.prime_row p h.1 h.2).choose_spec
  refine ⟨P.sigma row, ?_, ?_⟩
  · intro b hb
    obtain ⟨hp, hχ⟩ := mem_sigma.mp hb
    exact ⟨(hP _ hp).1.ne_zero, (row_spec _ hp).1 _ hχ, (hP _ hp).1.squarefree⟩
  · change K * mass < ∑ b ∈ P.sigma row, ‖series (1 : DirichletCharacter ℂ 1) b.2 2‖^2
    rw [sum_sigma]
    calc
      K * mass < mass * (∑ p ∈ P, 1 / ((p : ℝ) - 2)) := by
        simpa only [mul_comm mass] using mul_lt_mul_of_pos_right hlarge hm
      _ = _ := by
        rw [mul_sum]
        exact sum_congr rfl fun p hp => (row_spec p hp).2.symm
