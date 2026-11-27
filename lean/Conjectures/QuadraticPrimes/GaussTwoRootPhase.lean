import Mathlib

namespace Conjectures.QuadraticPrimes.GaussTwoRootPhase_aux

private theorem sum_two_roots (p : ℕ) [Fact (Nat.Prime p)]
    (r k : ZMod p) (hr : r ^ 2 + 1 = 0) (hneq : r ≠ -r) :
    (∑ v : ZMod p, if v ^ 2 + 1 = 0 then ZMod.stdAddChar (k * v) else 0) =
      ZMod.stdAddChar (k * r) + ZMod.stdAddChar (-k * r) := by
  classical
  have hroots (v : ZMod p) : v ^ 2 + 1 = 0 ↔ v = r ∨ v = -r := by
    constructor
    · intro hv
      have hsq : v ^ 2 = r ^ 2 := by linear_combination hv - hr
      have hprod : (v - r) * (v + r) = 0 := by
        calc
          (v - r) * (v + r) = v ^ 2 - r ^ 2 := by ring
          _ = 0 := sub_eq_zero.mpr hsq
      rcases mul_eq_zero.mp hprod with hleft | hright
      · exact Or.inl (sub_eq_zero.mp hleft)
      · exact Or.inr (eq_neg_iff_add_eq_zero.mpr hright)
    · rintro (rfl | rfl)
      · exact hr
      · simpa only [even_two, Even.neg_pow] using hr
  have hfilter : Finset.univ.filter (fun v : ZMod p => v ^ 2 + 1 = 0) = {r, -r} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact hroots v
  rw [← Finset.sum_filter]
  rw [hfilter]
  simp [hneq, mul_neg, neg_mul]

end Conjectures.QuadraticPrimes.GaussTwoRootPhase_aux

theorem Conjectures.QuadraticPrimes.GaussTwoRootPhase :
    ∀ (p : ℕ) [Fact (Nat.Prime p)] (a b : ℕ), 2 < p → 0 < a → a ≤ b → p = a ^ 2 + b ^ 2 →
      let r : ZMod p := (a : ZMod p) / (b : ZMod p)
      ∀ k : ZMod p, (∑ v : ZMod p, if v ^ 2 + 1 = 0 then ZMod.stdAddChar (k * v) else 0) =
        ZMod.stdAddChar (k * r) + ZMod.stdAddChar (-k * r) := by
  intro p _ a b hp2 ha hab hp
  dsimp
  intro k
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  have ha_lt : a < p := by nlinarith [sq_nonneg (a : ℤ), sq_nonneg (b : ℤ)]
  have hb_lt : b < p := by nlinarith
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt ha ha_lt) ((ZMod.natCast_eq_zero_iff a p).mp h)
  have hb0 : (b : ZMod p) ≠ 0 := by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt hbpos hb_lt) ((ZMod.natCast_eq_zero_iff b p).mp h)
  have hcast : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = 0 := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) hp
    simpa only [Nat.cast_add, Nat.cast_pow, ZMod.natCast_self] using h.symm
  let r : ZMod p := (a : ZMod p) / (b : ZMod p)
  have hr0 : r ≠ 0 := div_ne_zero ha0 hb0
  have hr : r ^ 2 + 1 = 0 := by
    dsimp [r]
    apply (mul_eq_zero_iff_right hb0).mp
    field_simp
    linear_combination hcast
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt (by omega : 0 < 2) hp2)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  have hneq : r ≠ -r := by
    intro h
    have hsum : r + r = 0 := by
      have : r - -r = 0 := sub_eq_zero.mpr h
      simpa only [sub_neg_eq_add] using this
    have hmul : (2 : ZMod p) * r = 0 := by simpa only [two_mul] using hsum
    rcases mul_eq_zero.mp hmul with hzero | hzero
    · exact htwo hzero
    · exact hr0 hzero
  exact Conjectures.QuadraticPrimes.GaussTwoRootPhase_aux.sum_two_roots p r k hr hneq
