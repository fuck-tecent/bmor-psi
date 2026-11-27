import Mathlib

namespace PEqualNP.Outside

/-- Separate complete periods from a segment of length `b`. -/
private theorem count_blocks (P : ℕ → Prop) [DecidablePred P] {q : ℕ}
    (hP : Function.Periodic P q) (a b : ℕ) :
    Nat.count P (b + a * q) = Nat.count P b + a * Nat.count P q := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, Nat.count_add']
    simp_rw [show ∀ k, P (k + q) = P k from hP]
    rw [ih, Nat.succ_mul, Nat.add_assoc]

/-- A bounded final segment contributes at most one period's root count in error. -/
theorem L_goldbach_sieve_residue_boundary :
    let r := fun n q : ℕ => ((Finset.range q).filter (fun k => q ∣ k*(k+n))).card; ∀ x n q : ℕ, 0<q → |((((Finset.range x).filter (fun k => q ∣ k*(k+n))).card : ℝ) - (x:ℝ)*(r n q:ℝ)/q)| ≤ (r n q:ℝ) := by
  intro r x n q hq
  let P := fun k : ℕ => q ∣ k * (k + n)
  have hP : Function.Periodic P q := by
    intro k
    have hk : k + q ≡ k [MOD q] := Nat.add_modulus_modEq_iff.mpr (Nat.ModEq.refl k)
    exact propext ((hk.mul (hk.add_right n)).dvd_iff (dvd_refl q))
  change |(((Finset.range x).filter P).card : ℝ) - (x : ℝ) *
    (((Finset.range q).filter P).card : ℝ) / q| ≤ (((Finset.range q).filter P).card : ℝ)
  simp only [← Nat.count_eq_card_filter_range]
  have hdiv : x % q + (x / q) * q = x := by
    simpa only [Nat.mul_comm q] using Nat.mod_add_div x q
  have hcount := count_blocks P hP (x / q) (x % q)
  rw [hdiv] at hcount
  have hcountR : (Nat.count P x : ℝ) = (Nat.count P (x % q) : ℝ) +
      (x / q : ℕ) * (Nat.count P q : ℝ) := by exact_mod_cast hcount
  have hxR : (x : ℝ) = ((x % q : ℕ) : ℝ) + (x / q : ℕ) * (q : ℝ) := by
    exact_mod_cast hdiv.symm
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrem : ((x % q : ℕ) : ℝ) ≤ q := by exact_mod_cast (Nat.mod_lt x hq).le
  have htail : (Nat.count P (x % q) : ℝ) ≤ Nat.count P q := by
    exact_mod_cast Nat.count_monotone P (Nat.mod_lt x hq).le
  have hfrac : ((x % q : ℕ) : ℝ) / q ≤ 1 := (div_le_one hqR).mpr hrem
  have hexpected : (x : ℝ) * (Nat.count P q : ℝ) / q =
      (x / q : ℕ) * (Nat.count P q : ℝ) + ((x % q : ℕ) : ℝ) / q * Nat.count P q := by
    conv_lhs => rw [hxR]
    field_simp
    ring
  have hlo : 0 ≤ ((x % q : ℕ) : ℝ) / q * Nat.count P q := by positivity
  have hhi := mul_le_mul_of_nonneg_right hfrac (by positivity : 0 ≤ (Nat.count P q : ℝ))
  rw [hcountR, hexpected, abs_le]
  constructor <;> linarith [show (0 : ℝ) ≤ Nat.count P (x % q) by positivity]

end PEqualNP.Outside
