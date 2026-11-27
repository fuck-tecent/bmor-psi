import Mathlib

namespace Conjectures.Goldbach.FareyReturnDigitLine_aux

/-- The central denominator line splits the doubled numerator: the numerator `2*n-1` of the
return digit is the numerator `n-1+u` of the first return digit plus the denominator `n-u`. -/
lemma numerator_split (n u : ℕ) (hu : 1 ≤ u) (hun : u < n) :
    2 * n - 1 = (n - 1 + u) + (n - u) := by
  omega

/-- Dividing the split numerator by the positive denominator `n-u` adds exactly one quotient. -/
lemma quotient_split (n u : ℕ) (hu : 1 ≤ u) (hun : u < n) :
    (2 * n - 1) / (n - u) = (n - 1 + u) / (n - u) + 1 := by
  have hpos : 0 < n - u := Nat.sub_pos_of_lt hun
  rw [numerator_split n u hu hun, Nat.add_div_right _ hpos]

end Conjectures.Goldbach.FareyReturnDigitLine_aux

/-- New route · H01 · Rewrite the first return digit as a quotient on the central denominator
line: for `1 ≤ u < n` the digit `(n-1+u)/(n-u)` is the quotient `(2*n-1)/(n-u)` minus one. -/
theorem Conjectures.Goldbach.FareyReturnDigitLine :
  ∀ n u : ℕ, 1≤u → u<n → (n-1+u)/(n-u) = (2*n-1)/(n-u)-1 := by
  intro n u hu hun
  rw [Conjectures.Goldbach.FareyReturnDigitLine_aux.quotient_split n u hu hun,
    Nat.add_sub_cancel]
