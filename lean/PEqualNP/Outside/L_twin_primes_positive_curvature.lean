import Mathlib

namespace PEqualNP.Outside

/-- The second difference of the diagonal kernel `1/(u+c) + 1/(u-c) - 2/u` equals
`2*c^2/(u*(u^2-c^2))` and is strictly positive for `0 < c < u`. -/
theorem L_twin_primes_positive_curvature :
    ∀ u c : ℝ, 0 < c → c < u →
      1/(u+c)+1/(u-c)-2/u = 2*c^2/(u*(u^2-c^2)) ∧ 0 < 1/(u+c)+1/(u-c)-2/u := by
  intro u c hc hcu
  have hu : 0 < u := lt_trans hc hcu
  have h1 : 0 < u + c := by linarith
  have h2 : 0 < u - c := by linarith
  have h3 : 0 < u^2 - c^2 := by nlinarith
  have hden : 0 < u * (u^2 - c^2) := mul_pos hu h3
  have huc : u + c ≠ 0 := ne_of_gt h1
  have huc' : u - c ≠ 0 := ne_of_gt h2
  have hu' : u ≠ 0 := ne_of_gt hu
  have hden' : u * (u^2 - c^2) ≠ 0 := ne_of_gt hden
  constructor
  · field_simp
    ring
  · rw [show 1/(u+c)+1/(u-c)-2/u = 2*c^2/(u*(u^2-c^2)) from by
      field_simp
      ring]
    exact div_pos (by positivity) hden

end PEqualNP.Outside
