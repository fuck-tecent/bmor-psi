import Mathlib

namespace PEqualNP.Outside

/-- Combine two normalized lift errors with an arithmetic matching error: if `(P - Q)/A`
is within `E` of `4*C`, `P/A` within `e` of `M`, and `Q/A` within `f` of `N`, then
`(M - N - E - e - f)/4 ≤ C`. -/
theorem L_twin_primes_theta_error_budget :
    ∀ (A P M Q N C E e f : ℝ), 0 < A → |(P-Q)/A-4*C| ≤ E → |P/A-M| ≤ e →
      |Q/A-N| ≤ f → (M-N-E-e-f)/4 ≤ C := by
  intro A P M Q N C E e f hA h1 h2 h3
  have h1' : (P-Q)/A - 4*C ≤ E := (abs_le.mp h1).2
  have h2' : M - e ≤ P/A := by
    have := (abs_le.mp h2).1
    linarith
  have h3' : Q/A ≤ N + f := by
    have := (abs_le.mp h3).2
    linarith
  have hsplit : (P-Q)/A = P/A - Q/A := by ring
  linarith [h1', h2', h3', hsplit]

end PEqualNP.Outside
