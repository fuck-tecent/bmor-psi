import Mathlib

namespace PEqualNP.Outside

theorem L_no_three_in_line_cert_25_3 :
(
∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+50<n ∧ z.2+6<n)).card=(n-50)*(n-6)
) := by
  intro n
  have heq : (((Finset.range n).product (Finset.range n)).filter (fun z => z.1 + 50 < n ∧ z.2 + 6 < n)) =
      (Finset.range (n - 50)).product (Finset.range (n - 6)) := by
    ext ⟨a, b⟩
    simp
    omega
  rw [heq]
  simp

end PEqualNP.Outside
