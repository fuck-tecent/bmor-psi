import Mathlib

namespace PEqualNP.Outside

theorem L_no_three_in_line_cert_23_4 :
(
∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+46<n ∧ z.2+8<n)).card=(n-46)*(n-8)
) := by
  intro n
  have heq : (((Finset.range n).product (Finset.range n)).filter (fun z => z.1 + 46 < n ∧ z.2 + 8 < n)) =
      (Finset.range (n - 46)).product (Finset.range (n - 8)) := by
    ext ⟨a, b⟩
    simp
    omega
  rw [heq]
  simp

end PEqualNP.Outside
