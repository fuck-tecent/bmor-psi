import Mathlib

/-- Initial points `x < n` with `x + k < n` are exactly the first `n - k` naturals. -/
private lemma filter_range_add_lt (n k : ℕ) :
    (Finset.range n).filter (fun x => x + k < n) = Finset.range (n - k) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hx⟩
    omega
  · intro hx
    refine ⟨?_, ?_⟩ <;> omega

/-- The starting conditions for this stride split into two independent coordinate ranges. -/
private lemma grid_filter (n : ℕ) :
    ((Finset.range n).product (Finset.range n)).filter (fun z => z.1 + 60 < n ∧ z.2 + 2 < n)
      = (Finset.range n).filter (fun x => x + 60 < n) ×ˢ
          (Finset.range n).filter (fun x => x + 2 < n) := by
  simpa using Finset.filter_product (s := Finset.range n) (t := Finset.range n)
    (fun x : ℕ => x + 60 < n) (fun x : ℕ => x + 2 < n)

theorem PEqualNP.Outside.L_no_three_in_line_cert_30_1 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+60<n ∧ z.2+2<n)).card=(n-60)*(n-2) := by
  intro n
  rw [grid_filter, Finset.card_product, filter_range_add_lt, filter_range_add_lt,
    Finset.card_range, Finset.card_range]
