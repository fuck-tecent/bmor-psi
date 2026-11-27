import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card

theorem PEqualNP.Outside.L_goldbach_unit_parity :
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q); ∀ n, (U 2 n).card = if Even n then 1 else 0 := by
  dsimp only
  intro n
  have admissible (a : ℕ) :
      (a < 2 ∧ Nat.Coprime a 2 ∧ Nat.Coprime (n + 2 - a) 2) ↔
        a = 1 ∧ Even n := by
    simp only [Nat.coprime_two_right, Nat.odd_iff, Nat.even_iff]
    omega
  let residues := (Finset.range 2).filter (fun a => Nat.Coprime a 2 ∧ Nat.Coprime (n + 2 - a) 2)
  change residues.card = _
  have mem_residues (a : ℕ) : a ∈ residues ↔ a = 1 ∧ Even n := by
    simpa only [residues, Finset.mem_filter, Finset.mem_range] using admissible a
  by_cases hn : Even n
  · have h : residues = {1} := by ext a; simp [mem_residues, hn]
    simp [h, hn]
  · have h : residues = ∅ := by ext a; simp [mem_residues, hn]
    simp [h, hn]
