import Mathlib

/-!
# L-goldbach-cut-291ed25a8d627cb4a9346bdd

Simultaneous nonvanishing of the reflected sieve forms.  Each form
`(18 * s + c) * (c2 * s + c3)` over `ZMod p` is a product of two affine maps with
nonvanishing leading coefficient (`18` or `6`, and `p ≥ 5` is prime), so it has at most
two roots.  Hence for the pair of forms at `s` and `t - s` at most four residues of
`ZMod p` are bad, and since `p ≥ 5` some residue avoids all of them.
-/

namespace Conjectures.Cuts.Task291ed25a8d627cb4a9346bdd_aux

/-- A linear form with nonvanishing leading coefficient has a single root. -/
lemma root_of_linear {p : ℕ} [Fact p.Prime] {c d s : ZMod p} (hc : c ≠ 0)
    (h : c * s + d = 0) : s = c⁻¹ * (-d) := by
  have h1 : c * s = -d := by linear_combination h
  calc s = c⁻¹ * (c * s) := by rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    _ = c⁻¹ * (-d) := by rw [h1]

/-- A set given by four elements has at most four members. -/
lemma card_insert4 {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α).card ≤ 4 := by
  have h1 := Finset.card_insert_le a ({b, c, d} : Finset α)
  have h2 := Finset.card_insert_le b ({c, d} : Finset α)
  have h3 := Finset.card_insert_le c ({d} : Finset α)
  have h4 : ({d} : Finset α).card = 1 := Finset.card_singleton d
  omega

/-- A prime at least five divides neither six nor eighteen. -/
lemma prime_not_dvd {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {n : ℕ} (hn : n = 6 ∨ n = 18) :
    ¬ p ∣ n := by
  rcases hn with rfl | rfl
  · intro hd
    rw [show (6 : ℕ) = 2 * 3 by norm_num] at hd
    rcases hp.dvd_mul.mp hd with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) h2; omega
    · have := Nat.le_of_dvd (by norm_num) h3; omega
  · intro hd
    rw [show (18 : ℕ) = 2 * 9 by norm_num] at hd
    rcases hp.dvd_mul.mp hd with h2 | h9
    · have := Nat.le_of_dvd (by norm_num) h2; omega
    · rw [show (9 : ℕ) = 3 * 3 by norm_num] at h9
      rcases hp.dvd_mul.mp h9 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) h3; omega
      · have := Nat.le_of_dvd (by norm_num) h3; omega

end Conjectures.Cuts.Task291ed25a8d627cb4a9346bdd_aux

theorem Conjectures.Cuts.Task291ed25a8d627cb4a9346bdd :
    have x1 : Finset ℕ := {(1 : ℕ), (5 : ℕ), (11 : ℕ), (13 : ℕ), (17 : ℕ)}; have x2 : ℕ → ℕ := fun (x2 : ℕ) => if x2 % (3 : ℕ) = (1 : ℕ) then (6 : ℕ) else (18 : ℕ); have x3 : ℕ → ℕ := fun (x3 : ℕ) => if x3 % (3 : ℕ) = (1 : ℕ) then (x3 + (2 : ℕ)) / (3 : ℕ) else x3 + (2 : ℕ); have x4 : (x4 : ℕ) → ℕ → ZMod x4 → ZMod x4 := fun (x4 x5 : ℕ) (x6 : ZMod x4) => ((18 : ZMod x4) * x6 + ↑x5) * (↑(x2 x5) * x6 + ↑(x3 x5)); ∀ x5 ∈ x1, ∀ x7 ∈ x1, ∀ (x9 : ℕ), Nat.Prime x9 → (5 : ℕ) ≤ x9 → ∀ (x12 : ZMod x9), ∃ (x13 : ZMod x9), x4 x9 x5 x13 * x4 x9 x7 (x12 - x13) ≠ (0 : ZMod x9) := by
  intro x1 x2 x3 x4 x5 _ x7 _ x9 hp h5 x12
  have : Fact (Nat.Prime x9) := ⟨hp⟩
  have : NeZero x9 := ⟨hp.ne_zero⟩
  have h18 : (18 : ZMod x9) ≠ 0 := by
    intro h
    exact Conjectures.Cuts.Task291ed25a8d627cb4a9346bdd_aux.prime_not_dvd hp h5 (Or.inr rfl)
      ((ZMod.natCast_eq_zero_iff 18 x9).mp h)
  have h6 : (6 : ZMod x9) ≠ 0 := by
    intro h
    exact Conjectures.Cuts.Task291ed25a8d627cb4a9346bdd_aux.prime_not_dvd hp h5 (Or.inl rfl)
      ((ZMod.natCast_eq_zero_iff 6 x9).mp h)
  have hx2 : ∀ n : ℕ, (x2 n : ZMod x9) ≠ 0 := by
    intro n
    dsimp only [x2]
    split_ifs
    · exact h6
    · exact h18
  -- the four forbidden residues
  set r1 : ZMod x9 := (18 : ZMod x9)⁻¹ * (-(x5 : ZMod x9))
  set r2 : ZMod x9 := (x2 x5 : ZMod x9)⁻¹ * (-(x3 x5 : ZMod x9))
  set s1 : ZMod x9 := (18 : ZMod x9)⁻¹ * (-(x7 : ZMod x9))
  set s2 : ZMod x9 := (x2 x7 : ZMod x9)⁻¹ * (-(x3 x7 : ZMod x9))
  set B : Finset (ZMod x9) := {r1, r2, x12 - s1, x12 - s2}
  have hBcard : B.card ≤ 4 := by
    have h := Conjectures.Cuts.Task291ed25a8d627cb4a9346bdd_aux.card_insert4 r1 r2 (x12 - s1) (x12 - s2)
    exact h
  have hex : ∃ s : ZMod x9, s ∉ B := by
    by_contra h
    push_neg at h
    have hsub : (Finset.univ : Finset (ZMod x9)) ⊆ B := fun s _ => h s
    have hc := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card] at hc
    omega
  obtain ⟨s, hs⟩ := hex
  have hr1 : r1 ∈ B := by simp [B]
  have hr2 : r2 ∈ B := by simp [B]
  have hs1 : x12 - s1 ∈ B := by simp [B]
  have hs2 : x12 - s2 ∈ B := by simp [B]
  refine ⟨s, ?_⟩
  have hfirst : x4 x9 x5 s ≠ 0 := by
    dsimp only [x4]
    refine mul_ne_zero ?_ ?_
    · intro h
      have hr : s = r1 := Conjectures.Cuts.Task291ed25a8d627cb4a9346bdd_aux.root_of_linear h18 h
      exact hs (hr ▸ hr1)
    · intro h
      have hr : s = r2 := Conjectures.Cuts.Task291ed25a8d627cb4a9346bdd_aux.root_of_linear (hx2 x5) h
      exact hs (hr ▸ hr2)
  have hsecond : x4 x9 x7 (x12 - s) ≠ 0 := by
    dsimp only [x4]
    refine mul_ne_zero ?_ ?_
    · intro h
      have hr : x12 - s = s1 := Conjectures.Cuts.Task291ed25a8d627cb4a9346bdd_aux.root_of_linear h18 h
      have hr' : s = x12 - s1 := by rw [← hr]; ring
      exact hs (hr' ▸ hs1)
    · intro h
      have hr : x12 - s = s2 := Conjectures.Cuts.Task291ed25a8d627cb4a9346bdd_aux.root_of_linear (hx2 x7) h
      have hr' : s = x12 - s2 := by rw [← hr]; ring
      exact hs (hr' ▸ hs2)
  exact mul_ne_zero hfirst hsecond
