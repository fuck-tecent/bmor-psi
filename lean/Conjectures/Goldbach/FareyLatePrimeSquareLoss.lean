import Mathlib

/-!
# PREPUB goldbach gap: `L-goldbach-farey-late-prime-square-loss`

Elements of the middle Farey window whose product `u*(n-u)` has its least prime factor
larger than `√n` and which are of the form `p²` or `n-p²` are counted by at most
`2*√n` many integers: each admissible `u` is either a square `p²` or a complement
`n-p²` of a square, and there are at most `√n` choices for `p`.
-/

open scoped BigOperators
open Finset

/-- PREPUB frozen statement `L-goldbach-farey-late-prime-square-loss`. -/
theorem Conjectures.Goldbach.FareyLatePrimeSquareLoss :
    ∀ (n : ℕ) (J : Finset ℕ), 64 ≤ n → let I := Finset.Icc ((n+2)/3) ((2*n)/3); let Hit := I.filter (fun u => u.Coprime n ∧ (J.filter (fun a => (a*u)%n = 1)).Nonempty ∧ (∃ p : ℕ, p ≤ Nat.sqrt n ∧ p.Prime ∧ n < p^3 ∧ p ≤ (u*(n-u)).minFac ∧ (u=p^2 ∨ n-u=p^2))); Hit.card ≤ 2*Nat.sqrt n := by
  intro n J hn
  dsimp only
  have h64 : Nat.sqrt 64 = 8 := by
    have h := (Nat.eq_sqrt (a := 8) (n := 64)).mpr (by norm_num)
    exact h.symm
  have h8 : 8 ≤ Nat.sqrt n := by
    rw [← h64]
    exact Nat.sqrt_le_sqrt (by omega)
  have h2 : 2 ≤ Nat.sqrt n := by omega
  have hsq : (Nat.sqrt n) ^ 2 ≤ n := Nat.sqrt_le' n
  -- every admissible `u` is a square or a complement of a square
  have hsub : (Finset.Icc ((n+2)/3) ((2*n)/3)).filter
        (fun u => u.Coprime n ∧ (J.filter (fun a => (a*u)%n = 1)).Nonempty ∧
          (∃ p : ℕ, p ≤ Nat.sqrt n ∧ p.Prime ∧ n < p^3 ∧
            p ≤ (u*(n-u)).minFac ∧ (u=p^2 ∨ n-u=p^2)))
      ⊆ (Finset.Icc 2 (Nat.sqrt n)).image (fun p => p ^ 2)
        ∪ (Finset.Icc 2 (Nat.sqrt n)).image (fun p => n - p ^ 2) := by
    intro u hu
    obtain ⟨huI, huP⟩ := Finset.mem_filter.mp hu
    obtain ⟨-, -, p, hp_le, hpprime, -, -, hpcase⟩ := huP
    have hpI : p ∈ Finset.Icc 2 (Nat.sqrt n) :=
      Finset.mem_Icc.mpr ⟨hpprime.two_le, hp_le⟩
    have hpsq : p ^ 2 ≤ n := by
      have h1 : p ^ 2 ≤ (Nat.sqrt n) ^ 2 := Nat.pow_le_pow_left hp_le 2
      omega
    rcases hpcase with h | h
    · rw [Finset.mem_union]
      exact Or.inl (Finset.mem_image.mpr ⟨p, hpI, h.symm⟩)
    · rw [Finset.mem_union]
      refine Or.inr (Finset.mem_image.mpr ⟨p, hpI, ?_⟩)
      have hu_le : u ≤ n := by
        have h2 : u ≤ 2 * n / 3 := (Finset.mem_Icc.mp huI).2
        omega
      have hn_eq : n = p ^ 2 + u := (Nat.sub_eq_iff_eq_add hu_le).mp h
      rw [hn_eq]
      omega
  have hcardA : ((Finset.Icc 2 (Nat.sqrt n)).image (fun p => p ^ 2)).card
      ≤ Nat.sqrt n := by
    calc ((Finset.Icc 2 (Nat.sqrt n)).image (fun p => p ^ 2)).card
        ≤ (Finset.Icc 2 (Nat.sqrt n)).card := Finset.card_image_le
      _ = Nat.sqrt n + 1 - 2 := by simp
      _ ≤ Nat.sqrt n := by omega
  have hcardB : ((Finset.Icc 2 (Nat.sqrt n)).image (fun p => n - p ^ 2)).card
      ≤ Nat.sqrt n := by
    calc ((Finset.Icc 2 (Nat.sqrt n)).image (fun p => n - p ^ 2)).card
        ≤ (Finset.Icc 2 (Nat.sqrt n)).card := Finset.card_image_le
      _ = Nat.sqrt n + 1 - 2 := by simp
      _ ≤ Nat.sqrt n := by omega
  calc ((Finset.Icc ((n+2)/3) ((2*n)/3)).filter
        (fun u => u.Coprime n ∧ (J.filter (fun a => (a*u)%n = 1)).Nonempty ∧
          (∃ p : ℕ, p ≤ Nat.sqrt n ∧ p.Prime ∧ n < p^3 ∧
            p ≤ (u*(n-u)).minFac ∧ (u=p^2 ∨ n-u=p^2)))).card
      ≤ ((Finset.Icc 2 (Nat.sqrt n)).image (fun p => p ^ 2)
          ∪ (Finset.Icc 2 (Nat.sqrt n)).image (fun p => n - p ^ 2)).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.Icc 2 (Nat.sqrt n)).image (fun p => p ^ 2)).card
          + ((Finset.Icc 2 (Nat.sqrt n)).image (fun p => n - p ^ 2)).card :=
        Finset.card_union_le _ _
    _ ≤ Nat.sqrt n + Nat.sqrt n := Nat.add_le_add hcardA hcardB
    _ = 2 * Nat.sqrt n := by omega
