import Mathlib

open Finset

namespace Goldbach.DyadicPairs

/-- The sum determines its largest exponent, as it lies in (2^b,2^(b+1)]. -/
theorem ordered {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    (h : (2:ℕ)^a + 2^b = 2^c + 2^d) : a = c ∧ b = d := by
  have bound {i j k l : ℕ} (hij : i ≤ j) (hjk : j < k) :
      (2:ℕ)^i + 2^j < 2^l + 2^k := by
    have hi : (2:ℕ)^i ≤ 2^j := Nat.pow_le_pow_right (by decide) hij
    have hk : (2:ℕ)^(j+1) ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    have hl : 0 < (2:ℕ)^l := by positivity
    rw [pow_succ] at hk
    omega
  have he : b = d := by
    rcases lt_trichotomy b d with hb | hb | hb
    · exact False.elim ((ne_of_lt (bound (l:=c) hab hb)) h)
    · exact hb
    · exact False.elim ((ne_of_lt (bound (l:=a) hcd hb)) h.symm)
  subst d
  exact ⟨(Nat.pow_right_injective (by decide : 2 ≤ 2)) (Nat.add_right_cancel h), rfl⟩

theorem pair_eq {a b c d : ℕ} (h : (2:ℕ)^a + 2^b = 2^c + 2^d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  rcases le_total a b with hab | hba <;> rcases le_total c d with hcd | hdc
  · exact Or.inl (ordered hab hcd h)
  · exact Or.inr (ordered hab hdc (by simpa only [Nat.add_comm (2^d)] using h))
  · exact Or.inr ((ordered hba hcd (by simpa only [Nat.add_comm (2^b)] using h)).symm)
  · exact Or.inl ((ordered hba hdc (by simpa only [Nat.add_comm (2^b),Nat.add_comm (2^d)] using h)).symm)

theorem Conjecture (n L : ℕ) :
    ((Icc 1 L).filter (fun e => n = 2^e + 2^(Nat.log 2 (n-2^e)))).card ≤ 2 := by
  let s := (Icc 1 L).filter (fun e => n = 2^e + 2^(Nat.log 2 (n-2^e)))
  change s.card ≤ 2
  rcases s.eq_empty_or_nonempty with hs | ⟨a,ha⟩
  · simp [hs]
  · let b := Nat.log 2 (n-2^a)
    have h₀ : n = 2^a + 2^b := (mem_filter.mp ha).2
    have hsub : s ⊆ {a,b} := by
      intro e he
      have heq : (2:ℕ)^e + 2^(Nat.log 2 (n-2^e)) = 2^a + 2^b :=
        (mem_filter.mp he).2.symm.trans h₀
      rcases pair_eq heq with h | h <;> simp [h.1]
    exact (card_le_card hsub).trans (by simpa using (card_insert_le a {b}))

end Goldbach.DyadicPairs

theorem Conjectures.Goldbach.BinaryShiftMissedCenter :
    ∀ n L : ℕ, ((Finset.Icc 1 L).filter (fun e => n = 2^e + 2^(Nat.log 2 (n-2^e)))).card ≤ 2 := Goldbach.DyadicPairs.Conjecture
