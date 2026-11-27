import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Nat.Even

namespace GoldbachWheelUnitBase

private def residues : List ℕ := [17,19,23,181,29,37,41,43,31,47,53,67]

private def good (k : ℕ) : Bool :=
  residues.any (fun r => Nat.gcd r 30030 == 1 && Nat.gcd ((2*k+30030-r)%30030) 30030 == 1)

/-- Check the consecutive block of half-residues beginning at `start`. -/
private def block : ℕ → ℕ → Bool
  | 0, start => good start
  | d+1, start => block d start && block d (start + 2^d)

private theorem block_sound (d start : ℕ) (ok : block d start = true) :
    ∀ j < 2^d, good (start+j) = true := by
  induction d generalizing start with
  | zero =>
    intro j hj
    have : j = 0 := by simpa using hj
    simpa [this, block] using ok
  | succ d ih =>
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp ok
    intro j hj
    by_cases hjl : j < 2^d
    · exact ih start hl j hjl
    · have hlen : j - 2^d < 2^d := by rw [pow_succ] at hj; omega
      have hsum : start + 2^d + (j - 2^d) = start+j := by omega
      simpa [hsum] using ih (start + 2^d) hr (j - 2^d) hlen

private theorem checked : block 14 0 = true := by decide +kernel

end GoldbachWheelUnitBase

open GoldbachWheelUnitBase

theorem PEqualNP.Outside.L_goldbach_finite_wheel_unit_base :
    ∀ a : ℕ, a < 30030 → Even a → ∃ r ∈ ({17,19,23,181,29,37,41,43,31,47,53,67} : Finset ℕ), Nat.Coprime r 30030 ∧ Nat.Coprime ((a+30030-r)%30030) 30030 := by
  intro a ha he
  obtain ⟨k, hk⟩ := he
  have hbound : k < 2^14 := by change k < 16384; omega
  have hc := block_sound 14 0 checked k hbound
  simp only [Nat.zero_add] at hc
  unfold good at hc
  obtain ⟨r, hr, hp⟩ := List.any_eq_true.mp hc
  obtain ⟨hp₁, hp₂⟩ := Bool.and_eq_true_iff.mp hp
  refine ⟨r, ?_, eq_of_beq hp₁, ?_⟩
  · simpa [residues, List.mem_cons, Finset.mem_insert] using hr
  · have hh : a = 2*k := by omega
    simpa [hh, Nat.Coprime] using eq_of_beq hp₂
