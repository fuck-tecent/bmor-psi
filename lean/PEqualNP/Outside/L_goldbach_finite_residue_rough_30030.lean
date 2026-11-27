import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

private def candidates : List ℕ := [3,5,7,11,31,43,61,79,149,197]

private def passes (t : ℕ) : Bool :=
  candidates.any fun p => ((2*t+30030-p)%30030).gcd 30030 == 1

-- Check consecutive half-residues in two equal blocks at each step.
private def block (start : ℕ) : ℕ → Bool
  | 0 => passes start
  | d+1 => block start d && block (start + 2^d) d

private theorem inside {d start t : ℕ} (h : block start d = true)
    (hl : start ≤ t) (hu : t < start + 2^d) : passes t = true := by
  induction d generalizing start with
  | zero =>
    have : t = start := by simpa using (show t = start by simp at hu; omega)
    simpa [this, block] using h
  | succ d ih =>
    simp only [block, Bool.and_eq_true] at h
    rw [pow_succ] at hu
    by_cases ht : t < start + 2^d
    · exact ih h.1 hl ht
    · exact ih h.2 (by omega) (by omega)

set_option maxHeartbeats 4000000 in
private theorem coverage : block 0 14 = true := by decide +kernel

theorem PEqualNP.Outside.L_goldbach_finite_residue_rough_30030 :
    ∀ a : ℕ, a < 30030 → Even a → ∃ p ∈ ({3,5,7,11,31,43,61,79,149,197} : Finset ℕ), Nat.Coprime ((a+30030-p)%30030) 30030 := by
  intro a ha he
  obtain ⟨t, rfl⟩ := he
  have ht : t < 0 + 2^14 := by norm_num; omega
  have hc := (List.any_eq_true.mp (inside coverage (Nat.zero_le _) ht))
  obtain ⟨p, hp, hg⟩ := hc
  refine ⟨p, ?_, ?_⟩
  · simpa [candidates] using hp
  · simpa [Nat.Coprime, two_mul] using hg
