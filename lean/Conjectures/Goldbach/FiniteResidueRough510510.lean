import Mathlib

private def candidates : List ℕ := [3,5,7,11,41,61,79,149,167,769,1747,2297,2311]

private def good (a : ℕ) : Bool :=
  candidates.any (fun p => Nat.gcd ((a + 510510 - p) % 510510) 510510 == 1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000000 in
private theorem blocks (b : ℕ) (hb : b < 255) :
    (List.range 1001).all (fun i => good (2002 * b + 2 * i)) = true := by
  interval_cases b <;> decide +kernel

private theorem block_sound {b i : ℕ}
    (h : (List.range 1001).all (fun j => good (2002 * b + 2 * j)) = true)
    (hi : i < 1001) : good (2002 * b + 2 * i) = true :=
  List.all_eq_true.mp h i (List.mem_range.mpr hi)

theorem Conjectures.Goldbach.FiniteResidueRough510510 :
    ∀ a : ℕ, a < 510510 → Even a → ∃ p ∈ ({3,5,7,11,41,61,79,149,167,769,1747,2297,2311} : Finset ℕ), Nat.Coprime ((a+510510-p)%510510) 510510 := by
  intro a ha he
  have haeven : a % 2 = 0 := by
    obtain ⟨k, hk⟩ := he
    omega
  let b := a / 2002
  let i := (a % 2002) / 2
  have hb : b < 255 := by
    dsimp [b]
    omega
  have hi : i < 1001 := by
    dsimp [i]
    omega
  have hrepr : a = 2002 * b + 2 * i := by
    dsimp [b, i]
    omega
  have hgood : good a = true := by
    rw [hrepr]
    exact block_sound (blocks b hb) hi
  obtain ⟨p, hp, hg⟩ := List.any_eq_true.mp hgood
  refine ⟨p, ?_, ?_⟩
  · simpa [candidates] using hp
  · simpa [Nat.Coprime] using eq_of_beq hg
