import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_cert_877 :
    ∀ n : ℕ, 877 ∣ n ^ 2 + 1 ↔ n % 877 = 151 ∨ n % 877 = 726 := by
  intro n
  letI : Fact (Nat.Prime 877) := ⟨by norm_num⟩
  have ha : ((n : ZMod 877) = 151) ↔ n % 877 = 151 :=
    ZMod.natCast_eq_natCast_iff' n 151 877
  have hb : ((n : ZMod 877) = 726) ↔ n % 877 = 726 :=
    ZMod.natCast_eq_natCast_iff' n 726 877
  let roots := (Polynomial.nthRoots 2 (-1 : ZMod 877)).toFinset
  have hmem (z : ZMod 877) : z ∈ roots ↔ z ^ 2 = -1 := by
    change z ∈ (Polynomial.nthRoots 2 (-1 : ZMod 877)).toFinset ↔ _
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by decide : 0 < 2)]
  have hbound : roots.card ≤ 2 :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 2 (-1 : ZMod 877))
  have hab : (151 : ZMod 877) ≠ 726 := by decide
  have hsub : ({151, 726} : Finset (ZMod 877)) ⊆ roots := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> apply (hmem _).2 <;> decide
  have hexhaust : ({151, 726} : Finset (ZMod 877)) = roots :=
    Finset.eq_of_subset_of_card_le hsub (by simpa only [Finset.card_pair hab] using hbound)
  have hfield (z : ZMod 877) : z ^ 2 + 1 = 0 ↔ z = 151 ∨ z = 726 := calc
    z ^ 2 + 1 = 0 ↔ z ^ 2 = -1 := eq_neg_iff_add_eq_zero.symm
    _ ↔ z ∈ roots := (hmem z).symm
    _ ↔ z ∈ ({151, 726} : Finset (ZMod 877)) := by rw [hexhaust]
    _ ↔ z = 151 ∨ z = 726 := by simp only [Finset.mem_insert, Finset.mem_singleton]
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one, hfield, ha, hb]
