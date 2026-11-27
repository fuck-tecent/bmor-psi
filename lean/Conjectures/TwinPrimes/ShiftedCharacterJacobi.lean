import Mathlib

theorem Conjectures.TwinPrimes.ShiftedCharacterJacobi : ∀ (p : ℕ) [Fact p.Prime], 2 < p → ∀ (χ ψ : DirichletCharacter ℂ p), (∑ x : ZMod p, χ x * ψ (x+2)) = χ (-2) * ψ 2 * (∑ y : ZMod p, χ y * ψ (1-y)) ∧ (χ ≠ 1 → (∑ x : ZMod p, χ x * (1 : DirichletCharacter ℂ p) (x+2)) = -χ (-2)) := by
  intro p _ hp χ ψ
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by simpa using h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h1
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    omega
  have hu : IsUnit (-2 : ZMod p) := (isUnit_iff_ne_zero.mpr (by simpa using h2)).neg
  obtain ⟨u, huval⟩ := hu
  constructor
  · have hsum := (Units.mulLeft_bijective u).sum_comp (fun x : ZMod p => χ x * ψ (x + 2))
    have hkey : ∀ y : ZMod p, χ ((u : ZMod p) * y) * ψ ((u : ZMod p) * y + 2)
        = χ (-2) * ψ 2 * (χ y * ψ (1 - y)) := by
      intro y
      rw [huval, map_mul χ]
      have harg : (-2 : ZMod p) * y + 2 = 2 * (1 - y) := by ring
      rw [harg, map_mul ψ]
      ring
    calc (∑ x : ZMod p, χ x * ψ (x + 2))
        = ∑ y : ZMod p, χ ((u : ZMod p) * y) * ψ ((u : ZMod p) * y + 2) := hsum.symm
      _ = ∑ y : ZMod p, χ (-2) * ψ 2 * (χ y * ψ (1 - y)) :=
          Finset.sum_congr rfl (fun y _ => hkey y)
      _ = χ (-2) * ψ 2 * ∑ y : ZMod p, χ y * ψ (1 - y) := by rw [Finset.mul_sum]
  · intro hχ
    have hsum0 : ∑ x : ZMod p, χ x = 0 := MulChar.sum_eq_zero_of_ne_one hχ
    have hone : ∀ x : ZMod p, x ≠ -2 → (1 : DirichletCharacter ℂ p) (x + 2) = 1 := by
      intro x hx
      refine MulChar.one_apply (isUnit_iff_ne_zero.mpr ?_)
      intro h
      exact hx (add_eq_zero_iff_eq_neg.mp h)
    have hzero : (1 : DirichletCharacter ℂ p) ((-2 : ZMod p) + 2) = 0 := by
      rw [show (-2 : ZMod p) + 2 = 0 by ring, MulChar.map_zero]
    have herase : ∀ x ∈ (Finset.univ : Finset (ZMod p)).erase (-2),
        χ x * (1 : DirichletCharacter ℂ p) (x + 2) = χ x := by
      intro x hx
      rw [hone x (Finset.mem_erase.mp hx).1, mul_one]
    have hsplit : (∑ x : ZMod p, χ x * (1 : DirichletCharacter ℂ p) (x + 2))
        = (∑ x ∈ (Finset.univ : Finset (ZMod p)).erase (-2),
            χ x * (1 : DirichletCharacter ℂ p) (x + 2))
          + χ (-2) * (1 : DirichletCharacter ℂ p) ((-2 : ZMod p) + 2) :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ (-2))).symm
    have hfinal : (∑ x ∈ (Finset.univ : Finset (ZMod p)).erase (-2), χ x) + χ (-2)
        = ∑ x : ZMod p, χ x := Finset.sum_erase_add _ _ (Finset.mem_univ (-2))
    calc (∑ x : ZMod p, χ x * (1 : DirichletCharacter ℂ p) (x + 2))
        = (∑ x ∈ (Finset.univ : Finset (ZMod p)).erase (-2), χ x)
          + χ (-2) * (1 : DirichletCharacter ℂ p) ((-2 : ZMod p) + 2) := by
            rw [hsplit, Finset.sum_congr rfl herase]
      _ = (∑ x ∈ (Finset.univ : Finset (ZMod p)).erase (-2), χ x) := by
            rw [hzero, mul_zero, add_zero]
      _ = -χ (-2) := eq_neg_of_add_eq_zero_left (by rw [hfinal, hsum0])
