import Mathlib

namespace Conjectures.Goldbach.BeaumontPrimitiveCycle_aux

private theorem surj_of_prime {m : ℕ} (hm : Nat.Prime m) (a : ZMod m) (ha : a ≠ 0) :
    Function.Surjective (fun k : ZMod m => a * k) := by
  haveI : Fact (Nat.Prime m) := ⟨hm⟩
  intro y
  refine ⟨a⁻¹ * y, ?_⟩
  show a * (a⁻¹ * y) = y
  rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]

private theorem prime_of_surj {m : ℕ} (hm : 2 ≤ m)
    (H : ∀ a : ZMod m, a ≠ 0 → Function.Surjective (fun k : ZMod m => a * k)) :
    Nat.Prime m := by
  by_contra hnp
  obtain ⟨d, hd, hd2, hdlt⟩ := (Nat.not_prime_iff_exists_dvd_lt hm).mp hnp
  have hdz : (d : ZMod m) ≠ 0 := by
    intro hz
    have hmd : m ∣ d := (ZMod.natCast_eq_zero_iff d m).mp hz
    have hle : m ≤ d := Nat.le_of_dvd (by omega) hmd
    omega
  obtain ⟨k, hk⟩ := H (d : ZMod m) hdz 1
  have hu : IsUnit ((d : ZMod m)) := IsUnit.of_mul_eq_one k hk
  have hcop : Nat.Coprime d m := (ZMod.isUnit_iff_coprime d m).mp hu
  have hdone : d = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hd
  omega

end Conjectures.Goldbach.BeaumontPrimitiveCycle_aux

theorem Conjectures.Goldbach.BeaumontPrimitiveCycle : ∀ m : ℕ, 2 ≤ m → (Nat.Prime m ↔ ∀ a : ZMod m, a ≠ 0 → Function.Surjective (fun k : ZMod m => a*k)) := by
  intro m hm
  constructor
  · intro hp a ha
    exact Conjectures.Goldbach.BeaumontPrimitiveCycle_aux.surj_of_prime hp a ha
  · intro H
    exact Conjectures.Goldbach.BeaumontPrimitiveCycle_aux.prime_of_surj hm H
