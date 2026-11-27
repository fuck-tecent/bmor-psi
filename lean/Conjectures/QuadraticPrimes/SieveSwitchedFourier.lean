import Mathlib

open scoped BigOperators

namespace Conjectures.QuadraticPrimes.SieveSwitchedFourier_aux

noncomputable section

lemma cast_div_mul_eq {d p m : ℕ} [NeZero d] (h : p ∣ m) :
    (p : ZMod d) * (m / p : ℕ) = (m : ZMod d) := by
  calc
    (p : ZMod d) * (m / p : ℕ) = ((p * (m / p) : ℕ) : ZMod d) := by
      norm_cast
    _ = (m : ZMod d) := by rw [Nat.mul_div_cancel' h]

def affine_equiv {d p r : ℕ} [NeZero d]
    (u : ZMod d) (hu : (p : ZMod d) * u = 1) :
    ZMod d ≃ ZMod d :=
  let e : ZMod d → ZMod d := fun t => (p : ZMod d) * t + (r : ZMod d)
  let einv : ZMod d → ZMod d := fun v => u * (v - (r : ZMod d))
  Equiv.ofBijective e (by
    have hu' : u * (p : ZMod d) = 1 := by simpa [mul_comm] using hu
    constructor
    · intro a b hab
      dsimp [e] at hab
      have hab' := congrArg (fun x : ZMod d => u * (x - (r : ZMod d))) hab
      have ha : u * ((p : ZMod d) * a + (r : ZMod d) - (r : ZMod d)) = a := by
        rw [add_sub_cancel_right]
        calc
          u * ((p : ZMod d) * a) = (u * (p : ZMod d)) * a := by ring
          _ = a := by rw [hu']; simp
      have hb : u * ((p : ZMod d) * b + (r : ZMod d) - (r : ZMod d)) = b := by
        rw [add_sub_cancel_right]
        calc
          u * ((p : ZMod d) * b) = (u * (p : ZMod d)) * b := by ring
          _ = b := by rw [hu']; simp
      calc
        a = u * ((p : ZMod d) * a + (r : ZMod d) - (r : ZMod d)) := ha.symm
        _ = u * ((p : ZMod d) * b + (r : ZMod d) - (r : ZMod d)) := hab'
        _ = b := hb
    · intro v
      refine ⟨einv v, ?_⟩
      dsimp [e, einv]
      calc
        (p : ZMod d) * (u * (v - (r : ZMod d))) + (r : ZMod d) =
            ((p : ZMod d) * u) * (v - (r : ZMod d)) + (r : ZMod d) := by ring
        _ = v := by rw [hu]; ring)

lemma coeff_mul_eq {d p r : ℕ} [NeZero d]
    (_u : ZMod d) (_hu : (p : ZMod d) * _u = 1) (hdiv : p ∣ (4 * r ^ 2 + 1))
    (t : ZMod d) :
    (p : ZMod d) *
        (4 * (p : ZMod d) * t ^ 2 + 8 * (r : ZMod d) * t +
          ((4 * r ^ 2 + 1) / p : ℕ)) =
      4 * ((p : ZMod d) * t + (r : ZMod d)) ^ 2 + 1 := by
  have hq := cast_div_mul_eq (d := d) hdiv
  push_cast at hq ⊢
  linear_combination hq

lemma coeff_eq_zero_iff {d p r : ℕ} [NeZero d]
    (u : ZMod d) (hu : (p : ZMod d) * u = 1) (hdiv : p ∣ (4 * r ^ 2 + 1))
    (t : ZMod d) :
    (4 * (p : ZMod d) * t ^ 2 + 8 * (r : ZMod d) * t +
          ((4 * r ^ 2 + 1) / p : ℕ)) = 0 ↔
      4 * ((p : ZMod d) * t + (r : ZMod d)) ^ 2 + 1 = 0 := by
  have hm := coeff_mul_eq (d := d) (p := p) (r := r) u hu hdiv t
  have hu' : u * (p : ZMod d) = 1 := by simpa [mul_comm] using hu
  constructor
  · intro h
    rw [← hm, h, mul_zero]
  · intro h
    calc
      (4 * (p : ZMod d) * t ^ 2 + 8 * (r : ZMod d) * t +
          ((4 * r ^ 2 + 1) / p : ℕ)) =
          (u * (p : ZMod d)) *
            (4 * (p : ZMod d) * t ^ 2 + 8 * (r : ZMod d) * t +
              ((4 * r ^ 2 + 1) / p : ℕ)) := by rw [hu']; simp
      _ = u * ((p : ZMod d) *
            (4 * (p : ZMod d) * t ^ 2 + 8 * (r : ZMod d) * t +
              ((4 * r ^ 2 + 1) / p : ℕ))) := by ring
      _ = 0 := by rw [hm, h, mul_zero]

lemma phase_eq {d p r : ℕ} [NeZero d]
    (u k : ZMod d) (hu : (p : ZMod d) * u = 1) (t : ZMod d) :
    k * t = -k * u * (r : ZMod d) + k * u * ((p : ZMod d) * t + (r : ZMod d)) := by
  have hu' : u * (p : ZMod d) = 1 := by simpa [mul_comm] using hu
  calc
    k * t = k * (u * (p : ZMod d) * t) := by rw [hu']; simp
    _ = -k * u * (r : ZMod d) + k * u * ((p : ZMod d) * t + (r : ZMod d)) := by ring

end
end Conjectures.QuadraticPrimes.SieveSwitchedFourier_aux

namespace Conjectures.QuadraticPrimes

noncomputable section

theorem SieveSwitchedFourier :
    let f := fun k : ℕ => 4*k^2+1; ∀ (d : ℕ) [NeZero d] (p r : ℕ) (u k : ZMod d), Nat.Coprime d p → (p : ZMod d)*u=1 → p ∣ f r →
  let coeff := fun t : ZMod d => 4*(p : ZMod d)*t^2 + 8*(r : ZMod d)*t + (f r / p : ℕ);
  (∑ t : ZMod d, if coeff t = 0 then ZMod.stdAddChar (k*t) else 0) =
    ZMod.stdAddChar (-k*u*(r : ZMod d)) *
       (∑ v : ZMod d, if 4*v^2+1 = 0 then ZMod.stdAddChar (k*u*v) else 0) := by
  dsimp
  intro d hd p r u k _hcop hu hdiv
  let e := Conjectures.QuadraticPrimes.SieveSwitchedFourier_aux.affine_equiv
    (d := d) (p := p) (r := r) u hu
  have hcoeff (t : ZMod d) :=
    Conjectures.QuadraticPrimes.SieveSwitchedFourier_aux.coeff_eq_zero_iff
      (d := d) (p := p) (r := r) u hu hdiv t
  have hphase (t : ZMod d) :=
    Conjectures.QuadraticPrimes.SieveSwitchedFourier_aux.phase_eq
      (d := d) (p := p) (r := r) u k hu t
  let g : ZMod d → ℂ := fun v =>
    if 4 * v ^ 2 + 1 = 0 then ZMod.stdAddChar (k * u * v) else 0
  have hpoint (t : ZMod d) :
      (if (4 * (p : ZMod d) * t ^ 2 + 8 * (r : ZMod d) * t +
          ((4 * r ^ 2 + 1) / p : ℕ)) = 0 then
          ZMod.stdAddChar (k * t) else 0) =
        ZMod.stdAddChar (-k * u * (r : ZMod d)) * g (e t) := by
    dsimp [g, e]
    simp only [hcoeff t]
    change
      (if 4 * ((p : ZMod d) * t + (r : ZMod d)) ^ 2 + 1 = 0 then
          ZMod.stdAddChar (k * t) else 0) =
        ZMod.stdAddChar (-k * u * (r : ZMod d)) *
          (if 4 * ((p : ZMod d) * t + (r : ZMod d)) ^ 2 + 1 = 0 then
            ZMod.stdAddChar (k * u * ((p : ZMod d) * t + (r : ZMod d))) else 0)
    rw [hphase t]
    rw [AddChar.map_add_eq_mul]
    split_ifs <;> simp
  calc
    (∑ t : ZMod d, if (4 * (p : ZMod d) * t ^ 2 + 8 * (r : ZMod d) * t +
          ((4 * r ^ 2 + 1) / p : ℕ)) = 0 then
          ZMod.stdAddChar (k * t) else 0) =
        ∑ t : ZMod d, ZMod.stdAddChar (-k * u * (r : ZMod d)) * g (e t) := by
            apply Finset.sum_congr rfl
            intro t _ht
            exact hpoint t
    _ = ZMod.stdAddChar (-k * u * (r : ZMod d)) * ∑ t : ZMod d, g (e t) := by
      rw [Finset.mul_sum]
    _ = ZMod.stdAddChar (-k * u * (r : ZMod d)) * ∑ v : ZMod d, g v := by
      rw [e.sum_comp]

end
end Conjectures.QuadraticPrimes
