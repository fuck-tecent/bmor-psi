import Mathlib

theorem Conjectures.QuadraticPrimes.SieveSwitchedCofactor :
    let f := fun k : ℕ => 4*k^2+1; ∀ p r t : ℕ, 2<p → p.Prime → r<p → p ∣ f r →
  let cofactor := 4*p*t^2+8*r*t+(f r)/p;
  f (p*t+r) = p*cofactor ∧
    (8*(r : ℤ))^2 - 4*(4*(p : ℤ))*((f r / p : ℕ) : ℤ) = -16 ∧
    (∀ d : ℕ, Nat.Coprime d p → (d ∣ cofactor ↔ d ∣ f (p*t+r))) := by
  intro f p r t h2 hp hrt hdiv cofactor
  have hfr : f r = 4*r^2+1 := rfl
  have hmul : p * (f r / p) = f r := by
    rw [Nat.mul_comm]; exact Nat.div_mul_cancel hdiv
  refine ⟨?_, ?_, ?_⟩
  · change 4*(p*t+r)^2+1 = p*cofactor
    change 4*(p*t+r)^2+1 = p*(4*p*t^2+8*r*t+(f r)/p)
    rw [Nat.mul_add, Nat.mul_add, hmul, hfr]
    ring
  · have hm : ((f r / p : ℕ) : ℤ) * (p : ℤ) = (f r : ℤ) := by
      exact_mod_cast Nat.div_mul_cancel hdiv
    have hm2 : (p : ℤ) * ((f r / p : ℕ) : ℤ) = (f r : ℤ) := by
      rw [mul_comm]; exact hm
    have hfrz : (f r : ℤ) = 4*(r:ℤ)^2+1 := by rw [hfr]; push_cast; ring
    rw [hfrz] at hm2
    linear_combination (-16) * hm2
  · intro d hd
    have hkey1 : f (p*t+r) = p*cofactor := by
      change 4*(p*t+r)^2+1 = p*cofactor
      change 4*(p*t+r)^2+1 = p*(4*p*t^2+8*r*t+(f r)/p)
      rw [Nat.mul_add, Nat.mul_add, hmul, hfr]
      ring
    constructor
    · intro hdvd
      exact hkey1.symm ▸ dvd_mul_of_dvd_right hdvd p
    · intro hdvd
      exact hd.dvd_of_dvd_mul_left (hkey1 ▸ hdvd)
