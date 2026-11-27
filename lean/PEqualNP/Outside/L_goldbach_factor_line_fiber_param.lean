import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem PEqualNP.Outside.L_goldbach_factor_line_fiber_param :
    ∀ (a b N r₀ s₀ : ℤ), 0 < a → 0 < b → a*r₀+b*s₀=N →
      let g := (Int.gcd a b : ℤ)
      ∀ r s : ℤ, a*r+b*s=N ↔ ∃ j : ℤ, r=r₀+(b/g)*j ∧ s=s₀-(a/g)*j := by
  intro a b N r₀ s₀ ha hb h₀
  dsimp only
  intro r s
  let g : ℤ := Int.gcd a b
  let A : ℤ := a / g
  let B : ℤ := b / g
  change a*r+b*s=N ↔ ∃ j : ℤ, r=r₀+B*j ∧ s=s₀-A*j
  have hgNat : 0 < Int.gcd a b := Int.gcd_pos_of_ne_zero_left b (ne_of_gt ha)
  have hg : 0 < g := Int.ofNat_lt.mpr hgNat
  have hA : A*g = a := Int.ediv_mul_cancel (Int.gcd_dvd_left a b)
  have hB : B*g = b := Int.ediv_mul_cancel (Int.gcd_dvd_right a b)
  have hBnz : B ≠ 0 := by
    intro h
    rw [h, zero_mul] at hB
    omega
  have hcop : Int.gcd B A = 1 := by
    rw [Int.gcd_comm B A]
    exact Int.gcd_ediv_gcd_ediv_gcd hgNat
  constructor
  · intro h
    have hline : A*(r-r₀) + B*(s-s₀) = 0 := by
      apply mul_right_cancel₀ (ne_of_gt hg)
      calc
        (A*(r-r₀) + B*(s-s₀))*g = (A*g)*r + (B*g)*s - ((A*g)*r₀ + (B*g)*s₀) := by ring
        _ = 0*g := by rw [hA, hB, h, h₀, sub_self, zero_mul]
    have hdivprod : B ∣ A*(r-r₀) := by
      refine ⟨-(s-s₀), ?_⟩
      rw [mul_neg]
      exact eq_neg_of_add_eq_zero_left hline
    obtain ⟨j, hj⟩ := Int.dvd_of_dvd_mul_right_of_gcd_one hdivprod hcop
    refine ⟨j, by omega, ?_⟩
    apply mul_left_cancel₀ hBnz
    have hzero : B*(s-s₀)+B*(A*j)=0 := by
      calc
        B*(s-s₀)+B*(A*j) = A*(B*j)+B*(s-s₀) := by ring
        _ = 0 := by rw [← hj]; exact hline
    calc
      B*s = B*s₀ + (B*(s-s₀)+B*(A*j)) - B*(A*j) := by ring
      _ = B*(s₀-A*j) := by rw [hzero]; ring
  · rintro ⟨j, rfl, rfl⟩
    calc
      a*(r₀+B*j)+b*(s₀-A*j) = (A*g)*(r₀+B*j)+(B*g)*(s₀-A*j) := by rw [hA, hB]
      _ = (A*g)*r₀ + (B*g)*s₀ := by ring
      _ = N := by rw [hA, hB, h₀]
