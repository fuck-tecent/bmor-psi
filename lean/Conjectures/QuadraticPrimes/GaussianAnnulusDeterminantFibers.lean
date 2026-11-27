import Mathlib

theorem Conjectures.QuadraticPrimes.GaussianAnnulusDeterminantFibers :
    ∀ a b c d : ℤ, (a,b) ≠ (0,0) → let g : ℤ := Int.gcd a b; ∀ u v : ℤ, a*v-b*u=a*d-b*c ↔ ∃ t : ℤ, u=c+t*(a/g) ∧ v=d+t*(b/g) := by
  intro a b c d hne
  dsimp only
  intro u v
  let g : ℤ := Int.gcd a b
  let A : ℤ := a / g
  let B : ℤ := b / g
  change a*v-b*u = a*d-b*c ↔ ∃ t : ℤ, u = c + t*A ∧ v = d + t*B
  have hgNat : Int.gcd a b ≠ 0 := by
    intro h0
    have h01 := Int.gcd_eq_zero_iff.mp h0
    exact hne (Prod.ext h01.1 h01.2)
  have hg : g ≠ 0 := Nat.cast_ne_zero.mpr hgNat
  have hA : A*g = a := Int.ediv_mul_cancel (Int.gcd_dvd_left a b)
  have hB : B*g = b := Int.ediv_mul_cancel (Int.gcd_dvd_right a b)
  have hbez : A * Int.gcdA a b + B * Int.gcdB a b = 1 := by
    apply mul_right_cancel₀ hg
    calc
      (A * Int.gcdA a b + B * Int.gcdB a b) * g
          = a * Int.gcdA a b + b * Int.gcdB a b := by
              linear_combination Int.gcdA a b * hA + Int.gcdB a b * hB
      _ = g := (Int.gcd_eq_gcd_ab a b).symm
      _ = 1 * g := by ring
  constructor
  · intro h
    have hrel : A*(v-d) = B*(u-c) := by
      apply mul_right_cancel₀ hg
      linear_combination (v-d) * hA - (u-c) * hB + h
    refine ⟨Int.gcdA a b * (u-c) + Int.gcdB a b * (v-d), ?_, ?_⟩
    · have hAt : A * (Int.gcdA a b * (u-c) + Int.gcdB a b * (v-d)) = u - c := by
        calc
          A * (Int.gcdA a b * (u-c) + Int.gcdB a b * (v-d))
              = A * (Int.gcdA a b * (u-c)) + Int.gcdB a b * (A*(v-d)) := by ring
          _ = A * (Int.gcdA a b * (u-c)) + Int.gcdB a b * (B*(u-c)) := by rw [hrel]
          _ = (A * Int.gcdA a b + B * Int.gcdB a b) * (u-c) := by ring
          _ = u - c := by rw [hbez]; ring
      linear_combination -hAt
    · have hBt : B * (Int.gcdA a b * (u-c) + Int.gcdB a b * (v-d)) = v - d := by
        calc
          B * (Int.gcdA a b * (u-c) + Int.gcdB a b * (v-d))
              = Int.gcdA a b * (B*(u-c)) + B * (Int.gcdB a b * (v-d)) := by ring
          _ = Int.gcdA a b * (A*(v-d)) + B * (Int.gcdB a b * (v-d)) := by rw [hrel]
          _ = (A * Int.gcdA a b + B * Int.gcdB a b) * (v-d) := by ring
          _ = v - d := by rw [hbez]; ring
      linear_combination -hBt
  · rintro ⟨t, rfl, rfl⟩
    have hz : a*t*B - b*t*A = 0 := by rw [← hA, ← hB]; ring
    have key : a*(d+t*B) - b*(c+t*A) = (a*d - b*c) + (a*t*B - b*t*A) := by ring
    rw [key, hz, add_zero]
