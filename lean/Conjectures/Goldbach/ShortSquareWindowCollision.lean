import Mathlib

theorem Conjectures.Goldbach.ShortSquareWindowCollision :
∀ (P H a b c d : ℤ), 0 ≤ P → 0 ≤ H → H ^ 2 ≤ 8 * P + 4 * H + 4 → P ≤ a → a ≤ b → b ≤ P + H → P ≤ c → c ≤ d → d ≤ P + H → a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 → a + b ≤ c + d → (a = c ∧ b = d) ∨ (H ^ 2 = 8 * P + 4 * H + 4 ∧ a = P ∧ b = P + H ∧ c = d ∧ 2 * c = 2 * P + H + 2) := by
  intro P H a b c d hP hH hcap hPa hab hbH hPc hcd hdH he hsum
  by_cases same : a+b=c+d
  · left
    have eq : (b-a)^2=(d-c)^2 := by nlinarith [show (a+b)^2=(c+d)^2 by rw [same]]
    have := (sq_eq_sq₀ (by omega : 0 ≤ b-a) (by omega : 0 ≤ d-c)).mp eq
    omega
  have parity (x : ℤ) : x^2 % 2 = x % 2 := by
    rw [pow_two,Int.mul_emod]
    rcases (show x % 2=0 ∨ x % 2=1 by omega) with h|h <;> rw [h] <;> decide
  have modtwo := congrArg (fun z : ℤ => z % 2) he
  change (a^2+b^2) % 2=(c^2+d^2) % 2 at modtwo
  have pa := parity a
  have pb := parity b
  have pc := parity c
  have pd := parity d
  have gap : a+b+2 ≤ c+d := by omega
  clear modtwo pa pb pc pd parity
  have large := pow_le_pow_left₀ (by omega : 0 ≤ a+b+2) gap 2
  have e1 : 8*P+4*(b-a)+4 ≤ (b-a)^2 := by nlinarith [sq_nonneg (d-c)]
  have bound : 4 < b-a := by
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr h)]
  have ed : b-a=H := by
    by_contra h
    have pos := mul_pos (show 0 < H-(b-a) by omega) (show 0 < H+(b-a)-4 by omega)
    nlinarith
  have ea : a=P := by omega
  have eb : b=P+H := by omega
  subst a
  subst b
  have zd : d-c = 0 := by
    by_contra h
    nlinarith [sq_pos_of_ne_zero h]
  have sqeq : H^2=8*P+4*H+4 := by nlinarith
  have sums : c+d=P+(P+H)+2 := by
    by_contra h
    have strict := mul_pos (show 0 < c+d-(P+(P+H)+2) by omega) (show 0 < c+d+(P+(P+H)+2) by omega)
    have zz : (d-c)^2=0 := by rw [zd]; norm_num
    nlinarith only [strict,he,zz,sqeq]
  right
  exact ⟨sqeq,rfl,rfl,by omega,by omega⟩
