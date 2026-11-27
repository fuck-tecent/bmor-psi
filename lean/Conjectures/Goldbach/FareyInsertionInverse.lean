import Mathlib

namespace Conjectures.Goldbach.FareyInsertionInverse_aux

/-- Existence of a representative of the inverse of `u` modulo `n` inside `[1, n-1]`. -/
lemma exists_inv (n u : ℕ) (hn : 1 < n) (hc : u.Coprime n) :
    ∃ a : ℕ, 0 < a ∧ a < n ∧ (a * u) % n = 1 := by
  obtain ⟨m, hm, hmu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc hn
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hmu
    · exact h
  exact ⟨m, hm0, hm, by rwa [mul_comm]⟩

/-- Two representatives of the inverse of `u` modulo `n` that both lie in `[0, n-1]` agree. -/
lemma inv_unique (n u a a' : ℕ) (hc : u.Coprime n) (ha : a < n) (ha' : a' < n)
    (h1 : (a * u) % n = 1) (h2 : (a' * u) % n = 1) : a = a' := by
  have hmodeq : a * u ≡ a' * u [MOD n] := by
    show (a * u) % n = (a' * u) % n
    rw [h1, h2]
  have hcancel : a % n = a' % n :=
    Nat.ModEq.cancel_right_of_coprime (m := n) (c := u) hc.symm hmodeq
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at hcancel

/-- From the inverse `a` of `u` modulo `n` one recovers the two neighbouring numerators
`b = (a*u-1)/n` and `c = a-b`, together with the three determinant identities. -/
lemma neighbours (n u a : ℕ) (hn : 1 < n) (hu : 0 < u) (hun : u < n) (ha0 : 0 < a)
    (han : a < n) (hmod : (a * u) % n = 1) :
    ∃ b c : ℕ, b < u ∧ c ≤ n - u ∧ a * u = b * n + 1 ∧ c * n = a * (n - u) + 1 ∧
      c * u = b * (n - u) + 1 := by
  let b := (a * u) / n
  let c := a - b
  have hrepr : a * u = b * n + 1 := by
    calc
      a * u = n * ((a * u) / n) + (a * u) % n := (Nat.div_add_mod _ _).symm
      _ = n * ((a * u) / n) + 1 := by rw [hmod]
      _ = b * n + 1 := by dsimp [b]; ring
  have hba : b < a := by
    have huan : a * u < a * n := Nat.mul_lt_mul_of_pos_left hun ha0
    nlinarith
  have hbu : b < u := by
    have haun : a * u < n * u := Nat.mul_lt_mul_of_pos_right han hu
    nlinarith
  have hbnle : b * n ≤ a * n := Nat.mul_le_mul (Nat.le_of_lt hba) (Nat.le_refl n)
  have hbn1 : b * n + 1 ≤ a * n := by
    have hba1 : b + 1 ≤ a := hba
    have hmul := Nat.mul_le_mul hba1 (Nat.le_refl n)
    nlinarith
  have hbun : b * u ≤ b * n := Nat.mul_le_mul (Nat.le_refl b) (Nat.le_of_lt hun)
  have hcn : c * n = a * (n - u) + 1 := by
    dsimp [c]
    rw [Nat.mul_sub_right_distrib, Nat.mul_sub_left_distrib, hrepr]
    omega
  have hcu : c * u = b * (n - u) + 1 := by
    dsimp [c]
    rw [Nat.mul_sub_right_distrib, Nat.mul_sub_left_distrib, hrepr]
    omega
  have hc_le : c ≤ n - u := by
    have hd : 0 < n - u := Nat.sub_pos_of_lt hun
    nlinarith
  exact ⟨b, c, hbu, hc_le, hrepr, hcn, hcu⟩

end Conjectures.Goldbach.FareyInsertionInverse_aux

/-- For every ordered coprime denominator pair `(u, n-u)` the insertion numerator at order `n`
is the least positive inverse of `u` modulo `n`, and it is unique. -/
theorem Conjectures.Goldbach.FareyInsertionInverse :
  ∀ n u : ℕ, 1 < n → 0 < u → u < n → u.Coprime n → ∃! a : ℕ, 0 < a ∧ a < n ∧ (a*u)%n = 1 ∧ ∃ b c : ℕ, b < u ∧ c ≤ n-u ∧ a*u = b*n+1 ∧ c*n = a*(n-u)+1 ∧ c*u = b*(n-u)+1 := by
  intro n u hn hu hun hc
  obtain ⟨a, ha0, han, hmod⟩ :=
    Conjectures.Goldbach.FareyInsertionInverse_aux.exists_inv n u hn hc
  refine ⟨a, ⟨ha0, han, hmod,
    Conjectures.Goldbach.FareyInsertionInverse_aux.neighbours n u a hn hu hun ha0 han hmod⟩, ?_⟩
  rintro a' ⟨ha'0, ha'n, hmod', hbc⟩
  exact Conjectures.Goldbach.FareyInsertionInverse_aux.inv_unique n u a' a hc ha'n han hmod' hmod
