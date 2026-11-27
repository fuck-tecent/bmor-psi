import Mathlib

/-- For an odd prime `p` and positive `a`, `b`, the multiplicity of `p` in the local discriminant
`16 * a ^ 2 * b ^ 2 * (a + b) ^ 2` is twice its multiplicity in `a * b * (a + b)`: the factor `16`
contributes nothing at odd primes and `(a * b * (a + b)) ^ 2` doubles the multiplicity. -/
private lemma aux_double_multiplicity (p a b : ℕ) (hpp : Nat.Prime p) (hodd : Odd p)
    (ha : 0 < a) (hb : 0 < b) :
    multiplicity p (16*a^2*b^2*(a+b)^2) = 2 * multiplicity p (a*b*(a+b)) := by
  haveI : Fact p.Prime := ⟨hpp⟩
  have hrw : (16*a^2*b^2*(a+b)^2) = 16 * (a*b*(a+b))^2 := by ring
  have h16 : multiplicity p 16 = 0 := by
    apply multiplicity_eq_zero_of_not_dvd
    intro hd
    have h2 : p ∣ (2:ℕ)^4 := by simpa using hd
    have h2' : p ∣ 2 := hpp.dvd_of_dvd_pow h2
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2'
    have hge : 2 ≤ p := hpp.two_le
    have hpeq : p = 2 := by omega
    obtain ⟨k, hk⟩ := hodd
    omega
  rw [hrw, Nat.multiplicity_mul (by norm_num) (by positivity), Nat.multiplicity_pow, h16,
    zero_add]

theorem Conjectures.JoshiAbc.BoundedLocalSzpiro :
    ∀ (a b M : ℕ) (S : Finset ℕ), 0<a → 0<b → Nat.Coprime a b → (∀ p ∈ S, p.Prime ∧ Odd p ∧ multiplicity p (a*b*(a+b)) ≤ M) → S.sum (fun p => (multiplicity p (16*a^2*b^2*(a+b)^2):ℝ)*Real.log p) ≤ 2*(M:ℝ)*S.sum (fun p => Real.log p) := by
  intro a b M S ha hb _ hS
  have key : ∀ p ∈ S, multiplicity p (16*a^2*b^2*(a+b)^2) ≤ 2 * M := by
    intro p hp
    obtain ⟨hpp, hodd, hM⟩ := hS p hp
    have h2 : multiplicity p (16*a^2*b^2*(a+b)^2) = 2 * multiplicity p (a*b*(a+b)) :=
      aux_double_multiplicity p a b hpp hodd ha hb
    omega
  calc S.sum (fun p => (multiplicity p (16*a^2*b^2*(a+b)^2):ℝ)*Real.log p)
      ≤ S.sum (fun p => (2*(M:ℝ))*Real.log p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hlog : 0 ≤ Real.log (p:ℝ) := by
          apply Real.log_nonneg
          have hp2 : (2:ℕ) ≤ p := (hS p hp).1.two_le
          exact_mod_cast (show (1:ℕ) ≤ p by omega)
        have hkeyR : (multiplicity p (16*a^2*b^2*(a+b)^2):ℝ) ≤ 2*(M:ℝ) := by
          have hk := key p hp
          calc (multiplicity p (16*a^2*b^2*(a+b)^2):ℝ) ≤ ((2*M:ℕ):ℝ) := by exact_mod_cast hk
            _ = 2*(M:ℝ) := by push_cast; ring
        exact mul_le_mul_of_nonneg_right hkeyR hlog
    _ = 2*(M:ℝ) * S.sum (fun p => Real.log p) := by
        rw [Finset.mul_sum]
