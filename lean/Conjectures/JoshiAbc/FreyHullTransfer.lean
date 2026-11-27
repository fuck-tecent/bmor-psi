import Mathlib

theorem Conjectures.JoshiAbc.FreyHullTransfer :
    let rad := fun (n : ℕ) => n.primeFactors.prod id; let r := fun (a b : ℕ) => Real.log (rad (a*b*(a+b))); ∀ (l : ℕ) (K : ℝ) (Q R U δ A : ℕ → ℕ → ℝ), 7 ≤ l → let k := 4*(l:ℝ)/(((l:ℝ)-3)*(l+1)); let H := fun (a b : ℕ) => Real.log (16*((a:ℝ)^2+a*b+(b:ℝ)^2))/2; (∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → -(((l:ℝ)+1)/4)*Q a b-δ a b ≤ R a b ∧ R a b ≤ -((l:ℝ)*(l+1)/12)*Q a b+U a b ∧ H a b ≤ 2*l*Q a b/6+A a b ∧ A a b + k*(U a b+δ a b) ≤ (1+k)*r a b+K) → ∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → H a b ≤ (1+k)*r a b+K := by
  dsimp only
  intro l K Q R U δ A hl
  intro h a b ha hb hab
  rcases h a b ha hb hab with ⟨hR_lower, hR_upper, hH, hA⟩
  have hl_real : (7 : ℝ) ≤ (l : ℝ) := by
    exact_mod_cast hl
  have hl_nonneg : 0 ≤ (l : ℝ) := by
    nlinarith
  have hD : 0 < ((l : ℝ) - 3) * ((l : ℝ) + 1) := by
    nlinarith
  have hkey :
      (((l : ℝ) - 3) * ((l : ℝ) + 1)) * Q a b ≤
        12 * (U a b + δ a b) := by
    nlinarith [hR_lower, hR_upper]
  have hQ :
      2 * (l : ℝ) * Q a b / 6 ≤
        (4 * (l : ℝ) / (((l : ℝ) - 3) * ((l : ℝ) + 1))) *
          (U a b + δ a b) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hD]
    nlinarith [mul_le_mul_of_nonneg_left hkey hl_nonneg]
  linarith [hH, hQ, hA]
