import Mathlib

theorem Conjectures.JoshiAbc.WeakFromFrey :
    (let rad := fun (n : ℕ) => n.primeFactors.prod id; let r := fun (a b : ℕ) => Real.log (rad (a*b*(a+b))); ∃ K : ℝ, ∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → Real.log (16*((a:ℝ)^2+a*b+(b:ℝ)^2))/2 ≤ (15/8 : ℝ)*r a b+K) → let rad := fun (n : ℕ) => n.primeFactors.prod id; let h := fun (a b : ℕ) => Real.log ((a:ℝ)+b); let r := fun (a b : ℕ) => Real.log (rad (a*b*(a+b))); ∃ C : ℝ, ∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → h a b ≤ (15/8)*r a b+C := by
  intro hyp
  dsimp only at hyp
  dsimp only
  obtain ⟨K, hK⟩ := hyp
  refine ⟨K, ?_⟩
  intro a b ha hb hab
  have ha' : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hb' : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hsq : ((a:ℝ)+(b:ℝ))^2 ≤ 16*((a:ℝ)^2+(a:ℝ)*(b:ℝ)+(b:ℝ)^2) := by
    nlinarith [sq_nonneg ((a:ℝ)-(b:ℝ)), ha', hb']
  have hlog : Real.log (((a:ℝ)+(b:ℝ))^2) ≤ Real.log (16*((a:ℝ)^2+(a:ℝ)*(b:ℝ)+(b:ℝ)^2)) :=
    Real.log_le_log (by positivity) hsq
  rw [Real.log_pow] at hlog
  push_cast at hlog
  linarith [hK a b ha hb hab]
