import Mathlib

private lemma heightBridge_one_le_rad (n : ℕ) : (1 : ℕ) ≤ n.primeFactors.prod id :=
  Finset.one_le_prod (fun _p hp => Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp))

private lemma heightBridge_log_rad_nonneg (a b : ℕ) :
    (0 : ℝ) ≤ Real.log (((a * b * (a + b)).primeFactors.prod id : ℕ) : ℝ) := by
  refine Real.log_nonneg ?_
  have h := heightBridge_one_le_rad (a * b * (a + b))
  exact_mod_cast h

theorem Conjectures.JoshiAbc.HeightBridge :
    (let rad := fun (n : ℕ) => n.primeFactors.prod id; let r := fun (a b : ℕ) => Real.log (rad (a*b*(a+b))); ∀ l : ℕ, l.Prime → 7 ≤ l → ∃ K : ℝ, ∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → Real.log (16*((a:ℝ)^2+a*b+(b:ℝ)^2))/2 ≤ (1+4*(l:ℝ)/(((l:ℝ)-3)*(l+1)))*r a b+K) → (∀ ε : ℝ, 0 < ε → ∃ l : ℕ, l.Prime ∧ 7 ≤ l ∧ 4*(l:ℝ)/(((l:ℝ)-3)*(l+1)) ≤ ε) → (let h := fun (a b : ℕ) => Real.log ((a:ℝ)+b); ∀ a b : ℕ, 0 < a → 0 < b → 2*h a b + Real.log 12 ≤ Real.log (16*((a:ℝ)^2+a*b+(b:ℝ)^2))) → (let rad := fun (n : ℕ) => n.primeFactors.prod id; let h := fun (a b : ℕ) => Real.log ((a:ℝ)+b); let r := fun (a b : ℕ) => Real.log (rad (a*b*(a+b))); ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → h a b ≤ (1+ε)*r a b+C) := by
  dsimp only
  intro hU hAux hH ε hε
  obtain ⟨l, hl, hl7, hk⟩ := hAux ε hε
  obtain ⟨K, hK⟩ := hU l hl hl7
  refine ⟨K, ?_⟩
  intro a b ha hb hab
  have hL := hH a b ha hb
  have hF := hK a b ha hb hab
  have hlog12 : (0 : ℝ) ≤ Real.log 12 := Real.log_nonneg (by norm_num)
  have hr := heightBridge_log_rad_nonneg a b
  have hcoef : (1 + 4*(l:ℝ)/(((l:ℝ)-3)*(l+1))) ≤ 1 + ε := by linarith
  have hstep : (1 + 4*(l:ℝ)/(((l:ℝ)-3)*(l+1))) *
      Real.log (((a * b * (a + b)).primeFactors.prod id : ℕ) : ℝ) ≤
      (1 + ε) * Real.log (((a * b * (a + b)).primeFactors.prod id : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hcoef hr
  linarith
