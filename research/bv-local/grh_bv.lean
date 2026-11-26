import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

noncomputable section

def psiClass (X q a : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 X).filter (fun k => k % q = a % q),
    ArithmeticFunction.vonMangoldt k

def psiError (X q a : ℕ) : ℝ :=
  |psiClass X q a - (X : ℝ) / (Nat.totient q : ℝ)|

/-- The standard GRH consequence for primes in arithmetic progressions, treated
here as the analytic input. -/
def GRHPrimeErrorBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ X q a : ℕ, 2 ≤ X → 1 ≤ q → Nat.Coprime a q →
    psiError X q a ≤ C * Real.sqrt X * (Real.log X) ^ 2

/-- Classical Bombieri–Vinogradov with the usual logarithmic modulus cutoff. -/
def BVLogLevel (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ (B C : ℝ) (X₀ : ℕ), 0 < C ∧
    ∀ X : ℕ, X₀ ≤ X → ∃ b : ℕ → ℝ,
      (∀ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ θ / (Real.log X) ^ B⌋₊,
        ∀ a : ℕ, Nat.Coprime a q → psiError X q a ≤ b q) ∧
      (∑ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ θ / (Real.log X) ^ B⌋₊, b q) ≤
        C * (X : ℝ) / (Real.log X) ^ A

lemma grh_bv_budget {X C A : ℝ} (hX : 1 < X) :
    (Real.sqrt X / (Real.log X) ^ (A + 2)) *
        (C * Real.sqrt X * (Real.log X) ^ 2) =
      C * X / (Real.log X) ^ A := by
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hL : 0 < Real.log X := Real.log_pos hX
  have hLne : Real.log X ≠ 0 := hL.ne'
  have hsqrt : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX0.le
  rw [div_mul_eq_mul_div]
  have hnum : (Real.sqrt X * (C * Real.sqrt X * (Real.log X) ^ 2)) =
      C * X * (Real.log X) ^ 2 := by
    calc
      _ = C * (Real.sqrt X) ^ 2 * (Real.log X) ^ 2 := by ring
      _ = C * X * (Real.log X) ^ 2 := by rw [hsqrt]
  rw [hnum]
  have hpow : (Real.log X) ^ (A + 2) = (Real.log X) ^ A * (Real.log X) ^ 2 := by
    rw [Real.rpow_add hL]
    norm_num
  rw [hpow]
  field_simp [hLne]

theorem bv_log_level_one_half_of_grh (h : GRHPrimeErrorBound) :
    BVLogLevel (1 / 2 : ℝ) := by
  intro A hA
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨A + 2, C, 3, hC, ?_⟩
  intro X hX
  have hX1 : 1 < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos hX1
  let Q : ℕ := ⌊(X : ℝ) ^ (1 / 2 : ℝ) / (Real.log (X : ℝ)) ^ (A + 2)⌋₊
  let b : ℕ → ℝ := fun _ => C * Real.sqrt X * (Real.log (X : ℝ)) ^ 2
  refine ⟨b, ?_, ?_⟩
  · intro q hq a hcop
    simp only [b]
    exact hbound X q a (by omega) (Finset.mem_Icc.mp hq).1 hcop
  · have hQ : (Q : ℝ) ≤
        (X : ℝ) ^ (1 / 2 : ℝ) / (Real.log (X : ℝ)) ^ (A + 2) := by
      dsimp only [Q]
      exact Nat.floor_le (by positivity)
    have hsum : (∑ q ∈ Finset.Icc 1 Q, b q) = (Q : ℝ) * b 1 := by
      simp [b, Nat.card_Icc]
    rw [hsum]
    have hsqrt : (X : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt X := by
      rw [Real.sqrt_eq_rpow]
    have hbudget : (Q : ℝ) * b 1 ≤
        ((X : ℝ) ^ (1 / 2 : ℝ) / (Real.log (X : ℝ)) ^ (A + 2)) *
          (C * Real.sqrt X * (Real.log (X : ℝ)) ^ 2) := by
      apply mul_le_mul_of_nonneg_right hQ
      dsimp only [b]
      positivity
    have hidentity := grh_bv_budget (X := (X : ℝ)) (C := C) (A := A) hX1
    rw [hsqrt] at hbudget
    exact hbudget.trans_eq hidentity

end

end PEqualNP.Outside
