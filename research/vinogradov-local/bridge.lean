import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

noncomputable section

def w (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0

def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (u k : ℂ) * E ((k : ℝ) * t)

def Qpow (B n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ B

def arcsPoly (B n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qpow B n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / q| ≤ (Qpow B n : ℝ) / ((q : ℝ) * n)}

def VinogradovPolylogInput : Prop :=
  ∀ A : ℝ, 0 < A → ∀ B : ℕ, 4 ≤ B → ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ arcsPoly B n →
      ‖S n w t‖ ≤ (n : ℝ) * (Real.log (n : ℝ)) ^ (-A) ∧
      ‖S n (fun k => ArithmeticFunction.vonMangoldt k) t‖ ≤
        (n : ℝ) * (Real.log (n : ℝ)) ^ (-A)

theorem vinogradov_polylog_of_input (h : VinogradovPolylogInput) :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0;
     let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
     let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) =>
       ∑ k ∈ Finset.range (n + 1), (u k : ℂ) * E ((k : ℝ) * t);
     let Qpow := fun (B n : ℕ) => (Nat.log 2 (n + 2)) ^ B;
     let arcsPoly := fun (B n : ℕ) =>
       {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qpow B n ∧ a ≤ q ∧ Nat.Coprime a q ∧
         |t - (a : ℝ) / q| ≤ (Qpow B n : ℝ) / ((q : ℝ) * n)};
     ∀ A : ℝ, 0 < A → ∃ N : ℕ,
       ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1,
         t ∉ arcsPoly (2 * ⌈A⌉₊ + 16) n →
           ‖S n ArithmeticFunction.vonMangoldt t‖ ≤ (n : ℝ) * (Real.log (n : ℝ)) ^ (-A) ∧
           ‖S n w t‖ ≤ (n : ℝ) * (Real.log (n : ℝ)) ^ (-A)) := by
  dsimp only
  intro A hA
  let B₀ : ℕ := 2 * ⌈A⌉₊ + 16
  have hB₀ : 4 ≤ B₀ := by
    dsimp [B₀]
    omega
  obtain ⟨N, hN⟩ := h A hA B₀ hB₀
  refine ⟨N, ?_⟩
  intro n hn t htI ht
  obtain ⟨hw, hΛ⟩ := hN n hn t htI ht
  exact ⟨hΛ, hw⟩

end

end PEqualNP.Outside
