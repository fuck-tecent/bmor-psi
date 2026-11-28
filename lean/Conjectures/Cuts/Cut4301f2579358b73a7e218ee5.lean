import Mathlib

open Finset
open scoped BigOperators

-- child 1 zh: B13 的归一化能量在从 n 到 3n 的偶数上的平均趋于零。
-- child 1 en: The mean of the normalized B13 energy over the even targets from n to 3n tends to zero.
-- child 2 zh: 根号窗均方比倍区间均方的上偏差趋于零。
-- child 2 en: The positive excess of the square-root-window mean over the dyadic-scale mean tends to zero.
-- child 3 zh: 单点归一化能量比其根号窗均值的上偏差趋于零。
-- child 3 en: The positive excess of the normalized point energy over its square-root-window mean tends to zero.
set_option maxHeartbeats 4000000 in
theorem Conjectures.Cuts.Cut4301f2579358b73a7e218ee5 :
  (let B := fun (n : ℕ) (p : ℝ) => ⌊(n : ℝ)^p⌋₊
    let U := fun n => B n (1/16)
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I)
    let w := fun (n l h m : ℕ) =>
      ∑ a ∈ (Nat.divisors m).filter (fun a => l < a ∧ a ≤ h ∧ U n < m/a),
        (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) *
          ArithmeticFunction.vonMangoldt (m/a)
    let S := fun (n l h : ℕ) (t : ℝ) =>
      ∑ k ∈ Finset.range (n+1), (w n l h k : ℂ)*E ((k : ℝ)*t)
    let wide := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B n (1/3) ∧ a ≤ q ∧
      Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤
        ((256*B n (1/3)*(Nat.log 2 (n+2))^2 : ℕ) : ℝ)/((q : ℝ)*(n : ℝ))}
    let J := fun n : ℕ => intervalIntegral (fun t => (wide n)ᶜ.indicator
      (fun x => S n (U n) (B n (1/4)) x*S n (B n (1/3)) (B n (2/3)) x*E (-(n : ℝ)*x)) t)
      (0 : ℝ) 1 MeasureTheory.volume
    let q := fun n : ℕ => (‖J n‖/(n : ℝ))^2
    let A := fun n H : ℕ => (∑ j ∈ Finset.range (H+1), q (n+2*j))/((H+1 : ℕ) : ℝ)
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      A n n ≤ e) →
  (let B := fun (n : ℕ) (p : ℝ) => ⌊(n : ℝ)^p⌋₊
    let U := fun n => B n (1/16)
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I)
    let w := fun (n l h m : ℕ) =>
      ∑ a ∈ (Nat.divisors m).filter (fun a => l < a ∧ a ≤ h ∧ U n < m/a),
        (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) *
          ArithmeticFunction.vonMangoldt (m/a)
    let S := fun (n l h : ℕ) (t : ℝ) =>
      ∑ k ∈ Finset.range (n+1), (w n l h k : ℂ)*E ((k : ℝ)*t)
    let wide := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B n (1/3) ∧ a ≤ q ∧
      Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤
        ((256*B n (1/3)*(Nat.log 2 (n+2))^2 : ℕ) : ℝ)/((q : ℝ)*(n : ℝ))}
    let J := fun n : ℕ => intervalIntegral (fun t => (wide n)ᶜ.indicator
      (fun x => S n (U n) (B n (1/4)) x*S n (B n (1/3)) (B n (2/3)) x*E (-(n : ℝ)*x)) t)
      (0 : ℝ) 1 MeasureTheory.volume
    let q := fun n : ℕ => (‖J n‖/(n : ℝ))^2
    let A := fun n H : ℕ => (∑ j ∈ Finset.range (H+1), q (n+2*j))/((H+1 : ℕ) : ℝ)
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      A n n.sqrt ≤ A n n + e) →
  (let B := fun (n : ℕ) (p : ℝ) => ⌊(n : ℝ)^p⌋₊
    let U := fun n => B n (1/16)
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I)
    let w := fun (n l h m : ℕ) =>
      ∑ a ∈ (Nat.divisors m).filter (fun a => l < a ∧ a ≤ h ∧ U n < m/a),
        (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) *
          ArithmeticFunction.vonMangoldt (m/a)
    let S := fun (n l h : ℕ) (t : ℝ) =>
      ∑ k ∈ Finset.range (n+1), (w n l h k : ℂ)*E ((k : ℝ)*t)
    let wide := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B n (1/3) ∧ a ≤ q ∧
      Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤
        ((256*B n (1/3)*(Nat.log 2 (n+2))^2 : ℕ) : ℝ)/((q : ℝ)*(n : ℝ))}
    let J := fun n : ℕ => intervalIntegral (fun t => (wide n)ᶜ.indicator
      (fun x => S n (U n) (B n (1/4)) x*S n (B n (1/3)) (B n (2/3)) x*E (-(n : ℝ)*x)) t)
      (0 : ℝ) 1 MeasureTheory.volume
    let q := fun n : ℕ => (‖J n‖/(n : ℝ))^2
    let A := fun n H : ℕ => (∑ j ∈ Finset.range (H+1), q (n+2*j))/((H+1 : ℕ) : ℝ)
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      q n ≤ A n n.sqrt + e) →
  (let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let B₃ := fun n : ℕ => ⌊(n:ℝ)^(2/3:ℝ)⌋₊; let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let τ₃ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₁ n) (τ₃ n)‖ ≤ e * (n : ℝ)) := by
  intro long short point
  let F : ℕ → ℂ :=
    let B := fun (n : ℕ) (p : ℝ) => ⌊(n : ℝ)^p⌋₊
    let U := fun n => B n (1/16)
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I)
    let w := fun (n l h m : ℕ) =>
      ∑ a ∈ (Nat.divisors m).filter (fun a => l < a ∧ a ≤ h ∧ U n < m/a),
        (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) *
          ArithmeticFunction.vonMangoldt (m/a)
    let S := fun (n l h : ℕ) (t : ℝ) =>
      ∑ k ∈ Finset.range (n+1), (w n l h k : ℂ)*E ((k : ℝ)*t)
    let wide := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B n (1/3) ∧ a ≤ q ∧
      Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤
        ((256*B n (1/3)*(Nat.log 2 (n+2))^2 : ℕ) : ℝ)/((q : ℝ)*(n : ℝ))}
    let J := fun n : ℕ => intervalIntegral (fun t => (wide n)ᶜ.indicator
      (fun x => S n (U n) (B n (1/4)) x*S n (B n (1/3)) (B n (2/3)) x*E (-(n : ℝ)*x)) t)
      (0 : ℝ) 1 MeasureTheory.volume
    J
  let q (n : ℕ) : ℝ := (‖F n‖/(n : ℝ))^2
  let A (n H : ℕ) : ℝ := (∑ j ∈ range (H+1), q (n+2*j))/((H+1 : ℕ) : ℝ)
  change (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → A n n ≤ e) at long
  change (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    A n n.sqrt ≤ A n n + e) at short
  change (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    q n ≤ A n n.sqrt + e) at point
  change ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖F n‖ ≤ e*(n : ℝ)
  intro e he
  have δpos : 0 < e^2 / 3 := by positivity
  obtain ⟨L, hL⟩ := long (e^2 / 3) δpos
  obtain ⟨S, hS⟩ := short (e^2 / 3) δpos
  obtain ⟨P, hP⟩ := point (e^2 / 3) δpos
  refine ⟨max 1 (max L (max S P)), fun n hn even => ?_⟩
  have long_le := hL n (by omega) even
  have short_le := hS n (by omega) even
  have point_le := hP n (by omega) even
  have small : q n ≤ e^2 := by linarith only [long_le, short_le, point_le]
  have npos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ratio_nonneg : 0 ≤ ‖F n‖ / (n : ℝ) := by positivity
  unfold q at small
  apply (div_le_iff₀ npos).1
  nlinarith only [small, ratio_nonneg, he]
