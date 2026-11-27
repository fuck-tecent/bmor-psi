import Mathlib

theorem PEqualNP.Outside.L_goldbach_frontier_type2_matrix_bridge :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let deepMinor := fun n : ℕ => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let B₃ := fun n : ℕ => ⌊(n:ℝ)^(2/3:ℝ)⌋₊; let typeII := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let τ₂ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₁ n < a ∧ a ≤ B₂ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let τ₃ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let τ₄ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₃ n < a ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖Jdeep n Λ Λ - deepMinor n‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖Jdeep n Λ Λ - Jdeep n (typeII n) (typeII n)‖ ≤ e * (n : ℝ)) → (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Jdeep n (typeII n) (typeII n) = Jdeep n (τ₁ n) (τ₁ n) + 2 * Jdeep n (τ₁ n) (τ₂ n) + 2 * Jdeep n (τ₁ n) (τ₃ n) + 2 * Jdeep n (τ₁ n) (τ₄ n) + Jdeep n (τ₂ n) (τ₂ n) + 2 * Jdeep n (τ₂ n) (τ₃ n) + 2 * Jdeep n (τ₂ n) (τ₄ n) + Jdeep n (τ₃ n) (τ₃ n) + 2 * Jdeep n (τ₃ n) (τ₄ n) + Jdeep n (τ₄ n) (τ₄ n)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₁ n) (τ₁ n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₁ n) (τ₂ n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₁ n) (τ₄ n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₄ n) (τ₄ n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₂ n) (τ₂ n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₂ n) (τ₄ n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₁ n) (τ₃ n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₂ n) (τ₃ n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₃ n) (τ₄ n)‖ ≤ e * (n : ℝ)) → (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (Jdeep n (τ₃ n) (τ₃ n)).re) → ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (deepMinor n).re := by
  intro w E S Q f Q₁ H wideArcs deepMinor Λ μ U B₁ B₂ B₃ typeII τ₁ τ₂ τ₃ τ₄ Jdeep
  intro hswap htype ⟨N₀,hsplit⟩ h11 h12 h14 h44 h22 h24 h13 h23 h34 h33 e he
  obtain ⟨N₁,h₁⟩ := hswap (e/18) (by positivity)
  obtain ⟨N₂,h₂⟩ := htype (e/18) (by positivity)
  obtain ⟨N₃,h₃⟩ := h11 (e/18) (by positivity)
  obtain ⟨N₄,h₄⟩ := h12 (e/18) (by positivity)
  obtain ⟨N₅,h₅⟩ := h14 (e/18) (by positivity)
  obtain ⟨N₆,h₆⟩ := h44 (e/18) (by positivity)
  obtain ⟨N₇,h₇⟩ := h22 (e/18) (by positivity)
  obtain ⟨N₈,h₈⟩ := h24 (e/18) (by positivity)
  obtain ⟨N₉,h₉⟩ := h13 (e/18) (by positivity)
  obtain ⟨N₁₀,h₁₀⟩ := h23 (e/18) (by positivity)
  obtain ⟨N₁₁,h₁₁⟩ := h34 (e/18) (by positivity)
  obtain ⟨N₁₂,h₁₂⟩ := h33 (e/18) (by positivity)
  refine ⟨N₀+N₁+N₂+N₃+N₄+N₅+N₆+N₇+N₈+N₉+N₁₀+N₁₁+N₁₂, ?_⟩
  intro n hn ev
  have split := congrArg Complex.re (hsplit n (by omega))
  have b₁ := h₁ n (by omega)
  have b₂ := h₂ n (by omega)
  have b₃ := h₃ n (by omega) ev
  have b₄ := h₄ n (by omega) ev
  have b₅ := h₅ n (by omega) ev
  have b₆ := h₆ n (by omega) ev
  have b₇ := h₇ n (by omega) ev
  have b₈ := h₈ n (by omega) ev
  have b₉ := h₉ n (by omega) ev
  have b₁₀ := h₁₀ n (by omega) ev
  have b₁₁ := h₁₁ n (by omega) ev
  have b₁₂ := h₁₂ n (by omega) ev
  have c₁ := (Complex.abs_re_le_norm (Jdeep n Λ Λ - deepMinor n)).trans b₁
  have c₂ := (Complex.abs_re_le_norm (Jdeep n Λ Λ - Jdeep n (typeII n) (typeII n))).trans b₂
  have c₃ := (Complex.abs_re_le_norm (Jdeep n (τ₁ n) (τ₁ n))).trans b₃
  have c₄ := (Complex.abs_re_le_norm (Jdeep n (τ₁ n) (τ₂ n))).trans b₄
  have c₅ := (Complex.abs_re_le_norm (Jdeep n (τ₁ n) (τ₄ n))).trans b₅
  have c₆ := (Complex.abs_re_le_norm (Jdeep n (τ₄ n) (τ₄ n))).trans b₆
  have c₇ := (Complex.abs_re_le_norm (Jdeep n (τ₂ n) (τ₂ n))).trans b₇
  have c₈ := (Complex.abs_re_le_norm (Jdeep n (τ₂ n) (τ₄ n))).trans b₈
  have c₉ := (Complex.abs_re_le_norm (Jdeep n (τ₁ n) (τ₃ n))).trans b₉
  have c₁₀ := (Complex.abs_re_le_norm (Jdeep n (τ₂ n) (τ₃ n))).trans b₁₀
  have c₁₁ := (Complex.abs_re_le_norm (Jdeep n (τ₃ n) (τ₄ n))).trans b₁₁
  simp only [Complex.add_re,Complex.mul_re,Complex.sub_re] at split c₁ c₂ ⊢
  norm_num at split
  have d₁ := abs_le.mp c₁
  have d₂ := abs_le.mp c₂
  have d₃ := abs_le.mp c₃
  have d₄ := abs_le.mp c₄
  have d₅ := abs_le.mp c₅
  have d₆ := abs_le.mp c₆
  have d₇ := abs_le.mp c₇
  have d₈ := abs_le.mp c₈
  have d₉ := abs_le.mp c₉
  have d₁₀ := abs_le.mp c₁₀
  have d₁₁ := abs_le.mp c₁₁
  linarith
