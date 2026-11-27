import Mathlib

theorem Conjectures.Goldbach.FrontierType2B1B1BilinearExpansion :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * ArithmeticFunction.vonMangoldt (m / a); ∀ (n : ℕ) (t : ℝ), S n (τ₁ n) t = ∑ a ∈ Finset.Icc (U n + 1) (B₁ n), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * ∑ r ∈ Finset.Icc (U n + 1) (n / a), ArithmeticFunction.vonMangoldt r * E (((a*r:ℕ):ℝ)*t) := by
  intro E S U B₁ μ τ₁ n t
  let Lm : ℕ → ℝ := ArithmeticFunction.vonMangoldt
  let Ak : ℕ → Finset ℕ := fun k => (Nat.divisors k).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < k / a)
  let Da : ℕ → Finset ℕ := fun a => (Nat.divisors a).filter (fun d => U n < d)
  let Ra : ℕ → Finset ℕ := fun a => Finset.Icc (U n + 1) (n / a)
  let fL : ℕ → ℕ → ℕ → ℂ := fun k a d => (μ d : ℂ) * (Lm (k / a) : ℂ) * E ((k:ℝ)*t)
  let fR : ℕ → ℕ → ℕ → ℂ := fun a d r => (μ d : ℂ) * ((Lm r : ℂ) * E (((a*r:ℕ):ℝ)*t))
  have hsL0 : S n (τ₁ n) t = ∑ k ∈ Finset.range (n+1), ∑ a ∈ Ak k, ∑ d ∈ Da a, fL k a d := by
    dsimp only [S, Ak, Da, fL]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    dsimp only [τ₁]
    rw [Complex.ofReal_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Complex.ofReal_mul, Complex.ofReal_sum]
    rw [Finset.sum_mul, Finset.sum_mul]
  have hsR0 : (∑ a ∈ Finset.Icc (U n + 1) (B₁ n), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * ∑ r ∈ Finset.Icc (U n + 1) (n / a), ArithmeticFunction.vonMangoldt r * E (((a*r:ℕ):ℝ)*t))
      = ∑ a ∈ Finset.Icc (U n + 1) (B₁ n), ∑ d ∈ Da a, ∑ r ∈ Ra a, fR a d r := by
    dsimp only [Da, Ra, fR]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Complex.ofReal_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.mul_sum]
  have hsL : (∑ k ∈ Finset.range (n+1), ∑ a ∈ Ak k, ∑ d ∈ Da a, fL k a d)
      = ∑ x ∈ ((Finset.range (n+1)).sigma Ak).sigma (fun p => Da p.2), fL x.1.1 x.1.2 x.2 := by
    rw [Finset.sum_sigma' (Finset.range (n+1)) Ak (fun k a => ∑ d ∈ Da a, fL k a d)]
    rw [Finset.sum_sigma' ((Finset.range (n+1)).sigma Ak) (fun p => Da p.2) (fun p d => fL p.1 p.2 d)]
  have hsR : (∑ a ∈ Finset.Icc (U n + 1) (B₁ n), ∑ d ∈ Da a, ∑ r ∈ Ra a, fR a d r)
      = ∑ y ∈ ((Finset.Icc (U n + 1) (B₁ n)).sigma Da).sigma (fun q => Ra q.1), fR y.1.1 y.1.2 y.2 := by
    rw [Finset.sum_sigma' (Finset.Icc (U n + 1) (B₁ n)) Da (fun a d => ∑ r ∈ Ra a, fR a d r)]
    rw [Finset.sum_sigma' ((Finset.Icc (U n + 1) (B₁ n)).sigma Da) (fun q => Ra q.1) (fun q r => fR q.1 q.2 r)]
  have key : (∑ x ∈ ((Finset.range (n+1)).sigma Ak).sigma (fun p => Da p.2), fL x.1.1 x.1.2 x.2)
      = ∑ y ∈ ((Finset.Icc (U n + 1) (B₁ n)).sigma Da).sigma (fun q => Ra q.1), fR y.1.1 y.1.2 y.2 := by
    refine Finset.sum_bij' (fun p hp => ⟨⟨p.1.2, p.2⟩, p.1.1 / p.1.2⟩)
      (fun q hq => ⟨⟨q.1.1 * q.2, q.1.1⟩, q.1.2⟩) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨⟨k, a⟩, d⟩ := p
      try dsimp only at *
      obtain ⟨hp1, hp2⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hk1, hka⟩ := Finset.mem_sigma.mp hp1
      obtain ⟨hdiv, hne⟩ := Nat.mem_divisors.mp (Finset.mem_filter.mp hka).1
      try dsimp only at *
      obtain ⟨hUa, haB, hUka⟩ := (Finset.mem_filter.mp hka).2
      try dsimp only at *
      refine Finset.mem_sigma.mpr ⟨Finset.mem_sigma.mpr ⟨?_, ?_⟩, ?_⟩
      · try dsimp only
        exact Finset.mem_Icc.mpr ⟨by omega, haB⟩
      · exact hp2
      · try dsimp only
        refine Finset.mem_Icc.mpr ⟨by omega, ?_⟩
        exact Nat.div_le_div_right (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk1))
    · intro q hq
      obtain ⟨⟨a, d⟩, r⟩ := q
      obtain ⟨hq1, hq2⟩ := Finset.mem_sigma.mp hq
      obtain ⟨haIc, hdDa⟩ := Finset.mem_sigma.mp hq1
      obtain ⟨haU, haB⟩ := Finset.mem_Icc.mp haIc
      try dsimp only at *
      obtain ⟨hrU, hrN⟩ := Finset.mem_Icc.mp hq2
      try dsimp only at *
      have hapos : 0 < a := by omega
      have hrpos : 0 < r := by omega
      have harmul : a * r ≤ n := by
        have h1 : r * a ≤ n := (Nat.le_div_iff_mul_le hapos).mp hrN
        rw [mul_comm a r]
        exact h1
      have hne0 : a * r ≠ 0 := (Nat.mul_pos hapos hrpos).ne'
      refine Finset.mem_sigma.mpr ⟨Finset.mem_sigma.mpr ⟨?_, ?_⟩, hdDa⟩
      · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr harmul)
      · refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_mul_right a r, hne0⟩, ?_⟩
        try dsimp only
        refine ⟨by omega, haB, ?_⟩
        rw [Nat.mul_comm a r, Nat.mul_div_left r hapos]
        omega
    · intro p hp
      obtain ⟨⟨k, a⟩, d⟩ := p
      try dsimp only at *
      obtain ⟨hp1, hp2⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hk1, hka⟩ := Finset.mem_sigma.mp hp1
      obtain ⟨hdiv, hne⟩ := Nat.mem_divisors.mp (Finset.mem_filter.mp hka).1
      try dsimp only at *
      simp only [Sigma.mk.injEq, heq_eq_eq]
      exact ⟨⟨Nat.mul_div_cancel' hdiv, trivial⟩, trivial⟩
    · intro q hq
      obtain ⟨⟨a, d⟩, r⟩ := q
      obtain ⟨hq1, hq2⟩ := Finset.mem_sigma.mp hq
      obtain ⟨haIc, hdDa⟩ := Finset.mem_sigma.mp hq1
      obtain ⟨haU, haB⟩ := Finset.mem_Icc.mp haIc
      try dsimp only at *
      have hapos : 0 < a := by omega
      simp only [Sigma.mk.injEq, heq_eq_eq]
      exact ⟨trivial, by rw [Nat.mul_comm a r]; exact Nat.mul_div_left r hapos⟩
    · intro p hp
      obtain ⟨⟨k, a⟩, d⟩ := p
      try dsimp only at *
      obtain ⟨hp1, hp2⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hk1, hka⟩ := Finset.mem_sigma.mp hp1
      obtain ⟨hdiv, hne⟩ := Nat.mem_divisors.mp (Finset.mem_filter.mp hka).1
      try dsimp only at *
      simp only [fL, fR]
      rw [Nat.mul_div_cancel' hdiv]
      ring
  rw [hsL0, hsR0, hsL, key, ← hsR]
