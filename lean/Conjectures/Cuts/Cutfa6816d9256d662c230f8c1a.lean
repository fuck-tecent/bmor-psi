import Mathlib

-- child 1 zh: 在无界次数的二倍素数段和平方根窗口 n²+1<2X 上，二次相位的非零频率总和至少比负的零频贡献高一个固定正比例。
-- child 1 en: On unbounded dyadic prime blocks and the square-root window n²+1<2X, the total nonzero quadratic Fourier modes stay above the negative zero-mode contribution by a fixed positive fraction of that contribution.
-- child 2 zh: 每个 X≥2 的零频贡献为正；当零频与非零频合计为正时，该窗中存在 n²+1=p 且 p>X 为素数。
-- child 2 en: The zero mode is positive for every X≥2. A positive sum of zero and nonzero modes yields a prime p>X in the window satisfying n²+1=p.

theorem Conjectures.Cuts.Cutfa6816d9256d662c230f8c1a
    (hMargin : let primes := fun X : ℕ => (Finset.Ioc X (2*X)).filter Nat.Prime;
      let roots := fun X : ℕ => (Finset.range (2*X)).filter (fun n => n^2+1 < 2*X);
      let d := fun X : ℕ => ((primes X).card:ℝ) * (roots X).card;
      let e := fun X : ℕ => ∑ p ∈ primes X, ∑ n ∈ roots X, ∑ k ∈ (Finset.range p).erase 0,
        Real.cos (2 * Real.pi * (k:ℝ) * ((n^2+1 : ℕ):ℝ) / (p:ℝ));
      ∃ η : ℝ, 0 < η ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ -(1-η) * d X ≤ e X)
    (hWindow : let primes := fun X : ℕ => (Finset.Ioc X (2*X)).filter Nat.Prime;
      let roots := fun X : ℕ => (Finset.range (2*X)).filter (fun n => n^2+1 < 2*X);
      let d := fun X : ℕ => ((primes X).card:ℝ) * (roots X).card;
      let e := fun X : ℕ => ∑ p ∈ primes X, ∑ n ∈ roots X, ∑ k ∈ (Finset.range p).erase 0,
        Real.cos (2 * Real.pi * (k:ℝ) * ((n^2+1 : ℕ):ℝ) / (p:ℝ));
      ∀ X : ℕ, 2 ≤ X → 0 < d X ∧
        (0 < d X + e X → ∃ n p : ℕ, X < p ∧ Nat.Prime p ∧ n^2+1 = p)) :
    (∀ B : ℕ, ∃ n p : ℕ, B < n ∧ Nat.Prime p ∧ p ∣ n ^ 2 + 1 ∧ n ^ 2 < p ^ 1) := by
  classical
  intro B
  obtain ⟨η,hη,hMany⟩ := hMargin
  obtain ⟨X,hX,hE⟩ := hMany (max 2 (B^2+1))
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX.le
  have hBound : B^2+1 < X := (le_max_right _ _).trans_lt hX
  obtain ⟨hD,hDetect⟩ := hWindow X hX2
  obtain ⟨n,p,hXp,hp,hEq⟩ := hDetect (by nlinarith only [mul_pos hη hD,hE])
  have hn : B < n := by
    apply lt_of_not_ge
    intro h
    have hsq := Nat.pow_le_pow_left h 2
    omega
  refine ⟨n,p,hn,hp,?_,?_⟩
  · rw [hEq]
  · rw [← hEq, pow_one]; omega
