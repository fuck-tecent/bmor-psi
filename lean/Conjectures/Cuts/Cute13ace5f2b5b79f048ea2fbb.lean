import Mathlib

-- child 1 zh: 计算公平首位和 17/200 翻转概率的十六位余弦加权均值，证明它严格大于 1863/2500。
-- child 1 en: Prove the 16-bit cosine mean with a fair initial bit and transition probability 17/200 exceeds 1863/2500.
-- child 2 zh: 用固定翻转数的字族比较全长度指数和与十六位模型均值，统一控制每字总损失为 240。
-- child 2 en: Construct the fixed-transition word family and compare its total real-part sum with the 16-bit model mean at a loss of at most 240 per word.

theorem Conjectures.Cuts.Cute13ace5f2b5b79f048ea2fbb
  (hCertificate :
    ∀ B : ℕ, B = 256 →
    let flips := fun a : ℕ =>
      ((Finset.range 15).filter (fun j => a.testBit j ≠ a.testBit (j + 1))).card
    let term := fun a : ℕ =>
      ((17 ^ flips a * 183 ^ (15 - flips a) : ℕ) : ℝ) *
        Real.cos (2 * Real.pi * (a : ℝ) / 65536)
    let mean := (∑ i ∈ Finset.range B, ∑ j ∈ Finset.range B, term (B * i + j)) / (2 * 200 ^ 15)
    (1863 / 2500 : ℝ) < mean)
  (hTransfer :
    ∀ B : ℕ, B = 256 →
    let flips := fun a : ℕ =>
      ((Finset.range 15).filter (fun j => a.testBit j ≠ a.testBit (j + 1))).card
    let term := fun a : ℕ =>
      ((17 ^ flips a * 183 ^ (15 - flips a) : ℕ) : ℝ) *
        Real.cos (2 * Real.pi * (a : ℝ) / 65536)
    let mean := (∑ i ∈ Finset.range B, ∑ j ∈ Finset.range B, term (B * i + j)) / (2 * 200 ^ 15)
    let G := fun (L : ℕ) (x : ℝ) =>
      ∑ j ∈ Finset.range L,
        Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ j * x⌋ /
          (65536 : ℝ)) * Complex.I)
    ∀ m : ℝ, m < mean → ∀ t : ℕ, 2000 ≤ t →
      let L := 1000 * t + 1
      ∃ F ⊆ Finset.range (2 ^ L), 2 * (1000 * t).choose (85 * t) ≤ F.card ∧
        (m * (L : ℝ) - 240) * (F.card : ℝ) ≤
          ∑ a ∈ F, (G L ((a : ℝ) / (2 : ℝ) ^ L)).re) :
  (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => ∑ x3 ∈ Finset.range x1, Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ x3 * x2⌋ / (65536 : ℝ)) * Complex.I); ∀ (x2 : ℕ),   (2000 : ℕ) ≤ x2 →     have x4 : ℕ := (1000 : ℕ) * x2 + (1 : ℕ);     ∃ x5 ⊆ Finset.range ((2 : ℕ) ^ x4), (2 : ℕ) * ((1000 : ℕ) * x2).choose ((85 : ℕ) * x2) ≤ x5.card ∧ (745 / 1000 : ℝ) * ↑x4 * ↑x5.card < ∑ x6 ∈ x5, (x1 x4 (↑x6 / (2 : ℝ) ^ x4)).re) := by
  suffices ∀ B : ℕ, B = 256 → _ from this 256 rfl
  intro B hB G t ht L
  obtain ⟨F, hF, hCount, hTotal⟩ :=
    hTransfer B hB (1863 / 2500 : ℝ) (hCertificate B hB) t ht
  refine ⟨F, hF, hCount, ?_⟩
  have hL : 2000001 ≤ L := by
    dsimp only [L]
    omega
  have hLreal : (2000001 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hChoose : 0 < (1000 * t).choose (85 * t) := Nat.choose_pos (by omega)
  have hCardNat : 0 < F.card := by omega
  have hCard : 0 < (F.card : ℝ) := by exact_mod_cast hCardNat
  have hGap : (745 / 1000 : ℝ) * (L : ℝ) < (1863 / 2500 : ℝ) * (L : ℝ) - 240 :=
    by linarith only [hLreal]
  exact (mul_lt_mul_of_pos_right hGap hCard).trans_le hTotal
