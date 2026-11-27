import Mathlib
import Conjectures.TwinPrimes.SharpWindowContamination
import Conjectures.Cuts.Taskc7173c36e2211fc2c80c5b0e

-- child 1 zh: 正质量下界（沿无界的严格窗）：存在常数 c 大于 0，使得对每个起点 B 都存在 X 大于 B，窗口 X 小于 n 小于 51X 之 50 内孪生素数对 n 与 n+2 的对数权质量至少为 c 倍 X。
-- child 1 en: Positive mass on unbounded strict windows: some constant c above 0 with, for every bound B, an X above B whose log-weighted mass of twin prime pairs n and n+2 inside the window X below n below 51X over 50 is at least c times X.
-- child 2 zh: 逐项质量界：对每个 X，窗口 X 小于 n 小于 51X 之 50 内孪生素数对 n 与 n+2 的对数权质量不超过同一窗口上 vonMangoldt 在 n 与 n+2 处乘积的和。
-- child 2 en: Termwise mass bound: for every X, the log-weighted mass of twin prime pairs n and n+2 inside the strict window X below n below 51X over 50 is at most the sum over the same window of the product of vonMangoldt at n and at n+2.
-- Refinement: once the power error is known to vanish (the second premise of the first cut, now a verified module), the parent reduces to the positive-mass premise and this termwise bound.

theorem Conjectures.Cuts.Cut43fe36ae4bfc352af14b3625
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ c * (X:ℝ) ≤
      ∑ n ∈ Finset.range (2*X+1),
        if X < n ∧ 50*n < 51*X ∧ Nat.Prime n ∧ Nat.Prime (n+2) then
          Real.log (n:ℝ) * Real.log ((n+2 : ℕ) : ℝ)
        else 0)
    (h₂ : ∀ X : ℕ,
      (∑ n ∈ Finset.range (2*X+1),
        if X < n ∧ 50*n < 51*X ∧ Nat.Prime n ∧ Nat.Prime (n+2) then
          Real.log (n:ℝ) * Real.log ((n+2 : ℕ) : ℝ)
        else 0) ≤
      ∑ n ∈ (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X),
        ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)) :
    (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let M := fun (X : ℕ) => (w X).sum v / (X : ℝ); let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X) := by
  intro w v M e K B
  obtain ⟨c, hc0, hc⟩ := h₁
  have hmax : (1 : ℝ) ≤ max (1 : ℝ) |K| := le_max_left _ _
  have hmaxpos : (0 : ℝ) < 2 * max (1 : ℝ) |K| := by linarith
  -- the power error vanishes: the verified module for the second premise of the first cut
  obtain ⟨X₀, hX₀⟩ := Conjectures.Cuts.Taskc7173c36e2211fc2c80c5b0e (c / (2 * max (1 : ℝ) |K|)) (div_pos hc0 hmaxpos)
  obtain ⟨X, hBX, hXc⟩ := hc (max B X₀)
  have hmax0 : (0 : ℕ) ≤ max B X₀ := Nat.zero_le _
  have hXpos : 0 < X := by omega
  have hXR : (0 : ℝ) < X := Nat.cast_pos.mpr hXpos
  refine ⟨X, lt_of_le_of_lt (le_max_left B X₀) hBX, ?_⟩
  show K * (Real.log (2 + (X:ℝ))^3 / Real.sqrt (X:ℝ)) <
    ((Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)).sum
      (fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)) / (X : ℝ)
  -- the positive mass is bounded by the window mean through the termwise bound
  have hMX : c * (X:ℝ) ≤
      ((Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)).sum
        (fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)) :=
    le_trans hXc (h₂ X)
  -- beyond X₀ the error term is small compared with c
  have hX₀X := hX₀ X (le_of_lt (lt_of_le_of_lt (le_max_right B X₀) hBX))
  have habs : |K| ≤ max (1 : ℝ) |K| := le_max_right _ _
  have hlog : (0 : ℝ) < Real.log (2 + (X:ℝ)) := Real.log_pos (by linarith)
  have hepos : 0 ≤ Real.log (2 + (X:ℝ))^3 / Real.sqrt (X:ℝ) :=
    div_nonneg (pow_nonneg hlog.le 3) (Real.sqrt_nonneg _)
  have h1 : K * (Real.log (2 + (X:ℝ))^3 / Real.sqrt (X:ℝ)) ≤
      |K| * (Real.log (2 + (X:ℝ))^3 / Real.sqrt (X:ℝ)) :=
    mul_le_mul_of_nonneg_right (le_abs_self K) hepos
  have h2 : |K| * (Real.log (2 + (X:ℝ))^3 / Real.sqrt (X:ℝ)) ≤
      |K| * (c / (2 * max (1 : ℝ) |K|)) :=
    mul_le_mul_of_nonneg_left hX₀X.le (abs_nonneg K)
  have hkey : |K| / (2 * max (1 : ℝ) |K|) ≤ 1 / 2 := by
    rw [div_le_iff₀ hmaxpos]
    nlinarith
  have h3 : |K| * (c / (2 * max (1 : ℝ) |K|)) ≤ c / 2 := by
    have hring : |K| * (c / (2 * max (1 : ℝ) |K|)) = c * (|K| / (2 * max (1 : ℝ) |K|)) := by ring
    rw [hring]
    exact le_trans (mul_le_mul_of_nonneg_left hkey hc0.le) (le_of_eq (by ring))
  have hMXdiv : c ≤
      ((Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)).sum
        (fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)) / (X : ℝ) :=
    (le_div_iff₀ hXR).mpr hMX
  linarith
