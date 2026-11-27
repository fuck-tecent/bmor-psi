import Mathlib
import Conjectures.TwinPrimes.SharpWindowContamination

-- child 1 zh: 正质量下界（沿无界的严格窗）：存在常数 c 大于 0，使得对每个起点 B 都存在 X 大于 B，窗口 X 小于 n 小于 51X 之 50 内孪生素数对 n 与 n+2 的对数权质量至少为 c 倍 X。
-- child 1 en: Positive mass on unbounded strict windows: some constant c above 0 with, for every bound B, an X above B whose log-weighted mass of twin prime pairs n and n+2 inside the window X below n below 51X over 50 is at least c times X.
-- child 2 zh: 误差项消失：log(2+X) 的三次方除以 X 的平方根最终小于任意给定的正数。
-- child 2 en: The power error vanishes: the cube of log(2+X) divided by the square root of X is eventually below every given positive number.

theorem Conjectures.Cuts.Cut0327400533ee1e3258f44584
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ c * (X:ℝ) ≤
      ∑ n ∈ Finset.range (2*X+1),
        if X < n ∧ 50*n < 51*X ∧ Nat.Prime n ∧ Nat.Prime (n+2) then
          Real.log (n:ℝ) * Real.log ((n+2 : ℕ) : ℝ)
        else 0)
    (h₂ : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → Real.log (2+(X:ℝ))^3 / Real.sqrt (X:ℝ) < ε) :
    (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let M := fun (X : ℕ) => (w X).sum v / (X : ℝ); let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X) := by
  intro w v M e K B
  obtain ⟨c, hc0, hc⟩ := h₁
  have hmax : (1 : ℝ) ≤ max (1 : ℝ) |K| := le_max_left _ _
  have hmaxpos : (0 : ℝ) < 2 * max (1 : ℝ) |K| := by linarith
  obtain ⟨X₀, hX₀⟩ := h₂ (c / (2 * max (1 : ℝ) |K|)) (div_pos hc0 hmaxpos)
  obtain ⟨X, hBX, hXc⟩ := hc (max B X₀)
  have hmax0 : (0 : ℕ) ≤ max B X₀ := Nat.zero_le _
  have hXpos : 0 < X := by omega
  have hXR : (0 : ℝ) < X := Nat.cast_pos.mpr hXpos
  refine ⟨X, lt_of_le_of_lt (le_max_left B X₀) hBX, ?_⟩
  show K * (Real.log (2 + (X:ℝ))^3 / Real.sqrt (X:ℝ)) <
    ((Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)).sum
      (fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)) / (X : ℝ)
  -- termwise: on the window the pair weight of Λ is at least the twin-prime log weight
  have hterm : ∀ n ∈ (Finset.range (2*X+1)),
      (if X < n ∧ 50*n < 51*X ∧ Nat.Prime n ∧ Nat.Prime (n+2) then
          Real.log (n:ℝ) * Real.log ((n+2 : ℕ) : ℝ)
        else 0) ≤
      (if X < n ∧ 50*n < 51*X then
          ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)
        else 0) := by
    intro n _
    by_cases hw : X < n ∧ 50*n < 51*X
    · by_cases hp : Nat.Prime n ∧ Nat.Prime (n+2)
      · have hwp : X < n ∧ 50*n < 51*X ∧ Nat.Prime n ∧ Nat.Prime (n+2) :=
          ⟨hw.1, hw.2, hp.1, hp.2⟩
        rw [if_pos hw, if_pos hwp, ArithmeticFunction.vonMangoldt_apply_prime hp.1,
          ArithmeticFunction.vonMangoldt_apply_prime hp.2]
      · rw [if_pos hw, if_neg (fun h => hp h.2.2)]
        exact mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg) (ArithmeticFunction.vonMangoldt_nonneg)
    · have hnot : ¬ (X < n ∧ 50*n < 51*X ∧ Nat.Prime n ∧ Nat.Prime (n+2)) := fun h => hw ⟨h.1, h.2.1⟩
      rw [if_neg hnot, if_neg hw]
  have hsum : (∑ n ∈ Finset.range (2*X+1),
        if X < n ∧ 50*n < 51*X ∧ Nat.Prime n ∧ Nat.Prime (n+2) then
          Real.log (n:ℝ) * Real.log ((n+2 : ℕ) : ℝ)
        else 0) ≤
      ((Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)).sum
        (fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)) := by
    rw [Finset.sum_filter]
    exact Finset.sum_le_sum hterm
  have hMX : c * (X:ℝ) ≤
      ((Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)).sum
        (fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)) :=
    le_trans hXc hsum
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
