import Mathlib

/-!
# Cut: two-piece reduction of `L-goldbach-fixed-ap-bmor-psi`

`child 1` is the window obligation `8·10⁹ ≤ n ≤ 10¹² ⟹ |E(n)| ≤ 4√n + log n`
(square-root strength: verified zero tables inside a GRH height plus an
explicit-formula truncation). `child 2` is the tail obligation
`n ≥ 10¹² ⟹ |E(n)| ≤ n/(3360 log n)` (zero-free region plus the
explicit-formula remainder). The arithmetic inequality
`4√x + log x ≤ x/(840 log x)` for `x ≥ 8·10⁹` is proved inside the proof.
-/

-- child 1 zh: 窗口段：8·10⁹ ≤ n ≤ 10¹² 时，误差不超过 4√n + log n（√n 强度；由已验证零点表 + 显式公式截断给出）。
-- child 1 en: Window: for 8e9 <= n <= 1e12 the error is at most 4*sqrt(n) + log(n); square-root strength, from verified zero tables inside a GRH height plus an explicit-formula truncation.
-- child 2 zh: 尾段：n ≥ 10¹² 时，误差不超过 n/(3360 log n)（解析尾界：零自由区 + 显式公式余项）。
-- child 2 en: Tail: for n >= 1e12 the error is at most n/(3360 log n); analytic tail from a zero-free region plus the explicit-formula remainder.
theorem Conjectures.Cuts.Cut1d7e7d503260df5e7cceb957
    (h₁ : ∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q →
      8000000000 ≤ n → n ≤ 10 ^ 12 →
        |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
          ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q|
          ≤ 4 * Real.sqrt (n : ℝ) + Real.log (n : ℝ))
    (h₂ : ∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q →
      10 ^ 12 ≤ n →
        |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
          ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q|
          ≤ (n : ℝ) / (3360 * Real.log (n : ℝ))) :
    (∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 8000000000 ≤ n →
      |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
        ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q|
        ≤ (n:ℝ)/(840 * Real.log (n:ℝ))) := by
  -- Arithmetic: `8·10⁹ ≤ x ⟹ 89442 ≤ √x`.
  have sqrt_ge : ∀ {x : ℝ}, 8 * 10 ^ 9 ≤ x → 89442 ≤ Real.sqrt x := by
    intro x hx
    have hsq : (89442 : ℝ) ^ 2 ≤ 8000000000 := by norm_num
    have h2 : (89442 : ℝ) ≤ Real.sqrt 8000000000 := by
      calc (89442 : ℝ) = Real.sqrt ((89442 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt 8000000000 := Real.sqrt_le_sqrt hsq
    have hx' : (8000000000 : ℝ) ≤ x := by
      norm_num at hx
      linarith
    calc (89442 : ℝ) ≤ Real.sqrt 8000000000 := h2
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx'
  -- Arithmetic: `s ≥ 89442 ⟹ log s ≤ s/7000`.
  have log_le_div : ∀ {s : ℝ}, 89442 ≤ s → Real.log s ≤ s / 7000 := by
    intro s hs
    have hs0 : (0 : ℝ) < s := by linarith
    have h89442 : (0 : ℝ) < 89442 := by norm_num
    have hsplit : Real.log s = Real.log 89442 + Real.log (s / 89442) := by
      rw [← Real.log_mul h89442.ne' (ne_of_gt (by positivity : (0 : ℝ) < s / 89442))]
      congr 1
      field_simp
    have hlog_div : Real.log (s / 89442) ≤ s / 89442 - 1 := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < s / 89442)
      linarith
    have hlog89442 : Real.log 89442 ≤ 12 := by
      rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 89442)]
      have h1 : (2.7 : ℝ) ^ 12 ≤ Real.exp 12 := by
        rw [show Real.exp 12 = Real.exp 1 ^ 12 by rw [← Real.exp_nat_mul]; norm_num]
        exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7)
          (le_of_lt (by linarith [Real.exp_one_gt_d9] : (2.7 : ℝ) < Real.exp 1)) 12
      have h2 : (89442 : ℝ) ≤ (2.7 : ℝ) ^ 12 := by norm_num
      linarith
    have hkey : Real.log s ≤ 11 + s / 89442 := by
      rw [hsplit]; linarith
    have hfin : 11 + s / 89442 ≤ s / 7000 := by
      have hcoef : (0 : ℝ) < 1 / 7000 - 1 / 89442 := by norm_num
      have hle : (11 : ℝ) ≤ 89442 * (1 / 7000 - 1 / 89442) := by norm_num
      have hmono : (89442 : ℝ) * (1 / 7000 - 1 / 89442)
          ≤ s * (1 / 7000 - 1 / 89442) :=
        mul_le_mul_of_nonneg_right hs hcoef.le
      have heq : s * (1 / 7000 - 1 / 89442) = s / 7000 - s / 89442 := by
        field_simp
      linarith
    linarith
  -- Arithmetic: the budget inequality `4√x + log x ≤ x/(840 log x)`.
  have budget_slack : ∀ {x : ℝ}, 8 * 10 ^ 9 ≤ x →
      4 * Real.sqrt x + Real.log x ≤ x / (840 * Real.log x) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith
    set s : ℝ := Real.sqrt x with hs_def
    have hs : 89442 ≤ s := sqrt_ge hx
    have hs0 : (0 : ℝ) < s := by linarith
    have hxs : x = s ^ 2 := by rw [hs_def, Real.sq_sqrt hx0.le]
    have hlogx : Real.log x = 2 * Real.log s := by
      rw [hxs, Real.log_pow]; push_cast; ring
    have hlogs1 : (1 : ℝ) ≤ Real.log s := by
      have he : Real.exp 1 ≤ 89442 := by
        nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
      have h1 : Real.log (Real.exp 1) ≤ Real.log 89442 := Real.log_le_log (Real.exp_pos 1) he
      rw [Real.log_exp] at h1
      exact le_trans h1 (Real.log_le_log (by norm_num) hs)
    have hlogs0 : (0 : ℝ) < Real.log s := by linarith
    have hlogs2 : Real.log s ≤ s / 7000 := log_le_div hs
    rw [hlogx, hxs]
    have hleft : 4 * s + 2 * Real.log s ≤ s * (4 + 1 / 3500) := by
      nlinarith [hlogs2]
    have hright : s * (4 + 1 / 3500) ≤ s ^ 2 / (840 * (2 * Real.log s)) := by
      rw [le_div_iff₀ (by positivity)]
      have h3 : 840 * (2 * Real.log s) ≤ 840 * (2 * (s / 7000)) := by nlinarith [hlogs2]
      have h4 : (0 : ℝ) ≤ s * (4 + 1 / 3500) := by positivity
      calc s * (4 + 1 / 3500) * (840 * (2 * Real.log s))
          ≤ s * (4 + 1 / 3500) * (840 * (2 * (s / 7000))) :=
            mul_le_mul_of_nonneg_left h3 h4
        _ ≤ s ^ 2 := by nlinarith [hs0]
    calc 4 * s + 2 * Real.log s ≤ s * (4 + 1 / 3500) := hleft
      _ ≤ s ^ 2 / (840 * (2 * Real.log s)) := hright
  -- Combination.
  intro q a n hq hq' ha hcop hn
  have hlogn : (0 : ℝ) < Real.log (n : ℝ) := by
    have hn1 : (1 : ℝ) < (n : ℝ) := by
      have : (8000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact Real.log_pos hn1
  by_cases hle : n ≤ 10 ^ 12
  · have hw := h₁ q a n hq hq' ha hcop hn hle
    have hb := budget_slack (x := (n : ℝ)) (by
      have : (8000000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      norm_num
      linarith)
    exact hw.trans hb
  · have hge : 10 ^ 12 ≤ n := by omega
    have ht := h₂ q a n hq hq' ha hcop hge
    have hmono : (n : ℝ) / (3360 * Real.log (n : ℝ))
        ≤ (n : ℝ) / (840 * Real.log (n : ℝ)) := by
      apply div_le_div_of_nonneg_left (by positivity)
      · have : (0 : ℝ) < Real.log (n : ℝ) := hlogn
        positivity
      · nlinarith [hlogn]
    exact ht.trans hmono
