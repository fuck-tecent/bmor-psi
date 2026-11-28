import Mathlib
open ArithmeticFunction Finset

-- child 1 zh: 反向陈氏筛的粗糙候选集计数最终至少为 X/log²X 的一个固定正倍数。
-- child 1 en: The reverse rough candidate set eventually has size at least a positive multiple of X/log²X.
-- child 2 zh: 在同一粗糙候选集中，两个不同素数的乘积最终至少占固定正比例。
-- child 2 en: Products of two distinct primes eventually make up a positive fraction of the same rough candidate set.
-- child 3 zh: 二阶塞尔伯格权乘以莫比乌斯函数平方，逐点等于不同素因子的有序对数质量加上素数质量。
-- child 3 en: Pointwise, the squared Möbius factor times the second Selberg weight splits into the ordered distinct-prime-pair mass and the prime mass.
theorem Conjectures.Cuts.Cutcabf71b71c0728719c30ca82
    (hCount : have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range (x1 + (1 : ℕ)) | (1 : ℕ) < x2 ∧ Nat.Prime (x2 + (2 : ℕ)) ∧ ∀ x3 ∈ x2.divisors, Nat.Prime x3 → x1 ≤ x3 ^ (10 : ℕ)}; ∃ (x2 : ℝ), (0 : ℝ) < x2 ∧ ∃ (x3 : ℕ), ∀ (x4 : ℕ), x3 ≤ x4 → x2 * ↑x4 ≤ ↑(x1 x4).card * Real.log ↑x4 ^ (2 : ℕ))
    (hFraction :
      let R : ℕ → Finset ℕ := fun X =>
        {n ∈ range (X+1) | 1 < n ∧ (n+2).Prime ∧
          ∀ p ∈ n.divisors, p.Prime → X ≤ p^10}
      ∃ δ : ℝ, 0 < δ ∧ ∃ X₁ : ℕ, ∀ X : ℕ, X₁ ≤ X →
        δ * ((R X).card : ℝ) ≤ (((R X).filter (fun n =>
          ∃ p ∈ n.divisors, p.Prime ∧ (n/p).Prime ∧ p ≠ n/p)).card : ℝ))
    (hSplit : ∀ (x1 : ℕ), ↑(ArithmeticFunction.moebius x1) ^ (2 : ℕ) * (ArithmeticFunction.vonMangoldt x1 * Real.log ↑x1 + ∑ x2 ∈ x1.divisors, ArithmeticFunction.vonMangoldt x2 * ArithmeticFunction.vonMangoldt (x1 / x2)) = ∑ x2 ∈ x1.divisors with Nat.Prime x2 ∧ Nat.Prime (x1 / x2) ∧ x2 ≠ x1 / x2, Real.log ↑x2 * Real.log ↑(x1 / x2) + if Nat.Prime x1 then Real.log ↑x1 ^ (2 : ℕ) else (0 : ℝ)) :
    ∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∃ (x2 : ℕ), ∀ (x3 : ℕ), x2 ≤ x3 → x1 * ↑x3 * Real.log ↑x3 ≤ ∑ x5 ∈ Finset.range (x3 + (1 : ℕ)) with ∃ x6 ∈ x5.divisors, Nat.Prime x6 ∧ Nat.Prime (x5 / x6) ∧ x6 ≠ x5 / x6, ↑(ArithmeticFunction.moebius x5) ^ (2 : ℕ) * (ArithmeticFunction.vonMangoldt x5 * Real.log ↑x5 + ∑ x6 ∈ x5.divisors, ArithmeticFunction.vonMangoldt x6 * ArithmeticFunction.vonMangoldt (x5 / x6)) * if Nat.Prime (x5 + (2 : ℕ)) then Real.log (↑x5 + (2 : ℝ)) else (0 : ℝ) := by
  classical
  let R : ℕ → Finset ℕ := fun X =>
    {n ∈ range (X+1) | 1 < n ∧ (n+2).Prime ∧ ∀ p ∈ n.divisors, p.Prime → X ≤ p^10}
  let semi (n : ℕ) := ∃ p ∈ n.divisors, p.Prime ∧ (n/p).Prime ∧ p ≠ n/p
  obtain ⟨c, hc, X₀, hCount⟩ := hCount
  obtain ⟨δ, hδ, X₁, hFraction⟩ := hFraction
  refine ⟨(δ*c)/1000, by positivity, max (max X₀ X₁) 2, ?_⟩
  intro X hX
  have h2 : 2 ≤ X := (le_max_right (max X₀ X₁) 2).trans hX
  have hTime : max X₀ X₁ ≤ X := (le_max_left (max X₀ X₁) 2).trans hX
  let L := Real.log (X : ℝ)
  let G := (R X).filter semi
  let T := (range (X+1)).filter semi
  let W (n : ℕ) := ((moebius n : ℤ) : ℝ)^2 *
    (vonMangoldt n * Real.log (n : ℝ) +
      ∑ d ∈ n.divisors, vonMangoldt d * vonMangoldt (n/d))
  let w (n : ℕ) := W n * if (n+2).Prime then Real.log ((n : ℝ)+2) else 0
  have logNat (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
    by_cases h : n = 0
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h)
  have hw (n : ℕ) : 0 ≤ w n := by
    dsimp only [w,W]
    apply mul_nonneg (mul_nonneg (sq_nonneg _)
      (add_nonneg (mul_nonneg vonMangoldt_nonneg (logNat n))
        (sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)))
    split_ifs
    · exact Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
    · rfl
  have sub : G ⊆ T := by
    intro n hn
    obtain ⟨hr, ha⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨(mem_filter.mp hr).1,ha⟩
  have hLX : 0 ≤ L := logNat X
  have hLP : 0 ≤ L/10 := by positivity
  have logPower (p : ℕ) (h : X ≤ p^10) : L/10 ≤ Real.log (p : ℝ) := by
    have xpos : (0 : ℝ) < X := Nat.cast_pos.mpr (by omega)
    have powBound : (X : ℝ) ≤ (p : ℝ)^10 := by exact_mod_cast h
    have logBound := Real.log_le_log xpos powBound
    rw [Real.log_pow] at logBound
    dsimp only [L]
    norm_num at logBound
    linarith only [logBound]
  have point (n : ℕ) (hn : n ∈ G) : (L/10)^3 ≤ w n := by
    obtain ⟨hnR, hSemi⟩ := mem_filter.mp hn
    obtain ⟨_,hn1,hShift,hRough⟩ := mem_filter.mp hnR
    obtain ⟨p,hpD,hp,hq,hne⟩ := hSemi
    have hpdvd := Nat.dvd_of_mem_divisors hpD
    have hqD : n/p ∈ n.divisors :=
      Nat.mem_divisors.mpr ⟨⟨p,(Nat.div_mul_cancel hpdvd).symm⟩, by omega⟩
    have lp := logPower p (hRough p hpD hp)
    have lq := logPower (n/p) (hRough (n/p) hqD hq)
    have pLe : (p:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.divisor_le hpD
    have ls := lp.trans (Real.log_le_log (Nat.cast_pos.mpr hp.pos)
      (by linarith only [pLe] : (p:ℝ) ≤ (n:ℝ)+2))
    let D := n.divisors.filter (fun d => d.Prime ∧ (n/d).Prime ∧ d ≠ n/d)
    have pIn : p ∈ D := mem_filter.mpr ⟨hpD,hp,hq,hne⟩
    have single := single_le_sum (f := fun d : ℕ => Real.log (d : ℝ) * Real.log ((n/d : ℕ) : ℝ))
      (fun d _ => mul_nonneg (logNat d) (logNat (n/d))) pIn
    have divided : W n = (∑ d ∈ D, Real.log (d:ℝ) * Real.log ((n/d:ℕ):ℝ)) +
        (if n.Prime then Real.log (n:ℝ)^2 else 0) := hSplit n
    have lW : (L/10)^2 ≤ W n := calc
      _ = (L/10)*(L/10) := by ring
      _ ≤ Real.log (p:ℝ)*Real.log ((n/p:ℕ):ℝ) := mul_le_mul lp lq hLP (logNat p)
      _ ≤ ∑ d ∈ D, Real.log (d:ℝ)*Real.log ((n/d:ℕ):ℝ) := single
      _ ≤ W n := by rw [divided]; apply le_add_of_nonneg_right; split_ifs <;> positivity
    change (L/10)^3 ≤ W n * (if (n+2).Prime then Real.log ((n:ℝ)+2) else 0)
    rw [ite_eq_left hShift, pow_succ]
    exact mul_le_mul lW ls hLP ((sq_nonneg _).trans lW)
  have hRaw : c*(X:ℝ) ≤ ((R X).card:ℝ)*L^2 := hCount X ((le_max_left X₀ X₁).trans hTime)
  have hFrac : δ*((R X).card:ℝ) ≤ (G.card:ℝ) := hFraction X ((le_max_right X₀ X₁).trans hTime)
  have hMass : (δ*c)*(X:ℝ) ≤ (G.card:ℝ)*L^2 := calc
    _ = δ*(c*(X:ℝ)) := by ring
    _ ≤ δ*(((R X).card:ℝ)*L^2) := mul_le_mul_of_nonneg_left hRaw hδ.le
    _ = (δ*((R X).card:ℝ))*L^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hFrac (sq_nonneg _)
  change (δ*c)/1000*(X:ℝ)*L ≤ ∑ n ∈ T, w n
  calc
    _ = ((δ*c)*(X:ℝ))*(L/1000) := by ring
    _ ≤ ((G.card:ℝ)*L^2)*(L/1000) := mul_le_mul_of_nonneg_right hMass (by positivity)
    _ = (G.card:ℝ)*(L/10)^3 := by ring
    _ = ∑ _ ∈ G, (L/10)^3 := by rw [sum_const,nsmul_eq_mul]
    _ ≤ ∑ n ∈ G, w n := sum_le_sum point
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub fun n _ _ => hw n
