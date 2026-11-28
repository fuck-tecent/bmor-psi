import Mathlib

-- child 1 zh: 高质量有序三元组的乘积型弱 abc 界：存在 B > 1、K > 0 与阈值 N，使所有满足 0 < a < b、互素、a + b ≥ N 且 rad(ab(a+b)) < a + b 的三元组满足 a + b ≤ K · rad(ab(a+b))^B。
-- child 1 en: Multiplicative weak abc bound on ordered high-quality triples: there exist B > 1, K > 0, and a threshold N such that every coprime pair with 0 < a < b, a + b ≥ N, and rad(ab(a+b)) < a + b satisfies a + b ≤ K · rad(ab(a+b))^B.
-- child 2 zh: 边界与高根基三元组的对数界：对任意 B > 1 与阈值 N，存在常数 C₀，使所有满足 a + b < N、a = b 或 a + b ≤ rad(ab(a+b)) 的正互素对均满足 log(a + b) ≤ B · log(rad(ab(a+b))) + C₀。
-- child 2 en: Logarithmic bound on boundary and high-radical triples: for every B > 1 and threshold N there exists C₀ such that every positive coprime pair with a + b < N, a = b, or a + b ≤ rad(ab(a+b)) satisfies log(a + b) ≤ B · log(rad(ab(a+b))) + C₀.

theorem Conjectures.Cuts.Cut82bea810e5eb0bd7d1155793
    (h_high_quality :
      ∃ B K : ℝ, 1 < B ∧ 0 < K ∧ ∃ N : ℕ, ∀ a b : ℕ,
        0 < a → a < b → Nat.Coprime a b → N ≤ a + b →
        (a * b * (a + b)).primeFactors.prod id < a + b →
        ((a : ℝ) + b) ≤ K * (((a * b * (a + b)).primeFactors.prod id : ℕ) : ℝ) ^ B)
    (h_boundary :
      ∀ B : ℝ, 1 < B → ∀ N : ℕ, ∃ C₀ : ℝ, ∀ a b : ℕ,
        0 < a → 0 < b → Nat.Coprime a b →
        (a + b < N ∨ a = b ∨ a + b ≤ (a * b * (a + b)).primeFactors.prod id) →
        Real.log ((a : ℝ) + b) ≤ B * Real.log (((a * b * (a + b)).primeFactors.prod id : ℕ) : ℝ) + C₀) :
    (let rad := fun (n : ℕ) => n.primeFactors.prod id; let h := fun (a b : ℕ) => Real.log ((a:ℝ)+b); let r := fun (a b : ℕ) => Real.log (rad (a*b*(a+b))); ∃ B C : ℝ, 1 < B ∧ ∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → h a b ≤ B*r a b+C) := by
  dsimp only
  obtain ⟨B, K, hB, hK, N, hMain⟩ := h_high_quality
  obtain ⟨C₀, hBnd⟩ := h_boundary B hB N
  refine ⟨B, max C₀ (Real.log K), hB, ?_⟩
  -- 辅助引理：对满足高质量与顺序条件的三元组，由乘积幂次上界取对数得到对数型上界
  have hlog_of_prod : ∀ x y : ℕ, 0 < x → x < y → Nat.Coprime x y → N ≤ x + y →
      (x * y * (x + y)).primeFactors.prod id < x + y →
      Real.log ((x : ℝ) + y) ≤
        B * Real.log (((x * y * (x + y)).primeFactors.prod id : ℕ) : ℝ) + Real.log K := by
    intro x y hx hxy hcop hN hrad
    have hprod := hMain x y hx hxy hcop hN hrad
    have hsum_pos : (0 : ℝ) < (x : ℝ) + y := by positivity
    have hrad_nat_pos : 0 < (x * y * (x + y)).primeFactors.prod id :=
      Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    have hrad_pos : (0 : ℝ) < (((x * y * (x + y)).primeFactors.prod id : ℕ) : ℝ) := by
      exact_mod_cast hrad_nat_pos
    have hrpow_pos : (0 : ℝ) < (((x * y * (x + y)).primeFactors.prod id : ℕ) : ℝ) ^ B :=
      Real.rpow_pos_of_pos hrad_pos B
    have hle := Real.log_le_log hsum_pos hprod
    rw [Real.log_mul hK.ne' hrpow_pos.ne', Real.log_rpow hrad_pos] at hle
    linarith
  intro a b ha hb hcop
  by_cases hcase : a + b < N ∨ a = b ∨ a + b ≤ (a * b * (a + b)).primeFactors.prod id
  · -- 边界或高 radical 情况直接由前提 2 给出
    have h1 := hBnd a b ha hb hcop hcase
    have hC : C₀ ≤ max C₀ (Real.log K) := le_max_left _ _
    linarith
  · -- 剩余为高质量且 a ≠ b 的大三元组，按对称性归约到 x < y
    push_neg at hcase
    rcases hcase with ⟨hN, hne, hrad⟩
    have hC : Real.log K ≤ max C₀ (Real.log K) := le_max_right _ _
    rcases lt_or_gt_of_ne hne with hab | hba
    · have h1 := hlog_of_prod a b ha hab hcop hN hrad
      linarith
    · have hsum_eq : b + a = a + b := Nat.add_comm b a
      have hprod_eq : b * a * (b + a) = a * b * (a + b) := by ring
      have hN' : N ≤ b + a := by omega
      have hrad' : (b * a * (b + a)).primeFactors.prod id < b + a := by
        rw [hprod_eq, hsum_eq]
        exact hrad
      have h1 := hlog_of_prod b a hb hba hcop.symm hN' hrad'
      have hcast : (b : ℝ) + (a : ℝ) = (a : ℝ) + (b : ℝ) := add_comm (b : ℝ) (a : ℝ)
      rw [hcast, hprod_eq] at h1
      linarith
