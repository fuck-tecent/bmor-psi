import Mathlib

-- child 1 zh: 只对特殊的互素三元组证明指数 15/8 的高度上界：和与较大加数分别有平方因子 t²、u²，满足 t³⁰>(a+b)⁷、u³⁰>max(a,b)⁷。
-- child 1 en: Bound the logarithmic sum height at exponent 15/8 for coprime triples whose sum and larger summand each contain a square divisor with fifteenth power exceeding the seventh power of its host.
-- child 2 zh: 若正整数 n 的每个平方因子 t² 都满足 t³⁰≤n⁷，那么对 n 的任何正倍数 N，log n 至多为 15/8 倍 log rad(N)。
-- child 2 en: If every square divisor t² of n satisfies t³⁰ ≤ n⁷, then log n is at most 15/8 times the log radical of each positive multiple N of n.

theorem Conjectures.Cuts.Cut7740e8bb112b61d3b67b42f6
    (hHard : ∃ K : ℝ, ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
      (∃ t : ℕ, t^2 ∣ (a+b) ∧ (a+b)^7 < t^30) →
      (∃ u : ℕ, u^2 ∣ max a b ∧ (max a b)^7 < u^30) →
      Real.log ((a+b : ℕ):ℝ) ≤ (15/8 : ℝ) *
        Real.log (((a*b*(a+b)).primeFactors.prod id : ℕ):ℝ) + K)
    (hEasy : ∀ n N : ℕ, 0 < n → 0 < N → n ∣ N →
      (∀ t : ℕ, t^2 ∣ n → t^30 ≤ n^7) →
      Real.log (n:ℝ) ≤ (15/8 : ℝ) * Real.log ((N.primeFactors.prod id : ℕ):ℝ)) :
    (let rad := fun (n : ℕ) => n.primeFactors.prod id; let r := fun (a b : ℕ) => Real.log (rad (a*b*(a+b))); ∃ K : ℝ, ∀ a b : ℕ, 0<a → 0<b → Nat.Coprime a b → Real.log (16*((a:ℝ)^2+a*b+(b:ℝ)^2))/2 ≤ (15/8 : ℝ)*r a b+K) := by
  classical
  obtain ⟨K, hSparse⟩ := hHard
  dsimp only
  refine ⟨Real.log 4 + max K (Real.log 2), ?_⟩
  intro a b ha hb hCop
  let c := a+b
  let m := max a b
  let N := a*b*c
  let R : ℝ := (15/8 : ℝ) * Real.log ((N.primeFactors.prod id : ℕ):ℝ)
  have hc : 0 < c := by dsimp [c]; omega
  have hm : 0 < m := lt_of_lt_of_le ha (le_max_left _ _)
  have hN : 0 < N := Nat.mul_pos (Nat.mul_pos ha hb) hc
  have hcD : c ∣ N := dvd_mul_left c (a*b)
  have hmD : m ∣ N := by
    apply dvd_trans _ (dvd_mul_right (a*b) c)
    rcases le_total a b with h|h
    · dsimp [m]; rw [max_eq_right h]; exact dvd_mul_left b a
    · dsimp [m]; rw [max_eq_left h]; exact dvd_mul_right a b
  have hcR : 0 < (c:ℝ) := by exact_mod_cast hc
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have haR : 0 < (a:ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b:ℝ) := by exact_mod_cast hb
  have hF : Real.log (16 * ((a:ℝ)^2 + a*b + (b:ℝ)^2)) / 2 ≤
      Real.log 4 + Real.log (c:ℝ) := by
    have hEq : (c:ℝ) = a+b := by simp [c]
    have hsq : 16 * ((a:ℝ)^2+a*b+(b:ℝ)^2) ≤ (4*(c:ℝ))^2 := by
      rw [hEq]; nlinarith [mul_nonneg haR.le hbR.le]
    have h := Real.log_le_log (by positivity) hsq
    rw [Real.log_pow, Real.log_mul (by norm_num) hcR.ne'] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have hCm : Real.log (c:ℝ) ≤ Real.log 2 + Real.log (m:ℝ) := by
    have hle : c ≤ 2*m := by
      have := le_max_left a b; have := le_max_right a b; dsimp [c,m]; omega
    have hleR : (c:ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast hle
    have h := Real.log_le_log hcR hleR
    rwa [Real.log_mul (by norm_num) hmR.ne'] at h
  have hC : Real.log (c:ℝ) ≤ R + max K (Real.log 2) := by
    by_cases hHeavyC : ∃ t : ℕ, t^2 ∣ c ∧ c^7 < t^30
    · by_cases hHeavyM : ∃ t : ℕ, t^2 ∣ m ∧ m^7 < t^30
      · exact (hSparse a b ha hb hCop hHeavyC hHeavyM).trans
          (add_le_add (show R ≤ R from le_rfl) (le_max_left K (Real.log 2)))
      · have hLight : ∀ t : ℕ, t^2 ∣ m → t^30 ≤ m^7 := by
          intro t ht; exact le_of_not_gt (fun h => hHeavyM ⟨t,ht,h⟩)
        have hmBound : Real.log (m:ℝ) ≤ R := hEasy m N hm hN hmD hLight
        linarith only [hCm,hmBound,le_max_right K (Real.log 2)]
    · have hLight : ∀ t : ℕ, t^2 ∣ c → t^30 ≤ c^7 := by
        intro t ht; exact le_of_not_gt (fun h => hHeavyC ⟨t,ht,h⟩)
      have hcBound : Real.log (c:ℝ) ≤ R := hEasy c N hc hN hcD hLight
      linarith only [hcBound,le_max_right K (Real.log 2),Real.log_pos (by norm_num : (1:ℝ)<2)]
  change Real.log (16 * ((a:ℝ)^2 + a*b + (b:ℝ)^2)) / 2 ≤
    R + (Real.log 4 + max K (Real.log 2))
  linarith only [hF,hC]
