import Mathlib

/-!
新路线 · Levent GRH 方法与自然推广 · 近等双素因子的计数上界

证明思路（conic parameter）：
设 `n^2+1 = p*q`，`p < q` 为素数，`q - p ≤ H`，`x < n`。记 `m = n - p`（`m ≥ 1`），
则 `(p+m)^2+1 = p*q = p*(p+(q-p))` 给出
`p * ((q-p) - 2*m) = m^2 + 1`，
即 `p ∣ m^2+1` 且 `2*m+1 ≤ q-p ≤ H`。又 `p = n - m ≥ x + 1 - m ≥ m + 2`。
于是映射 `n ↦ m = n - p` 在所计数的集合上是单射：同一 `m` 对应的两个不同素因子
`p₁ ≠ p₂` 都整除 `m^2+1` 且都 `≥ m+2`，故 `p₁*p₂ ∣ m^2+1`，但
`p₁*p₂ ≥ (m+2)^2 > m^2+1`，矛盾。
因此计数 `≤ #\{m : 1 ≤ m ≤ (H-1)/2\} = (H-1)/2 ≤ H`，取 `C = 1`。
-/

namespace Conjectures.QuadraticPrimes.NearEqualSemiprimeCount_aux

/-- Two distinct primes, both at least `m + 2`, cannot both divide `m ^ 2 + 1`. -/
lemma pair_bound (m p₁ p₂ : ℕ) (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂)
    (hd₁ : p₁ ∣ m ^ 2 + 1) (hd₂ : p₂ ∣ m ^ 2 + 1) (h₁ : m + 2 ≤ p₁) (h₂ : m + 2 ≤ p₂) :
    False := by
  have hcop : Nat.Coprime p₁ p₂ := by
    refine (Nat.Prime.coprime_iff_not_dvd hp₁).mpr ?_
    intro h
    exact hne ((Nat.Prime.dvd_iff_eq hp₂ (Nat.Prime.ne_one hp₁)).mp h).symm
  have hmul : p₁ * p₂ ∣ m ^ 2 + 1 := hcop.mul_dvd_of_dvd_of_dvd hd₁ hd₂
  have hle : p₁ * p₂ ≤ m ^ 2 + 1 := Nat.le_of_dvd (by positivity) hmul
  have hge : (m + 2) * (m + 2) ≤ p₁ * p₂ := Nat.mul_le_mul h₁ h₂
  have h : (m + 2) * (m + 2) ≤ m ^ 2 + 1 := hge.trans hle
  have hexp : (m + 2) * (m + 2) = m ^ 2 + 4 * m + 4 := by ring
  omega

/-- The conic parameter `m = n - p` of a near-equal factorisation `n ^ 2 + 1 = p * q`. -/
lemma facts (x H n p q : ℕ) (_hq : q.Prime) (hpq : p < q)
    (heq : n ^ 2 + 1 = p * q) (hgap : q - p ≤ H) (hH1 : 1 ≤ H) (hHx : H ≤ x) (hn : x < n) :
    p.Prime → 1 ≤ n - p ∧ 2 * (n - p) + 1 ≤ H ∧ p ∣ (n - p) ^ 2 + 1 ∧ (n - p) + 2 ≤ p := by
  intro hp
  have hn2 : 2 ≤ n := by omega
  have hp2 : p * p < n ^ 2 + 1 := by
    calc p * p < p * q := Nat.mul_lt_mul_of_pos_left hpq hp.pos
      _ = n ^ 2 + 1 := heq.symm
  have hpn : p ≤ n := by
    by_contra h
    have hpn' : n + 1 ≤ p := by omega
    have : (n + 1) * (n + 1) ≤ p * p := Nat.mul_le_mul hpn' hpn'
    have hexp : (n + 1) * (n + 1) = n ^ 2 + 2 * n + 1 := by ring
    omega
  have hpne : p ≠ n := by
    intro hpn'
    have hqn : n * q = n ^ 2 + 1 := by rw [heq, hpn']
    have hqq : n * n ≤ n * q := by
      calc n * n ≤ n ^ 2 + 1 := by rw [sq]; omega
        _ = n * q := hqn.symm
    have hqge : n ≤ q := Nat.le_of_mul_le_mul_left hqq (by omega)
    have h1 : n * (q - n) = 1 := by
      calc n * (q - n) = n * q - n * n := Nat.mul_sub n q n
        _ = n ^ 2 + 1 - n ^ 2 := by rw [hqn, sq]
        _ = 1 := by omega
    have hn1 : n ≤ 1 := Nat.le_of_dvd one_pos ⟨q - n, h1.symm⟩
    omega
  have hm : 1 ≤ n - p := by omega
  set m := n - p
  have hnm : n = p + m := by omega
  set d := q - p
  have hqd : q = p + d := (Nat.add_sub_of_le (le_of_lt hpq)).symm
  have key : p * d = 2 * p * m + m ^ 2 + 1 := by
    have hZ : (p : ℤ) * (d : ℤ) = 2 * (p : ℤ) * (m : ℤ) + (m : ℤ) ^ 2 + 1 := by
      have h : ((n : ℤ) ^ 2 + 1) = (p : ℤ) * (q : ℤ) := by exact_mod_cast heq
      have h1 : (n : ℤ) = (p : ℤ) + (m : ℤ) := by exact_mod_cast hnm
      have h2 : (q : ℤ) = (p : ℤ) + (d : ℤ) := by exact_mod_cast hqd
      rw [h1, h2] at h
      linarith
    exact_mod_cast hZ
  have hd2m : 2 * m + 1 ≤ d := by
    by_contra hlt
    have hlt' : d ≤ 2 * m := by omega
    have : p * d ≤ p * (2 * m) := Nat.mul_le_mul_left p hlt'
    have hpm : p * (2 * m) = 2 * p * m := by ring
    omega
  have hdvd : p ∣ m ^ 2 + 1 := by
    refine ⟨d - 2 * m, ?_⟩
    have h2 : p * (2 * m) = 2 * p * m := by ring
    calc m ^ 2 + 1 = (2 * p * m + m ^ 2 + 1) - 2 * p * m := by omega
      _ = p * d - p * (2 * m) := by rw [key, h2]
      _ = p * (d - 2 * m) := (Nat.mul_sub p d (2 * m)).symm
  have hgap' : 2 * m + 1 ≤ H := hd2m.trans hgap
  have hpm2 : m + 2 ≤ p := by omega
  exact ⟨hm, hgap', hdvd, hpm2⟩

/-- The counting bound: at most `H` integers `n > x` carry a near-equal factorisation. -/
lemma card_le (x H : ℕ) (hH1 : 1 ≤ H) (hHx : H ≤ x) (S : Finset ℕ)
    (hmem : ∀ n ∈ S, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n ^ 2 + 1 = p * q ∧ q - p ≤ H)
    (hlo : ∀ n ∈ S, x < n) : S.card ≤ H := by
  classical
  let f : ℕ → ℕ := fun n =>
    if h : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n ^ 2 + 1 = p * q ∧ q - p ≤ H then
      n - Classical.choose h else 0
  have hfmem : ∀ n ∈ S, f n ∈ Finset.Icc 1 ((H - 1) / 2) := by
    intro n hn
    have h := hmem n hn
    have hfn : f n = n - Classical.choose h := dite_eq_left h
    obtain ⟨q, hp, hq, hpq, heq, hgap⟩ := Classical.choose_spec h
    obtain ⟨hm, h2m, -, -⟩ := facts x H n (Classical.choose h) q hq hpq heq hgap hH1 hHx
      (hlo n hn) hp
    rw [hfn]
    refine Finset.mem_Icc.mpr ⟨hm, ?_⟩
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  have hinj : ∀ n₁ ∈ S, ∀ n₂ ∈ S, f n₁ = f n₂ → n₁ = n₂ := by
    intro n₁ hn₁ n₂ hn₂ hfeq
    have h1 := hmem n₁ hn₁
    have h2 := hmem n₂ hn₂
    have hf1 : f n₁ = n₁ - Classical.choose h1 := dite_eq_left h1
    have hf2 : f n₂ = n₂ - Classical.choose h2 := dite_eq_left h2
    obtain ⟨q₁, hp₁, hq₁, hpq₁, heq₁, hgap₁⟩ := Classical.choose_spec h1
    obtain ⟨q₂, hp₂, hq₂, hpq₂, heq₂, hgap₂⟩ := Classical.choose_spec h2
    obtain ⟨hm1, h2m1, hdvd1, hle1⟩ := facts x H n₁ (Classical.choose h1) q₁ hq₁ hpq₁ heq₁
      hgap₁ hH1 hHx (hlo n₁ hn₁) hp₁
    obtain ⟨hm2, h2m2, hdvd2, hle2⟩ := facts x H n₂ (Classical.choose h2) q₂ hq₂ hpq₂ heq₂
      hgap₂ hH1 hHx (hlo n₂ hn₂) hp₂
    have hsub : n₁ - Classical.choose h1 = n₂ - Classical.choose h2 := by
      rw [← hf1, ← hf2]; exact hfeq
    by_cases hp12 : Classical.choose h1 = Classical.choose h2
    · omega
    · exfalso
      refine pair_bound (n₁ - Classical.choose h1) (Classical.choose h1)
        (Classical.choose h2) hp₁ hp₂ hp12 hdvd1 ?_ hle1 ?_
      · rw [hsub]; exact hdvd2
      · rw [hsub]; exact hle2
  calc S.card ≤ (Finset.Icc 1 ((H - 1) / 2)).card := Finset.card_le_card_of_injOn f hfmem hinj
    _ ≤ H := by rw [Nat.card_Icc]; omega

end Conjectures.QuadraticPrimes.NearEqualSemiprimeCount_aux

theorem Conjectures.QuadraticPrimes.NearEqualSemiprimeCount :
    letI := Classical.propDecidable; ∃ C : ℝ, 0 < C ∧ ∀ x H : ℕ, 1 ≤ H → H ≤ x → (((Finset.Ioc x (2*x)).filter fun n => Even n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p<q ∧ n^2+1=p*q ∧ q-p≤H).card : ℝ) ≤ C*H := by
  refine ⟨1, by norm_num, ?_⟩
  intro x H hH1 hHx
  classical
  have hcard : ((Finset.Ioc x (2 * x)).filter (fun n => Even n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n ^ 2 + 1 = p * q ∧ q - p ≤ H)).card ≤ H := by
    refine Conjectures.QuadraticPrimes.NearEqualSemiprimeCount_aux.card_le x H hH1 hHx _ ?_ ?_
    · intro n hn
      exact (Finset.mem_filter.mp hn).2.2
    · intro n hn
      exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
  have hreal : (((Finset.Ioc x (2*x)).filter fun n => Even n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p<q ∧ n^2+1=p*q ∧ q-p≤H).card : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast hcard
  simpa using hreal
