import Mathlib

/-!
# QP `L-quadratic-primes-middle-coarse`：中段质量 ≤ 4 · apTheta

把 `middle x` 按素数纤维重排。三个初等事实就够了：

* 每个中段素数 `p`（`p ∣ n ^ 2 + 1`、`x < p`）重数 ≤ 2，因为 `p ≥ x + 1`、`n ≤ 2 x` 给出
  `p ^ 3 ≥ (x + 1) ^ 3 > 4 x ^ 2 + 1 ≥ n ^ 2 + 1`（`x ≥ 1` 时恒成立）；
* 每个中段素数满足 `p ≡ 1 [MOD 4]`（`n ^ 2 ≡ -1`，`ZMod.mod_four_ne_three_of_sq_eq_neg_one`，
  而 `p = 2` 在 `x ≥ 1` 时不可能）；
* 固定 `p`，落在 `(x, 2 x]` 里的根至多两个：区间长度 `< p` 使 `(↑) : ℕ → ZMod p` 在区间上单射，
  而 `n ^ 2 = b ^ 2 = -1` 逼出 `n = ±b`。

于是 `(n, p)` 对的和重排成 `Σ p, card • log p` 且每个纤维 `card ≤ 2`，配上重数 2 就是常数 4；
纤维的支撑含在 `apTheta x` 的求和集里。全程不上任何 AP-Chebyshev 下界。
-/

namespace QpMiddleCoarse

open Finset Nat

/-- 中段素数纤维：`n ^ 2 + 1` 的素因子中满足 `x < p` 与 `p ^ 100000 ≤ n ^ 132301` 的那些。 -/
def fib (x n : ℕ) : Finset ℕ :=
  (n ^ 2 + 1).primeFactors.filter (fun p => x < p ∧ p ^ 100000 ≤ n ^ 132301)

noncomputable def wgt (n p : ℕ) : ℝ := ((n ^ 2 + 1).factorization p : ℝ) * Real.log p

noncomputable def middle (x : ℕ) : ℝ :=
  ∑ n ∈ Ioc x (2 * x), ∑ p ∈ fib x n, wgt n p

noncomputable def apTheta (x : ℕ) : ℝ :=
  ∑ p ∈ ((range ((2 * x) ^ 132301 + 1)).filter (fun p => p.Prime ∧ p % 4 = 1)), Real.log p

lemma mem_fib {x n p : ℕ} (h : p ∈ fib x n) : p.Prime ∧ p ∣ n ^ 2 + 1 ∧ x < p := by
  have hm := Finset.mem_filter.mp h
  have h1 := Nat.mem_primeFactors.mp hm.1
  exact ⟨h1.1, h1.2.1, hm.2.1⟩

lemma log_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ Real.log (p : ℝ) :=
  Real.log_nonneg (by exact_mod_cast (show (1 : ℕ) ≤ p from by omega))

lemma sq_neg_one {n p : ℕ} (hp : p ∈ fib x n) : (n : ZMod p) ^ 2 = -1 := by
  obtain ⟨hpp, hpdvd, _⟩ := mem_fib hp
  have h0 : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) p).mpr hpdvd
  have h1 : (n : ZMod p) ^ 2 + 1 = 0 := by
    have hc : ((n ^ 2 + 1 : ℕ) : ZMod p) = (n : ZMod p) ^ 2 + 1 := by push_cast; rfl
    rwa [hc] at h0
  calc (n : ZMod p) ^ 2 = (n : ZMod p) ^ 2 + 1 - 1 := by abel
    _ = 0 - 1 := by rw [h1]
    _ = -1 := by simp

/-- 重数 ≤ 2。 -/
lemma multiplicity_le_two {x n p : ℕ} (hx : 1 ≤ x) (hn : n ∈ Ioc x (2 * x))
    (hp : p ∈ fib x n) : (n ^ 2 + 1).factorization p ≤ 2 := by
  obtain ⟨hpp, hpdvd, hxp⟩ := mem_fib hp
  have hn1 := Finset.mem_Ioc.mp hn
  by_contra hcontra
  push_neg at hcontra
  have h3dvd : p ^ 3 ∣ n ^ 2 + 1 := by
    have hle : 3 ≤ (n ^ 2 + 1).factorization p := by omega
    exact (hpp.pow_dvd_iff_le_factorization (by omega : n ^ 2 + 1 ≠ 0)).mpr hle
  have h3le : p ^ 3 ≤ n ^ 2 + 1 := Nat.le_of_dvd (by positivity) h3dvd
  have hpx : x + 1 ≤ p := by omega
  have hcube : (x + 1) ^ 3 > 4 * x ^ 2 + 1 := by
    have h1 : (x + 1) ^ 3 = x ^ 3 + 3 * x ^ 2 + 3 * x + 1 := by ring
    have h2 : x ^ 2 ≤ x ^ 3 := pow_le_pow_right' hx (by omega)
    have h3 : 3 * x ≥ 3 := by omega
    omega
  have hnle : n ^ 2 + 1 ≤ 4 * x ^ 2 + 1 := by
    have hh : n ^ 2 ≤ 4 * x ^ 2 := by
      calc n ^ 2 ≤ (2 * x) ^ 2 := pow_le_pow_left' hn1.2 2
        _ = 4 * x ^ 2 := by ring
    exact Nat.add_le_add_right hh 1
  have : (x + 1) ^ 3 ≤ p ^ 3 := pow_le_pow_left' hpx 3
  omega

/-- 中段素数都是 `1 [MOD 4]`。 -/
lemma mod_four_eq_one {x n p : ℕ} (hx : 1 ≤ x) (hn : n ∈ Ioc x (2 * x)) (hp : p ∈ fib x n) :
    p % 4 = 1 := by
  obtain ⟨hpp, hpdvd, hxp⟩ := mem_fib hp
  have hp2 : p ≠ 2 := by
    intro h2
    have hx1 : x = 1 := by omega
    have hn1 := Finset.mem_Ioc.mp hn
    subst hx1
    have hn2 : n = 2 := by omega
    rw [hn2, show (2 : ℕ) ^ 2 + 1 = 5 by norm_num] at hpdvd
    rw [h2] at hpdvd
    norm_num at hpdvd
  haveI : Fact p.Prime := ⟨hpp⟩
  have hne3 : p % 4 ≠ 3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one (p := p) (sq_neg_one hp)
  have hodd : p % 2 = 1 := by
    rcases hpp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hdiv : p = 4 * (p / 4) + p % 4 := (Nat.div_add_mod p 4).symm
  omega

/-- `(↑) : ℕ → ZMod p` 在 `(x, 2 x]` 上单射，只要 `x < p`。 -/
lemma cast_inj {x p a b : ℕ} (hxp : x < p) (ha : a ∈ Ioc x (2 * x)) (hb : b ∈ Ioc x (2 * x))
    (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  obtain ⟨ha1, ha2⟩ := Finset.mem_Ioc.mp ha
  obtain ⟨hb1, hb2⟩ := Finset.mem_Ioc.mp hb
  rcases le_total a b with hle | hle
  · have h0 : ((b - a : ℕ) : ZMod p) = 0 := by rw [Nat.cast_sub hle, h, sub_self]
    have hd : p ∣ b - a := (ZMod.natCast_eq_zero_iff (b - a) p).mp h0
    have hbnd : b - a ≤ x := by omega
    have hzero : b - a = 0 := by
      by_contra hnz
      have hpos : 0 < b - a := Nat.pos_of_ne_zero hnz
      have : p ≤ b - a := Nat.le_of_dvd hpos hd
      omega
    omega
  · have h0 : ((a - b : ℕ) : ZMod p) = 0 := by rw [Nat.cast_sub hle, h.symm, sub_self]
    have hd : p ∣ a - b := (ZMod.natCast_eq_zero_iff (a - b) p).mp h0
    have hbnd : a - b ≤ x := by omega
    have hzero : a - b = 0 := by
      by_contra hnz
      have hpos : 0 < a - b := Nat.pos_of_ne_zero hnz
      have : p ≤ a - b := Nat.le_of_dvd hpos hd
      omega
    omega

/-- 固定素数 `p`，区间 `(x, 2 x]` 里 `n ^ 2 ≡ -1 [MOD p]` 的根至多两个。 -/
lemma card_fibre_le_two {x p : ℕ} (hxp : x < p) :
    ((Ioc x (2 * x)).filter (fun n => p ∈ fib x n)).card ≤ 2 := by
  classical
  set s := (Ioc x (2 * x)).filter (fun n => p ∈ fib x n) with hs
  by_cases hb : s = ∅
  · rw [hb]
    simp
  obtain ⟨b, hb⟩ : ∃ b, b ∈ s := Finset.nonempty_of_ne_empty hb
  have hbmem : b ∈ Ioc x (2 * x) ∧ p ∈ fib x b := Finset.mem_filter.mp hb
  have hp : p.Prime := (mem_fib hbmem.2).1
  haveI : Fact p.Prime := ⟨hp⟩
  have hb2 : (b : ZMod p) ^ 2 = -1 := sq_neg_one hbmem.2
  have hn0 : (b : ZMod p) ≠ 0 := by
    intro hz
    have h1 : (-1 : ZMod p) = 0 := by rw [← hb2, hz]; simp
    exact absurd h1 (neg_ne_zero.mpr one_ne_zero)
  have hsub : s.image (fun n : ℕ => (n : ZMod p)) ⊆ {(b : ZMod p), -(b : ZMod p)} := by
    intro y hy
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
    have hnmem : n ∈ Ioc x (2 * x) ∧ p ∈ fib x n := Finset.mem_filter.mp hn
    have h2n : (n : ZMod p) ^ 2 = -1 := sq_neg_one hnmem.2
    have hu : ((n : ZMod p) * (b : ZMod p)⁻¹) ^ 2 = 1 := by
      calc ((n : ZMod p) * (b : ZMod p)⁻¹) ^ 2 = (n : ZMod p) ^ 2 * ((b : ZMod p) ^ 2)⁻¹ := by field_simp [hn0, pow_two]
        _ = (-1 : ZMod p) * (-1 : ZMod p)⁻¹ := by rw [h2n, hb2]
        _ = 1 := by field_simp
    have hfac : ((n : ZMod p) * (b : ZMod p)⁻¹ - 1) *
        ((n : ZMod p) * (b : ZMod p)⁻¹ + 1) = 0 := by
      have h1 : ((n : ZMod p) * (b : ZMod p)⁻¹) ^ 2 - 1 = 0 := by rw [hu]; simp
      have h2 : ((n : ZMod p) * (b : ZMod p)⁻¹ - 1) *
          ((n : ZMod p) * (b : ZMod p)⁻¹ + 1) = ((n : ZMod p) * (b : ZMod p)⁻¹) ^ 2 - 1 := by
        ring
      rw [h2, h1]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hfac with h | h
    · have hu1 : (n : ZMod p) * (b : ZMod p)⁻¹ = 1 := by
        have h' : ((n : ZMod p) * (b : ZMod p)⁻¹ - 1) + 1 = (0 : ZMod p) + 1 := by rw [h]
        simpa using h'
      have hn' : (n : ZMod p) = (b : ZMod p) := by
        calc (n : ZMod p) = (n : ZMod p) * ((b : ZMod p) * (b : ZMod p)⁻¹) := by field_simp [hn0]
          _ = ((n : ZMod p) * (b : ZMod p)⁻¹) * (b : ZMod p) := by ring
          _ = 1 * (b : ZMod p) := by rw [hu1]
          _ = (b : ZMod p) := by simp
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl hn'
    · have hu1 : (n : ZMod p) * (b : ZMod p)⁻¹ = -1 := by
        have h' : ((n : ZMod p) * (b : ZMod p)⁻¹ + 1) - 1 = (0 : ZMod p) - 1 := by rw [h]
        simpa using h'
      have hn' : (n : ZMod p) = -(b : ZMod p) := by
        calc (n : ZMod p) = (n : ZMod p) * ((b : ZMod p) * (b : ZMod p)⁻¹) := by field_simp [hn0]
          _ = ((n : ZMod p) * (b : ZMod p)⁻¹) * (b : ZMod p) := by ring
          _ = (-1 : ZMod p) * (b : ZMod p) := by rw [hu1]
          _ = -(b : ZMod p) := by simp
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr hn'
  have hinj : Set.InjOn (fun n : ℕ => (n : ZMod p)) (↑s) := by
    intro a ha bb hb h
    obtain ⟨ha1, _⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb1, _⟩ := Finset.mem_filter.mp hb
    exact cast_inj hxp ha1 hb1 h
  have hpair : ({(b : ZMod p), -(b : ZMod p)} : Finset (ZMod p)).card ≤ 2 := by
    calc ({(b : ZMod p), -(b : ZMod p)} : Finset (ZMod p)).card
        = (insert (b : ZMod p) ({-(b : ZMod p)} : Finset (ZMod p))).card := rfl
      _ ≤ ({-(b : ZMod p)} : Finset (ZMod p)).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by rw [Finset.card_singleton]
  calc s.card = (s.image (fun n : ℕ => (n : ZMod p))).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ ({(b : ZMod p), -(b : ZMod p)} : Finset (ZMod p)).card := Finset.card_le_card hsub
    _ ≤ 2 := hpair

/-- 双重和按第二个坐标重排（`g` 不依赖第一个坐标）。 -/
lemma swap_sum {F : ℕ → Finset ℕ} {s : Finset ℕ} (g : ℕ → ℝ) :
    (∑ n ∈ s, ∑ p ∈ F n, g p) = ∑ p ∈ s.biUnion F, (s.filter (fun n => p ∈ F n)).card • g p := by
  classical
  have hdn : Set.PairwiseDisjoint (↑s) (fun n => (F n).image (fun p => (n, p))) := by
    intro a ha b hb hab
    refine Finset.disjoint_left.mpr ?_
    intro y hy1 hy2
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hy1
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hy2
    rw [Prod.mk.injEq] at hq
    exact hab hq.1.symm
  have hdp : Set.PairwiseDisjoint (↑(s.biUnion F))
      (fun p => (s.filter (fun n => p ∈ F n)).image (fun n => (n, p))) := by
    intro a ha b hb hab
    refine Finset.disjoint_left.mpr ?_
    intro y hy1 hy2
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hy1
    obtain ⟨m, hm, h2⟩ := Finset.mem_image.mp hy2
    rw [Prod.mk.injEq] at h2
    exact hab h2.2.symm
  have hEq : s.biUnion (fun n => (F n).image (fun p => (n, p))) =
      (s.biUnion F).biUnion (fun p => (s.filter (fun n => p ∈ F n)).image (fun n => (n, p))) := by
    apply Finset.ext
    intro q
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, and_assoc]
    constructor
    · rintro ⟨n, hn, p, hp, rfl⟩
      exact ⟨p, ⟨n, hn, hp⟩, n, hn, hp, rfl⟩
    · rintro ⟨p, ⟨n, hn, hp⟩, m, hm, hmp, hq⟩
      subst hq
      exact ⟨m, hm, p, by simpa using hmp, rfl⟩
  calc ∑ n ∈ s, ∑ p ∈ F n, g p
      = ∑ n ∈ s, ∑ q ∈ (F n).image (fun p => (n, p)), g q.2 := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.sum_image]
        simp
    _ = (s.biUnion (fun n => (F n).image (fun p => (n, p)))).sum (fun q => g q.2) :=
        (Finset.sum_biUnion hdn).symm
    _ = ((s.biUnion F).biUnion (fun p => (s.filter (fun n => p ∈ F n)).image (fun n => (n, p)))).sum
        (fun q => g q.2) := by rw [hEq]
    _ = ∑ p ∈ s.biUnion F,
        ∑ q ∈ (s.filter (fun n => p ∈ F n)).image (fun n => (n, p)), g q.2 :=
        Finset.sum_biUnion hdp
    _ = ∑ p ∈ s.biUnion F, ∑ n ∈ s.filter (fun n => p ∈ F n), g p := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.sum_image]
        simp
    _ = ∑ p ∈ s.biUnion F, (s.filter (fun n => p ∈ F n)).card • g p := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.sum_const]

/-- 纤维支撑含在 `apTheta x` 的求和集里。 -/
lemma support_subset (x : ℕ) (hx : 1 ≤ x) :
    (Ioc x (2 * x)).biUnion (fib x) ⊆
      ((range ((2 * x) ^ 132301 + 1)).filter (fun p => p.Prime ∧ p % 4 = 1)) := by
  intro p hp
  obtain ⟨n, hn, hp'⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨hpp, hpdvd, hxp⟩ := mem_fib hp'
  have hn1 := Finset.mem_Ioc.mp hn
  have h1 : p ≤ n ^ 2 + 1 := Nat.le_of_dvd (by positivity) hpdvd
  have h2 : n ^ 2 + 1 ≤ 4 * x ^ 2 + 1 := by
    have hh : n ^ 2 ≤ 4 * x ^ 2 := by
      calc n ^ 2 ≤ (2 * x) ^ 2 := pow_le_pow_left' hn1.2 2
        _ = 4 * x ^ 2 := by ring
    exact Nat.add_le_add_right hh 1
  have h3 : 4 * x ^ 2 + 1 ≤ (2 * x) ^ 132301 := by
    have h4 : (2 * x) ^ 3 ≤ (2 * x) ^ 132301 :=
      pow_le_pow_right' (by omega : 1 ≤ 2 * x) (by omega : 3 ≤ (132301 : ℕ))
    have h5 : (2 * x) ^ 3 = 8 * x ^ 3 := by ring
    have h6 : x ^ 2 ≤ x ^ 3 := pow_le_pow_right' hx (by omega : 2 ≤ (3 : ℕ))
    have h7 : 8 * x ^ 3 ≥ 8 * x ^ 2 := Nat.mul_le_mul_left 8 h6
    have h8 : 8 * x ^ 2 ≥ 4 * x ^ 2 + 1 := by
      have : 4 * x ^ 2 ≥ 1 := by nlinarith
      omega
    omega
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hpp, mod_four_eq_one hx hn hp'⟩

lemma main (x : ℕ) (hx : 1 ≤ x) : middle x ≤ 4 * apTheta x := by
  classical
  have hstep1 : middle x ≤ 2 * ∑ n ∈ Ioc x (2 * x), ∑ p ∈ fib x n, Real.log (p : ℝ) := by
    have hA : (∑ n ∈ Ioc x (2 * x), ∑ p ∈ fib x n, wgt n p) ≤
        ∑ n ∈ Ioc x (2 * x), ∑ p ∈ fib x n, (2 : ℝ) * Real.log (p : ℝ) := by
      refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun p hp => ?_
      have hle := multiplicity_le_two hx hn hp
      have hlog := log_nonneg (Nat.Prime.two_le (mem_fib hp).1)
      have h2 : ((n ^ 2 + 1).factorization p : ℝ) ≤ (2 : ℝ) := by exact_mod_cast hle
      calc wgt n p = ((n ^ 2 + 1).factorization p : ℝ) * Real.log (p : ℝ) := rfl
        _ ≤ (2 : ℝ) * Real.log (p : ℝ) := mul_le_mul_of_nonneg_right h2 hlog
    have hB : ∑ n ∈ Ioc x (2 * x), ∑ p ∈ fib x n, (2 : ℝ) * Real.log (p : ℝ)
        = 2 * ∑ n ∈ Ioc x (2 * x), ∑ p ∈ fib x n, Real.log (p : ℝ) := by
      simp only [Finset.mul_sum]
    rw [← hB]
    exact hA
  have hP := support_subset x hx
  have hcard : ∀ p ∈ (Ioc x (2 * x)).biUnion (fib x),
      ((Ioc x (2 * x)).filter (fun n => p ∈ fib x n)).card ≤ 2 := by
    intro p hp
    obtain ⟨n, _, hpn⟩ := Finset.mem_biUnion.mp hp
    exact card_fibre_le_two (mem_fib hpn).2.2
  have hprime : ∀ p ∈ (Ioc x (2 * x)).biUnion (fib x), Nat.Prime p := by
    intro p hp
    obtain ⟨n, _, hpn⟩ := Finset.mem_biUnion.mp hp
    exact (mem_fib hpn).1
  have hmid : (∑ p ∈ (Ioc x (2 * x)).biUnion (fib x),
      ((Ioc x (2 * x)).filter (fun n => p ∈ fib x n)).card • Real.log (p : ℝ))
      ≤ ∑ p ∈ (Ioc x (2 * x)).biUnion (fib x), (2 : ℝ) * Real.log (p : ℝ) := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hlog := log_nonneg (Nat.Prime.two_le (hprime p hp))
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcard p hp)) hlog
  have hsum : ∑ p ∈ (Ioc x (2 * x)).biUnion (fib x), (2 : ℝ) * Real.log (p : ℝ)
      = 2 * ∑ p ∈ (Ioc x (2 * x)).biUnion (fib x), Real.log (p : ℝ) := by
        simp only [Finset.mul_sum]
  have htail : ∑ p ∈ (Ioc x (2 * x)).biUnion (fib x), Real.log (p : ℝ) ≤ apTheta x := by
    show ∑ p ∈ (Ioc x (2 * x)).biUnion (fib x), Real.log (p : ℝ) ≤
      ∑ p ∈ ((range ((2 * x) ^ 132301 + 1)).filter (fun p => p.Prime ∧ p % 4 = 1)), Real.log p
    refine Finset.sum_le_sum_of_subset_of_nonneg hP (fun p hp _ => ?_)
    obtain ⟨_, hpr⟩ := Finset.mem_filter.mp hp
    exact log_nonneg (Nat.Prime.two_le hpr.1)
  calc middle x ≤ 2 * ∑ n ∈ Ioc x (2 * x), ∑ p ∈ fib x n, Real.log (p : ℝ) := hstep1
    _ = 2 * ∑ p ∈ (Ioc x (2 * x)).biUnion (fib x),
          ((Ioc x (2 * x)).filter (fun n => p ∈ fib x n)).card • Real.log (p : ℝ) := by
        rw [swap_sum (fun p => Real.log (p : ℝ))]
    _ ≤ 2 * ∑ p ∈ (Ioc x (2 * x)).biUnion (fib x), (2 : ℝ) * Real.log (p : ℝ) :=
        mul_le_mul_of_nonneg_left hmid (by norm_num : (0 : ℝ) ≤ 2)
    _ = 2 * (2 * ∑ p ∈ (Ioc x (2 * x)).biUnion (fib x), Real.log (p : ℝ)) := by rw [hsum]
    _ = 4 * ∑ p ∈ (Ioc x (2 * x)).biUnion (fib x), Real.log (p : ℝ) := by ring
    _ ≤ 4 * apTheta x :=
        mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 4)

end QpMiddleCoarse

/-- 中段质量按素数纤维重排：单素数重数 ≤ 2、根数 ≤ 2，故总贡献 ≤ `4 · apTheta x`。
每个中段素数 `p ∣ n ^ 2 + 1`（`x < p`、`x ≥ 1`）是 `1 [MOD 4]`，重数 `≤ 2`（因
`p ^ 3 ≥ (x + 1) ^ 3 > 4 x ^ 2 + 1 ≥ n ^ 2 + 1`），且 `(x, 2 x]` 里至多两个根（区间长度 `< p`
使 `ZMod p` 上的像单射，`n ^ 2 = b ^ 2 = -1` 逼出 `n = ± b`）。重排双重和即得常数 4。 -/
theorem Conjectures.QuadraticPrimes.MiddleCoarse :
    let wgt := fun (n p : ℕ) => (((n ^ 2 + 1).factorization p : ℕ) : ℝ) * Real.log (p : ℝ);
    let middle := fun (x : ℕ) =>
      Finset.sum (Finset.Ioc x (2 * x)) (fun n =>
        Finset.sum ((n ^ 2 + 1).primeFactors.filter (fun p => x < p ∧ p ^ 100000 ≤ n ^ 132301))
          (fun (p : ℕ) => wgt n p));
    let apTheta := fun (x : ℕ) =>
      Finset.sum ((Finset.range ((2 * x) ^ 132301 + 1)).filter (fun p => p.Prime ∧ p % 4 = 1))
        (fun p => Real.log (p : ℝ));
    ∀ x : ℕ, 1 ≤ x → middle x ≤ 4 * apTheta x := by
  intros wgt middle apTheta x hx
  exact QpMiddleCoarse.main x hx
