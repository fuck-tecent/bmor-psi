import Mathlib

/-!
# `r² ≡ -a (mod p^k)` 的根數上界：至多 `4a` 個

設 `p` 為素數、`a ≥ 1`。

- 若 `p^k ≤ 4a`，根數不超過 `p^k`，直接成立。
- 否則固定一個根 `r₀`，令 `j = min(v_p(2r₀), k)`、`g = p^j`、`q = p^(k-j)`。
  - 任一根 `s` 都滿足 `q ∣ |r₀ - s|` 或 `q ∣ r₀ + s`，因為 `p^k ∣ (r₀-s)(r₀+s)`，而兩因子的公共 `p` 冪整除 `2r₀`。
  - `g² ≤ 4a`：若 `2j ≤ k`，則 `g² ∣ 4(r₀²+a) - (2r₀)² = 4a`；若 `2j > k`，則 `p^k ∣ 4a`，與 `p^k > 4a` 矛盾。
  - 所以根落在模 `q` 的兩個剩餘類中，每類至多 `g` 個，合計至多 `2g ≤ 4a` 個。
-/

namespace QPShift

def rootsA (a m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun n => m ∣ n ^ 2 + a)

/-- 一個剩餘類在 `[0, q·g)` 中至多 `g` 個元素。 -/
lemma card_residue_le (q g c : ℕ) (hq : 0 < q) :
    ((Finset.range (q * g)).filter (fun s => s % q = c)).card ≤ g := by
  calc ((Finset.range (q * g)).filter (fun s => s % q = c)).card
      ≤ (Finset.range g).card := by
        apply Finset.card_le_card_of_injOn (fun s => s / q)
        · intro s hs
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hs
          rw [Finset.mem_coe, Finset.mem_range]
          exact (Nat.div_lt_iff_lt_mul hq).mpr (by rw [mul_comm]; exact hs.1)
        · intro s hs t ht hst
          rw [Finset.mem_coe, Finset.mem_filter] at hs ht
          have h1 := Nat.div_add_mod s q
          have h2 := Nat.div_add_mod t q
          simp only at hst
          rw [hst, hs.2] at h1
          rw [ht.2] at h2
          omega
    _ = g := Finset.card_range g

/-- 兩因子的公共 `p` 冪：若 `p^m ∣ D` 且 `p^m ∣ B`，則 `p^m ∣ 2r₀`。 -/
lemma common_dvd_two_mul {r s D B P : ℕ} (hD : D = max r s - min r s) (hB : B = r + s)
    (h1 : P ∣ D) (h2 : P ∣ B) : P ∣ 2 * r := by
  rcases le_total s r with h | h
  · have hD' : D = r - s := by rw [hD, max_eq_left h, min_eq_right h]
    have : D + B = 2 * r := by omega
    rw [← this]; exact dvd_add h1 h2
  · have hD' : D = s - r := by rw [hD, max_eq_right h, min_eq_left h]
    have : B - D = 2 * r := by omega
    rw [← this]; exact Nat.dvd_sub h2 h1

theorem rootsA_prime_power_le {a p k : ℕ} (ha : 1 ≤ a) (hp : p.Prime) (hk : 0 < k) :
    (rootsA a (p ^ k)).card ≤ 4 * a := by
  classical
  have hpk0 : 0 < p ^ k := pow_pos hp.pos k
  by_cases hsmall : p ^ k ≤ 4 * a
  · calc (rootsA a (p ^ k)).card ≤ (Finset.range (p ^ k)).card := Finset.card_filter_le _ _
      _ = p ^ k := Finset.card_range _
      _ ≤ 4 * a := hsmall
  push_neg at hsmall
  rcases (rootsA a (p ^ k)).eq_empty_or_nonempty with hE | ⟨r0, hr0⟩
  · simp [hE]
  have hr0' := Finset.mem_filter.mp hr0
  have hr0lt : r0 < p ^ k := Finset.mem_range.mp hr0'.1
  have hr0d : p ^ k ∣ r0 ^ 2 + a := hr0'.2
  have := Fact.mk hp
  -- r0 > 0：否則 p^k ∣ a
  have hr0pos : 0 < r0 := by
    rcases Nat.eq_zero_or_pos r0 with h | h
    · subst h
      have : p ^ k ∣ a := by simpa using hr0d
      have := Nat.le_of_dvd (by omega) this
      omega
    · exact h
  set j := min (multiplicity p (2 * r0)) k with hj
  set g := p ^ j with hg
  set q := p ^ (k - j) with hq
  have hjk : j ≤ k := min_le_right _ _
  have hqg : q * g = p ^ k := by rw [hq, hg, ← pow_add]; congr 1; omega
  have hq0 : 0 < q := pow_pos hp.pos _
  have hg2r : g ∣ 2 * r0 := by
    rw [hg]
    exact (pow_dvd_pow p (min_le_left _ _)).trans (pow_multiplicity_dvd _ _)
  -- g² ≤ 4a
  have hg4a : g ^ 2 ≤ 4 * a := by
    by_cases h2j : 2 * j ≤ k
    · have hgsq : g ^ 2 ∣ p ^ k := by
        rw [hg, ← pow_mul]; exact pow_dvd_pow p (by omega)
      have h4 : g ^ 2 ∣ 4 * (r0 ^ 2 + a) := (hgsq.trans hr0d).mul_left 4
      have h4r : g ^ 2 ∣ (2 * r0) ^ 2 := pow_dvd_pow_of_dvd hg2r 2
      have h4a : g ^ 2 ∣ 4 * a := by
        have := Nat.dvd_sub h4 h4r
        rwa [show 4 * (r0 ^ 2 + a) - (2 * r0) ^ 2 = 4 * a by ring_nf; omega] at this
      exact Nat.le_of_dvd (by omega) h4a
    · exfalso
      have hpkg : p ^ k ∣ g ^ 2 := by
        rw [hg, ← pow_mul]; exact pow_dvd_pow p (by omega)
      have h4r : p ^ k ∣ (2 * r0) ^ 2 := hpkg.trans (pow_dvd_pow_of_dvd hg2r 2)
      have h4 : p ^ k ∣ 4 * (r0 ^ 2 + a) := hr0d.mul_left 4
      have h4a : p ^ k ∣ 4 * a := by
        have := Nat.dvd_sub h4 h4r
        rwa [show 4 * (r0 ^ 2 + a) - (2 * r0) ^ 2 = 4 * a by ring_nf; omega] at this
      have := Nat.le_of_dvd (by omega) h4a
      omega
  have hg2a : g ≤ 2 * a := by nlinarith
  -- 每個根落在兩個剩餘類之一
  have hclass : ∀ s ∈ rootsA a (p ^ k),
      s % q = r0 % q ∨ s % q = (q - r0 % q) % q := by
    intro s hs
    have hs' := Finset.mem_filter.mp hs
    have hsd : p ^ k ∣ s ^ 2 + a := hs'.2
    set D := max r0 s - min r0 s with hD
    set B := r0 + s with hB
    have hBpos : 0 < B := by omega
    have hprod : p ^ k ∣ D * B := by
      rcases le_total s r0 with h | h
      · have hD' : D = r0 - s := by rw [hD, max_eq_left h, min_eq_right h]
        have e : D * B = (r0 ^ 2 + a) - (s ^ 2 + a) := by
          rw [hD', hB]
          have : s ^ 2 ≤ r0 ^ 2 := Nat.pow_le_pow_left h 2
          zify [h, this, (show s ^ 2 + a ≤ r0 ^ 2 + a by omega)]; ring
        rw [e]; exact Nat.dvd_sub hr0d hsd
      · have hD' : D = s - r0 := by rw [hD, max_eq_right h, min_eq_left h]
        have e : D * B = (s ^ 2 + a) - (r0 ^ 2 + a) := by
          rw [hD', hB]
          have : r0 ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left h 2
          zify [h, this, (show r0 ^ 2 + a ≤ s ^ 2 + a by omega)]; ring
        rw [e]; exact Nat.dvd_sub hsd hr0d
    -- q ∣ D 或 q ∣ B
    have hqDB : q ∣ D ∨ q ∣ B := by
      by_cases hD0 : D = 0
      · left; rw [hD0]; exact dvd_zero q
      by_cases hqD : q ∣ D
      · exact Or.inl hqD
      right
      have hvD : multiplicity p D < k - j := by
        by_contra hc
        push_neg at hc
        exact hqD ((pow_dvd_pow p hc).trans (pow_multiplicity_dvd _ _))
      have hvsum : k ≤ multiplicity p D + multiplicity p B := by
        rw [← Nat.multiplicity_mul hD0 hBpos.ne']
        exact (Nat.pow_dvd_iff_le_multiplicity hp.ne_one (by positivity)).mp hprod
      -- 公共冪
      have hmin : min (multiplicity p D) (multiplicity p B) ≤ multiplicity p (2 * r0) := by
        apply (Nat.pow_dvd_iff_le_multiplicity hp.ne_one (by omega)).mp
        apply common_dvd_two_mul hD hB
        · exact (pow_dvd_pow p (min_le_left _ _)).trans (pow_multiplicity_dvd _ _)
        · exact (pow_dvd_pow p (min_le_right _ _)).trans (pow_multiplicity_dvd _ _)
      have hvB : k - j ≤ multiplicity p B := by
        by_cases hjeq : j = k
        · omega
        have hj' : j = multiplicity p (2 * r0) := by
          rw [hj]; exact min_eq_left (by omega)
        rcases le_total (multiplicity p D) (multiplicity p B) with h | h
        · rw [min_eq_left h] at hmin
          omega
        · rw [min_eq_right h] at hmin
          omega
      exact (pow_dvd_pow p hvB).trans (pow_multiplicity_dvd _ _)
    rcases hqDB with h | h
    · left
      rcases le_total s r0 with hsr | hsr
      · have hD' : D = r0 - s := by rw [hD, max_eq_left hsr, min_eq_right hsr]
        rw [hD'] at h
        exact ((Nat.modEq_iff_dvd' hsr).mpr h)
      · have hD' : D = s - r0 := by rw [hD, max_eq_right hsr, min_eq_left hsr]
        rw [hD'] at h
        exact ((Nat.modEq_iff_dvd' hsr).mpr h).symm
    · right
      have h1 : (r0 % q + s % q) % q = 0 := by
        rw [← Nat.add_mod]; exact Nat.mod_eq_zero_of_dvd h
      obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h1
      have hr := Nat.mod_lt r0 hq0
      have hs := Nat.mod_lt s hq0
      have hc2 : c < 2 := by
        by_contra hc2
        push_neg at hc2
        have : q * 2 ≤ q * c := Nat.mul_le_mul_left q hc2
        omega
      interval_cases c
      · have hr0' : r0 % q = 0 := by omega
        have hs0 : s % q = 0 := by omega
        rw [hr0', hs0, Nat.sub_zero, Nat.mod_self]
      · rw [Nat.mod_eq_of_lt (by omega : q - r0 % q < q)]
        omega
  -- 計數
  have hsub : rootsA a (p ^ k) ⊆
      ((Finset.range (q * g)).filter (fun s => s % q = r0 % q)) ∪
        ((Finset.range (q * g)).filter (fun s => s % q = (q - r0 % q) % q)) := by
    intro s hs
    have hslt : s < p ^ k := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_range, hqg]
    rcases hclass s hs with h | h
    · exact Or.inl ⟨hslt, h⟩
    · exact Or.inr ⟨hslt, h⟩
  calc (rootsA a (p ^ k)).card
      ≤ (((Finset.range (q * g)).filter (fun s => s % q = r0 % q)) ∪
        ((Finset.range (q * g)).filter (fun s => s % q = (q - r0 % q) % q))).card :=
        Finset.card_le_card hsub
    _ ≤ g + g := (Finset.card_union_le _ _).trans
        (add_le_add (card_residue_le q g _ hq0) (card_residue_le q g _ hq0))
    _ ≤ 4 * a := by omega

end QPShift

/-- 指數參數：`1.32301 ≤ U/V ≤ 1.325`。 -/
class ShiftData (U V : ℕ) : Prop where
  hV : 0 < V
  h1 : 132301 * V ≤ 100000 * U
  h2 : 40 * U ≤ 53 * V

namespace ShiftData
variable {U V : ℕ} [h : ShiftData U V]
include h
theorem U_pos : 0 < U := by have := h.hV; have := h.h1; omega
theorem V_pos' : (0 : ℝ) < V := by exact_mod_cast h.hV
theorem U_pos' : (0 : ℝ) < U := by exact_mod_cast U_pos (V := V)
theorem alpha_ge : (132301 / 100000 : ℝ) ≤ (U : ℝ) / V := by
  rw [le_div_iff₀ (V_pos' (U := U))]; have := h.h1; have : (132301 * V : ℝ) ≤ 100000 * U := by exact_mod_cast this
  linarith
theorem alpha_le : (U : ℝ) / V ≤ 53 / 40 := by
  rw [div_le_iff₀ (V_pos' (U := U))]; have := h.h2; have : (40 * U : ℝ) ≤ 53 * V := by exact_mod_cast this
  linarith
theorem alpha_pos : (0 : ℝ) < (U : ℝ) / V := div_pos (U_pos' (V := V)) (V_pos' (U := U))
theorem alpha_ge_one : (1 : ℝ) ≤ (U : ℝ) / V := by have := alpha_ge (U := U) (V := V); linarith
theorem alpha_le_three_halves : (U : ℝ) / V ≤ 3 / 2 := by have := alpha_le (U := U) (V := V); linarith
theorem alpha_le_two : (U : ℝ) / V ≤ 2 := by have := alpha_le (U := U) (V := V); linarith
end ShiftData

/-!
# High frequencies in the quadratic-root window

Pair opposite Fourier frequencies and sum an interval exactly. Abel summation
bounds each endpoint tail by the square root of the modulus divided by the
distance to a representative of the root. Near the moving lower endpoint,
switch to the cofactor of the quadratic value and count roots in short intervals.
The two endpoints together satisfy a power-saving estimate at all large scales.
-/

open scoped BigOperators

namespace QP0052Fourier

open Finset
open scoped BigOperators

/-- Consecutive cosine phases, with half-step `t`, telescope at half-integer endpoints. -/
theorem cosine_interval (b t : ℝ) (N : ℕ) :
    2 * Real.sin t * (∑ j ∈ range N, Real.cos (b + (j : ℝ) * (2*t))) =
      Real.sin (b + (N : ℝ)*(2*t) - t) - Real.sin (b-t) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih, Nat.cast_succ]
    set z := b + (N : ℝ)*(2*t)
    rw [show b + ((N : ℝ)+1)*(2*t)-t = z+t by dsimp [z]; ring]
    rw [Real.sin_sub z t, Real.sin_add z t]
    ring

/-- The sine interval identity has cosine values at its endpoints. -/
theorem sine_interval (b t : ℝ) (N : ℕ) :
    2 * Real.sin t * (∑ j ∈ range N, Real.sin (b + (j : ℝ) * (2*t))) =
      Real.cos (b-t) - Real.cos (b + (N : ℝ)*(2*t)-t) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih, Nat.cast_succ]
    set z := b + (N : ℝ)*(2*t)
    rw [show b + ((N : ℝ)+1)*(2*t)-t = z+t by dsimp [z]; ring]
    rw [Real.cos_sub z t, Real.cos_add z t]
    ring

theorem sine_interval_abs (b t : ℝ) (N : ℕ) (ht : 0 < |Real.sin t|) :
    |∑ j ∈ range N, Real.sin (b + (j : ℝ) * (2*t))| ≤ 1 / |Real.sin t| := by
  have h : |2 * Real.sin t * (∑ j ∈ range N, Real.sin (b + (j : ℝ) * (2*t)))| ≤ 2 := by
    rw [sine_interval]
    apply abs_le.mpr
    constructor <;> linarith [Real.cos_le_one (b-t), Real.neg_one_le_cos (b-t),
      Real.cos_le_one (b + (N : ℝ)*(2*t)-t), Real.neg_one_le_cos (b + (N : ℝ)*(2*t)-t)]
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h
  apply (le_div_iff₀ ht).mpr
  nlinarith

/-- Abel's bound localized to the supplied range. This permits the weights to start increasing
again after its last frequency. -/
theorem weighted_partial_bound (w g : ℕ → ℝ) (N : ℕ) (D : ℝ)
    (hdec : ∀ i < N, w (i+1) ≤ w i) (hpos : 0 ≤ w N)
    (hpartial : ∀ j ≤ N, |∑ i ∈ range j, g i| ≤ D) :
    |∑ i ∈ range N, w i * g i| ≤ w 0 * D := by
  let G := fun j : ℕ => ∑ i ∈ range j, g i
  let W := fun j : ℕ => ∑ i ∈ range j, w i * g i
  have Gstep (n : ℕ) : G (n+1) = G n + g n := sum_range_succ _ _
  have Wstep (n : ℕ) : W (n+1) = W n + w n * g n := sum_range_succ _ _
  have mid : ∀ j ≤ N, |W j - w j * G j| ≤ (w 0 - w j)*D := by
    intro j
    induction j with
    | zero => intro _; simp [G,W]
    | succ j ih =>
      intro hj
      have hd : 0 ≤ w j-w (j+1) := sub_nonneg.mpr (hdec j (by omega))
      calc
        |W (j+1) - w (j+1)*G (j+1)| =
            |(W j - w j * G j) + (w j-w (j+1))*G (j+1)| := by
              rw [Wstep, Gstep]; congr 1; ring
        _ ≤ |W j-w j*G j| + |(w j-w (j+1))*G (j+1)| := abs_add_le _ _
        _ ≤ (w 0-w j)*D + (w j-w (j+1))*D := by
            rw [abs_mul, abs_of_nonneg hd]
            exact add_le_add (ih (by omega)) (mul_le_mul_of_nonneg_left (hpartial _ hj) hd)
        _ = (w 0-w (j+1))*D := by ring
  change |W N| ≤ _
  calc
    |W N| = |(W N-w N*G N)+w N*G N| := by rw [sub_add_cancel]
    _ ≤ |W N-w N*G N| + |w N*G N| := abs_add_le _ _
    _ ≤ (w 0-w N)*D + w N*D := by
      rw [abs_mul, abs_of_nonneg hpos]
      exact add_le_add (mid N le_rfl) (mul_le_mul_of_nonneg_left (hpartial N le_rfl) hpos)
    _ = w 0*D := by ring

noncomputable def weight (p : ℝ) (k : ℕ) : ℝ := 1 / (p * Real.sin (Real.pi*k/p))

/-- The interval of positive frequencies is `m, ..., m+N-1`. The angle `t`
is `π * (E-r) / p`, where `E` is a half-integer interval endpoint. -/
noncomputable def endpoint (p : ℝ) (m N : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ range N, weight p (m+i) * Real.sin (((m+i : ℕ) : ℝ) * (2*t))

theorem weight_spec {p : ℝ} {k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (hhalf : 2*(k : ℝ) ≤ p) : 0 < weight p k ∧ weight p k ≤ 1/(2*(k : ℝ)) := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hθ : 2*(k : ℝ)/p ≤ Real.sin (Real.pi*k/p) := by
    have h := Real.le_sin_mul (show 0 ≤ 2*(k : ℝ)/p by positivity) ((div_le_one hp).mpr hhalf)
    rwa [show Real.pi/2*(2*(k : ℝ)/p) = Real.pi*k/p by ring] at h
  have hden : 2*(k : ℝ) ≤ p * Real.sin (Real.pi*k/p) := by
    have := (div_le_iff₀ hp).mp hθ
    linarith only [this, mul_comm p (Real.sin (Real.pi*k/p))]
  have hpos : 0 < 2*(k : ℝ) := by positivity
  exact ⟨one_div_pos.mpr (hpos.trans_le hden), one_div_le_one_div_of_le hpos hden⟩

theorem weight_antitone {p : ℝ} {k j : ℕ} (hp : 0 < p) (hk : 0 < k) (hkj : k ≤ j)
    (hj : 2*(j : ℝ) ≤ p) : weight p j ≤ weight p k := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkj' : (k : ℝ) ≤ j := by exact_mod_cast hkj
  have hπ := Real.pi_pos
  have ha : 0 < Real.pi*k/p := by positivity
  have hb : Real.pi*j/p ≤ Real.pi/2 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hj hπ.le]
  have hc : Real.pi*k/p ≤ Real.pi*j/p := by gcongr
  have hd := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith : -(Real.pi/2) ≤ Real.pi*k/p) hb hc
  have he := Real.sin_pos_of_pos_of_lt_pi ha (by linarith : Real.pi*k/p < Real.pi)
  exact one_div_le_one_div_of_le (mul_pos hp he) (mul_le_mul_of_nonneg_left hd hp.le)

theorem endpoint_far_sine {p : ℝ} {m N : ℕ} (t : ℝ) (hp : 0 < p) (hm : 0 < m)
    (hspan : ∀ i < N, 2*((m+i : ℕ) : ℝ) ≤ p) (hs : 0 < |Real.sin t|) :
    |endpoint p m N t| ≤ (1/(2*(m : ℝ)))*(1/|Real.sin t|) := by
  by_cases hz : N = 0
  · subst N; simp only [endpoint, range_zero, sum_empty, abs_zero]; positivity
  have hN : 0 < N := Nat.pos_of_ne_zero hz
  let v := fun i : ℕ => if i < N then weight p (m+i) else 0
  let g := fun i : ℕ => Real.sin (((m+i : ℕ) : ℝ) * (2*t))
  have hv : ∀ i < N, v (i+1) ≤ v i := by
    intro i hi
    by_cases hj : i+1 < N
    · simp only [v, ite_eq_left hi, ite_eq_left hj]
      exact weight_antitone hp (by omega) (by omega) (hspan _ hj)
    · simp only [v, ite_eq_left hi, ite_eq_right hj]
      exact (weight_spec hp (by omega) (hspan _ hi)).1.le
  have hg (j : ℕ) (_hj : j ≤ N) : |∑ i ∈ range j, g i| ≤ 1/|Real.sin t| := by
    have heq (i : ℕ) : g i = Real.sin ((m:ℝ)*(2*t)+(i:ℝ)*(2*t)) := by
      dsimp [g]; congr 1; push_cast; ring
    simp only [heq]
    exact sine_interval_abs _ _ _ hs
  have hsum : endpoint p m N t = ∑ i ∈ range N, v i * g i := by
    unfold endpoint
    apply sum_congr rfl
    intro i hi
    simp [v, g, mem_range.mp hi]
  rw [hsum]
  have hw := weighted_partial_bound v g N (1/|Real.sin t|) hv (by simp [v]) hg
  have hweight : weight p m ≤ 1/(2*(m : ℝ)) := (weight_spec hp hm (by simpa using hspan 0 hN)).2
  exact hw.trans (mul_le_mul_of_nonneg_right (by simpa [v, hN] using hweight) (by positivity))

theorem endpoint_near {p : ℝ} {m N : ℕ} (t : ℝ) (hp : 0 < p) (hm : 0 < m)
    (hspan : ∀ i < N, 2*((m+i : ℕ) : ℝ) ≤ p) :
    |endpoint p m N t| ≤ 1 + Real.log N := by
  calc
    |endpoint p m N t| ≤ ∑ i ∈ range N, |weight p (m+i) * Real.sin (((m+i : ℕ) : ℝ) * (2*t))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range N, 1/((i : ℝ)+1) := by
      apply sum_le_sum
      intro i hi
      obtain ⟨hwpos, hw⟩ := weight_spec hp (by omega : 0 < m+i) (hspan i (mem_range.mp hi))
      rw [abs_mul, abs_of_nonneg hwpos.le]
      have hsin : |Real.sin (((m+i : ℕ) : ℝ) * (2*t))| ≤ 1 :=
        abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
      calc
        _ ≤ weight p (m+i) * 1 := mul_le_mul_of_nonneg_left hsin hwpos.le
        _ ≤ 1/((i:ℝ)+1) := by
          rw [mul_one]
          apply hw.trans (one_div_le_one_div_of_le (by positivity) ?_)
          exact_mod_cast (show i+1 ≤ 2*(m+i) by omega)
    _ = (harmonic N : ℝ) := by simp [harmonic, one_div]
    _ ≤ 1+Real.log N := harmonic_le_one_add_log N

/-- A lift `z` is chosen so that `|u-z*p| ≤ p/2`. Other nearest lifts at a tie also work. -/
theorem chord_of_lift {p u : ℝ} (z : ℤ) (hp : 0 < p) (hd : |u-(z:ℝ)*p| ≤ p/2) :
    2*|u-(z:ℝ)*p|/p ≤ |Real.sin (Real.pi*u/p)| := by
  let a := Real.pi*(u-(z:ℝ)*p)/p
  have ha : |a| = Real.pi*|u-(z:ℝ)*p|/p := by
    simp [a, abs_div, abs_mul, abs_of_pos hp, abs_of_pos Real.pi_pos]
  have hsmall : |a| ≤ Real.pi/2 := by
    rw [ha, div_le_iff₀ hp]; nlinarith [mul_le_mul_of_nonneg_left hd Real.pi_pos.le]
  have hj := Real.mul_abs_le_abs_sin hsmall
  have he : Real.pi*u/p = a+(z:ℝ)*Real.pi := by dsimp [a]; field_simp; ring
  rw [he, Real.sin_add_int_mul_pi, abs_mul, abs_zpow]
  simp only [abs_neg, abs_one, one_zpow, one_mul]
  rw [ha] at hj
  convert hj using 1; field_simp

theorem endpoint_far {p u : ℝ} {m N : ℕ} (z : ℤ) (hp : 0 < p) (hm : 0 < m)
    (hspan : ∀ i < N, 2*((m+i : ℕ) : ℝ) ≤ p)
    (hd : |u-(z:ℝ)*p| ≤ p/2) (hdpos : 0 < |u-(z:ℝ)*p|) :
    |endpoint p m N (Real.pi*u/p)| ≤ p/(4*(m:ℝ)*|u-(z:ℝ)*p|) := by
  have hch := chord_of_lift z hp hd
  have hpositive : 0 < 2*|u-(z:ℝ)*p|/p := by positivity
  have htail := endpoint_far_sine (Real.pi*u/p) hp hm hspan (hpositive.trans_le hch)
  refine htail.trans ?_
  calc
    _ ≤ (1/(2*(m:ℝ)))*(1/(2*|u-(z:ℝ)*p|/p)) := by
      exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hpositive hch) (by positivity)
    _ = _ := by field_simp; ring

theorem high_fold {p h K : ℕ} (hp : p = 2*h+1) (f : ℕ → ℝ)
    (hsym : ∀ k, 0 < k → k < p → f (p-k) = f k) :
    ∑ k ∈ (Ico 1 p).filter (fun k => K < min k (p-k)), f k =
      2*∑ j ∈ range (h-K), f (K+1+j) := by
  let s := range (h-K)
  let lo := fun j : ℕ => K+1+j
  let hi := fun j : ℕ => p-(K+1+j)
  have split : (Ico 1 p).filter (fun k => K < min k (p-k)) = s.image lo ∪ s.image hi := by
    ext k
    simp only [mem_filter, mem_Ico, lt_min_iff, mem_union, mem_image, s, mem_range, lo, hi]
    constructor
    · rintro ⟨⟨h1,h2⟩,h3,h4⟩
      by_cases hsmall : k ≤ h
      · exact Or.inl ⟨k-(K+1), by omega, by omega⟩
      · exact Or.inr ⟨p-k-(K+1), by omega, by omega⟩
    · rintro (⟨j, hj, he⟩ | ⟨j, hj, he⟩) <;> omega
  have hd : Disjoint (s.image lo) (s.image hi) := by
    apply disjoint_left.mpr
    intro k hk1 hk2
    obtain ⟨a, ha, ea⟩ := mem_image.mp hk1
    obtain ⟨b, hb, eb⟩ := mem_image.mp hk2
    simp only [s, mem_range] at ha hb
    dsimp [lo, hi] at ea eb
    omega
  have hinjl : Set.InjOn lo (↑s) := by intro a ha b hb he; dsimp [lo] at he; omega
  have hinjh : Set.InjOn hi (↑s) := by
    intro a ha b hb he
    change a ∈ range (h-K) at ha
    change b ∈ range (h-K) at hb
    rw [mem_range] at ha hb
    dsimp [hi] at he; omega
  have he : ∑ j ∈ s, f (hi j) = ∑ j ∈ s, f (lo j) := by
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    exact hsym (K+1+j) (by omega) (by omega)
  rw [split, sum_union hd, sum_image hinjl, sum_image hinjh, he, two_mul]

theorem cos_reflect {p k : ℕ} (n r : ℕ) (hp : 0 < p) (hk : k ≤ p) :
    Real.cos (2*Real.pi*((p-k : ℕ) : ℝ)*((n : ℝ)-r)/p) =
      Real.cos (2*Real.pi*k*((n : ℝ)-r)/p) := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Nat.cast_sub hk]
  have he : 2*Real.pi*((p : ℝ)-k)*((n : ℝ)-r)/p =
      (((n:ℤ)-(r:ℤ) : ℤ) : ℝ)*(2*Real.pi) - 2*Real.pi*k*((n : ℝ)-r)/p := by
    push_cast; field_simp
  rw [he, Real.cos_int_mul_two_pi_sub]

theorem cosine_one_frequency {p : ℝ} {k : ℕ} (L r : ℝ) (N : ℕ) (hp : 0 < p)
    (hk : 0 < k) (hhalf : 2*(k : ℝ) ≤ p) :
    2*(∑ j ∈ range N, Real.cos (2*Real.pi*k*(L+(j:ℝ)-r)/p))/p =
      weight p k * (Real.sin ((k : ℝ)*(2*(Real.pi*(L+N-1/2-r)/p))) -
        Real.sin ((k : ℝ)*(2*(Real.pi*(L-1/2-r)/p)))) := by
  let t := Real.pi*k/p
  let b := (L-r)*(2*t)
  have he (j : ℕ) : 2*Real.pi*k*(L+(j:ℝ)-r)/p = b+(j:ℝ)*(2*t) := by dsimp [b,t]; ring
  have hU : b+(N:ℝ)*(2*t)-t = (k : ℝ)*(2*(Real.pi*(L+N-1/2-r)/p)) := by dsimp [b,t]; ring
  have hL : b-t = (k : ℝ)*(2*(Real.pi*(L-1/2-r)/p)) := by dsimp [b,t]; ring
  have hs : Real.sin t ≠ 0 := by
    intro hz
    have hw := (weight_spec hp hk hhalf).1
    change 0 < 1/(p*Real.sin t) at hw
    simp [hz] at hw
  have hweight (S : ℝ) : 2*S/p = weight p k * (2*Real.sin t*S) := by
    change _ = (1/(p*Real.sin t))*_
    field_simp
  simp only [he]
  calc
    _ = weight p k * (2*Real.sin t*(∑ j ∈ range N, Real.cos (b+(j:ℝ)*(2*t)))) := hweight _
    _ = _ := by rw [cosine_interval, hU, hL]

/-- The complete high-band contribution of one root, normalized as in the registry. -/
theorem high_window_endpoint {p h K : ℕ} (L r N : ℕ) (hp : p = 2*h+1) :
    (∑ k ∈ (Ico 1 p).filter (fun k => K < min k (p-k)),
      (∑ j ∈ range N, Real.cos (2*Real.pi*k*(((L+j : ℕ) : ℝ)-r)/p))/(p:ℝ)) =
    endpoint p (K+1) (h-K) (Real.pi*((L:ℝ)+N-1/2-r)/p) -
    endpoint p (K+1) (h-K) (Real.pi*((L:ℝ)-1/2-r)/p) := by
  have hp0 : 0 < p := by omega
  have hp' : 0 < (p:ℝ) := by exact_mod_cast hp0
  let f := fun k : ℕ => (∑ j ∈ range N, Real.cos (2*Real.pi*k*(((L+j : ℕ) : ℝ)-r)/p))/(p:ℝ)
  have hsym (k : ℕ) (_ : 0 < k) (hkp : k < p) : f (p-k) = f k := by
    dsimp only [f]
    apply congrArg (fun y : ℝ => y/(p:ℝ))
    apply sum_congr rfl
    intro j _
    exact cos_reflect (L+j) r hp0 hkp.le
  change (∑ k ∈ _, f k) = _
  rw [high_fold hp f hsym, Finset.mul_sum]
  unfold endpoint
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  have hk : 2*((K+1+i : ℕ) : ℝ) ≤ p := by exact_mod_cast (show 2*(K+1+i) ≤ p by omega)
  have he := cosine_one_frequency (p:=(p:ℝ)) (k:=K+1+i) L r N hp' (by omega) hk
  dsimp [f]
  push_cast
  push_cast at he
  rw [← mul_sub]
  convert he using 1; ring

noncomputable def boundaryTerm (p r : ℕ) (e : ℝ) : ℝ :=
  endpoint p (p.sqrt+1) (p/2-p.sqrt) (Real.pi*(e-r)/p)

theorem span_high (p i : ℕ) (hi : i < p/2-p.sqrt) :
    2*((p.sqrt+1+i : ℕ) : ℝ) ≤ p := by
  exact_mod_cast (show 2*(p.sqrt+1+i) ≤ p by omega)

theorem boundary_near (p r : ℕ) (e : ℝ) (hp : 0 < p) :
    |boundaryTerm p r e| ≤ 1+Real.log (p:ℝ) := by
  by_cases hz : p/2-p.sqrt = 0
  · simp only [boundaryTerm, hz, endpoint, range_zero, sum_empty, abs_zero]
    have := Real.log_nonneg (show (1:ℝ) ≤ p by exact_mod_cast hp)
    linarith
  · have hN : 0 < p/2-p.sqrt := Nat.pos_of_ne_zero hz
    have hlog : Real.log ((p/2-p.sqrt:ℕ):ℝ) ≤ Real.log (p:ℝ) :=
      Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast (show p/2-p.sqrt ≤ p by omega))
    exact (endpoint_near _ (by exact_mod_cast hp) (by omega : 0 < p.sqrt+1) (span_high p)).trans
      (by linarith)

theorem boundary_far (p r : ℕ) (e : ℝ) (n : ℤ) (hp : 0 < p)
    (hn : n ≡ (r:ℤ) [ZMOD (p:ℤ)]) (hd : |e-(n:ℝ)| ≤ (p:ℝ)/2)
    (hpos : 0 < |e-(n:ℝ)|) :
    |boundaryTerm p r e| ≤ Real.sqrt (p:ℝ) / |e-(n:ℝ)| := by
  obtain ⟨z,hz⟩ := Int.modEq_iff_dvd.mp hn
  have hn' : (n:ℝ) = (r:ℝ)+((-z : ℤ):ℝ)*(p:ℝ) := by
    exact_mod_cast (show n = (r:ℤ)+(-z)*(p:ℤ) by linarith only [hz, mul_comm (p:ℤ) z])
  have heq : (e-(r:ℝ))-((-z : ℤ):ℝ)*(p:ℝ) = e-(n:ℝ) := by rw [hn']; ring
  have hf := endpoint_far (m:=p.sqrt+1) (N:=p/2-p.sqrt) (u:=e-r) (-z)
    (by exact_mod_cast hp : 0 < (p:ℝ)) (by omega) (span_high p) (by rwa [heq]) (by rwa [heq])
  rw [heq] at hf
  have hs1 := Nat.succ_le_succ_sqrt' p
  have hs2 : (p:ℝ)+1 ≤ ((p.sqrt:ℝ)+1)^2 := by exact_mod_cast hs1
  have hle : Real.sqrt (p:ℝ) ≤ ((p.sqrt:ℝ)+1) :=
    (Real.sqrt_le_iff).mpr ⟨by positivity, by linarith⟩
  refine hf.trans ?_
  rw [Nat.cast_add, Nat.cast_one]
  apply (div_le_div_iff₀ (by positivity) hpos).mpr
  have hr := Real.sq_sqrt (Nat.cast_nonneg p)
  have hmul := mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg (p:ℝ))
  have haux : (p:ℝ) ≤ Real.sqrt (p:ℝ) * (4*((p.sqrt:ℝ)+1)) := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg (p:ℝ)) (show 0 ≤ (p.sqrt:ℝ)+1 by positivity)]
  nlinarith only [mul_le_mul_of_nonneg_right haux hpos.le]

theorem high_Icc_ends (p r A B : ℕ) (hpOdd : p = 2*(p/2)+1) (hAB : A ≤ B) :
    (∑ k ∈ (Ico 1 p).filter (fun k => p.sqrt < min k (p-k)),
      (∑ n ∈ Icc A B, Real.cos (2*Real.pi*k*((n:ℝ)-r)/p))/(p:ℝ)) =
    boundaryTerm p r ((B:ℝ)+1/2) - boundaryTerm p r ((A:ℝ)-1/2) := by
  have hset : Icc A B = (range (B+1-A)).image (fun j => A+j) := by
    ext n
    simp only [mem_Icc, mem_image, mem_range]
    constructor
    · rintro ⟨hlo,hhi⟩; exact ⟨n-A, by omega, by omega⟩
    · rintro ⟨j, hj, he⟩; omega
  have hconv (k : ℕ) : (∑ n ∈ Icc A B, Real.cos (2*Real.pi*k*((n:ℝ)-r)/p)) =
      ∑ j ∈ range (B+1-A), Real.cos (2*Real.pi*k*(((A+j:ℕ):ℝ)-r)/p) := by
    rw [hset, sum_image (fun a _ b _ hab => by omega)]
  simp only [hconv]
  rw [high_window_endpoint (h:=p/2) A r (B+1-A) hpOdd]
  unfold boundaryTerm
  have he : (A:ℝ) + ((B+1-A:ℕ):ℝ) - 1/2 = (B:ℝ)+1/2 := by
    rw [Nat.cast_sub (show A ≤ B+1 by omega), Nat.cast_add, Nat.cast_one]; ring
  rw [he]

/-- Commute the actual high-frequency and root sums before applying the one-root identity. -/
theorem high_Icc_roots (p A B : ℕ) (R : Finset ℕ) (hpOdd : p = 2*(p/2)+1) (hAB : A ≤ B) :
    (∑ k ∈ (Ico 1 p).filter (fun k => p.sqrt < min k (p-k)),
      (∑ r ∈ R, ∑ n ∈ Icc A B, Real.cos (2*Real.pi*k*((n:ℝ)-r)/p))/(p:ℝ)) * Real.log p =
      ∑ r ∈ R, (boundaryTerm p r ((B:ℝ)+1/2) - boundaryTerm p r ((A:ℝ)-1/2)) * Real.log p := by
  have hdist (k : ℕ) :
      (∑ r ∈ R, ∑ n ∈ Icc A B, Real.cos (2*Real.pi*k*((n:ℝ)-r)/p))/(p:ℝ) =
      ∑ r ∈ R, (∑ n ∈ Icc A B, Real.cos (2*Real.pi*k*((n:ℝ)-r)/p))/(p:ℝ) := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
  simp only [hdist]
  rw [Finset.sum_comm, Finset.sum_mul]
  apply sum_congr rfl
  intro r _
  rw [high_Icc_ends p r A B hpOdd hAB]

end QP0052Fourier

/-! Auxiliary finite counting estimates for the high-frequency root window. -/

namespace QP0052.Counting

variable {ofs : ℕ} [hofs : Fact (1 ≤ ofs)]

/-- Residues of the roots of `n² + ofs` modulo `m`. -/
def roots (ofs m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun n => m ∣ n ^ 2 + ofs)

theorem sq_add_ofs_pos (n : ℕ) : 0 < n ^ 2 + ofs :=
  Nat.lt_of_lt_of_le (show 0 < ofs by have := hofs.out; omega) (Nat.le_add_left ofs (n ^ 2))

theorem mod_mem_roots {n m : ℕ} (hm : 0 < m) (h : m ∣ n^2+ofs) : n % m ∈ roots ofs m := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n hm), ?_⟩
  have he : Nat.ModEq m ((n % m)^2+ofs) (n^2+ofs) :=
    Nat.ModEq.add_right ofs (Nat.ModEq.pow 2 (Nat.mod_modEq n m))
  exact Nat.modEq_zero_iff_dvd.mp (he.trans h.modEq_zero_nat)

theorem roots_mul_le {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b) :
    (roots ofs (a*b)).card ≤ (roots ofs a).card * (roots ofs b).card := by
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun n : ℕ => (n % a, n % b))
  · intro n hn
    have hd := (Finset.mem_filter.mp hn).2
    exact Finset.mem_product.mpr
      ⟨mod_mem_roots ha ((dvd_mul_right a b).trans hd),
        mod_mem_roots hb ((dvd_mul_left b a).trans hd)⟩
  · intro n hn r hr h
    have hnr : Nat.ModEq (a*b) n r := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
      ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    exact hnr.eq_of_lt_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)

theorem roots_prime_power_le {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (roots ofs (p^k)).card ≤ 4 * ofs :=
  QPShift.rootsA_prime_power_le hofs.out hp hk

theorem roots_card_le_two_pow (m : ℕ) :
    (roots ofs m).card ≤ (4 * ofs) ^ m.primeFactors.card := by
  refine Nat.recOnPosPrimePosCoprime (motive := fun m => (roots ofs m).card ≤ (4 * ofs) ^ m.primeFactors.card)
    ?_ ?_ ?_ ?_ m
  · intro p k hp hk
    rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.card_singleton, pow_one]
    exact roots_prime_power_le hp hk
  · simp [roots]
  · simp [roots]
  · intro a b ha hb hc ihA ihB
    rw [hc.primeFactors_mul, Finset.card_union_of_disjoint hc.disjoint_primeFactors, pow_add]
    exact (roots_mul_le (by omega) (by omega) hc).trans (Nat.mul_le_mul ihA ihB)

private theorem prod_prime_subset_le {m : ℕ} (hm : 0 < m) (s : Finset ℕ) (hs : s ⊆ m.primeFactors) :
    (∏ p ∈ s, p) ≤ m := by
  refine le_trans (Finset.prod_le_prod_of_subset_of_one_le hs ?_) (Nat.le_of_dvd hm m.prod_primeFactors_dvd)
  intro p hp _
  exact (Nat.prime_of_mem_primeFactors hp).one_lt.le

/-- Uniform integral form of the subpower bound for the number of roots. -/
theorem roots_pow_bound {m : ℕ} (hm : 0 < m) (k : ℕ) :
    (roots ofs m).card ^ k ≤ ((4 * ofs)^k)^((4 * ofs)^k) * m := by
  classical
  let B : ℕ := (4 * ofs)^k
  let small := m.primeFactors.filter (fun p => p < B)
  let large := m.primeFactors.filter (fun p => ¬ p < B)
  have hs : small.card ≤ B := by
    have hsub : small ⊆ Finset.range B := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa using Finset.card_le_card hsub
  have hl : B ^ large.card ≤ m := by
    refine (Finset.pow_card_le_prod large (fun p => p) B ?_).trans ?_
    · intro p hp
      exact Nat.le_of_not_gt (Finset.mem_filter.mp hp).2
    · exact prod_prime_subset_le hm large (by intro p hp; exact (Finset.mem_filter.mp hp).1)
  have hcards : small.card + large.card = m.primeFactors.card :=
    Finset.card_filter_add_card_filter_not (s := m.primeFactors) (fun p => p < B)
  have hpos : 0 < B := pow_pos (by have := hofs.out; omega) _
  calc
    (roots ofs m).card ^ k ≤ ((4 * ofs) ^ m.primeFactors.card)^k := Nat.pow_le_pow_left (roots_card_le_two_pow m) k
    _ = B ^ m.primeFactors.card := by
      show ((4 * ofs) ^ m.primeFactors.card)^k = ((4 * ofs)^k) ^ m.primeFactors.card
      rw [← pow_mul, ← pow_mul, Nat.mul_comm m.primeFactors.card k]
    _ = B ^ small.card * B ^ large.card := by rw [← hcards, pow_add]
    _ ≤ B^B * m := Nat.mul_le_mul (Nat.pow_le_pow_right hpos hs) hl

/-- For each modulus, rounding the interval ends costs at most two quotient bins. -/
theorem interval_roots_bound (s : Finset ℕ) (L W m : ℕ) (hm : 0 < m)
    (hmem : ∀ n ∈ s, L ≤ n ∧ n ≤ L+W ∧ m ∣ n^2+ofs) :
    s.card ≤ (W/m+2) * (roots ofs m).card := by
  classical
  have htop : (L+W) / m < L/m + W/m + 2 := by
    apply (Nat.div_lt_iff_lt_mul hm).2
    have hL := Nat.div_add_mod L m
    have hW := Nat.div_add_mod W m
    nlinarith only [hL, hW, Nat.mod_lt L hm, Nat.mod_lt W hm]
  rw [← Finset.card_range (W/m+2), ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun n : ℕ => (n / m - L / m, n % m))
  · intro n hn
    obtain ⟨hL, hW, hd⟩ := hmem n hn
    have h1 : L/m ≤ n/m := Nat.div_le_div_right hL
    have h2 : n/m ≤ (L+W)/m := Nat.div_le_div_right hW
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (show n/m - L/m < W/m+2 by omega), mod_mem_roots hm hd⟩
  · intro a ha b hb heq
    have h1 : a / m - L / m = b / m - L / m := congrArg Prod.fst heq
    have ha' : L/m ≤ a/m := Nat.div_le_div_right (hmem a ha).1
    have hb' : L/m ≤ b/m := Nat.div_le_div_right (hmem b hb).1
    exact Nat.ext_div_modEq (by omega : a / m = b / m) (congrArg Prod.snd heq)

/-- Count a family of pairs (argument, prime) by its cofactor and then by the
argument residue. The real-variable localization supplies the bounds L and W. -/
theorem cofactor_count {ι : Type*} [DecidableEq ι] (S : Finset ι) (K : Finset ℕ)
    (n p m : ι → ℕ) (L : ℕ → ℕ) (W : ℕ)
    (hkey : ∀ i ∈ S, ∀ j ∈ S, n i = n j → p i = p j → i = j)
    (hK : ∀ i ∈ S, m i ∈ K) (hpos : ∀ q ∈ K, 0 < q)
    (heq : ∀ i ∈ S, m i * p i = n i ^2+ofs)
    (hwin : ∀ i ∈ S, L (m i) ≤ n i ∧ n i ≤ L (m i) + W) :
    S.card ≤ ∑ q ∈ K, (W/q + 2) * (roots ofs q).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := m) hK]
  apply Finset.sum_le_sum
  intro q hq
  let F := S.filter (fun i => m i = q)
  have hFm (i : ι) (hi : i ∈ F) : i ∈ S ∧ m i = q := Finset.mem_filter.mp hi
  have hsize : F.card ≤ (F.image n).card := by
    apply Finset.card_le_card_of_injOn n
    · intro i hi
      exact Finset.mem_image_of_mem _ hi
    · intro i hi j hj hn
      obtain ⟨hSi, hmi⟩ := hFm i hi
      obtain ⟨hSj, hmj⟩ := hFm j hj
      apply hkey i hSi j hSj hn
      apply Nat.eq_of_mul_eq_mul_left (hpos q hq)
      calc
        q * p i = n i ^2+ofs := by simpa only [hmi] using heq i hSi
        _ = n j ^2+ofs := by rw [hn]
        _ = q * p j := by simpa only [hmj] using (heq j hSj).symm
  refine hsize.trans (interval_roots_bound (F.image n) (L q) W q (hpos q hq) ?_)
  intro z hz
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hSi, hmi⟩ := hFm i hi
  have hw := hwin i hSi
  rw [hmi] at hw
  exact ⟨hw.1, hw.2, ⟨p i, by simpa only [hmi] using (heq i hSi).symm⟩⟩

/-- A single integer below Q³ has at most two distinct prime factors ≥ Q. -/
theorem large_primes_le_two (M Q : ℕ) (hM : 0 < M) (hQ : 1 < Q) (hsmall : M < Q^3) :
    (M.primeFactors.filter (fun p => Q ≤ p)).card ≤ 2 := by
  classical
  let S := M.primeFactors.filter (fun p => Q ≤ p)
  have hpow : Q^S.card ≤ M :=
    (Finset.pow_card_le_prod S (fun p => p) Q (fun p hp => (Finset.mem_filter.mp hp).2)).trans
      (prod_prime_subset_le hM S (by intro p hp; exact (Finset.mem_filter.mp hp).1))
  change S.card ≤ 2
  by_contra! h
  have hle := Nat.pow_le_pow_right (show 0 < Q by omega) (show 3 ≤ S.card by omega)
  omega

/-- Count fixed-endpoint events by the nearby integer, with two prime choices per integer. -/
theorem fixed_endpoint_count {ι : Type*} [DecidableEq ι] (S : Finset ι) (A : Finset ℕ)
    (n p : ι → ℕ) (Q : ℕ) (hQ : 1 < Q)
    (hkey : ∀ i ∈ S, ∀ j ∈ S, n i = n j → p i = p j → i = j)
    (hA : ∀ i ∈ S, n i ∈ A) (hsize : ∀ a ∈ A, a^2+ofs < Q^3)
    (hprime : ∀ i ∈ S, (p i).Prime ∧ Q ≤ p i ∧ p i ∣ n i^2+ofs) :
    S.card ≤ A.card * 2 := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := n) hA]
  have hbound : ∀ a ∈ A, (S.filter fun i => n i = a).card ≤ 2 := by
    intro a ha
    refine le_trans ?_ (large_primes_le_two (a^2+ofs) Q (sq_add_ofs_pos a) hQ (hsize a ha))
    apply Finset.card_le_card_of_injOn p
    · intro i hi
      obtain ⟨hSi, hni⟩ := Finset.mem_filter.mp hi
      obtain ⟨hpp, hQi, hd⟩ := hprime i hSi
      rw [hni] at hd
      exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp, hd, (sq_add_ofs_pos _).ne'⟩, hQi⟩
    · intro i hi j hj hp
      obtain ⟨hSi, hii⟩ := Finset.mem_filter.mp hi
      obtain ⟨hSj, hjj⟩ := Finset.mem_filter.mp hj
      exact hkey i hSi j hSj (hii.trans hjj.symm) hp
  calc
    _ ≤ ∑ _a ∈ A, 2 := Finset.sum_le_sum hbound
    _ = _ := by simp

/-- Extract the fixed 256-th root before passing to real scales. -/
theorem roots_subpower :
    ∃ A : ℝ, 0 < A ∧ ∀ m : ℕ, 0 < m →
      ((roots ofs m).card : ℝ) ≤ A * (m : ℝ) ^ (1 / 256 : ℝ) := by
  let k : ℕ := 256
  let B : ℕ := (4 * ofs)^k
  let C : ℕ := B^B
  have hB : 0 < B := pow_pos (by have := hofs.out; omega) _
  have hC : 0 < C := pow_pos hB _
  have hc : 0 < (C : ℝ) := Nat.cast_pos.mpr hC
  refine ⟨(C : ℝ) ^ (1/256 : ℝ), Real.rpow_pos_of_pos hc _, ?_⟩
  intro m hm
  have hn : (roots ofs m).card^k ≤ C*m := roots_pow_bound hm k
  have hr : ((roots ofs m).card : ℝ)^k ≤ (C : ℝ)*(m : ℝ) := by exact_mod_cast hn
  calc
    ((roots ofs m).card : ℝ) = (((roots ofs m).card : ℝ)^k)^(1/256 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num [k]
    _ ≤ ((C : ℝ)*(m : ℝ))^(1/256 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hr (by norm_num)
    _ = _ := Real.mul_rpow hc.le (Nat.cast_nonneg _)

/-- Count a natural finset controlled above by a positive real scale. -/
private theorem card_le_top (K : Finset ℕ) {Y : ℝ} (hY : 0 ≤ Y)
    (hk : ∀ m ∈ K, (m : ℝ) ≤ Y) : (K.card : ℝ) ≤ Y+1 := by
  classical
  by_cases h : K.Nonempty
  · have hs : K ⊆ Finset.range (K.max' h + 1) := by
      intro m hm
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' _ _ hm))
    have hc : K.card ≤ K.max' h + 1 := by simpa using Finset.card_le_card hs
    have hh : (K.card : ℝ) ≤ (K.max' h : ℝ) + 1 := by exact_mod_cast hc
    linarith [hk _ (Finset.max'_mem K h)]
  · have he := Finset.not_nonempty_iff_eq_empty.mp h
    simpa only [he, Finset.card_empty, Nat.cast_zero] using (show (0 : ℝ) ≤ Y+1 by linarith)

/-- Counts localized moving-boundary events. All constants are independent of
the real scale X and the finite family S. For QP-0052 take β=2−1.32301. -/
theorem cofactor_count_power (c C D : ℝ) (hc : 0 < c) (hC : 0 < C) (hD : 0 ≤ D) :
    ∃ E : ℝ, 0 < E ∧
      ∀ {ι : Type} [DecidableEq ι] (S : Finset ι) (K : Finset ℕ) (n p m : ι → ℕ)
        (L : ℕ → ℕ) (W : ℕ) (X β : ℝ), 1 ≤ X → 0 ≤ β → β ≤ 99/100 →
        (∀ i ∈ S, ∀ j ∈ S, n i = n j → p i = p j → i = j) →
        (∀ i ∈ S, m i ∈ K) →
        (∀ q ∈ K, c * X^β ≤ (q : ℝ) ∧ (q : ℝ) ≤ C * X^β) →
        (∀ i ∈ S, m i * p i = n i^2+ofs) →
        (∀ i ∈ S, L (m i) ≤ n i ∧ n i ≤ L (m i)+W) →
        (W : ℝ) ≤ D * X^(99/100 : ℝ) →
        (S.card : ℝ) ≤ E * X^(995/1000 : ℝ) := by
  classical
  obtain ⟨A, hA, hroot⟩ := roots_subpower (ofs := ofs)
  let e : ℝ := 1/256
  let V : ℝ := A*C^e
  have hV : 0 < V := mul_pos hA (Real.rpow_pos_of_pos hC _)
  have hDc : 0 ≤ D/c := div_nonneg hD hc.le
  refine ⟨(C+1)*(D/c+2)*V, mul_pos (mul_pos (by linarith) (by linarith)) hV, ?_⟩
  intro ι inst S K n p m L W X β hX hβ hβ' hkey hK hk heq hwin hW
  let R : ℝ := X^β
  have hX0 : 0 < X := by linarith
  have hR1 : 1 ≤ R := Real.one_le_rpow hX hβ
  have hR : 0 < R := by linarith
  have he : 0 ≤ e := by norm_num [e]
  have hRX : R ≤ X := by
    calc
      R ≤ X^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
      _ = X := Real.rpow_one _
  have hR99 : R ≤ X^(99/100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX hβ'
  have hpos (q : ℕ) (hq : q ∈ K) : 0 < q := by
    have hp : 0 < (q : ℝ) := (mul_pos hc hR).trans_le (hk q hq).1
    exact Nat.cast_pos.mp hp
  have hcard : (K.card : ℝ) ≤ (C+1)*R := by
    have H := card_le_top K (mul_nonneg hC.le hR.le) (fun q hq => (hk q hq).2)
    linarith
  let U : ℝ := (W : ℝ)/(c*R)+2
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hXe : 0 < X^e := Real.rpow_pos_of_pos hX0 _
  have hsum := cofactor_count S K n p m L W hkey hK hpos heq hwin
  have hsum' : (S.card : ℝ) ≤ ∑ q ∈ K, (((W/q : ℕ) : ℝ)+2)*((roots ofs q).card : ℝ) := by
    exact_mod_cast hsum
  have hu (q : ℕ) (hq : q ∈ K) : (((W/q : ℕ) : ℝ)+2) ≤ U := by
    have hq' : 0 < (q : ℝ) := Nat.cast_pos.mpr (hpos q hq)
    have hd : ((W/q : ℕ) : ℝ) ≤ (W : ℝ)/q := by
      apply (le_div_iff₀ hq').mpr
      exact_mod_cast Nat.div_mul_le_self W q
    have hd' := div_le_div_of_nonneg_left (Nat.cast_nonneg W) (mul_pos hc hR) (hk q hq).1
    dsimp [U]
    linarith [hd.trans hd']
  have hv (q : ℕ) (hq : q ∈ K) : ((roots ofs q).card : ℝ) ≤ V*X^e := by
    have hqX := (hk q hq).2.trans (mul_le_mul_of_nonneg_left hRX hC.le)
    calc
      ((roots ofs q).card : ℝ) ≤ A*(q : ℝ)^e := hroot q (hpos q hq)
      _ ≤ A*(C*X)^e := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hqX he) hA.le
      _ = V*X^e := by rw [Real.mul_rpow hC.le hX0.le]; dsimp [V]; ring
  have hadd : (W : ℝ)/c+2*R ≤ (D/c+2)*X^(99/100 : ℝ) := by
    have hd := div_le_div_of_nonneg_right hW hc.le
    calc
      (W : ℝ)/c+2*R ≤ (D*X^(99/100 : ℝ))/c+2*X^(99/100 : ℝ) := by linarith
      _ = _ := by ring
  calc
    (S.card : ℝ) ≤ _ := hsum'
    _ ≤ ∑ _q ∈ K, U*(V*X^e) := Finset.sum_le_sum fun q hq =>
      mul_le_mul (hu q hq) (hv q hq) (Nat.cast_nonneg _) hU
    _ = (K.card : ℝ)*(U*(V*X^e)) := by simp
    _ ≤ ((C+1)*R)*(U*(V*X^e)) := mul_le_mul_of_nonneg_right hcard
      (mul_nonneg hU (mul_nonneg hV.le hXe.le))
    _ = (C+1)*((W : ℝ)/c+2*R)*(V*X^e) := by
      dsimp [U]
      field_simp [hc.ne', hR.ne']
    _ ≤ (C+1)*((D/c+2)*X^(99/100 : ℝ))*(V*X^e) := by
      have hC1 : 0 ≤ C+1 := by linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hadd hC1)
        (mul_nonneg hV.le hXe.le)
    _ = ((C+1)*(D/c+2)*V)*X^((99/100 : ℝ)+e) := by
      rw [Real.rpow_add hX0]; ring
    _ ≤ ((C+1)*(D/c+2)*V)*X^(995/1000 : ℝ) := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX (by norm_num [e]))
      positivity

end QP0052.Counting

namespace QuadraticHigh

variable {ofs U V : ℕ} [hofs : Fact (1 ≤ ofs)] [hUV : ShiftData U V]


noncomputable def cutoff (U V p : ℕ) : ℝ := (p : ℝ) ^ ((V : ℝ) / U)
noncomputable def start (U V x p : ℕ) : ℕ := max (x+1) ⌈cutoff U V p⌉₊
noncomputable def lift (e : ℝ) (p r : ℕ) : ℤ :=
  (r : ℤ) + round ((e - r) / p) * (p : ℤ)

theorem cutoff_nonneg (p : ℕ) : 0 ≤ cutoff U V p :=
  Real.rpow_nonneg (Nat.cast_nonneg p) _

theorem cutoff_pow (p : ℕ) : (cutoff U V p) ^ U = (p : ℝ) ^ V := by
  unfold cutoff
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p),
    div_mul_cancel₀ _ (ShiftData.U_pos' (V := V)).ne', Real.rpow_natCast]

theorem cutoff_iff (n p : ℕ) : cutoff U V p ≤ (n : ℝ) ↔ p^V ≤ n^U := by
  have h := Real.rpow_le_rpow_iff (cutoff_nonneg (U := U) (V := V) p) (Nat.cast_nonneg n)
    (show (0 : ℝ) < (U : ℕ) from ShiftData.U_pos' (V := V))
  rw [Real.rpow_natCast, Real.rpow_natCast, cutoff_pow] at h
  exact h.symm.trans (by exact_mod_cast (Iff.rfl : p^V ≤ n^U ↔ p^V ≤ n^U))

theorem cutoff_exponent (p : ℕ) : (cutoff U V p) ^ ((U : ℝ) / V) = p := by
  unfold cutoff
  rw [← Real.rpow_mul (Nat.cast_nonneg p)]
  have : (V : ℝ) / U * (U / V) = 1 := by
    field_simp [(ShiftData.U_pos' (V := V)).ne', (ShiftData.V_pos' (U := U)).ne']
  rw [this, Real.rpow_one]

theorem window_interval (x p : ℕ) :
    (Finset.Ioc x (2*x)).filter (fun n => p^V ≤ n^U) = Finset.Icc (start U V x p) (2*x) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc, start, max_le_iff,
    Nat.ceil_le, cutoff_iff]
  omega

theorem start_le_top {x p : ℕ} (hx : 1 ≤ x) (hp : p^V ≤ (2*x)^U) :
    start U V x p ≤ 2*x := by
  apply max_le (by omega)
  exact Nat.ceil_le.mpr ((cutoff_iff (2*x) p).mpr hp)

theorem lower_boundary {x p : ℕ} (hs : start U V x p ≠ x+1) :
    x ≤ cutoff U V p ∧ |(start U V x p : ℝ) - 1/2 - cutoff U V p| ≤ 1/2 := by
  have hlt : x+1 < ⌈cutoff U V p⌉₊ := by
    by_contra! h
    exact hs (max_eq_left h)
  have hgt : ((x+1 : ℕ) : ℝ) < cutoff U V p := by
    exact lt_of_not_ge (fun h => (not_lt_of_ge (Nat.ceil_le.mpr h)) hlt)
  have hceil := Nat.le_ceil (cutoff U V p)
  have hc := Nat.ceil_lt_add_one (cutoff_nonneg (U := U) (V := V) p)
  rw [start, max_eq_right hlt.le, abs_le]
  constructor
  · push_cast at hgt
    linarith
  · constructor <;> linarith

theorem lift_dist (e : ℝ) (p r : ℕ) (hp : 0 < p) : |e - lift e p r| ≤ (p : ℝ)/2 := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h := abs_sub_round ((e - r)/(p : ℝ))
  have hm (y : ℝ) : (p : ℝ) * |y| = |(p : ℝ)*y| := by rw [abs_mul, abs_of_pos hp']
  calc
    |e - lift e p r| =
      (p : ℝ) * |(e-r)/p - (round ((e-r)/(p:ℝ)) : ℝ)| := by
        rw [hm]
        congr 1
        unfold lift
        push_cast
        field_simp
        ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h hp'.le]

theorem lift_congr (e : ℝ) (p r : ℕ) :
    lift e p r ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  use -round ((e - r) / p)
  unfold lift
  ring

theorem lift_pos {e : ℝ} {p r : ℕ} {T : ℝ} (hT : T < e)
    (hd : |e - (lift e p r : ℝ)| ≤ T) : 0 < lift e p r := by
  obtain ⟨_, hup⟩ := abs_le.mp hd
  exact_mod_cast (by linarith : (0 : ℝ) < lift e p r)



/-- On the positive half-line exponents between zero and two have this elementary
two-point bound when one argument is one. -/
theorem rpow_dist_one {u g : ℝ} (hu : 0 < u) (hg₀ : 0 ≤ g) (hg₂ : g ≤ 2) :
    |u ^ g - 1| ≤ (u + 1) * |u - 1| := by
  by_cases h : 1 ≤ u
  · have hpow := Real.one_le_rpow h hg₀
    have hsq : u ^ g ≤ u ^ (2 : ℕ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le h hg₂
    rw [abs_of_nonneg (sub_nonneg.mpr hpow), abs_of_nonneg (sub_nonneg.mpr h)]
    nlinarith
  · have h' : u ≤ 1 := le_of_not_ge h
    have hpow := Real.rpow_le_one hu.le h' hg₀
    have hsq : u ^ (2 : ℕ) ≤ u ^ g := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hu h' hg₂
    rw [abs_of_nonpos (sub_nonpos.mpr hpow), abs_of_nonpos (sub_nonpos.mpr h')]
    nlinarith

/-- Move a root near the prime-dependent boundary to an interval depending only
on its cofactor. Here s is the positive real power of the prime and `c` the offset. -/
theorem cofactor_close {n s m a T c : ℝ} (hs : 1 ≤ s)
    (hT : 1 ≤ T) (hTs : T ≤ s/2) (hn : |n - s| ≤ T)
    (ha : 1 ≤ a) (hahi : a ≤ 3/2) (hc0 : 0 ≤ c) (hcT : c ≤ s * T)
    (hprod : m * s ^ a = n ^ 2 + c) :
    |n - m ^ (1 / (2-a))| ≤ 25 * T := by
  have hs0 : 0 < s := by linarith
  have hq : 0 < 2-a := by linarith
  have hg0 : 0 ≤ 1 / (2-a) := by positivity
  have hg2 : 1 / (2-a) ≤ 2 := (div_le_iff₀ hq).mpr (by linarith [ha])
  obtain ⟨hnl, hnr⟩ := abs_le.mp hn
  have hn0 : 0 < n := by linarith
  let u := (n ^ 2 + c) / s ^ 2
  have hu : 0 < u := by dsimp [u]; exact div_pos (by nlinarith) (by positivity)
  have hus : u * s ^ 2 = n ^ 2 + c := by
    dsimp [u]; field_simp
  have hns : n ≤ 3/2 * s := by linarith
  have hcs : c ≤ s ^ 2 / 2 := by nlinarith
  have hu4 : u ≤ 4 := by
    dsimp [u]
    apply (div_le_iff₀ (sq_pos_of_pos hs0)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 3/2*s - n by linarith)
      (show 0 ≤ 3/2*s + n by linarith)]
  have hdist : s * |u - 1| ≤ 4 * T := by
    have hfactor : s ^ 2 * (u - 1) = (n-s)*(n+s)+c := by
      nlinarith [hus]
    have htriangle : s ^ 2 * |u-1| ≤ |n-s| * (n+s)+c := by
      calc
        s ^ 2 * |u-1| = |s ^ 2 * (u-1)| := by rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
        _ = |(n-s)*(n+s)+c| := by rw [hfactor]
        _ ≤ |(n-s)*(n+s)| + |c| := abs_add_le _ _
        _ = |n-s| * (n+s)+c := by
            rw [abs_mul, abs_of_nonneg (show 0 ≤ n+s by linarith), abs_of_nonneg hc0]
    have hupper := mul_le_mul_of_nonneg_right hn (show 0 ≤ n+s by linarith)
    have hnsT := mul_le_mul_of_nonneg_left (show n+s ≤ 3*s by linarith)
      (show 0 ≤ T by linarith)
    exact (mul_le_mul_iff_right₀ hs0).mp (by nlinarith [htriangle, hupper, hnsT, hcT] :
      s * (s * |u-1|) ≤ s * (4*T))
  have hp : s ^ (2-a) * s ^ a = s ^ (2 : ℕ) := by
    rw [← Real.rpow_add hs0]; norm_num
  have hm : m = s ^ (2-a) * u := by
    apply (mul_right_cancel₀ (Real.rpow_pos_of_pos hs0 a).ne')
    calc
      m * s ^ a = n^2+c := hprod
      _ = u * (s ^ (2-a) * s ^ a) := by rw [hp, hus]
      _ = _ := by ring
  have hpow : m ^ (1/(2-a)) = s * u ^ (1/(2-a)) := by
    rw [hm, Real.mul_rpow (Real.rpow_nonneg hs0.le _) hu.le, ← Real.rpow_mul hs0.le]
    have hcancel : (2-a) * (1/(2-a)) = 1 := by field_simp
    rw [hcancel, Real.rpow_one]
  have hrep : |s - m ^ (1/(2-a))| = s * |u ^ (1/(2-a)) - 1| := by
    rw [hpow, show s - s * u ^ (1/(2-a)) = s * (1 - u ^ (1/(2-a))) by ring,
      abs_mul, abs_of_pos hs0, abs_sub_comm (1 : ℝ)]
  have hroot := rpow_dist_one hu hg0 hg2
  have hr5 : |u ^ (1/(2-a)) - 1| ≤ 5 * |u-1| :=
    hroot.trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
  calc
    |n - m ^ (1/(2-a))| ≤ |n-s| + |s-m ^ (1/(2-a))| := abs_sub_le _ _ _
    _ ≤ T + s * (5 * |u-1|) := by rw [hrep]; gcongr
    _ ≤ 25*T := by nlinarith

theorem cofactor_scale {x s n m a T c : ℝ} (hx : 1 ≤ x)
    (hxs : x ≤ s) (hsx : s ≤ 2*x) (ha : 1 ≤ a) (hahi : a ≤ 3/2)
    (hn : |n-s| ≤ T) (hT : T ≤ x/2) (hc0 : 0 ≤ c) (hcs : c ≤ s ^ 2)
    (hprod : m * s^a = n^2+c) :
    x^(2-a)/4 ≤ m ∧ m ≤ 8*x^(2-a) := by
  have hs : 0 < s := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hq : 0 ≤ 2-a := by linarith
  have hq' : 2-a ≤ 1 := by linarith
  obtain ⟨hlo, hhi⟩ := abs_le.mp hn
  have hnl : s/2 ≤ n := by linarith
  have hnr : n ≤ (3/2)*s := by linarith
  have hident : s^(2-a) * s^a = s^2 := by
    rw [← Real.rpow_add hs]; norm_num
  have hpa := Real.rpow_pos_of_pos hs a
  have hl : s^(2-a)/4 ≤ m := by
    apply (mul_le_mul_iff_left₀ hpa).mp
    rw [hprod]
    nlinarith [hident, mul_nonneg (show 0 ≤ n - s/2 by linarith)
      (show 0 ≤ n + s/2 by linarith)]
  have hu : m ≤ 4*s^(2-a) := by
    apply (mul_le_mul_iff_left₀ hpa).mp
    rw [hprod]
    nlinarith [hident, mul_nonneg (show 0 ≤ (3/2)*s - n by linarith)
      (show 0 ≤ (3/2)*s + n by linarith)]
  have hleft := Real.rpow_le_rpow hx0 hxs hq
  have hright := Real.rpow_le_rpow hs.le hsx hq
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hx0] at hright
  have hd : (2:ℝ)^(2-a) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hq'
  exact ⟨by linarith, by nlinarith [mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hx0 (2-a))]⟩

open Filter Asymptotics
open scoped BigOperators Topology


/-- Sum the bounds for (roots ofs) close to an endpoint U V and for the remaining (roots ofs). -/
theorem sum_near_far {ι : Type*} (s : Finset ι) (near : ι → Prop)
    [DecidablePred near] (f : ι → ℝ) {u v : ℝ} (hv : 0 ≤ v)
    (hupp : ∀ i ∈ s, near i → f i ≤ u)
    (vupp : ∀ i ∈ s, ¬ near i → f i ≤ v) :
    ∑ i ∈ s, f i ≤ ((s.filter near).card : ℝ) * u + (s.card : ℝ) * v := by
  classical
  calc
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, ((if near i then u else 0) + v) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hn : near i
      · simpa [hn] using (hupp i hi hn).trans (le_add_of_nonneg_right hv)
      · simpa [hn] using vupp i hi hn
    _ = ((s.filter near).card : ℝ) * u + (s.card : ℝ) * v := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp

/-- A fixed power saving covers the two logarithms from the endpoint U V estimates. -/
theorem eventual_linear_of_power_log (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    {a : ℝ} (ha : a < 1)
    (hf : ∀ᶠ n : ℕ in atTop, f n ≤ C * (n : ℝ) ^ a * (Real.log n) ^ (2 : ℕ)) :
    ∀ᶠ n : ℕ in atTop, f n ≤ C * (n : ℝ) := by
  have hlog : ∀ᶠ y : ℝ in atTop, (Real.log y) ^ (2 : ℕ) ≤ y ^ (1 - a) := by
    filter_upwards [(isLittleO_log_rpow_rpow_atTop (2 : ℝ) (sub_pos.mpr ha)).bound
      (by norm_num : (0 : ℝ) < 1), eventually_ge_atTop (1 : ℝ)] with y h hy
    have hy0 : 0 ≤ y := by linarith
    simpa [Real.norm_eq_abs, Real.rpow_natCast, abs_of_nonneg (Real.rpow_nonneg hy0 (1 - a)),
      abs_of_nonneg (sq_nonneg (Real.log y))] using h
  filter_upwards [hf, (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlog,
    eventually_ge_atTop (1 : ℕ)] with n hn hlogn hn1
  have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  calc
    f n ≤ C * (n : ℝ) ^ a * (Real.log n) ^ (2 : ℕ) := hn
    _ ≤ C * (n : ℝ) ^ a * (n : ℝ) ^ (1 - a) :=
      mul_le_mul_of_nonneg_left hlogn (mul_nonneg hC (Real.rpow_nonneg hpos.le a))
    _ = C * (n : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hpos]
      simp

/-- A linear estimate is enough for the precise recurrence with strict lower U V bound. -/
theorem recurrent_budget_of_eventual_linear (f : ℕ → ℝ) (C : ℝ)
    (h : ∀ᶠ n : ℕ in atTop, f n ≤ C * (n : ℝ)) :
    ∀ B : ℕ, ∃ n : ℕ, B < n ∧ f n ≤ (19/50 : ℝ) * ((n : ℝ) * Real.log n) := by
  intro B
  have hg : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨n, hnB, hn, hlog⟩ := ((eventually_gt_atTop B).and
    (h.and (hg.eventually_ge_atTop (50 / 19 * C)))).exists
  refine ⟨n, hnB, hn.trans ?_⟩
  have hc : C ≤ (19 / 50 : ℝ) * Real.log n := by linarith
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg n : (0 : ℝ) ≤ n))



open QP0052.Counting QP0052Fourier

abbrev Row := Sigma (fun _ : ℕ => ℕ)
def primes (ofs U V x : ℕ) := (Finset.Ioc x ((2*x)^2+ofs)).filter
  (fun p => Nat.Prime p ∧ p^V ≤ (2*x)^U)
def rows (ofs U V x : ℕ) : Finset Row := (primes ofs U V x).sigma (roots ofs)

noncomputable def upper (x : ℕ) (_p : ℕ) : ℝ := 2*(x:ℝ)+1/2
noncomputable def lower (U V x p : ℕ) : ℝ := (start U V x p : ℝ)-1/2

noncomputable def highSum (ofs U V x : ℕ) : ℝ :=
  ∑ p ∈ primes ofs U V x,
    (∑ k ∈ (Finset.Ico 1 p).filter (fun k => Nat.sqrt p < min k (p-k)),
      (∑ r ∈ roots ofs p, ∑ n ∈ (Finset.Ioc x (2*x)).filter (fun n => p^V ≤ n^U),
        Real.cos (2*Real.pi*k*((n:ℝ)-r)/p)) / p) * Real.log p

theorem row_info {x : ℕ} {i : Row} (hi : i ∈ rows ofs U V x) :
    x < i.1 ∧ i.1.Prime ∧ i.1^V ≤ (2*x)^U ∧
      i.2 < i.1 ∧ i.1 ∣ i.2^2+ofs := by
  obtain ⟨hp, hr⟩ := Finset.mem_sigma.mp hi
  obtain ⟨hI, hprime, hcut⟩ := Finset.mem_filter.mp hp
  obtain ⟨hlt, hd⟩ := Finset.mem_filter.mp hr
  exact ⟨(Finset.mem_Ioc.mp hI).1, hprime, hcut, Finset.mem_range.mp hlt, hd⟩

theorem highSum_eq_endpoints {x : ℕ} (hx : 2 ≤ x) :
    highSum ofs U V x = ∑ i ∈ rows ofs U V x, (boundaryTerm i.1 i.2 (upper x i.1) -
      boundaryTerm i.1 i.2 (lower U V x i.1)) * Real.log i.1 := by
  classical
  rw [rows, Finset.sum_sigma]
  unfold highSum
  refine Finset.sum_congr rfl ?_
  intro p hp
  obtain ⟨hi, hprime, hcut⟩ := Finset.mem_filter.mp hp
  have hxp := (Finset.mem_Ioc.mp hi).1
  have hmod := hprime.eq_two_or_odd.resolve_left (by omega)
  have hodd : p = 2*(p/2)+1 := by omega
  have hw := window_interval (U := U) (V := V) x p
  have hs := start_le_top (by omega : 1 ≤ x) hcut
  rw [hw, high_Icc_roots p _ _ _ hodd hs]
  simp [upper, lower]

noncomputable def value (e : ℕ → ℝ) (i : Row) : ℕ := (lift (e i.1) i.1 i.2).toNat

theorem near_data {x : ℕ} {e : ℕ → ℝ} {T : ℝ} {i : Row} (hi : i ∈ rows ofs U V x)
    (he : T < e i.1) (hd : |e i.1 - (lift (e i.1) i.1 i.2 : ℝ)| ≤ T) :
    (value e i : ℝ) = lift (e i.1) i.1 i.2 ∧
    value e i % i.1 = i.2 ∧ i.1 ∣ (value e i)^2+ofs := by
  obtain ⟨_, hprime, _, hlt, hroot⟩ := row_info hi
  have hz := lift_pos he hd
  have hcast : (value e i : ℤ) = lift (e i.1) i.1 i.2 := Int.toNat_of_nonneg hz.le
  have hmod : value e i ≡ i.2 [MOD i.1] := by
    apply Int.natCast_modEq_iff.mp
    rw [hcast]
    exact lift_congr (e i.1) i.1 i.2
  have hrep : value e i % i.1 = i.2 :=
    (show value e i % i.1 = i.2 % i.1 from hmod).trans (Nat.mod_eq_of_lt hlt)
  have hr : (value e i)^2+ofs ≡ i.2^2+ofs [MOD i.1] :=
    (hmod.pow 2).add_right ofs
  have hzero : (value e i)^2+ofs ≡ 0 [MOD i.1] :=
    hr.trans (Nat.modEq_zero_iff_dvd.mpr hroot)
  exact ⟨by exact_mod_cast hcast, hrep, Nat.modEq_zero_iff_dvd.mp hzero⟩

theorem row_unique {e : ℕ → ℝ} {i j : Row}
    (hi : value e i % i.1 = i.2) (hj : value e j % j.1 = j.2)
    (hn : value e i = value e j) (hp : i.1 = j.1) : i = j := by
  rcases i with ⟨p,r⟩
  rcases j with ⟨q,s⟩
  dsimp at hi hj hp
  subst q
  have hrs : r = s := hi.symm.trans ((congrArg (· % p) hn).trans hj)
  subst s
  rfl

theorem small_square {n x : ℕ} (hx : 10 ≤ x) (hn : n ≤ 3*x) (hofx : ofs ≤ x) :
    n^2+ofs < x^3 := by
  have h1 := Nat.mul_le_mul hn hn
  have h2 := Nat.mul_le_mul_right (x*x) hx
  nlinarith [h1, h2, Nat.mul_le_mul hx hx]

theorem nat_interval (e T : ℝ) (hT : 0 ≤ T) (he : 0 ≤ e + T) :
    ((Finset.Icc ⌈e-T⌉₊ ⌊e+T⌋₊).card : ℝ) ≤ 2*T+1 := by
  by_cases h : ⌈e-T⌉₊ ≤ ⌊e+T⌋₊
  · rw [Nat.card_Icc, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    linarith [Nat.le_ceil (e-T), Nat.floor_le he]
  · rw [Finset.Icc_eq_empty_of_lt (by omega), Finset.card_empty, Nat.cast_zero]
    linarith

theorem fixed_count {x : ℕ} (hx : 10 ≤ x) (hofx : ofs ≤ x) (S : Finset Row) (hS : S ⊆ rows ofs U V x)
    (e : ℕ → ℝ) (c T : ℝ) (hT : 0 ≤ T) (hc : T < c) (hupper : c+T ≤ 3*x)
    (hs : ∀ i ∈ S, e i.1 = c ∧ |e i.1 - (lift (e i.1) i.1 i.2 : ℝ)| ≤ T) :
    (S.card : ℝ) ≤ 2 * (2*T+1) := by
  classical
  let A := Finset.Icc ⌈c-T⌉₊ ⌊c+T⌋₊
  have hright : 0 ≤ c+T := by linarith
  have hd i (hi : i ∈ S) := near_data (hS hi) (by rw [(hs i hi).1]; exact hc) (hs i hi).2
  have hA (i : Row) (hi : i ∈ S) : value e i ∈ A := by
    have hh := (hs i hi).2
    rw [← (hd i hi).1, (hs i hi).1, abs_le] at hh
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr (by linarith), Nat.le_floor (by linarith)⟩
  have hsmall (n : ℕ) (hn : n ∈ A) : n^2+ofs < x^3 := by
    apply small_square hx _ hofx
    have h := (Finset.mem_Icc.mp hn).2
    have : (n:ℝ) ≤ 3*(x:ℝ) :=
      (show (n:ℝ) ≤ ⌊c+T⌋₊ by exact_mod_cast h).trans ((Nat.floor_le hright).trans hupper)
    exact_mod_cast this
  have hcard := fixed_endpoint_count S A (value e) (fun i => i.1) x (by omega)
    (fun i hi j hj hn hp => row_unique (hd i hi).2.1 (hd j hj).2.1 hn hp) hA hsmall
    (fun i hi => ⟨(row_info (hS hi)).2.1, (row_info (hS hi)).1.le, (hd i hi).2.2⟩)
  calc
    (S.card : ℝ) ≤ (A.card : ℝ)*2 := by exact_mod_cast hcard
    _ ≤ 2*(2*T+1) := by nlinarith [nat_interval c T hT hright]



open QP0052.Counting

noncomputable def scale (x : ℕ) : ℝ := (x : ℝ) ^ (99/100 : ℝ)
noncomputable def near (x : ℕ) (e : ℕ → ℝ) (i : Row) : Prop :=
  |e i.1 - (lift (e i.1) i.1 i.2 : ℝ)| ≤ scale x

theorem scale_one {x : ℕ} (hx : 1 ≤ x) : 1 ≤ scale x :=
  Real.one_le_rpow (by exact_mod_cast hx) (by norm_num)

theorem lower_ge (x p : ℕ) : (x : ℝ) + 1/2 ≤ lower U V x p := by
  have h : x+1 ≤ start U V x p := le_max_left _ _
  have h' : (x : ℝ)+1 ≤ (start U V x p : ℝ) := by exact_mod_cast h
  unfold lower
  linarith

noncomputable def cofactor (ofs U V x : ℕ) (i : Row) : ℕ := ((value (lower U V x) i)^2+ofs) / i.1

theorem moving_point {x : ℕ} (hx : 10 ≤ x) (hw : 4*scale x ≤ x) (hofx : ofs ≤ x) {i : Row}
    (hi : i ∈ rows ofs U V x) (hn : near x (lower U V x) i) (hmove : start U V x i.1 ≠ x+1) :
    let m := cofactor ofs U V x i
    let n := value (lower U V x) i
    m*i.1 = n^2+ofs ∧
    (1/4 : ℝ)*(x : ℝ)^(2 - (U : ℝ) / V) ≤ m ∧
    (m : ℝ) ≤ 8*(x : ℝ)^(2 - (U : ℝ) / V) ∧
    |(n:ℝ)-(m:ℝ)^(1 / (2 - (U : ℝ) / V))| ≤ 50*scale x := by
  dsimp only
  have hx' : (10:ℝ) ≤ x := by exact_mod_cast hx
  have hT := scale_one (by omega : 1 ≤ x)
  have hel : scale x < lower U V x i.1 := by linarith [lower_ge (U := U) (V := V) x i.1]
  obtain ⟨hnlift, hmod, hdvd⟩ := near_data hi hel hn
  have hmn : cofactor ofs U V x i * i.1 = (value (lower U V x) i)^2+ofs := Nat.div_mul_cancel hdvd
  refine ⟨hmn, ?_⟩
  obtain ⟨hxs, hsc⟩ := lower_boundary hmove
  have hsx := (cutoff_iff (2*x) i.1).mpr (row_info hi).2.2.1
  push_cast at hsx
  have heq : (cofactor ofs U V x i : ℝ) * (cutoff U V i.1) ^ ((U : ℝ) / V) =
      (value (lower U V x) i : ℝ)^2+ofs := by
    rw [cutoff_exponent]
    exact_mod_cast hmn
  have hnear : |(value (lower U V x) i : ℝ) - cutoff U V i.1| ≤ 2*scale x := by
    calc
      _ ≤ |(value (lower U V x) i : ℝ) - lower U V x i.1| + |lower U V x i.1 - cutoff U V i.1| :=
        abs_sub_le _ _ _
      _ ≤ _ := by
        have h := hn
        change |lower U V x i.1 - (lift (lower U V x i.1) i.1 i.2 : ℝ)| ≤ scale x at h
        rw [← hnlift, abs_sub_comm] at h
        change |lower U V x i.1 - cutoff U V i.1| ≤ 1/2 at hsc
        linarith
  have hofsR : (ofs : ℝ) ≤ x := by exact_mod_cast hofx
  have hofs0 : (0 : ℝ) ≤ ofs := Nat.cast_nonneg _
  have hcut1 : (1 : ℝ) ≤ cutoff U V i.1 := by linarith
  have hscale := cofactor_scale (by linarith : (1:ℝ) ≤ x) hxs hsx
    (a := ((U : ℝ) / V)) ShiftData.alpha_ge_one ShiftData.alpha_le_three_halves hnear
    (by linarith) hofs0 (by nlinarith) heq
  have hclose := cofactor_close hcut1
    (by linarith : 1 ≤ 2*scale x) (by linarith) hnear
    (a := ((U : ℝ) / V)) ShiftData.alpha_ge_one ShiftData.alpha_le_three_halves hofs0
    (by nlinarith) heq
  exact ⟨by linarith [hscale.1], hscale.2, by linarith⟩

theorem moving_count_constant :
    ∃ E : ℝ, 0 < E ∧ ∀ x : ℕ, 10 ≤ x → 4*scale x ≤ x → ofs ≤ x →
      ∀ S : Finset Row, S ⊆ rows ofs U V x →
        (∀ i ∈ S, near x (lower U V x) i ∧ start U V x i.1 ≠ x+1) →
        (S.card : ℝ) ≤ E*(x:ℝ)^(995/1000 : ℝ) := by
  classical
  obtain ⟨E,hE,H⟩ := cofactor_count_power (ofs := ofs) (1/4) 8 101 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨E,hE,?_⟩
  intro x hx hw hofx S hS hnear
  let m := cofactor ofs U V x
  let n := value (lower U V x)
  let K := S.image m
  let T := scale x
  let L := fun q : ℕ => ⌈(q:ℝ)^(1 / (2 - (U : ℝ) / V)) - 50*T⌉₊
  let W := ⌈100*T⌉₊
  have hx' : (10:ℝ) ≤ x := by exact_mod_cast hx
  have hT : 1 ≤ T := scale_one (by omega)
  have point (i : Row) (hi : i ∈ S) :=
    moving_point hx hw hofx (hS hi) (hnear i hi).1 (hnear i hi).2
  have hrep (i : Row) (hi : i ∈ S) : n i % i.1 = i.2 :=
    (near_data (hS hi) (by linarith [lower_ge (U := U) (V := V) x i.1]) (hnear i hi).1).2.1
  apply H S K n (fun i => i.1) m L W x (2 - (U : ℝ) / V)
    (by linarith) (by linarith [ShiftData.alpha_le_two (U := U) (V := V)])
    (by linarith [ShiftData.alpha_ge (U := U) (V := V)])
  · intro i hi j hj hij hp
    exact row_unique (hrep i hi) (hrep j hj) hij hp
  · intro i hi
    exact Finset.mem_image_of_mem _ hi
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨i,hi,rfl⟩
    exact ⟨(point i hi).2.1, (point i hi).2.2.1⟩
  · intro i hi
    exact (point i hi).1
  · intro i hi
    obtain ⟨hlo, hup⟩ := abs_le.mp (point i hi).2.2.2
    constructor
    · apply Nat.ceil_le.mpr
      change (m i : ℝ)^(1 / (2 - (U : ℝ) / V)) - 50*T ≤ (n i : ℝ)
      linarith
    · have hl := Nat.le_ceil ((m i : ℝ)^(1 / (2 - (U : ℝ) / V))-50*T)
      have hh := Nat.le_ceil (100*T)
      have hnw : (n i : ℝ) ≤ (L (m i) : ℝ) + (W : ℝ) := by
        change _ ≤ (⌈(m i : ℝ)^(1 / (2 - (U : ℝ) / V))-50*T⌉₊ : ℝ) + (⌈100*T⌉₊ : ℝ)
        linarith
      exact_mod_cast hnw
  · have hw' := Nat.ceil_lt_add_one (by positivity : 0 ≤ 100*T)
    change (⌈100*T⌉₊ : ℝ) ≤ 101*T
    linarith



open QP0052.Counting
open scoped Classical

noncomputable def endpoint (U V x : ℕ) (isLower : Bool) : ℕ → ℝ :=
  if isLower then lower U V x else upper x

theorem prime_real_bound {x p : ℕ} (hp : p^V ≤ (2*x)^U) :
    (p:ℝ) ≤ (2*(x:ℝ))^((U : ℝ) / V) := by
  have hc := (cutoff_iff (2*x) p).mpr hp
  push_cast at hc
  rw [← cutoff_exponent (U := U) (V := V) p]
  exact Real.rpow_le_rpow (cutoff_nonneg (U := U) (V := V) p) hc (ShiftData.alpha_pos (U := U) (V := V)).le

theorem row_card_bound (x : ℕ) (hx : 1 ≤ x) :
    ((rows ofs U V x).card : ℝ) ≤ (20 * ofs) * (x:ℝ)^((U : ℝ) / V) := by
  classical
  let P := (2*(x:ℝ))^((U : ℝ) / V)
  have hP : 0 ≤ P := Real.rpow_nonneg (by positivity) _
  have hsub : primes ofs U V x ⊆ Finset.range (⌊P⌋₊+1) := by
    intro p hp
    obtain ⟨_,_,hcut⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (prime_real_bound hcut)))
  have hs : (primes ofs U V x).card ≤ ⌊P⌋₊+1 := by
    simpa using Finset.card_le_card hsub
  have hr : (rows ofs U V x).card ≤ (primes ofs U V x).card * (4 * ofs) := by
    rw [rows, Finset.card_sigma]
    calc
      _ ≤ ∑ _p ∈ primes ofs U V x, 4 * ofs := by
        apply Finset.sum_le_sum
        intro p hp
        have hpp := (Finset.mem_filter.mp hp).2.1
        simpa using (roots_prime_power_le (ofs := ofs) (k:=1) hpp (by decide))
      _ = _ := by simp
  have hx1 : (1:ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : 0 ≤ (x:ℝ) := Nat.cast_nonneg x
  have hnum : (2:ℝ)^((U : ℝ) / V) ≤ 4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ShiftData.alpha_le_two
      _ = _ := by norm_num
  have hb : P ≤ 4*(x:ℝ)^((U : ℝ) / V) := by
    dsimp [P]
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hx0]
    exact mul_le_mul_of_nonneg_right hnum (Real.rpow_nonneg hx0 _)
  have hr' : ((rows ofs U V x).card : ℝ) ≤ ((primes ofs U V x).card : ℝ)*(4 * ofs) := by
    exact_mod_cast hr
  have hs' : ((primes ofs U V x).card : ℝ) ≤ (⌊P⌋₊:ℝ)+1 := by exact_mod_cast hs
  have hxa := Real.one_le_rpow hx1 (ShiftData.alpha_pos (U := U) (V := V)).le
  have hprimes : ((primes ofs U V x).card : ℝ) ≤ 5 * (x:ℝ)^((U : ℝ) / V) := by
    linarith [Nat.floor_le hP]
  have hofs0 : (0:ℝ) ≤ 4 * ofs := by positivity
  calc ((rows ofs U V x).card : ℝ) ≤ ((primes ofs U V x).card : ℝ)*(4 * ofs) := hr'
    _ ≤ (5 * (x:ℝ)^((U : ℝ) / V)) * (4 * ofs) := mul_le_mul_of_nonneg_right hprimes hofs0
    _ = (20 * ofs) * (x:ℝ)^((U : ℝ) / V) := by ring

theorem all_endpoint_counts :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 10 ≤ x → 4*scale x ≤ x → ofs ≤ x →
    ∀ l : Bool, ((Finset.filter (near x (endpoint U V x l)) (rows ofs U V x)).card : ℝ)
        ≤ C*(x:ℝ)^(995/1000:ℝ) := by
  classical
  obtain ⟨E,hE,hmove⟩ := moving_count_constant (ofs := ofs) (U := U) (V := V)
  use E+6
  refine ⟨by linarith,?_⟩
  intro x hx hw hofx l
  have ht := scale_one (by omega : 1 ≤ x)
  have hx' : (10:ℝ) ≤ x := by exact_mod_cast hx
  have hpow : scale x ≤ (x:ℝ)^(995/1000:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hlin : 2*(2*scale x+1) ≤ 6*(x:ℝ)^(995/1000:ℝ) := by linarith
  have hpos := Real.rpow_nonneg (Nat.cast_nonneg x) (995/1000:ℝ)
  cases l
  · let S := (rows ofs U V x).filter (near x (upper x))
    have hdis (i : Row) (hi : i ∈ S) : near x (upper x) i := (Finset.mem_filter.mp hi).2
    have hf := fixed_count hx hofx S (Finset.filter_subset _ _) (upper x) (2*(x:ℝ)+1/2) (scale x)
      (by linarith) (by linarith) (by linarith) (fun i hi => ⟨rfl,hdis i hi⟩)
    change (S.card:ℝ) ≤ _
    nlinarith [mul_nonneg hE.le hpos]
  · let S := (rows ofs U V x).filter (near x (lower U V x))
    let F := S.filter (fun i => start U V x i.1 = x+1)
    let Vs := S.filter (fun i => ¬ start U V x i.1 = x+1)
    have hS : S ⊆ rows ofs U V x := Finset.filter_subset _ _
    have hF : F ⊆ S := Finset.filter_subset _ _
    have hVs : Vs ⊆ S := Finset.filter_subset _ _
    have hf := fixed_count hx hofx F (hF.trans hS) (lower U V x) ((x:ℝ)+1/2) (scale x)
      (by linarith) (by linarith) (by linarith) (by
        intro i hi
        have he := (Finset.mem_filter.mp hi).2
        have hd := (Finset.mem_filter.mp (hF hi)).2
        refine ⟨?_, hd⟩
        unfold lower
        rw [he, Nat.cast_add, Nat.cast_one]
        ring)
    have hm := hmove x hx hw hofx Vs (hVs.trans hS) (by
      intro i hi
      exact ⟨(Finset.mem_filter.mp (hVs hi)).2,(Finset.mem_filter.mp hi).2⟩)
    have hcard : F.card + Vs.card = S.card := Finset.card_filter_add_card_filter_not _
    have hcard' : (F.card:ℝ)+(Vs.card:ℝ)=(S.card:ℝ) := by exact_mod_cast hcard
    change (S.card:ℝ) ≤ _
    nlinarith


open scoped BigOperators


/-- Absorb the two endpoint U V estimates, including the logarithmic prime weight.
The far rows ofs U V have exponent 1.32301 + 1.32301/2 - 0.99 = 0.994515.
The cutoff U V assumptions hold at all sufficiently large real or natural scales. -/
theorem sum_weighted_endpoints {ι : Type*} (rows : Finset ι)
    (near : ι → Prop) [DecidablePred near] (p : ι → ℕ) (f : ι → ℝ)
    {x C D : ℝ} (hx : 2 ≤ x) (hlogx : 1 ≤ Real.log x)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hrows : (rows.card : ℝ) ≤ C * x ^ ((U : ℝ) / V))
    (hnear : ((rows.filter near).card : ℝ) ≤ C * x ^ (9975 / 10000 : ℝ))
    (hp : ∀ i ∈ rows, 1 ≤ p i ∧ (p i : ℝ) ≤ (2 * x) ^ ((U : ℝ) / V))
    (hnearf : ∀ i ∈ rows, near i →
      f i ≤ D * ((1 + Real.log (p i)) * Real.log (p i)))
    (hfarf : ∀ i ∈ rows, ¬near i →
      f i ≤ D * ((Real.sqrt (p i) / x ^ (99 / 100 : ℝ)) * Real.log (p i))) :
    ∑ i ∈ rows, f i ≤ 28 * C * D * x ^ (9975 / 10000 : ℝ) * (Real.log x) ^ 2 := by
  let a : ℝ := (U : ℝ) / V
  let d : ℝ := 99 / 100
  let b : ℝ := 9975 / 10000
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hl0 : 0 ≤ Real.log x := by linarith
  have htwo : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have bounds (i : ι) (hi : i ∈ rows) :
      0 ≤ Real.log (p i) ∧ Real.log (p i) ≤ 4 * Real.log x ∧
        Real.sqrt (p i) / x ^ d ≤ 2 * x ^ (a/2-d) := by
    obtain ⟨hp1, hpu⟩ := hp i hi
    have hp1' : (1 : ℝ) ≤ p i := by exact_mod_cast hp1
    refine ⟨Real.log_nonneg hp1', ?_, ?_⟩
    · have h := Real.log_le_log (lt_of_lt_of_le zero_lt_one hp1') hpu
      rw [Real.log_rpow (by positivity), Real.log_mul (by norm_num) hx0.ne'] at h
      have ha2 : (U:ℝ)/V ≤ 2 := ShiftData.alpha_le_two
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hm := mul_le_mul ha2 (show Real.log 2 + Real.log x ≤ 2 * Real.log x by linarith)
        (by linarith) (by norm_num)
      linarith
    · have htwoPow : (2 : ℝ) ^ (a / 2) ≤ 2 := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
          (show (1 : ℝ) ≤ 2 by norm_num) (show a / 2 ≤ 1 by have := ShiftData.alpha_le_two (U := U) (V := V); simp only [a]; linarith)
      have hs : Real.sqrt (p i) ≤ 2 * x ^ (a / 2) := calc
        Real.sqrt (p i) ≤ Real.sqrt ((2 * x) ^ a) := Real.sqrt_le_sqrt hpu
        _ = (2 : ℝ) ^ (a / 2) * x ^ (a / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity),
            Real.mul_rpow (by norm_num) hx0.le, show a * (1 / 2) = a / 2 by ring]
        _ ≤ 2 * x ^ (a / 2) :=
          mul_le_mul_of_nonneg_right htwoPow (Real.rpow_nonneg hx0.le _)
      calc
        _ ≤ (2 * x ^ (a / 2)) / x ^ d :=
          div_le_div_of_nonneg_right hs (Real.rpow_nonneg hx0.le _)
        _ = 2 * x ^ (a / 2 - d) := by rw [Real.rpow_sub hx0]; ring
  have hu (i : ι) (hi : i ∈ rows) (hn : near i) :
      f i ≤ D * (20 * (Real.log x)^2) := by
    obtain ⟨hlp, hpmax, _⟩ := bounds i hi
    apply (hnearf i hi hn).trans
    apply mul_le_mul_of_nonneg_left _ hD
    calc
      _ ≤ (5 * Real.log x) * (4 * Real.log x) :=
        mul_le_mul (by linarith) hpmax hlp (by positivity)
      _ = _ := by ring
  have hv (i : ι) (hi : i ∈ rows) (hn : ¬near i) :
      f i ≤ D * (8 * x ^ (a/2-d) * Real.log x) := by
    obtain ⟨hlp, hpmax, hs⟩ := bounds i hi
    apply (hfarf i hi hn).trans
    apply mul_le_mul_of_nonneg_left _ hD
    calc
      _ ≤ (2 * x ^ (a/2-d)) * (4 * Real.log x) :=
        mul_le_mul hs hpmax hlp (by positivity)
      _ = _ := by ring
  have hexp : x ^ a * x ^ (a/2-d) ≤ x ^ b := by
    rw [← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    have := ShiftData.alpha_le (U := U) (V := V)
    simp only [a, d, b]
    linarith
  have hlog2 : Real.log x ≤ (Real.log x)^2 := by nlinarith
  have htotal := sum_near_far rows near f (by positivity) hu hv
  calc
    _ ≤ _ := htotal
    _ ≤ C * x ^ b * (D * (20 * (Real.log x)^2)) +
          C * x ^ a * (D * (8 * x ^ (a/2-d) * Real.log x)) := by
      exact add_le_add (mul_le_mul_of_nonneg_right hnear (by positivity))
        (mul_le_mul_of_nonneg_right hrows (by positivity))
    _ = 20*C*D*x^b*(Real.log x)^2 +
          (8*C*D)*((x^a*x^(a/2-d))*Real.log x) := by ring
    _ ≤ 20*C*D*x^b*(Real.log x)^2 + (8*C*D)*(x^b*(Real.log x)^2) := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hexp hlog2 hl0 (Real.rpow_nonneg hx0.le _)
    _ = _ := by dsimp [b]; ring



open Filter QP0052Fourier
open scoped Topology Classical

theorem width_eventually : ∀ᶠ x : ℕ in atTop, 4*scale x ≤ x := by
  have H : Tendsto (fun n : ℕ => (n : ℝ)^(1/100:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [H.eventually_ge_atTop 4, eventually_ge_atTop (1:ℕ)] with x h hx
  have hpx : (0:ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hmul := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hpx.le (99/100:ℝ))
  unfold scale
  calc
    4*(x:ℝ)^(99/100:ℝ) ≤ (x:ℝ)^(1/100:ℝ)*(x:ℝ)^(99/100:ℝ) := hmul
    _ = (x : ℝ) := by rw [← Real.rpow_add hpx]; norm_num

/-- 推廣版的冪次節省估計：對 `n² + ofs`、指數比 `U/V ∈ [1.32301, 1.325]`。 -/
theorem high_power_eventual :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℕ in atTop,
      highSum ofs U V x ≤ K * (x : ℝ) ^ (9975/10000 : ℝ) * (Real.log x) ^ (2 : ℕ) := by
  classical
  obtain ⟨C, hC, H⟩ := all_endpoint_counts (ofs := ofs) (U := U) (V := V)
  let A := max (20 * (ofs : ℝ)) C
  have ha : 0 ≤ A := le_trans hC (le_max_right _ _)
  refine ⟨56*A, by positivity, ?_⟩
  have hlog : Tendsto (fun x : ℕ => Real.log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (10:ℕ),width_eventually,hlog.eventually_ge_atTop 1,
    eventually_ge_atTop ofs]
    with x hx hw hlogx hofx
  let w := fun l : Bool => fun i : Row =>
    |boundaryTerm i.1 i.2 (endpoint U V x l i.1)| * Real.log i.1
  have hx2 : (2:ℝ) ≤ x := by exact_mod_cast (by omega : 2 ≤ x)
  have hT := scale_one (by omega : 1 ≤ x)
  have hsum (l : Bool) : ∑ i ∈ rows ofs U V x, w l i ≤
      28*A*(x:ℝ)^(9975/10000:ℝ)*(Real.log x)^2 := by
    have hrows := (row_card_bound (ofs := ofs) (U := U) (V := V) x (by omega)).trans
      (mul_le_mul_of_nonneg_right (le_max_left (20 * (ofs : ℝ)) C)
        (Real.rpow_nonneg (Nat.cast_nonneg x) _))
    have hx1 : (1:ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
    have hnear := (H x hx hw hofx l).trans
      ((mul_le_mul_of_nonneg_right (le_max_right (20 * (ofs : ℝ)) C)
        (Real.rpow_nonneg (Nat.cast_nonneg x) _)).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (995/1000:ℝ) ≤ 9975/10000)) ha))
    have hh := sum_weighted_endpoints (U := U) (V := V) (rows ofs U V x) (near x (endpoint U V x l)) (fun i => i.1) (w l)
      (x := (x:ℝ)) (C:=A) (D:=1) hx2 hlogx ha (by norm_num) hrows hnear (by
        intro i hi
        exact ⟨(row_info hi).2.1.pos, prime_real_bound (row_info hi).2.2.1⟩) (by
        intro i hi _
        have hp := (row_info hi).2.1.pos
        have hl := Real.log_nonneg (show (1:ℝ) ≤ i.1 by exact_mod_cast hp)
        simpa [w] using mul_le_mul_of_nonneg_right
          (boundary_near i.1 i.2 (endpoint U V x l i.1) hp) hl) (by
        intro i hi hfar
        have hp := (row_info hi).2.1.pos
        have hl := Real.log_nonneg (show (1:ℝ) ≤ i.1 by exact_mod_cast hp)
        let e := endpoint U V x l i.1
        let n := lift e i.1 i.2
        have hdist : scale x < |e - (n:ℝ)| := lt_of_not_ge hfar
        have hh := boundary_far i.1 i.2 e n hp (lift_congr e i.1 i.2)
          (lift_dist e i.1 i.2 hp) (by linarith)
        have hd := div_le_div_of_nonneg_left (Real.sqrt_nonneg (i.1:ℝ))
          (by linarith : 0 < scale x) hdist.le
        simpa [w,e,scale] using mul_le_mul_of_nonneg_right (hh.trans hd) hl)
    simpa using hh
  rw [highSum_eq_endpoints (ofs := ofs) (U := U) (V := V) (by omega : 2 ≤ x)]
  calc
    _ ≤ ∑ i ∈ rows ofs U V x, (w false i + w true i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hp := (row_info hi).2.1.pos
      have hl := Real.log_nonneg (show (1:ℝ) ≤ i.1 by exact_mod_cast hp)
      change (_-_) * Real.log i.1 ≤
        |boundaryTerm i.1 i.2 (upper x i.1)| * Real.log i.1 +
        |boundaryTerm i.1 i.2 (lower U V x i.1)| * Real.log i.1
      rw [← add_mul]
      apply mul_le_mul_of_nonneg_right _ hl
      linarith [le_abs_self (boundaryTerm i.1 i.2 (upper x i.1)),
        neg_le_abs (boundaryTerm i.1 i.2 (lower U V x i.1))]
    _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith [hsum false, hsum true]


/-- 冪次節省估計最終小於任意 `ε · x log x`。 -/
theorem high_eventual_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x → highSum ofs U V x ≤ ε * ((x : ℝ) * Real.log x) := by
  obtain ⟨K, hK, hev⟩ := high_power_eventual (ofs := ofs) (U := U) (V := V)
  have hr : (0 : ℝ) < 1/400 := by norm_num
  have hlo := (isLittleO_log_rpow_atTop hr).bound (show (0 : ℝ) < ε / (K + 1) by positivity)
  have hlo' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlo
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp
    (hev.and (hlo'.and (eventually_ge_atTop (2 : ℕ))))
  refine ⟨X, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hX x hx
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast h3
  have hxpos : (0 : ℝ) < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hrp : 0 ≤ (x : ℝ) ^ (1/400 : ℝ) := Real.rpow_nonneg hxpos.le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hrp] at h2
  have hsplit : (x : ℝ) ^ (9975/10000 : ℝ) * (x : ℝ) ^ (1/400 : ℝ) = x := by
    rw [← Real.rpow_add hxpos]; norm_num
  have hpow0 : 0 ≤ (x : ℝ) ^ (9975/10000 : ℝ) := Real.rpow_nonneg hxpos.le _
  calc highSum ofs U V x ≤ K * (x : ℝ) ^ (9975/10000 : ℝ) * (Real.log x) ^ (2 : ℕ) := h1
    _ = (K * (x : ℝ) ^ (9975/10000 : ℝ) * Real.log x) * Real.log x := by ring
    _ ≤ (K * (x : ℝ) ^ (9975/10000 : ℝ) * (ε / (K + 1) * (x : ℝ) ^ (1/400 : ℝ))) * Real.log x := by
        gcongr
    _ = (K / (K + 1)) * ε * (((x : ℝ) ^ (9975/10000 : ℝ) * (x : ℝ) ^ (1/400 : ℝ)) * Real.log x) := by
        field_simp
    _ = (K / (K + 1)) * ε * ((x : ℝ) * Real.log x) := by rw [hsplit]
    _ ≤ 1 * ε * ((x : ℝ) * Real.log x) := by
        gcongr
        rw [div_le_one (by linarith)]; linarith
    _ = ε * ((x : ℝ) * Real.log x) := by ring

end QuadraticHigh

/-- `L-quadratic-primes-high-shift-exponent-extension`。 -/
theorem PEqualNP.Outside.L_quadratic_primes_high_shift_exponent_extension :
  ∀ (offset U V : ℕ), 0 < offset → 0 < V → 132301 * V ≤ 100000 * U → 40 * U ≤ 53 * V → (let block := fun x : ℕ => Finset.Ioc x (2*x); let budget := fun x : ℕ => (x : ℝ) * Real.log (x : ℝ); let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); let primes := fun x : ℕ => (Finset.Ioc x ((2*x)^2+offset)).filter (fun p => Nat.Prime p ∧ p^V ≤ (2*x)^U); let window := fun x p : ℕ => (block x).filter (fun n => p^V ≤ n^U); let angle := fun p k : ℕ => fun t : ℝ => 2 * Real.pi * k * t / p; let coef := fun a x p k : ℕ => (∑ r ∈ roots a p, ∑ n ∈ window x p, Real.cos (angle p k ((n : ℝ) - r))) / p; let freqs := fun (p : ℕ) (low : Bool) => (Finset.Ico 1 p).filter (fun k => if low then min k (p-k) ≤ Nat.sqrt p else Nat.sqrt p < min k (p-k)); let part := fun (a x p : ℕ) (low : Bool) => (∑ k ∈ freqs p low, coef a x p k) * Real.log (p : ℝ); let modes := fun (a x : ℕ) (low : Bool) => ∑ p ∈ primes x, part a x p low; ∀ ε : ℝ, 0 < ε → ∃ X : ℕ, ∀ x : ℕ, X ≤ x → modes offset x false ≤ ε * budget x) := by
  intro offset U V hoff hV h1 h2
  have : Fact (1 ≤ offset) := ⟨hoff⟩
  have : ShiftData U V := ⟨hV, h1, h2⟩
  intro block budget roots primes window angle coef freqs part modes ε hε
  exact QuadraticHigh.high_eventual_epsilon (ofs := offset) (U := U) (V := V) ε hε
