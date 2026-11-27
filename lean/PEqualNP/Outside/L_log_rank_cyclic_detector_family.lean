import Mathlib

/-!
# Cyclic detector family at one-third density (`n = 3k + 1`)

We prove `PEqualNP.Outside.L_log_rank_cyclic_detector_family`: there exist absolute
constants `C` and `K` (`C = 8009`, `K = 10^8`) such that for every `k ≥ K` and
`n = 3k + 1`, augmenting the cyclic `k`-intervals by `C` explicit `k`-element seed
orbits detects every interior subset `A ⊆ Fin n` (`2 ≤ |A| ≤ n - 2`).

## Proof overview

1. **Weighted spectral detection criterion**: If a finite family of `k`-element seeds
   `S_i ⊆ Fin n` with nonnegative weights `w_i` summing to `1` satisfies
   `∑ i, w_i * ‖hat S_i ξ‖^2 > n^2 / (8 * (n - 2))` for every nonzero frequency
   `ξ : Fin n`, then the union of their cyclic orbits detects every interior subset `A`
   (by discrete Parseval on `Fin n` and the variance upper bound `1/4` for adjacent-valued
   intersection counts).
2. **Low-frequency seed (`lowSeed`)**: Take `s = Nat.sqrt n`, `a = 8 * s`, `M = k - a`,
   a nearly uniform background `U = {⌊j * n / M⌋ : j < M}` (whose Fourier sum at
   `1 ≤ min ξ (n - ξ) ≤ s / 96` is bounded by `2π * M * m / n ≤ s`), and `a` elements
   `I' ⊆ [0, 2a) \ U` (possible because consecutive elements of `U` differ by at least `3`).
   Every element of `I'` has phase in `[0, π/3]`, giving `‖hat lowSeed ξ‖ ≥ 3 * s`, so
   weight `1/32` already yields `(9/32) * s^2 > n^2 / (8*(n-2))`.
3. **High-frequency Golay family (`8 * (q + 1)` seeds, `q = 1000`)**: Decompose
   `T = 2*k - 6*s` into its top four powers of `2`, `L = L₀ + L₁ + L₂ + L₃ ≥ (15/16) * T`.
   Combine Golay complementary pairs on each block via the `4 × 4` Hadamard matrix to get
   `8` sequences `W_r ∈ {±1}^L` satisfying `∑_r ‖W_r(z)‖^2 = 8 * L` identically on `‖z‖ = 1`
   (hence `|sum W_r| ≤ 3 * s`, so both `±1` level sets have size `≤ k`). Pad the larger
   level set with a fixed interval `J₀` and the smaller with `J₀ ∪ D_j` for `q = 1000`
   consecutive disjoint intervals `D_j` of length `d_r = |sum W_r|`. Averaging over `j < q`
   turns the padding discrepancy into `(1/q)` times a single geometric sum bounded by
   `2 / (q * ‖z - 1‖)`, which is controlled uniformly for all `min ξ (n - ξ) > s / 96`.
-/

namespace LogRankCyclicDetector

open scoped BigOperators ComplexConjugate
open Finset

/-! ### Section 1: Elementary phase, complex, and trigonometric inequalities -/

noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private lemma phase_zero : phase 0 = 1 := by
  simp [phase]

private lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma phase_neg (x : ℝ) : phase (-x) = conj (phase x) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private lemma phase_nat (m : ℕ) : phase (m : ℝ) = 1 := by
  unfold phase
  have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
      (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

private lemma phase_pow (x : ℝ) (m : ℕ) : phase x ^ m = phase ((m : ℝ) * x) := by
  induction m with
  | zero => simp [phase_zero]
  | succ m ih =>
    rw [pow_succ, ih, ← phase_add]
    congr 1
    push_cast
    ring

private lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  unfold phase
  exact Complex.norm_exp_ofReal_mul_I _

private lemma phase_re (x : ℝ) : (phase x).re = Real.cos (2 * Real.pi * x) := by
  unfold phase
  exact Complex.exp_ofReal_mul_I_re _

private lemma phase_im (x : ℝ) : (phase x).im = Real.sin (2 * Real.pi * x) := by
  unfold phase
  exact Complex.exp_ofReal_mul_I_im _

private lemma sq_norm_phase_sub_one (x : ℝ) :
    ‖phase x - 1‖ ^ 2 = 4 * Real.sin (Real.pi * x) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero,
    phase_re, phase_im]
  have hcs := Real.sin_sq_add_cos_sq (2 * Real.pi * x)
  have hcs1 := Real.sin_sq_add_cos_sq (Real.pi * x)
  have hcos : Real.cos (2 * Real.pi * x) = 1 - 2 * Real.sin (Real.pi * x) ^ 2 := by
    have h2 : 2 * Real.pi * x = 2 * (Real.pi * x) := by ring
    rw [h2, Real.cos_two_mul]
    nlinarith
  nlinarith

private lemma norm_phase_sub_one_le (x : ℝ) : ‖phase x - 1‖ ≤ 2 * Real.pi * |x| := by
  have hsq : ‖phase x - 1‖ ^ 2 ≤ (2 * Real.pi * |x|) ^ 2 := by
    rw [sq_norm_phase_sub_one]
    have hsin : |Real.sin (Real.pi * x)| ≤ |Real.pi * x| := Real.abs_sin_le_abs
    have hsin2 : Real.sin (Real.pi * x) ^ 2 ≤ (Real.pi * x) ^ 2 := by
      have h1 : |Real.sin (Real.pi * x)| ^ 2 ≤ |Real.pi * x| ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hsin 2
      simpa only [sq_abs] using h1
    have hpi : (Real.pi * x) ^ 2 = (Real.pi * |x|) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
    nlinarith
  have hnonneg : 0 ≤ 2 * Real.pi * |x| := by positivity
  nlinarith [norm_nonneg (phase x - 1)]

private lemma norm_phase_sub_one_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    4 * x ≤ ‖phase x - 1‖ := by
  have hpi_nonneg : 0 ≤ Real.pi * x := by positivity
  have hpi_le : Real.pi * x ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hsin_ge : 2 * x ≤ Real.sin (Real.pi * x) := by
    have h := Real.mul_le_sin hpi_nonneg hpi_le
    have hcancel : 2 / Real.pi * (Real.pi * x) = 2 * x := by
      field_simp [ne_of_gt Real.pi_pos]
    linarith
  have hsq : (4 * x) ^ 2 ≤ ‖phase x - 1‖ ^ 2 := by
    rw [sq_norm_phase_sub_one]
    nlinarith [hsin_ge, hx0]
  nlinarith [norm_nonneg (phase x - 1), hx0]

private lemma norm_phase_sub_phase_le (x y : ℝ) :
    ‖phase x - phase y‖ ≤ 2 * Real.pi * |x - y| := by
  have hfac : phase x - phase y = phase y * (phase (x - y) - 1) := by
    rw [mul_sub, mul_one, ← phase_add]
    ring_nf
  rw [hfac, norm_mul, norm_phase, one_mul]
  exact norm_phase_sub_one_le (x - y)

private lemma parallelogram_complex (u v : ℂ) :
    ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im]
  ring

private lemma sq_norm_sub_ge (u v : ℂ) {η : ℝ} (hη : 0 < η) :
    (1 - η) * ‖u‖ ^ 2 - (1 / η) * ‖v‖ ^ 2 ≤ ‖u - v‖ ^ 2 := by
  suffices h : 0 ≤ η * (‖u - v‖ ^ 2 - ((1 - η) * ‖u‖ ^ 2 - (1 / η) * ‖v‖ ^ 2)) by
    nlinarith
  have h1 : η * (1 / η) = 1 := mul_one_div_cancel (ne_of_gt hη)
  have h2 : η * (‖u - v‖ ^ 2 - ((1 - η) * ‖u‖ ^ 2 - (1 / η) * ‖v‖ ^ 2)) =
      (η * u.re - v.re) ^ 2 + (η * u.im - v.im) ^ 2 + η * (v.re ^ 2 + v.im ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    calc
      η * ((u.re - v.re) * (u.re - v.re) + (u.im - v.im) * (u.im - v.im) -
          ((1 - η) * (u.re * u.re + u.im * u.im) - 1 / η * (v.re * v.re + v.im * v.im)))
        = η * ((u.re - v.re) ^ 2 + (u.im - v.im) ^ 2 - (1 - η) * (u.re ^ 2 + u.im ^ 2)) +
          (η * (1 / η)) * (v.re ^ 2 + v.im ^ 2) := by ring
      _ = (η * u.re - v.re) ^ 2 + (η * u.im - v.im) ^ 2 + η * (v.re ^ 2 + v.im ^ 2) := by
          rw [h1]; ring
  rw [h2]
  positivity

private lemma jensen_sq_norm {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s f) 2
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := sq_sum_le_card_mul_sum_sq

private lemma geom_sum_Ico_bound (a m : ℕ) {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ‖∑ j ∈ Finset.Ico a (a + m), z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  have hshift : ∑ j ∈ Finset.Ico a (a + m), z ^ j = z ^ a * ∑ j ∈ Finset.range m, z ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun j _ => j - a) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_Ico] at hj
      rw [Finset.mem_range]
      omega
    · intro j₁ hj₁ j₂ hj₂ h
      rw [Finset.mem_Ico] at hj₁ hj₂
      omega
    · intro r hr
      rw [Finset.mem_range] at hr
      refine ⟨a + r, Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩, by omega⟩
    · intro j hj
      rw [Finset.mem_Ico] at hj
      rw [← pow_add, Nat.add_sub_of_le hj.1]
  rw [hshift, geom_sum_eq hz1, norm_mul, norm_pow, hz, one_pow, one_mul, norm_div]
  have hnum : ‖z ^ m - 1‖ ≤ 2 := by
    calc
      ‖z ^ m - 1‖ ≤ ‖z ^ m‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_pow, hz, one_pow, norm_one]
      _ = 2 := by norm_num
  exact div_le_div_of_nonneg_right hnum (norm_nonneg _)

/-! ### Section 2: Finite Fourier transform and weighted spectral detection on `Fin n` -/

noncomputable def chi (n : ℕ) (ξ x : Fin n) : ℂ :=
  phase (((ξ.val * x.val : ℕ) : ℝ) / (n : ℝ))

private lemma chi_comm (n : ℕ) (ξ x : Fin n) : chi n ξ x = chi n x ξ := by
  simp [chi, Nat.mul_comm]

private lemma chi_zero_left (n : ℕ) [NeZero n] (x : Fin n) : chi n 0 x = 1 := by
  simp [chi, phase_zero]

private lemma norm_chi (n : ℕ) (ξ x : Fin n) : ‖chi n ξ x‖ = 1 :=
  norm_phase _

private lemma chi_add_right {n : ℕ} [NeZero n] (ξ x y : Fin n) :
    chi n ξ (x + y) = chi n ξ x * chi n ξ y := by
  unfold chi
  rw [← phase_add]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  set q := (x.val + y.val) / n
  have hmod : (x + y).val = (x.val + y.val) % n := rfl
  have hdiv : x.val + y.val = n * q + (x + y).val := by
    rw [hmod]
    exact (Nat.div_add_mod (x.val + y.val) n).symm
  have hnat : ξ.val * x.val + ξ.val * y.val = ξ.val * (x + y).val + n * (ξ.val * q) := by
    calc
      ξ.val * x.val + ξ.val * y.val = ξ.val * (x.val + y.val) := by ring
      _ = ξ.val * (n * q + (x + y).val) := by rw [hdiv]
      _ = ξ.val * (x + y).val + n * (ξ.val * q) := by ring
  have harg :
      ((ξ.val * x.val : ℕ) : ℝ) / (n : ℝ) + ((ξ.val * y.val : ℕ) : ℝ) / (n : ℝ) =
      ((ξ.val * (x + y).val : ℕ) : ℝ) / (n : ℝ) + ((ξ.val * q : ℕ) : ℝ) := by
    have hcast : ((ξ.val * x.val : ℕ) : ℝ) + ((ξ.val * y.val : ℕ) : ℝ) =
        ((ξ.val * (x + y).val : ℕ) : ℝ) + (n : ℝ) * ((ξ.val * q : ℕ) : ℝ) := by
      exact_mod_cast hnat
    field_simp [hn]
    linarith
  rw [harg, phase_add, phase_nat, mul_one]

private lemma chi_sub_right {n : ℕ} [NeZero n] (ξ x y : Fin n) :
    chi n ξ (x - y) = chi n ξ x * conj (chi n ξ y) := by
  have h1 : chi n ξ ((x - y) + y) = chi n ξ (x - y) * chi n ξ y := chi_add_right ξ (x - y) y
  rw [sub_add_cancel] at h1
  have hmul : chi n ξ y * conj (chi n ξ y) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_chi]
    norm_num
  calc
    chi n ξ (x - y) = chi n ξ (x - y) * (chi n ξ y * conj (chi n ξ y)) := by rw [hmul, mul_one]
    _ = (chi n ξ (x - y) * chi n ξ y) * conj (chi n ξ y) := by ring
    _ = chi n ξ x * conj (chi n ξ y) := by rw [h1]

private lemma chi_eq_pow {n : ℕ} (ξ x : Fin n) :
    chi n ξ x = phase ((ξ.val : ℝ) / (n : ℝ)) ^ x.val := by
  rw [chi, phase_pow]
  congr 1
  push_cast
  ring

private lemma phase_div_ne_one {n m : ℕ} (hm0 : 0 < m) (hmn : m < n) :
    phase ((m : ℝ) / (n : ℝ)) ≠ 1 := by
  intro heq
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_trans hm0 hmn
  by_cases hhalf : 2 * m ≤ n
  · have hge := norm_phase_sub_one_ge (x := (m : ℝ) / (n : ℝ)) (by positivity)
      (by
        rw [div_le_iff₀ hn]
        have : (2 : ℝ) * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hhalf
        linarith)
    rw [heq, sub_self, norm_zero] at hge
    have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
    have : 0 < 4 * ((m : ℝ) / (n : ℝ)) := by positivity
    linarith
  · have hcomp0 : 0 < n - m := by omega
    have hcomp2 : 2 * (n - m) ≤ n := by omega
    have hge := norm_phase_sub_one_ge (x := ((n - m : ℕ) : ℝ) / (n : ℝ)) (by positivity)
      (by
        rw [div_le_iff₀ hn]
        have : (2 : ℝ) * ((n - m : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcomp2
        linarith)
    have hphase_eq : phase (((n - m : ℕ) : ℝ) / (n : ℝ)) = conj (phase ((m : ℝ) / (n : ℝ))) := by
      have harg : (((n - m : ℕ) : ℝ) / (n : ℝ)) = (1 : ℝ) + (-((m : ℝ) / (n : ℝ))) := by
        rw [Nat.cast_sub (le_of_lt hmn)]
        field_simp [ne_of_gt hn]
        ring
      rw [harg, phase_add, show phase (1 : ℝ) = 1 from by simpa using phase_nat 1, one_mul,
        phase_neg]
    rw [hphase_eq, heq, map_one, sub_self, norm_zero] at hge
    have hc' : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by exact_mod_cast hcomp0
    have : 0 < 4 * (((n - m : ℕ) : ℝ) / (n : ℝ)) := by positivity
    linarith

private lemma sum_chi_right {n : ℕ} [NeZero n] (ξ : Fin n) :
    ∑ x : Fin n, chi n ξ x = if ξ = 0 then (n : ℂ) else 0 := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp [chi_zero_left]
  · simp only [hξ, ↓reduceIte]
    have hpos : 0 < ξ.val := Nat.pos_of_ne_zero (fun h => hξ (Fin.ext h))
    have hz1 : phase ((ξ.val : ℝ) / (n : ℝ)) ≠ 1 := phase_div_ne_one hpos ξ.isLt
    have hsum : ∑ x : Fin n, chi n ξ x =
        ∑ j ∈ Finset.range n, phase ((ξ.val : ℝ) / (n : ℝ)) ^ j := by
      calc
        ∑ x : Fin n, chi n ξ x = ∑ x : Fin n, phase ((ξ.val : ℝ) / (n : ℝ)) ^ x.val :=
          Finset.sum_congr rfl fun x _ => chi_eq_pow ξ x
        _ = ∑ j ∈ Finset.range n, phase ((ξ.val : ℝ) / (n : ℝ)) ^ j :=
          Fin.sum_univ_eq_sum_range (fun j => phase ((ξ.val : ℝ) / (n : ℝ)) ^ j) n
    rw [hsum, geom_sum_eq hz1, phase_pow]
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    have hmul : (n : ℝ) * ((ξ.val : ℝ) / (n : ℝ)) = (ξ.val : ℝ) := mul_div_cancel₀ _ hn
    rw [hmul, phase_nat, sub_self, zero_div]

noncomputable def hat (n : ℕ) (f : Fin n → ℂ) (ξ : Fin n) : ℂ :=
  ∑ x : Fin n, f x * chi n ξ x

noncomputable def hatSet (n : ℕ) (S : Finset (Fin n)) (ξ : Fin n) : ℂ :=
  ∑ x ∈ S, chi n ξ x

private lemma hatSet_eq_hat (n : ℕ) (S : Finset (Fin n)) (ξ : Fin n) :
    hatSet n S ξ = hat n (fun x => if x ∈ S then 1 else 0) ξ := by
  unfold hatSet hat
  have hpt : ∀ x : Fin n, (if x ∈ S then (1 : ℂ) else 0) * chi n ξ x =
      if x ∈ S then chi n ξ x else 0 := by
    intro x
    split_ifs <;> simp
  simp_rw [hpt, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp

private lemma parseval (n : ℕ) [NeZero n] (f : Fin n → ℂ) :
    ∑ ξ : Fin n, ‖hat n f ξ‖ ^ 2 = (n : ℝ) * ∑ x : Fin n, ‖f x‖ ^ 2 := by
  have hterm (z : ℂ) : ((‖z‖ : ℂ) ^ 2) = z * conj z := by
    rw [← Complex.ofReal_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hc : ((∑ ξ : Fin n, ‖hat n f ξ‖ ^ 2 : ℝ) : ℂ) =
      (((n : ℝ) * ∑ x : Fin n, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    simp_rw [hterm]
    calc
      ∑ ξ : Fin n, hat n f ξ * conj (hat n f ξ)
        = ∑ ξ : Fin n, ∑ x : Fin n, ∑ y : Fin n,
            f x * chi n ξ x * (conj (f y) * conj (chi n ξ y)) := by
          refine Finset.sum_congr rfl fun ξ _ => ?_
          unfold hat
          rw [map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => by rw [map_mul]
      _ = ∑ x : Fin n, ∑ y : Fin n, f x * conj (f y) * ∑ ξ : Fin n, chi n (x - y) ξ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ξ _ => ?_
          rw [chi_comm n (x - y) ξ, chi_sub_right]
          ring
      _ = (n : ℂ) * ∑ x : Fin n, f x * conj (f x) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_eq_single x]
          · simp [sum_chi_right]; ring
          · intro y _ hyx
            have hne : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyx)
            simp [sum_chi_right, hne]
          · intro hx
            exact absurd (Finset.mem_univ x) hx
  exact Complex.ofReal_inj.mp hc

private lemma parseval_set (n : ℕ) [NeZero n] (A : Finset (Fin n)) :
    ∑ ξ ∈ Finset.univ.erase (0 : Fin n), ‖hatSet n A ξ‖ ^ 2 =
      (A.card : ℝ) * ((n : ℝ) - (A.card : ℝ)) := by
  have hp := parseval n (fun x => if x ∈ A then (1 : ℂ) else 0)
  have hlhs : ∑ ξ : Fin n, ‖hat n (fun x => if x ∈ A then (1 : ℂ) else 0) ξ‖ ^ 2 =
      ‖hatSet n A 0‖ ^ 2 + ∑ ξ ∈ Finset.univ.erase (0 : Fin n), ‖hatSet n A ξ‖ ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin n))]
    congr 1
    · rw [hatSet_eq_hat]
    · refine Finset.sum_congr rfl fun ξ _ => by rw [hatSet_eq_hat]
  have h0 : ‖hatSet n A 0‖ ^ 2 = (A.card : ℝ) ^ 2 := by
    unfold hatSet
    simp only [chi_zero_left, Finset.sum_const, nsmul_eq_mul, mul_one, Complex.norm_natCast]
  have hrhs : ∑ x : Fin n, ‖(if x ∈ A then (1 : ℂ) else 0)‖ ^ 2 = (A.card : ℝ) := by
    have : ∀ x : Fin n, ‖(if x ∈ A then (1 : ℂ) else 0)‖ ^ 2 = if x ∈ A then (1 : ℝ) else 0 := by
      intro x; split_ifs <;> simp
    simp_rw [this, Finset.sum_boole]
    simp
  rw [hlhs, h0, hrhs] at hp
  nlinarith

private lemma hat_inter_shift {n : ℕ} [NeZero n] (A S : Finset (Fin n)) (ξ : Fin n) :
    hat n (fun t => ((A ∩ S.image (fun i => i + t)).card : ℂ)) ξ =
      hatSet n A ξ * conj (hatSet n S ξ) := by
  have hcard (t : Fin n) :
      ((A ∩ S.image (fun i => i + t)).card : ℂ) =
        ∑ x ∈ A, ∑ y ∈ S, if y + t = x then (1 : ℂ) else 0 := by
    have hinj : ∀ x ∈ A, (∑ y ∈ S, if y + t = x then (1 : ℂ) else 0) =
        if x ∈ S.image (fun i => i + t) then 1 else 0 := by
      intro x _
      by_cases hx : x ∈ S.image (fun i => i + t)
      · rw [ite_eq_left hx]
        obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hx
        rw [Finset.sum_eq_single y₀]
        · simp
        · intro y _ hne
          have : y + t ≠ y₀ + t := fun h => hne (add_right_cancel h)
          simp [this]
        · intro h
          exact absurd hy₀ h
      · rw [ite_eq_right hx]
        refine Finset.sum_eq_zero fun y hy => ?_
        have : y + t ≠ x := fun h => hx (Finset.mem_image.mpr ⟨y, hy, h⟩)
        simp [this]
    rw [Finset.sum_congr rfl hinj]
    have hfilt : (∑ x ∈ A, if x ∈ S.image (fun i => i + t) then (1 : ℂ) else 0) =
        ((A.filter (fun x => x ∈ S.image (fun i => i + t))).card : ℂ) := by
      rw [Finset.sum_boole]
    rw [hfilt, Finset.filter_mem_eq_inter]
  unfold hat
  simp_rw [hcard, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h1 :
      ∑ x ∈ A, ∑ t : Fin n, ∑ y ∈ S, (if y + t = x then (1 : ℂ) else 0) * chi n ξ t =
      ∑ x ∈ A, ∑ y ∈ S, chi n ξ x * conj (chi n ξ y) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single (x - y)]
    · rw [add_sub_cancel, ite_eq_left rfl, one_mul, chi_sub_right]
    · intro t _ ht
      have hne : y + t ≠ x := fun h => ht (eq_sub_of_add_eq' h)
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h1]
  unfold hatSet
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]

private lemma orbit_variance_le_quarter {n : ℕ} [NeZero n] (A S : Finset (Fin n)) (a : ℤ)
    (hadj : ∀ t : Fin n,
      ((A ∩ S.image (fun i => i + t)).card : ℤ) = a ∨
      ((A ∩ S.image (fun i => i + t)).card : ℤ) = a + 1) :
    ∑ ξ ∈ Finset.univ.erase (0 : Fin n), ‖hatSet n A ξ‖ ^ 2 * ‖hatSet n S ξ‖ ^ 2 ≤
      (n : ℝ) ^ 2 / 4 := by
  let v : Fin n → ℝ := fun t => ((A ∩ S.image (fun i => i + t)).card : ℝ)
  let g : Fin n → ℂ := fun t => (v t : ℂ)
  have h0 : hat n g 0 = ((A.card * S.card : ℕ) : ℂ) := by
    have hg := hat_inter_shift A S 0
    simp only [hatSet, chi_zero_left, Finset.sum_const, nsmul_eq_mul, mul_one, map_natCast] at hg
    simpa [g, v] using hg
  have hsum_v : ∑ t : Fin n, v t = (A.card : ℝ) * (S.card : ℝ) := by
    have hre := congrArg Complex.re h0
    simp only [hat, g, chi_zero_left, mul_one, Complex.re_sum, Complex.ofReal_re,
      Nat.cast_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero,
      sub_zero] at hre
    exact hre
  have hp := parseval n g
  have hsplit : ∑ ξ : Fin n, ‖hat n g ξ‖ ^ 2 =
      ‖hat n g 0‖ ^ 2 +
        ∑ ξ ∈ Finset.univ.erase (0 : Fin n), ‖hatSet n A ξ‖ ^ 2 * ‖hatSet n S ξ‖ ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin n))]
    congr 1
    refine Finset.sum_congr rfl fun ξ _ => ?_
    have hg : hat n g ξ = hatSet n A ξ * conj (hatSet n S ξ) := by
      simpa [g, v] using hat_inter_shift A S ξ
    rw [hg, norm_mul, Complex.norm_conj, mul_pow]
  have hnorm0 : ‖hat n g 0‖ ^ 2 = ((A.card : ℝ) * (S.card : ℝ)) ^ 2 := by
    rw [h0, Complex.norm_natCast, Nat.cast_mul]
  have hnorm_g : ∑ t : Fin n, ‖g t‖ ^ 2 = ∑ t : Fin n, (v t) ^ 2 := by
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [g, Real.norm_eq_abs, sq_abs]
  rw [hsplit, hnorm0, hnorm_g] at hp
  have hquarter : ∑ t : Fin n, (v t - ((a : ℝ) + 1 / 2)) ^ 2 = (n : ℝ) / 4 := by
    have hpt : ∀ t : Fin n, (v t - ((a : ℝ) + 1 / 2)) ^ 2 = 1 / 4 := by
      intro t
      rcases hadj t with h | h
      · have hr : v t = (a : ℝ) := by
          dsimp only [v]
          exact_mod_cast h
        rw [hr]; ring
      · have hr : v t = (a : ℝ) + 1 := by
          dsimp only [v]
          have : ((A ∩ S.image (fun i => i + t)).card : ℝ) = ((a + 1 : ℤ) : ℝ) := by
            exact_mod_cast h
          simpa using this
        rw [hr]; ring
    simp_rw [hpt]
    simp [div_eq_mul_inv]
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  let μ : ℝ := ((A.card : ℝ) * (S.card : ℝ)) / (n : ℝ)
  have hvar_eq : ∑ t : Fin n, (v t - ((a : ℝ) + 1 / 2)) ^ 2 =
      (∑ t : Fin n, (v t) ^ 2) - 2 * ((a : ℝ) + 1 / 2) * (∑ t : Fin n, v t) +
        (n : ℝ) * ((a : ℝ) + 1 / 2) ^ 2 := by
    have hexp : ∀ t : Fin n, (v t - ((a : ℝ) + 1 / 2)) ^ 2 =
        (v t) ^ 2 - 2 * ((a : ℝ) + 1 / 2) * v t + ((a : ℝ) + 1 / 2) ^ 2 := fun t => by ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdiff_nonneg : 0 ≤ (n : ℝ) * ((n : ℝ) * (μ - ((a : ℝ) + 1 / 2)) ^ 2) := by positivity
  have hstep : (n : ℝ) * (∑ t : Fin n, (v t) ^ 2) - ((A.card : ℝ) * (S.card : ℝ)) ^ 2 ≤
      (n : ℝ) ^ 2 / 4 := by
    have hcalc : (n : ℝ) * (∑ t : Fin n, (v t) ^ 2) - ((A.card : ℝ) * (S.card : ℝ)) ^ 2 =
        (n : ℝ) * (∑ t : Fin n, (v t - ((a : ℝ) + 1 / 2)) ^ 2) -
          (n : ℝ) * ((n : ℝ) * (μ - ((a : ℝ) + 1 / 2)) ^ 2) := by
      rw [hvar_eq, hsum_v]
      dsimp only [μ]
      field_simp [ne_of_gt hn_pos]
      ring
    rw [hcalc, hquarter]
    linarith [hdiff_nonneg]
  linarith

private lemma weighted_spectral_detection {n : ℕ} [NeZero n] (hn4 : 4 ≤ n)
    {ι : Type*} [Fintype ι] (S : ι → Finset (Fin n)) (w : ι → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hspec : ∀ ξ : Fin n, ξ ≠ 0 →
      (n : ℝ) ^ 2 / (8 * ((n : ℝ) - 2)) < ∑ i, w i * ‖hatSet n (S i) ξ‖ ^ 2)
    (Y : Finset (Finset (Fin n)))
    (hY : ∀ i (t : Fin n), (S i).image (fun x => x + t) ∈ Y) :
    ∀ A : Finset (Fin n), 2 ≤ A.card → A.card + 2 ≤ n → ∀ a : ℤ,
      ∃ B ∈ Y, ¬ (((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a + 1) := by
  intro A hA2 hAn a
  by_contra hnone
  push Not at hnone
  have hupper :
      ∑ ξ ∈ Finset.univ.erase (0 : Fin n),
        ‖hatSet n A ξ‖ ^ 2 * (∑ i, w i * ‖hatSet n (S i) ξ‖ ^ 2) ≤ (n : ℝ) ^ 2 / 4 := by
    have hswap :
        ∑ ξ ∈ Finset.univ.erase (0 : Fin n),
          ‖hatSet n A ξ‖ ^ 2 * (∑ i, w i * ‖hatSet n (S i) ξ‖ ^ 2) =
        ∑ i, w i * ∑ ξ ∈ Finset.univ.erase (0 : Fin n),
          ‖hatSet n A ξ‖ ^ 2 * ‖hatSet n (S i) ξ‖ ^ 2 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ξ _ => by ring
    rw [hswap]
    calc
      ∑ i, w i * ∑ ξ ∈ Finset.univ.erase (0 : Fin n),
          ‖hatSet n A ξ‖ ^ 2 * ‖hatSet n (S i) ξ‖ ^ 2
        ≤ ∑ i, w i * ((n : ℝ) ^ 2 / 4) := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hw_nonneg i)
          exact orbit_variance_le_quarter A (S i) a (fun t => hnone _ (hY i t))
      _ = (∑ i, w i) * ((n : ℝ) ^ 2 / 4) := by rw [← Finset.sum_mul]
      _ = (n : ℝ) ^ 2 / 4 := by rw [hw_sum, one_mul]
  have hA_energy : 2 * ((n : ℝ) - 2) ≤ ∑ ξ ∈ Finset.univ.erase (0 : Fin n), ‖hatSet n A ξ‖ ^ 2 := by
    rw [parseval_set]
    have h1 : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA2
    have h2 : (A.card : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hAn
    nlinarith
  have hn2_pos : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    linarith
  have hex_pos : ∃ ξ₀ ∈ Finset.univ.erase (0 : Fin n), 0 < ‖hatSet n A ξ₀‖ ^ 2 := by
    by_contra hall
    push Not at hall
    have hle0 : ∑ ξ ∈ Finset.univ.erase (0 : Fin n), ‖hatSet n A ξ‖ ^ 2 ≤ 0 :=
      Finset.sum_nonpos fun ξ hξ => hall ξ hξ
    linarith
  obtain ⟨ξ₀, hξ₀, hAξ₀⟩ := hex_pos
  have hstrict :
      ∑ ξ ∈ Finset.univ.erase (0 : Fin n),
        ‖hatSet n A ξ‖ ^ 2 * ((n : ℝ) ^ 2 / (8 * ((n : ℝ) - 2))) <
      ∑ ξ ∈ Finset.univ.erase (0 : Fin n),
        ‖hatSet n A ξ‖ ^ 2 * (∑ i, w i * ‖hatSet n (S i) ξ‖ ^ 2) := by
    refine Finset.sum_lt_sum ?_ ⟨ξ₀, hξ₀, ?_⟩
    · intro ξ hξ
      have hne : ξ ≠ 0 := (Finset.mem_erase.mp hξ).1
      exact mul_le_mul_of_nonneg_left (le_of_lt (hspec ξ hne)) (sq_nonneg _)
    · have hne : ξ₀ ≠ 0 := (Finset.mem_erase.mp hξ₀).1
      exact mul_lt_mul_of_pos_left (hspec ξ₀ hne) hAξ₀
  have hlower :
      (n : ℝ) ^ 2 / 4 ≤
        ∑ ξ ∈ Finset.univ.erase (0 : Fin n),
          ‖hatSet n A ξ‖ ^ 2 * ((n : ℝ) ^ 2 / (8 * ((n : ℝ) - 2))) := by
    rw [← Finset.sum_mul]
    have hfrac : 0 ≤ (n : ℝ) ^ 2 / (8 * ((n : ℝ) - 2)) := by positivity
    calc
      (n : ℝ) ^ 2 / 4 = (2 * ((n : ℝ) - 2)) * ((n : ℝ) ^ 2 / (8 * ((n : ℝ) - 2))) := by
        field_simp [ne_of_gt hn2_pos]
        ring
      _ ≤ (∑ ξ ∈ Finset.univ.erase (0 : Fin n), ‖hatSet n A ξ‖ ^ 2) *
            ((n : ℝ) ^ 2 / (8 * ((n : ℝ) - 2))) := mul_le_mul_of_nonneg_right hA_energy hfrac
  linarith

/-! ### Section 3: Conjugate symmetry, scale helpers, and the low-frequency seed `lowSeed` -/

private lemma norm_hatSet_neg {n : ℕ} [NeZero n] (S : Finset (Fin n)) (ξ : Fin n) :
    ‖hatSet n S (-ξ)‖ = ‖hatSet n S ξ‖ := by
  have hconj : hatSet n S (-ξ) = conj (hatSet n S ξ) := by
    unfold hatSet
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [chi_comm n (-ξ) x]
    have hsub := chi_sub_right x (0 : Fin n) ξ
    rw [zero_sub, chi_comm n x 0, chi_zero_left, one_mul, chi_comm n x ξ] at hsub
    exact hsub
  rw [hconj, Complex.norm_conj]

private lemma neg_val_of_ne_zero {n : ℕ} [NeZero n] {ξ : Fin n} (hξ : ξ ≠ 0) :
    (-ξ).val = n - ξ.val := by
  rw [Fin.val_neg, ite_eq_right hξ]

private lemma scale_bounds {k : ℕ} (hk : 100000000 ≤ k) :
    17000 ≤ Nat.sqrt (3 * k + 1) ∧
    8 * Nat.sqrt (3 * k + 1) < k ∧
    2 * (8 * Nat.sqrt (3 * k + 1)) < 3 * k + 1 ∧
    6 * Nat.sqrt (3 * k + 1) ≤ 2 * k ∧
    3000 * Nat.sqrt (3 * k + 1) ≤ k := by
  set s := Nat.sqrt (3 * k + 1)
  have hs_sq : s * s ≤ 3 * k + 1 := Nat.sqrt_le (3 * k + 1)
  have hs_lt : 3 * k + 1 < (s + 1) * (s + 1) := Nat.lt_succ_sqrt (3 * k + 1)
  have h1 : 17000 ≤ s := by
    by_contra hlt
    have : s + 1 ≤ 17000 := by omega
    nlinarith
  have h5 : 3000 * s ≤ k := by
    by_contra hlt
    have : k + 1 ≤ 3000 * s := by omega
    have hsq1 : (k + 1) * (k + 1) ≤ (3000 * s) * (3000 * s) := Nat.mul_le_mul this this
    have hsq2 : (3000 * s) * (3000 * s) ≤ 9000000 * (3 * k + 1) := by nlinarith
    nlinarith
  refine ⟨h1, by omega, by omega, by omega, h5⟩

def uniformBgPt (k a : ℕ) (ha : a < k) (j : Fin (k - a)) : Fin (3 * k + 1) :=
  ⟨(j.val * (3 * k + 1)) / (k - a), by
    have hM : 0 < k - a := by omega
    exact (Nat.div_lt_iff_lt_mul hM).mpr (by nlinarith [j.isLt])⟩

def uniformBg (k a : ℕ) (ha : a < k) : Finset (Fin (3 * k + 1)) :=
  Finset.univ.image (uniformBgPt k a ha)

private lemma uniformBg_gap {k a : ℕ} (ha : a < k) {j₁ j₂ : ℕ} (hlt : j₁ < j₂) :
    (j₁ * (3 * k + 1)) / (k - a) + 3 ≤ (j₂ * (3 * k + 1)) / (k - a) := by
  have hM : 0 < k - a := by omega
  have hstep : 3 * (k - a) ≤ 3 * k + 1 := by omega
  have hmul : j₁ * (3 * k + 1) + 3 * (k - a) ≤ j₂ * (3 * k + 1) := by
    have hj : j₁ + 1 ≤ j₂ := hlt
    nlinarith
  calc
    (j₁ * (3 * k + 1)) / (k - a) + 3
      = (j₁ * (3 * k + 1) + 3 * (k - a)) / (k - a) := by
        rw [Nat.add_mul_div_right _ _ hM]
    _ ≤ (j₂ * (3 * k + 1)) / (k - a) := Nat.div_le_div_right hmul

private lemma uniformBgPt_injective {k a : ℕ} (ha : a < k) :
    Function.Injective (uniformBgPt k a ha) := by
  intro j₁ j₂ h
  apply Fin.ext
  have hval : (j₁.val * (3 * k + 1)) / (k - a) = (j₂.val * (3 * k + 1)) / (k - a) :=
    congrArg Fin.val h
  rcases lt_trichotomy j₁.val j₂.val with hlt | heq | hgt
  · have := uniformBg_gap ha hlt; omega
  · exact heq
  · have := uniformBg_gap ha hgt; omega

private lemma uniformBg_card {k a : ℕ} (ha : a < k) :
    (uniformBg k a ha).card = k - a := by
  unfold uniformBg
  rw [Finset.card_image_of_injective _ (uniformBgPt_injective ha), Finset.card_univ,
    Fintype.card_fin]

private lemma uniformBg_no_adj {k a : ℕ} (ha : a < k) (x y : Fin (3 * k + 1))
    (hx : x ∈ uniformBg k a ha) (hy : y ∈ uniformBg k a ha) (hxy : x.val + 1 = y.val) :
    False := by
  unfold uniformBg at hx hy
  obtain ⟨j₁, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j₂, _, rfl⟩ := Finset.mem_image.mp hy
  dsimp only [uniformBgPt] at hxy
  rcases lt_trichotomy j₁.val j₂.val with hlt | heq | hgt
  · have := uniformBg_gap ha hlt; omega
  · rw [heq] at hxy; omega
  · have := uniformBg_gap ha hgt; omega

def lowSpikePt (k a : ℕ) (ha : a < k) (h2a : 2 * a < 3 * k + 1) (r : Fin a) :
    Fin (3 * k + 1) :=
  let p : Fin (3 * k + 1) := ⟨2 * r.val, by omega⟩
  if p ∈ uniformBg k a ha then ⟨2 * r.val + 1, by omega⟩ else p

private lemma lowSpikePt_val_eq (k a : ℕ) (ha : a < k) (h2a : 2 * a < 3 * k + 1) (r : Fin a) :
    (lowSpikePt k a ha h2a r).val = 2 * r.val ∨
    (lowSpikePt k a ha h2a r).val = 2 * r.val + 1 := by
  unfold lowSpikePt
  dsimp only
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

private lemma lowSpikePt_injective {k a : ℕ} (ha : a < k) (h2a : 2 * a < 3 * k + 1) :
    Function.Injective (lowSpikePt k a ha h2a) := by
  intro r₁ r₂ h
  apply Fin.ext
  have hv := congrArg Fin.val h
  rcases lowSpikePt_val_eq k a ha h2a r₁ with h1 | h1 <;>
    rcases lowSpikePt_val_eq k a ha h2a r₂ with h2 | h2 <;> omega

private lemma lowSpikePt_not_mem {k a : ℕ} (ha : a < k) (h2a : 2 * a < 3 * k + 1) (r : Fin a) :
    lowSpikePt k a ha h2a r ∉ uniformBg k a ha := by
  unfold lowSpikePt
  dsimp only
  split_ifs with hp
  · intro hU
    exact uniformBg_no_adj ha _ _ hp hU rfl
  · exact hp

def lowSpike (k a : ℕ) (ha : a < k) (h2a : 2 * a < 3 * k + 1) : Finset (Fin (3 * k + 1)) :=
  Finset.univ.image (lowSpikePt k a ha h2a)

private lemma lowSpike_card {k a : ℕ} (ha : a < k) (h2a : 2 * a < 3 * k + 1) :
    (lowSpike k a ha h2a).card = a := by
  unfold lowSpike
  rw [Finset.card_image_of_injective _ (lowSpikePt_injective ha h2a), Finset.card_univ,
    Fintype.card_fin]

private lemma lowSpike_disjoint {k a : ℕ} (ha : a < k) (h2a : 2 * a < 3 * k + 1) :
    Disjoint (lowSpike k a ha h2a) (uniformBg k a ha) := by
  rw [Finset.disjoint_left]
  intro x hx
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hx
  exact lowSpikePt_not_mem ha h2a r

private lemma lowSpike_val_lt {k a : ℕ} (ha : a < k) (h2a : 2 * a < 3 * k + 1)
    {x : Fin (3 * k + 1)} (hx : x ∈ lowSpike k a ha h2a) : x.val < 2 * a := by
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hx
  rcases lowSpikePt_val_eq k a ha h2a r with h1 | h1 <;> omega

def lowSeed (k a : ℕ) (ha : a < k) (h2a : 2 * a < 3 * k + 1) : Finset (Fin (3 * k + 1)) :=
  lowSpike k a ha h2a ∪ uniformBg k a ha

private lemma lowSeed_card {k a : ℕ} (ha : a < k) (h2a : 2 * a < 3 * k + 1) :
    (lowSeed k a ha h2a).card = k := by
  unfold lowSeed
  rw [Finset.card_union_of_disjoint (lowSpike_disjoint ha h2a),
    lowSpike_card, uniformBg_card]
  omega

private lemma hatSet_uniformBg_le {k a : ℕ} (ha : a < k)
    (ξ : Fin (3 * k + 1)) (hξ0 : 0 < ξ.val) (hξM : ξ.val < k - a) :
    ‖hatSet (3 * k + 1) (uniformBg k a ha) ξ‖ ≤
      2 * Real.pi * ((k - a : ℕ) : ℝ) * (ξ.val : ℝ) / ((3 * k + 1 : ℕ) : ℝ) := by
  have hMpos : 0 < k - a := by omega
  let : NeZero (k - a) := ⟨Nat.ne_of_gt hMpos⟩
  have hMr : (0 : ℝ) < ((k - a : ℕ) : ℝ) := by exact_mod_cast hMpos
  have hnr : (0 : ℝ) < ((3 * k + 1 : ℕ) : ℝ) := by positivity
  have hsum_U :
      hatSet (3 * k + 1) (uniformBg k a ha) ξ =
        ∑ j : Fin (k - a), chi (3 * k + 1) ξ (uniformBgPt k a ha j) := by
    unfold hatSet uniformBg
    rw [Finset.sum_image (fun x _ y _ h => uniformBgPt_injective ha h)]
  let ξM : Fin (k - a) := ⟨ξ.val, hξM⟩
  have hξM_ne : ξM ≠ 0 := fun h => by
    have : ξ.val = 0 := congrArg Fin.val h
    omega
  have hzero : ∑ j : Fin (k - a), chi (k - a) ξM j = 0 := by
    rw [sum_chi_right, ite_eq_right hξM_ne]
  have hdiff : hatSet (3 * k + 1) (uniformBg k a ha) ξ =
      ∑ j : Fin (k - a), (chi (3 * k + 1) ξ (uniformBgPt k a ha j) - chi (k - a) ξM j) := by
    rw [hsum_U, Finset.sum_sub_distrib, hzero, sub_zero]
  rw [hdiff]
  calc
    ‖∑ j : Fin (k - a), (chi (3 * k + 1) ξ (uniformBgPt k a ha j) - chi (k - a) ξM j)‖
      ≤ ∑ j : Fin (k - a), ‖chi (3 * k + 1) ξ (uniformBgPt k a ha j) - chi (k - a) ξM j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j : Fin (k - a), (2 * Real.pi * (ξ.val : ℝ) / ((3 * k + 1 : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        unfold chi uniformBgPt
        dsimp only [ξM]
        set u := (j.val * (3 * k + 1)) / (k - a)
        have hle : (k - a) * u ≤ j.val * (3 * k + 1) := Nat.mul_div_le (j.val * (3 * k + 1)) (k - a)
        have hlt : j.val * (3 * k + 1) < (k - a) * u + (k - a) := by
          have hdm : (k - a) * u + (j.val * (3 * k + 1)) % (k - a) = j.val * (3 * k + 1) :=
            Nat.div_add_mod (j.val * (3 * k + 1)) (k - a)
          have hmlt : (j.val * (3 * k + 1)) % (k - a) < k - a :=
            Nat.mod_lt (j.val * (3 * k + 1)) hMpos
          omega
        have hdiff_abs :
            |(((ξ.val * u : ℕ) : ℝ) / ((3 * k + 1 : ℕ) : ℝ)) -
              (((ξ.val * j.val : ℕ) : ℝ) / ((k - a : ℕ) : ℝ))| ≤
              (ξ.val : ℝ) / ((3 * k + 1 : ℕ) : ℝ) := by
          have h1 : ((k - a : ℕ) : ℝ) * (u : ℝ) ≤ (j.val : ℝ) * ((3 * k + 1 : ℕ) : ℝ) := by
            exact_mod_cast hle
          have h2 : (j.val : ℝ) * ((3 * k + 1 : ℕ) : ℝ) ≤
              ((k - a : ℕ) : ℝ) * (u : ℝ) + ((k - a : ℕ) : ℝ) := by
            exact_mod_cast le_of_lt hlt
          have hsub :
              (((ξ.val * u : ℕ) : ℝ) / ((3 * k + 1 : ℕ) : ℝ)) -
                (((ξ.val * j.val : ℕ) : ℝ) / ((k - a : ℕ) : ℝ)) =
                (ξ.val : ℝ) * (((k - a : ℕ) : ℝ) * (u : ℝ) -
                  (j.val : ℝ) * ((3 * k + 1 : ℕ) : ℝ)) /
                  (((3 * k + 1 : ℕ) : ℝ) * ((k - a : ℕ) : ℝ)) := by
            push_cast
            field_simp [ne_of_gt hnr, ne_of_gt hMr]
          rw [hsub, abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
            abs_of_pos (mul_pos hnr hMr)]
          have hba : |((k - a : ℕ) : ℝ) * (u : ℝ) - (j.val : ℝ) * ((3 * k + 1 : ℕ) : ℝ)| ≤
              ((k - a : ℕ) : ℝ) := by
            rw [abs_le]
            constructor <;> linarith
          calc
            (ξ.val : ℝ) * |((k - a : ℕ) : ℝ) * (u : ℝ) - (j.val : ℝ) * ((3 * k + 1 : ℕ) : ℝ)| /
                (((3 * k + 1 : ℕ) : ℝ) * ((k - a : ℕ) : ℝ))
              ≤ (ξ.val : ℝ) * ((k - a : ℕ) : ℝ) / (((3 * k + 1 : ℕ) : ℝ) * ((k - a : ℕ) : ℝ)) :=
                div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hba (Nat.cast_nonneg _)) (by positivity)
            _ = (ξ.val : ℝ) / ((3 * k + 1 : ℕ) : ℝ) := by
                field_simp [ne_of_gt hnr, ne_of_gt hMr]
        calc
          ‖phase (((ξ.val * u : ℕ) : ℝ) / ((3 * k + 1 : ℕ) : ℝ)) -
              phase (((ξ.val * j.val : ℕ) : ℝ) / ((k - a : ℕ) : ℝ))‖
            ≤ 2 * Real.pi *
                |(((ξ.val * u : ℕ) : ℝ) / ((3 * k + 1 : ℕ) : ℝ)) -
                  (((ξ.val * j.val : ℕ) : ℝ) / ((k - a : ℕ) : ℝ))| :=
              norm_phase_sub_phase_le _ _
          _ ≤ 2 * Real.pi * ((ξ.val : ℝ) / ((3 * k + 1 : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hdiff_abs (by positivity)
          _ = 2 * Real.pi * (ξ.val : ℝ) / ((3 * k + 1 : ℕ) : ℝ) := by ring
    _ = 2 * Real.pi * ((k - a : ℕ) : ℝ) * (ξ.val : ℝ) / ((3 * k + 1 : ℕ) : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

private lemma hatSet_lowSeed_ge {k : ℕ} (hk : 100000000 ≤ k)
    (ha : 8 * Nat.sqrt (3 * k + 1) < k) (h2a : 2 * (8 * Nat.sqrt (3 * k + 1)) < 3 * k + 1)
    (ξ : Fin (3 * k + 1)) (hξ0 : 0 < ξ.val) (hξ_low : 96 * ξ.val ≤ Nat.sqrt (3 * k + 1)) :
    9 * (Nat.sqrt (3 * k + 1) : ℝ) ^ 2 ≤
      ‖hatSet (3 * k + 1) (lowSeed k (8 * Nat.sqrt (3 * k + 1)) ha h2a) ξ‖ ^ 2 := by
  have hs_sq : Nat.sqrt (3 * k + 1) * Nat.sqrt (3 * k + 1) ≤ 3 * k + 1 :=
    Nat.sqrt_le (3 * k + 1)
  have hsc := scale_bounds hk
  have hnr : (0 : ℝ) < ((3 * k + 1 : ℕ) : ℝ) := by positivity
  have hsr : (0 : ℝ) ≤ (Nat.sqrt (3 * k + 1) : ℝ) := Nat.cast_nonneg _
  have hspike_re :
      4 * (Nat.sqrt (3 * k + 1) : ℝ) ≤
        (hatSet (3 * k + 1) (lowSpike k (8 * Nat.sqrt (3 * k + 1)) ha h2a) ξ).re := by
    unfold hatSet
    rw [Complex.re_sum]
    have hpt : ∀ x ∈ lowSpike k (8 * Nat.sqrt (3 * k + 1)) ha h2a,
        (1 / 2 : ℝ) ≤ (chi (3 * k + 1) ξ x).re := by
      intro x hx
      have hxlt : x.val < 2 * (8 * Nat.sqrt (3 * k + 1)) := lowSpike_val_lt ha h2a hx
      rw [chi, phase_re, ← Real.cos_pi_div_three]
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · positivity
      · linarith [Real.pi_pos]
      · have hprod : 6 * (ξ.val * x.val) ≤ 3 * k + 1 := by
          have h1 : 96 * (ξ.val * x.val) ≤ Nat.sqrt (3 * k + 1) * (16 * Nat.sqrt (3 * k + 1)) := by
            have hxa : x.val ≤ 16 * Nat.sqrt (3 * k + 1) := by omega
            calc
              96 * (ξ.val * x.val) = (96 * ξ.val) * x.val := by ring
              _ ≤ Nat.sqrt (3 * k + 1) * (16 * Nat.sqrt (3 * k + 1)) :=
                Nat.mul_le_mul hξ_low hxa
          nlinarith
        have hprod' : (6 : ℝ) * ((ξ.val * x.val : ℕ) : ℝ) ≤ ((3 * k + 1 : ℕ) : ℝ) := by
          exact_mod_cast hprod
        have hdiv : ((ξ.val * x.val : ℕ) : ℝ) / ((3 * k + 1 : ℕ) : ℝ) ≤ 1 / 6 := by
          rw [div_le_iff₀ hnr]; linarith
        nlinarith [Real.pi_pos]
    calc
      4 * (Nat.sqrt (3 * k + 1) : ℝ)
        = ((lowSpike k (8 * Nat.sqrt (3 * k + 1)) ha h2a).card : ℝ) * (1 / 2 : ℝ) := by
          rw [lowSpike_card]; push_cast; ring
      _ = ∑ _x ∈ lowSpike k (8 * Nat.sqrt (3 * k + 1)) ha h2a, (1 / 2 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ lowSpike k (8 * Nat.sqrt (3 * k + 1)) ha h2a, (chi (3 * k + 1) ξ x).re :=
          Finset.sum_le_sum hpt
  have hspike_norm :
      4 * (Nat.sqrt (3 * k + 1) : ℝ) ≤
        ‖hatSet (3 * k + 1) (lowSpike k (8 * Nat.sqrt (3 * k + 1)) ha h2a) ξ‖ :=
    hspike_re.trans (Complex.re_le_norm _)
  have hξM : ξ.val < k - 8 * Nat.sqrt (3 * k + 1) := by omega
  have hbg_norm :
      ‖hatSet (3 * k + 1) (uniformBg k (8 * Nat.sqrt (3 * k + 1)) ha) ξ‖ ≤
        (Nat.sqrt (3 * k + 1) : ℝ) := by
    have h1 := hatSet_uniformBg_le ha ξ hξ0 hξM
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have hMle : ((k - 8 * Nat.sqrt (3 * k + 1) : ℕ) : ℝ) ≤ ((3 * k + 1 : ℕ) : ℝ) / 3 := by
      have : 3 * (k - 8 * Nat.sqrt (3 * k + 1)) ≤ 3 * k + 1 := by omega
      have : (3 : ℝ) * ((k - 8 * Nat.sqrt (3 * k + 1) : ℕ) : ℝ) ≤ ((3 * k + 1 : ℕ) : ℝ) := by
        exact_mod_cast this
      linarith
    have hξle : (ξ.val : ℝ) ≤ (Nat.sqrt (3 * k + 1) : ℝ) / 96 := by
      have : (96 : ℝ) * (ξ.val : ℝ) ≤ (Nat.sqrt (3 * k + 1) : ℝ) := by exact_mod_cast hξ_low
      linarith
    calc
      ‖hatSet (3 * k + 1) (uniformBg k (8 * Nat.sqrt (3 * k + 1)) ha) ξ‖
        ≤ 2 * Real.pi * ((k - 8 * Nat.sqrt (3 * k + 1) : ℕ) : ℝ) * (ξ.val : ℝ) /
            ((3 * k + 1 : ℕ) : ℝ) := h1
      _ ≤ 2 * 4 * (((3 * k + 1 : ℕ) : ℝ) / 3) * ((Nat.sqrt (3 * k + 1) : ℝ) / 96) /
            ((3 * k + 1 : ℕ) : ℝ) := by
          apply div_le_div_of_nonneg_right _ hnr.le
          have hpos1 : 0 ≤ 2 * Real.pi * ((k - 8 * Nat.sqrt (3 * k + 1) : ℕ) : ℝ) := by positivity
          calc
            2 * Real.pi * ((k - 8 * Nat.sqrt (3 * k + 1) : ℕ) : ℝ) * (ξ.val : ℝ)
              ≤ 2 * Real.pi * ((k - 8 * Nat.sqrt (3 * k + 1) : ℕ) : ℝ) *
                  ((Nat.sqrt (3 * k + 1) : ℝ) / 96) :=
                mul_le_mul_of_nonneg_left hξle hpos1
            _ ≤ 2 * 4 * (((3 * k + 1 : ℕ) : ℝ) / 3) * ((Nat.sqrt (3 * k + 1) : ℝ) / 96) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                calc
                  2 * Real.pi * ((k - 8 * Nat.sqrt (3 * k + 1) : ℕ) : ℝ)
                    ≤ 2 * 4 * ((k - 8 * Nat.sqrt (3 * k + 1) : ℕ) : ℝ) := by
                      nlinarith [Nat.cast_nonneg (α := ℝ) (k - 8 * Nat.sqrt (3 * k + 1))]
                  _ ≤ 2 * 4 * (((3 * k + 1 : ℕ) : ℝ) / 3) := by nlinarith
      _ = (Nat.sqrt (3 * k + 1) : ℝ) / 36 := by field_simp [ne_of_gt hnr]; ring
      _ ≤ (Nat.sqrt (3 * k + 1) : ℝ) := by linarith
  have hsum_union :
      hatSet (3 * k + 1) (lowSeed k (8 * Nat.sqrt (3 * k + 1)) ha h2a) ξ =
        hatSet (3 * k + 1) (lowSpike k (8 * Nat.sqrt (3 * k + 1)) ha h2a) ξ +
          hatSet (3 * k + 1) (uniformBg k (8 * Nat.sqrt (3 * k + 1)) ha) ξ := by
    unfold hatSet lowSeed
    exact Finset.sum_union (lowSpike_disjoint ha h2a)
  have hnorm_ge :
      3 * (Nat.sqrt (3 * k + 1) : ℝ) ≤
        ‖hatSet (3 * k + 1) (lowSeed k (8 * Nat.sqrt (3 * k + 1)) ha h2a) ξ‖ := by
    rw [hsum_union]
    have htri := norm_add_le
      (hatSet (3 * k + 1) (lowSpike k (8 * Nat.sqrt (3 * k + 1)) ha h2a) ξ +
        hatSet (3 * k + 1) (uniformBg k (8 * Nat.sqrt (3 * k + 1)) ha) ξ)
      (-hatSet (3 * k + 1) (uniformBg k (8 * Nat.sqrt (3 * k + 1)) ha) ξ)
    rw [add_neg_cancel_right, norm_neg] at htri
    linarith
  calc
    9 * (Nat.sqrt (3 * k + 1) : ℝ) ^ 2 = (3 * (Nat.sqrt (3 * k + 1) : ℝ)) ^ 2 := by ring
    _ ≤ ‖hatSet (3 * k + 1) (lowSeed k (8 * Nat.sqrt (3 * k + 1)) ha h2a) ξ‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hnorm_ge 2

/-! ### Section 4: 4-block Golay complementary sequences and Hadamard assembly -/

def golayPair : ℕ → ℕ → ℤ × ℤ
  | 0, _ => (1, 1)
  | m + 1, j =>
      if j < 2 ^ m then
        ((golayPair m j).1, (golayPair m j).1)
      else
        ((golayPair m (j - 2 ^ m)).2, -(golayPair m (j - 2 ^ m)).2)

def golayA (m j : ℕ) : ℤ := (golayPair m j).1
def golayB (m j : ℕ) : ℤ := (golayPair m j).2

private lemma golay_pm_one (m : ℕ) :
    ∀ j, (golayA m j = 1 ∨ golayA m j = -1) ∧ (golayB m j = 1 ∨ golayB m j = -1) := by
  induction m with
  | zero => intro j; simp [golayA, golayB, golayPair]
  | succ m ih =>
    intro j
    unfold golayA golayB golayPair
    split_ifs
    · exact ⟨(ih j).1, (ih j).1⟩
    · refine ⟨(ih (j - 2 ^ m)).2, ?_⟩
      rcases (ih (j - 2 ^ m)).2 with h | h <;> simp [golayB] at h ⊢ <;> simp [h]

noncomputable def golayPolyA (m : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (2 ^ m), (golayA m j : ℂ) * z ^ j

noncomputable def golayPolyB (m : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (2 ^ m), (golayB m j : ℂ) * z ^ j

private lemma golay_poly_succ (m : ℕ) (z : ℂ) :
    golayPolyA (m + 1) z = golayPolyA m z + z ^ (2 ^ m) * golayPolyB m z ∧
    golayPolyB (m + 1) z = golayPolyA m z - z ^ (2 ^ m) * golayPolyB m z := by
  have hsplit (f : ℕ → ℂ) :
      ∑ j ∈ Finset.range (2 ^ (m + 1)), f j =
        (∑ j ∈ Finset.range (2 ^ m), f j) + ∑ j ∈ Finset.range (2 ^ m), f (j + 2 ^ m) := by
    have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
    rw [h2, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun j _ => by rw [Nat.add_comm]
  constructor
  · unfold golayPolyA
    rw [hsplit]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      simp [golayA, golayPair, Finset.mem_range.mp hj]
    · rw [golayPolyB, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hge : ¬ j + 2 ^ m < 2 ^ m := by omega
      simp only [golayA, golayB, golayPair, hge, ↓reduceIte, Nat.add_sub_cancel, pow_add]
      ring
  · unfold golayPolyB
    rw [hsplit, sub_eq_add_neg]
    congr 1
    · unfold golayPolyA
      refine Finset.sum_congr rfl fun j hj => ?_
      simp [golayA, golayB, golayPair, Finset.mem_range.mp hj]
    · rw [← neg_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hge : ¬ j + 2 ^ m < 2 ^ m := by omega
      simp only [golayB, golayPair, hge, ↓reduceIte, Nat.add_sub_cancel, Int.cast_neg, pow_add]
      ring

private lemma golay_sq_sum (m : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖golayPolyA m z‖ ^ 2 + ‖golayPolyB m z‖ ^ 2 = 2 * (2 ^ m : ℝ) := by
  induction m with
  | zero =>
    simp [golayPolyA, golayPolyB, golayA, golayB, golayPair]
    norm_num
  | succ m ih =>
    obtain ⟨hA, hB⟩ := golay_poly_succ m z
    rw [hA, hB, parallelogram_complex, norm_mul, norm_pow, hz, one_pow, one_mul, ih]
    ring

def optLen : Option ℕ → ℕ
  | none => 0
  | some m => 2 ^ m

def optGolay (isB : Bool) : Option ℕ → ℕ → ℤ
  | none, _ => 1
  | some m, j => if isB then golayB m j else golayA m j

private lemma optGolay_pm_one (isB : Bool) (opt : Option ℕ) (j : ℕ) :
    optGolay isB opt j = 1 ∨ optGolay isB opt j = -1 := by
  cases opt with
  | none => exact Or.inl rfl
  | some m =>
    unfold optGolay
    cases isB
    · simpa using (golay_pm_one m j).1
    · simpa using (golay_pm_one m j).2

noncomputable def optPoly (isB : Bool) (opt : Option ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (optLen opt), (optGolay isB opt j : ℂ) * z ^ j

private lemma opt_sq_sum (opt : Option ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖optPoly false opt z‖ ^ 2 + ‖optPoly true opt z‖ ^ 2 = 2 * (optLen opt : ℝ) := by
  cases opt with
  | none => simp [optPoly, optLen]
  | some m =>
    simpa [optPoly, optLen, optGolay, golayPolyA, golayPolyB] using golay_sq_sum m hz

def topPow2 (x : ℕ) : Option ℕ :=
  if x = 0 then none else some (Nat.log 2 x)

private lemma topPow2_le (x : ℕ) : optLen (topPow2 x) ≤ x := by
  unfold topPow2
  split_ifs with hx
  · simp [optLen]
  · simp only [optLen]
    exact Nat.pow_log_le_self 2 hx

private lemma topPow2_rem (x : ℕ) : 2 * (x - optLen (topPow2 x)) ≤ x := by
  unfold topPow2
  split_ifs with hx
  · subst hx; simp [optLen]
  · simp only [optLen]
    have hlt : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
    have hpow : 2 ^ (Nat.log 2 x + 1) = 2 * 2 ^ Nat.log 2 x := by ring
    omega

def block4 (T : ℕ) (i : Fin 4) : Option ℕ :=
  let b0 := topPow2 T
  let r1 := T - optLen b0
  let b1 := topPow2 r1
  let r2 := r1 - optLen b1
  let b2 := topPow2 r2
  let r3 := r2 - optLen b2
  let b3 := topPow2 r3
  match i.val with
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | _ => b3

def block4Len (T : ℕ) (i : Fin 4) : ℕ := optLen (block4 T i)

def block4Total (T : ℕ) : ℕ :=
  block4Len T 0 + block4Len T 1 + block4Len T 2 + block4Len T 3

private lemma block4Total_bounds (T : ℕ) :
    block4Total T ≤ T ∧ 15 * T ≤ 16 * block4Total T := by
  unfold block4Total block4Len block4
  dsimp only
  set b0 := topPow2 T
  set r1 := T - optLen b0
  set b1 := topPow2 r1
  set r2 := r1 - optLen b1
  set b2 := topPow2 r2
  set r3 := r2 - optLen b2
  set b3 := topPow2 r3
  set r4 := r3 - optLen b3
  have h0le : optLen b0 ≤ T := topPow2_le T
  have h1le : optLen b1 ≤ r1 := topPow2_le r1
  have h2le : optLen b2 ≤ r2 := topPow2_le r2
  have h3le : optLen b3 ≤ r3 := topPow2_le r3
  have h0r : 2 * r1 ≤ T := topPow2_rem T
  have h1r : 2 * r2 ≤ r1 := topPow2_rem r1
  have h2r : 2 * r3 ≤ r2 := topPow2_rem r2
  have h3r : 2 * r4 ≤ r3 := topPow2_rem r3
  have heq1 : optLen b0 + r1 = T := Nat.add_sub_of_le h0le
  have heq2 : optLen b1 + r2 = r1 := Nat.add_sub_of_le h1le
  have heq3 : optLen b2 + r3 = r2 := Nat.add_sub_of_le h2le
  have heq4 : optLen b3 + r4 = r3 := Nat.add_sub_of_le h3le
  change optLen b0 + optLen b1 + optLen b2 + optLen b3 ≤ T ∧
    15 * T ≤ 16 * (optLen b0 + optLen b1 + optLen b2 + optLen b3)
  omega

def hadamard4 (r i : Fin 4) : ℤ :=
  match r.val, i.val with
  | 0, _ => 1
  | 1, 0 => 1
  | 1, 1 => 1
  | 1, _ => -1
  | 2, 0 => 1
  | 2, 2 => 1
  | 2, _ => -1
  | _, 0 => 1
  | _, 3 => 1
  | _, _ => -1

private lemma hadamard4_pm_one (r i : Fin 4) :
    hadamard4 r i = 1 ∨ hadamard4 r i = -1 := by
  fin_cases r <;> fin_cases i <;> decide

private lemma hadamard4_sq_sum (c : Fin 4 → ℂ) :
    ∑ r : Fin 4, ‖∑ i : Fin 4, (hadamard4 r i : ℂ) * c i‖ ^ 2 =
      4 * ∑ i : Fin 4, ‖c i‖ ^ 2 := by
  simp only [Fin.sum_univ_four, hadamard4, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num [Complex.sq_norm, Complex.normSq_apply]
  ring

def golaySeq (T : ℕ) (r : Fin 4) (isB : Bool) (j : ℕ) : ℤ :=
  if j < block4Len T 0 then
    hadamard4 r 0 * optGolay isB (block4 T 0) j
  else if j < block4Len T 0 + block4Len T 1 then
    hadamard4 r 1 * optGolay isB (block4 T 1) (j - block4Len T 0)
  else if j < block4Len T 0 + block4Len T 1 + block4Len T 2 then
    hadamard4 r 2 * optGolay isB (block4 T 2) (j - (block4Len T 0 + block4Len T 1))
  else
    hadamard4 r 3 * optGolay isB (block4 T 3) (j - (block4Len T 0 + block4Len T 1 + block4Len T 2))

private lemma golaySeq_pm_one (T : ℕ) (r : Fin 4) (isB : Bool) (j : ℕ) :
    golaySeq T r isB j = 1 ∨ golaySeq T r isB j = -1 := by
  have hmul : ∀ a b : ℤ, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) → a * b = 1 ∨ a * b = -1 := by
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
  unfold golaySeq
  split_ifs
  · exact hmul _ _ (hadamard4_pm_one r 0) (optGolay_pm_one isB _ _)
  · exact hmul _ _ (hadamard4_pm_one r 1) (optGolay_pm_one isB _ _)
  · exact hmul _ _ (hadamard4_pm_one r 2) (optGolay_pm_one isB _ _)
  · exact hmul _ _ (hadamard4_pm_one r 3) (optGolay_pm_one isB _ _)

noncomputable def golaySeqPoly (T : ℕ) (r : Fin 4) (isB : Bool) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (block4Total T), (golaySeq T r isB j : ℂ) * z ^ j

def block4Off (T : ℕ) (i : Fin 4) : ℕ :=
  match i.val with
  | 0 => 0
  | 1 => block4Len T 0
  | 2 => block4Len T 0 + block4Len T 1
  | _ => block4Len T 0 + block4Len T 1 + block4Len T 2

private lemma golaySeqPoly_eq (T : ℕ) (r : Fin 4) (isB : Bool) (z : ℂ) :
    golaySeqPoly T r isB z =
      ∑ i : Fin 4, (hadamard4 r i : ℂ) * (z ^ block4Off T i * optPoly isB (block4 T i) z) := by
  rw [Fin.sum_univ_four]
  unfold golaySeqPoly block4Total
  rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
  change _ = (hadamard4 r 0 : ℂ) * (z ^ 0 * optPoly isB (block4 T 0) z) +
      (hadamard4 r 1 : ℂ) * (z ^ block4Len T 0 * optPoly isB (block4 T 1) z) +
      (hadamard4 r 2 : ℂ) * (z ^ (block4Len T 0 + block4Len T 1) * optPoly isB (block4 T 2) z) +
      (hadamard4 r 3 : ℂ) *
        (z ^ (block4Len T 0 + block4Len T 1 + block4Len T 2) * optPoly isB (block4 T 3) z)
  congr 1
  · congr 1
    · congr 1
      · rw [pow_zero, one_mul, optPoly, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hlt : j < block4Len T 0 := Finset.mem_range.mp hj
        rw [golaySeq, ite_eq_left hlt, Int.cast_mul]
        ring
      · rw [optPoly, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hlt : j < block4Len T 1 := Finset.mem_range.mp hj
        have h1 : ¬ block4Len T 0 + j < block4Len T 0 := by omega
        have h2 : block4Len T 0 + j < block4Len T 0 + block4Len T 1 := by omega
        rw [golaySeq, ite_eq_right h1, ite_eq_left h2, Nat.add_sub_cancel_left, Int.cast_mul,
          pow_add]
        ring
    · rw [optPoly, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hlt : j < block4Len T 2 := Finset.mem_range.mp hj
      have h1 : ¬ (block4Len T 0 + block4Len T 1) + j < block4Len T 0 := by omega
      have h2 : ¬ (block4Len T 0 + block4Len T 1) + j < block4Len T 0 + block4Len T 1 := by omega
      have h3 : (block4Len T 0 + block4Len T 1) + j <
          block4Len T 0 + block4Len T 1 + block4Len T 2 := by omega
      rw [golaySeq, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, Nat.add_sub_cancel_left,
        Int.cast_mul, pow_add]
      ring
  · rw [optPoly, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : ¬ (block4Len T 0 + block4Len T 1 + block4Len T 2) + j < block4Len T 0 := by omega
    have h2 : ¬ (block4Len T 0 + block4Len T 1 + block4Len T 2) + j <
        block4Len T 0 + block4Len T 1 := by omega
    have h3 : ¬ (block4Len T 0 + block4Len T 1 + block4Len T 2) + j <
        block4Len T 0 + block4Len T 1 + block4Len T 2 := by omega
    rw [golaySeq, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, Nat.add_sub_cancel_left,
      Int.cast_mul, pow_add]
    ring

private lemma golaySeq_sq_sum (T : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ∑ r : Fin 4, (‖golaySeqPoly T r false z‖ ^ 2 + ‖golaySeqPoly T r true z‖ ^ 2) =
      8 * (block4Total T : ℝ) := by
  have hsingle (isB : Bool) :
      ∑ r : Fin 4, ‖golaySeqPoly T r isB z‖ ^ 2 =
        4 * ∑ i : Fin 4, ‖optPoly isB (block4 T i) z‖ ^ 2 := by
    let c : Fin 4 → ℂ := fun i => z ^ block4Off T i * optPoly isB (block4 T i) z
    have h1 : ∀ r : Fin 4, golaySeqPoly T r isB z = ∑ i : Fin 4, (hadamard4 r i : ℂ) * c i :=
      fun r => golaySeqPoly_eq T r isB z
    simp_rw [h1]
    rw [hadamard4_sq_sum c]
    apply congrArg (4 * ·)
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [c, norm_mul, norm_pow, hz, one_pow, one_mul]
  rw [Finset.sum_add_distrib, hsingle false, hsingle true, ← mul_add, ← Finset.sum_add_distrib]
  have hopt : ∑ i : Fin 4, (‖optPoly false (block4 T i) z‖ ^ 2 + ‖optPoly true (block4 T i) z‖ ^ 2) =
      2 * (block4Total T : ℝ) := by
    have hpt : ∀ i : Fin 4,
        ‖optPoly false (block4 T i) z‖ ^ 2 + ‖optPoly true (block4 T i) z‖ ^ 2 =
          2 * (block4Len T i : ℝ) := fun i => opt_sq_sum (block4 T i) hz
    simp_rw [hpt, ← Finset.mul_sum, Fin.sum_univ_four]
    unfold block4Total
    push_cast
    ring
  rw [hopt]
  ring

private lemma golaySeq_sum_sq_le (T : ℕ) (r : Fin 4) (isB : Bool) :
    ((∑ j ∈ Finset.range (block4Total T), golaySeq T r isB j : ℤ) : ℝ) ^ 2 ≤
      8 * (block4Total T : ℝ) := by
  have h1 := golaySeq_sq_sum T (z := (1 : ℂ)) norm_one
  have hinner : ‖golaySeqPoly T r isB 1‖ ^ 2 ≤
      ‖golaySeqPoly T r false 1‖ ^ 2 + ‖golaySeqPoly T r true 1‖ ^ 2 := by
    cases isB
    · linarith [sq_nonneg ‖golaySeqPoly T r true 1‖]
    · linarith [sq_nonneg ‖golaySeqPoly T r false 1‖]
  have houter :
      ‖golaySeqPoly T r false 1‖ ^ 2 + ‖golaySeqPoly T r true 1‖ ^ 2 ≤
        ∑ r' : Fin 4, (‖golaySeqPoly T r' false 1‖ ^ 2 + ‖golaySeqPoly T r' true 1‖ ^ 2) :=
    Finset.single_le_sum
      (f := fun r' : Fin 4 => ‖golaySeqPoly T r' false 1‖ ^ 2 + ‖golaySeqPoly T r' true 1‖ ^ 2)
      (fun r' _ => by positivity) (Finset.mem_univ r)
  have hval : ‖golaySeqPoly T r isB 1‖ ^ 2 =
      ((∑ j ∈ Finset.range (block4Total T), golaySeq T r isB j : ℤ) : ℝ) ^ 2 := by
    unfold golaySeqPoly
    simp only [one_pow, mul_one]
    have hcast : (∑ j ∈ Finset.range (block4Total T), (golaySeq T r isB j : ℂ)) =
        (((∑ j ∈ Finset.range (block4Total T), golaySeq T r isB j : ℤ) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  linarith

/-! ### Section 5: Parametric Golay seeds (`q` consecutive interval pads) and high-frequency bound -/

def finIco (n a b : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun x : Fin n => a ≤ x.val ∧ x.val < b

private lemma finIco_card {n a b : ℕ} (hb : b ≤ n) :
    (finIco n a b).card = b - a := by
  rw [← Nat.card_Ico a b]
  refine Finset.card_bij (fun x _ => x.val) ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hx).2
  · intro x _ y _ h
    exact Fin.ext h
  · intro j hj
    have hj' := Finset.mem_Ico.mp hj
    refine ⟨⟨j, lt_of_lt_of_le hj'.2 hb⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩, rfl⟩

private lemma hatSet_finIco {n a b : ℕ} (hb : b ≤ n) (ξ : Fin n) :
    hatSet n (finIco n a b) ξ =
      ∑ j ∈ Finset.Ico a b, phase ((ξ.val : ℝ) / (n : ℝ)) ^ j := by
  unfold hatSet
  refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hx).2
  · intro x _ y _ h
    exact Fin.ext h
  · intro j hj
    have hj' := Finset.mem_Ico.mp hj
    refine ⟨⟨j, lt_of_lt_of_le hj'.2 hb⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩, rfl⟩
  · intro x _
    exact chi_eq_pow ξ x

private lemma sum_Ico_blocks {α : Type*} [AddCommMonoid α] (f : ℕ → α) (base d q : ℕ) :
    ∑ j ∈ Finset.range q, ∑ m ∈ Finset.Ico (base + j * d) (base + (j + 1) * d), f m =
      ∑ m ∈ Finset.Ico base (base + q * d), f m := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : base ≤ base + q * d := Nat.le_add_right _ _
    have h2 : base + q * d ≤ base + (q + 1) * d := by
      have : q * d ≤ (q + 1) * d := Nat.mul_le_mul_right d (Nat.le_succ q)
      omega
    exact Finset.sum_Ico_consecutive f h1 h2

def golayPosSet (n T : ℕ) (r : Fin 4) (isB : Bool) : Finset (Fin n) :=
  Finset.univ.filter fun x : Fin n => x.val < block4Total T ∧ golaySeq T r isB x.val = 1

def golayNegSet (n T : ℕ) (r : Fin 4) (isB : Bool) : Finset (Fin n) :=
  Finset.univ.filter fun x : Fin n => x.val < block4Total T ∧ golaySeq T r isB x.val = -1

private lemma golayPos_neg_disjoint (n T : ℕ) (r : Fin 4) (isB : Bool) :
    Disjoint (golayPosSet n T r isB) (golayNegSet n T r isB) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  have h1 := (Finset.mem_filter.mp hx).2.2
  have h2 := (Finset.mem_filter.mp hy).2.2
  omega

private lemma golayPos_neg_union (n T : ℕ) (r : Fin 4) (isB : Bool) :
    golayPosSet n T r isB ∪ golayNegSet n T r isB = finIco n 0 (block4Total T) := by
  ext x
  simp only [Finset.mem_union, golayPosSet, golayNegSet, finIco, Finset.mem_filter,
    Finset.mem_univ, true_and, Nat.zero_le]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    rcases golaySeq_pm_one T r isB x.val with h1 | h1
    · exact Or.inl ⟨h, h1⟩
    · exact Or.inr ⟨h, h1⟩

private lemma golayPos_neg_card_sum {n T : ℕ} (hLn : block4Total T ≤ n)
    (r : Fin 4) (isB : Bool) :
    (golayPosSet n T r isB).card + (golayNegSet n T r isB).card = block4Total T := by
  rw [← Finset.card_union_of_disjoint (golayPos_neg_disjoint n T r isB),
    golayPos_neg_union, finIco_card hLn, Nat.sub_zero]

private lemma golayPos_neg_card_sub {n T : ℕ} (hLn : block4Total T ≤ n)
    (r : Fin 4) (isB : Bool) :
    ((golayPosSet n T r isB).card : ℤ) - ((golayNegSet n T r isB).card : ℤ) =
      ∑ j ∈ Finset.range (block4Total T), golaySeq T r isB j := by
  have h1 :
      ∑ x ∈ finIco n 0 (block4Total T), golaySeq T r isB x.val =
        ((golayPosSet n T r isB).card : ℤ) - ((golayNegSet n T r isB).card : ℤ) := by
    rw [← golayPos_neg_union, Finset.sum_union (golayPos_neg_disjoint n T r isB)]
    have hp : ∑ x ∈ golayPosSet n T r isB, golaySeq T r isB x.val =
        ((golayPosSet n T r isB).card : ℤ) := by
      calc
        ∑ x ∈ golayPosSet n T r isB, golaySeq T r isB x.val
          = ∑ _x ∈ golayPosSet n T r isB, (1 : ℤ) :=
            Finset.sum_congr rfl fun x hx => (Finset.mem_filter.mp hx).2.2
        _ = ((golayPosSet n T r isB).card : ℤ) := by simp
    have hn : ∑ x ∈ golayNegSet n T r isB, golaySeq T r isB x.val =
        -((golayNegSet n T r isB).card : ℤ) := by
      calc
        ∑ x ∈ golayNegSet n T r isB, golaySeq T r isB x.val
          = ∑ _x ∈ golayNegSet n T r isB, (-1 : ℤ) :=
            Finset.sum_congr rfl fun x hx => (Finset.mem_filter.mp hx).2.2
        _ = -((golayNegSet n T r isB).card : ℤ) := by simp
    rw [hp, hn, sub_eq_add_neg]
  rw [← h1]
  refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2.2
  · intro x _ y _ h
    exact Fin.ext h
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    refine ⟨⟨j, lt_of_lt_of_le hj' hLn⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.zero_le _, hj'⟩, rfl⟩
  · intro _ _
    rfl

private lemma hatSet_golayPos_sub_neg {n T : ℕ} (hLn : block4Total T ≤ n)
    (r : Fin 4) (isB : Bool) (ξ : Fin n) :
    hatSet n (golayPosSet n T r isB) ξ - hatSet n (golayNegSet n T r isB) ξ =
      golaySeqPoly T r isB (phase ((ξ.val : ℝ) / (n : ℝ))) := by
  have hsum :
      ∑ x ∈ finIco n 0 (block4Total T), (golaySeq T r isB x.val : ℂ) * chi n ξ x =
        hatSet n (golayPosSet n T r isB) ξ - hatSet n (golayNegSet n T r isB) ξ := by
    rw [← golayPos_neg_union, Finset.sum_union (golayPos_neg_disjoint n T r isB)]
    have hp : ∑ x ∈ golayPosSet n T r isB, (golaySeq T r isB x.val : ℂ) * chi n ξ x =
        hatSet n (golayPosSet n T r isB) ξ := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.mp hx).2.2]
      simp
    have hn : ∑ x ∈ golayNegSet n T r isB, (golaySeq T r isB x.val : ℂ) * chi n ξ x =
        -hatSet n (golayNegSet n T r isB) ξ := by
      unfold hatSet
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.mp hx).2.2]
      simp
    rw [hp, hn, sub_eq_add_neg]
  rw [← hsum, golaySeqPoly]
  refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2.2
  · intro x _ y _ h
    exact Fin.ext h
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    refine ⟨⟨j, lt_of_lt_of_le hj' hLn⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.zero_le _, hj'⟩, rfl⟩
  · intro x _
    rw [chi_eq_pow]

def golayBigSet (n T : ℕ) (r : Fin 4) (isB : Bool) : Finset (Fin n) :=
  if (golayNegSet n T r isB).card ≤ (golayPosSet n T r isB).card
  then golayPosSet n T r isB
  else golayNegSet n T r isB

def golaySmallSet (n T : ℕ) (r : Fin 4) (isB : Bool) : Finset (Fin n) :=
  if (golayNegSet n T r isB).card ≤ (golayPosSet n T r isB).card
  then golayNegSet n T r isB
  else golayPosSet n T r isB

def golaySign (n T : ℕ) (r : Fin 4) (isB : Bool) : ℂ :=
  if (golayNegSet n T r isB).card ≤ (golayPosSet n T r isB).card then 1 else -1

private lemma golayBig_small_props {n T : ℕ} (hLn : block4Total T ≤ n)
    (r : Fin 4) (isB : Bool) :
    (golaySmallSet n T r isB).card ≤ (golayBigSet n T r isB).card ∧
    (golayBigSet n T r isB).card + (golaySmallSet n T r isB).card = block4Total T ∧
    (∀ x ∈ golayBigSet n T r isB, x.val < block4Total T) ∧
    (∀ x ∈ golaySmallSet n T r isB, x.val < block4Total T) ∧
    (((golayBigSet n T r isB).card - (golaySmallSet n T r isB).card : ℕ) : ℝ) ^ 2 ≤
      8 * (block4Total T : ℝ) := by
  have hsum := golayPos_neg_card_sum hLn r isB
  have hsub := golayPos_neg_card_sub hLn r isB
  have hsq := golaySeq_sum_sq_le T r isB
  unfold golayBigSet golaySmallSet
  split_ifs with hle
  · refine ⟨hle, hsum, fun x hx => (Finset.mem_filter.mp hx).2.1,
      fun x hx => (Finset.mem_filter.mp hx).2.1, ?_⟩
    have hcast :
        (((golayPosSet n T r isB).card - (golayNegSet n T r isB).card : ℕ) : ℝ) =
          ((∑ j ∈ Finset.range (block4Total T), golaySeq T r isB j : ℤ) : ℝ) := by
      rw [← hsub, Nat.cast_sub hle]
      push_cast
      rfl
    rw [hcast]
    exact hsq
  · have hlt : (golayPosSet n T r isB).card ≤ (golayNegSet n T r isB).card := by omega
    refine ⟨hlt, by omega, fun x hx => (Finset.mem_filter.mp hx).2.1,
      fun x hx => (Finset.mem_filter.mp hx).2.1, ?_⟩
    have hcast :
        (((golayNegSet n T r isB).card - (golayPosSet n T r isB).card : ℕ) : ℝ) =
          -((∑ j ∈ Finset.range (block4Total T), golaySeq T r isB j : ℤ) : ℝ) := by
      rw [← hsub, Nat.cast_sub hlt]
      push_cast
      ring
    rw [hcast, neg_sq]
    exact hsq

private lemma hatSet_golayBig_sub_small {n T : ℕ} (hLn : block4Total T ≤ n)
    (r : Fin 4) (isB : Bool) (ξ : Fin n) :
    hatSet n (golayBigSet n T r isB) ξ - hatSet n (golaySmallSet n T r isB) ξ =
      golaySign n T r isB * golaySeqPoly T r isB (phase ((ξ.val : ℝ) / (n : ℝ))) := by
  unfold golayBigSet golaySmallSet golaySign
  split_ifs
  · rw [one_mul, hatSet_golayPos_sub_neg hLn]
  · rw [neg_one_mul, ← hatSet_golayPos_sub_neg hLn]
    ring

private lemma norm_golaySign (n T : ℕ) (r : Fin 4) (isB : Bool) :
    ‖golaySign n T r isB‖ = 1 := by
  unfold golaySign
  split_ifs <;> simp

def golayPadBig (k T : ℕ) (r : Fin 4) (isB : Bool) : Finset (Fin (3 * k + 1)) :=
  let L := block4Total T
  let big := golayBigSet (3 * k + 1) T r isB
  big ∪ finIco (3 * k + 1) L (L + (k - big.card))

def golayPadSmall (k T q : ℕ) (r : Fin 4) (isB : Bool) (j : Fin q) : Finset (Fin (3 * k + 1)) :=
  let L := block4Total T
  let big := golayBigSet (3 * k + 1) T r isB
  let small := golaySmallSet (3 * k + 1) T r isB
  let p0 := k - big.card
  let d := big.card - small.card
  small ∪ finIco (3 * k + 1) L (L + p0) ∪
    finIco (3 * k + 1) (L + p0 + j.val * d) (L + p0 + (j.val + 1) * d)

private lemma golayPad_bounds {k q : ℕ} (hk : 100000000 ≤ k) (hq : q ≤ 1000)
    (r : Fin 4) (isB : Bool) :
    block4Total (2 * k - 6 * Nat.sqrt (3 * k + 1)) ≤ 3 * k + 1 ∧
    (golayBigSet (3 * k + 1) (2 * k - 6 * Nat.sqrt (3 * k + 1)) r isB).card ≤ k ∧
    (golayBigSet (3 * k + 1) (2 * k - 6 * Nat.sqrt (3 * k + 1)) r isB).card -
      (golaySmallSet (3 * k + 1) (2 * k - 6 * Nat.sqrt (3 * k + 1)) r isB).card ≤
      3 * Nat.sqrt (3 * k + 1) ∧
    block4Total (2 * k - 6 * Nat.sqrt (3 * k + 1)) +
      (k - (golayBigSet (3 * k + 1) (2 * k - 6 * Nat.sqrt (3 * k + 1)) r isB).card) +
      q * ((golayBigSet (3 * k + 1) (2 * k - 6 * Nat.sqrt (3 * k + 1)) r isB).card -
        (golaySmallSet (3 * k + 1) (2 * k - 6 * Nat.sqrt (3 * k + 1)) r isB).card) ≤
      3 * k + 1 := by
  have ⟨hs_ge, _, _, h6s, h3000s⟩ := scale_bounds hk
  set s := Nat.sqrt (3 * k + 1)
  set T := 2 * k - 6 * s
  set L := block4Total T
  have hs_lt : 3 * k + 1 < (s + 1) * (s + 1) := Nat.lt_succ_sqrt (3 * k + 1)
  have hT_le : T ≤ 2 * k := Nat.sub_le _ _
  have hL_le : L ≤ T := (block4Total_bounds T).1
  have hLn : L ≤ 3 * k + 1 := by omega
  obtain ⟨hle, hsum, _, _, hdsq⟩ := golayBig_small_props hLn r isB
  set bigCard := (golayBigSet (3 * k + 1) T r isB).card
  set smallCard := (golaySmallSet (3 * k + 1) T r isB).card
  have hd_le : bigCard - smallCard ≤ 3 * s := by
    have h8L : 8 * (L : ℝ) < (3 * (s : ℝ)) ^ 2 := by
      have h1 : (L : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast le_trans hL_le hT_le
      have h2 : ((3 * k + 1 : ℕ) : ℝ) < ((s : ℝ) + 1) ^ 2 := by
        have hlt2 : 3 * k + 1 < (s + 1) ^ 2 := by simpa [sq] using hs_lt
        have hcast : ((3 * k + 1 : ℕ) : ℝ) < (((s + 1 : ℕ) : ℝ) ^ 2) := by exact_mod_cast hlt2
        rw [Nat.cast_add s 1, Nat.cast_one] at hcast
        exact hcast
      have h3 : (17000 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_ge
      have h4 : ((3 * k + 1 : ℕ) : ℝ) = 3 * (k : ℝ) + 1 := by push_cast; ring
      nlinarith
    have hlt' : ((bigCard - smallCard : ℕ) : ℝ) < 3 * (s : ℝ) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (bigCard - smallCard)]
    have : bigCard - smallCard < 3 * s := by exact_mod_cast hlt'
    omega
  have hbig_le : bigCard ≤ k := by
    have h2big : 2 * bigCard = L + (bigCard - smallCard) := by omega
    omega
  have hfit : L + (k - bigCard) + q * (bigCard - smallCard) ≤ 3 * k + 1 := by
    have h1 : L + (k - bigCard) = k + smallCard := by omega
    have h2 : smallCard ≤ k := le_trans hle hbig_le
    have hqd : q * (bigCard - smallCard) ≤ 1000 * (3 * s) :=
      Nat.mul_le_mul hq hd_le
    omega
  exact ⟨hLn, hbig_le, hd_le, hfit⟩

private lemma golayPadBig_card {k : ℕ} (hk : 100000000 ≤ k) (r : Fin 4) (isB : Bool) :
    (golayPadBig k (2 * k - 6 * Nat.sqrt (3 * k + 1)) r isB).card = k := by
  have ⟨hLn, hbig_le, _, hfit⟩ := golayPad_bounds (q := 0) hk (by norm_num) r isB
  obtain ⟨_, _, hbig_lt, _, _⟩ := golayBig_small_props hLn r isB
  set T := 2 * k - 6 * Nat.sqrt (3 * k + 1)
  set L := block4Total T
  set big := golayBigSet (3 * k + 1) T r isB
  unfold golayPadBig
  dsimp only
  have hdisj : Disjoint big (finIco (3 * k + 1) L (L + (k - big.card))) := by
    rw [Finset.disjoint_left]
    intro x hx hI
    have h1 := hbig_lt x hx
    have h2 := (Finset.mem_filter.mp hI).2.1
    omega
  have hbn : L + (k - big.card) ≤ 3 * k + 1 := by omega
  rw [Finset.card_union_of_disjoint hdisj, finIco_card hbn]
  omega

private lemma golayPadSmall_card {k q : ℕ} (hk : 100000000 ≤ k) (hq : q ≤ 1000)
    (r : Fin 4) (isB : Bool) (j : Fin q) :
    (golayPadSmall k (2 * k - 6 * Nat.sqrt (3 * k + 1)) q r isB j).card = k := by
  have ⟨hLn, hbig_le, _, hfit⟩ := golayPad_bounds hk hq r isB
  obtain ⟨hle, _, _, hsmall_lt, _⟩ := golayBig_small_props hLn r isB
  set T := 2 * k - 6 * Nat.sqrt (3 * k + 1)
  set L := block4Total T
  set big := golayBigSet (3 * k + 1) T r isB
  set small := golaySmallSet (3 * k + 1) T r isB
  set p0 := k - big.card
  set d := big.card - small.card
  unfold golayPadSmall
  dsimp only
  have hdisj1 : Disjoint small (finIco (3 * k + 1) L (L + p0)) := by
    rw [Finset.disjoint_left]
    intro x hx hI
    have h1 := hsmall_lt x hx
    have h2 := (Finset.mem_filter.mp hI).2.1
    omega
  have hdisj2 : Disjoint (small ∪ finIco (3 * k + 1) L (L + p0))
      (finIco (3 * k + 1) (L + p0 + j.val * d) (L + p0 + (j.val + 1) * d)) := by
    rw [Finset.disjoint_left]
    intro x hx hI
    have h2 := (Finset.mem_filter.mp hI).2.1
    rcases Finset.mem_union.mp hx with hs | hJ
    · have h1 := hsmall_lt x hs; omega
    · have h1 := (Finset.mem_filter.mp hJ).2.2; omega
  have hbn : L + p0 + (j.val + 1) * d ≤ 3 * k + 1 := by
    have hj : j.val + 1 ≤ q := j.isLt
    have : (j.val + 1) * d ≤ q * d := Nat.mul_le_mul_right d hj
    omega
  have hbn0 : L + p0 ≤ 3 * k + 1 := by omega
  rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
    finIco_card hbn0, finIco_card hbn]
  have hsub : L + p0 + (j.val + 1) * d - (L + p0 + j.val * d) = d := by
    have : (j.val + 1) * d = j.val * d + d := by ring
    omega
  rw [hsub]
  omega

private lemma golayPad_pair_lower {k q : ℕ} (hk : 100000000 ≤ k) (hqpos : 0 < q) (hq : q ≤ 1000)
    (r : Fin 4) (isB : Bool) (ξ : Fin (3 * k + 1)) (hξ : ξ ≠ 0) :
    (9 / 40 : ℝ) *
        ‖golaySeqPoly (2 * k - 6 * Nat.sqrt (3 * k + 1)) r isB
          (phase ((ξ.val : ℝ) / ((3 * k + 1 : ℕ) : ℝ)))‖ ^ 2 -
        (10 / 4 : ℝ) * (2 / ((q : ℝ) * ‖phase ((ξ.val : ℝ) / ((3 * k + 1 : ℕ) : ℝ)) - 1‖)) ^ 2 ≤
      (1 / 2 : ℝ) *
        ‖hatSet (3 * k + 1) (golayPadBig k (2 * k - 6 * Nat.sqrt (3 * k + 1)) r isB) ξ‖ ^ 2 +
        (1 / (2 * (q : ℝ))) *
          ∑ j : Fin q,
            ‖hatSet (3 * k + 1) (golayPadSmall k (2 * k - 6 * Nat.sqrt (3 * k + 1)) q r isB j) ξ‖ ^ 2 := by
  have ⟨hLn, _, _, hfit⟩ := golayPad_bounds hk hq r isB
  obtain ⟨_, _, hbig_lt, hsmall_lt, _⟩ := golayBig_small_props hLn r isB
  set T := 2 * k - 6 * Nat.sqrt (3 * k + 1)
  set z := phase ((ξ.val : ℝ) / ((3 * k + 1 : ℕ) : ℝ))
  set L := block4Total T
  set big := golayBigSet (3 * k + 1) T r isB
  set small := golaySmallSet (3 * k + 1) T r isB
  set p0 := k - big.card
  set d := big.card - small.card
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hpos : 0 < ξ.val := Nat.pos_of_ne_zero (fun h => hξ (Fin.ext h))
  have hz1 : z ≠ 1 := phase_div_ne_one hpos ξ.isLt
  have hznorm : ‖z‖ = 1 := norm_phase _
  have hdiff (j : Fin q) :
      hatSet (3 * k + 1) (golayPadBig k T r isB) ξ -
        hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ =
        golaySign (3 * k + 1) T r isB * golaySeqPoly T r isB z -
          hatSet (3 * k + 1) (finIco (3 * k + 1) (L + p0 + j.val * d) (L + p0 + (j.val + 1) * d)) ξ := by
    have hdisjB : Disjoint big (finIco (3 * k + 1) L (L + p0)) := by
      rw [Finset.disjoint_left]
      intro x hx hI
      have h1 := hbig_lt x hx; have h2 := (Finset.mem_filter.mp hI).2.1; omega
    have hdisjS1 : Disjoint small (finIco (3 * k + 1) L (L + p0)) := by
      rw [Finset.disjoint_left]
      intro x hx hI
      have h1 := hsmall_lt x hx; have h2 := (Finset.mem_filter.mp hI).2.1; omega
    have hdisjS2 : Disjoint (small ∪ finIco (3 * k + 1) L (L + p0))
        (finIco (3 * k + 1) (L + p0 + j.val * d) (L + p0 + (j.val + 1) * d)) := by
      rw [Finset.disjoint_left]
      intro x hx hI
      have h2 := (Finset.mem_filter.mp hI).2.1
      rcases Finset.mem_union.mp hx with hs | hJ
      · have h1 := hsmall_lt x hs; omega
      · have h1 := (Finset.mem_filter.mp hJ).2.2; omega
    have hB : hatSet (3 * k + 1) (golayPadBig k T r isB) ξ =
        hatSet (3 * k + 1) big ξ + hatSet (3 * k + 1) (finIco (3 * k + 1) L (L + p0)) ξ :=
      Finset.sum_union hdisjB
    have hS : hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ =
        hatSet (3 * k + 1) small ξ + hatSet (3 * k + 1) (finIco (3 * k + 1) L (L + p0)) ξ +
          hatSet (3 * k + 1) (finIco (3 * k + 1) (L + p0 + j.val * d) (L + p0 + (j.val + 1) * d)) ξ := by
      unfold golayPadSmall hatSet
      rw [Finset.sum_union hdisjS2, Finset.sum_union hdisjS1]
    rw [hB, hS]
    have hBS := hatSet_golayBig_sub_small hLn r isB ξ
    linear_combination hBS
  let Dbar : ℂ := (((1 / (q : ℝ) : ℝ) : ℂ)) *
    ∑ j : Fin q,
      hatSet (3 * k + 1) (finIco (3 * k + 1) (L + p0 + j.val * d) (L + p0 + (j.val + 1) * d)) ξ
  have hDbar_norm : ‖Dbar‖ ≤ 2 / ((q : ℝ) * ‖z - 1‖) := by
    have hsumD :
        ∑ j : Fin q,
          hatSet (3 * k + 1) (finIco (3 * k + 1) (L + p0 + j.val * d) (L + p0 + (j.val + 1) * d)) ξ =
          ∑ m ∈ Finset.Ico (L + p0) (L + p0 + q * d), z ^ m := by
      have h1 : ∀ j : Fin q,
          hatSet (3 * k + 1) (finIco (3 * k + 1) (L + p0 + j.val * d) (L + p0 + (j.val + 1) * d)) ξ =
            ∑ m ∈ Finset.Ico (L + p0 + j.val * d) (L + p0 + (j.val + 1) * d), z ^ m := by
        intro j
        have hbn : L + p0 + (j.val + 1) * d ≤ 3 * k + 1 := by
          have hj : j.val + 1 ≤ q := j.isLt
          have : (j.val + 1) * d ≤ q * d := Nat.mul_le_mul_right d hj
          omega
        exact hatSet_finIco hbn ξ
      simp_rw [h1]
      rw [Fin.sum_univ_eq_sum_range
        (fun j => ∑ m ∈ Finset.Ico (L + p0 + j * d) (L + p0 + (j + 1) * d), z ^ m) q]
      exact sum_Ico_blocks (fun m => z ^ m) (L + p0) d q
    dsimp only [Dbar]
    rw [hsumD, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hgb := geom_sum_Ico_bound (L + p0) (q * d) hznorm hz1
    calc
      (1 / (q : ℝ)) * ‖∑ m ∈ Finset.Ico (L + p0) (L + p0 + q * d), z ^ m‖
        ≤ (1 / (q : ℝ)) * (2 / ‖z - 1‖) := mul_le_mul_of_nonneg_left hgb (by positivity)
      _ = 2 / ((q : ℝ) * ‖z - 1‖) := by ring
  have hpara :
      (1 / (4 * (q : ℝ))) * ∑ j : Fin q,
        ‖hatSet (3 * k + 1) (golayPadBig k T r isB) ξ -
          hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖hatSet (3 * k + 1) (golayPadBig k T r isB) ξ‖ ^ 2 +
        (1 / (2 * (q : ℝ))) *
          ∑ j : Fin q, ‖hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ‖ ^ 2 := by
    have hpt (j : Fin q) :
        ‖hatSet (3 * k + 1) (golayPadBig k T r isB) ξ -
          hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ‖ ^ 2 ≤
          2 * ‖hatSet (3 * k + 1) (golayPadBig k T r isB) ξ‖ ^ 2 +
            2 * ‖hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ‖ ^ 2 := by
      have hp := parallelogram_complex (hatSet (3 * k + 1) (golayPadBig k T r isB) ξ)
        (hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ)
      linarith [sq_nonneg ‖hatSet (3 * k + 1) (golayPadBig k T r isB) ξ +
        hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ‖]
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin q))) (fun j _ => hpt j)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum] at hsum
    have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 1 / (4 * (q : ℝ)))
    have hsimp :
        (1 / (4 * (q : ℝ))) *
          ((q : ℝ) * (2 * ‖hatSet (3 * k + 1) (golayPadBig k T r isB) ξ‖ ^ 2) +
            2 * ∑ j : Fin q, ‖hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ‖ ^ 2) =
        (1 / 2 : ℝ) * ‖hatSet (3 * k + 1) (golayPadBig k T r isB) ξ‖ ^ 2 +
          (1 / (2 * (q : ℝ))) *
            ∑ j : Fin q, ‖hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ‖ ^ 2 := by
      field_simp [ne_of_gt hqr]
      ring
    linarith
  have hjensen :
      (1 / 4 : ℝ) * ‖golaySign (3 * k + 1) T r isB * golaySeqPoly T r isB z - Dbar‖ ^ 2 ≤
        (1 / (4 * (q : ℝ))) * ∑ j : Fin q,
          ‖hatSet (3 * k + 1) (golayPadBig k T r isB) ξ -
            hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ‖ ^ 2 := by
    have hsum_eq :
        ∑ j : Fin q,
          (hatSet (3 * k + 1) (golayPadBig k T r isB) ξ -
            hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ) =
        ((q : ℝ) : ℂ) * (golaySign (3 * k + 1) T r isB * golaySeqPoly T r isB z - Dbar) := by
      simp_rw [hdiff, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      dsimp only [Dbar]
      rw [mul_sub, ← mul_assoc ((q : ℝ) : ℂ) (((1 / (q : ℝ) : ℝ) : ℂ))]
      have hqc : ((q : ℝ) : ℂ) * (((1 / (q : ℝ) : ℝ) : ℂ)) = 1 := by
        rw [← Complex.ofReal_mul, mul_one_div_cancel (ne_of_gt hqr), Complex.ofReal_one]
      rw [hqc, one_mul, Complex.ofReal_natCast]
    have hj := jensen_sq_norm (Finset.univ : Finset (Fin q))
      (fun j => hatSet (3 * k + 1) (golayPadBig k T r isB) ξ -
        hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ)
    rw [hsum_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hqr.le,
      mul_pow, Finset.card_univ, Fintype.card_fin] at hj
    have hmul := mul_le_mul_of_nonneg_left hj (by positivity : (0 : ℝ) ≤ 1 / (4 * (q : ℝ) ^ 2))
    have hlhs :
        (1 / (4 * (q : ℝ) ^ 2)) *
          ((q : ℝ) ^ 2 * ‖golaySign (3 * k + 1) T r isB * golaySeqPoly T r isB z - Dbar‖ ^ 2) =
        (1 / 4 : ℝ) * ‖golaySign (3 * k + 1) T r isB * golaySeqPoly T r isB z - Dbar‖ ^ 2 := by
      field_simp [ne_of_gt hqr]
    have hrhs :
        (1 / (4 * (q : ℝ) ^ 2)) *
          ((q : ℝ) * ∑ j : Fin q,
            ‖hatSet (3 * k + 1) (golayPadBig k T r isB) ξ -
              hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ‖ ^ 2) =
        (1 / (4 * (q : ℝ))) * ∑ j : Fin q,
          ‖hatSet (3 * k + 1) (golayPadBig k T r isB) ξ -
            hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ‖ ^ 2 := by
      field_simp [ne_of_gt hqr]
    linarith
  have hsub_ge := sq_norm_sub_ge (golaySign (3 * k + 1) T r isB * golaySeqPoly T r isB z) Dbar
    (η := (1 / 10 : ℝ)) (by norm_num)
  rw [norm_mul, norm_golaySign, one_mul] at hsub_ge
  have hDsq : ‖Dbar‖ ^ 2 ≤ (2 / ((q : ℝ) * ‖z - 1‖)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hDbar_norm 2
  have hcombine :
      (9 / 40 : ℝ) * ‖golaySeqPoly T r isB z‖ ^ 2 - (10 / 4 : ℝ) * (2 / ((q : ℝ) * ‖z - 1‖)) ^ 2 ≤
        (1 / 4 : ℝ) * ‖golaySign (3 * k + 1) T r isB * golaySeqPoly T r isB z - Dbar‖ ^ 2 := by
    linarith
  exact hcombine.trans (hjensen.trans hpara)

/-! ### Section 6: Parametric assembly (`q = 1000`, `C = 8009`, `K = 10^8`) -/

abbrev SeedIdx (q : ℕ) := Unit ⊕ (Fin 4 × Bool × Fin (q + 1))

private lemma card_seedIdx (q : ℕ) : Fintype.card (SeedIdx q) = 1 + 8 * (q + 1) := by
  simp [SeedIdx]
  ring

def seedByIdx (k q : ℕ) (hk : 100000000 ≤ k) : SeedIdx q → Finset (Fin (3 * k + 1))
  | Sum.inl () =>
      let hsc := scale_bounds hk
      lowSeed k (8 * Nat.sqrt (3 * k + 1)) hsc.2.1 hsc.2.2.1
  | Sum.inr (r, isB, idx) =>
      let T := 2 * k - 6 * Nat.sqrt (3 * k + 1)
      if h0 : idx.val = 0 then
        golayPadBig k T r isB
      else
        golayPadSmall k T q r isB ⟨idx.val - 1, by omega⟩

noncomputable def weightByIdx (q : ℕ) : SeedIdx q → ℝ
  | Sum.inl () => 1 / 32
  | Sum.inr (_, _, idx) =>
      if idx.val = 0 then (31 / 32) / 16 else (31 / 32) / (16 * (q : ℝ))

private lemma seedByIdx_card {k q : ℕ} (hk : 100000000 ≤ k) (hq : q ≤ 1000) (i : SeedIdx q) :
    (seedByIdx k q hk i).card = k := by
  cases i with
  | inl u =>
    cases u
    exact lowSeed_card _ _
  | inr p =>
    rcases p with ⟨r, isB, idx⟩
    dsimp only [seedByIdx]
    split_ifs
    · exact golayPadBig_card hk r isB
    · exact golayPadSmall_card hk hq r isB _

private lemma weightByIdx_nonneg (q : ℕ) (i : SeedIdx q) : 0 ≤ weightByIdx q i := by
  cases i with
  | inl u => cases u; dsimp only [weightByIdx]; norm_num
  | inr p =>
    rcases p with ⟨r, isB, idx⟩
    dsimp only [weightByIdx]
    split_ifs <;> positivity

private lemma weightByIdx_sum {q : ℕ} (hq : 0 < q) : ∑ i : SeedIdx q, weightByIdx q i = 1 := by
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [Fintype.sum_sum_type, Fintype.sum_unique]
  change (1 / 32 : ℝ) + ∑ p : Fin 4 × Bool × Fin (q + 1), weightByIdx q (Sum.inr p) = 1
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have hinner (r : Fin 4) (isB : Bool) :
      ∑ idx : Fin (q + 1), weightByIdx q (Sum.inr (r, isB, idx)) = 31 / 256 := by
    rw [Fin.sum_univ_succ]
    have h0 : weightByIdx q (Sum.inr (r, isB, (0 : Fin (q + 1)))) = (31 / 32) / 16 := by
      simp [weightByIdx]
    have hs (j : Fin q) :
        weightByIdx q (Sum.inr (r, isB, j.succ)) = (31 / 32) / (16 * (q : ℝ)) := by
      simp [weightByIdx]
    rw [h0]
    simp_rw [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [ne_of_gt hqr]
    ring
  simp_rw [hinner]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  norm_num

private lemma weighted_spectrum_lower {k q : ℕ} (hk : 100000000 ≤ k) (hq : q = 1000)
    (ξ : Fin (3 * k + 1)) (hξ : ξ ≠ 0) :
    ((3 * k + 1 : ℕ) : ℝ) ^ 2 / (8 * (((3 * k + 1 : ℕ) : ℝ) - 2)) <
      ∑ i : SeedIdx q, weightByIdx q i * ‖hatSet (3 * k + 1) (seedByIdx k q hk i) ξ‖ ^ 2 := by
  have hqpos : 0 < q := by omega
  have hqle : q ≤ 1000 := by omega
  have hqr : (q : ℝ) = 1000 := by exact_mod_cast hq
  have ⟨hs_ge, ha, h2a, h6s, _⟩ := scale_bounds hk
  set s := Nat.sqrt (3 * k + 1)
  set T := 2 * k - 6 * s
  have hs_sq : s * s ≤ 3 * k + 1 := Nat.sqrt_le (3 * k + 1)
  have hs_lt : 3 * k + 1 < (s + 1) * (s + 1) := Nat.lt_succ_sqrt (3 * k + 1)
  have hnr : (0 : ℝ) < ((3 * k + 1 : ℕ) : ℝ) := by positivity
  have hn2_pos : (0 : ℝ) < ((3 * k + 1 : ℕ) : ℝ) - 2 := by
    have : (4 : ℝ) ≤ ((3 * k + 1 : ℕ) : ℝ) := by exact_mod_cast (show 4 ≤ 3 * k + 1 by omega)
    linarith
  suffices hred : ∀ ξ' : Fin (3 * k + 1), 0 < ξ'.val → 2 * ξ'.val ≤ 3 * k + 1 →
      ((3 * k + 1 : ℕ) : ℝ) ^ 2 / (8 * (((3 * k + 1 : ℕ) : ℝ) - 2)) <
        ∑ i : SeedIdx q, weightByIdx q i * ‖hatSet (3 * k + 1) (seedByIdx k q hk i) ξ'‖ ^ 2 by
    by_cases hhalf : 2 * ξ.val ≤ 3 * k + 1
    · exact hred ξ (Nat.pos_of_ne_zero (fun h => hξ (Fin.ext h))) hhalf
    · have hneg_pos : 0 < (-ξ).val := by
        rw [neg_val_of_ne_zero hξ]; omega
      have hneg_half : 2 * (-ξ).val ≤ 3 * k + 1 := by
        rw [neg_val_of_ne_zero hξ]; omega
      have hspec := hred (-ξ) hneg_pos hneg_half
      simpa only [norm_hatSet_neg] using hspec
  intro ξ' hξ0 hξhalf
  have hξ'_ne : ξ' ≠ 0 := fun h => by
    have : ξ'.val = 0 := congrArg Fin.val h; omega
  have hsum_split :
      ∑ i : SeedIdx q, weightByIdx q i * ‖hatSet (3 * k + 1) (seedByIdx k q hk i) ξ'‖ ^ 2 =
        (1 / 32 : ℝ) * ‖hatSet (3 * k + 1) (seedByIdx k q hk (Sum.inl ())) ξ'‖ ^ 2 +
        (31 / 32 : ℝ) * ((1 / 8 : ℝ) * ∑ r : Fin 4, ∑ isB : Bool,
          ((1 / 2 : ℝ) * ‖hatSet (3 * k + 1) (golayPadBig k T r isB) ξ'‖ ^ 2 +
            (1 / (2 * (q : ℝ))) *
              ∑ j : Fin q, ‖hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ'‖ ^ 2)) := by
    rw [Fintype.sum_sum_type, Fintype.sum_unique]
    congr 1
    change ∑ p : Fin 4 × Bool × Fin (q + 1),
        weightByIdx q (Sum.inr p) * ‖hatSet (3 * k + 1) (seedByIdx k q hk (Sum.inr p)) ξ'‖ ^ 2 = _
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun isB _ => ?_
    rw [Fin.sum_univ_succ]
    have h0 : weightByIdx q (Sum.inr (r, isB, (0 : Fin (q + 1)))) *
        ‖hatSet (3 * k + 1) (seedByIdx k q hk (Sum.inr (r, isB, (0 : Fin (q + 1))))) ξ'‖ ^ 2 =
        ((31 / 32 : ℝ) / 16) * ‖hatSet (3 * k + 1) (golayPadBig k T r isB) ξ'‖ ^ 2 := by
      simp [weightByIdx, seedByIdx, T, s]
    have hsj (j : Fin q) :
        weightByIdx q (Sum.inr (r, isB, j.succ)) *
          ‖hatSet (3 * k + 1) (seedByIdx k q hk (Sum.inr (r, isB, j.succ))) ξ'‖ ^ 2 =
        ((31 / 32 : ℝ) / (16 * (q : ℝ))) *
          ‖hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ'‖ ^ 2 := by
      simp [weightByIdx, seedByIdx, T, s]
    rw [h0]
    simp_rw [hsj, ← Finset.mul_sum]
    ring
  rw [hsum_split]
  by_cases hlow : 96 * ξ'.val ≤ s
  · have hlow_ge : 9 * (s : ℝ) ^ 2 ≤ ‖hatSet (3 * k + 1) (seedByIdx k q hk (Sum.inl ())) ξ'‖ ^ 2 := by
      dsimp only [seedByIdx]
      exact hatSet_lowSeed_ge hk ha h2a ξ' hξ0 hlow
    have hgolay_nonneg :
        0 ≤ (31 / 32 : ℝ) * ((1 / 8 : ℝ) * ∑ r : Fin 4, ∑ isB : Bool,
          ((1 / 2 : ℝ) * ‖hatSet (3 * k + 1) (golayPadBig k T r isB) ξ'‖ ^ 2 +
            (1 / (2 * (q : ℝ))) *
              ∑ j : Fin q, ‖hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ'‖ ^ 2)) := by
      apply mul_nonneg (by positivity)
      apply mul_nonneg (by positivity)
      refine Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun isB _ => ?_
      have : 0 ≤ ∑ j : Fin q, ‖hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ'‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      positivity
    have hnum :
        ((3 * k + 1 : ℕ) : ℝ) ^ 2 / (8 * (((3 * k + 1 : ℕ) : ℝ) - 2)) <
          (1 / 32 : ℝ) * (9 * (s : ℝ) ^ 2) := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 8 * (((3 * k + 1 : ℕ) : ℝ) - 2))]
      have h1 : ((3 * k + 1 : ℕ) : ℝ) < ((s : ℝ) + 1) ^ 2 := by
        have hlt2 : 3 * k + 1 < (s + 1) ^ 2 := by simpa [sq] using hs_lt
        have hcast : ((3 * k + 1 : ℕ) : ℝ) < (((s + 1 : ℕ) : ℝ) ^ 2) := by exact_mod_cast hlt2
        rw [Nat.cast_add s 1, Nat.cast_one] at hcast
        exact hcast
      have h2 : (17000 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_ge
      have hnbig : (300000000 : ℝ) ≤ ((3 * k + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 300000000 ≤ 3 * k + 1 by omega)
      have hs2_ge : (999 / 1000 : ℝ) * ((3 * k + 1 : ℕ) : ℝ) ≤ (s : ℝ) ^ 2 := by
        nlinarith only [h1, h2]
      have hn_sub : (999 / 1000 : ℝ) * ((3 * k + 1 : ℕ) : ℝ) ≤ ((3 * k + 1 : ℕ) : ℝ) - 2 := by
        linarith only [hnbig]
      have hprod := mul_le_mul hs2_ge hn_sub (by positivity) (by positivity)
      nlinarith only [hprod, hnbig]
    linarith only [hlow_ge, hgolay_nonneg, hnum]
  · have hhigh : s < 96 * ξ'.val := by omega
    have hlow_nonneg :
        0 ≤ (1 / 32 : ℝ) * ‖hatSet (3 * k + 1) (seedByIdx k q hk (Sum.inl ())) ξ'‖ ^ 2 := by
      positivity
    set z := phase ((ξ'.val : ℝ) / ((3 * k + 1 : ℕ) : ℝ))
    have hznorm : ‖z‖ = 1 := norm_phase _
    have hpair_sum :
        (9 / 40 : ℝ) * (block4Total T : ℝ) - (10 / 4 : ℝ) * (2 / ((q : ℝ) * ‖z - 1‖)) ^ 2 ≤
          (1 / 8 : ℝ) * ∑ r : Fin 4, ∑ isB : Bool,
            ((1 / 2 : ℝ) * ‖hatSet (3 * k + 1) (golayPadBig k T r isB) ξ'‖ ^ 2 +
              (1 / (2 * (q : ℝ))) *
                ∑ j : Fin q, ‖hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ'‖ ^ 2) := by
      have hle_sum :
          ∑ r : Fin 4, ∑ isB : Bool,
            ((9 / 40 : ℝ) * ‖golaySeqPoly T r isB z‖ ^ 2 -
              (10 / 4 : ℝ) * (2 / ((q : ℝ) * ‖z - 1‖)) ^ 2) ≤
          ∑ r : Fin 4, ∑ isB : Bool,
            ((1 / 2 : ℝ) * ‖hatSet (3 * k + 1) (golayPadBig k T r isB) ξ'‖ ^ 2 +
              (1 / (2 * (q : ℝ))) *
                ∑ j : Fin q, ‖hatSet (3 * k + 1) (golayPadSmall k T q r isB j) ξ'‖ ^ 2) :=
        Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun isB _ =>
          golayPad_pair_lower hk hqpos hqle r isB ξ' hξ'_ne
      have heval :
          ∑ r : Fin 4, ∑ isB : Bool,
            ((9 / 40 : ℝ) * ‖golaySeqPoly T r isB z‖ ^ 2 -
              (10 / 4 : ℝ) * (2 / ((q : ℝ) * ‖z - 1‖)) ^ 2) =
          8 * ((9 / 40 : ℝ) * (block4Total T : ℝ) -
            (10 / 4 : ℝ) * (2 / ((q : ℝ) * ‖z - 1‖)) ^ 2) := by
        simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
        have hbool : ∑ r : Fin 4, ∑ isB : Bool, ‖golaySeqPoly T r isB z‖ ^ 2 =
            8 * (block4Total T : ℝ) := by
          have h2 : ∀ r : Fin 4, ∑ isB : Bool, ‖golaySeqPoly T r isB z‖ ^ 2 =
              ‖golaySeqPoly T r false z‖ ^ 2 + ‖golaySeqPoly T r true z‖ ^ 2 := by
            intro r
            rw [Fintype.sum_bool, add_comm]
          simp_rw [h2]
          exact golaySeq_sq_sum T hznorm
        rw [hbool]
        push_cast
        ring
      rw [heval] at hle_sum
      linarith
    have hsr_pos : (0 : ℝ) < (s : ℝ) := by
      have : (17000 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_ge
      linarith
    have hz_ge : (s : ℝ) / (24 * ((3 * k + 1 : ℕ) : ℝ)) ≤ ‖z - 1‖ := by
      have h1 := norm_phase_sub_one_ge (x := (ξ'.val : ℝ) / ((3 * k + 1 : ℕ) : ℝ)) (by positivity)
        (by
          rw [div_le_iff₀ hnr]
          have : (2 : ℝ) * (ξ'.val : ℝ) ≤ ((3 * k + 1 : ℕ) : ℝ) := by exact_mod_cast hξhalf
          linarith)
      have h2 : (s : ℝ) ≤ 96 * (ξ'.val : ℝ) := by exact_mod_cast le_of_lt hhigh
      have h3 : (s : ℝ) / (24 * ((3 * k + 1 : ℕ) : ℝ)) ≤
          4 * ((ξ'.val : ℝ) / ((3 * k + 1 : ℕ) : ℝ)) := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 24 * ((3 * k + 1 : ℕ) : ℝ))]
        have : 4 * ((ξ'.val : ℝ) / ((3 * k + 1 : ℕ) : ℝ)) * (24 * ((3 * k + 1 : ℕ) : ℝ)) =
            96 * (ξ'.val : ℝ) := by
          field_simp [ne_of_gt hnr]; ring
        linarith
      exact h3.trans h1
    have herr_le :
        (2 / ((q : ℝ) * ‖z - 1‖)) ^ 2 ≤
          (48 * ((3 * k + 1 : ℕ) : ℝ) / (1000 * (s : ℝ))) ^ 2 := by
      rw [hqr]
      have hpos1 : 0 < 1000 * ((s : ℝ) / (24 * ((3 * k + 1 : ℕ) : ℝ))) := by positivity
      have hfrac : 2 / (1000 * ‖z - 1‖) ≤ 48 * ((3 * k + 1 : ℕ) : ℝ) / (1000 * (s : ℝ)) := by
        have hstep := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hpos1
          (mul_le_mul_of_nonneg_left hz_ge (by norm_num : (0 : ℝ) ≤ 1000))
        have hsimp : 2 / (1000 * ((s : ℝ) / (24 * ((3 * k + 1 : ℕ) : ℝ)))) =
            48 * ((3 * k + 1 : ℕ) : ℝ) / (1000 * (s : ℝ)) := by
          field_simp [ne_of_gt hnr, ne_of_gt hsr_pos]; ring
        linarith
      exact pow_le_pow_left₀ (by positivity) hfrac 2
    have hL_ge : (15 / 16 : ℝ) * (2 * (k : ℝ) - 6 * (s : ℝ)) ≤ (block4Total T : ℝ) := by
      have h15 := (block4Total_bounds T).2
      have hTcast : (T : ℝ) = 2 * (k : ℝ) - 6 * (s : ℝ) := by
        dsimp only [T]
        rw [Nat.cast_sub h6s]
        push_cast
        ring
      have h15r : (15 : ℝ) * (T : ℝ) ≤ 16 * (block4Total T : ℝ) := by exact_mod_cast h15
      rw [hTcast] at h15r
      linarith
    have hfinal_num :
        ((3 * k + 1 : ℕ) : ℝ) ^ 2 / (8 * (((3 * k + 1 : ℕ) : ℝ) - 2)) <
          (31 / 32 : ℝ) * ((9 / 40 : ℝ) * (block4Total T : ℝ) -
            (10 / 4 : ℝ) * (48 * ((3 * k + 1 : ℕ) : ℝ) / (1000 * (s : ℝ))) ^ 2) := by
      have hs_lb : (17000 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_ge
      have hns : ((3 * k + 1 : ℕ) : ℝ) < ((s : ℝ) + 1) ^ 2 := by
        have hlt2 : 3 * k + 1 < (s + 1) ^ 2 := by simpa [sq] using hs_lt
        have hcast : ((3 * k + 1 : ℕ) : ℝ) < (((s + 1 : ℕ) : ℝ) ^ 2) := by exact_mod_cast hlt2
        rw [Nat.cast_add s 1, Nat.cast_one] at hcast
        exact hcast
      have hs2_le : (s : ℝ) * (s : ℝ) ≤ ((3 * k + 1 : ℕ) : ℝ) := by exact_mod_cast hs_sq
      have hnbig : (300000000 : ℝ) ≤ ((3 * k + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 300000000 ≤ 3 * k + 1 by omega)
      have hn_eq : ((3 * k + 1 : ℕ) : ℝ) = 3 * (k : ℝ) + 1 := by push_cast; ring
      set nr : ℝ := ((3 * k + 1 : ℕ) : ℝ)
      have h1 : nr / (s : ℝ) ^ 2 ≤ 1001 / 1000 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (s : ℝ) ^ 2)]
        nlinarith only [hns, hs_lb]
      have herr_lin : (48 * nr / (1000 * (s : ℝ))) ^ 2 ≤ (48 / 1000 : ℝ) ^ 2 * (1001 / 1000) * nr := by
        have hrew : (48 * nr / (1000 * (s : ℝ))) ^ 2 =
            (48 / 1000 : ℝ) ^ 2 * (nr / (s : ℝ) ^ 2) * nr := by
          field_simp [ne_of_gt hsr_pos]
        rw [hrew]
        have hposc : 0 ≤ (48 / 1000 : ℝ) ^ 2 * nr := by positivity
        nlinarith only [h1, hposc]
      have hsn : (s : ℝ) ≤ nr / 17000 := by
        nlinarith only [hs2_le, hs_lb]
      have hL_lin : (5 / 8 : ℝ) * nr - (1 / 1000 : ℝ) * nr ≤ (block4Total T : ℝ) := by
        linarith only [hL_ge, hn_eq, hsn, hs_lb, hnbig]
      have hthresh : nr ^ 2 / (8 * (nr - 2)) ≤ (126 / 1000 : ℝ) * nr := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (nr - 2))]
        nlinarith only [hnbig]
      linarith only [hthresh, hL_lin, herr_lin, hnbig]
    linarith only [hpair_sum, herr_le, hlow_nonneg, hfinal_num]

private lemma detects_of_q {k q : ℕ} (hk : 100000000 ≤ k) (hq : q = 1000) :
    let n := 3 * k + 1
    let adj := fun (A B : Finset (Fin n)) (a : ℤ) => ((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a + 1
    let detects := fun (Y : Finset (Finset (Fin n))) =>
      ∀ A : Finset (Fin n), 2 ≤ A.card → A.card + 2 ≤ n → ∀ a : ℤ, ∃ B ∈ Y, ¬ adj A B a
    let shift := fun (S : Finset (Fin n)) (t : Fin n) => S.image (fun i => i + t)
    let orbit := fun (S : Finset (Fin n)) => (Finset.univ : Finset (Fin n)).image (shift S)
    let I := (Finset.univ : Finset (Fin n)).filter (fun i => i.val < k)
    ∃ seed : Fin (1 + 8 * (q + 1)) → Finset (Fin n),
      (∀ i, (seed i).card = k) ∧ detects (orbit I ∪ Finset.univ.biUnion (fun i => orbit (seed i))) := by
  dsimp only
  have hn4 : 4 ≤ 3 * k + 1 := by omega
  have hqpos : 0 < q := by omega
  have hqle : q ≤ 1000 := by omega
  let e : Fin (1 + 8 * (q + 1)) ≃ SeedIdx q :=
    (Fintype.equivFinOfCardEq (card_seedIdx q)).symm
  refine ⟨fun i => seedByIdx k q hk (e i), ?_, ?_⟩
  · intro i
    exact seedByIdx_card hk hqle (e i)
  · refine weighted_spectral_detection hn4
      (seedByIdx k q hk)
      (weightByIdx q)
      (weightByIdx_nonneg q)
      (weightByIdx_sum hqpos)
      (weighted_spectrum_lower hk hq)
      _ ?_
    intro idx t
    apply Finset.mem_union_right
    rw [Finset.mem_biUnion]
    refine ⟨e.symm idx, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    refine ⟨t, Finset.mem_univ _, ?_⟩
    simp

end LogRankCyclicDetector

theorem PEqualNP.Outside.L_log_rank_cyclic_detector_family :
    ∃ C K : ℕ, ∀ k : ℕ, K ≤ k → 2 ≤ k →
      let n := 3*k+1;
      let adj := fun (A B : Finset (Fin n)) (a : ℤ) => ((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a+1;
      let detects := fun (Y : Finset (Finset (Fin n))) => ∀ A : Finset (Fin n), 2 ≤ A.card → A.card + 2 ≤ n → ∀ a : ℤ, ∃ B ∈ Y, ¬ adj A B a;
      let shift := fun (S : Finset (Fin n)) (t : Fin n) => S.image (fun i => i+t);
      let orbit := fun (S : Finset (Fin n)) => (Finset.univ : Finset (Fin n)).image (shift S);
      let I := (Finset.univ : Finset (Fin n)).filter (fun i => i.val < k);
      ∃ seed : Fin C → Finset (Fin n), (∀ i, (seed i).card=k) ∧ detects (orbit I ∪ Finset.univ.biUnion (fun i => orbit (seed i))) :=
  ⟨1 + 8 * (1000 + 1), 100000000, fun _ hk _ => LogRankCyclicDetector.detects_of_q hk rfl⟩
