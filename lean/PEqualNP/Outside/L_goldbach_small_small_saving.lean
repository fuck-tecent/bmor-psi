import Mathlib

open Filter

theorem PEqualNP.Outside.L_goldbach_small_small_saving : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e:ℝ, 0<e → ∃ N:ℕ, ∀ n≥N, ‖I n (low n) (low n)‖≤e*(n:ℝ) := by
  intro w E S Q arcs low high I e he
  have cap (n : ℕ) (t : ℝ) (hn : 2 ≤ n) :
      ‖S n (low n) t‖ ≤ ((n : ℝ) ^ (1 / 3 : ℝ) + 1) * Real.log n := by
    let f (k : ℕ) : ℂ := (low n k : ℂ) * E ((k : ℝ) * t)
    let K := (Finset.range (n + 1)).filter (fun k => k^3 ≤ n ∧ Nat.Prime k)
    let R : ℝ := (n : ℝ) ^ (1 / 3 : ℝ)
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have hs : ∑ k ∈ K, f k = S n (low n) t := by
      apply Finset.sum_filter_of_ne
      intro k _ hk
      by_contra! h
      by_cases hc : k^3 ≤ n
      · exact hk (by simp [f, low, w, hc, h hc])
      · exact hk (by simp [f, low, hc])
    have hcard : (K.card : ℝ) ≤ R + 1 := by
      have hsub : K ⊆ Finset.range (⌊R⌋₊ + 1) := by
        intro k hk
        obtain ⟨_, hc, _⟩ := Finset.mem_filter.mp hk
        apply Finset.mem_range.mpr
        apply Nat.lt_succ_of_le
        apply Nat.le_floor
        dsimp [R]
        rw [one_div, Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by norm_num)]
        norm_cast
      have hc : K.card ≤ ⌊R⌋₊ + 1 := by simpa using Finset.card_le_card hsub
      calc
        (K.card : ℝ) ≤ (⌊R⌋₊ : ℝ) + 1 := by exact_mod_cast hc
        _ ≤ R + 1 := by gcongr; exact Nat.floor_le (by dsimp [R]; positivity)
    change ‖S n (low n) t‖ ≤ (R + 1) * Real.log n
    rw [← hs]
    calc
      ‖∑ k ∈ K, f k‖ ≤ ∑ k ∈ K, ‖f k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ K, Real.log (n : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        obtain ⟨hkn, hc, hp⟩ := Finset.mem_filter.mp hk
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hp.one_le
        simp only [f, low, hc, ite_true, w, hp, E, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hk1), Complex.norm_exp_ofReal_mul_I, mul_one]
        exact Real.log_le_log (by linarith) (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hkn))
      _ = (K.card : ℝ) * Real.log n := by simp
      _ ≤ (R + 1) * Real.log n := mul_le_mul_of_nonneg_right hcard hlog
  have asymp := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 3)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (asymp.bound (by positivity : 0 < e / 4))
  refine ⟨max N 2, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  let R : ℝ := (n : ℝ) ^ (1 / 3 : ℝ)
  have hR : 1 ≤ R := Real.one_le_rpow hn1 (by norm_num)
  have hR0 : 0 ≤ R := by linarith
  have hcube : R^3 = n := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlog2 : (Real.log n)^2 ≤ (e / 4) * R := by
    have h := hN n (le_trans (le_max_left _ _) hn)
    change ‖(Real.log n) ^ (2 : ℝ)‖ ≤ e / 4 * ‖R‖ at h
    simpa only [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg hR0] using h
  let B : ℝ := (R + 1) * Real.log n
  have pointwise (t : ℝ) : ‖(arcs n)ᶜ.indicator (fun u => S n (low n) u * S n (low n) u * E (-(n : ℝ) * u)) t‖ ≤ B^2 := by
    by_cases hm : t ∈ (arcs n)ᶜ
    · rw [Set.indicator_of_mem hm, norm_mul, norm_mul]
      simp only [E, Complex.norm_exp_ofReal_mul_I, mul_one, ← sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (cap n t hn2) _
    · rw [Set.indicator_of_notMem hm, norm_zero]; exact sq_nonneg _
  have hint : ‖I n (low n) (low n)‖ ≤ B^2 := by
    simpa only [I, sub_zero, abs_one, mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (fun t _ => pointwise t)
  calc
    ‖I n (low n) (low n)‖ ≤ B^2 := hint
    _ = (R + 1)^2 * (Real.log n)^2 := mul_pow _ _ _
    _ ≤ (2 * R)^2 * ((e / 4) * R) := by
      gcongr
      linarith
    _ = e * (n : ℝ) := by rw [← hcube]; ring
