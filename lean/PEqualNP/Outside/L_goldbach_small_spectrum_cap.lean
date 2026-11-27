import Mathlib

theorem PEqualNP.Outside.L_goldbach_small_spectrum_cap :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0;
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * E ((k : ℝ) * t));
    let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2;
    let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))};
    let low := fun (n k : ℕ) => if k ^ 3 ≤ n then w k else 0;
    let high := fun (n k : ℕ) => w k - low n k;
    let I := fun (n : ℕ) (a b : ℕ → ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u * S n b u * E (-(n : ℝ) * u)) t) (0 : ℝ) 1 MeasureTheory.volume;
    ∀ (n : ℕ) (t : ℝ), 2 ≤ n → ‖S n (low n) t‖ ≤ ((n : ℝ) ^ (1 / 3 : ℝ) + 1) * Real.log (n : ℝ) := by
  intro w E S Q arcs low high I n t hn
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hw_nonneg : ∀ k : ℕ, 0 ≤ w k := by
    intro k
    dsimp only [w]
    split_ifs with hp
    · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
    · exact le_rfl
  have hlow_nonneg : ∀ k : ℕ, 0 ≤ low n k := by
    intro k
    dsimp only [low]
    split_ifs
    · exact hw_nonneg k
    · exact le_rfl
  have hlow_le_log : ∀ k ∈ Finset.range (n + 1), low n k ≤ Real.log (n : ℝ) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    dsimp only [low, w]
    split_ifs with h1 hp
    · exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hkn)
    · exact hlog_nonneg
    · exact hlog_nonneg
  have hnorm_E : ∀ x : ℝ, ‖E x‖ = 1 := by
    intro x
    dsimp only [E]
    exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
  have hstep1 : ‖S n (low n) t‖ ≤ ∑ k ∈ Finset.range (n + 1), low n k := by
    dsimp only [S]
    calc
      ‖∑ k ∈ Finset.range (n + 1), (low n k : ℂ) * E ((k : ℝ) * t)‖
        ≤ ∑ k ∈ Finset.range (n + 1), ‖(low n k : ℂ) * E ((k : ℝ) * t)‖ := norm_sum_le _ _
      _ = ∑ k ∈ Finset.range (n + 1), low n k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlow_nonneg k), hnorm_E, mul_one]
  set s : Finset ℕ := (Finset.range (n + 1)).filter (fun k => k ^ 3 ≤ n)
  have hstep2 : ∑ k ∈ Finset.range (n + 1), low n k = ∑ k ∈ s, low n k := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun k hk hks => ?_
    have hnot : ¬ (k ^ 3 ≤ n) := by
      intro hle
      exact hks (Finset.mem_filter.mpr ⟨hk, hle⟩)
    simp [low, hnot]
  set m : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
  have hs_sub : s ⊆ Finset.range (m + 1) := by
    intro k hk
    have hk3 : k ^ 3 ≤ n := (Finset.mem_filter.mp hk).2
    have hk3_real : ((k : ℝ) ^ (3 : ℝ)) ≤ (n : ℝ) := by
      have hcast : ((k ^ 3 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk3
      simpa [Real.rpow_natCast] using hcast
    have hk_le_rpow : (k : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
      have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg k) (3 : ℝ)) hk3_real (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rw [← Real.rpow_mul (Nat.cast_nonneg k)] at hpow
      have h3 : (3 : ℝ) * (1 / 3 : ℝ) = 1 := by norm_num
      rw [h3, Real.rpow_one] at hpow
      exact hpow
    have hk_le_m : k ≤ m := Nat.le_floor hk_le_rpow
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le_m)
  have hcard : (s.card : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) + 1 := by
    have h1 : s.card ≤ m + 1 := by
      simpa [Finset.card_range] using Finset.card_le_card hs_sub
    have h1r : (s.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast h1
    have h2 : (m : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Nat.floor_le (Real.rpow_nonneg hn_nonneg (1 / 3 : ℝ))
    linarith
  calc
    ‖S n (low n) t‖ ≤ ∑ k ∈ Finset.range (n + 1), low n k := hstep1
    _ = ∑ k ∈ s, low n k := hstep2
    _ ≤ ∑ _k ∈ s, Real.log (n : ℝ) := by
        refine Finset.sum_le_sum fun k hk => hlow_le_log k (Finset.mem_filter.mp hk).1
    _ = (s.card : ℝ) * Real.log (n : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n : ℝ) ^ (1 / 3 : ℝ) + 1) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right hcard hlog_nonneg
