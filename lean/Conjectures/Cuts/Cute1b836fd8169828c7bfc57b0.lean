import Mathlib

open MeasureTheory

-- child 1 zh: 计数有裕量的二进制网格词。每个相位只读取当前小数点后的十六位。
-- child 1 en: Count dyadic grid words whose sixteen-bit phase sum clears the threshold with both error margins.
-- child 2 zh: 将每个相位向下截断到十六位时，L 项复指数和的误差至多为 2πL/65536。
-- child 2 en: Flooring each phase to sixteen fractional bits changes the length-L exponential sum by at most 2πL/65536.
-- child 3 zh: 相距至多二的负 L 次幂的两点，其 L 项倍频指数和相差至多 2π。
-- child 3 en: Two points at distance at most 2⁻ᴸ have dyadic length-L exponential sums differing by at most 2π.
theorem Conjectures.Cuts.Cute1b836fd8169828c7bfc57b0
    (hWords : let T := fun (L : ℕ) (u : ℝ) => ∑ j ∈ Finset.range L, Complex.exp (((2 * Real.pi * ((⌊65536 * (2 : ℝ)^j * u⌋ : ℤ) : ℝ) / 65536 : ℝ) : ℂ) * Complex.I)
     ∃ L₀ : ℕ, ∀ L ≥ L₀, ∃ S : Finset ℕ, S ⊆ Finset.range (2^L) ∧
       (2:ℝ)^(-((291/500:ℝ)*L)) ≤ (S.card:ℝ)/(2:ℝ)^L ∧
       ∀ k ∈ S, (93/125:ℝ)*L + (2*Real.pi/65536)*L + 2*Real.pi <
         ‖T L ((k:ℝ)/(2:ℝ)^L)‖)
    (hTrunc : let G := fun (L : ℕ) (x : ℝ) => ∑ j ∈ Finset.range L, Complex.exp (((2*Real.pi*(2 : ℝ)^j*x : ℝ) : ℂ)*Complex.I)
     let T := fun (L : ℕ) (u : ℝ) => ∑ j ∈ Finset.range L, Complex.exp (((2 * Real.pi * ((⌊65536 * (2 : ℝ)^j * u⌋ : ℤ) : ℝ) / 65536 : ℝ) : ℂ) * Complex.I)
     ∀ (L : ℕ) (u : ℝ), ‖T L u - G L u‖ ≤ (2*Real.pi/65536)*L)
    (hCell : let G := fun (L : ℕ) (x : ℝ) => ∑ j ∈ Finset.range L, Complex.exp (((2*Real.pi*(2 : ℝ)^j*x : ℝ) : ℂ)*Complex.I)
     ∀ (L : ℕ) (x u : ℝ), |x-u| ≤ 1/(2:ℝ)^L → ‖G L x - G L u‖ ≤ 2*Real.pi) : (let G := fun (L : ℕ) (x : ℝ) => ∑ j ∈ Finset.range L, Complex.exp (((2*Real.pi*(2 : ℝ)^j*x : ℝ) : ℂ)*Complex.I); ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → (2 : ℝ)^(-((291/500 : ℝ)*(L : ℝ))) ≤ (MeasureTheory.volume {x : ℝ | x ∈ Set.Icc 0 1 ∧ (93/125 : ℝ)*(L : ℝ) < ‖G L x‖}).toReal) := by
  intro G
  classical
  obtain ⟨L₀, hL₀⟩ := hWords
  refine ⟨L₀, fun L hL => ?_⟩
  obtain ⟨S, hS, hmass, hlarge⟩ := hL₀ L hL
  let D : ℝ := (2:ℝ)^L
  have hD : 0 < D := by dsimp [D]; positivity
  let cell (k : ℕ) := Set.Ico ((k:ℝ)/D) (((k:ℝ)+1)/D)
  let high := {x : ℝ | x ∈ Set.Icc 0 1 ∧ (93/125:ℝ)*L < ‖G L x‖}
  have cover : (⋃ k ∈ S, cell k) ⊆ high := by
    intro x hx
    obtain ⟨k, hk, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hlo, hhi⟩ := hx
    have hkD : (k:ℝ)+1 ≤ D := by
      have h := Finset.mem_range.mp (hS hk)
      dsimp only [D]
      exact_mod_cast Nat.succ_le_of_lt h
    have hdist : |x - (k:ℝ)/D| ≤ 1/D := by
      rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
      rw [add_div] at hhi
      linarith
    have hx0 : 0 ≤ x := le_trans (div_nonneg (Nat.cast_nonneg _) hD.le) hlo
    have hx1 : x ≤ 1 := hhi.le.trans ((div_le_one hD).mpr hkD)
    refine ⟨⟨hx0,hx1⟩, ?_⟩
    have ht := hTrunc L ((k:ℝ)/D)
    have hc := hCell L ((k:ℝ)/D) x (by simpa only [abs_sub_comm] using hdist)
    have ht' := norm_sub_norm_le _ _ |>.trans ht
    have hc' := norm_sub_norm_le _ _ |>.trans hc
    change ‖G L ((k:ℝ)/D)‖ - ‖G L x‖ ≤ 2*Real.pi at hc'
    have hw := hlarge k hk
    dsimp only [D, G] at ht' hc' hw ⊢
    linarith only [ht', hc', hw]
  have disj : Set.PairwiseDisjoint (↑S) cell := by
    intro k hk j hj hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hklo, hkhi⟩ := hx
    obtain ⟨hjlo, hjhi⟩ := hy
    rcases lt_or_gt_of_ne hne with h | h
    · have hkj : (k:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast h
      exact hkhi.not_ge ((div_le_div_of_nonneg_right hkj hD.le).trans hjlo)
    · have hjk : (j:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast h
      exact hjhi.not_ge ((div_le_div_of_nonneg_right hjk hD.le).trans hklo)
  have hlength (k : ℕ) : volume.real (cell k) = 1/D := by
    change volume.real (Set.Ico ((k:ℝ)/D) (((k:ℝ)+1)/D)) = _
    rw [Real.volume_real_Ico_of_le (div_le_div_of_nonneg_right (by linarith) hD.le)]
    ring
  change _ ≤ volume.real high
  calc
    _ ≤ (S.card:ℝ)/D := hmass
    _ = ∑ k ∈ S, volume.real (cell k) := by simp [hlength, div_eq_mul_inv]
    _ = volume.real (⋃ k ∈ S, cell k) := by
      symm
      exact measureReal_biUnion_finset disj (fun _ _ => measurableSet_Ico)
        (fun _ _ => measure_Ico_lt_top.ne)
    _ ≤ _ := measureReal_mono cover (ne_top_of_le_ne_top measure_Icc_lt_top.ne
      (measure_mono (fun x hx => hx.1 : high ⊆ Set.Icc 0 1)))
