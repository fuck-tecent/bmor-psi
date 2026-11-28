import Mathlib

theorem Conjectures.Cuts.Cuta3aebdbba73b185368da3175 (hp :
      let P := fun (N : ℕ) (x : ℝ) => ∑ m ∈ (Finset.range N).filter Nat.Prime,
        ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
          Complex.exp (((2*Real.pi*(m : ℝ)*x : ℝ) : ℂ)*Complex.I)
      ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N q : ℕ, N₀ ≤ N → 2 ≤ N →
        ∀ a : ℤ, ∀ x : ℝ, 0 < q → q^2 ≤ N → Nat.Coprime a.natAbs q →
        let e := |x - (a : ℝ)/(q : ℝ)|
        e ≤ 1/((q : ℝ)*Real.sqrt (N : ℝ)) →
        let B := max (q : ℝ) ((q : ℝ)*(N : ℝ)*e)
        2 * ‖P N x‖ ≤ (N : ℝ)^η * (N : ℝ)/Real.sqrt B)
    (ht : ∃ T : ℕ, ∀ N ≥ T,
      ∑ m ∈ (Finset.range N).filter (fun m => ¬ Nat.Prime m), ArithmeticFunction.vonMangoldt m
        ≤ Real.sqrt (N : ℝ) * Real.sqrt (Real.sqrt (N : ℝ)) / 2) : (let S := fun (N : ℕ) (x : ℝ) => ∑ m ∈ Finset.range N, ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * Complex.exp (((2*Real.pi*(m : ℝ)*x : ℝ) : ℂ)*Complex.I); ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N q : ℕ, N₀ ≤ N → 2 ≤ N → ∀ a : ℤ, ∀ x : ℝ, 0 < q → q^2 ≤ N → Nat.Coprime a.natAbs q → let e := |x - (a : ℝ)/(q : ℝ)|; e ≤ 1/((q : ℝ)*Real.sqrt (N : ℝ)) → let B := max (q : ℝ) ((q : ℝ)*(N : ℝ)*e); ‖S N x‖ ≤ (N : ℝ)^η * (N : ℝ)/Real.sqrt B) := by
  intro S η hη
  obtain ⟨N₀, hN₀⟩ := hp η hη
  obtain ⟨T, hT⟩ := ht
  refine ⟨max N₀ T, ?_⟩
  intro N q hN h2 a x hq hqN ha e he B
  let f (m : ℕ) : ℂ := ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
    Complex.exp (((2*Real.pi*(m : ℝ)*x : ℝ) : ℂ)*Complex.I)
  let R := (Finset.range N).filter (fun m => ¬ m.Prime)
  let P := (Finset.range N).filter Nat.Prime
  have hprime : 2 * ‖∑ m ∈ P, f m‖ ≤ (N : ℝ)^η * N / Real.sqrt B :=
    hN₀ N q ((le_max_left _ _).trans hN) h2 a x hq hqN ha he
  have htail : ‖∑ m ∈ R, f m‖ ≤ Real.sqrt N * Real.sqrt (Real.sqrt N) / 2 := by
    apply (norm_sum_le _ _).trans
    have hf (m : ℕ) : ‖f m‖ = ArithmeticFunction.vonMangoldt m := by
      unfold f
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    simpa only [hf] using hT N ((le_max_right _ _).trans hN)
  have nq : (0 : ℝ) < q := by exact_mod_cast hq
  have npos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have ns := Real.sqrt_pos.2 npos
  have sqN := Real.sq_sqrt npos.le
  have hq' : (q : ℝ)^2 ≤ N := by exact_mod_cast hqN
  have hB : B ≤ Real.sqrt N := by
    apply max_le
    · nlinarith [sq_nonneg ((q : ℝ) - Real.sqrt N)]
    · have h := (le_div_iff₀ (mul_pos nq ns)).mp he
      nlinarith [mul_le_mul_of_nonneg_right h ns.le, sqN,
        show e * ((q : ℝ) * Real.sqrt N) * Real.sqrt N = (q : ℝ)*N*e by
          rw [show e * ((q : ℝ) * Real.sqrt N) * Real.sqrt N =
            ((q : ℝ) * e) * (Real.sqrt N)^2 by ring, sqN]; ring]
  have bpos : 0 < B := nq.trans_le (le_max_left _ _)
  have hscale : (Real.sqrt N * Real.sqrt (Real.sqrt N)) * Real.sqrt B ≤ (N : ℝ) := calc
    _ ≤ (Real.sqrt N * Real.sqrt (Real.sqrt N)) * Real.sqrt (Real.sqrt N) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hB) (by positivity)
    _ = N := by rw [mul_assoc, ← sq, Real.sq_sqrt ns.le, ← sq, sqN]
  have hpow : (1 : ℝ) ≤ (N : ℝ)^η := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ N)) hη.le
  have hbudget : Real.sqrt N * Real.sqrt (Real.sqrt N) ≤ (N : ℝ)^η * N / Real.sqrt B := by
    apply (le_div_iff₀ (Real.sqrt_pos.2 bpos)).mpr
    exact hscale.trans (le_mul_of_one_le_left npos.le hpow)
  have hsplit : S N x = (∑ m ∈ P, f m) + ∑ m ∈ R, f m :=
    (Finset.sum_filter_add_sum_filter_not (Finset.range N) Nat.Prime f).symm
  rw [hsplit]
  exact (norm_add_le _ _).trans (by linarith only [hprime, htail, hbudget])
