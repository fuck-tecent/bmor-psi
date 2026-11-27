import Mathlib

-- Adapted from GoldbachBudget by CGandGameEngineLearner, PR #2327 (Apache-2.0): https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2327
namespace GoldbachBudget
noncomputable section

private def w (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
private def phase (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
private def spec (n : ℕ) (a : ℕ → ℝ) (t : ℝ) :=
  ∑ k ∈ Finset.range (n+1), (a k : ℂ) * phase ((k:ℝ)*t)
private def arcs (n : ℕ) : Set ℝ :=
  let Q := (Nat.log 2 (n+2))^2
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t-(a:ℝ)/(q:ℝ)| ≤ (Q:ℝ)/((q:ℝ)*(n:ℝ))}
private def full (n : ℕ) (s : Set ℝ) : ℂ :=
  intervalIntegral (fun t => s.indicator
    (fun u => (spec n w u)^2 * phase (-(n:ℝ)*u)) t) 0 1 MeasureTheory.volume
private def pair (n : ℕ) (a b : ℕ → ℝ) : ℂ :=
  intervalIntegral (fun t => (arcs n)ᶜ.indicator
    (fun u => spec n a u * spec n b u * phase (-(n:ℝ)*u)) t) 0 1 MeasureTheory.volume
private def low (n k : ℕ) := if k^3 ≤ n then w k else 0
private def high (n k : ℕ) := w k - low n k
private def mass (n : ℕ) := ∑ p ∈ Finset.range (n+1), w p * w (n-p)

private def K (n : ℕ) (t : ℝ) : ℝ :=
  let L := max 1 (Nat.log 2 n / 2)
  (∑ j ∈ Finset.range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L:ℝ)
private def J (n : ℕ) (v : ℝ → ℝ) :=
  (intervalIntegral (fun t => (arcs n)ᶜ.indicator
    (fun u => (v u:ℂ)*spec n (high n) u*spec n (high n) u*phase (-(n:ℝ)*u)) t)
    0 1 MeasureTheory.volume).re

private def kernelIntegrand (n : ℕ) (v : ℝ → ℝ) (t : ℝ) :=
  (arcs n)ᶜ.indicator
    (fun u => (v u:ℂ)*spec n (high n) u*spec n (high n) u*phase (-(n:ℝ)*u)) t

private def cutoff (n : ℕ) : ℝ := 1 / (2304 * (1 + (Real.log (n:ℝ))^2))
private def small (n : ℕ) (t : ℝ) :=
  max (-(cutoff n)) (min (cutoff n) (1 - K n t))
private theorem energyControl {n : ℕ} {a : ℝ} (ha : 0 ≤ a) {v : ℝ → ℝ}
    (hv : ∀ t, |v t| ≤ a) :
    |J n v| ≤ a * intervalIntegral (fun t => ‖spec n (high n) t‖^2) 0 1 MeasureTheory.volume := by
  have hp (x : ℝ) : ‖phase x‖ = 1 := by simp [phase, Complex.norm_exp]
  have pt (t : ℝ) : ‖kernelIntegrand n v t‖ ≤ a * ‖spec n (high n) t‖^2 := by
    by_cases ht : t ∈ (arcs n)ᶜ
    · simp only [kernelIntegrand, Set.indicator_of_mem ht, norm_mul, hp, mul_one, Complex.norm_real,
        Real.norm_eq_abs, pow_two, ← mul_assoc]
      gcongr
      exact hv t
    · simpa [kernelIntegrand, ht] using mul_nonneg ha (sq_nonneg ‖spec n (high n) t‖)
  have hc : Continuous (fun t : ℝ => a * ‖spec n (high n) t‖^2) := by unfold spec phase; fun_prop
  have hi := intervalIntegral.norm_integral_le_of_norm_le
    (f := kernelIntegrand n v) (by norm_num : (0:ℝ) ≤ 1)
    (Filter.Eventually.of_forall fun t _ => pt t) (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
  rw [intervalIntegral.integral_const_mul] at hi
  exact (Complex.abs_re_le_norm _).trans hi

theorem clippedBound
    (energy : ∀ n : ℕ, 2 ≤ n → intervalIntegral (fun t => ‖spec n (high n) t‖^2)
      0 1 MeasureTheory.volume ≤ ((n:ℝ)+1)*(Real.log (n:ℝ))^2) :
    ∀ n : ℕ, 2 ≤ n → |J n (small n)| ≤ (n:ℝ)/1152 := by
  intro n hn
  have ht : 0 ≤ cutoff n := by unfold cutoff; positivity
  have cap (t : ℝ) : |small n t| ≤ cutoff n := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  apply (energyControl ht cap).trans
  apply (mul_le_mul_of_nonneg_left (energy n hn) ht).trans
  unfold cutoff
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hlog := sq_nonneg (Real.log (n:ℝ))
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr (show (1:ℝ) ≤ n by linarith)) hlog]


end
end GoldbachBudget

noncomputable section

theorem Conjectures.Goldbach.BulkEnergyToClipped :
  (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ n:ℕ,2≤n → intervalIntegral (fun t => ‖S n (high n) t‖^2) (0:ℝ) 1 MeasureTheory.volume≤((n:ℝ)+1)*(Real.log (n:ℝ))^2) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let J := fun (n : ℕ) (v : ℝ → ℝ) => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => (v u:ℂ)*S n (high n) u*S n (high n) u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re; let τ := fun n : ℕ => 1/(2304*(1+(Real.log (n:ℝ))^2)); let small := fun (n : ℕ) (t : ℝ) => max (-(τ n)) (min (τ n) (1-K n t)); ∀ n : ℕ, 2 ≤ n → |J n (small n)| ≤ (n:ℝ)/1152) := by
  simpa only [GoldbachBudget.spec, GoldbachBudget.high, GoldbachBudget.low, GoldbachBudget.w, GoldbachBudget.phase, GoldbachBudget.arcs, GoldbachBudget.J, GoldbachBudget.small, GoldbachBudget.cutoff, GoldbachBudget.K] using GoldbachBudget.clippedBound

