import Mathlib

open scoped Classical

theorem Conjectures.Goldbach.BulkBinaryPartition :
  let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let J := fun (n : ℕ) (v : ℝ → ℝ) => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => (v u:ℂ)*S n (high n) u*S n (high n) u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re; ∀ n : ℕ, (I n (high n) (high n)).re = J n (K n) + J n (fun t => 1-K n t) := by
  intro w E S Q arcs low high I L K J n
  have hA : MeasurableSet (arcs n) := by
    dsimp only [arcs]
    simp only [Set.ofPred_exists, Set.ofPred_and]
    measurability
  let f := fun t : ℝ => S n (high n) t * S n (high n) t * E (-(n:ℝ)*t)
  let F := fun (v : ℝ → ℝ) t => (arcs n)ᶜ.indicator (fun u => (v u:ℂ) * f u) t
  have hc : Continuous f := by dsimp [f,S,E]; fun_prop
  have hK : Continuous (K n) := by dsimp [K]; fun_prop
  have hi (v : ℝ → ℝ) (hv : Continuous v) :
      IntervalIntegrable (F v) MeasureTheory.volume 0 1 := by
    have hh := ((Complex.continuous_ofReal.comp hv).mul hc).intervalIntegrable (μ := MeasureTheory.volume) 0 1
    exact ⟨hh.1.indicator hA.compl, hh.2.indicator hA.compl⟩
  have hadd : (fun t => (arcs n)ᶜ.indicator f t) =
      fun t => F (K n) t + F (fun u => 1-K n u) t := by
    funext t
    by_cases ht : t ∈ (arcs n)ᶜ
    · simp only [F, Set.indicator_of_mem ht, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    · simp [F, Set.indicator_of_notMem ht]
  change (intervalIntegral (fun t => (arcs n)ᶜ.indicator f t) 0 1 MeasureTheory.volume).re = _
  rw [hadd, intervalIntegral.integral_add (hi _ hK) (hi (fun u => 1-K n u) (continuous_const.sub hK))]
  simp only [Complex.add_re, J, F, f, mul_assoc]
