import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Continuity

noncomputable section

open MeasureTheory

private def arcSet (n qmax : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ qmax ∧ a ≤ q ∧ a.Coprime q ∧
       |t - (a:ℝ)/q| ≤ (qmax:ℝ)/((q:ℝ)*n)}

private theorem measurableArcs (n qmax : ℕ) : MeasurableSet (arcSet n qmax) := by
  let P := {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.1 ≤ qmax ∧ p.2 ≤ p.1 ∧ p.2.Coprime p.1}
  have eqn : arcSet n qmax = ⋃ p : P,
      {t : ℝ | |t - (p.1.2:ℝ)/p.1.1| ≤ (qmax:ℝ)/((p.1.1:ℝ)*n)} := by
    ext t
    simp only [arcSet, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q,a,h1,h2,h3,h4,ht⟩
      exact ⟨⟨(q,a),h1,h2,h3,h4⟩,ht⟩
    · rintro ⟨⟨⟨q,a⟩,h1,h2,h3,h4⟩,ht⟩
      exact ⟨q,a,h1,h2,h3,h4,ht⟩
  rw [eqn]
  exact MeasurableSet.iUnion (fun p =>
    measurableSet_le (Continuous.measurable (by continuity)) measurable_const)

private def ephase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

private def expSum (n : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), (w k : ℂ) * ephase ((k:ℝ)*t)

private def cosineMean (l : ℕ) (t : ℝ) : ℝ :=
  (∑ j ∈ Finset.range l, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(l:ℝ)

private lemma contMean (l : ℕ) : Continuous (cosineMean l) := by
  unfold cosineMean
  apply Continuous.div_const
  exact continuous_finsetSum _ (fun j _ => by fun_prop)

private def weightIntegral (A : Set ℝ) (n : ℕ) (w : ℕ → ℝ) (v : ℝ → ℝ) : ℝ :=
  (intervalIntegral (A.indicator (fun t =>
     (v t : ℂ) * expSum n w t * expSum n w t * ephase (-(n:ℝ)*t))) 0 1 volume).re

private theorem weight_add (A : Set ℝ) (hA : MeasurableSet A) (n : ℕ) (w : ℕ → ℝ)
    (v u : ℝ → ℝ) (hv : Continuous v) (hu : Continuous u) :
    weightIntegral A n w (fun t => v t + u t) =
    weightIntegral A n w v + weightIntegral A n w u := by
  let f (g : ℝ → ℝ) (t : ℝ) := (g t : ℂ) * expSum n w t * expSum n w t * ephase (-(n:ℝ)*t)
  have hE : Continuous ephase := by unfold ephase; fun_prop
  have hS : Continuous (expSum n w) := by
    unfold expSum
    exact continuous_finsetSum _ (fun k _ => continuous_const.mul (hE.comp (by fun_prop)))
  have hi (g : ℝ → ℝ) (hg : Continuous g) : IntervalIntegrable (A.indicator (f g)) volume 0 1 := by
    have hc : Continuous (f g) := by
      unfold f
      exact (((Complex.continuous_ofReal.comp hg).mul hS).mul hS).mul (hE.comp (by fun_prop))
    exact ⟨(hc.intervalIntegrable 0 1).1.indicator hA, (hc.intervalIntegrable 0 1).2.indicator hA⟩
  have eqn : A.indicator (f (fun t => v t + u t)) =
      fun t => A.indicator (f v) t + A.indicator (f u) t := by
    funext t
    by_cases ht : t ∈ A <;> simp [Set.indicator,ht,f,add_mul]
  unfold weightIntegral
  change (intervalIntegral (A.indicator (f (fun t => v t + u t))) 0 1 volume).re = _
  rw [eqn, intervalIntegral.integral_add (hi v hv) (hi u hu)]
  rfl

theorem Conjectures.Goldbach.BulkOffCoherenceTransfer :
(let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t));
let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
let low := fun (n k : ℕ) => if k^3≤n then w k else 0;
let high := fun (n k : ℕ) => w k-low n k;
let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume;
let L := fun n : ℕ => max 1 (Nat.log 2 n / 2);
let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ);
let J := fun (n : ℕ) (v : ℝ → ℝ) => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => (v u:ℂ)*S n (high n) u*S n (high n) u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re;
let τ := fun n : ℕ => 1/(2304*(1+(Real.log (n:ℝ))^2));
let small := fun (n : ℕ) (t : ℝ) => max (-(τ n)) (min (τ n) (1-K n t));
∀ n : ℕ, 2 ≤ n → |J n (small n)| ≤ (n:ℝ)/1152) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t));
let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
let low := fun (n k : ℕ) => if k^3≤n then w k else 0;
let high := fun (n k : ℕ) => w k-low n k;
let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume;
let L := fun n : ℕ => max 1 (Nat.log 2 n / 2);
let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ);
let J := fun (n : ℕ) (v : ℝ → ℝ) => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => (v u:ℂ)*S n (high n) u*S n (high n) u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re;
let τ := fun n : ℕ => 1/(2304*(1+(Real.log (n:ℝ))^2));
let small := fun (n : ℕ) (t : ℝ) => max (-(τ n)) (min (τ n) (1-K n t));
∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/1152 ≤ J n (fun t => 1-K n t-small n t)) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t));
let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
let low := fun (n k : ℕ) => if k^3≤n then w k else 0;
let high := fun (n k : ℕ) => w k-low n k;
let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume;
let L := fun n : ℕ => max 1 (Nat.log 2 n / 2);
let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ);
let J := fun (n : ℕ) (v : ℝ → ℝ) => (intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => (v u:ℂ)*S n (high n) u*S n (high n) u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume).re;
∃ N : ℕ, ∀ n ≥ N, Even n → -(n:ℝ)/576 ≤ J n (fun t => 1-K n t)) := by
  intro hsmall hrest w E S Q arcs low high I L K J
  obtain ⟨N, hN⟩ := hrest
  refine ⟨max N 2, ?_⟩
  intro n hn heven
  let tau : ℝ := 1/(2304*(1+(Real.log (n:ℝ))^2))
  let small (t : ℝ) := max (-tau) (min tau (1-K n t))
  let rest (t : ℝ) := 1-K n t-small t
  have hs := hsmall n ((le_max_right N 2).trans hn)
  have hr := hN n ((le_max_left N 2).trans hn) heven
  change |J n small| ≤ (n:ℝ)/1152 at hs
  change -(n:ℝ)/1152 ≤ J n rest at hr
  have hk : Continuous (K n) := contMean (L n)
  have hsm : Continuous small :=
    continuous_const.max (continuous_const.min (continuous_const.sub hk))
  have hre : Continuous rest := (continuous_const.sub hk).sub hsm
  have hA := (measurableArcs n (Q n)).compl
  have hadd := weight_add (arcs n)ᶜ hA n (high n) small rest hsm hre
  change J n (fun t => small t + rest t) = J n small + J n rest at hadd
  have eqn : (fun t => small t + rest t) = (fun t => 1-K n t) := by
    funext t
    dsimp [rest]
    ring
  rw [eqn] at hadd
  linarith [(abs_le.mp hs).1]
