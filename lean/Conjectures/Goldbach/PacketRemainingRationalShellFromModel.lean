import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open MeasureTheory Set
noncomputable section

namespace Packet42

private def w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0

private def E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

private def S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t))

private def Q := fun n : ℕ => (Nat.log 2 (n+2))^2

private def low := fun (n k : ℕ) => if k^3≤n then w k else 0

private def high := fun (n k : ℕ) => w k-low n k

private def W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}

private def F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2

private def G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2))

private def m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume

private def arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}

private def L := fun n : ℕ => max 1 (Nat.log 2 n / 2)

private def K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ)

private def B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}

private def o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1

private theorem measArcs (n : ℕ) : MeasurableSet (arcs n) := by
  classical
  simp only [arcs, Set.ofPred_exists]
  apply MeasurableSet.iUnion; intro q
  apply MeasurableSet.iUnion; intro a
  by_cases hp : 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q
  · rcases hp with ⟨h1,h2,h3,h4⟩
    simp only [h1,h2,h3,and_iff_right h4,true_and]
    apply measurableSet_le
    · exact (continuous_id.sub continuous_const).abs.measurable
    · exact measurable_const
  · convert MeasurableSet.empty (α := ℝ) using 1
    ext t; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    tauto

private theorem measW (n : ℕ) (p : ℕ → Prop) : MeasurableSet (W n p) := by
  classical
  simp only [W, Set.ofPred_exists]
  apply MeasurableSet.iUnion; intro q
  apply MeasurableSet.iUnion; intro a
  by_cases hp : 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q
  · rcases hp with ⟨h1,h2,h3,h4,h5⟩
    simp only [h1,h2,h3,and_iff_right h4,h5,true_and]
    apply measurableSet_le
    · exact (continuous_id.sub continuous_const).abs.measurable
    · exact measurable_const
  · convert MeasurableSet.empty (α := ℝ) using 1
    ext t; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    tauto

private theorem measB (n : ℕ) : MeasurableSet (B n) := by
  change MeasurableSet ((arcs n)ᶜ ∩ {t : ℝ | (1:ℝ)/2 < K n t})
  apply (measArcs n).compl.inter
  exact (isOpen_lt continuous_const (show Continuous (K n) by unfold K; fun_prop)).measurableSet

private theorem contG (n : ℕ) : Continuous (G n) := by
  unfold G
  simp_rw [← div_div]
  fun_prop (disch := first | intro x; positivity | positivity)

private theorem intInd {s : Set ℝ} {f : ℝ → ℝ} (hs : MeasurableSet s) (hf : Continuous f) :
    Integrable (s.indicator f) (volume.restrict (Ioc 0 1)) :=
  (hf.integrableOn_Ioc : Integrable f (volume.restrict (Ioc 0 1))).indicator hs

private theorem nonnegG (n : ℕ) (t : ℝ) : 0 ≤ G n t := by unfold G; positivity

private theorem measR (n : ℕ) :
    MeasurableSet ((B n ∩ W n (fun _ => True)) \ W n (o n)) :=
  ((measB n).inter (measW n _)).diff (measW n _)


end Packet42
open Packet42

theorem Conjectures.Goldbach.PacketRemainingRationalShellFromModel :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m (W n (fun _ => True)) (fun t => max 0 (F n t - G n t)) ≤ (n:ℝ)/4608) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) \ W n (o n)) (G n) ≤ (n:ℝ)/4608) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) \ W n (o n)) (F n) ≤ (n:ℝ)/2304) := by
  intro hx hg
  change ∃ N : ℕ, ∀ n ≥ N, Even n → m (W n (fun _ => True)) (fun t => max 0 (F n t - G n t)) ≤ (n:ℝ)/4608 at hx
  change ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ W n (fun _ => True)) \ W n (o n)) (G n) ≤ (n:ℝ)/4608 at hg
  obtain ⟨Nx,hx⟩ := hx
  obtain ⟨Ng,hg⟩ := hg
  refine ⟨max Nx Ng,fun n hn he => ?_⟩
  have h1 := hx n ((le_max_left _ _).trans hn) he
  have h2 := hg n ((le_max_right _ _).trans hn) he
  let R := ((B n ∩ W n (fun _ => True)) \ W n (o n))
  let A := W n (fun _ => True)
  let U := fun t => max 0 (F n t - G n t)
  have cF : Continuous (F n) := by unfold F S E; fun_prop
  have cU : Continuous U := continuous_const.max (cF.sub (contG n))
  change m R (F n) ≤ (n:ℝ)/2304
  have h : m R (F n) ≤ m R (G n) + m A U := by
    unfold m; simp only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [← integral_add (intInd (measR n) (contG n)) (intInd (measW n _) cU)]
    apply integral_mono (intInd (measR n) cF) ((intInd (measR n) (contG n)).add (intInd (measW n _) cU))
    intro t
    change R.indicator (F n) t ≤ R.indicator (G n) t + A.indicator U t
    by_cases ht : t ∈ R
    · rw [Set.indicator_of_mem ht,Set.indicator_of_mem ht,Set.indicator_of_mem (show t ∈ A from ht.1.2)]
      have := le_max_right 0 (F n t - G n t)
      dsimp [U]; linarith
    · rw [Set.indicator_of_notMem ht,Set.indicator_of_notMem ht,zero_add]
      exact Set.indicator_nonneg (fun x _ => le_max_left _ _) _
  change m A U ≤ _ at h1
  change m R (G n) ≤ _ at h2
  linarith
