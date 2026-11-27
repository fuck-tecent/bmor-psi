import Mathlib

open MeasureTheory Set

namespace Conjectures.Goldbach.PacketShortOrderShellFromModel_aux

noncomputable section

def w : ℕ → ℝ := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0
def E : ℝ → ℂ := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
def S : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t))
def Q : ℕ → ℕ := fun n : ℕ => (Nat.log 2 (n+2))^2
def arcs : ℕ → Set ℝ := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}
def low : ℕ → ℕ → ℝ := fun (n k : ℕ) => if k^3≤n then w k else 0
def high : ℕ → ℕ → ℝ := fun (n k : ℕ) => w k-low n k
def L : ℕ → ℕ := fun n : ℕ => max 1 (Nat.log 2 n / 2)
def K : ℕ → ℝ → ℝ := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ)
def B : ℕ → Set ℝ := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}
def W : ℕ → (ℕ → Prop) → Set ℝ := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}
def o : ℕ → ℕ → Prop := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1
def F : ℕ → ℝ → ℝ := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2
def G : ℕ → ℝ → ℝ := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2))
def m : Set ℝ → (ℝ → ℝ) → ℝ := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume
def R : ℕ → Set ℝ := fun n : ℕ => (B n ∩ W n (fun _ => True)) ∩ W n (o n)

theorem measurable_arcs (n : ℕ) : MeasurableSet (arcs n) := by
  simp only [arcs, Set.ofPred_exists, Set.ofPred_and]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  refine (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter ((MeasurableSet.const _).inter ?_)))
  exact measurableSet_le (by fun_prop) measurable_const

theorem measurable_W (n : ℕ) (p : ℕ → Prop) : MeasurableSet (W n p) := by
  simp only [W, Set.ofPred_exists, Set.ofPred_and]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  refine (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      ((MeasurableSet.const _).inter ?_))))
  exact measurableSet_le (by fun_prop) measurable_const

theorem measurable_B (n : ℕ) : MeasurableSet (B n) := by
  unfold B
  rw [Set.ofPred_and]
  have hK : Measurable (K n) := by
    unfold K
    fun_prop
  exact (measurable_arcs n).compl.inter (measurableSet_lt measurable_const hK)

theorem measurable_R (n : ℕ) : MeasurableSet (R n) := by
  exact ((measurable_B n).inter (measurable_W n (fun _ => True))).inter
    (measurable_W n (o n))

theorem continuous_S (n : ℕ) (v : ℕ → ℝ) : Continuous (S n v) := by
  unfold S E
  fun_prop

theorem continuous_F (n : ℕ) : Continuous (F n) := by
  change Continuous (fun t => ‖S n (high n) t‖ ^ 2)
  exact (continuous_S n (high n)).norm.pow 2

theorem continuous_G (n : ℕ) : Continuous (G n) := by
  unfold G
  refine continuous_finsetSum _ fun q hq => ?_
  have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
  have hqreal : (0:ℝ) < q := by exact_mod_cast hqpos
  have htot : (0:ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr hqpos
  refine continuous_finsetSum _ fun a _ => ?_
  apply Continuous.div₀
  · fun_prop
  · fun_prop
  · intro t
    positivity

theorem core_ineq {f g : ℝ → ℝ} {s T : Set ℝ}
    (hsub : s ⊆ T) (hfc : Continuous f) (hgc : Continuous g)
    (hs : MeasurableSet s) (hT : MeasurableSet T) :
    intervalIntegral (s.indicator f) 0 1 volume ≤
      intervalIntegral (T.indicator (fun t => max 0 (f t - g t))) 0 1 volume +
        intervalIntegral (s.indicator g) 0 1 volume := by
  have hpt : ∀ t,
      s.indicator f t ≤
        T.indicator (fun t => max 0 (f t - g t)) t + s.indicator g t := by
    intro t
    by_cases ht : t ∈ s
    · simp only [Set.indicator_of_mem ht, Set.indicator_of_mem (hsub ht)]
      linarith [le_max_right 0 (f t - g t)]
    · simp only [Set.indicator_of_notMem ht]
      by_cases hTt : t ∈ T
      · rw [Set.indicator_of_mem hTt]
        linarith [le_max_left 0 (f t - g t)]
      · rw [Set.indicator_of_notMem hTt]
        simp
  have hmaxc : Continuous (fun t => max 0 (f t - g t)) :=
    continuous_const.max (hfc.sub hgc)
  have hfi : IntervalIntegrable (s.indicator f) volume 0 1 :=
    intervalIntegrable_iff.mpr
      ((hfc.intervalIntegrable 0 1).def'.indicator hs)
  have hmaxi :
      IntervalIntegrable (T.indicator (fun t => max 0 (f t - g t))) volume 0 1 :=
    intervalIntegrable_iff.mpr
      ((hmaxc.intervalIntegrable 0 1).def'.indicator hT)
  have hgi : IntervalIntegrable (s.indicator g) volume 0 1 :=
    intervalIntegrable_iff.mpr
      ((hgc.intervalIntegrable 0 1).def'.indicator hs)
  calc
    intervalIntegral (s.indicator f) 0 1 volume ≤
        intervalIntegral
          (fun t => T.indicator (fun t => max 0 (f t - g t)) t + s.indicator g t)
          0 1 volume :=
      intervalIntegral.integral_mono (by norm_num) hfi (hmaxi.add hgi) hpt
    _ = intervalIntegral (T.indicator (fun t => max 0 (f t - g t))) 0 1 volume +
        intervalIntegral (s.indicator g) 0 1 volume :=
      intervalIntegral.integral_add hmaxi hgi

end

end Conjectures.Goldbach.PacketShortOrderShellFromModel_aux

open Conjectures.Goldbach.PacketShortOrderShellFromModel_aux

theorem Conjectures.Goldbach.PacketShortOrderShellFromModel : 
(let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m (W n (fun _ => True)) (fun t => max 0 (F n t - G n t)) ≤ (n:ℝ)/4608) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) ∩ W n (o n)) (G n) ≤ (n:ℝ)/4608) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let F := fun (n : ℕ) (t : ℝ) => ‖S n (high n) t‖^2; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) ∩ W n (o n)) (F n) ≤ (n:ℝ)/2304) := by
  intro H1 H2
  obtain ⟨N1, h1⟩ := H1
  obtain ⟨N2, h2⟩ := H2
  refine ⟨max N1 N2, fun n hn hEven => ?_⟩
  have e1 : m (W n (fun _ => True)) (fun t => max 0 (F n t - G n t)) ≤ (n:ℝ)/4608 :=
    h1 n (le_trans (le_max_left N1 N2) hn) hEven
  have e2 : m (R n) (G n) ≤ (n:ℝ)/4608 :=
    h2 n (le_trans (le_max_right N1 N2) hn) hEven
  have hcore : m (R n) (F n)
      ≤ m (W n (fun _ => True)) (fun t => max 0 (F n t - G n t)) + m (R n) (G n) :=
    core_ineq (fun t ht => ht.1.2) (continuous_F n) (continuous_G n) (measurable_R n)
      (measurable_W n _)
  calc m (R n) (F n)
      ≤ m (W n (fun _ => True)) (fun t => max 0 (F n t - G n t)) + m (R n) (G n) := hcore
    _ ≤ (n:ℝ)/4608 + (n:ℝ)/4608 := add_le_add e1 e2
    _ = (n:ℝ)/2304 := by ring

