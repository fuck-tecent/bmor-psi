import Mathlib

open MeasureTheory

namespace Conjectures.Goldbach.MinorSavingIffMajorUpper_aux

noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma phase_add (u v : ℝ) : E (u + v) = E u * E v := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma fourier_mode (m : ℤ) :
    (∫ t in (0 : ℝ)..1, E ((m : ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [E]
  let c : ℂ := (m : ℂ) * (2 * Real.pi * Complex.I)
  have he (t : ℝ) : E ((m : ℝ) * t) = Complex.exp (c * (t : ℂ)) := by
    unfold E c
    congr 1
    push_cast
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast hm)
      (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  simp [hm, c, Complex.exp_int_mul_two_pi_mul_I]

lemma coefficient (u : ℕ → ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, (∑ k ∈ Finset.range (n + 1), (u k : ℂ) * E ((k : ℝ) * t)) ^ 2 *
      E (-(n : ℝ) * t)) = ((∑ k ∈ Finset.range (n + 1), u k * u (n - k) : ℝ) : ℂ) := by
  let I := Finset.range (n + 1)
  let term := fun (k j : ℕ) (t : ℝ) =>
    ((u k : ℂ) * (u j : ℂ)) * E (((((k : ℤ) + j - n) : ℤ) : ℝ) * t)
  have hcont (k j : ℕ) : Continuous (term k j) := by dsimp [term, E]; fun_prop
  have hpoint (t : ℝ) : (∑ k ∈ I, (u k : ℂ) * E ((k : ℝ) * t)) ^ 2 * E (-(n : ℝ) * t) =
      ∑ k ∈ I, ∑ j ∈ I, term k j t := by
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
    dsimp [term]
    push_cast
    rw [show ((k : ℝ) + j - n) * t = ((k : ℝ) * t + j * t) + -(n : ℝ) * t by ring,
      phase_add, phase_add]
    ring
  have hrow (k : ℕ) (hk : k ∈ I) :
      (∫ t in (0 : ℝ)..1, ∑ j ∈ I, term k j t) = (u k : ℂ) * (u (n - k) : ℂ) := by
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont k j).intervalIntegrable _ _)]
    have hk' : k < n + 1 := Finset.mem_range.mp hk
    have hsub : n - k ∈ I := Finset.mem_range.mpr (by omega)
    simp only [term, intervalIntegral.integral_const_mul, fourier_mode]
    rw [Finset.sum_eq_single_of_mem (n - k) hsub]
    · simp [show (k : ℤ) + ((n - k : ℕ) : ℤ) - n = 0 by omega]
    · intro j _ hne
      simp [show (k : ℤ) + j - n ≠ 0 by omega]
  change (∫ t in (0 : ℝ)..1, (∑ k ∈ I, (u k : ℂ) * E ((k : ℝ) * t)) ^ 2 *
    E (-(n : ℝ) * t)) = _
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (continuous_finsetSum I (fun j _ => hcont k j)).intervalIntegrable _ _)]
  push_cast
  exact Finset.sum_congr rfl hrow

theorem measurable_rational_arcs (R n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ R ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ (R : ℝ) / ((q : ℝ) * (n : ℝ))} := by
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro a
  by_cases h : 1 ≤ q ∧ q ≤ R ∧ a ≤ q ∧ Nat.Coprime a q
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    have hmeas : MeasurableSet {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (R : ℝ) / (q * n)} :=
      measurableSet_le (show Continuous (fun t : ℝ => |t - (a : ℝ) / (q : ℝ)|) by fun_prop).measurable
        measurable_const
    convert hmeas using 1
    ext t
    exact ⟨fun h => h.2.2.2.2, fun h => ⟨h₁, h₂, h₃, h₄, h⟩⟩
  · convert MeasurableSet.empty (α := ℝ) using 1
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h₁, h₂, h₃, h₄, _⟩
    exact h ⟨h₁, h₂, h₃, h₄⟩

theorem indicator_integral_split {g : ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s)
    {a b : ℝ} (hg : IntervalIntegrable g volume a b) :
    intervalIntegral (s.indicator g) a b volume +
      intervalIntegral (sᶜ.indicator g) a b volume = intervalIntegral g a b volume := by
  have hi {v : Set ℝ} (hv : MeasurableSet v) :
      IntervalIntegrable (v.indicator g) volume a b :=
    ⟨hg.1.indicator hv, hg.2.indicator hv⟩
  rw [← intervalIntegral.integral_add (hi hs) (hi hs.compl)]
  apply congrArg (fun h : ℝ → ℂ => intervalIntegral h a b volume)
  funext t
  by_cases ht : t ∈ s <;> simp [ht]

noncomputable def w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0

noncomputable def S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n + 1)) (fun k => (u k : ℂ) * E ((k : ℝ) * t))

noncomputable def Q (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

noncomputable def arcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))}

noncomputable def f (n : ℕ) (t : ℝ) : ℂ := (S n w t) ^ 2 * E (-(n : ℝ) * t)

noncomputable def minor (n : ℕ) : ℂ :=
  intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0 : ℝ) 1 volume

noncomputable def major (n : ℕ) : ℂ :=
  intervalIntegral (fun t => (arcs n).indicator (f n) t) (0 : ℝ) 1 volume

noncomputable def conv (u v : ℕ → ℝ) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (n + 1)) (fun k => u k * v (n - k))

theorem major_add_minor (n : ℕ) : major n + minor n = (conv w w n : ℂ) := by
  have hA : MeasurableSet (arcs n) := measurable_rational_arcs (Q n) n
  have hcont : Continuous (f n) := by
    first
    | (dsimp [f, S, E]; fun_prop)
    | (unfold f S E; fun_prop)
    | (simp only [f, S, E]; fun_prop)
    | exact (by fun_prop : Continuous (fun t : ℝ =>
        (Finset.sum (Finset.range (n + 1))
          (fun k => (w k : ℂ) * Complex.exp (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I))) ^ 2 *
        Complex.exp (((2 * Real.pi * (-(n : ℝ) * t) : ℝ) : ℂ) * Complex.I)))
  have hsplit : major n + minor n = intervalIntegral (f n) (0 : ℝ) 1 volume :=
    indicator_integral_split hA (hcont.intervalIntegrable 0 1)
  have hcoef : intervalIntegral (f n) (0 : ℝ) 1 volume = (conv w w n : ℂ) := by
    first
    | exact coefficient w n
    | simpa [f, S, conv] using coefficient w n
  exact hsplit.trans hcoef

theorem re_major_add_minor (n : ℕ) : (major n).re + (minor n).re = conv w w n := by
  have h := congrArg Complex.re (major_add_minor n)
  first
  | simpa using h
  | (rw [Complex.add_re, Complex.ofReal_re] at h; exact h)

theorem per_n (n : ℕ) (e : ℝ) :
    -(e * (n : ℝ)) ≤ (minor n).re ↔ (major n).re ≤ conv w w n + e * (n : ℝ) := by
  have h := re_major_add_minor n
  constructor
  · intro hh
    first
    | linarith
    | nlinarith [h, hh]
  · intro hh
    first
    | linarith
    | nlinarith [h, hh]

theorem main_iff :
    (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      -(e * (n : ℝ)) ≤ (minor n).re) ↔
    (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      (major n).re ≤ conv w w n + e * (n : ℝ)) := by
  constructor
  · intro h e he
    obtain ⟨N, hN⟩ := h e he
    exact ⟨N, fun n hn hEven => (per_n n e).mp (hN n hn hEven)⟩
  · intro h e he
    obtain ⟨N, hN⟩ := h e he
    exact ⟨N, fun n hn hEven => (per_n n e).mpr (hN n hn hEven)⟩

end Conjectures.Goldbach.MinorSavingIffMajorUpper_aux

theorem Conjectures.Goldbach.MinorSavingIffMajorUpper : (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let minor := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; (∀ e : ℝ, 0<e → ∃ N : ℕ, ∀ n : ℕ, N≤n → Even n → -(e*(n:ℝ)) ≤ (minor n).re)) ↔ (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let major := fun n : ℕ => intervalIntegral (fun t => (arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let conv := fun (u v : ℕ → ℝ) (n : ℕ) => Finset.sum (Finset.range (n+1)) (fun k => u k*v (n-k)); (∀ e : ℝ, 0<e → ∃ N : ℕ, ∀ n : ℕ, N≤n → Even n → (major n).re ≤ conv w w n + e*(n:ℝ))) :=
  by
    constructor
    · intro h
      exact Conjectures.Goldbach.MinorSavingIffMajorUpper_aux.main_iff.mp h
    · intro h
      exact Conjectures.Goldbach.MinorSavingIffMajorUpper_aux.main_iff.mpr h
