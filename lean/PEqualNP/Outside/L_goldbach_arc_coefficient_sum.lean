import Mathlib

open MeasureTheory

namespace PEqualNP.Outside.L_goldbach_arc_coefficient_sum

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

lemma coefficient (w : ℕ → ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, (∑ k ∈ Finset.range (n + 1), (w k : ℂ) * E ((k : ℝ) * t)) ^ 2 *
      E (-(n : ℝ) * t)) = ((∑ k ∈ Finset.range (n + 1), w k * w (n - k) : ℝ) : ℂ) := by
  let I := Finset.range (n + 1)
  let term := fun (k j : ℕ) (t : ℝ) =>
    ((w k : ℂ) * (w j : ℂ)) * E (((((k : ℤ) + j - n) : ℤ) : ℝ) * t)
  have hcont (k j : ℕ) : Continuous (term k j) := by dsimp [term, E]; fun_prop
  have hpoint (t : ℝ) : (∑ k ∈ I, (w k : ℂ) * E ((k : ℝ) * t)) ^ 2 * E (-(n : ℝ) * t) =
      ∑ k ∈ I, ∑ j ∈ I, term k j t := by
    simp only [sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
    dsimp [term]
    push_cast
    rw [show ((k : ℝ) + j - n) * t = ((k : ℝ) * t + j * t) + -(n : ℝ) * t by ring,
      phase_add, phase_add]
    ring
  have hrow (k : ℕ) (hk : k ∈ I) :
      (∫ t in (0 : ℝ)..1, ∑ j ∈ I, term k j t) = (w k : ℂ) * (w (n - k) : ℂ) := by
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont k j).intervalIntegrable _ _)]
    have hk' : k < n + 1 := Finset.mem_range.mp hk
    have hsub : n - k ∈ I := Finset.mem_range.mpr (by omega)
    simp only [term, intervalIntegral.integral_const_mul, fourier_mode]
    rw [Finset.sum_eq_single_of_mem (n - k) hsub]
    · simp [show (k : ℤ) + ((n - k : ℕ) : ℤ) - n = 0 by omega]
    · intro j _ hne
      simp [show (k : ℤ) + j - n ≠ 0 by omega]
  change (∫ t in (0 : ℝ)..1, (∑ k ∈ I, (w k : ℂ) * E ((k : ℝ) * t)) ^ 2 *
    E (-(n : ℝ) * t)) = _
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (continuous_finsetSum I (fun j _ => hcont k j)).intervalIntegrable _ _)]
  push_cast
  exact Finset.sum_congr rfl hrow

/-- Rational neighborhoods of any prescribed cutoff and radius form a measurable set. -/
theorem measurable_rational_arcs (Q n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / ((q : ℝ) * (n : ℝ))} := by
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro a
  by_cases h : 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    have hmeas : MeasurableSet {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / (q * n)} :=
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

/-- Split any interval-integrable complex coefficient at an arbitrary measurable set. -/
theorem indicator_integral_split {f : ℝ → ℂ} {s : Set ℝ} (hs : MeasurableSet s)
    {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    intervalIntegral (s.indicator f) a b volume +
      intervalIntegral (sᶜ.indicator f) a b volume = intervalIntegral f a b volume := by
  have hi {u : Set ℝ} (hu : MeasurableSet u) :
      IntervalIntegrable (u.indicator f) volume a b :=
    ⟨hf.1.indicator hu, hf.2.indicator hu⟩
  rw [← intervalIntegral.integral_add (hi hs) (hi hs.compl)]
  apply congrArg (fun g : ℝ → ℂ => intervalIntegral g a b volume)
  funext t
  by_cases ht : t ∈ s <;> simp [ht]


end PEqualNP.Outside.L_goldbach_arc_coefficient_sum

theorem PEqualNP.Outside.L_goldbach_arc_coefficient_sum : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let major := fun n : ℕ => intervalIntegral (fun t => (arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let minor := fun n : ℕ => intervalIntegral (fun t => (arcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let conv := fun (u v : ℕ → ℝ) (n : ℕ) => Finset.sum (Finset.range (n+1)) (fun k => u k*v (n-k)); ∀ n, major n+minor n=(conv w w n:ℂ) := by
  intro w E S Q arcs f major minor conv n
  have hA : MeasurableSet (arcs n) :=
    PEqualNP.Outside.L_goldbach_arc_coefficient_sum.measurable_rational_arcs (Q n) n
  have hcont : Continuous (f n) := by
    dsimp [f, S, E]
    fun_prop
  exact (PEqualNP.Outside.L_goldbach_arc_coefficient_sum.indicator_integral_split hA
    (hcont.intervalIntegrable 0 1)).trans
    (PEqualNP.Outside.L_goldbach_arc_coefficient_sum.coefficient w n)
