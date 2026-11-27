import Mathlib

namespace Conjectures.Goldbach

open MeasureTheory

private lemma measurableSet_arcs (n : ℕ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Nat.log 2 (n+2))^2 ∧ a ≤ q ∧
      Nat.Coprime a q ∧
      |t - (a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ))} := by
  simp only [Set.setOf_exists, Set.setOf_and]
  refine MeasurableSet.iUnion (fun q => MeasurableSet.iUnion (fun a => ?_))
  refine (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter ((MeasurableSet.const _).inter ?_)))
  exact measurableSet_le (by fun_prop) measurable_const

private lemma continuous_denom (n : ℕ) :
    Continuous (fun t : ℝ => ((n:ℝ)+1)^2/(1+((n:ℝ)+1)^2*
      ‖Complex.exp (((2*Real.pi*(30*t):ℝ):ℂ)*Complex.I)-1‖^2)) := by
  have hE : Continuous (fun t : ℝ => Complex.exp (((2*Real.pi*(30*t):ℝ):ℂ)*Complex.I)) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_const.mul continuous_id))).mul continuous_const)
  have hsq : Continuous (fun t : ℝ => ‖Complex.exp (((2*Real.pi*(30*t):ℝ):ℂ)*Complex.I)-1‖^2) :=
    ((hE.sub continuous_const).norm).pow 2
  have hden : Continuous (fun t : ℝ => 1+((n:ℝ)+1)^2*
      ‖Complex.exp (((2*Real.pi*(30*t):ℝ):ℂ)*Complex.I)-1‖^2) :=
    continuous_const.add (continuous_const.mul hsq)
  have hne : ∀ t : ℝ, (1+((n:ℝ)+1)^2*
      ‖Complex.exp (((2*Real.pi*(30*t):ℝ):ℂ)*Complex.I)-1‖^2) ≠ 0 := by
    intro t
    have h1 : (0:ℝ) ≤ ((n:ℝ)+1)^2 * ‖Complex.exp (((2*Real.pi*(30*t):ℝ):ℂ)*Complex.I)-1‖^2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith
  exact continuous_const.div hden hne

private lemma envelope_transfer
    (arcs : ℕ → Set ℝ) (Fn Dn : ℕ → ℝ → ℝ)
    (hpt : ∀ n t, Fn n t ≤ 3616 * Dn n t)
    (hnonneg : ∀ n t, 0 ≤ Fn n t)
    (hmeas : ∀ n, MeasurableSet (arcs n))
    (hDcont : ∀ n, Continuous (Dn n))
    (h2 : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      intervalIntegral ((arcs n)ᶜ.indicator (Dn n)) (0:ℝ) 1 MeasureTheory.volume
        ≤ ε * (n:ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      intervalIntegral ((arcs n)ᶜ.indicator (Fn n)) (0:ℝ) 1 MeasureTheory.volume
        ≤ ε * (n:ℝ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h2 (ε/3616) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hbig0 : IntegrableOn ((arcs n)ᶜ.indicator (fun t => 3616 * Dn n t)) (Set.Ioc 0 1)
      MeasureTheory.volume :=
    ((continuous_const.mul (hDcont n)).integrableOn_Ioc).indicator (hmeas n).compl
  have hbig : MeasureTheory.Integrable ((arcs n)ᶜ.indicator (fun t => 3616 * Dn n t))
      (MeasureTheory.volume.restrict (Set.Ioc 0 1)) := hbig0
  have hmono : intervalIntegral ((arcs n)ᶜ.indicator (Fn n)) (0:ℝ) 1 MeasureTheory.volume
      ≤ intervalIntegral ((arcs n)ᶜ.indicator (fun t => 3616 * Dn n t)) (0:ℝ) 1
        MeasureTheory.volume := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    refine integral_mono_of_nonneg ?_ hbig ?_
    · refine Filter.Eventually.of_forall (fun t => ?_)
      by_cases ht : t ∈ (arcs n)ᶜ
      · simpa [Set.indicator, ht] using hnonneg n t
      · simp [Set.indicator, ht]
    · refine Filter.Eventually.of_forall (fun t => ?_)
      by_cases ht : t ∈ (arcs n)ᶜ
      · simpa [Set.indicator, ht] using hpt n t
      · simp [Set.indicator, ht]
  have hscale : intervalIntegral ((arcs n)ᶜ.indicator (fun t => 3616 * Dn n t)) (0:ℝ) 1
      MeasureTheory.volume
      = 3616 * intervalIntegral ((arcs n)ᶜ.indicator (Dn n)) (0:ℝ) 1
        MeasureTheory.volume := by
    have heq : (arcs n)ᶜ.indicator (fun t => 3616 * Dn n t)
        = fun t => 3616 * ((arcs n)ᶜ.indicator (Dn n) t) := by
      funext t
      by_cases ht : t ∈ (arcs n)ᶜ <;> simp [Set.indicator, ht]
    rw [heq, intervalIntegral.integral_const_mul]
  have hbound : intervalIntegral ((arcs n)ᶜ.indicator (Dn n)) (0:ℝ) 1
      MeasureTheory.volume ≤ (ε/3616) * (n:ℝ) := hN n hn
  calc intervalIntegral ((arcs n)ᶜ.indicator (Fn n)) (0:ℝ) 1 MeasureTheory.volume
      ≤ intervalIntegral ((arcs n)ᶜ.indicator (fun t => 3616 * Dn n t)) (0:ℝ) 1
        MeasureTheory.volume := hmono
    _ = 3616 * intervalIntegral ((arcs n)ᶜ.indicator (Dn n)) (0:ℝ) 1
        MeasureTheory.volume := hscale
    _ ≤ 3616 * ((ε/3616) * (n:ℝ)) := mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = ε * (n:ℝ) := by ring

theorem PacketWheelEnvelopeTransfer :
    (let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let D := fun (n : ℕ) (t : ℝ) => ((n:ℝ)+1)^2/(1+((n:ℝ)+1)^2*‖E (30*t)-1‖^2); ∀ (n : ℕ) (t : ℝ), ‖S n model t‖^2 ≤ 3616*D n t) → (let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let D := fun (n : ℕ) (t : ℝ) => ((n:ℝ)+1)^2/(1+((n:ℝ)+1)^2*‖E (30*t)-1‖^2); ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, intervalIntegral ((arcs n)ᶜ.indicator (D n)) (0:ℝ) 1 MeasureTheory.volume ≤ ε*(n:ℝ)) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, intervalIntegral ((arcs n)ᶜ.indicator (fun t => ‖S n model t‖^2)) (0:ℝ) 1 MeasureTheory.volume ≤ ε*(n:ℝ)) := by
  intro H1 H2
  have h := envelope_transfer
    (fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤(Nat.log 2 (n+2))^2 ∧ a≤q ∧
      Nat.Coprime a q ∧
      |t-(a:ℝ)/(q:ℝ)| ≤ (((Nat.log 2 (n+2))^2 : ℕ):ℝ)/((q:ℝ)*(n:ℝ))})
    (fun (n : ℕ) (t : ℝ) => ‖Finset.sum (Finset.range (n+1))
      (fun k => Complex.ofReal (if Nat.Coprime k 30 then (30:ℝ)/8 else (0:ℝ))*
        Complex.exp (((2*Real.pi*((k:ℝ)*t):ℝ):ℂ)*Complex.I))‖^2)
    (fun (n : ℕ) (t : ℝ) => ((n:ℝ)+1)^2/(1+((n:ℝ)+1)^2*
      ‖Complex.exp (((2*Real.pi*(30*t):ℝ):ℂ)*Complex.I)-1‖^2))
    H1 (fun n t => sq_nonneg _) (fun n => measurableSet_arcs n)
    (fun n => continuous_denom n) H2
  exact h

end Conjectures.Goldbach
