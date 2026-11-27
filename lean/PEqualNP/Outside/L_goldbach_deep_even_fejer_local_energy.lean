import Mathlib

private lemma fe_meas (B : ℕ) (r : ℕ → ℝ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a:ℝ)/(q:ℝ)| ≤ r q} := by
  simp only [Set.setOf_exists, Set.setOf_and]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  refine (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter ((MeasurableSet.const _).inter ?_)))
  exact measurableSet_le (by fun_prop) measurable_const

private lemma fe_core (E : ℝ → ℂ) (hEmul : ∀ a b, E a * E b = E (a + b))
    (hEconj : ∀ a, (starRingEnd ℂ) (E a) = E (-a)) (hEcont : Continuous E)
    (P : ℝ → ℂ) (hP : Continuous P) (W : Set ℝ) (hW : MeasurableSet W) (m K : ℕ) (hK : 0 < K) :
    ((∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K,
      ‖∫ t in (0:ℝ)..1, W.indicator (fun u => P u * E (-((m+2*(i+(K-1)-j) : ℕ):ℝ)*u)) t‖^2 : ℝ):ℂ)
    = ∫ u in (0:ℝ)..1, ∫ v in (0:ℝ)..1, W.indicator P u * (starRingEnd ℂ) (W.indicator P v)
        * E (-((m+2*(K-1):ℕ):ℝ)*(u-v)) * ((‖∑ j ∈ Finset.range K, E (2*(j:ℝ)*(u-v))‖^2:ℝ):ℂ) := by
  have h01 : (0:ℝ) ≤ 1 := zero_le_one
  have hind : ∀ g : ℝ → ℂ, Continuous g →
      IntervalIntegrable (W.indicator g) MeasureTheory.volume 0 1 := by
    intro g hg
    have hi := hg.intervalIntegrable (μ := MeasureTheory.volume) 0 1
    exact ⟨hi.1.indicator hW, hi.2.indicator hW⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ × ℕ → ℝ → ℂ, A = fun p t =>
      W.indicator P t * E (-((m+2*(p.1+(K-1)-p.2) : ℕ):ℝ) * t) := ⟨_, rfl⟩
  have hApt : ∀ p, A p = W.indicator (fun t => P t * E (-((m+2*(p.1+(K-1)-p.2) : ℕ):ℝ) * t)) := by
    intro p; funext t; rw [hA]
    by_cases ht : t ∈ W <;> simp [ht]
  have hAconj : ∀ p, (fun t => (starRingEnd ℂ) (A p t)) =
      W.indicator (fun t => (starRingEnd ℂ) (P t * E (-((m+2*(p.1+(K-1)-p.2) : ℕ):ℝ) * t))) := by
    intro p; funext t; rw [hA]
    by_cases ht : t ∈ W <;> simp [ht]
  have hAint : ∀ p, IntervalIntegrable (A p) MeasureTheory.volume 0 1 := fun p => by
    rw [hApt p]; exact hind _ (by fun_prop)
  have hAcint : ∀ p, IntervalIntegrable (fun t => (starRingEnd ℂ) (A p t)) MeasureTheory.volume 0 1 :=
    fun p => by
      rw [hAconj p]; exact hind _ (Complex.continuous_conj.comp (by fun_prop))
  have hterm : ∀ p, ((‖∫ t in (0:ℝ)..1, A p t‖^2 : ℝ) : ℂ)
      = ∫ u in (0:ℝ)..1, ∫ v in (0:ℝ)..1, A p u * (starRingEnd ℂ) (A p v) := by
    intro p
    have hc : (starRingEnd ℂ) (∫ t in (0:ℝ)..1, A p t) = ∫ t in (0:ℝ)..1, (starRingEnd ℂ) (A p t) := by
      rw [intervalIntegral.integral_of_le h01, intervalIntegral.integral_of_le h01, integral_conj]
    push_cast
    rw [← Complex.mul_conj', hc, ← intervalIntegral.integral_mul_const]
    congr 1; funext u
    rw [← intervalIntegral.integral_const_mul]
  have hI1 : ∀ p u, IntervalIntegrable (fun v => A p u * (starRingEnd ℂ) (A p v))
      MeasureTheory.volume 0 1 := fun p u => (hAcint p).const_mul (A p u)
  have hI2 : ∀ p, IntervalIntegrable (fun u => ∫ v in (0:ℝ)..1, A p u * (starRingEnd ℂ) (A p v))
      MeasureTheory.volume 0 1 := by
    intro p
    have : (fun u => ∫ v in (0:ℝ)..1, A p u * (starRingEnd ℂ) (A p v))
        = fun u => A p u * ∫ v in (0:ℝ)..1, (starRingEnd ℂ) (A p v) := by
      funext u; exact intervalIntegral.integral_const_mul _ _
    rw [this]; exact (hAint p).mul_const _
  have hInt : ∀ i j : ℕ, (∫ t in (0:ℝ)..1,
      W.indicator (fun u => P u * E (-((m+2*(i+(K-1)-j) : ℕ):ℝ)*u)) t)
      = ∫ t in (0:ℝ)..1, A (i, j) t := by
    intro i j
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hA]
    by_cases ht : t ∈ W <;> simp [ht]
  have hpt : ∀ u v : ℝ, W.indicator P u * (starRingEnd ℂ) (W.indicator P v)
      * E (-((m+2*(K-1):ℕ):ℝ)*(u-v)) * ((‖∑ j ∈ Finset.range K, E (2*(j:ℝ)*(u-v))‖^2:ℝ):ℂ)
      = ∑ p ∈ Finset.range K ×ˢ Finset.range K, A p u * (starRingEnd ℂ) (A p v) := by
    intro u v
    have hz : ((‖∑ j ∈ Finset.range K, E (2*(j:ℝ)*(u-v))‖^2:ℝ):ℂ)
        = ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K,
            E (2*(j:ℝ)*(u-v)) * E (-(2*(i:ℝ)*(u-v))) := by
      push_cast
      rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, Finset.sum_comm]
      simp only [hEconj]
    rw [hz, Finset.mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [hA]
    rw [map_mul, hEconj]
    have hj' : j ≤ i + (K-1) := by have := Finset.mem_range.1 hj; omega
    have hcast : ((m+2*(i+(K-1)-j) : ℕ):ℝ) = (m:ℝ) + 2*(((i:ℝ) + ((K-1:ℕ):ℝ)) - j) := by
      push_cast [Nat.cast_sub hj']; ring
    have hcast0 : ((m+2*(K-1):ℕ):ℝ) = (m:ℝ) + 2*((K-1:ℕ):ℝ) := by push_cast; ring
    set X := W.indicator P u
    set Y := (starRingEnd ℂ) (W.indicator P v)
    calc X * Y * E (-((m+2*(K-1):ℕ):ℝ)*(u-v)) * (E (2*(j:ℝ)*(u-v)) * E (-(2*(i:ℝ)*(u-v))))
        = X * Y * (E (-((m+2*(K-1):ℕ):ℝ)*(u-v)) * (E (2*(j:ℝ)*(u-v)) * E (-(2*(i:ℝ)*(u-v))))) := by
          ring
      _ = X * Y * E (-((m+2*(K-1):ℕ):ℝ)*(u-v) + (2*(j:ℝ)*(u-v) + -(2*(i:ℝ)*(u-v)))) := by
          rw [hEmul, hEmul]
      _ = X * Y * E (-((m+2*(i+(K-1)-j) : ℕ):ℝ) * u + -(-((m+2*(i+(K-1)-j) : ℕ):ℝ) * v)) := by
          rw [hcast, hcast0]; ring_nf
      _ = X * E (-((m+2*(i+(K-1)-j) : ℕ):ℝ) * u) * (Y * E (-(-((m+2*(i+(K-1)-j) : ℕ):ℝ) * v))) := by
          rw [← hEmul]; ring
  calc ((∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K,
      ‖∫ t in (0:ℝ)..1, W.indicator (fun u => P u * E (-((m+2*(i+(K-1)-j) : ℕ):ℝ)*u)) t‖^2 : ℝ):ℂ)
      = ∑ p ∈ Finset.range K ×ˢ Finset.range K, ((‖∫ t in (0:ℝ)..1, A p t‖^2 : ℝ) : ℂ) := by
        rw [Finset.sum_product, Complex.ofReal_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hInt i j]
    _ = ∑ p ∈ Finset.range K ×ˢ Finset.range K,
          ∫ u in (0:ℝ)..1, ∫ v in (0:ℝ)..1, A p u * (starRingEnd ℂ) (A p v) :=
        Finset.sum_congr rfl (fun p _ => hterm p)
    _ = ∫ u in (0:ℝ)..1, ∑ p ∈ Finset.range K ×ˢ Finset.range K,
          ∫ v in (0:ℝ)..1, A p u * (starRingEnd ℂ) (A p v) :=
        (intervalIntegral.integral_finsetSum (fun p _ => hI2 p)).symm
    _ = ∫ u in (0:ℝ)..1, ∫ v in (0:ℝ)..1, ∑ p ∈ Finset.range K ×ˢ Finset.range K,
          A p u * (starRingEnd ℂ) (A p v) := by
        congr 1; funext u
        exact (intervalIntegral.integral_finsetSum (fun p _ => hI1 p u)).symm
    _ = _ := by
        congr 1; funext u; congr 1; funext v
        exact (hpt u v).symm

theorem PEqualNP.Outside.L_goldbach_deep_even_fejer_local_energy :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let deepCoeff := fun (n m : ℕ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun u => (S n w u)^2 * E (-(m:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let F := fun (n : ℕ) => (wideArcs n)ᶜ.indicator (fun u => (S n w u)^2); ∀ (n m H : ℕ), 0 < H → Even m → n ≤ m → m+4*(H-1) ≤ 2*n → ((∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H, ‖deepCoeff n (m+2*(i+(H-1)-j))‖^2 : ℝ):ℂ) = intervalIntegral (fun u => intervalIntegral (fun v => F n u * (starRingEnd ℂ) (F n v) * E (-((m+2*(H-1):ℕ):ℝ)*(u-v)) * ((‖∑ j ∈ Finset.range H, E (2*(j:ℝ)*(u-v))‖^2:ℝ):ℂ)) (0:ℝ) 1 MeasureTheory.volume) (0:ℝ) 1 MeasureTheory.volume := by
  intro w E S Q Q₁ H wideArcs deepCoeff F n m K hK _ _ _
  have hEmul : ∀ a b, E a * E b = E (a + b) := by
    intro a b; simp only [E]; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hEconj : ∀ a, (starRingEnd ℂ) (E a) = E (-a) := by
    intro a; simp only [E]; rw [← Complex.exp_conj]; congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
  have hEcont : Continuous E := by simp only [E]; fun_prop
  have hP : Continuous (fun u => (S n w u)^2) := by simp only [S, E]; fun_prop
  have hW : MeasurableSet (wideArcs n)ᶜ :=
    (fe_meas (Q₁ n) (fun q => (H n:ℝ)/((q:ℝ)*(n:ℝ)))).compl
  exact fe_core E hEmul hEconj hEcont (fun u => (S n w u)^2) hP (wideArcs n)ᶜ hW m K hK
