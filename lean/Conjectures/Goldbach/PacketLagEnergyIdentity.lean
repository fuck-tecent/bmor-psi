import Mathlib

private theorem pk_arcsMeas (X : ℕ) (ρ n : ℝ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ X ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)} := by
  have hset : {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ X ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)}
      = ⋃ q : ℕ, ⋃ a : ℕ, ({t : ℝ | 1 ≤ q ∧ q ≤ X ∧ a ≤ q ∧ Nat.Coprime a q} ∩
        {t : ℝ | |t - (a:ℝ)/(q:ℝ)| ≤ ρ/((q:ℝ)*n)}) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
      exact ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨q, a, ⟨h1, h2, h3, h4⟩, h5⟩
      exact ⟨q, a, h1, h2, h3, h4, h5⟩
  rw [hset]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  refine (MeasurableSet.const _).inter ?_
  exact measurableSet_le (by fun_prop) (by fun_prop)

private theorem pk_upperTriangleLags (n : ℕ) (g : ℕ → ℕ → ℝ) :
    (∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1), if i < j then g i j else 0) =
      ∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.range (n+1-h), g k (k+h) := by
  let R := Finset.range (n+1)
  let U := (R ×ˢ R).filter (fun p => p.1 < p.2)
  let D := (Finset.Icc 1 n).sigma (fun h => Finset.range (n+1-h))
  calc
    _ = ∑ p ∈ U, g p.1 p.2 := by
      dsimp [U, R]
      rw [Finset.sum_filter, Finset.sum_product]
    _ = ∑ d ∈ D, g d.2 (d.2+d.1) := by
      apply Finset.sum_nbij' (fun p : ℕ × ℕ => (⟨p.2-p.1, p.1⟩ : Σ _ : ℕ, ℕ))
        (fun d => (d.2, d.2+d.1))
      · rintro ⟨i, j⟩ hp
        simp only [U, R, D, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_sigma, Finset.mem_Icc] at hp ⊢
        omega
      · rintro ⟨h, k⟩ hd
        simp only [U, R, D, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_sigma, Finset.mem_Icc] at hd ⊢
        omega
      · rintro ⟨i, j⟩ hu
        have hij : i < j := by
          have h2 := (Finset.mem_filter.mp hu).2
          simpa using h2
        change (i, i+(j-i)) = (i, j)
        rw [show i+(j-i) = j by omega]
      · rintro ⟨h, k⟩ hk
        change (⟨k+h-k, k⟩ : Σ _ : ℕ, ℕ) = ⟨h, k⟩
        rw [show k+h-k = h by omega]
      · rintro ⟨i, j⟩ hu
        have hij : i < j := by
          have h2 := (Finset.mem_filter.mp hu).2
          simpa using h2
        change g i j = g i (i+(j-i))
        rw [show i+(j-i) = j by omega]
    _ = _ := by
      rw [Finset.sum_sigma]

private theorem pk_squareLags (n : ℕ) (g : ℕ → ℕ → ℝ) (hsym : ∀ i j, g i j = g j i) :
    (∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1), g i j) =
      (∑ i ∈ Finset.range (n+1), g i i) +
      2*(∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.range (n+1-h), g k (k+h)) := by
  let R := Finset.range (n+1)
  let up := fun i j => if i < j then g i j else 0
  let diag := fun i j => if i = j then g i i else 0
  have split (i j : ℕ) : g i j = diag i j + up i j + up j i := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [diag, up, hij, ne_of_lt hij, not_lt_of_ge hij.le]
    · simp [diag, up]
    · simp [diag, up, hji, ne_of_gt hji, not_lt_of_ge hji.le, hsym i j]
  have hd : (∑ i ∈ R, ∑ j ∈ R, diag i j) = ∑ i ∈ R, g i i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [diag, hi]
  have hu : (∑ i ∈ R, ∑ j ∈ R, up j i) = ∑ i ∈ R, ∑ j ∈ R, up i j := Finset.sum_comm
  calc
    _ = ∑ i ∈ R, ∑ j ∈ R, (diag i j + up i j + up j i) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => split i j
    _ = (∑ i ∈ R, g i i) + 2*(∑ i ∈ R, ∑ j ∈ R, up i j) := by
      simp only [Finset.sum_add_distrib, hd, hu]
      ring
    _ = _ := by rw [show (∑ i ∈ R, ∑ j ∈ R, up i j) = _ from pk_upperTriangleLags n g]

noncomputable section

private def pkAngle (t : ℝ) (k : ℕ) : ℝ := 2*Real.pi*((k:ℝ)*t)

private def pkPair (a : ℕ → ℝ) (t : ℝ) (i j : ℕ) : ℝ :=
  a i * a j * Real.cos (pkAngle t j - pkAngle t i)

end

theorem Conjectures.Goldbach.PacketLagEnergyIdentity :
let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; let V := fun (n h : ℕ) => intervalIntegral ((B n).indicator (fun t => Real.cos (2*Real.pi*(h:ℝ)*t))) (0:ℝ) 1 MeasureTheory.volume; let A := fun (n h : ℕ) (a : ℕ → ℝ) => ∑ k ∈ Finset.range (n+1-h), a k * a (k+h); let model := fun k : ℕ => if Nat.Coprime k 30 then (30:ℝ)/8 else 0; let short := fun (n : ℕ) (a : ℕ → ℝ) => A n 0 a * V n 0 + 2*(∑ h ∈ Finset.Icc 1 (min n ((L n)^2)), A n h a * V n h); let long := fun (n : ℕ) (a : ℕ → ℝ) => 2*(∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h); ∀ (n : ℕ) (a : ℕ → ℝ), U n a = short n a + long n a
:= by
  intro w E S Q arcs low high I L K B U V A model short long n a
  have hArcs : MeasurableSet (arcs n) := by
    have hset : arcs n = ⋃ q : ℕ, ⋃ c : ℕ,
        ({t : ℝ | 1 ≤ q ∧ q ≤ Q n ∧ c ≤ q ∧ Nat.Coprime c q} ∩
          {t : ℝ | |t - (c:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}) := by
      ext t
      simp only [arcs, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨q, c, h1, h2, h3, h4, h5⟩
        exact ⟨q, c, ⟨h1, h2, h3, h4⟩, h5⟩
      · rintro ⟨q, c, ⟨h1, h2, h3, h4⟩, h5⟩
        exact ⟨q, c, h1, h2, h3, h4, h5⟩
    rw [hset]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun c => ?_
    refine (MeasurableSet.const _).inter ?_
    exact measurableSet_le (by fun_prop) (by fun_prop)
  have hK : Continuous (K n) := by
    simp only [K]
    fun_prop
  have hB : MeasurableSet (B n) := by
    have hset : B n = (arcs n)ᶜ ∩ {t : ℝ | (1:ℝ)/2 < K n t} := by
      ext t
      simp only [B, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    rw [hset]
    exact hArcs.compl.inter
      (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)/2)) hK).measurableSet
  have hpt (t : ℝ) : ‖S n a t‖^2 = A n 0 a +
      2*∑ h ∈ Finset.Icc 1 n, A n h a * Real.cos (2*Real.pi*(h:ℝ)*t) := by
    have hsym (i j : ℕ) : pkPair a t i j = pkPair a t j i := by
      simp only [pkPair]
      rw [← Real.cos_neg (pkAngle t i - pkAngle t j), neg_sub]
      ring
    calc
      ‖S n a t‖^2 = (∑ k ∈ Finset.range (n+1), a k * Real.cos (pkAngle t k))^2 +
          (∑ k ∈ Finset.range (n+1), a k * Real.sin (pkAngle t k))^2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [S, E, Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
          Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, pkAngle, pow_two]
      _ = ∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1), pkPair a t i j := by
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [pkPair, Real.cos_sub]
        ring
      _ = A n 0 a + 2*∑ h ∈ Finset.Icc 1 n, A n h a * Real.cos (2*Real.pi*(h:ℝ)*t) := by
        rw [pk_squareLags n (pkPair a t) hsym]
        have hd : (∑ i ∈ Finset.range (n+1), pkPair a t i i) = A n 0 a := by
          simp [pkPair, A]
        have hsum : (∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.range (n+1-h), pkPair a t k (k+h))
            = ∑ h ∈ Finset.Icc 1 n, A n h a * Real.cos (2*Real.pi*(h:ℝ)*t) := by
          apply Finset.sum_congr rfl
          intro h _
          simp only [A]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          simp only [pkPair]
          have hang : pkAngle t (k+h) - pkAngle t k = 2*Real.pi*(h:ℝ)*t := by
            simp only [pkAngle]
            push_cast
            ring
          rw [hang]
        rw [hd, hsum]
  let f := fun (h : ℕ) => (B n).indicator (fun t : ℝ => Real.cos (2*Real.pi*(h:ℝ)*t))
  let cA := fun h : ℕ => A n h a
  let H := Finset.Icc 1 n
  have hi (h : ℕ) : IntervalIntegrable (f h) MeasureTheory.volume (0:ℝ) 1 := by
    have hc : Continuous (fun t : ℝ => Real.cos (2*Real.pi*(h:ℝ)*t)) := by fun_prop
    have h1 : MeasureTheory.IntegrableOn ((B n).indicator (fun t : ℝ => Real.cos (2*Real.pi*(h:ℝ)*t)))
        (Set.Ioc (0:ℝ) 1) MeasureTheory.volume := by
      have h2 := hc.intervalIntegrable (μ := MeasureTheory.volume) 0 1
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h2
      exact h2.indicator hB
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact h1
  have hiA (h : ℕ) : IntervalIntegrable (fun t => cA h * f h t) MeasureTheory.volume (0:ℝ) 1 :=
    (hi h).const_mul (cA h)
  have hs : IntervalIntegrable (fun t => ∑ h ∈ H, cA h * f h t)
      MeasureTheory.volume (0:ℝ) 1 := by
    have heq : (fun t => ∑ h ∈ H, cA h * f h t) = ∑ h ∈ H, (fun t => cA h * f h t) := by
      funext t
      simp
    rw [heq]
    exact IntervalIntegrable.sum H (fun h _ => hiA h)
  have hident : (B n).indicator (fun t => ‖S n a t‖^2) =
      fun t => cA 0 * f 0 t + 2*∑ h ∈ H, cA h * f h t := by
    funext t
    by_cases ht : t ∈ B n
    · rw [Set.indicator_of_mem ht]
      simp only [f, Set.indicator_of_mem ht, cA, H]
      rw [hpt t]
      simp
    · have hz (h : ℕ) : f h t = 0 := by
        simp only [f, Set.indicator_of_notMem ht]
      rw [Set.indicator_of_notMem ht]
      simp [hz]
  have hU : U n a = intervalIntegral (fun t => cA 0 * f 0 t + 2*∑ h ∈ H, cA h * f h t)
      (0:ℝ) 1 MeasureTheory.volume := by
    show intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1
      MeasureTheory.volume = _
    rw [hident]
  have hfs : intervalIntegral (fun x => ∑ h ∈ H, cA h * f h x) (0:ℝ) 1
      MeasureTheory.volume = ∑ h ∈ H, intervalIntegral (fun t => cA h * f h t) (0:ℝ) 1
      MeasureTheory.volume :=
    intervalIntegral.integral_finsetSum (fun h _ => hiA h)
  have hV (h : ℕ) : intervalIntegral (f h) (0:ℝ) 1 MeasureTheory.volume = V n h := rfl
  have hsplit : H = Finset.Icc 1 (min n ((L n)^2)) ∪ Finset.Icc ((L n)^2+1) n := by
    ext h
    simp only [H, Finset.mem_union, Finset.mem_Icc]
    omega
  have hdis : Disjoint (Finset.Icc 1 (min n ((L n)^2))) (Finset.Icc ((L n)^2+1) n) := by
    rw [Finset.disjoint_left]
    intro h ha hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  rw [hU, intervalIntegral.integral_add (hiA 0) (hs.const_mul 2)]
  simp only [intervalIntegral.integral_const_mul]
  rw [hfs]
  simp only [intervalIntegral.integral_const_mul, hV]
  rw [hsplit, Finset.sum_union hdis]
  simp only [cA, short, long]
  ring
