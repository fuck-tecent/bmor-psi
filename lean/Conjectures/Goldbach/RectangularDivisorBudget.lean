import Mathlib

open scoped BigOperators

private lemma rect_inv_nat_nonneg {n : ℕ} (h : 1 ≤ n) : (0:ℝ) ≤ (n:ℝ)⁻¹ := by
  have hn : (0:ℝ) < (n:ℝ) := by
    have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast h
    linarith
  exact inv_nonneg.mpr (le_of_lt hn)

private lemma rect_gcd_divisors_eq_filter {A D u v : ℕ}
    (hu : u ∈ Finset.Icc 1 A) (hv : v ∈ Finset.Icc 1 D) :
    (u.gcd v).divisors = (Finset.Icc 1 (min A D)).filter (fun q => q ∣ u ∧ q ∣ v) := by
  have hu1 : 1 ≤ u := (Finset.mem_Icc.mp hu).1
  have huA : u ≤ A := (Finset.mem_Icc.mp hu).2
  have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1
  have hvD : v ≤ D := (Finset.mem_Icc.mp hv).2
  have hupos : 0 < u := by omega
  have hvpos : 0 < v := by omega
  ext q
  rw [Nat.mem_divisors, Nat.dvd_gcd_iff, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hqu, hqv⟩, -⟩
    have hqpos : 0 < q := Nat.pos_of_dvd_of_pos hqu hupos
    have hq1 : 1 ≤ q := by omega
    have hqA : q ≤ A := le_trans (Nat.le_of_dvd hupos hqu) huA
    have hqD : q ≤ D := le_trans (Nat.le_of_dvd hvpos hqv) hvD
    exact ⟨⟨hq1, le_min hqA hqD⟩, hqu, hqv⟩
  · rintro ⟨⟨hq1, -⟩, hqu, hqv⟩
    have hg : 0 < u.gcd v := Nat.gcd_pos_of_pos_left v hupos
    exact ⟨⟨hqu, hqv⟩, Nat.pos_iff_ne_zero.mp hg⟩

private lemma rect_sum_multiples_inv_le (q A : ℕ) (hq : 1 ≤ q) :
    (∑ u ∈ (Finset.Icc 1 A).filter (fun u => q ∣ u), (u:ℝ)⁻¹)
      ≤ (q:ℝ)⁻¹ * ∑ u ∈ Finset.Icc 1 A, (u:ℝ)⁻¹ := by
  set Q : Finset ℕ := (Finset.Icc 1 A).filter (fun u => q ∣ u) with hQ
  have hval : ∀ u ∈ Q, (u:ℝ)⁻¹ = (q:ℝ)⁻¹ * ((u / q : ℕ) : ℝ)⁻¹ := by
    intro u hu
    have hdvd : q ∣ u := (Finset.mem_filter.mp hu).2
    have heq : q * (u / q) = u := Nat.mul_div_cancel' hdvd
    have hcast : (u:ℝ) = (q:ℝ) * ((u / q : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, heq]
    rw [hcast, mul_inv]
  have hinj : Set.InjOn (fun u : ℕ => u / q) (↑Q : Set ℕ) := by
    intro u hu v hv huv
    have huQ : u ∈ Q := by simpa using hu
    have hvQ : v ∈ Q := by simpa using hv
    have hdu : q ∣ u := (Finset.mem_filter.mp huQ).2
    have hdv : q ∣ v := (Finset.mem_filter.mp hvQ).2
    have h1 : q * (u / q) = u := Nat.mul_div_cancel' hdu
    have h2 : q * (v / q) = v := Nat.mul_div_cancel' hdv
    have huv' : u / q = v / q := huv
    rw [← h1, ← h2, huv']
  have himage : Q.image (fun u : ℕ => u / q) ⊆ Finset.Icc 1 A := by
    intro k hk
    obtain ⟨u, huQ, hk⟩ := Finset.mem_image.mp hk
    have huI : u ∈ Finset.Icc 1 A := (Finset.mem_filter.mp huQ).1
    have hdu : q ∣ u := (Finset.mem_filter.mp huQ).2
    have hu1 : 1 ≤ u := (Finset.mem_Icc.mp huI).1
    have huA : u ≤ A := (Finset.mem_Icc.mp huI).2
    have heq : q * (u / q) = u := Nat.mul_div_cancel' hdu
    have hkne : u / q ≠ 0 := by
      intro h0
      rw [h0, Nat.mul_zero] at heq
      omega
    have hk1 : 1 ≤ u / q := Nat.one_le_iff_ne_zero.mpr hkne
    have hkA : u / q ≤ A := le_trans (Nat.div_le_self u q) huA
    rw [← hk]
    exact Finset.mem_Icc.mpr ⟨hk1, hkA⟩
  have hsub : (∑ k ∈ Q.image (fun u : ℕ => u / q), (k:ℝ)⁻¹)
      ≤ ∑ k ∈ Finset.Icc 1 A, (k:ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg himage
    intro k hk _
    exact rect_inv_nat_nonneg (Finset.mem_Icc.mp hk).1
  calc (∑ u ∈ Q, (u:ℝ)⁻¹)
      = ∑ u ∈ Q, (q:ℝ)⁻¹ * ((u / q : ℕ) : ℝ)⁻¹ := Finset.sum_congr rfl hval
    _ = (q:ℝ)⁻¹ * ∑ u ∈ Q, ((u / q : ℕ) : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ = (q:ℝ)⁻¹ * ∑ k ∈ Q.image (fun u : ℕ => u / q), (k:ℝ)⁻¹ := by
          rw [Finset.sum_image]
          exact hinj
    _ ≤ (q:ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 A, (k:ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hsub (rect_inv_nat_nonneg hq)

theorem Conjectures.Goldbach.RectangularDivisorBudget :
    ∀ (A D : ℕ) (T : ℕ→ℝ), (∀ q,0≤T q) → (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D, ((∑ q ∈ (u.gcd v).divisors,T q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹)) ≤ (∑ q ∈ Finset.Icc 1 (min A D),T q*(q:ℝ)⁻¹^2)* (∑ u ∈ Finset.Icc 1 A,(u:ℝ)⁻¹)*(∑ v ∈ Finset.Icc 1 D,(v:ℝ)⁻¹) := by
  intro A D T hT
  set S : Finset ℕ := Finset.Icc 1 (min A D) with hS
  have hdiv_eq : ∀ u ∈ Finset.Icc 1 A, ∀ v ∈ Finset.Icc 1 D,
      (∑ q ∈ (u.gcd v).divisors, T q)
        = ∑ q ∈ S, (if q ∣ u ∧ q ∣ v then T q else 0) := by
    intro u hu v hv
    rw [rect_gcd_divisors_eq_filter hu hv, ← hS, Finset.sum_filter]
  have hswap : (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
        ((∑ q ∈ (u.gcd v).divisors, T q) * (u:ℝ)⁻¹ * (v:ℝ)⁻¹))
      = ∑ q ∈ S, T q * (∑ u ∈ (Finset.Icc 1 A).filter (fun u => q ∣ u), (u:ℝ)⁻¹)
          * (∑ v ∈ (Finset.Icc 1 D).filter (fun v => q ∣ v), (v:ℝ)⁻¹) := by
    calc (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
          ((∑ q ∈ (u.gcd v).divisors, T q) * (u:ℝ)⁻¹ * (v:ℝ)⁻¹))
        = ∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D, ∑ q ∈ S,
            ((if q ∣ u ∧ q ∣ v then T q else 0) * (u:ℝ)⁻¹ * (v:ℝ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro v hv
          rw [hdiv_eq u hu v hv, Finset.sum_mul, Finset.sum_mul]
      _ = ∑ u ∈ Finset.Icc 1 A, ∑ q ∈ S, ∑ v ∈ Finset.Icc 1 D,
            ((if q ∣ u ∧ q ∣ v then T q else 0) * (u:ℝ)⁻¹ * (v:ℝ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.sum_comm]
      _ = ∑ q ∈ S, ∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
            ((if q ∣ u ∧ q ∣ v then T q else 0) * (u:ℝ)⁻¹ * (v:ℝ)⁻¹) := by
          rw [Finset.sum_comm]
      _ = ∑ q ∈ S, T q * (∑ u ∈ (Finset.Icc 1 A).filter (fun u => q ∣ u), (u:ℝ)⁻¹)
            * (∑ v ∈ (Finset.Icc 1 D).filter (fun v => q ∣ v), (v:ℝ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro q hq
          have key : ∀ u ∈ Finset.Icc 1 A, ∀ v ∈ Finset.Icc 1 D,
              ((if q ∣ u ∧ q ∣ v then T q else 0) * (u:ℝ)⁻¹ * (v:ℝ)⁻¹)
                = (T q * (if q ∣ u then (u:ℝ)⁻¹ else 0))
                  * (if q ∣ v then (v:ℝ)⁻¹ else 0) := by
            intro u hu v hv
            by_cases h1 : q ∣ u <;> by_cases h2 : q ∣ v <;> simp [h1, h2]
          calc ∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
                ((if q ∣ u ∧ q ∣ v then T q else 0) * (u:ℝ)⁻¹ * (v:ℝ)⁻¹)
              = ∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
                  (T q * (if q ∣ u then (u:ℝ)⁻¹ else 0))
                    * (if q ∣ v then (v:ℝ)⁻¹ else 0) := by
                apply Finset.sum_congr rfl
                intro u hu
                apply Finset.sum_congr rfl
                intro v hv
                exact key u hu v hv
            _ = (∑ u ∈ Finset.Icc 1 A, T q * (if q ∣ u then (u:ℝ)⁻¹ else 0))
                  * (∑ v ∈ Finset.Icc 1 D, (if q ∣ v then (v:ℝ)⁻¹ else 0)) := by
                rw [Finset.sum_mul_sum]
            _ = (T q * (∑ u ∈ Finset.Icc 1 A, (if q ∣ u then (u:ℝ)⁻¹ else 0)))
                  * (∑ v ∈ Finset.Icc 1 D, (if q ∣ v then (v:ℝ)⁻¹ else 0)) := by
                rw [← Finset.mul_sum]
            _ = T q * (∑ u ∈ (Finset.Icc 1 A).filter (fun u => q ∣ u), (u:ℝ)⁻¹)
                  * (∑ v ∈ (Finset.Icc 1 D).filter (fun v => q ∣ v), (v:ℝ)⁻¹) := by
                have hau : (∑ u ∈ Finset.Icc 1 A, (if q ∣ u then (u:ℝ)⁻¹ else 0))
                    = ∑ u ∈ (Finset.Icc 1 A).filter (fun u => q ∣ u), (u:ℝ)⁻¹ := by
                  rw [Finset.sum_filter]
                have hbv : (∑ v ∈ Finset.Icc 1 D, (if q ∣ v then (v:ℝ)⁻¹ else 0))
                    = ∑ v ∈ (Finset.Icc 1 D).filter (fun v => q ∣ v), (v:ℝ)⁻¹ := by
                  rw [Finset.sum_filter]
                rw [hau, hbv]
  calc (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D,
        ((∑ q ∈ (u.gcd v).divisors, T q) * (u:ℝ)⁻¹ * (v:ℝ)⁻¹))
      = ∑ q ∈ S, T q * (∑ u ∈ (Finset.Icc 1 A).filter (fun u => q ∣ u), (u:ℝ)⁻¹)
          * (∑ v ∈ (Finset.Icc 1 D).filter (fun v => q ∣ v), (v:ℝ)⁻¹) := hswap
    _ ≤ ∑ q ∈ S, T q * ((q:ℝ)⁻¹ * (∑ u ∈ Finset.Icc 1 A, (u:ℝ)⁻¹))
          * ((q:ℝ)⁻¹ * (∑ v ∈ Finset.Icc 1 D, (v:ℝ)⁻¹)) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqI : q ∈ Finset.Icc 1 (min A D) := by
          rw [hS] at hq
          exact hq
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hqI).1
        have hqinv : (0:ℝ) ≤ (q:ℝ)⁻¹ := rect_inv_nat_nonneg hq1
        have hup : (∑ u ∈ (Finset.Icc 1 A).filter (fun u => q ∣ u), (u:ℝ)⁻¹)
            ≤ (q:ℝ)⁻¹ * ∑ u ∈ Finset.Icc 1 A, (u:ℝ)⁻¹ := rect_sum_multiples_inv_le q A hq1
        have hvp : (∑ v ∈ (Finset.Icc 1 D).filter (fun v => q ∣ v), (v:ℝ)⁻¹)
            ≤ (q:ℝ)⁻¹ * ∑ v ∈ Finset.Icc 1 D, (v:ℝ)⁻¹ := rect_sum_multiples_inv_le q D hq1
        have hqu : (0:ℝ) ≤ ∑ u ∈ (Finset.Icc 1 A).filter (fun u => q ∣ u), (u:ℝ)⁻¹ := by
          apply Finset.sum_nonneg
          intro u hu
          exact rect_inv_nat_nonneg (Finset.mem_Icc.mp ((Finset.mem_filter.mp hu).1)).1
        have hqv : (0:ℝ) ≤ ∑ v ∈ (Finset.Icc 1 D).filter (fun v => q ∣ v), (v:ℝ)⁻¹ := by
          apply Finset.sum_nonneg
          intro v hv
          exact rect_inv_nat_nonneg (Finset.mem_Icc.mp ((Finset.mem_filter.mp hv).1)).1
        have hA0 : (0:ℝ) ≤ ∑ u ∈ Finset.Icc 1 A, (u:ℝ)⁻¹ := by
          apply Finset.sum_nonneg
          intro u hu
          exact rect_inv_nat_nonneg (Finset.mem_Icc.mp hu).1
        have hB0 : (0:ℝ) ≤ ∑ v ∈ Finset.Icc 1 D, (v:ℝ)⁻¹ := by
          apply Finset.sum_nonneg
          intro v hv
          exact rect_inv_nat_nonneg (Finset.mem_Icc.mp hv).1
        have hb0 : (0:ℝ) ≤ T q * ((q:ℝ)⁻¹ * (∑ u ∈ Finset.Icc 1 A, (u:ℝ)⁻¹)) :=
          mul_nonneg (hT q) (mul_nonneg hqinv hA0)
        have h1 : T q * (∑ u ∈ (Finset.Icc 1 A).filter (fun u => q ∣ u), (u:ℝ)⁻¹)
            ≤ T q * ((q:ℝ)⁻¹ * (∑ u ∈ Finset.Icc 1 A, (u:ℝ)⁻¹)) :=
          mul_le_mul (le_refl (T q)) hup hqu (hT q)
        exact mul_le_mul h1 hvp hqv hb0
    _ = (∑ q ∈ S, T q * (q:ℝ)⁻¹^2) * (∑ u ∈ Finset.Icc 1 A, (u:ℝ)⁻¹)
          * (∑ v ∈ Finset.Icc 1 D, (v:ℝ)⁻¹) := by
        have hterm : ∀ q ∈ S, T q * ((q:ℝ)⁻¹ * (∑ u ∈ Finset.Icc 1 A, (u:ℝ)⁻¹))
              * ((q:ℝ)⁻¹ * (∑ v ∈ Finset.Icc 1 D, (v:ℝ)⁻¹))
            = T q * (q:ℝ)⁻¹^2 * (∑ u ∈ Finset.Icc 1 A, (u:ℝ)⁻¹)
              * (∑ v ∈ Finset.Icc 1 D, (v:ℝ)⁻¹) := by
          intro q hq
          ring
        rw [Finset.sum_congr rfl hterm]
        rw [Finset.sum_mul, Finset.sum_mul]
