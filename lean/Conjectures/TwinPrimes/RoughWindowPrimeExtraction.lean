import Mathlib

namespace Conjectures.TwinPrimes.RoughWindowPrimeExtraction_aux

theorem trichotomy {X p : ℕ} (hX : 4096 ≤ X) (hlo : X < p) (hhi : p ≤ 2 * X)
    (hrough : Nat.sqrt X / 2 ≤ (p + 2).minFac) :
    (p + 2).Prime
      ∨ ((Nat.sqrt (p + 2)).Prime ∧ p + 2 = (Nat.sqrt (p + 2)) ^ 2)
      ∨ (∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r < s ∧ Nat.sqrt X / 2 ≤ r
            ∧ r ≤ Nat.sqrt (2 * X + 2) ∧ p + 2 = r * s) := by
  let N : ℕ := p + 2
  let q : ℕ := N.minFac
  let m : ℕ := N / q
  have hNpos : 0 < N := by
    dsimp [N]
    omega
  have hNne_one : N ≠ 1 := by
    dsimp [N]
    omega
  have hNupper : N ≤ 2 * X + 2 := by
    dsimp [N]
    omega
  have hqprime : q.Prime := by
    simpa [q] using (Nat.minFac_prime hNne_one)
  have hqdvd : q ∣ N := by
    simpa [q] using (Nat.minFac_dvd N)
  have hrough_q : Nat.sqrt X / 2 ≤ q := by
    simpa [N, q] using hrough
  by_cases hNprime : N.Prime
  · exact Or.inl (by simpa [N] using hNprime)
  have hqle_m : q ≤ m := by
    simpa [q, m] using (Nat.minFac_le_div hNpos hNprime)
  have hNfactor : N = q * m := by
    calc
      N = m * q := (Nat.div_mul_cancel hqdvd).symm
      _ = q * m := mul_comm _ _
  rcases Nat.eq_or_lt_of_le hqle_m with hmq | hqm
  · have hNsquare : N = q ^ 2 := by
      calc
        N = q * m := hNfactor
        _ = q * q := by rw [hmq]
        _ = q ^ 2 := by rw [pow_two]
    have hsqrtN : Nat.sqrt (p + 2) = q := by
      change Nat.sqrt N = q
      rw [hNsquare, Nat.sqrt_eq']
    exact Or.inr (Or.inl ⟨by simpa [hsqrtN] using hqprime,
      by simpa [N, hsqrtN] using hNsquare⟩)
  · by_cases hmprime : m.Prime
    · have hq_sq_le_N : q ^ 2 ≤ N := by
        calc
          q ^ 2 = q * q := by rw [pow_two]
          _ ≤ q * m := Nat.mul_le_mul_left q hqm.le
          _ = N := hNfactor.symm
      have hq_le_sqrt : q ≤ Nat.sqrt (2 * X + 2) := by
        apply (Nat.le_sqrt').2
        exact hq_sq_le_N.trans hNupper
      exact Or.inr (Or.inr ⟨q, m, hqprime, hmprime, hqm, hrough_q, hq_le_sqrt,
        hNfactor⟩)
    · exfalso
      have hm_two : 2 ≤ m := hqprime.two_le.trans hqm.le
      have hm_ne_one : m ≠ 1 := by omega
      let r : ℕ := m.minFac
      have hrprime : r.Prime := by
        simpa [r] using (Nat.minFac_prime hm_ne_one)
      have hrdvd_m : r ∣ m := by
        simpa [r] using (Nat.minFac_dvd m)
      have hmdvd_N : m ∣ N := ⟨q, hNfactor.trans (mul_comm q m)⟩
      have hrdvd_N : r ∣ N := Nat.dvd_trans hrdvd_m hmdvd_N
      have hqr : q ≤ r := by
        have h : N.minFac ≤ r := Nat.minFac_le_of_dvd hrprime.two_le hrdvd_N
        simpa [q] using h
      have hr_sq_le_m : r ^ 2 ≤ m := by
        simpa [r] using (Nat.minFac_sq_le_self (by omega : 0 < m) hmprime)
      have hq_sq_le_r_sq : q ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hqr 2
      have hq_cube_le_N : q ^ 3 ≤ N := by
        calc
          q ^ 3 = q * q ^ 2 := by ring
          _ ≤ q * r ^ 2 := Nat.mul_le_mul_left q hq_sq_le_r_sq
          _ ≤ q * m := Nat.mul_le_mul_left q hr_sq_le_m
          _ = N := hNfactor.symm
      have hsqrt64 : 64 ≤ Nat.sqrt X := (Nat.le_sqrt').2 (by omega)
      have hq32 : 32 ≤ q := by omega
      have hsqrt_upper : Nat.sqrt X ≤ 2 * q + 1 := by omega
      have hNbound : N ≤ 2 * (2 * q + 2) ^ 2 := by
        calc
          N ≤ 2 * X + 2 := hNupper
          _ ≤ 2 * (Nat.sqrt X + 1) ^ 2 := by
            have h : X < (Nat.sqrt X + 1) ^ 2 := by
              simpa [Nat.succ_eq_add_one] using (Nat.lt_succ_sqrt' X)
            omega
          _ ≤ 2 * (2 * q + 2) ^ 2 :=
            Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega) 2)
      have hbase : 2 * q + 2 ≤ 3 * q := by omega
      have hsmall : 2 * (2 * q + 2) ^ 2 ≤ 18 * q ^ 2 := by
        calc
          2 * (2 * q + 2) ^ 2 ≤ 2 * (3 * q) ^ 2 :=
            Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hbase 2)
          _ = 18 * q ^ 2 := by ring
      have hq_sq_pos : 0 < q ^ 2 := by positivity
      have hsmall_lt : 18 * q ^ 2 < 32 * q ^ 2 := by omega
      have hleft : 32 * q ^ 2 ≤ q ^ 3 := by
        calc
          32 * q ^ 2 = q ^ 2 * 32 := by ring
          _ ≤ q ^ 2 * q := Nat.mul_le_mul_left (q ^ 2) hq32
          _ = q ^ 3 := by ring
      omega

theorem sum_union_le {s t : Finset ℕ} {f : ℕ → ℝ} (hf : ∀ i ∈ s ∪ t, 0 ≤ f i) :
    (s ∪ t).sum f ≤ s.sum f + t.sum f := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have hnn : 0 ≤ (s ∩ t).sum f :=
    Finset.sum_nonneg fun i hi => hf i (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hi).1))
  linarith

end Conjectures.TwinPrimes.RoughWindowPrimeExtraction_aux

open Conjectures.TwinPrimes.RoughWindowPrimeExtraction_aux

theorem Conjectures.TwinPrimes.RoughWindowPrimeExtraction :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let z := fun (X : ℕ) => Nat.sqrt X / 2; let R := fun (X : ℕ) => ((w X).filter (fun p => p.Prime ∧ z X ≤ (p+2).minFac)); let T := fun (X : ℕ) => ((w X).filter (fun p => p.Prime ∧ (p+2).Prime)); let Q := fun (X : ℕ) => ((w X).filter (fun p => p.Prime ∧ (Nat.sqrt (p+2)).Prime ∧ p+2=(Nat.sqrt (p+2))^2)); let S := fun (X : ℕ) => @Finset.filter ℕ (fun p => p.Prime ∧ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r < s ∧ Nat.sqrt X/2 ≤ r ∧ r ≤ Nat.sqrt (2*X+2) ∧ p+2=r*s) (fun _ => Classical.propDecidable _) (w X); let L := fun (p : ℕ) => Real.log p * Real.log (p+2); ∀ (X : ℕ) (M E F : ℝ), 4096 ≤ X → M ≤ (R X).sum L → (Q X).sum L ≤ E → (S X).sum L ≤ F → M-E-F ≤ (T X).sum L := by
  intro w z R T Q S L X M E F hX hM hE hF
  have hSsub : S X ⊆ w X := by
    apply @Finset.filter_subset ℕ
      (fun p => p.Prime ∧ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r < s ∧ Nat.sqrt X / 2 ≤ r
        ∧ r ≤ Nat.sqrt (2 * X + 2) ∧ p + 2 = r * s)
      (fun _ => Classical.propDecidable _) (w X)
  have hSmem : ∀ (p : ℕ), p ∈ w X → p.Prime →
      (∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r < s ∧ Nat.sqrt X / 2 ≤ r
        ∧ r ≤ Nat.sqrt (2 * X + 2) ∧ p + 2 = r * s) → p ∈ S X := by
    intro p hpw hpp hex
    exact (@Finset.mem_filter ℕ
      (fun p => p.Prime ∧ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r < s ∧ Nat.sqrt X / 2 ≤ r
        ∧ r ≤ Nat.sqrt (2 * X + 2) ∧ p + 2 = r * s)
      (fun _ => Classical.propDecidable _) (w X) p).mpr ⟨hpw, hpp, hex⟩
  have hLnn : ∀ i ∈ w X, (0 : ℝ) ≤ L i := by
    intro i hi
    have hi' : i ∈ Finset.range (2 * X + 1) ∧ (X < i ∧ 50 * i < 51 * X) :=
      Finset.mem_filter.mp hi
    have h1 : (1 : ℝ) ≤ (i : ℝ) := by
      have h : 1 ≤ i := by have := hi'.2.1; omega
      exact_mod_cast h
    have h2 : (1 : ℝ) ≤ (i : ℝ) + 2 := by linarith
    dsimp only [L]
    exact mul_nonneg (Real.log_nonneg h1) (Real.log_nonneg h2)
  have hLnn2 : ∀ i ∈ T X ∪ Q X ∪ S X, (0 : ℝ) ≤ L i := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rcases Finset.mem_union.mp hi with hi | hi
      · exact hLnn i (Finset.filter_subset _ _ hi)
      · exact hLnn i (Finset.filter_subset _ _ hi)
    · exact hLnn i (hSsub hi)
  have hsub : R X ⊆ T X ∪ Q X ∪ S X := by
    intro p hp
    have hpR : p ∈ w X ∧ p.Prime ∧ z X ≤ (p + 2).minFac := Finset.mem_filter.mp hp
    obtain ⟨hpw, hpp, hrough⟩ := hpR
    have hpw' : p ∈ Finset.range (2 * X + 1) ∧ (X < p ∧ 50 * p < 51 * X) :=
      Finset.mem_filter.mp hpw
    have hlo : X < p := hpw'.2.1
    have hhi : p ≤ 2 * X := by
      have h := Finset.mem_range.mp hpw'.1
      omega
    have hrough' : Nat.sqrt X / 2 ≤ (p + 2).minFac := hrough
    rcases trichotomy hX hlo hhi hrough' with hT | hQ | hS
    · refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ?_)))
      exact Finset.mem_filter.mpr ⟨hpw, hpp, hT⟩
    · refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ?_)))
      exact Finset.mem_filter.mpr ⟨hpw, hpp, hQ⟩
    · refine Finset.mem_union.mpr (Or.inr ?_)
      exact hSmem p hpw hpp hS
  have hkey : (R X).sum L ≤ (T X).sum L + (Q X).sum L + (S X).sum L := by
    calc (R X).sum L ≤ (T X ∪ Q X ∪ S X).sum L :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hLnn2 i hi)
      _ ≤ (T X ∪ Q X).sum L + (S X).sum L :=
          sum_union_le (s := T X ∪ Q X) (t := S X) (f := L) (fun i hi => hLnn2 i hi)
      _ ≤ (T X).sum L + (Q X).sum L + (S X).sum L := by
          have h := sum_union_le (s := T X) (t := Q X) (f := L)
            (fun i hi => hLnn2 i (show i ∈ T X ∪ Q X ∪ S X from
              Finset.mem_union.mpr (Or.inl (show i ∈ T X ∪ Q X from hi))))
          linarith
  linarith
