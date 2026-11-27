import Mathlib

namespace Conjectures.QuadraticPrimes.SieveFinalSign_aux

open Finset

lemma mem_wheel_primes {z q : ℕ} :
    q ∈ (Finset.Icc 3 z).filter (fun p => Nat.Prime p) ↔ Nat.Prime q ∧ 3 ≤ q ∧ q ≤ z := by
  constructor
  · intro h
    have h' := Finset.mem_filter.mp h
    exact ⟨h'.2, (Finset.mem_Icc.mp h'.1).1, (Finset.mem_Icc.mp h'.1).2⟩
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h.2.1, h.2.2⟩, h.1⟩

lemma dvd_wheel {z q : ℕ} (h : q ∈ (Finset.Icc 3 z).filter (fun p => Nat.Prime p)) :
    q ∣ ∏ p ∈ (Finset.Icc 3 z).filter (fun p => Nat.Prime p), p :=
  Finset.dvd_prod_of_mem (fun p => p) h

lemma coprime_wheel_of_lt {p z : ℕ} (hp : Nat.Prime p) (hzp : z < p) :
    Nat.Coprime p (∏ q ∈ (Finset.Icc 3 z).filter (fun r => Nat.Prime r), q) := by
  refine Nat.coprime_prod_right_iff.mpr (fun q hq => ?_)
  obtain ⟨hq', _, hqz⟩ := mem_wheel_primes.mp hq
  exact (Nat.coprime_primes hp hq').mpr (by omega)

lemma two_not_dvd_f (k : ℕ) : ¬ (2 ∣ 4 * k ^ 2 + 1) := by
  intro h
  have h0 : (4 * k ^ 2 + 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  have h1 : (4 * k ^ 2 + 1) % 2 = 1 := by
    rw [Nat.add_mod, Nat.mul_mod]
    simp
  omega

lemma prime_factor_gt {n z : ℕ} (hodd : ¬ (2 ∣ n))
    (hcop : Nat.Coprime n (∏ q ∈ (Finset.Icc 3 z).filter (fun r => Nat.Prime r), q))
    {q : ℕ} (hq : q.Prime) (hqn : q ∣ n) : z < q := by
  by_contra hcon
  push_neg at hcon
  have hq3 : 3 ≤ q := by
    by_contra hc
    push_neg at hc
    have hq2' := hq.two_le
    have hq2 : q = 2 := by omega
    exact hodd (by simpa [hq2] using hqn)
  have hmem : q ∈ (Finset.Icc 3 z).filter (fun r => Nat.Prime r) :=
    mem_wheel_primes.mpr ⟨hq, hq3, hcon⟩
  have hdiv : q ∣ Nat.gcd n (∏ r ∈ (Finset.Icc 3 z).filter (fun r => Nat.Prime r), r) :=
    Nat.dvd_gcd hqn (dvd_wheel hmem)
  have hcop' : Nat.gcd n (∏ r ∈ (Finset.Icc 3 z).filter (fun r => Nat.Prime r), r) = 1 := hcop
  rw [hcop'] at hdiv
  have hq1 : q = 1 := Nat.dvd_one.mp hdiv
  have := hq.two_le
  omega

lemma f_not_sq {k : ℕ} (hk : 1 ≤ k) (m : ℕ) : 4 * k ^ 2 + 1 ≠ m ^ 2 := by
  intro h
  have hmm : m * m = 4 * (k * k) + 1 := by
    calc m * m = m ^ 2 := (pow_two m).symm
      _ = 4 * k ^ 2 + 1 := h.symm
      _ = 4 * (k * k) + 1 := by ring
  rcases Nat.lt_or_ge m (2 * k + 1) with hlt | hle
  · have h1 : m * m ≤ (2 * k) * (2 * k) :=
      Nat.mul_self_le_mul_self (by omega : m ≤ 2 * k)
    have e : (2 * k) * (2 * k) = 4 * (k * k) := by ring
    rw [hmm, e] at h1
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h1)
  · have h2 : (2 * k + 1) * (2 * k + 1) ≤ m * m := Nat.mul_self_le_mul_self hle
    have e : (2 * k + 1) * (2 * k + 1) = 4 * (k * k) + (4 * k + 1) := by ring
    rw [hmm, e] at h2
    have h3 : 4 * k + 1 ≤ 1 := Nat.add_le_add_iff_left.mp h2
    omega

lemma classify {n z : ℕ} (hz : 1 ≤ z) (hn : 2 ≤ n)
    (hfac : ∀ q : ℕ, q.Prime → q ∣ n → z < q) (hsmall : n ≤ z ^ 3)
    (hsq : ∀ t : ℕ, n ≠ t ^ 2) :
    n.Prime ∨ (¬ n.Prime ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q) := by
  by_cases hpr : n.Prime
  · exact Or.inl hpr
  refine Or.inr ⟨hpr, ?_⟩
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hpz : z < p := hfac p hp hpn
  obtain ⟨m, hpm⟩ : ∃ m, n = p * m :=
    ⟨n / p, (Nat.div_mul_cancel hpn).symm.trans (mul_comm _ _)⟩
  have hmn : m ∣ n := ⟨p, hpm.trans (mul_comm p m)⟩
  have hm2 : 2 ≤ m := by
    by_contra hc
    push_neg at hc
    have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with rfl | rfl
    · rw [hpm] at hn
      simp at hn
    · exact hpr (by rw [hpm]; simpa using hp)
  have hmlt : m < z ^ 2 := by
    by_contra hc
    push_neg at hc
    have h1 : (z + 1) * z ^ 2 ≤ p * m := Nat.mul_le_mul (by omega : z + 1 ≤ p) hc
    have h2 : z ^ 3 < (z + 1) * z ^ 2 := by
      have e : (z + 1) * z ^ 2 = z ^ 3 + z ^ 2 := by ring
      rw [e]
      exact Nat.lt_add_of_pos_right (by positivity)
    have h3 : p * m ≤ z ^ 3 := by rw [← hpm]; exact hsmall
    exact absurd (lt_of_le_of_lt h3 (lt_of_lt_of_le h2 h1)) (lt_irrefl _)
  have hmprime : m.Prime := by
    by_contra hmnp
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    have hqz : z < q := hfac q hq (dvd_trans hqm hmn)
    obtain ⟨m', hm'⟩ : ∃ m', m = q * m' :=
      ⟨m / q, (Nat.div_mul_cancel hqm).symm.trans (mul_comm _ _)⟩
    have hm'n : m' ∣ m := ⟨q, hm'.trans (mul_comm q m')⟩
    have hm'2 : 2 ≤ m' := by
      by_contra hc
      push_neg at hc
      have hm'01 : m' = 0 ∨ m' = 1 := by omega
      rcases hm'01 with rfl | rfl
      · rw [hm'] at hm2
        simp at hm2
      · exact hmnp (by rw [hm']; simpa using hq)
    obtain ⟨r, hr, hrm'⟩ := Nat.exists_prime_and_dvd (by omega : m' ≠ 1)
    have hrz : z < r := hfac r hr (dvd_trans (dvd_trans hrm' hm'n) hmn)
    have hm'z : z < m' := lt_of_lt_of_le hrz (Nat.le_of_dvd (by omega : 0 < m') hrm')
    have hcontr : z ^ 2 < m := by
      calc z ^ 2 = z * z := by ring
        _ < q * m' := Nat.mul_lt_mul_of_lt_of_lt hqz hm'z
        _ = m := hm'.symm
    exact absurd hcontr (not_lt.mpr (Nat.le_of_lt hmlt))
  have hpne : p ≠ m := by
    intro heq
    exact hsq p (by rw [hpm, heq]; ring)
  exact ⟨p, m, hp, hmprime, hpne, hpm⟩

lemma sum_weight_eq {B : Finset ℕ} {f : ℕ → ℕ} {W : ℕ}
    (hsub : ∀ k ∈ B, (f k).Prime → Nat.Coprime (f k) W)
    (hzero : ∀ k ∈ B, Nat.Coprime (f k) W → ¬ (f k).Prime →
      ArithmeticFunction.moebius (f k) = 1) :
    (∑ k ∈ B.filter (fun k => (f k).Prime), Real.log ((f k : ℕ) : ℝ))
      = ∑ k ∈ B.filter (fun k => Nat.Coprime (f k) W),
          (1 - (ArithmeticFunction.moebius (f k) : ℝ)) / 2 * Real.log ((f k : ℕ) : ℝ) := by
  classical
  have hsub' : B.filter (fun k => (f k).Prime) ⊆ B.filter (fun k => Nat.Coprime (f k) W) := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨hk'.1, hsub k hk'.1 hk'.2⟩
  have hpt : ∀ k ∈ B.filter (fun k => (f k).Prime),
      Real.log ((f k : ℕ) : ℝ)
        = (1 - (ArithmeticFunction.moebius (f k) : ℝ)) / 2 * Real.log ((f k : ℕ) : ℝ) := by
    intro k hk
    have hkp : (f k).Prime := (Finset.mem_filter.mp hk).2
    rw [ArithmeticFunction.moebius_apply_prime hkp]
    push_cast
    ring
  calc (∑ k ∈ B.filter (fun k => (f k).Prime), Real.log ((f k : ℕ) : ℝ))
      = ∑ k ∈ B.filter (fun k => (f k).Prime),
          (1 - (ArithmeticFunction.moebius (f k) : ℝ)) / 2 * Real.log ((f k : ℕ) : ℝ) :=
        Finset.sum_congr rfl hpt
    _ = ∑ k ∈ B.filter (fun k => Nat.Coprime (f k) W),
          (1 - (ArithmeticFunction.moebius (f k) : ℝ)) / 2 * Real.log ((f k : ℕ) : ℝ) := by
        apply Finset.sum_subset hsub'
        intro k hkB hkno
        have hkB' := Finset.mem_filter.mp hkB
        have hknp : ¬ (f k).Prime := fun hp => hkno (Finset.mem_filter.mpr ⟨hkB'.1, hp⟩)
        rw [hzero k hkB'.1 hkB'.2 hknp]
        push_cast
        ring

end Conjectures.QuadraticPrimes.SieveFinalSign_aux

theorem Conjectures.QuadraticPrimes.SieveFinalSign :
let f := fun k : ℕ => 4*k^2+1; let block := fun x : ℕ => Finset.Ioc (x/2) x; let primes := fun z : ℕ => (Finset.Icc 3 z).filter (fun p => Nat.Prime p); let wheel := fun z : ℕ => ∏ p ∈ primes z, p; let rough := fun x z : ℕ => (block x).filter (fun k => Nat.Coprime (f k) (wheel z)); ∀ x z : ℕ, 2≤x → z≤2*x → (2*x)^2+1≤z^3 →
  (∑ k ∈ (block x).filter (fun k => (f k).Prime), Real.log (f k : ℝ)) =
    ∑ k ∈ rough x z, (1 - (ArithmeticFunction.moebius (f k) : ℝ))/2 * Real.log (f k : ℝ) := by
  dsimp only
  intro x z hx hz hcube
  refine Conjectures.QuadraticPrimes.SieveFinalSign_aux.sum_weight_eq
    (B := Finset.Ioc (x / 2) x) (f := fun k => 4 * k ^ 2 + 1)
    (W := ∏ p ∈ (Finset.Icc 3 z).filter (fun p => Nat.Prime p), p)
    (fun k hk hp => ?_) (fun k hk hcop hnp => ?_)
  · have hkx : x / 2 < k := (Finset.mem_Ioc.mp hk).1
    have h2k : x < 2 * k := by
      have h := (Nat.div_lt_iff_lt_mul (by norm_num) : x / 2 < k ↔ x < k * 2).mp hkx
      simpa [mul_comm] using h
    have hxx : x * x < (2 * k) * (2 * k) := Nat.mul_self_lt_mul_self h2k
    have h2x : 2 * x ≤ x * x := Nat.mul_le_mul_right x hx
    have hlt : 2 * x < 4 * k ^ 2 + 1 := by
      calc 2 * x ≤ x * x := h2x
        _ < (2 * k) * (2 * k) := hxx
        _ = 4 * k ^ 2 := by ring
        _ < 4 * k ^ 2 + 1 := Nat.lt_succ_self _
    exact Conjectures.QuadraticPrimes.SieveFinalSign_aux.coprime_wheel_of_lt hp
      (lt_of_le_of_lt hz hlt)
  · have hkx : x / 2 < k := (Finset.mem_Ioc.mp hk).1
    have hkle : k ≤ x := (Finset.mem_Ioc.mp hk).2
    have h2k : x < 2 * k := by
      have h := (Nat.div_lt_iff_lt_mul (by norm_num) : x / 2 < k ↔ x < k * 2).mp hkx
      simpa [mul_comm] using h
    have hk2 : 2 ≤ k := by omega
    have hn2 : 2 ≤ 4 * k ^ 2 + 1 := by
      have h4 : 2 * 2 ≤ k * k := Nat.mul_self_le_mul_self hk2
      have h16 : 4 * (2 * 2) ≤ 4 * (k * k) := Nat.mul_le_mul_left 4 h4
      have hb : 16 ≤ 4 * k ^ 2 := by
        calc 16 = 4 * (2 * 2) := by norm_num
          _ ≤ 4 * (k * k) := h16
          _ = 4 * k ^ 2 := by ring
      exact Nat.le_trans (Nat.le_trans (by norm_num : (2 : ℕ) ≤ 16) hb) (Nat.le_succ _)
    have hnsmall : 4 * k ^ 2 + 1 ≤ z ^ 3 := by
      have hkx2 : k * k ≤ x * x := Nat.mul_self_le_mul_self hkle
      have h4 : 4 * (k * k) ≤ 4 * (x * x) := Nat.mul_le_mul_left 4 hkx2
      have e1 : 4 * k ^ 2 = 4 * (k * k) := by ring
      have e2 : 4 * x ^ 2 = 4 * (x * x) := by ring
      calc 4 * k ^ 2 + 1 ≤ 4 * x ^ 2 + 1 := by
            rw [e1, e2]; exact Nat.add_le_add_right h4 1
        _ = (2 * x) ^ 2 + 1 := by ring
        _ ≤ z ^ 3 := hcube
    have hfac : ∀ q : ℕ, q.Prime → q ∣ 4 * k ^ 2 + 1 → z < q := fun q hq hqn =>
      Conjectures.QuadraticPrimes.SieveFinalSign_aux.prime_factor_gt
        (Conjectures.QuadraticPrimes.SieveFinalSign_aux.two_not_dvd_f k) hcop hq hqn
    have hz1 : 1 ≤ z := by
      by_contra hc
      push_neg at hc
      have hz0 : z = 0 := by omega
      have hz3 : z ^ 3 = 0 := by rw [hz0]; norm_num
      rw [hz3] at hcube
      exact absurd hcube (Nat.not_le.mpr (Nat.zero_lt_succ _))
    have hsq : ∀ t : ℕ, 4 * k ^ 2 + 1 ≠ t ^ 2 := fun t =>
      Conjectures.QuadraticPrimes.SieveFinalSign_aux.f_not_sq (by omega : 1 ≤ k) t
    rcases Conjectures.QuadraticPrimes.SieveFinalSign_aux.classify hz1 hn2 hfac hnsmall hsq with
      hp' | ⟨_, p, q, hp, hq, hpq, hpq_eq⟩
    · exact absurd hp' hnp
    · rw [hpq_eq,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
          ((Nat.coprime_primes hp hq).mpr hpq),
        ArithmeticFunction.moebius_apply_prime hp,
        ArithmeticFunction.moebius_apply_prime hq]
      norm_num
