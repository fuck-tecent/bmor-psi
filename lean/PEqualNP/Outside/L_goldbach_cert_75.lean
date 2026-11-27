import Mathlib
open ArithmeticFunction

namespace PEqualNP.Outside

private theorem sum_moebius_eq (n : ℕ) :
    ∑ d ∈ n.divisors, (moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun (f : ArithmeticFunction ℤ) => f n) moebius_mul_coe_zeta
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h
  simp only [natCoe_apply, zeta_apply] at h
  rw [Nat.sum_divisorsAntidiagonal (n := n)
      (f := fun a b => moebius a * (((if b = 0 then 0 else 1) : ℕ) : ℤ))] at h
  have hfac : ∀ d ∈ n.divisors,
      moebius d * (((if n / d = 0 then 0 else 1) : ℕ) : ℤ) = moebius d := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdvd, hn0⟩ := hd
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
    have hnd : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hnpos hdvd) hd0
    have hif : ((if n / d = 0 then 0 else 1) : ℕ) = 1 := if_neg (Nat.ne_of_gt hnd)
    rw [hif, Nat.cast_one, mul_one]
  rw [Finset.sum_congr rfl hfac] at h
  simpa using h

private theorem sum_moebius_eq_c (n : ℕ) :
    ∑ d ∈ n.divisors, (moebius d : ℂ) = if n = 1 then 1 else 0 := by
  have h := sum_moebius_eq n
  exact_mod_cast h

private theorem inner_geom (q d : ℕ) (hq : 0 < q) (hd : d ∈ q.divisors)
    (Z : ℂ) (hZ : IsPrimitiveRoot Z q) (a : ℕ) (ha : Nat.Coprime a q) :
    ∑ b ∈ (Finset.range q).filter (fun b => d ∣ b), Z ^ (a * b) = if d = q then 1 else 0 := by
  rw [Nat.mem_divisors] at hd
  obtain ⟨hdvd, hq0⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hq
  have hqm : q = d * (q / d) := by
    have h := Nat.div_mul_cancel hdvd
    rw [mul_comm] at h
    exact h.symm
  have hset : (Finset.range q).filter (fun b => d ∣ b)
      = (Finset.range (q / d)).image (fun j => d * j) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hb, j, rfl⟩
      refine ⟨j, ?_, rfl⟩
      have hb' : j * d < (q / d) * d := by
        calc j * d = d * j := by ring
          _ < q := hb
          _ = (q / d) * d := (Nat.div_mul_cancel hdvd).symm
      exact Nat.lt_of_mul_lt_mul_right hb'
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, j, rfl⟩
      have hjd : j * d < (q / d) * d := by
        have hqd : (q / d) * d = q := Nat.div_mul_cancel hdvd
        nlinarith [hj, hd0, hqd]
      calc d * j = j * d := by ring
        _ < (q / d) * d := hjd
        _ = q := Nat.div_mul_cancel hdvd
  rw [hset]
  rw [Finset.sum_image (by
    intro x _ y _ hxy
    exact Nat.mul_left_cancel hd0 hxy)]
  have hterm : ∀ j, Z ^ (a * (d * j)) = (Z ^ d) ^ (a * j) := by
    intro j
    rw [show a * (d * j) = d * (a * j) from by ring]
    rw [pow_mul]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  have hpow : ∑ j ∈ Finset.range (q / d), (Z ^ d) ^ (a * j)
      = ∑ j ∈ Finset.range (q / d), ((Z ^ d) ^ a) ^ j :=
    Finset.sum_congr rfl (fun j _ => by rw [pow_mul])
  rw [hpow]
  have hmpos : 0 < q / d := by
    rcases Nat.eq_zero_or_pos (q / d) with h | h
    · exfalso
      rw [h, mul_zero] at hqm
      exact absurd hqm (Nat.ne_of_gt hq)
    · exact h
  have hdvdq : q / d ∣ q := ⟨d, by rw [mul_comm]; exact hqm⟩
  have hZd : IsPrimitiveRoot (Z ^ d) (q / d) := hZ.pow_of_dvd (p := d) (by omega) hdvd
  have ham : Nat.Coprime a (q / d) := ha.coprime_dvd_right hdvdq
  by_cases hm1 : q / d = 1
  · have hdq : d = q := by rw [hqm, hm1, mul_one]
    rw [if_pos hdq]
    simp [hm1]
  · have hgt : 1 < q / d := by omega
    have hpr := (hZd.pow_iff_coprime hmpos a).mpr ham
    rw [hpr.geom_sum_eq_zero hgt]
    have hdq : d ≠ q := by
      intro h
      rw [h] at hm1
      have hq1 : q / q = 1 := Nat.div_self hq
      omega
    rw [if_neg hdq]

private theorem ramanujan_general (q a : ℕ) (hq : 1 < q) (ha : Nat.Coprime a q) :
    ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
      Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / q) ^ (a * b)
    = (moebius q : ℂ) := by
  let Z : ℂ := Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / q)
  have hZ : IsPrimitiveRoot Z q := Complex.isPrimitiveRoot_exp q (by omega)
  have hind : ∀ b, (if Nat.Coprime b q then (1 : ℂ) else 0)
      = ∑ d ∈ (Nat.gcd b q).divisors, (moebius d : ℂ) := by
    intro b
    by_cases h : Nat.Coprime b q
    · rw [if_pos h, h.gcd_eq_one, sum_moebius_eq_c]
      simp
    · have hg : Nat.gcd b q ≠ 1 := fun h1 => h (Nat.coprime_iff_gcd_eq_one.mpr h1)
      rw [if_neg h, sum_moebius_eq_c, if_neg hg]
  calc ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), Z ^ (a * b)
      = ∑ b ∈ Finset.range q, (if Nat.Coprime b q then Z ^ (a * b) else 0) := by
          rw [Finset.sum_filter]
      _ = ∑ b ∈ Finset.range q,
            (∑ d ∈ (Nat.gcd b q).divisors, (moebius d : ℂ)) * Z ^ (a * b) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [show (if Nat.Coprime b q then Z ^ (a * b) else 0)
              = (if Nat.Coprime b q then (1 : ℂ) else 0) * Z ^ (a * b) from by
            by_cases hp : Nat.Coprime b q
            · rw [if_pos hp, if_pos hp, one_mul]
            · rw [if_neg hp, if_neg hp, zero_mul]]
          rw [hind b]
      _ = ∑ b ∈ Finset.range q,
            ∑ d ∈ (Nat.gcd b q).divisors, (moebius d : ℂ) * Z ^ (a * b) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_mul]
      _ = ∑ b ∈ Finset.range q,
            ∑ d ∈ q.divisors.filter (fun d => d ∣ Nat.gcd b q), (moebius d : ℂ) * Z ^ (a * b) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Nat.divisors_filter_dvd_of_dvd (by omega) (Nat.gcd_dvd_right b q)]
      _ = ∑ b ∈ Finset.range q,
            ∑ d ∈ q.divisors.filter (fun d => d ∣ b), (moebius d : ℂ) * Z ^ (a * b) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          congr 1
          apply Finset.filter_congr
          intro d hd
          rw [Nat.mem_divisors] at hd
          exact ⟨fun h1 => Nat.dvd_trans h1 (Nat.gcd_dvd_left b q),
            fun h1 => Nat.dvd_gcd h1 hd.1⟩
      _ = ∑ b ∈ Finset.range q,
            ∑ d ∈ q.divisors, (if d ∣ b then (moebius d : ℂ) * Z ^ (a * b) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_filter]
      _ = ∑ d ∈ q.divisors,
            ∑ b ∈ Finset.range q, (if d ∣ b then (moebius d : ℂ) * Z ^ (a * b) else 0) :=
          Finset.sum_comm
      _ = ∑ d ∈ q.divisors, (moebius d : ℂ) * (if d = q then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          rw [← Finset.sum_filter, ← Finset.mul_sum]
          rw [inner_geom q d (by omega) hd Z hZ a ha]
      _ = (moebius q : ℂ) := by
          simp only [mul_ite, mul_one, mul_zero]
          rw [Finset.sum_ite_eq']
          rw [if_pos (Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩)]

private lemma cq_arg (a b : ℕ) :
    (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 75 : ℝ) : ℂ) * Complex.I)
      = ((a * b : ℕ) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 75) := by
  push_cast
  ring

private lemma cq_term (a b : ℕ) :
    Complex.exp (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 75 : ℝ) : ℂ) * Complex.I)
      = Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 75) ^ (a * b) := by
  rw [cq_arg a b, ← Complex.exp_nat_mul]

theorem L_goldbach_cert_75 (a : ℕ) (ha : Nat.Coprime a 75) :
    (∑ b ∈ (Finset.range 75).filter (fun b => Nat.Coprime b 75),
        Complex.exp (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 75 : ℝ) : ℂ) * Complex.I)) / (40 : ℂ)
      = (0 : ℂ) / 40 := by
  have hnsq : ¬ Squarefree 75 := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro h
    exact h 5 (by norm_num) (by norm_num)
  have hmuZ : (moebius 75 : ℤ) = 0 := by
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
  have hmu : (moebius 75 : ℂ) = 0 := by exact_mod_cast hmuZ
  have hzero :
      ∑ b ∈ (Finset.range 75).filter (fun b => Nat.Coprime b 75),
        Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 75) ^ (a * b) = 0 := by
    have hg := ramanujan_general 75 a (by norm_num) ha
    rw [hmu] at hg
    exact hg
  have hconv :
      ∑ b ∈ (Finset.range 75).filter (fun b => Nat.Coprime b 75),
        Complex.exp (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 75 : ℝ) : ℂ) * Complex.I)
      = 0 := by
    rw [← hzero]
    exact Finset.sum_congr rfl (fun b _ => cq_term a b)
  rw [hconv]

end PEqualNP.Outside
