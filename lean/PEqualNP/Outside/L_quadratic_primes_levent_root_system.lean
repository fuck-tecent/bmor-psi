import Mathlib

namespace PEqualNP.Outside

private lemma qp_dvd_mod_sq_add_one {q n : ℕ} : q ∣ n ^ 2 + 1 ↔ q ∣ (n % q) ^ 2 + 1 := by
  let k := n / q
  let r := n % q
  have hdiv : n = q * k + r := (Nat.div_add_mod n q).symm
  have heq : n ^ 2 + 1 = q * (q * k ^ 2 + 2 * k * r) + (r ^ 2 + 1) := by
    calc
      n ^ 2 + 1 = (q * k + r) ^ 2 + 1 := by rw [hdiv]
      _ = q * (q * k ^ 2 + 2 * k * r) + (r ^ 2 + 1) := by ring
  change q ∣ n ^ 2 + 1 ↔ q ∣ r ^ 2 + 1
  rw [heq]
  exact Nat.dvd_add_right (dvd_mul_right q _)

private lemma qp_exp_re (x : ℝ) : (Complex.exp ((x : ℂ) * Complex.I)).re = Real.cos x := by
  have hc : (Complex.cos (x : ℂ)).re = Real.cos x := by
    rw [← Complex.ofReal_cos]
    exact Complex.ofReal_re (Real.cos x)
  have hs : (Complex.sin (x : ℂ) * Complex.I).re = 0 := by
    rw [← Complex.ofReal_sin]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self]
  rw [Complex.exp_mul_I, Complex.add_re, hc, hs, add_zero]

private lemma qp_re_sum {ι : Type*} (s : Finset ι) (g : ι → ℂ) :
    (∑ i ∈ s, g i).re = ∑ i ∈ s, (g i).re := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t _ ih => rw [Finset.sum_cons, Finset.sum_cons, Complex.add_re, ih]

private lemma qp_cos_orth {p : ℕ} (hp : 0 < p) {r : ℕ} (hr : r < p) (n : ℕ) :
    (∑ k ∈ Finset.range p, Real.cos (2 * Real.pi * (k : ℝ) * ((n : ℝ) - (r : ℝ)) / (p : ℝ))) =
      if n % p = r then (p : ℝ) else 0 := by
  have : NeZero p := ⟨Nat.ne_of_gt hp⟩
  let t : ZMod p := (n : ZMod p) - (r : ZMod p)
  have himg : (Finset.range p).image (fun k : ℕ => (k : ZMod p)) = Finset.univ := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, iff_true]
    exact ⟨x.val, ZMod.val_lt x, ZMod.natCast_zmod_val x⟩
  have hinj : Set.InjOn (fun k : ℕ => (k : ZMod p)) (Finset.range p : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a < p := Finset.mem_range.mp ha
    have hb' : b < p := Finset.mem_range.mp hb
    have hv := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at hv
  have hterm : ∀ k : ℕ,
      (ZMod.stdAddChar (t * (k : ZMod p))).re =
        Real.cos (2 * Real.pi * (k : ℝ) * ((n : ℝ) - (r : ℝ)) / (p : ℝ)) := by
    intro k
    let j : ℤ := ((n : ℤ) - (r : ℤ)) * (k : ℤ)
    have hcast : (j : ZMod p) = t * (k : ZMod p) := by
      dsimp only [j, t]
      push_cast
      ring
    have hexp_arg : 2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) / (p : ℂ) =
        (((2 * Real.pi * (k : ℝ) * ((n : ℝ) - (r : ℝ)) / (p : ℝ) : ℝ) : ℂ) * Complex.I) := by
      dsimp only [j]
      push_cast
      ring
    rw [← hcast, ZMod.stdAddChar_coe j, hexp_arg, qp_exp_re]
  have hsum_eq : (∑ k ∈ Finset.range p,
        Real.cos (2 * Real.pi * (k : ℝ) * ((n : ℝ) - (r : ℝ)) / (p : ℝ))) =
      (∑ x : ZMod p, ZMod.stdAddChar (t * x)).re := by
    rw [qp_re_sum, ← himg, Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun k _ => (hterm k).symm)
  have horth : (∑ x : ZMod p, ZMod.stdAddChar (t * x)) = if t = 0 then (p : ℂ) else 0 := by
    split_ifs with ht
    · simp only [ht, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
        ZMod.card, nsmul_eq_mul, mul_one]
    · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p ht)
  rw [hsum_eq, horth]
  have ht_iff : t = 0 ↔ n % p = r := by
    dsimp only [t]
    rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr]
  by_cases hmod : n % p = r
  · have ht0 : t = 0 := ht_iff.mpr hmod
    simp only [ht0, hmod, ↓reduceIte]
    rw [← Complex.ofReal_natCast]
    exact Complex.ofReal_re (p : ℝ)
  · have ht0 : t ≠ 0 := fun h => hmod (ht_iff.mp h)
    simp only [ht0, hmod, ↓reduceIte, Complex.zero_re]

private lemma qp_root_system_gen (E1 E2 x : ℕ) :
    let block := fun x : ℕ => Finset.Ioc x (2 * x)
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r ^ 2 + a)
    let primes := fun x : ℕ => (Finset.Ioc x ((2 * x) ^ 2 + 1)).filter (fun p => Nat.Prime p ∧ p ^ E1 ≤ (2 * x) ^ E2)
    let window := fun x p : ℕ => (block x).filter (fun n => p ^ E1 ≤ n ^ E2)
    let countHits := fun a x p : ℕ => ((window x p).filter (fun n => p ∣ n ^ 2 + a)).card
    let inc := fun a x : ℕ => ∑ p ∈ primes x, (countHits a x p : ℝ) * Real.log (p : ℝ)
    let model := fun a x : ℕ => ∑ p ∈ primes x, ((window x p).card : ℝ) * ((roots a p).card : ℝ) / p * Real.log (p : ℝ)
    let angle := fun p k : ℕ => fun t : ℝ => 2 * Real.pi * k * t / p
    let coef := fun a x p k : ℕ => (∑ r ∈ roots a p, ∑ n ∈ window x p, Real.cos (angle p k ((n : ℝ) - r))) / p
    let freqs := fun (p : ℕ) (low : Bool) => (Finset.Ico 1 p).filter (fun k => if low then min k (p - k) ≤ Nat.sqrt p else Nat.sqrt p < min k (p - k))
    let part := fun (a x p : ℕ) (low : Bool) => (∑ k ∈ freqs p low, coef a x p k) * Real.log (p : ℝ)
    let modes := fun (a x : ℕ) (low : Bool) => ∑ p ∈ primes x, part a x p low
    inc 1 x = model 1 x + modes 1 x true + modes 1 x false := by
  intro block roots primes window countHits inc model angle coef freqs part modes
  dsimp only [inc, model, modes, part]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp_prime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
  have hp_pos : 0 < p := hp_prime.pos
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp_pos)
  rw [← add_mul, ← add_mul]
  congr 1
  have hfreqs_true : freqs p true = (Finset.Ico 1 p).filter (fun k => min k (p - k) ≤ Nat.sqrt p) := rfl
  have hfreqs_false : freqs p false =
      (Finset.Ico 1 p).filter (fun k => ¬ min k (p - k) ≤ Nat.sqrt p) := by
    dsimp only [freqs]
    ext k
    simp only [Finset.mem_filter, Bool.false_eq_true, ↓reduceIte, not_le]
  have hmodes_sum : (∑ k ∈ freqs p true, coef 1 x p k) + (∑ k ∈ freqs p false, coef 1 x p k) =
      ∑ k ∈ Finset.Ico 1 p, coef 1 x p k := by
    rw [hfreqs_true, hfreqs_false]
    exact Finset.sum_filter_add_sum_filter_not (Finset.Ico 1 p)
      (fun k => min k (p - k) ≤ Nat.sqrt p) (coef 1 x p)
  rw [add_assoc, hmodes_sum]
  have hcoef0 : coef 1 x p 0 =
      ((window x p).card : ℝ) * ((roots 1 p).card : ℝ) / (p : ℝ) := by
    dsimp only [coef, angle]
    have hcos0 : (∑ r ∈ roots 1 p, ∑ n ∈ window x p,
        Real.cos (2 * Real.pi * ((0 : ℕ) : ℝ) * ((n : ℝ) - (r : ℝ)) / (p : ℝ))) =
        ∑ _r ∈ roots 1 p, ∑ _n ∈ window x p, (1 : ℝ) := by
      refine Finset.sum_congr rfl (fun r _ => ?_)
      refine Finset.sum_congr rfl (fun n _ => ?_)
      simp
    rw [hcos0]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  rw [← hcoef0]
  have hrange : Finset.range p = insert 0 (Finset.Ico 1 p) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have h0_not_mem : (0 : ℕ) ∉ Finset.Ico 1 p := by simp
  rw [← Finset.sum_insert h0_not_mem, ← hrange]
  dsimp only [coef]
  rw [← Finset.sum_div]
  have hswap1 : (∑ k ∈ Finset.range p, ∑ r ∈ roots 1 p, ∑ n ∈ window x p,
        Real.cos (angle p k ((n : ℝ) - (r : ℝ)))) =
      ∑ r ∈ roots 1 p, ∑ n ∈ window x p, ∑ k ∈ Finset.range p,
        Real.cos (angle p k ((n : ℝ) - (r : ℝ))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_comm]
  rw [hswap1]
  have horth_inner : (∑ r ∈ roots 1 p, ∑ n ∈ window x p, ∑ k ∈ Finset.range p,
        Real.cos (angle p k ((n : ℝ) - (r : ℝ)))) =
      (∑ r ∈ roots 1 p, ∑ n ∈ window x p, if n % p = r then (1 : ℝ) else 0) * (p : ℝ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    have hr_lt : r < p := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    dsimp only [angle]
    rw [qp_cos_orth hp_pos hr_lt n]
    split_ifs <;> ring
  rw [horth_inner, mul_div_cancel_right₀ _ hp_ne, Finset.sum_comm]
  dsimp only [countHits]
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hd : p ∣ n ^ 2 + 1
  · have hd_mod : p ∣ (n % p) ^ 2 + 1 := qp_dvd_mod_sq_add_one.mp hd
    have hmem : n % p ∈ roots 1 p :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n hp_pos), hd_mod⟩
    simp only [hd, ↓reduceIte, Nat.cast_one, Finset.sum_ite_eq, hmem]
  · simp only [hd, ↓reduceIte, Nat.cast_zero]
    symm
    refine Finset.sum_eq_zero (fun r hr => ?_)
    have hne : n % p ≠ r := by
      intro heq
      have hr_dvd : p ∣ r ^ 2 + 1 := (Finset.mem_filter.mp hr).2
      rw [← heq] at hr_dvd
      exact hd (qp_dvd_mod_sq_add_one.mpr hr_dvd)
    simp only [hne, ↓reduceIte]

theorem L_quadratic_primes_levent_root_system :
    let block := fun x : ℕ => Finset.Ioc x (2*x); let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a); let primes := fun x : ℕ => (Finset.Ioc x ((2*x)^2+1)).filter (fun p => Nat.Prime p ∧ p^100000 ≤ (2*x)^132301); let window := fun x p : ℕ => (block x).filter (fun n => p^100000 ≤ n^132301); let countHits := fun a x p : ℕ => ((window x p).filter (fun n => p ∣ n^2+a)).card; let inc := fun a x : ℕ => ∑ p ∈ primes x, (countHits a x p : ℝ) * Real.log (p : ℝ); let model := fun a x : ℕ => ∑ p ∈ primes x, ((window x p).card : ℝ) * ((roots a p).card : ℝ) / p * Real.log (p : ℝ); let angle := fun p k : ℕ => fun t : ℝ => 2 * Real.pi * k * t / p; let coef := fun a x p k : ℕ => (∑ r ∈ roots a p, ∑ n ∈ window x p, Real.cos (angle p k ((n : ℝ) - r))) / p; let freqs := fun (p : ℕ) (low : Bool) => (Finset.Ico 1 p).filter (fun k => if low then min k (p-k) ≤ Nat.sqrt p else Nat.sqrt p < min k (p-k)); let part := fun (a x p : ℕ) (low : Bool) => (∑ k ∈ freqs p low, coef a x p k) * Real.log (p : ℝ); let modes := fun (a x : ℕ) (low : Bool) => ∑ p ∈ primes x, part a x p low; ∀ x : ℕ, inc 1 x = model 1 x + modes 1 x true + modes 1 x false := by
  intro block roots primes window countHits inc model angle coef freqs part modes x
  exact qp_root_system_gen 100000 132301 x

end PEqualNP.Outside
