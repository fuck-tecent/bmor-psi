import Mathlib


namespace Conjectures.Goldbach.PacketShortOrderCenterCount_aux

open Finset

private noncomputable def g (d : ℕ) : ℝ := (Real.sqrt (d:ℝ))⁻¹

private theorem exp_prod (S : Finset ℕ) (f : ℕ → ℝ) :
    (∏ p ∈ S, Real.exp (f p)) = Real.exp (∑ p ∈ S, f p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Real.exp_add, ih]

private theorem min_one_le_sqrt (x : ℝ) (hx : 0 ≤ x) : min 1 x ≤ Real.sqrt x := by
  rcases le_or_gt x 1 with h | h
  · rw [min_eq_right h]
    have h1 : Real.sqrt x ≤ 1 := Real.sqrt_le_one.mpr h
    calc x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx).symm
      _ ≤ Real.sqrt x * 1 := by exact mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg x)
      _ = Real.sqrt x := by ring
  · rw [min_eq_left h.le]
    exact Real.one_le_sqrt.mpr h.le

private def numerators (q : ℕ) := (Finset.range (q+1)).filter (fun a => Nat.Coprime a q)

private theorem countNumerators (q : ℕ) (hq : 0<q) : (numerators q).card ≤ 2*q.totient := by
  have card : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    simp only [Nat.totient_eq_card_coprime,Nat.coprime_comm]
  have sub : numerators q ⊆ insert q ((Finset.range q).filter (fun a => Nat.Coprime a q)) := by
    intro a ha
    obtain ⟨hr,hc⟩ := Finset.mem_filter.mp ha
    rcases eq_or_ne a q with rfl | h
    · simp
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hr; omega),hc⟩)
  have bound := (Finset.card_le_card sub).trans (Finset.card_insert_le ..)
  rw [card] at bound
  have hp := Nat.totient_pos.mpr hq
  omega

private theorem fractionProduct (S : Finset ℕ) (hs : ∀ p ∈ S, 2≤p) :
    (∏ p ∈ S, (p:ℝ)/((p:ℝ)-1)) ≤ (S.card:ℝ)+1 := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hmax ih =>
    have ha := hs a (Finset.mem_insert_self ..)
    have old (p : ℕ) (hp : p∈S) := hs p (Finset.mem_insert_of_mem hp)
    have ha' : 0 < (a:ℝ)-1 := by
      have h : (2:ℝ) ≤ a := by exact_mod_cast ha
      linarith
    have notMem : a ∉ S := fun h => (lt_irrefl a) (hmax a h)
    have sub : S ⊆ Finset.Ico 2 a := fun p hp => Finset.mem_Ico.mpr ⟨old p hp,hmax p hp⟩
    have count := Finset.card_le_card sub
    rw [Nat.card_Ico] at count
    have cr : (S.card:ℝ)+2 ≤ (a:ℝ) := by exact_mod_cast (show S.card+2≤a by omega)
    rw [Finset.prod_insert notMem,Finset.card_insert_of_notMem notMem,Nat.cast_add,Nat.cast_one]
    apply (mul_le_mul_of_nonneg_left (ih old) (div_nonneg (Nat.cast_nonneg _) ha'.le)).trans
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ ha').mpr
    linarith

private theorem totientLogLower (q : ℕ) (hq : 0<q) :
    (q:ℝ)/(q.totient:ℝ) ≤ (Nat.log 2 q:ℝ)+1 := by
  let S := q.primeFactors
  have hs (p : ℕ) (hp : p∈S) := (Nat.prime_of_mem_primeFactors hp).two_le
  have card : S.card ≤ Nat.log 2 q := by
    apply Nat.le_log_of_pow_le (by decide)
    calc
      _ = ∏ _p ∈ S, (2:ℕ) := by simp
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod' hs
      _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hf : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have id : (q:ℝ)/(q.totient:ℝ) = ∏ p ∈ S, (p:ℝ)/((p:ℝ)-1) := by
    rw [Finset.prod_div_distrib]
    have pos : 0 < ∏ p ∈ S, ((p:ℝ)-1) := Finset.prod_pos (fun p hp => by
      have h : (2:ℝ)≤p := by exact_mod_cast hs p hp
      linarith)
    apply (div_eq_div_iff hf.ne' pos.ne').mpr
    have formula := congrArg (fun k : ℕ => (k:ℝ)) (Nat.totient_mul_prod_primeFactors q)
    simp only [Nat.cast_mul,Nat.cast_prod] at formula
    change (q:ℝ)*_ = _*(q.totient:ℝ)
    rw [mul_comm _ (q.totient:ℝ)]
    dsimp [S]
    rw [formula]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (by have h := hs p hp; omega),Nat.cast_one]
  rw [id]
  exact (fractionProduct S hs).trans (by exact_mod_cast (show S.card+1≤Nat.log 2 q+1 by omega))

private theorem chargeWitnesses {α β : Type*} [DecidableEq β]
    (S : Finset β) (T : Finset α) (key : α → β) (w : β → ℝ) (v : α → ℝ)
    (pos : ∀ a∈T, 0≤v a) (charge : ∀ b∈S, ∃ a∈T, key a=b ∧ w b≤v a) :
    (∑ b ∈ S, w b) ≤ ∑ a ∈ T, v a := by
  calc
    _ ≤ ∑ b ∈ S, ∑ a ∈ T, if key a=b then v a else 0 := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨a,ha,e,h⟩ := charge b hb
      apply h.trans
      simpa only [e,if_true] using Finset.single_le_sum
        (s := T) (f := fun x => if key x=b then v x else 0)
        (fun x hx => by split <;> first | exact pos x hx | exact le_rfl) ha
    _ = ∑ a ∈ T, ∑ b ∈ S, if key a=b then v a else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : key a ∈ S <;> simp [h,pos a ha]



private theorem g_mul (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : g (a*b) = g a * g b := by
  unfold g
  rw [Nat.cast_mul, Real.sqrt_mul (by positivity), mul_inv_rev]
  exact mul_comm _ _

private theorem g_nonneg (d : ℕ) : 0 ≤ g d := by
  unfold g
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

private theorem g_one : g 1 = 1 := by
  simp [g]

private theorem g_pow (p x : ℕ) (hp : 1 ≤ p) : g (p ^ x) = (g p) ^ x := by
  induction x with
  | zero => simpa using g_one
  | succ x ih =>
      calc
        g (p ^ (x + 1)) = g (p ^ x * p) := by rw [pow_succ]
        _ = g (p ^ x) * g p := g_mul (p ^ x) p (Nat.one_le_pow x p hp) hp
        _ = (g p) ^ (x + 1) := by rw [ih, pow_succ]

private theorem g_lt_one {p : ℕ} (hp : 2 ≤ p) : g p < 1 := by
  have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have h1 : (1:ℝ) < Real.sqrt (p:ℝ) := by
    refine Real.lt_sqrt_of_sq_lt ?_
    norm_num
    linarith
  have hpos : (0:ℝ) < Real.sqrt (p:ℝ) := by linarith
  unfold g
  exact (inv_lt_one₀ hpos).mpr h1

private theorem divSum_step (m p : ℕ) (hpp : Nat.Prime p) (hp : p ∈ m.primeFactors) (hm : 0 < m)
    (hIH : (∑ b ∈ (m / p ^ m.factorization p).divisors, g b) ≤
      ∏ q ∈ (m / p ^ m.factorization p).primeFactors, (1 - g q)⁻¹) :
    (∑ d ∈ m.divisors, g d) ≤ ∏ q ∈ m.primeFactors, (1 - g q)⁻¹ := by
  have hm0 : m ≠ 0 := by omega
  have hPdvd : p ^ m.factorization p ∣ m := Nat.ordProj_dvd m p
  have hmc : (p ^ m.factorization p) * (m / p ^ m.factorization p) = m := by
    have h := Nat.div_mul_cancel hPdvd
    rw [mul_comm] at h
    exact h
  have hcop : Nat.Coprime (p ^ m.factorization p) (m / p ^ m.factorization p) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hpp hm0)
  have hcpf : (m / p ^ m.factorization p).primeFactors = m.primeFactors.erase p := by
    calc (m / p ^ m.factorization p).primeFactors
        = (m / p ^ m.factorization p).factorization.support := (Nat.support_factorization _).symm
      _ = (m.factorization.erase p).support := by rw [Nat.factorization_ordCompl]
      _ = m.factorization.support.erase p := Finsupp.support_erase
      _ = m.primeFactors.erase p := by rw [Nat.support_factorization]
  have hkey : (∑ d ∈ m.divisors, g d)
      = (∑ a ∈ (p ^ m.factorization p).divisors, g a)
        * (∑ b ∈ (m / p ^ m.factorization p).divisors, g b) := by
    have step1 : (∑ d ∈ ((p ^ m.factorization p) * (m / p ^ m.factorization p)).divisors, g d)
        = ∑ x ∈ (p ^ m.factorization p).divisors ×ˢ (m / p ^ m.factorization p).divisors,
            g (x.1 * x.2) := by
      rw [hcop.divisors_mul, Finset.sum_map]
      exact Finset.sum_attach _ (fun y : ℕ × ℕ => g (y.1 * y.2))
    have step2 : (∑ d ∈ m.divisors, g d)
        = ∑ x ∈ (p ^ m.factorization p).divisors ×ˢ (m / p ^ m.factorization p).divisors,
            g (x.1 * x.2) := by
      rw [← step1, hmc]
    rw [step2, Finset.sum_product]
    calc (∑ a ∈ (p ^ m.factorization p).divisors,
            ∑ b ∈ (m / p ^ m.factorization p).divisors, g (a * b))
        = ∑ a ∈ (p ^ m.factorization p).divisors,
            ∑ b ∈ (m / p ^ m.factorization p).divisors, g a * g b := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          exact g_mul a b (Nat.pos_of_mem_divisors ha) (Nat.pos_of_mem_divisors hb)
      _ = (∑ a ∈ (p ^ m.factorization p).divisors, g a
            * ∑ b ∈ (m / p ^ m.factorization p).divisors, g b) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_mul]
  have hPsum : (∑ a ∈ (p ^ m.factorization p).divisors, g a) ≤ (1 - g p)⁻¹ := by
    rw [Nat.sum_divisors_prime_pow hpp]
    have hg1 : g p < 1 := g_lt_one hpp.two_le
    have hne : g p ≠ 1 := by linarith
    have hgeom : (∑ x ∈ Finset.range (m.factorization p + 1), (g p)^x)
        = ((g p)^(m.factorization p + 1) - 1)/(g p - 1) :=
      geom_sum_eq hne _
    calc (∑ x ∈ Finset.range (m.factorization p + 1), g (p ^ x))
        = ∑ x ∈ Finset.range (m.factorization p + 1), (g p)^x := by
          apply Finset.sum_congr rfl
          intro x _
          exact g_pow p x hpp.one_le
      _ = ((g p)^(m.factorization p + 1) - 1)/(g p - 1) := hgeom
      _ = (1 - (g p)^(m.factorization p + 1))/(1 - g p) := by
          rw [show g p - 1 = -(1 - g p) by ring, div_neg]
          ring
      _ ≤ 1/(1 - g p) := by
          have hpow : 0 ≤ (g p)^(m.factorization p + 1) := pow_nonneg (g_nonneg p) _
          have hden : (0:ℝ) < 1 - g p := by linarith
          exact div_le_div_of_nonneg_right (by linarith) hden.le
      _ = (1 - g p)⁻¹ := by rw [one_div]
  have hprod0 : 0 ≤ ∏ q ∈ (m / p ^ m.factorization p).primeFactors, (1 - g q)⁻¹ := by
    apply Finset.prod_nonneg
    intro q hq
    have hq2 : 2 ≤ q := (Nat.prime_of_mem_primeFactors hq).two_le
    exact inv_nonneg.mpr (by have := g_lt_one hq2; linarith)
  have hgp0 : (0:ℝ) ≤ (1 - g p)⁻¹ := by
    exact inv_nonneg.mpr (by have := g_lt_one hpp.two_le; linarith)
  calc (∑ d ∈ m.divisors, g d)
      = (∑ a ∈ (p ^ m.factorization p).divisors, g a)
        * (∑ b ∈ (m / p ^ m.factorization p).divisors, g b) := hkey
    _ ≤ (1 - g p)⁻¹ * (∑ b ∈ (m / p ^ m.factorization p).divisors, g b) := by
        exact mul_le_mul_of_nonneg_right hPsum
          (Finset.sum_nonneg (fun b _ => g_nonneg b))
    _ ≤ (1 - g p)⁻¹ * ∏ q ∈ (m / p ^ m.factorization p).primeFactors, (1 - g q)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hIH hgp0
    _ = ∏ q ∈ m.primeFactors, (1 - g q)⁻¹ := by
        rw [hcpf, mul_comm, Finset.prod_erase_mul _ _ hp]

private theorem divSum_le_prod : ∀ m : ℕ, 0 < m →
    (∑ d ∈ m.divisors, g d) ≤ ∏ p ∈ m.primeFactors, (1 - g p)⁻¹ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro hm
    by_cases h1 : m = 1
    · subst h1
      simp [g, Nat.divisors_one, Nat.primeFactors_one]
    obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd h1
    have hm0 : m ≠ 0 := by omega
    have hp : p ∈ m.primeFactors := hpp.mem_primeFactors hpd hm0
    apply divSum_step m p hpp hp hm
    apply IH (m / p ^ m.factorization p)
    · have hv1 : 1 ≤ m.factorization p :=
        (Nat.Prime.dvd_iff_one_le_factorization hpp hm0).mp hpd
      have hP2 : 2 ≤ p ^ m.factorization p := by
        calc 2 ≤ p := hpp.two_le
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ m.factorization p := Nat.pow_le_pow_right hpp.pos hv1
      have hmc : (p ^ m.factorization p) * (m / p ^ m.factorization p) = m := by
        have h := Nat.div_mul_cancel (Nat.ordProj_dvd m p)
        rw [mul_comm] at h
        exact h
      have hstep : 2 * (m / p ^ m.factorization p)
          ≤ (p ^ m.factorization p) * (m / p ^ m.factorization p) :=
        Nat.mul_le_mul_right _ hP2
      have h2 : 2 * (m / p ^ m.factorization p) ≤ m := by
        rw [hmc] at hstep
        exact hstep
      have hcpos : 0 < m / p ^ m.factorization p := Nat.ordCompl_pos p hm0
      omega
    · exact Nat.ordCompl_pos p hm0



private lemma sqrtInv_step (i : ℕ) :
    (Real.sqrt ((i + 1 : ℕ) : ℝ))⁻¹ ≤
      2 * (Real.sqrt ((i + 1 : ℕ) : ℝ) - Real.sqrt (i : ℝ)) := by
  have hc1 : (((i + 1 : ℕ) : ℝ)) = (i : ℝ) + 1 := by push_cast; ring
  have hA : (0:ℝ) < Real.sqrt ((i + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hA2 : Real.sqrt ((i + 1 : ℕ) : ℝ) * Real.sqrt ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by
    have h := Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ ((i + 1 : ℕ) : ℝ))
    rw [hc1] at h ⊢
    exact h
  have hAB : Real.sqrt ((i + 1 : ℕ) : ℝ) * Real.sqrt (i : ℝ)
      = Real.sqrt (((i : ℝ) + 1) * (i : ℝ)) := by
    rw [hc1, Real.sqrt_mul (by positivity : (0:ℝ) ≤ (i : ℝ) + 1) (i : ℝ)]
  have hkey : Real.sqrt (((i : ℝ) + 1) * (i : ℝ)) ≤ (2 * (i : ℝ) + 1) / 2 := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg (1:ℝ)]
  rw [inv_le_iff_one_le_mul₀ hA]
  nlinarith [hA2, hAB, hkey]

private lemma sqrtInv_sum_range (N : ℕ) :
    (∑ i ∈ Finset.range N, (Real.sqrt ((i + 1 : ℕ) : ℝ))⁻¹) ≤
      2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ i ∈ Finset.range N, (Real.sqrt ((i + 1 : ℕ) : ℝ))⁻¹) +
              (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹
            ≤ 2 * Real.sqrt (N : ℝ) + (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ := add_le_add ih le_rfl
        _ ≤ 2 * Real.sqrt (N : ℝ) +
              2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) := add_le_add le_rfl (sqrtInv_step N)
        _ = 2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by ring

private lemma icc_one_eq_map_range (N : ℕ) :
    Finset.Icc 1 N = (Finset.range N).map (addRightEmbedding 1) := by
  ext n
  constructor
  · intro hn
    have hn_bounds := Finset.mem_Icc.mp hn
    refine Finset.mem_map.mpr ⟨n - 1, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · simp only [addRightEmbedding_apply]
      omega
  · intro hn
    rcases Finset.mem_map.mp hn with ⟨i, hi, hin⟩
    have hi_range := Finset.mem_range.mp hi
    have hin_eq : i + 1 = n := by
      simpa only [addRightEmbedding_apply] using hin
    apply Finset.mem_Icc.mpr
    constructor <;> omega

private theorem sqrtInv_sum_Icc (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹) ≤ 2 * Real.sqrt (N : ℝ) := by
  rw [icc_one_eq_map_range N, Finset.sum_map]
  simpa only [addRightEmbedding_apply, Nat.cast_add, Nat.cast_one] using
    sqrtInv_sum_range N



private theorem primeSumSplit (m W : ℕ) (hm : 0 < m) (hW : 2 ≤ W) :
    (∑ p ∈ m.primeFactors, (Real.sqrt (p : ℝ))⁻¹)
      ≤ 2 * (W : ℝ) + (Nat.log 2 m : ℝ) / ((2 * (Nat.log 2 W : ℝ)) * (W : ℝ)) := by
  let small := m.primeFactors.filter (fun p => p ≤ W ^ 2)
  let large := m.primeFactors.filter (fun p => ¬ p ≤ W ^ 2)
  have hsplit :
      (∑ p ∈ small, (Real.sqrt (p : ℝ))⁻¹) +
          (∑ p ∈ large, (Real.sqrt (p : ℝ))⁻¹) =
        ∑ p ∈ m.primeFactors, (Real.sqrt (p : ℝ))⁻¹ := by
    dsimp [small, large]
    exact Finset.sum_filter_add_sum_filter_not m.primeFactors (fun p => p ≤ W ^ 2)
      (fun p => (Real.sqrt (p : ℝ))⁻¹)
  have hsmall_subset : small ⊆ Finset.Icc 1 (W ^ 2) := by
    intro p hp
    have hp_mem : p ∈ m.primeFactors := (Finset.mem_filter.mp hp).1
    have hp_le : p ≤ W ^ 2 := (Finset.mem_filter.mp hp).2
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
    exact Finset.mem_Icc.mpr ⟨hp_prime.one_le, hp_le⟩
  have hsmall :
      (∑ p ∈ small, (Real.sqrt (p : ℝ))⁻¹) ≤
        2 * Real.sqrt ((W ^ 2 : ℕ) : ℝ) := by
    calc
      (∑ p ∈ small, (Real.sqrt (p : ℝ))⁻¹) ≤
          ∑ p ∈ Finset.Icc 1 (W ^ 2), (Real.sqrt (p : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsmall_subset (fun p _ _ =>
          inv_nonneg.2 (Real.sqrt_nonneg _))
      _ ≤ 2 * Real.sqrt ((W ^ 2 : ℕ) : ℝ) := sqrtInv_sum_Icc (W ^ 2)
  have hsqrt_sq : Real.sqrt ((W ^ 2 : ℕ) : ℝ) = (W : ℝ) := by
    rw [Nat.cast_pow]
    exact Real.sqrt_sq (Nat.cast_nonneg W)
  have hsmall' :
      (∑ p ∈ small, (Real.sqrt (p : ℝ))⁻¹) ≤ 2 * (W : ℝ) := by
    simpa only [hsqrt_sq] using hsmall
  have hlarge_subset : large ⊆ m.primeFactors := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hlarge_factor (p : ℕ) (hp : p ∈ large) : W ^ 2 ≤ p := by
    have hnot : ¬ p ≤ W ^ 2 := (Finset.mem_filter.mp hp).2
    omega
  have hlarge_sqrt (p : ℕ) (hp : p ∈ large) :
      (W : ℝ) ≤ Real.sqrt (p : ℝ) := by
    have hnat : W ^ 2 ≤ p := hlarge_factor p hp
    have hreal : (W : ℝ) ^ 2 ≤ (p : ℝ) := by
      exact_mod_cast hnat
    calc
      (W : ℝ) = Real.sqrt ((W : ℝ) ^ 2) := (Real.sqrt_sq (Nat.cast_nonneg W)).symm
      _ ≤ Real.sqrt (p : ℝ) := Real.sqrt_le_sqrt hreal
  have hW_pos_nat : 0 < W := by omega
  have hW_pos : 0 < (W : ℝ) := by exact_mod_cast hW_pos_nat
  have hlarge_term (p : ℕ) (hp : p ∈ large) :
      (Real.sqrt (p : ℝ))⁻¹ ≤ (W : ℝ)⁻¹ := by
    have hsqrt := hlarge_sqrt p hp
    exact (inv_le_inv₀ (hW_pos.trans_le hsqrt) hW_pos).2 hsqrt
  have hlarge :
      (∑ p ∈ large, (Real.sqrt (p : ℝ))⁻¹) ≤
        (large.card : ℝ) * (W : ℝ)⁻¹ := by
    calc
      (∑ p ∈ large, (Real.sqrt (p : ℝ))⁻¹) ≤
          ∑ _p ∈ large, (W : ℝ)⁻¹ :=
        Finset.sum_le_sum (fun p hp => hlarge_term p hp)
      _ = (large.card : ℝ) * (W : ℝ)⁻¹ := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hlarge_product :
      W ^ (2 * large.card) ≤ ∏ p ∈ large, p := by
    rw [pow_mul]
    exact Finset.pow_card_le_prod large id (W ^ 2) (fun p hp => hlarge_factor p hp)
  have hlarge_product_dvd : (∏ p ∈ large, p) ∣ m := by
    exact dvd_trans
      (Finset.prod_dvd_prod_of_subset large m.primeFactors id hlarge_subset)
      (Nat.prod_primeFactors_dvd m)
  have hlarge_product_le : (∏ p ∈ large, p) ≤ m :=
    Nat.le_of_dvd hm hlarge_product_dvd
  have hW_pow_le : W ^ (2 * large.card) ≤ m :=
    hlarge_product.trans hlarge_product_le
  have hbase_pow : 2 ^ Nat.log 2 W ≤ W :=
    Nat.pow_log_le_self 2 (Nat.ne_of_gt hW_pos_nat)
  have htwo_pow :
      2 ^ (Nat.log 2 W * (2 * large.card)) ≤ W ^ (2 * large.card) := by
    calc
      2 ^ (Nat.log 2 W * (2 * large.card)) =
          (2 ^ Nat.log 2 W) ^ (2 * large.card) := by rw [pow_mul]
      _ ≤ W ^ (2 * large.card) := Nat.pow_le_pow_left hbase_pow _
  have hlog :
      Nat.log 2 W * (2 * large.card) ≤ Nat.log 2 m :=
    Nat.le_log_of_pow_le (by omega) (htwo_pow.trans hW_pow_le)
  have hcard_log :
      2 * large.card * Nat.log 2 W ≤ Nat.log 2 m := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlog
  have hlogW_pos_nat : 0 < Nat.log 2 W :=
    Nat.log_pos (by omega) hW
  have hlogW_pos : 0 < (Nat.log 2 W : ℝ) := by
    exact_mod_cast hlogW_pos_nat
  have hcard_div :
      (large.card : ℝ) ≤
        (Nat.log 2 m : ℝ) / (2 * (Nat.log 2 W : ℝ)) := by
    apply (le_div_iff₀ (by positivity)).2
    norm_cast
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcard_log
  have hlarge' :
      (∑ p ∈ large, (Real.sqrt (p : ℝ))⁻¹) ≤
        (Nat.log 2 m : ℝ) / ((2 * (Nat.log 2 W : ℝ)) * (W : ℝ)) := by
    calc
      (∑ p ∈ large, (Real.sqrt (p : ℝ))⁻¹) ≤
          (large.card : ℝ) * (W : ℝ)⁻¹ := hlarge
      _ = (large.card : ℝ) / (W : ℝ) := by rw [div_eq_mul_inv]
      _ ≤ ((Nat.log 2 m : ℝ) / (2 * (Nat.log 2 W : ℝ))) / (W : ℝ) :=
        div_le_div_of_nonneg_right hcard_div hW_pos.le
      _ = (Nat.log 2 m : ℝ) / ((2 * (Nat.log 2 W : ℝ)) * (W : ℝ)) := by
        rw [div_div]
  calc
    (∑ p ∈ m.primeFactors, (Real.sqrt (p : ℝ))⁻¹) =
        (∑ p ∈ small, (Real.sqrt (p : ℝ))⁻¹) +
          (∑ p ∈ large, (Real.sqrt (p : ℝ))⁻¹) := hsplit.symm
    _ ≤ 2 * (W : ℝ) + (∑ p ∈ large, (Real.sqrt (p : ℝ))⁻¹) := add_le_add hsmall' le_rfl
    _ ≤ 2 * (W : ℝ) +
        (Nat.log 2 m : ℝ) / ((2 * (Nat.log 2 W : ℝ)) * (W : ℝ)) := add_le_add le_rfl hlarge'



private theorem poly24_le_exp (L : ℕ) (hL : 2^70000 ≤ L) :
    24*(L:ℝ)^3 ≤ Real.exp ((L:ℝ)/100) := by
  have hlarge_nat : (604:ℕ)^2 ≤ L := by
    have hp : (2:ℕ)^20 ≤ 2^70000 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact (by norm_num : (604:ℕ)^2 ≤ 2^20).trans (hp.trans hL)
  have hlarge : (604:ℝ)^2 ≤ (L:ℝ) := by
    exact_mod_cast hlarge_nat
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hlpos : 0 < (L:ℝ) := by
    exact_mod_cast hLpos
  have hlnonneg : 0 ≤ (L:ℝ) := Nat.cast_nonneg L
  let s : ℝ := Real.sqrt (L:ℝ)
  have hsnonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hssq : s^2 = (L:ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt hlnonneg
  have hs604 : (604:ℝ) ≤ s := by
    apply (Real.le_sqrt (by norm_num) hlnonneg).2
    exact hlarge
  have hxpos : 0 < 24*(L:ℝ)^3 := by
    positivity
  have hloglarge :
      Real.log (24*(L:ℝ)^3) = Real.log 24 + 3*Real.log (L:ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    ring
  have hrpow : (L:ℝ)^((1:ℝ)/2) = s := by
    dsimp [s]
    rw [← Real.sqrt_eq_rpow]
  have hlogsqrt : Real.log (L:ℝ) ≤ 2*s := by
    calc
      Real.log (L:ℝ) ≤ (L:ℝ)^((1:ℝ)/2)/((1:ℝ)/2) :=
        Real.log_le_rpow_div hlnonneg (by norm_num)
      _ = 2*s := by rw [hrpow]; ring
  have hlog24 : Real.log 24 ≤ 24 :=
    Real.log_le_self (by norm_num)
  have hquad : 0 ≤ (s-604)*(s+4) :=
    mul_nonneg (sub_nonneg.mpr hs604) (by linarith)
  have hfinal : 24 + 6*s ≤ (L:ℝ)/100 := by
    nlinarith [hquad, hssq]
  have hlog :
      Real.log (24*(L:ℝ)^3) ≤ (L:ℝ)/100 := by
    calc
      Real.log (24*(L:ℝ)^3) = Real.log 24 + 3*Real.log (L:ℝ) := hloglarge
      _ ≤ 24 + 6*s := by nlinarith [hlog24, hlogsqrt]
      _ ≤ (L:ℝ)/100 := hfinal
  exact (Real.log_le_iff_le_exp hxpos).1 hlog



private theorem sqrt_inv_le_exp (Q L : ℕ) (hQ : 2^L ≤ Q) :
    (Real.sqrt (Q:ℝ))⁻¹ ≤ Real.exp (-(345/1000)*(L:ℝ)) := by
  have hQpos : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  have hQrpos : 0 < (Q:ℝ) := by
    exact_mod_cast hQpos
  have hQreal : (2:ℝ)^L ≤ (Q:ℝ) := by
    exact_mod_cast hQ
  have hsqrt : Real.sqrt ((2:ℝ)^L) ≤ Real.sqrt (Q:ℝ) :=
    Real.sqrt_le_sqrt hQreal
  have hsqrtpow : Real.sqrt ((2:ℝ)^L) = (2:ℝ)^((L:ℝ)/2) := by
    calc
      Real.sqrt ((2:ℝ)^L) = ((2:ℝ)^L)^((1:ℝ)/2) :=
        Real.sqrt_eq_rpow _
      _ = ((2:ℝ)^((L:ℝ)))^((1:ℝ)/2) := by rw [Real.rpow_natCast]
      _ = (2:ℝ)^((L:ℝ)*((1:ℝ)/2)) := by
        rw [← Real.rpow_mul (by norm_num)]
      _ = (2:ℝ)^((L:ℝ)/2) := by congr 1 <;> ring
  have hhalf : (345/1000:ℝ) ≤ Real.log 2/2 := by
    linarith [Real.log_two_gt_d9]
  have hlogfactor :
      (345/1000:ℝ)*(L:ℝ) ≤ Real.log 2*((L:ℝ)/2) := by
    calc
      (345/1000:ℝ)*(L:ℝ) ≤ (Real.log 2/2)*(L:ℝ) :=
        mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg L)
      _ = Real.log 2*((L:ℝ)/2) := by ring
  have hexp :
      Real.exp ((345/1000:ℝ)*(L:ℝ)) ≤ Real.sqrt ((2:ℝ)^L) := by
    rw [hsqrtpow, Real.rpow_def_of_pos (by norm_num)]
    exact Real.exp_le_exp.mpr hlogfactor
  have hmain :
      Real.exp ((345/1000:ℝ)*(L:ℝ)) ≤ Real.sqrt (Q:ℝ) :=
    hexp.trans hsqrt
  rw [show -(345/1000:ℝ)*(L:ℝ) = -((345/1000)*(L:ℝ)) by ring,
    Real.exp_neg]
  exact (inv_le_inv₀ (Real.sqrt_pos.2 hQrpos) (Real.exp_pos _)).2 hmain



private theorem sqCast_le (L : ℕ) (hL1 : 1 ≤ L) : (((L+1)^2:ℕ):ℝ) ≤ 4*(L:ℝ)^2 := by
  have h3 : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL1
  push_cast
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3*(L:ℝ)+1)
    (by linarith : (0:ℝ) ≤ (L:ℝ)-1)]

private theorem poly24_aux (L : ℕ) (hL2 : 2 ≤ L) :
    2*(2*(L:ℝ)+2)*4*(L:ℝ)^2 ≤ 24*(L:ℝ)^3 := by
  have h3 : (2:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL2
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (L:ℝ))
    (by linarith : (0:ℝ) ≤ (L:ℝ)))
    (by linarith : (0:ℝ) ≤ (L:ℝ)-2)]

private theorem mulW_aux (lW W : ℕ) (h : 69992 ≤ lW) :
    (69632:ℝ)*(W:ℝ) ≤ (lW:ℝ)*(W:ℝ) := by
  have hzl : (69992:ℝ) ≤ (lW:ℝ) := by exact_mod_cast h
  have hW0 : (0:ℝ) ≤ (W:ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.mpr hzl) hW0]

private theorem halg_aux (q Q : ℕ) (hq : (0:ℝ) < q) (hQ : (0:ℝ) < Q)
    (hφ : (0:ℝ) < (q.totient:ℝ)) :
    (Real.sqrt (q:ℝ)/Real.sqrt (Q:ℝ)) * (2*(q.totient:ℝ)) / (q.totient:ℝ)^2
      = 2*((q:ℝ)/(q.totient:ℝ))*(Real.sqrt (Q:ℝ))⁻¹*(Real.sqrt (q:ℝ))⁻¹ := by
  have hs : Real.sqrt (q:ℝ)*Real.sqrt (q:ℝ) = (q:ℝ) := Real.mul_self_sqrt hq.le
  have hQ0 : Real.sqrt (Q:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hQ)
  have hq0 : Real.sqrt (q:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have hφ0 : (q.totient:ℝ) ≠ 0 := ne_of_gt hφ
  field_simp
  nlinarith [hs]

private theorem prod_le_prod_real (s : Finset ℕ) (f₁ f₂ : ℕ → ℝ)
    (h : ∀ p ∈ s, 0 ≤ f₁ p) (hle : ∀ p ∈ s, f₁ p ≤ f₂ p) :
    (∏ p ∈ s, f₁ p) ≤ ∏ p ∈ s, f₂ p := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hfa : 0 ≤ f₁ a := h a (Finset.mem_insert_self a s)
      have hga : 0 ≤ f₂ a := le_trans hfa (hle a (Finset.mem_insert_self a s))
      exact mul_le_mul (hle a (Finset.mem_insert_self a s))
        (ih (fun q hq => h q (Finset.mem_insert_of_mem hq))
          (fun q hq => hle q (Finset.mem_insert_of_mem hq)))
        (Finset.prod_nonneg (fun q hq => h q (Finset.mem_insert_of_mem hq))) hga

private theorem prod_bound (m : ℕ) :
    (∏ p ∈ m.primeFactors, (1 - g p)⁻¹) ≤ Real.exp (4 * ∑ p ∈ m.primeFactors, g p) := by
  have key : ∀ p ∈ m.primeFactors, (1 - g p)⁻¹ ≤ Real.exp (4 * g p) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    have hsqrt : (4:ℝ)/3 ≤ Real.sqrt (p:ℝ) := by
      refine (Real.le_sqrt (by norm_num) (by linarith)).mpr ?_
      nlinarith
    have hg0 : 0 ≤ g p := by
      dsimp [g]; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hg : g p ≤ 3/4 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 4/3) hsqrt
      dsimp [g]
      calc (Real.sqrt (p:ℝ))⁻¹ = 1/(Real.sqrt (p:ℝ)) := by rw [one_div]
        _ ≤ 1/((4:ℝ)/3) := h
        _ = 3/4 := by norm_num
    have h1 : (1 - g p)⁻¹ ≤ 1 + 4*g p := by
      rw [inv_eq_one_div]
      refine (div_le_iff₀ (by linarith : (0:ℝ) < 1 - g p)).mpr ?_
      nlinarith [mul_nonneg hg0 (by linarith : (0:ℝ) ≤ 3 - 4*g p)]
    calc (1 - g p)⁻¹ ≤ 1 + 4*g p := h1
      _ ≤ Real.exp (4*g p) := by simpa [add_comm] using Real.add_one_le_exp (4*g p)
  calc (∏ p ∈ m.primeFactors, (1 - g p)⁻¹) ≤ ∏ p ∈ m.primeFactors, Real.exp (4 * g p) := by
        refine prod_le_prod_real _ _ _ (fun p hp => ?_) key
        exact inv_nonneg.mpr (by have := g_lt_one (Nat.prime_of_mem_primeFactors hp).two_le; linarith)
    _ = Real.exp (∑ p ∈ m.primeFactors, 4 * g p) := exp_prod _ _
    _ = Real.exp (4 * ∑ p ∈ m.primeFactors, g p) := by rw [Finset.mul_sum]

private theorem divSum_pow (j W : ℕ) (hj : 1 ≤ j) (hW : 2 ≤ W) :
    (∑ d ∈ (2^j-1:ℕ).divisors, g d) ≤
      Real.exp (4 * (2*(W:ℝ) + (j:ℝ)/((2*(Nat.log 2 W:ℝ))*(W:ℝ)))) := by
  have hm : 0 < (2^j-1:ℕ) :=
    Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.one_le_iff_ne_zero.mp hj))
  have hlog : Nat.log 2 (2^j-1:ℕ) ≤ j := by
    have h1 : Nat.log 2 (2^j-1:ℕ) ≤ Nat.log 2 (2^j) :=
      Nat.log_mono_right (Nat.sub_le (2^j) 1)
    have h2 : Nat.log 2 (2^j) = j := Nat.log_pow (by decide) j
    omega
  have hsplit : (∑ p ∈ (2^j-1:ℕ).primeFactors, g p) ≤
      2*(W:ℝ) + (Nat.log 2 (2^j-1:ℕ):ℝ)/((2*(Nat.log 2 W:ℝ))*(W:ℝ)) := by
    have h := primeSumSplit (2^j-1) W hm hW
    simpa only [g] using h
  have hden : (0:ℝ) < (2*(Nat.log 2 W:ℝ))*(W:ℝ) := by
    have h1 : 0 < Nat.log 2 W := Nat.log_pos (by decide) hW
    have h1' : (0:ℝ) < (Nat.log 2 W:ℝ) := by exact_mod_cast h1
    have h2 : (0:ℝ) < (W:ℝ) := by exact_mod_cast (by omega : 0 < W)
    positivity
  calc (∑ d ∈ (2^j-1:ℕ).divisors, g d) ≤ ∏ p ∈ (2^j-1:ℕ).primeFactors, (1 - g p)⁻¹ :=
        divSum_le_prod _ hm
    _ ≤ Real.exp (4 * ∑ p ∈ (2^j-1:ℕ).primeFactors, g p) := prod_bound _
    _ ≤ Real.exp (4 * (2*(W:ℝ) + (Nat.log 2 (2^j-1:ℕ):ℝ)/((2*(Nat.log 2 W:ℝ))*(W:ℝ)))) := by
        refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsplit (by norm_num))
    _ ≤ Real.exp (4 * (2*(W:ℝ) + (j:ℝ)/((2*(Nat.log 2 W:ℝ))*(W:ℝ)))) := by
        have hstep : 2*(W:ℝ) + (Nat.log 2 (2^j-1:ℕ):ℝ)/((2*(Nat.log 2 W:ℝ))*(W:ℝ))
            ≤ 2*(W:ℝ) + (j:ℝ)/((2*(Nat.log 2 W:ℝ))*(W:ℝ)) := add_le_add le_rfl (div_le_div_of_nonneg_right (by exact_mod_cast hlog) hden.le)
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hstep (by norm_num))


end Conjectures.Goldbach.PacketShortOrderCenterCount_aux



open Conjectures.Goldbach.PacketShortOrderCenterCount_aux

theorem Conjectures.Goldbach.PacketShortOrderCenterCount : let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) * (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) / (Nat.totient q:ℝ)^2) ≤ ε := by
  intro Q L K o ε hε
  classical
  obtain ⟨M, hM⟩ := exists_nat_ge (max 1 (1/ε))
  have hM1 : (1:ℕ) ≤ M := by
    exact_mod_cast (le_trans (le_max_left (1:ℝ) (1/ε)) hM)
  have hMε : (1:ℝ)/ε ≤ (M:ℝ) := le_trans (le_max_right 1 (1/ε)) hM
  refine ⟨2^(2^(2^(M+70000)+1)), ?_⟩
  intro n hn
  have hn2 : 2^(2^(2^(M+70000)+1)) ≤ n+2 := by omega
  have hlog1 : 2^(2^(M+70000)+1) ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) hn2
  have hQval : Q n = (Nat.log 2 (n+2))^2 := rfl
  have hQn : 2^(2^(M+70000)) ≤ Q n := by
    rw [hQval]
    have h1 : (2^(2^(M+70000)+1))^2 ≤ (Nat.log 2 (n+2))^2 := Nat.pow_le_pow_left hlog1 2
    have h2 : 2^(2^(M+70000)) ≤ (2^(2^(M+70000)+1))^2 := by
      have he : (2^(2^(M+70000)+1))^2 = 2^((2^(M+70000)+1)*2) :=
        (pow_mul 2 (2^(M+70000)+1) 2).symm
      rw [he]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact h2.trans h1
  have hLg : 2^(M+70000) ≤ Nat.log 2 (Q n) := Nat.le_log_of_pow_le (by decide) hQn
  have hQnpos : 0 < Q n := lt_of_lt_of_le (by positivity) hQn
  have hLg2 : 2^70000 ≤ Nat.log 2 (Q n) :=
    (Nat.pow_le_pow_right (by decide) (show (70000:ℕ) ≤ M + 70000 by omega)).trans hLg
  have hLg1 : 1 ≤ Nat.log 2 (Q n) := le_trans (Nat.one_le_pow 70000 2 (by decide)) hLg2
  have hLg2b : 2 ≤ Nat.log 2 (Q n) := by omega
  have hLL : 70000 ≤ Nat.log 2 (Nat.log 2 (Q n)) := Nat.le_log_of_pow_le (by decide) hLg2
  have hzdef : 8 + (Nat.log 2 (Nat.log 2 (Q n)) - 8) = Nat.log 2 (Nat.log 2 (Q n)) :=
    Nat.add_sub_of_le (by omega)
  have hWle : 256 * 2^(Nat.log 2 (Nat.log 2 (Q n)) - 8) ≤ Nat.log 2 (Q n) := by
    have h1 : 256 * 2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)
        = 2^(8 + (Nat.log 2 (Nat.log 2 (Q n)) - 8)) := by
      rw [show (256:ℕ) = 2^8 from rfl, ← pow_add]
    rw [h1, hzdef]
    exact Nat.pow_log_le_self 2 (by omega)
  have hWgt : Nat.log 2 (Q n) < 512 * 2^(Nat.log 2 (Nat.log 2 (Q n)) - 8) := by
    have h1 : 512 * 2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)
        = 2^(9 + (Nat.log 2 (Nat.log 2 (Q n)) - 8)) := by
      rw [show (512:ℕ) = 2^9 from rfl, ← pow_add]
    have h2 : 9 + (Nat.log 2 (Nat.log 2 (Q n)) - 8) = Nat.log 2 (Nat.log 2 (Q n)) + 1 := by omega
    rw [h1, h2]
    exact Nat.lt_pow_succ_log_self (by decide) (Nat.log 2 (Q n))
  have hLW : Nat.log 2 (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)) = Nat.log 2 (Nat.log 2 (Q n)) - 8 :=
    Nat.log_pow (by decide) _
  have hW2 : 2 ≤ 2^(Nat.log 2 (Nat.log 2 (Q n)) - 8) := by
    have h : (2:ℕ)^1 ≤ 2^(Nat.log 2 (Nat.log 2 (Q n)) - 8) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    simpa using h
  have hterm : ∀ q : ℕ, q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q) →
      min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) *
          (((Finset.range (q+1)).filter
            (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) /
          (Nat.totient q:ℝ)^2
        ≤ 2*(2*(Nat.log 2 (Q n):ℝ)+2)*(Real.sqrt (Q n:ℝ))⁻¹*(Real.sqrt (q:ℝ))⁻¹ := by
    intro q hq
    have hqI : q ∈ Finset.Icc 1 ((Q n)^2) := (Finset.mem_filter.mp hq).1
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hqI).1
    have hqQ : q ≤ (Q n)^2 := (Finset.mem_Icc.mp hqI).2
    have hcard : ((Finset.range (q+1)).filter
          (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card ≤ 2*q.totient := by
      have hsub : (Finset.range (q+1)).filter
            (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ))) ⊆ numerators q := by
        intro a ha
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2.1⟩
      exact (Finset.card_le_card hsub).trans (countNumerators q (by omega))
    have hφ : (0:ℝ) < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hQp : (0:ℝ) < (Q n:ℝ) := by exact_mod_cast hQnpos
    have hqp : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hlogq : Nat.log 2 q ≤ 2*(Nat.log 2 (Q n)) + 1 := by
      have h1 : Nat.log 2 q ≤ Nat.log 2 ((Q n)^2) := Nat.log_mono_right hqQ
      have h2 : Nat.log 2 ((Q n)^2) < 2*(Nat.log 2 (Q n)) + 2 := by
        refine Nat.log_lt_of_lt_pow (pow_ne_zero 2 (by omega)) ?_
        have h3 := Nat.lt_pow_succ_log_self (by decide : (1:ℕ) < 2) (Q n)
        calc (Q n)^2 < (2^(Nat.log 2 (Q n)+1))^2 := Nat.pow_lt_pow_left h3 (by norm_num)
          _ = 2^((Nat.log 2 (Q n)+1)*2) := (pow_mul 2 (Nat.log 2 (Q n)+1) 2).symm
          _ = 2^(2*(Nat.log 2 (Q n))+2) := by ring
      omega
    have htq : (q:ℝ)/(q.totient:ℝ) ≤ 2*(Nat.log 2 (Q n):ℝ)+2 := by
      have h1 := totientLogLower q (by omega)
      have h2 : (Nat.log 2 q:ℝ)+1 ≤ 2*(Nat.log 2 (Q n):ℝ)+2 := by
        exact_mod_cast (show Nat.log 2 q + 1 ≤ 2*Nat.log 2 (Q n)+2 by omega)
      linarith
    have hmin : min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) ≤ Real.sqrt (q:ℝ)/Real.sqrt (Q n:ℝ) := by
      have h := min_one_le_sqrt ((q:ℝ)/(Q n:ℝ)) (div_nonneg (Nat.cast_nonneg q) hQp.le)
      rwa [Real.sqrt_div (by positivity)] at h
    have halg : (Real.sqrt (q:ℝ)/Real.sqrt (Q n:ℝ)) * (2*(q.totient:ℝ)) / (q.totient:ℝ)^2
        = 2*((q:ℝ)/(q.totient:ℝ))*(Real.sqrt (Q n:ℝ))⁻¹*(Real.sqrt (q:ℝ))⁻¹ :=
      halg_aux q (Q n) hqp hQp hφ
    calc min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) * (((Finset.range (q+1)).filter
            (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) /
          (Nat.totient q:ℝ)^2
        ≤ (Real.sqrt (q:ℝ)/Real.sqrt (Q n:ℝ)) * (2*(q.totient:ℝ)) / (Nat.totient q:ℝ)^2 := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul hmin (by exact_mod_cast hcard) (by positivity) (by positivity)
      _ = 2*((q:ℝ)/(q.totient:ℝ))*(Real.sqrt (Q n:ℝ))⁻¹*(Real.sqrt (q:ℝ))⁻¹ := halg
      _ ≤ 2*(2*(Nat.log 2 (Q n):ℝ)+2)*(Real.sqrt (Q n:ℝ))⁻¹*(Real.sqrt (q:ℝ))⁻¹ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) (by positivity)
          linarith
  have hcharge : (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q), (Real.sqrt (q:ℝ))⁻¹)
      ≤ ∑ j ∈ Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2),
          ∑ d ∈ (2^j-1:ℕ).divisors, (Real.sqrt (d:ℝ))⁻¹ := by
    set S := (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q) with hSdef
    set J := Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2) with hJdef
    let T : Finset (Σ _j : ℕ, ℕ) := J.sigma (fun j => (2^j-1:ℕ).divisors)
    have vpos : ∀ a ∈ T, (0:ℝ) ≤ (Real.sqrt (a.2:ℝ))⁻¹ := by
      intro a _
      exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    have charge : ∀ b ∈ S, ∃ a ∈ T, a.2 = b ∧ (Real.sqrt (b:ℝ))⁻¹ ≤ (Real.sqrt (a.2:ℝ))⁻¹ := by
      intro b hb
      have ho : o n b := (Finset.mem_filter.mp hb).2
      have ho' : b % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter
          (fun j => b ∣ 2^j-1)).Nonempty := ho
      obtain ⟨j, hj⟩ := ho'.2
      obtain ⟨hj1, hj2⟩ := Finset.mem_filter.mp hj
      have hjpos : 1 ≤ j := (Finset.mem_Icc.mp hj1).1
      refine ⟨⟨j, b⟩, ?_, rfl, le_rfl⟩
      refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · simpa only [hJdef] using hj1
      · rw [Nat.mem_divisors]
        refine ⟨hj2, ?_⟩
        exact ne_of_gt (Nat.sub_pos_of_lt
          (Nat.one_lt_two_pow (Nat.one_le_iff_ne_zero.mp hjpos)))
    have h := chargeWitnesses S T (fun a => a.2) (fun b => (Real.sqrt (b:ℝ))⁻¹)
      (fun a => (Real.sqrt (a.2:ℝ))⁻¹) vpos charge
    calc (∑ q ∈ S, (Real.sqrt (q:ℝ))⁻¹) ≤ ∑ a ∈ T, (Real.sqrt (a.2:ℝ))⁻¹ := h
      _ = ∑ j ∈ J, ∑ d ∈ (2^j-1:ℕ).divisors, (Real.sqrt (d:ℝ))⁻¹ := by
          dsimp only [T]
          rw [Finset.sum_sigma]
  have hexp : ∀ j ∈ Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2),
      (∑ d ∈ (2^j-1:ℕ).divisors, (Real.sqrt (d:ℝ))⁻¹)
        ≤ Real.exp (4*((Nat.log 2 (Q n):ℝ)/44)) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj2 : j ≤ (Nat.log 2 (Q n)+1)^2 := (Finset.mem_Icc.mp hj).2
    have hds := divSum_pow j (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)) hj1 hW2
    have hz' : 69992 ≤ Nat.log 2 (Nat.log 2 (Q n)) - 8 := by omega
    have hzl : (69992:ℝ) ≤ ((Nat.log 2 (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)):ℕ):ℝ) := by
      rw [hLW]; exact_mod_cast hz'
    have hWl : (Nat.log 2 (Q n):ℝ) < 512*((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ) := by
      exact_mod_cast hWgt
    have hW0 : (0:ℝ) ≤ ((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ) := Nat.cast_nonneg _
    have hLg0 : (0:ℝ) ≤ (Nat.log 2 (Q n):ℝ) := Nat.cast_nonneg _
    have hLgp : (0:ℝ) < (Nat.log 2 (Q n):ℝ) := by exact_mod_cast (by omega : 0 < Nat.log 2 (Q n))
    have hjl : (j:ℝ) ≤ 4*(Nat.log 2 (Q n):ℝ)^2 := by
      have h1 : (j:ℝ) ≤ (((Nat.log 2 (Q n)+1)^2:ℕ):ℝ) := by exact_mod_cast hj2
      have h2 : (((Nat.log 2 (Q n)+1)^2:ℕ):ℝ) ≤ 4*(Nat.log 2 (Q n):ℝ)^2 :=
        sqCast_le (Nat.log 2 (Q n)) hLg1
      linarith
    have hkey : (136:ℝ)*(Nat.log 2 (Q n):ℝ)
        ≤ ((Nat.log 2 (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)):ℕ):ℝ)
          * ((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ) := by
      have h1 : (136:ℝ)*(Nat.log 2 (Q n):ℝ)
          ≤ 136*(512*((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ)) := by
        exact mul_le_mul_of_nonneg_left hWl.le (by norm_num)
      have h2 : (136:ℝ)*(512*((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ))
          ≤ ((Nat.log 2 (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)):ℕ):ℝ)
            * ((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ) := by
        have hz'' : 69992 ≤ Nat.log 2 (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)) := by
          rw [hLW]; exact hz'
        have h4 : (69632:ℝ)*((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ)
            ≤ ((Nat.log 2 (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)):ℕ):ℝ)
              * ((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ) :=
          mulW_aux _ _ hz''
        have h5 : (136:ℝ)*(512*((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ))
            = (69632:ℝ)*((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ) := by ring
        rw [h5]
        exact h4
      linarith
    have hA : 2*((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ) ≤ (Nat.log 2 (Q n):ℝ)/128 := by
      have h1 : (256:ℝ)*((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ) ≤ (Nat.log 2 (Q n):ℝ) := by
        exact_mod_cast hWle
      have h2 : 2*((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ)
          = ((256:ℝ)*((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ))/128 := by ring
      rw [h2]
      exact div_le_div_of_nonneg_right h1 (by norm_num)
    have hB : (j:ℝ)/((2*((Nat.log 2 (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)):ℕ):ℝ))
        *((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ)) ≤ (Nat.log 2 (Q n):ℝ)/68 := by
      have hden : (0:ℝ) < (2*((Nat.log 2 (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)):ℕ):ℝ))
          *((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ) := by
        have hz0 : (0:ℝ) < ((Nat.log 2 (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)):ℕ):ℝ) := by
          exact_mod_cast (by omega : 0 < Nat.log 2 (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)))
        have hW0p : (0:ℝ) < ((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ) := by
          exact_mod_cast (by positivity : 0 < 2^(Nat.log 2 (Nat.log 2 (Q n)) - 8))
        positivity
      have hmain : (68:ℝ)*(j:ℝ) ≤ (Nat.log 2 (Q n):ℝ)*((2*((Nat.log 2
          (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)):ℕ):ℝ))
          *((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ)) := by
        have h1 : (68:ℝ)*(j:ℝ) ≤ 68*(4*(Nat.log 2 (Q n):ℝ)^2) :=
          mul_le_mul_of_nonneg_left hjl (by norm_num)
        have h2 : (68:ℝ)*(4*(Nat.log 2 (Q n):ℝ)^2)
            = (Nat.log 2 (Q n):ℝ)*(2*((136:ℝ)*(Nat.log 2 (Q n):ℝ))) := by ring
        have h3 : (Nat.log 2 (Q n):ℝ)*(2*((136:ℝ)*(Nat.log 2 (Q n):ℝ)))
            ≤ (Nat.log 2 (Q n):ℝ)*(2*(((Nat.log 2
                (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)):ℕ):ℝ)
              *((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hLg0
          linarith
        have h4 : (Nat.log 2 (Q n):ℝ)*(2*(((Nat.log 2
              (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)):ℕ):ℝ)
            *((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ)))
            = (Nat.log 2 (Q n):ℝ)*((2*((Nat.log 2
              (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)):ℕ):ℝ))
              *((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ)) := by ring
        linarith
      refine (div_le_div_iff₀ hden (by norm_num)).mpr ?_
      simpa only [mul_comm] using hmain
    have hsum44 : 2*((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ)
        + (j:ℝ)/((2*((Nat.log 2 (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)):ℕ):ℝ))
          *((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ)) ≤ (Nat.log 2 (Q n):ℝ)/44 := by
      have h1 : (Nat.log 2 (Q n):ℝ)/128 + (Nat.log 2 (Q n):ℝ)/68 ≤ (Nat.log 2 (Q n):ℝ)/44 := by
        have h2 : (1:ℝ)/128 + 1/68 ≤ 1/44 := by norm_num
        calc (Nat.log 2 (Q n):ℝ)/128 + (Nat.log 2 (Q n):ℝ)/68
            = (Nat.log 2 (Q n):ℝ)*(1/128 + 1/68) := by ring
          _ ≤ (Nat.log 2 (Q n):ℝ)*(1/44) := by exact mul_le_mul_of_nonneg_left h2 hLg0
          _ = (Nat.log 2 (Q n):ℝ)/44 := by ring
      linarith
    calc (∑ d ∈ (2^j-1:ℕ).divisors, (Real.sqrt (d:ℝ))⁻¹)
        ≤ Real.exp (4 * (2*((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ)
            + (j:ℝ)/((2*((Nat.log 2 (2^(Nat.log 2 (Nat.log 2 (Q n)) - 8)):ℕ):ℝ))
              *((2^(Nat.log 2 (Nat.log 2 (Q n)) - 8):ℕ):ℝ)))) := hds
      _ ≤ Real.exp (4*((Nat.log 2 (Q n):ℝ)/44)) := by
          refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum44 (by norm_num))
  have htotal : (∑ j ∈ Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2),
        ∑ d ∈ (2^j-1:ℕ).divisors, (Real.sqrt (d:ℝ))⁻¹)
      ≤ (((Nat.log 2 (Q n)+1)^2:ℕ):ℝ) * Real.exp (4*((Nat.log 2 (Q n):ℝ)/44)) := by
    calc _ ≤ ∑ j ∈ Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2),
            Real.exp (4*((Nat.log 2 (Q n):ℝ)/44)) :=
          Finset.sum_le_sum (fun j hj => hexp j hj)
      _ = (((Nat.log 2 (Q n)+1)^2:ℕ):ℝ) * Real.exp (4*((Nat.log 2 (Q n):ℝ)/44)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          simp
  have hJ : (((Nat.log 2 (Q n)+1)^2:ℕ):ℝ) ≤ 4*(Nat.log 2 (Q n):ℝ)^2 :=
    sqCast_le (Nat.log 2 (Q n)) hLg1
  have hpre : 2*(2*(Nat.log 2 (Q n):ℝ)+2)*4*(Nat.log 2 (Q n):ℝ)^2
      ≤ 24*(Nat.log 2 (Q n):ℝ)^3 := poly24_aux (Nat.log 2 (Q n)) hLg2b
  have hQpow : 2^(Nat.log 2 (Q n)) ≤ Q n := Nat.pow_log_le_self 2 (by omega)
  have hbound : (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q),
        min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) *
          (((Finset.range (q+1)).filter
            (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) /
          (Nat.totient q:ℝ)^2)
      ≤ Real.exp (-(19/100)*(Nat.log 2 (Q n):ℝ)) := by
    have h1 : (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q),
        min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) *
          (((Finset.range (q+1)).filter
            (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) /
          (Nat.totient q:ℝ)^2)
        ≤ 2*(2*(Nat.log 2 (Q n):ℝ)+2)*(Real.sqrt (Q n:ℝ))⁻¹ *
          (∑ j ∈ Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2),
            ∑ d ∈ (2^j-1:ℕ).divisors, (Real.sqrt (d:ℝ))⁻¹) := by
      calc _ ≤ ∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q),
              2*(2*(Nat.log 2 (Q n):ℝ)+2)*(Real.sqrt (Q n:ℝ))⁻¹*(Real.sqrt (q:ℝ))⁻¹ :=
            Finset.sum_le_sum (fun q hq => hterm q hq)
        _ = 2*(2*(Nat.log 2 (Q n):ℝ)+2)*(Real.sqrt (Q n:ℝ))⁻¹ *
              ∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q), (Real.sqrt (q:ℝ))⁻¹ := by
            rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left hcharge (by positivity)
    calc _ ≤ 2*(2*(Nat.log 2 (Q n):ℝ)+2)*(Real.sqrt (Q n:ℝ))⁻¹ *
          (∑ j ∈ Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2),
            ∑ d ∈ (2^j-1:ℕ).divisors, (Real.sqrt (d:ℝ))⁻¹) := h1
      _ ≤ 2*(2*(Nat.log 2 (Q n):ℝ)+2)*(Real.sqrt (Q n:ℝ))⁻¹ *
          (4*(Nat.log 2 (Q n):ℝ)^2 * Real.exp (4*((Nat.log 2 (Q n):ℝ)/44))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc _ ≤ (((Nat.log 2 (Q n)+1)^2:ℕ):ℝ) * Real.exp (4*((Nat.log 2 (Q n):ℝ)/44)) := htotal
            _ ≤ 4*(Nat.log 2 (Q n):ℝ)^2 * Real.exp (4*((Nat.log 2 (Q n):ℝ)/44)) :=
                mul_le_mul_of_nonneg_right hJ (by positivity)
      _ = (2*(2*(Nat.log 2 (Q n):ℝ)+2)*4*(Nat.log 2 (Q n):ℝ)^2)
            * ((Real.sqrt (Q n:ℝ))⁻¹ * Real.exp (4*((Nat.log 2 (Q n):ℝ)/44))) := by ring
      _ ≤ (24*(Nat.log 2 (Q n):ℝ)^3)
            * ((Real.sqrt (Q n:ℝ))⁻¹ * Real.exp (4*((Nat.log 2 (Q n):ℝ)/44))) :=
          mul_le_mul_of_nonneg_right hpre (by positivity)
      _ ≤ (24*(Nat.log 2 (Q n):ℝ)^3)
            * (Real.exp (-(345/1000)*(Nat.log 2 (Q n):ℝ)) * Real.exp (4*((Nat.log 2 (Q n):ℝ)/44))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (sqrt_inv_le_exp (Q n) (Nat.log 2 (Q n)) hQpow) (by positivity)
      _ ≤ Real.exp ((Nat.log 2 (Q n):ℝ)/100)
            * (Real.exp (-(345/1000)*(Nat.log 2 (Q n):ℝ)) * Real.exp (4*((Nat.log 2 (Q n):ℝ)/44))) := by
          refine mul_le_mul_of_nonneg_right (poly24_le_exp _ hLg2) ?_
          positivity
      _ = Real.exp ((Nat.log 2 (Q n):ℝ)/100 + (-(345/1000)*(Nat.log 2 (Q n):ℝ)
            + 4*((Nat.log 2 (Q n):ℝ)/44))) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (-(19/100)*(Nat.log 2 (Q n):ℝ)) := by
          refine Real.exp_le_exp.mpr ?_
          have h0 : (0:ℝ) ≤ (Nat.log 2 (Q n):ℝ) := Nat.cast_nonneg _
          linarith
  have hfin : Real.exp (-(19/100)*(Nat.log 2 (Q n):ℝ)) ≤ 1/(M:ℝ) := by
    have hkey : (M:ℝ) ≤ Real.exp ((19/100)*(Nat.log 2 (Q n):ℝ)) := by
      have hA : (2:ℝ)^(M+70000) ≤ (Nat.log 2 (Q n):ℝ) := by exact_mod_cast hLg
      have hC : (1:ℝ) ≤ (19/100)*(2:ℝ)^70000 := by
        have h4 : (2:ℝ)^4 ≤ (2:ℝ)^70000 := by
          exact_mod_cast (Nat.pow_le_pow_right (by decide : (0:ℕ) < 2) (by norm_num : (4:ℕ) ≤ 70000))
        have h4' : (2:ℝ)^4 = 16 := by norm_num
        have h16 : (16:ℝ) ≤ (2:ℝ)^70000 := by
          rw [← h4']
          exact h4
        calc (1:ℝ) ≤ (19/100)*16 := by norm_num
          _ ≤ (19/100)*(2:ℝ)^70000 := mul_le_mul_of_nonneg_left h16 (by norm_num)
      have hB : (2:ℝ)^M * (2:ℝ)^70000 = (2:ℝ)^(M+70000) := by rw [pow_add]
      have h1 : (2:ℝ)^M ≤ (19/100)*(Nat.log 2 (Q n):ℝ) := by
        calc (2:ℝ)^M = 1 * (2:ℝ)^M := by ring
          _ ≤ ((19/100)*(2:ℝ)^70000) * (2:ℝ)^M := by
              exact mul_le_mul_of_nonneg_right hC (by positivity)
          _ = (19/100)*((2:ℝ)^(M+70000)) := by rw [← hB]; ring
          _ ≤ (19/100)*(Nat.log 2 (Q n):ℝ) := by
              exact mul_le_mul_of_nonneg_left hA (by norm_num)
      have h2 : (19/100)*(Nat.log 2 (Q n):ℝ) + 1 ≤ Real.exp ((19/100)*(Nat.log 2 (Q n):ℝ)) :=
        Real.add_one_le_exp _
      have h3 : (M:ℝ)+1 ≤ (2:ℝ)^M := by
        exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := M)))
      have h4 : (M:ℝ) + 2 ≤ Real.exp ((19/100)*(Nat.log 2 (Q n):ℝ)) := by
        calc (M:ℝ) + 2 = ((M:ℝ)+1) + 1 := by ring
          _ ≤ (2:ℝ)^M + 1 := add_le_add h3 le_rfl
          _ ≤ (19/100)*(Nat.log 2 (Q n):ℝ) + 1 := add_le_add h1 le_rfl
          _ ≤ Real.exp ((19/100)*(Nat.log 2 (Q n):ℝ)) := h2
      calc (M:ℝ) ≤ (M:ℝ) + 2 := le_add_of_nonneg_right (by norm_num)
        _ ≤ Real.exp ((19/100)*(Nat.log 2 (Q n):ℝ)) := h4
    calc Real.exp (-(19/100)*(Nat.log 2 (Q n):ℝ))
        = 1/(Real.exp ((19/100)*(Nat.log 2 (Q n):ℝ))) := by
          rw [show -(19/100)*(Nat.log 2 (Q n):ℝ) = -((19/100)*(Nat.log 2 (Q n):ℝ)) by ring,
            Real.exp_neg, one_div]
      _ ≤ 1/(M:ℝ) := one_div_le_one_div_of_le (by exact_mod_cast hM1) hkey
  have hMε' : (1:ℝ)/(M:ℝ) ≤ ε := by
    have hMp : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM1
    refine (div_le_iff₀ hMp).mpr ?_
    have := (div_le_iff₀ hε).mp hMε
    simpa only [mul_comm] using this
  exact hbound.trans (hfin.trans hMε')