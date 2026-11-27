import Mathlib

namespace PacketRemainingOverlapFullSupport

-- Adapted from PacketShortOrderCenterCount at 2366f2b0660bcc65d4dfe2c0c3a25eba62498095 under the repository license.
namespace PacketAllMassShortSupport

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

end PacketAllMassShortSupport

-- Adapted from PacketRemainingCenterCount at 5d74e5a07df63b8178fbd75aaeea10819bbab26a under the repository license.
namespace PacketAllMassRemainingSupport

/-!
# Resonant numerators for the remaining Goldbach packet moduli

For the dyadic cosine average, the weighted number of resonant primitive
numerators tends to zero, uniformly over every denominator in the registered
range. Smooth denominators and denominators with a large prime factor of short
binary period each have negligible total weight. On all remaining denominators,
Fourier orthogonality bounds the second moment by the number of collisions
between separated binary frequencies. The Euler totient second-moment estimate
then bounds their combined contribution.

The component proofs below retain their original attribution. The long-factor
argument is related to the reference proof in goldbach-proofs PR #3669.
-/

/-! The finite character orthogonality and second moment below are reproduced from
Conjectures.Goldbach.PacketBinaryOrbitSecondMoment, goldbach-proofs,
commit 99020bf57fb80332fceb70bec7f5bb7b49d3dc3d, Apache-2.0. -/

open scoped BigOperators

namespace Conjectures.Goldbach.PacketBinaryOrbitSecondMoment_aux

noncomputable def ph (q a k : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((k : ℝ) * (a : ℝ) / (q : ℝ)) : ℝ) : ℂ) * Complex.I)

private lemma ph_unit (q a k : ℕ) : ‖ph q a k‖ = 1 := by
  unfold ph
  exact Complex.norm_exp_ofReal_mul_I _

private theorem orth (q u v : ℕ) (hq : 0 < q) :
    (∑ a ∈ Finset.range q, ph q a u * (starRingEnd ℂ) (ph q a v)) =
      if u % q = v % q then (q : ℂ) else 0 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)
  have hζ : IsPrimitiveRoot ζ q := Complex.isPrimitiveRoot_exp q hq.ne'
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have phase (a k : ℕ) : ph q a k = (ζ ^ k) ^ a := by
    unfold ph
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have term (a : ℕ) : ph q a u * (starRingEnd ℂ) (ph q a v) =
      (ζ ^ u / ζ ^ v) ^ a := by
    rw [← Complex.inv_eq_conj (ph_unit q a v), phase, phase, div_pow, div_eq_mul_inv]
  simp_rw [term]
  have hpowiff (x y : ℕ) : ζ ^ x = ζ ^ y ↔ x % q = y % q := by
    have hfin := hζ.isOfFinOrder hq.ne'
    rw [hfin.pow_inj_mod, hζ.eq_orderOf]
  by_cases huv : u % q = v % q
  · have hbase : ζ ^ u / ζ ^ v = 1 :=
      (div_eq_one_iff_eq (pow_ne_zero v hζ0)).2 ((hpowiff u v).2 huv)
    rw [ite_eq_left huv, hbase]
    simp
  · rw [ite_eq_right huv, geom_sum_eq]
    · have hpow (x : ℕ) : (ζ ^ x) ^ q = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
      simp [div_pow, hpow]
    · intro hbase
      apply huv
      apply (hpowiff u v).1
      exact (div_eq_one_iff_eq (pow_ne_zero v hζ0)).1 hbase

theorem second_moment (q m : ℕ) (k : ℕ → ℕ) (hq : 0 < q) :
    (∑ a ∈ Finset.range q, ‖∑ j ∈ Finset.range m, ph q a (k j)‖ ^ 2) =
      (q : ℝ) * ((((Finset.range m ×ˢ Finset.range m).filter
        (fun ij => k ij.1 % q = k ij.2 % q)).card : ℝ)) := by
  have expand (a : ℕ) :
      (∑ j ∈ Finset.range m, ph q a (k j)) *
          (starRingEnd ℂ) (∑ j ∈ Finset.range m, ph q a (k j)) =
        ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m,
          ph q a (k j) * (starRingEnd ℂ) (ph q a (k l)) := by
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', expand]
  have hswap :
      (∑ a ∈ Finset.range q, ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m,
        ph q a (k j) * (starRingEnd ℂ) (ph q a (k l))) =
      ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, ∑ a ∈ Finset.range q,
        ph q a (k j) * (starRingEnd ℂ) (ph q a (k l)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  rw [hswap]
  rw [Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun l _ => orth q (k j) (k l) hq))]
  rw [← Finset.sum_product']
  calc
    (∑ ij ∈ Finset.range m ×ˢ Finset.range m,
        if k ij.1 % q = k ij.2 % q then (q : ℂ) else 0) =
        (q : ℂ) * ∑ ij ∈ Finset.range m ×ˢ Finset.range m,
          if k ij.1 % q = k ij.2 % q then (1 : ℂ) else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ij _
            split_ifs <;> ring
    _ = (q : ℂ) * ((((Finset.range m ×ˢ Finset.range m).filter
        (fun ij => k ij.1 % q = k ij.2 % q)).card : ℂ)) := by
      rw [Finset.sum_boole]

end Conjectures.Goldbach.PacketBinaryOrbitSecondMoment_aux

namespace GB4Moment
open Finset Conjectures.Goldbach.PacketBinaryOrbitSecondMoment_aux

noncomputable def K (L : ℕ) (t : ℝ) : ℝ :=
  (∑ j ∈ range L, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L:ℝ)

private theorem collision_count (q L m : ℕ) (hm : 0 < m)
    (sep : ∀ i j : ℕ, i < j → j < L →
      (2:ℕ)^(i+1)%q = 2^(j+1)%q → m ≤ j-i) :
    (((range L ×ˢ range L).filter (fun ij =>
      (2:ℕ)^(ij.1+1)%q = 2^(ij.2+1)%q)).card) ≤ L * (L/m+1) := by
  let P := (range L ×ˢ range L).filter (fun ij =>
      (2:ℕ)^(ij.1+1)%q = 2^(ij.2+1)%q)
  change P.card ≤ _
  have data {i j : ℕ} (h : (i,j) ∈ P) :
      i < L ∧ j < L ∧ (2:ℕ)^(i+1)%q = 2^(j+1)%q := by
    simpa only [P, mem_filter, mem_product, mem_range, and_assoc] using h
  have inj : Set.InjOn (fun ij : ℕ × ℕ => (ij.1,ij.2/m)) (P : Set (ℕ × ℕ)) := by
    rintro ⟨i,j⟩ hx ⟨i',k⟩ hy heq
    change (i,j/m) = (i',k/m) at heq
    obtain ⟨rfl,hjk⟩ := Prod.mk.inj heq
    have dx := data hx
    have dy := data hy
    have ee := dx.2.2.symm.trans dy.2.2
    have hj := Nat.mod_add_div j m
    have hk := Nat.mod_add_div k m
    rw [hjk] at hj
    have hj' := Nat.mod_lt j hm
    have hk' := Nat.mod_lt k hm
    have h : j = k := by
      rcases lt_trichotomy j k with hl | he | hl
      · have := sep j k hl dy.2.1 ee
        omega
      · exact he
      · have := sep k j hl dx.2.1 ee.symm
        omega
    cases h
    rfl
  calc
    P.card = (P.image (fun ij : ℕ × ℕ => (ij.1,ij.2/m))).card :=
      (card_image_of_injOn inj).symm
    _ ≤ (range L ×ˢ range (L/m+1)).card := by
      apply card_le_card
      intro y hy
      obtain ⟨⟨i,j⟩,h,rfl⟩ := mem_image.mp hy
      exact mem_product.mpr ⟨mem_range.mpr (data h).1,
        mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (data h).2.1.le))⟩
    _ = _ := by simp

theorem centers_le (q L m : ℕ) (hq : 1 < q) (hm : 0 < m) (hmL : m ≤ L)
    (sep : ∀ i j : ℕ, i < j → j < L →
      (2:ℕ)^(i+1)%q = 2^(j+1)%q → m ≤ j-i) :
    (((range (q+1)).filter (fun a : ℕ => a.Coprime q ∧ (1:ℝ)/3 < K L ((a:ℝ)/q))).card : ℝ) ≤
      18*(q:ℝ)/m := by
  classical
  let H := (range (q+1)).filter (fun a : ℕ => a.Coprime q ∧ (1:ℝ)/3 < K L ((a:ℝ)/q))
  let F := fun a : ℕ => ∑ j ∈ range L, ph q a ((2:ℕ)^(j+1))
  have hL : (0:ℝ) < L := by exact_mod_cast hm.trans_le hmL
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hsub : H ⊆ range q := by
    intro a ha
    obtain ⟨har,hcop,_⟩ := mem_filter.mp ha
    have hle := mem_range.mp har
    have hne : a ≠ q := by
      rintro rfl
      have : a = 1 := by simpa [Nat.Coprime] using hcop
      omega
    exact mem_range.mpr (by omega)
  have reF (a : ℕ) : (F a).re = K L ((a:ℝ)/q)*L := by
    unfold K
    rw [div_mul_cancel₀ _ hL.ne']
    dsimp only [F]
    rw [Complex.re_sum]
    apply sum_congr rfl
    intro j _
    unfold ph
    rw [Complex.exp_ofReal_mul_I_re]
    push_cast
    congr 1
    ring
  have energy : (H.card:ℝ)*((L:ℝ)/3)^2 ≤ ∑ a ∈ range q, ‖F a‖^2 := by
    calc
      _ = ∑ _a ∈ H, ((L:ℝ)/3)^2 := by simp
      _ ≤ ∑ a ∈ H, ‖F a‖^2 := by
        apply sum_le_sum
        intro a ha
        have h := (mem_filter.mp ha).2.2
        have hs := Complex.re_le_norm (F a)
        rw [reF] at hs
        have hh : (L:ℝ)/3 ≤ ‖F a‖ := by nlinarith [mul_le_mul_of_nonneg_right h.le hL.le]
        exact pow_le_pow_left₀ (by positivity) hh 2
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
  have hcard := collision_count q L m hm sep
  have he := second_moment q L (fun j => (2:ℕ)^(j+1)) (by omega)
  change (∑ a ∈ range q, ‖F a‖^2) = _ at he
  rw [he] at energy
  have hc : ((((range L ×ˢ range L).filter (fun ij =>
      (2:ℕ)^(ij.1+1)%q = 2^(ij.2+1)%q)).card):ℝ) ≤
      (L:ℝ)*((L/m:ℕ)+1) := by exact_mod_cast hcard
  have div_le : (↑(L/m):ℝ)*(m:ℝ) ≤ L := by exact_mod_cast Nat.div_mul_le_self L m
  have hmlr : (m:ℝ) ≤ L := by exact_mod_cast hmL
  have hblock : ((↑(L/m):ℝ)+1)*m ≤ 2*L := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hblock (show 0 ≤ (q:ℝ)*L by positivity)
  have hc2 := energy.trans (mul_le_mul_of_nonneg_left hc (by positivity))
  change (H.card : ℝ) ≤ _
  apply (le_div_iff₀ hmr).mpr
  apply (mul_le_mul_iff_left₀ (show 0 < ((L:ℝ)/3)^2 by positivity)).mp
  nlinarith [mul_le_mul_of_nonneg_right hc2 hmr.le]

end GB4Moment

/-! The Rankin estimate and the divisor and totient sums adapt the Apache-2.0
Goldbach proofs from PRs #3341 and #2327 and the previously submitted short-order
center count at revision 33d9880d26eca803a13c4e6371e6960037e9ad73. Here the smooth cutoff is the twelfth power of the binary-log scale,
and a single large prime factor, rather than the whole modulus, has short period. -/

namespace GB4Bad
open Finset
open scoped Classical

def grid (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2
def u (n : ℕ) : ℕ := 1 + Nat.log 2 (grid n)
def smooth (n q : ℕ) : Prop := ∀ p ∈ q.primeFactors, p ≤ (u n)^12
def shortLarge (n q : ℕ) : Prop := ∃ p ∈ q.primeFactors, (u n)^12 < p ∧
  ∃ j ∈ Finset.Icc 1 ((u n)^4), p ∣ 2^j-1
noncomputable def weight (n q : ℕ) : ℝ := min 1 ((q:ℝ)/(grid n:ℝ))/(q.totient:ℝ)

namespace GoldbachSmoothModuli

private theorem rankin_min (x : ℝ) (hx : 0 < x) : min 1 x ≤ x^(1/32 : ℝ) := by
  by_cases hx1 : x ≤ 1
  · rw [min_eq_right hx1]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num : (1/32:ℝ) ≤ 1)
  · rw [min_eq_left (le_of_not_ge hx1)]
    exact Real.one_le_rpow (le_of_not_ge hx1) (by norm_num)

private theorem reciprocal_totient (q : ℕ) (hq : 0 < q) :
    1 / (q.totient : ℝ) ≤ (q.divisors.card : ℝ) / q := by
  have hcount : q ≤ q.divisors.card * q.totient := by
    calc
      q = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
      _ ≤ ∑ _d ∈ q.divisors, q.totient := sum_le_sum fun d hd =>
        Nat.le_of_dvd (Nat.totient_pos.mpr hq) (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
      _ = _ := by simp
  apply (div_le_div_iff₀ (by exact_mod_cast Nat.totient_pos.mpr hq) (by exact_mod_cast hq)).2
  simpa using (show (q : ℝ) ≤ (q.divisors.card : ℝ) * q.totient by exact_mod_cast hcount)

/-- Expanding the divisor count sends each factor pair into the square of the smooth set. -/
theorem smooth_convolution_bound (Q Y : ℕ) (hQ : 1 ≤ Q) :
    (∑ q ∈ (Icc 1 (Q^2)).filter (fun q => ∀ p ∈ q.primeFactors, p ≤ Y),
      min (1 : ℝ) ((q : ℝ) / Q) / (q.totient : ℝ)) ≤
    (Q : ℝ)^(-(1/32:ℝ)) *
      (∑ a ∈ (Icc 1 (Q^2)).filter (fun a => ∀ p ∈ a.primeFactors, p ≤ Y),
        (a:ℝ)^((1/32:ℝ)-1))^2 := by
  classical
  let S := (Icc 1 (Q^2)).filter (fun q => ∀ p ∈ q.primeFactors, p ≤ Y)
  let w (a : ℕ) := (a:ℝ)^((1/32:ℝ)-1)
  let F (ab : ℕ × ℕ) := w ab.1 * w ab.2
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have w_nonneg (a : ℕ) : 0 ≤ w a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsingle (q : ℕ) (hq : q ∈ S) :
      min (1 : ℝ) ((q : ℝ)/Q) / (q.totient : ℝ) ≤
      (Q : ℝ)^(-(1/32:ℝ)) * ∑ ab ∈ q.divisorsAntidiagonal, F ab := by
    have hq0 : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
    have hsum : (∑ ab ∈ q.divisorsAntidiagonal, F ab) = (q.divisors.card : ℝ) * w q := by
      calc
        _ = ∑ _ab ∈ q.divisorsAntidiagonal, w q := by
          apply sum_congr rfl
          intro ab hab
          unfold F w
          rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
            ← Nat.cast_mul, (Nat.mem_divisorsAntidiagonal.mp hab).1]
        _ = _ := by
          rw [Nat.sum_divisorsAntidiagonal (fun _ _ => w q)]
          simp
    rw [hsum]
    calc
      min (1 : ℝ) ((q : ℝ)/Q) / (q.totient : ℝ) ≤
          ((q : ℝ)/Q)^(1/32:ℝ) * (1/(q.totient : ℝ)) := by
            rw [mul_one_div]
            exact div_le_div_of_nonneg_right (rankin_min _ (div_pos hqr hQR)) (Nat.cast_nonneg _)
      _ ≤ ((q : ℝ)/Q)^(1/32:ℝ) * ((q.divisors.card : ℝ)/q) :=
        mul_le_mul_of_nonneg_left (reciprocal_totient q hq0) (Real.rpow_nonneg (div_pos hqr hQR).le _)
      _ = _ := by
        rw [Real.div_rpow hqr.le hQR.le, Real.rpow_neg hQR.le]
        simp only [w, Real.rpow_sub hqr, Real.rpow_one]
        ring
  have hdisj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Disjoint a.divisorsAntidiagonal b.divisorsAntidiagonal := by
    intro a _ b _ hab
    apply disjoint_left.mpr
    intro ab ha hb
    exact hab ((Nat.mem_divisorsAntidiagonal.mp ha).1.symm.trans (Nat.mem_divisorsAntidiagonal.mp hb).1)
  have hsub : S.biUnion Nat.divisorsAntidiagonal ⊆ S ×ˢ S := by
    intro ab hab
    obtain ⟨q, hq, habq⟩ := mem_biUnion.mp hab
    obtain ⟨hqI,hqS⟩ := mem_filter.mp hq
    obtain ⟨hqpos,hqle⟩ := mem_Icc.mp hqI
    have hd (d : ℕ) (hdq : d ∈ q.divisors) : d ∈ S := by
      have hdiv := Nat.dvd_of_mem_divisors hdq
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdq, ?_⟩, ?_⟩
      · exact (Nat.le_of_dvd hqpos hdiv).trans hqle
      · exact fun p hp => hqS p (Nat.primeFactors_mono hdiv (by omega) hp)
    exact mem_product.mpr ⟨hd _ (Nat.fst_mem_divisors_of_mem_antidiagonal habq),
      hd _ (Nat.snd_mem_divisors_of_mem_antidiagonal habq)⟩
  change (∑ q ∈ S, _) ≤ (Q : ℝ)^(-(1/32:ℝ)) * (∑ a ∈ S, w a)^2
  calc
    _ ≤ ∑ q ∈ S, (Q : ℝ)^(-(1/32:ℝ)) * ∑ ab ∈ q.divisorsAntidiagonal, F ab :=
      sum_le_sum hsingle
    _ = (Q : ℝ)^(-(1/32:ℝ)) * ∑ ab ∈ S.biUnion Nat.divisorsAntidiagonal, F ab := by
      rw [← mul_sum, sum_biUnion hdisj]
    _ ≤ (Q : ℝ)^(-(1/32:ℝ)) * ∑ ab ∈ S ×ˢ S, F ab := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      apply sum_le_sum_of_subset_of_nonneg hsub
      exact fun ab _ _ => mul_nonneg (w_nonneg ab.1) (w_nonneg ab.2)
    _ = _ := by
      congr 1
      rw [Finset.sum_product, sq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]

private noncomputable def rankinWeight : ℕ →* ℝ where
  toFun m := (m : ℝ) ^ ((1 / 32 : ℝ) - 1)
  map_one' := by simp
  map_mul' a b := by rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

theorem finite_smooth_weight_le_product (y : ℕ) (S : Finset ℕ)
    (hS : ∀ m ∈ S, m ∈ Nat.smoothNumbers (y + 1)) :
    (∑ m ∈ S, (m : ℝ) ^ ((1 / 32 : ℝ) - 1)) ≤
      ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ) ^ ((1 / 32 : ℝ) - 1))⁻¹ := by
  classical
  have hin : ∀ {p : ℕ}, p.Prime → ‖rankinWeight p‖ < 1 := by
    intro p hp
    change ‖(p : ℝ) ^ ((1 / 32 : ℝ) - 1)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by norm_num)
  have hs := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := rankinWeight) hin (y + 1)).2
  change (∑ m ∈ S, rankinWeight m) ≤ _
  rw [← S.sum_subtype_of_mem (fun m => rankinWeight m) hS]
  exact sum_le_hasSum _ (fun m _ => Real.rpow_nonneg (Nat.cast_nonneg (m : ℕ)) _) hs

theorem smooth_interval_weight_le_product (y N : ℕ) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m => ∀ p ∈ m.primeFactors, p ≤ y),
        (m : ℝ) ^ ((1 / 32 : ℝ) - 1)) ≤
      ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ) ^ ((1 / 32 : ℝ) - 1))⁻¹ := by
  apply finite_smooth_weight_le_product
  intro m hm
  obtain ⟨hrange, hfactors⟩ := Finset.mem_filter.mp hm
  have hmpos := (Finset.mem_Icc.mp hrange).1
  apply Nat.mem_smoothNumbers'.2
  intro p hp hpm
  exact Nat.lt_succ_of_le (hfactors p (Nat.mem_primeFactors.mpr ⟨hp, hpm, by omega⟩))

private theorem factor_bound {p : ℕ} (hp : Nat.Prime p) :
    let t := (p : ℝ)^((1/32:ℝ)-1)
    0 < 1-t ∧ (1-t)⁻¹ ≤ Real.exp (4*t) := by
  let t := (p : ℝ)^((1/32:ℝ)-1)
  change 0 < 1-t ∧ _
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ) < p := by linarith
  have ht0 : 0 ≤ t := Real.rpow_nonneg hp0.le _
  have ht2 : t*t ≤ (p:ℝ)⁻¹ := by
    dsimp [t]
    rw [← Real.rpow_add hp0, ← Real.rpow_neg_one]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    norm_num
  have hinv : (p:ℝ)⁻¹ ≤ 1/2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hp2
  have h34 : t ≤ 3/4 := by nlinarith
  have hpos : 0 < 1-t := by linarith
  refine ⟨hpos, le_trans ?_ (Real.add_one_le_exp (4*t))⟩
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  nlinarith [mul_nonneg ht0 (show 0 ≤ 3-4*t by linarith)]

/-- Compare the logarithm of the Euler product with a weighted harmonic sum. -/
theorem eulerProduct_le (y : ℕ) (hy : 1 ≤ y) :
    (∏ p ∈ (y+1).primesBelow, (1 - (p:ℝ)^((1/32:ℝ)-1))⁻¹) ≤
      Real.exp (500 * (y:ℝ)^(1/16:ℝ)) := by
  let P := (y+1).primesBelow
  let t (p : ℕ) := (p:ℝ)^((1/32:ℝ)-1)
  have hsub : P ⊆ Icc 1 y := by
    intro p hp
    obtain ⟨hpy,hpp⟩ := Nat.mem_primesBelow.mp hp
    exact mem_Icc.mpr ⟨hpp.one_le, Nat.le_of_lt_succ hpy⟩
  have hy1 : (1:ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0:ℝ) < y := by linarith
  have hpow : 0 ≤ (y:ℝ)^(1/32:ℝ) := Real.rpow_nonneg hy0.le _
  have hlog : 1 + Real.log (y:ℝ) ≤ 32 * (y:ℝ)^(1/32:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy0 (1/32:ℝ))
    rw [Real.log_rpow hy0] at h
    linarith
  have hs : (∑ p ∈ P, t p) ≤ 32 * (y:ℝ)^(1/16:ℝ) := by
    calc
      _ ≤ ∑ p ∈ P, (y:ℝ)^(1/32:ℝ) * (p:ℝ)⁻¹ := by
        apply sum_le_sum
        intro p hp
        have hpy : p ≤ y := (mem_Icc.mp (hsub hp)).2
        have hp0 : (0:ℝ) < p := by exact_mod_cast (mem_Icc.mp (hsub hp)).1
        dsimp only [t]
        rw [Real.rpow_sub hp0, Real.rpow_one, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hp0.le (by exact_mod_cast hpy) (by norm_num)) (inv_nonneg.mpr hp0.le)
      _ = (y:ℝ)^(1/32:ℝ) * ∑ p ∈ P, (p:ℝ)⁻¹ := (mul_sum ..).symm
      _ ≤ (y:ℝ)^(1/32:ℝ) * ∑ p ∈ Icc 1 y, (p:ℝ)⁻¹ := by
        exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)) hpow
      _ ≤ (y:ℝ)^(1/32:ℝ) * (1+Real.log (y:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hpow
        simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using harmonic_le_one_add_log y
      _ ≤ (y:ℝ)^(1/32:ℝ) * (32*(y:ℝ)^(1/32:ℝ)) := mul_le_mul_of_nonneg_left hlog hpow
      _ = 32 * (y:ℝ)^(1/16:ℝ) := by
        rw [show (1/16:ℝ)=1/32+1/32 by norm_num, Real.rpow_add hy0]; ring
  calc
    _ ≤ ∏ p ∈ P, Real.exp (4*t p) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact inv_nonneg.mpr (factor_bound (Nat.prime_of_mem_primesBelow hp)).1.le
      · intro p hp
        exact (factor_bound (Nat.prime_of_mem_primesBelow hp)).2
    _ = Real.exp (4*∑ p ∈ P, t p) := by rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      linarith [Real.rpow_nonneg hy0.le (1/16:ℝ)]

/-- Exponential growth of Q in its binary logarithm absorbs the three-quarter-power
growth in the exponent of the smooth Euler product. -/
theorem eventual_rankin_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      let Q : ℕ := (Nat.log 2 (n + 2)) ^ 2
      let Y : ℕ := (1 + Nat.log 2 Q) ^ 12
      (Q : ℝ) ^ (-(1 / 32 : ℝ)) *
        (Real.exp (500 * (Y : ℝ) ^ (1 / 16 : ℝ))) ^ 2 ≤ ε := by
  obtain ⟨t, ht⟩ := Filter.eventually_atTop.mp ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).eventually_ge_atTop 128000)
  obtain ⟨b, hb⟩ := exists_nat_ge (max t (128 * (1 - Real.log ε)))
  refine ⟨2 ^ (2 ^ b), fun n hn => ?_⟩
  let L := Nat.log 2 (n + 2)
  let Q : ℕ := L ^ 2
  let k := Nat.log 2 Q
  have hLb : 2 ^ b ≤ L :=
    Nat.le_log_of_pow_le (by decide) (hn.trans (by omega))
  have hL : 1 ≤ L := (Nat.one_le_two_pow (n := b)).trans hLb
  have hQ : L ≤ Q := by dsimp [Q]; nlinarith
  have hk : b ≤ k := Nat.le_log_of_pow_le (by decide) (hLb.trans hQ)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hdyadic : (2 : ℝ) ^ k ≤ Q := by
    exact_mod_cast Nat.pow_log_le_self 2 (show Q ≠ 0 by omega)
  have hlog := Real.log_le_log (by positivity) hdyadic
  rw [Real.log_pow] at hlog
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hklog : (k : ℝ) / 2 ≤ Real.log Q := by
    calc
      (k : ℝ) / 2 = (k : ℝ) * (1 / 2) := by ring
      _ ≤ (k : ℝ) * Real.log 2 := by gcongr
      _ ≤ Real.log Q := hlog
  have hrpow : ((((1 + k)^12 : ℕ) : ℝ) ^ (1 / 16 : ℝ)) =
      (1 + (k : ℝ))^(3/4:ℝ) := by
    push_cast
    rw [← Real.rpow_natCast_mul (by positivity)]
    norm_num
  change (Q : ℝ) ^ (-(1 / 32 : ℝ)) *
    (Real.exp (500 * ((((1 + k)^12 : ℕ) : ℝ) ^ (1 / 16 : ℝ)))) ^ 2 ≤ ε
  rw [hrpow, Real.rpow_def_of_pos hQpos, sq, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_log hε, Real.exp_le_exp]
  have hb' : (b : ℝ) ≤ k := by exact_mod_cast hk
  have hkt : t ≤ 1 + (k:ℝ) := by linarith [(le_max_left ..).trans hb]
  have hlarge := ht (1 + (k:ℝ)) hkt
  have hprod := mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg (by positivity : 0 ≤ 1+(k:ℝ)) (3/4:ℝ))
  change (1+(k:ℝ))^(3/4:ℝ)*128000 ≤ (1+(k:ℝ))^(3/4:ℝ)*(1+(k:ℝ))^(1/4:ℝ) at hprod
  rw [← Real.rpow_add (by positivity), show (3/4:ℝ)+1/4=1 by norm_num, Real.rpow_one] at hprod
  linarith [(le_max_right ..).trans hb]

end GoldbachSmoothModuli

private theorem smoothDenominatorWeightRaw :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let smooth := fun n q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^12; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => smooth n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ))/(Nat.totient q:ℝ)) ≤ ε := by
  dsimp only
  intro ε hε
  obtain ⟨N, hN⟩ := GoldbachSmoothModuli.eventual_rankin_budget ε hε
  refine ⟨N, fun n hn => ?_⟩
  let Q : ℕ := (Nat.log 2 (n + 2)) ^ 2
  let Y : ℕ := (1 + Nat.log 2 Q) ^ 12
  have hlog : 1 ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have hQ : 1 ≤ Q := Nat.pow_pos hlog
  have hY : 1 ≤ Y := Nat.pow_pos (by omega : 0 < 1 + Nat.log 2 Q)
  have he := (GoldbachSmoothModuli.smooth_interval_weight_le_product Y (Q^2)).trans
    (GoldbachSmoothModuli.eulerProduct_le Y hY)
  refine (GoldbachSmoothModuli.smooth_convolution_bound Q Y hQ).trans (le_trans ?_ (hN n hn))
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg Q) _)
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (Nat.cast_nonneg a) _)) he 2



theorem smooth_budget : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    (∑ q ∈ (Icc 1 ((grid n)^2)).filter (smooth n), weight n q) ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := smoothDenominatorWeightRaw ε hε
  refine ⟨N, fun n hn => ?_⟩
  apply le_trans _ (hN n hn)
  apply le_of_eq
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext q
  simp only [mem_filter, smooth, u, grid]

theorem periodPrimeBudget (H Y : ℕ) (hY : 0<Y) :
    (∑ j ∈ Finset.Icc 1 H, ∑ p ∈ ((2^j-1:ℕ).primeFactors.filter (fun p => Y<p)),
      1/((p:ℝ)-1)) ≤ (H:ℝ)^2/Y := by
  have one (j : ℕ) (hj : j ∈ Finset.Icc 1 H) :
      (∑ p ∈ ((2^j-1:ℕ).primeFactors.filter (fun p => Y<p)), 1/((p:ℝ)-1)) ≤ (H:ℝ)/(Y:ℝ) := by
    let M : ℕ := 2^j-1
    let primes := M.primeFactors
    let T := primes.filter (fun p => Y<p)
    have jpos := (Finset.mem_Icc.mp hj).1
    have jle := (Finset.mem_Icc.mp hj).2
    have Mpos : 0<M := by
      have two : 2 ≤ 2^j := by simpa using Nat.pow_le_pow_right (by decide : 0<2) jpos
      dsimp [M]; omega
    have hc : 2^primes.card ≤ M := by
      calc
        _ = ∏ _p ∈ primes, (2:ℕ) := by simp
        _ ≤ ∏ p ∈ primes, p := Finset.prod_le_prod (fun p h => (Nat.prime_of_mem_primeFactors h).two_le)
        _ ≤ M := Nat.le_of_dvd Mpos (Nat.prod_primeFactors_dvd M)
    have card : primes.card ≤ j := by
      by_contra! hh
      have lower := Nat.pow_le_pow_right (by decide : 0<2) (show j+1 ≤ primes.card by omega)
      rw [pow_succ] at lower
      dsimp [M] at hc
      omega
    have cr : (T.card:ℝ) ≤ (H:ℝ) := by exact_mod_cast
      ((Finset.card_le_card (Finset.filter_subset _ primes)).trans card).trans jle
    change (∑ p ∈ T, _) ≤ _
    calc
      _ ≤ ∑ _p ∈ T, 1/(Y:ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hi : (Y:ℝ)+1 ≤ (p:ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = (T.card:ℝ)/(Y:ℝ) := by simp [div_eq_mul_inv]
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 H, (H:ℝ)/(Y:ℝ) := Finset.sum_le_sum one
    _ = _ := by simp [pow_two]; ring


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

theorem totientLogLower (q : ℕ) (hq : 0<q) :
    (q:ℝ)/(q.totient:ℝ) ≤ (Nat.log 2 q:ℝ)+1 := by
  let S := q.primeFactors
  have hs (p : ℕ) (hp : p∈S) := (Nat.prime_of_mem_primeFactors hp).two_le
  have card : S.card ≤ Nat.log 2 q := by
    apply Nat.le_log_of_pow_le (by decide)
    calc
      _ = ∏ _p ∈ S, (2:ℕ) := by simp
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod hs
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

private theorem harmonicBlock (k : ℕ) :
    (∑ m ∈ Finset.range (2^k), 1/((m:ℝ)+1)) ≤ (k:ℝ)+1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
    have block : (∑ j ∈ Finset.range (2^k), 1/(((2^k+j:ℕ):ℝ)+1)) ≤ 1 := by
      calc
        _ ≤ ∑ _j ∈ Finset.range (2^k), 1/((2:ℝ)^k) := by
          apply Finset.sum_le_sum
          intro j _
          apply one_div_le_one_div_of_le (by positivity)
          push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]
        _ = _ := by simp
    push_cast at block ⊢
    linarith only [ih,block]

theorem reciprocalTotientLogBound (X : ℕ) (_ : 0<X) :
    (∑ m ∈ Finset.Icc 1 X, 1/(m.totient:ℝ)) ≤ ((Nat.log 2 X:ℝ)+2)^2 := by
  let k := Nat.log 2 X
  have idx : Finset.Icc 1 X = (Finset.range X).map (addRightEmbedding 1) := by
    ext m
    simp only [Finset.mem_Icc,Finset.mem_map,Finset.mem_range,addRightEmbedding_apply]
    constructor
    · intro h; exact ⟨m-1,by omega,by omega⟩
    · rintro ⟨j,h,rfl⟩; omega
  have upper := (Nat.lt_pow_succ_log_self (by decide : 1<2) X).le
  have harm : (∑ m ∈ Finset.range X, 1/((m:ℝ)+1)) ≤ (k:ℝ)+2 := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono upper) (fun m _ _ => by positivity)).trans
    convert harmonicBlock (k+1) using 1; push_cast; ring
  rw [idx,Finset.sum_map]
  calc
    _ ≤ ∑ j ∈ Finset.range X, ((k:ℝ)+1)*(1/((j:ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have le : j+1 ≤ X := Finset.mem_range.mp hj
      have hk : Nat.log 2 (j+1) ≤ k := Nat.log_mono_right le
      have b := totientLogLower (j+1) (by omega)
      have h : (((j+1:ℕ):ℝ)/((j+1).totient:ℝ)) ≤ (k:ℝ)+1 := b.trans (by exact_mod_cast (Nat.add_le_add_right hk 1))
      change 1/((j+1).totient:ℝ) ≤ _
      rw [mul_one_div]
      apply (le_div_iff₀ (by positivity)).mpr
      push_cast at h
      simpa only [one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm] using h
    _ = ((k:ℝ)+1)*_ := (Finset.mul_sum ..).symm
    _ ≤ ((k:ℝ)+1)*((k:ℝ)+2) := mul_le_mul_of_nonneg_left harm (by positivity)
    _ ≤ _ := by dsimp [k]; nlinarith only [Nat.cast_nonneg (α := ℝ) (Nat.log 2 X)]


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
      simpa only [e,ite_true] using Finset.single_le_sum
        (s := T) (f := fun x => if key x=b then v x else 0)
        (fun x hx => by split <;> first | exact pos x hx | exact le_rfl) ha
    _ = ∑ a ∈ T, ∑ b ∈ S, if key a=b then v a else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : key a ∈ S <;> simp [h,pos a ha]

private theorem largePeriodWeightFinite (n : ℕ) :
    (∑ q ∈ (Finset.Icc 1 ((grid n)^2)).filter (shortLarge n),
      weight n q) ≤
      (∑ m ∈ Finset.Icc 1 ((grid n)^2), 1/(m.totient:ℝ)) *
        (((1+Nat.log 2 (grid n):ℕ):ℝ)^8 / ((1+Nat.log 2 (grid n):ℕ):ℝ)^12) := by
  classical
  let u := 1+Nat.log 2 (grid n)
  let H := u^4
  let Y := u^12
  let X := (grid n)^2
  let D := Finset.Icc 1 X
  let J := Finset.Icc 1 H
  let Ps := fun j : ℕ => (2^j-1:ℕ).primeFactors.filter (fun p => Y<p)
  let T : Finset (Σ _j : ℕ, ℕ × ℕ) := J.sigma (fun j => Ps j ×ˢ D)
  let S := D.filter (shortLarge n)
  let v := fun a : (Σ _j : ℕ, ℕ × ℕ) => (1/((a.2.1:ℝ)-1))*(1/(a.2.2.totient:ℝ))
  let M := ∑ m ∈ D, 1/(m.totient:ℝ)
  have vpos (a : Σ _j : ℕ, ℕ × ℕ) (ha : a∈T) : 0≤v a := by
    have h := (Finset.mem_product.mp (Finset.mem_sigma.mp ha).2).1
    have hp := (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp h).1).two_le
    have hp' : (2:ℝ)≤a.2.1 := by exact_mod_cast hp
    exact mul_nonneg (one_div_nonneg.mpr (by linarith)) (one_div_nonneg.mpr (Nat.cast_nonneg _))
  have witnesses (q : ℕ) (hq : q∈S) : ∃ a∈T, a.2.1*a.2.2=q ∧ weight n q≤v a := by
    obtain ⟨hd,p,hp,hY,j,hj',dvd⟩ := Finset.mem_filter.mp hq
    have pPrime := Nat.prime_of_mem_primeFactors hp
    have dp := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨m,eq⟩ := dp
    have qpos : 0<q := (Finset.mem_Icc.mp hd).1
    have mpos : 0< m := Nat.pos_of_ne_zero (fun e => (Nat.ne_of_gt qpos) (by simp [eq,e]))
    have mQ : m≤q := Nat.le_of_dvd qpos ⟨p,by simpa only [mul_comm] using eq⟩
    have hpos : 0<(2^j-1:ℕ) := by
      have two : 2≤2^j := by simpa using Nat.pow_le_pow_right (by decide : 0<2) (Finset.mem_Icc.mp hj').1
      omega
    have pm : p∈Ps j := Finset.mem_filter.mpr ⟨pPrime.mem_primeFactors dvd hpos.ne',hY⟩
    refine ⟨⟨j,(p,m)⟩, Finset.mem_sigma.mpr ⟨hj', Finset.mem_product.mpr ⟨pm,Finset.mem_Icc.mpr ⟨mpos,mQ.trans (Finset.mem_Icc.mp hd).2⟩⟩⟩,eq.symm, ?_⟩
    have phip : 0<(p.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr pPrime.pos
    have phim : 0<(m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr mpos
    have phi : (p.totient:ℝ)*(m.totient:ℝ) ≤ (q.totient:ℝ) := by rw [eq]; exact_mod_cast Nat.totient_super_multiplicative p m
    have phiq : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr qpos
    have primeId : (p.totient:ℝ)=(p:ℝ)-1 := by
      rw [Nat.totient_prime pPrime,Nat.cast_sub (by have := pPrime.two_le; omega),Nat.cast_one]
    calc
      _ ≤ 1/(q.totient:ℝ) := div_le_div_of_nonneg_right (min_le_left ..) phiq.le
      _ ≤ 1/((p.totient:ℝ)*(m.totient:ℝ)) := one_div_le_one_div_of_le (mul_pos phip phim) phi
      _ = _ := by dsimp [v]; rw [primeId]; simp only [one_div,mul_inv_rev,mul_comm]
  have eq : (∑ a ∈ T, v a) = M*(∑ j ∈ J, ∑ p ∈ Ps j, 1/((p:ℝ)-1)) := by
    dsimp only [T]
    rw [Finset.sum_sigma,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_product,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [v]
    rw [← Finset.mul_sum,mul_comm]
  have ub := periodPrimeBudget H Y (by dsimp [H,Y,u]; positivity)
  have conv : (H:ℝ)^2/(Y:ℝ) = (u:ℝ)^8/(u:ℝ)^12 := by dsimp [H,Y]; push_cast; ring
  rw [conv] at ub
  apply (chargeWitnesses S T (fun a => a.2.1*a.2.2) (weight n) v vpos witnesses).trans
  rw [eq]
  exact mul_le_mul_of_nonneg_left ub (Finset.sum_nonneg fun _ _ => by positivity)

theorem shortLarge_budget : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
    (∑ q ∈ (Finset.Icc 1 ((grid n)^2)).filter (shortLarge n),
      weight n q) ≤ ε := by
  intro ε hε
  obtain ⟨M,hM⟩ := exists_nat_ge (16/ε)
  refine ⟨2^(2^M), ?_⟩
  intro n hn
  let Q := grid n
  let u := 1+Nat.log 2 Q
  have hlog : 2^M ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have hQ : 2^M ≤ Q := by dsimp [Q,grid]; nlinarith [Nat.le_mul_self (Nat.log 2 (n+2))]
  have qpos : 0<Q := lt_of_lt_of_le (by positivity : 0<2^M) hQ
  have hu : M ≤ u := by have h := Nat.le_log_of_pow_le (by decide : 1<2) hQ; dsimp [u]; omega
  have u1 : (1:ℝ) ≤ u := by exact_mod_cast (show 1≤u by dsimp [u]; omega)
  have upos : (0:ℝ)<u := by linarith
  have cap := Nat.lt_pow_succ_log_self (by decide : 1<2) Q
  have cap' : Q < 2^u := by simpa only [u,Nat.add_comm 1] using cap
  have both : Q^2 < 2^(2*u) := by
    rw [mul_comm 2 u,pow_mul]
    exact Nat.pow_lt_pow_left cap' (by decide)
  have hL : Nat.log 2 (Q^2) < 2*u := by
    by_contra! hh
    have power := Nat.pow_le_pow_right (by decide : 0<2) hh
    have b := Nat.pow_log_le_self 2 (by positivity : Q^2≠0)
    omega
  have hR : (Nat.log 2 (Q^2):ℝ)+2 ≤ 4*(u:ℝ) := by exact_mod_cast (show Nat.log 2 (Q^2)+2≤4*u by omega)
  have hb := (reciprocalTotientLogBound (Q^2) (by positivity)).trans (pow_le_pow_left₀ (by positivity) hR 2)
  apply (largePeriodWeightFinite n).trans
  change _ * ((u:ℝ)^8/(u:ℝ)^12) ≤ ε
  apply (mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ (u:ℝ)^8/(u:ℝ)^12)).trans
  have limit : 16 ≤ ε*(u:ℝ) := by
    have h := (div_le_iff₀ hε).mp (hM.trans (by exact_mod_cast hu : (M:ℝ) ≤ u))
    linarith
  calc
    _ = 16/(u:ℝ)^2 := by field_simp; ring
    _ ≤ 16/(u:ℝ) := div_le_div_of_nonneg_left (by norm_num) upos (by nlinarith [sq_nonneg ((u:ℝ)-1)])
    _ ≤ ε := (div_le_iff₀ upos).mpr limit


end GB4Bad

/-! The singular-factor second moment is adapted from goldbach-proofs,
`BeaumontScaledDeletionSurvival.lean` (Apache 2.0). -/
namespace GB4Totient
open Finset

private def oddFactors (n : ℕ) : Finset ℕ := n.primeFactors.filter (2 < ·)

private noncomputable def singular (n : ℕ) : ℝ :=
  ∏ p ∈ oddFactors n, (1 + 1 / ((p : ℝ) - 2))

private noncomputable def increment (p : ℕ) : ℝ := (1 + 1 / ((p : ℝ) - 2))^2 - 1

private theorem increment_nonneg {p : ℕ} (hp : 3 ≤ p) : 0 ≤ increment p := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h : 0 ≤ 1 / ((p : ℝ) - 2) := div_nonneg zero_le_one (by linarith)
  unfold increment
  nlinarith [sq_nonneg (1 / ((p : ℝ) - 2))]

/-- A telescoping rational product bounds the averaged Euler factors at integers from 5 onwards. -/
private theorem tail_product (N : ℕ) (hN : 4 ≤ N) :
    ∏ p ∈ Icc 5 N, (1 + increment p / (p : ℝ)) ≤ 2 * ((N : ℝ) - 2) / N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hI : Icc 5 (k + 1) = insert (k + 1) (Icc 5 k) := by
      ext j
      simp only [mem_Icc, mem_insert]
      omega
    rw [hI, prod_insert (by simp)]
    have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
    have hinc := increment_nonneg (p := k + 1) (by omega)
    calc
      _ ≤ (1 + increment (k+1) / ((k+1 : ℕ) : ℝ)) * (2 * ((k : ℝ) - 2) / k) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ _ := by
        simp only [increment, Nat.cast_succ]
        rw [show (k : ℝ) + 1 - 2 = (k : ℝ) - 1 by ring]
        have h0 : (k : ℝ) ≠ 0 := by linarith
        have h1 : (k : ℝ) - 1 ≠ 0 := by linarith
        have h2 : (k : ℝ) + 1 ≠ 0 := by linarith
        calc
          _ = 2 * ((k : ℝ) - 1) / (k + 1) - 2 / ((k + 1) * (k - 1 : ℝ)^2) := by
            field_simp [h0, h1, h2]
            ring
          _ ≤ _ := sub_le_self _ (by positivity)

/-- Every odd prime factor of a positive integer at most `M` is 3 or lies in this tail. -/
private def candidates (M : ℕ) : Finset ℕ := insert 3 (Icc 5 (M+4))

private theorem candidates_ge_three {M p : ℕ} (hp : p ∈ candidates M) : 3 ≤ p := by
  rcases mem_insert.mp hp with rfl | hp
  · decide
  · have := (mem_Icc.mp hp).1
    omega

private theorem candidates_product (M : ℕ) :
    ∏ p ∈ candidates M, (1 + increment p / (p : ℝ)) ≤ 4 := by
  have htail := tail_product (M+4) (by omega)
  have hpos : (0 : ℝ) < (M+4 : ℕ) := by positivity
  have hbound : 2 * (((M+4 : ℕ) : ℝ) - 2) / (M+4 : ℕ) ≤ 2 :=
    (div_le_iff₀ hpos).mpr (by linarith)
  rw [candidates, prod_insert (by simp)]
  have hthree : 1 + increment 3 / (3 : ℝ) = 2 := by norm_num [increment]
  change (1 + increment 3 / (3 : ℝ)) * _ ≤ 4
  rw [hthree]
  linarith [htail.trans hbound]

private theorem oddFactors_subset {M n : ℕ} (hn : n ≤ M) : oddFactors n ⊆ candidates M := by
  intro p hp
  obtain ⟨hdiv, hodd⟩ := mem_filter.mp hp
  have hpN := Nat.le_of_mem_primeFactors hdiv
  have hfour : p ≠ 4 := by
    rintro rfl
    exact (by decide : ¬ Nat.Prime 4) (Nat.prime_of_mem_primeFactors hdiv)
  by_cases h : p = 3
  · exact mem_insert.mpr (Or.inl h)
  · exact mem_insert.mpr (Or.inr (mem_Icc.mpr ⟨by omega, by omega⟩))

private def divisorProduct (t : Finset ℕ) : ℕ := ∏ p ∈ t, p

private noncomputable def subsetWeight (t : Finset ℕ) : ℝ := ∏ p ∈ t, increment p

/-- A subset of the odd prime factors contributes only at multiples of its product. -/
private theorem square_le_divisor_sum {n M : ℕ} (hn : n ≤ M) :
    singular n ^ 2 ≤ ∑ t ∈ (candidates M).powerset,
      if divisorProduct t ∣ n then subsetWeight t else 0 := by
  classical
  let A := oddFactors n
  have hdiv (t : Finset ℕ) (ht : t ∈ A.powerset) : divisorProduct t ∣ n := by
    have hsub : t ⊆ n.primeFactors :=
      (mem_powerset.mp ht).trans (filter_subset _ _)
    exact (Finset.prod_dvd_prod_of_subset t n.primeFactors id hsub).trans n.prod_primeFactors_dvd
  calc
    singular n ^ 2 = ∏ p ∈ A, (1 + increment p) := by
      unfold singular
      rw [← Finset.prod_pow]
      apply prod_congr rfl
      intro p _
      dsimp [increment]
      ring
    _ = ∑ t ∈ A.powerset, subsetWeight t := Finset.prod_one_add A
    _ = ∑ t ∈ A.powerset, if divisorProduct t ∣ n then subsetWeight t else 0 := by
      exact sum_congr rfl fun t ht ↦ (ite_eq_left (hdiv t ht)).symm
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact fun t ht ↦ mem_powerset.mpr ((mem_powerset.mp ht).trans (oddFactors_subset hn))
      · intro t ht _
        split_ifs
        · exact prod_nonneg fun p hp ↦ increment_nonneg (candidates_ge_three (mem_powerset.mp ht hp))
        · exact le_rfl

private theorem multiples_count (M d : ℕ) : ((Icc 1 M).filter (fun n ↦ d ∣ n)).card = M / d := by
  have sets : (Icc 1 M).filter (fun n ↦ d ∣ n) = (range M.succ).filter (fun n ↦ n ≠ 0 ∧ d ∣ n) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_range]
    omega
  rw [sets, Nat.card_multiples']

/-- Average the expanded factors using the exact count `M / d` of positive multiples. -/
private theorem prefix_square (M : ℕ) : (∑ n ∈ Icc 1 M, singular n ^ 2) ≤ 4*(M : ℝ) := by
  classical
  let P := candidates M
  calc
    (∑ n ∈ Icc 1 M, singular n ^ 2) ≤ ∑ n ∈ Icc 1 M, ∑ t ∈ P.powerset,
        if divisorProduct t ∣ n then subsetWeight t else 0 :=
      sum_le_sum fun n hn ↦ square_le_divisor_sum (mem_Icc.mp hn).2
    _ = ∑ t ∈ P.powerset, ∑ n ∈ Icc 1 M,
        if divisorProduct t ∣ n then subsetWeight t else 0 := Finset.sum_comm
    _ ≤ ∑ t ∈ P.powerset, (M : ℝ) * (∏ p ∈ t, increment p / (p : ℝ)) := by
      apply sum_le_sum
      intro t ht
      have hw : 0 ≤ subsetWeight t := prod_nonneg fun p hp ↦
        increment_nonneg (candidates_ge_three (mem_powerset.mp ht hp))
      rw [← sum_filter, sum_const, multiples_count, nsmul_eq_mul]
      calc
        _ ≤ ((M : ℝ) / (divisorProduct t : ℝ)) * subsetWeight t :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le hw
        _ = _ := by
          rw [Finset.prod_div_distrib]
          simp only [divisorProduct, Nat.cast_prod, subsetWeight]
          ring
    _ = (M : ℝ) * ∏ p ∈ P, (1 + increment p / (p : ℝ)) := by
      rw [← Finset.mul_sum, Finset.prod_one_add]
    _ ≤ 4 * (M : ℝ) := by
      rw [mul_comm (4 : ℝ)]
      exact mul_le_mul_of_nonneg_left (candidates_product M) (Nat.cast_nonneg _)


private theorem singular_nonneg (q : ℕ) : 0 ≤ singular q := by
  apply Finset.prod_nonneg
  intro p hp
  have hp' : (2:ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
  positivity

private theorem ratio_le (q : ℕ) (hq : 0 < q) :
    (q:ℝ)/(q.totient:ℝ) ≤ 2*singular q := by
  classical
  let F (p : ℕ) := (p:ℝ)/((p:ℝ)-1)
  let O := oddFactors q
  have hfac : (q:ℝ)/(q.totient:ℝ) = ∏ p ∈ q.primeFactors, F p := by
    have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
    have hP1 : 0 < ∏ p ∈ q.primeFactors, ((p:ℝ)-1) := by
      apply Finset.prod_pos
      intro p hp
      have hh : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      linarith
    have hid := congrArg (fun x : ℕ => (x : ℝ)) (Nat.totient_mul_prod_primeFactors q)
    simp only [Nat.cast_mul, Nat.cast_prod] at hid
    have he : ∏ p ∈ q.primeFactors, ((p-1:ℕ):ℝ) = ∏ p ∈ q.primeFactors, ((p:ℝ)-1) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
    rw [he] at hid
    dsimp only [F]
    rw [Finset.prod_div_distrib, div_eq_div_iff hφ.ne' hP1.ne']
    linarith
  have hoff : (∏ p ∈ O, F p) ≤ singular q := by
    apply Finset.prod_le_prod₀
    · intro p hp
      have hp' : (2:ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)
    · intro p hp
      have hp' : (2:ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
      dsimp [F]
      field_simp [show (0:ℝ)<p-2 by linarith,show (0:ℝ)<p-1 by linarith]
      nlinarith
  rw [hfac]
  by_cases h : 2 ∈ q.primeFactors
  · have ho : q.primeFactors = insert 2 O := by
      ext p
      change p ∈ q.primeFactors ↔ p ∈ insert 2 (q.primeFactors.filter (2 < ·))
      simp only [Finset.mem_insert, Finset.mem_filter]
      constructor
      · intro hp
        have := (Nat.prime_of_mem_primeFactors hp).two_le
        by_cases he:p=2
        · exact Or.inl he
        · exact Or.inr ⟨hp,by omega⟩
      · rintro (rfl | ⟨hp,_⟩) <;> assumption
    have h2 : 2 ∉ O := by simp [O,oddFactors]
    rw [ho, Finset.prod_insert h2]
    have hf : F 2 = 2 := by norm_num [F]
    rw [hf]
    linarith
  · have ho : q.primeFactors = O := by
      ext p
      change p ∈ q.primeFactors ↔ p ∈ q.primeFactors.filter (2 < ·)
      simp only [Finset.mem_filter, iff_self_and]
      intro hp
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      have hh : p ≠ 2 := by rintro rfl; contradiction
      omega
    rw [ho]
    linarith [singular_nonneg q]

private noncomputable def w (q : ℕ) : ℝ := (q:ℝ)/(q.totient:ℝ)^2

private theorem dyadic_step (d : ℕ) (hd : 0 < d) : (∑ q ∈ Ioc d (2*d), w q) ≤ 32 := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hsub : Ioc d (2*d) ⊆ Icc 1 (2*d) := by intro q hq; simp_all [mem_Ioc, mem_Icc]; omega
  have h := prefix_square (2*d)
  calc
    (∑ q ∈ Ioc d (2*d), w q) ≤ ∑ q ∈ Ioc d (2*d), 4/(d:ℝ)*singular q^2 := by
      apply sum_le_sum
      intro q hq
      have dq := (mem_Ioc.mp hq).1
      have hq' : 0 < q := hd.trans dq
      have hqR : (0:ℝ)<q := by exact_mod_cast hq'
      have hdqR : (d:ℝ)≤q := by exact_mod_cast dq.le
      have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq'
      have hs := sq_le_sq₀ (show 0≤(q:ℝ)/q.totient by positivity) (mul_nonneg (by norm_num : (0:ℝ)≤2) (singular_nonneg q)) |>.mpr (ratio_le q hq')
      calc
        w q = ((q:ℝ)/q.totient)^2 / q := by dsimp [w]; field_simp
        _ ≤ (2*singular q)^2 / q := by gcongr
        _ ≤ (2*singular q)^2 / d := by gcongr
        _ = _ := by ring
    _ = 4/(d:ℝ)*(∑ q ∈ Ioc d (2*d), singular q^2) := (mul_sum ..).symm
    _ ≤ 4/(d:ℝ)*(∑ q ∈ Icc 1 (2*d), singular q^2) := by
      exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)) (by positivity)
    _ ≤ 4/(d:ℝ)*(4*((2*d:ℕ):ℝ)) := by gcongr
    _ = 32 := by push_cast; field_simp; ring

private theorem prefix_pow (k : ℕ) :
    (∑ q ∈ Icc 1 (2^k), w q) ≤ 32*((k:ℝ)+1) := by
  induction k with
  | zero => norm_num [w]
  | succ k ih =>
    have hs : Icc 1 (2^(k+1)) = Icc 1 (2^k) ∪ Ioc (2^k) (2*2^k) := by
      ext q
      have hk : 0 < (2:ℕ)^k := by positivity
      simp only [mem_Icc, mem_union, mem_Ioc, pow_succ]
      omega
    have hd : Disjoint (Icc 1 (2^k)) (Ioc (2^k) (2*2^k)) := by
      apply Finset.disjoint_left.mpr
      intro q hq hq'
      exact (not_lt_of_ge (mem_Icc.mp hq).2) (mem_Ioc.mp hq').1
    rw [hs, sum_union hd]
    have hh := dyadic_step (2^k) (by positivity)
    push_cast
    linarith

/-- The weighted totient sum costs only a single logarithm. -/
theorem sum_totient (Q : ℕ) :
    (∑ q ∈ Icc 1 (Q^2), (q:ℝ)/(q.totient:ℝ)^2) ≤ 96*(1+(Nat.log 2 Q:ℝ)) := by
  let k := Nat.log 2 Q + 1
  have h : Q ≤ 2^k := (Nat.lt_pow_succ_log_self (by decide : 1<2) Q).le
  have h2 : Q^2 ≤ 2^(k*2) := by rw [pow_mul]; gcongr
  have hs : Icc 1 (Q^2) ⊆ Icc 1 (2^(k*2)) := Finset.Icc_subset_Icc_right h2
  calc
    (∑ q ∈ Icc 1 (Q^2), (q:ℝ)/(q.totient:ℝ)^2) ≤ ∑ q ∈ Icc 1 (2^(k*2)), w q :=
      sum_le_sum_of_subset_of_nonneg hs (fun q _ _ => by positivity)
    _ ≤ _ := (prefix_pow (k*2)).trans (by dsimp [k]; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) (Nat.log 2 Q)])

end GB4Totient

namespace GB4Scale

def grid (n : ℕ) := (Nat.log 2 (n+2))^2
def depth (n : ℕ) := 1 + Nat.log 2 (grid n)
def length (n : ℕ) := max 1 (Nat.log 2 n / 2)

/-- An explicit comparison used only to make the orbit block fit inside the
available binary frequencies. No Goldbach instances are enumerated. -/
private theorem pow_dominates (k : ℕ) (hk : 128 ≤ k) : 16*(1+k)^8 ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ 2 k]
    have step : (1+(k+1))^8 ≤ 2*(1+k)^8 := by
      obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hk
      ring_nf
      omega
    omega

theorem eventual_scales (b : ℕ) : ∃ N : ℕ, ∀ n ≥ N,
    2 ≤ depth n ∧ b ≤ depth n ∧ (depth n)^4 ≤ length n := by
  let B := max 128 b
  refine ⟨2^(2^B),fun n hn => ?_⟩
  have hB : 128 ≤ B := le_max_left 128 b
  have hb : b ≤ B := le_max_right 128 b
  have hn2 : 2 ≤ n := (Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.one_le_two_pow (n:=B))).trans hn
  let v := Nat.log 2 (n+2)
  let k := Nat.log 2 (grid n)
  have hv : 2^B ≤ v := Nat.le_log_of_pow_le (by decide) (hn.trans (by omega))
  have hv1 : 1 ≤ v := (Nat.one_le_two_pow (n:=B)).trans hv
  have hv2 : v ≤ grid n := by change v ≤ v^2; nlinarith
  have hk : B ≤ k := Nat.le_log_of_pow_le (by decide) (hv.trans hv2)
  have hq0 : grid n ≠ 0 := by omega
  have he := (pow_dominates k (hB.trans hk)).trans (Nat.pow_log_le_self 2 hq0)
  change 16*(1+k)^8 ≤ v^2 at he
  have hsq : (4*(1+k)^4)^2 ≤ v^2 := by convert he using 1; ring
  have hl := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsq
  have hshift : v ≤ Nat.log 2 n + 1 := by
    have := Nat.log_mono_right (b:=2) (show n+2 ≤ n*2 by omega)
    rwa [Nat.log_mul_base (by decide) (by omega)] at this
  change 2 ≤ 1+k ∧ b ≤ 1+k ∧ (1+k)^4 ≤ max 1 (Nat.log 2 n / 2)
  have : 1 ≤ (1+k)^4 := Nat.one_le_pow _ _ (by omega)
  omega

theorem separation {q p m : ℕ} (hprime : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q)
    (hnone : ∀ h ∈ Finset.Icc 1 m, ¬ p ∣ 2^h-1)
    {i j : ℕ} (hij : i < j) (heq : (2:ℕ)^(i+1)%q = 2^(j+1)%q) : m ≤ j-i := by
  by_contra! hshort
  have hsplit : j+1 = i+1+(j-i) := by omega
  have hmod : 2^(i+1)*1 ≡ 2^(i+1)*2^(j-i) [MOD p] := by
    have h : (2:ℕ)^(i+1) ≡ 2^(j+1) [MOD p] := (show _ ≡ _ [MOD q] from heq).of_dvd hpq
    simpa only [mul_one, hsplit, pow_add] using h
  have hcop : p.Coprime 2 := (Nat.coprime_primes hprime Nat.prime_two).mpr hp2
  have hcancel := Nat.ModEq.cancel_left_of_coprime (hcop.pow_right (i+1)) hmod
  exact hnone (j-i) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
    ((Nat.modEq_iff_dvd' (Nat.one_le_two_pow (n:=j-i))).mp hcancel)

end GB4Scale

namespace GB4Centers
open Finset GB4Bad GB4Moment
open scoped Classical

noncomputable def centers (n q : ℕ) : ℕ :=
  ((range (q+1)).filter (fun a : ℕ =>
    Nat.Coprime a q ∧ (1:ℝ)/3 < K (GB4Scale.length n) ((a:ℝ)/q))).card

noncomputable def mass (n q : ℕ) : ℝ :=
  min 1 ((q:ℝ)/(grid n:ℝ)) * (centers n q:ℝ)/(q.totient:ℝ)^2

private theorem mass_nonneg (n q : ℕ) : 0 ≤ mass n q := by
  unfold mass
  positivity

-- The coprime counting argument is adapted from PacketShortCentersFromModuli.
private theorem mass_trivial (n q : ℕ) (hq : 1 ≤ q) : mass n q ≤ 2*weight n q := by
  let V := (range q).filter (fun a => Nat.Coprime q a)
  have cnt : centers n q ≤ (insert q V).card := by
    apply card_le_card
    intro a ha
    obtain ⟨hr,hc,_⟩ := mem_filter.mp ha
    rcases lt_or_ge a q with h|h
    · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_range.mpr h,hc.symm⟩)
    · exact mem_insert.mpr (Or.inl (by have := mem_range.mp hr; omega))
  have card := cnt.trans (card_insert_le q V)
  change centers n q ≤ q.totient+1 at card
  have hp : 0 < q.totient := Nat.totient_pos.mpr hq
  have hc : (centers n q:ℝ) ≤ 2*(q.totient:ℝ) := by exact_mod_cast (show centers n q ≤ 2*q.totient by omega)
  have hpos : (0:ℝ) < q.totient := by exact_mod_cast hp
  unfold mass weight
  calc
    _ ≤ min 1 ((q:ℝ)/(grid n:ℝ)) * (2*(q.totient:ℝ))/(q.totient:ℝ)^2 := by
      gcongr
    _ = _ := by field_simp

private theorem mass_long (n q : ℕ) (hu : 2 ≤ u n) (hL : (u n)^4 ≤ GB4Scale.length n)
    (hs : ¬ smooth n q) (hb : ¬shortLarge n q) :
    mass n q ≤ (18/(u n:ℝ)^4)*((q:ℝ)/(q.totient:ℝ)^2) := by
  unfold smooth at hs
  push Not at hs
  obtain ⟨p,hp,hlarge⟩ := hs
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpq := Nat.dvd_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    have := Nat.pow_le_pow_left hu 12
    omega
  have hq : 1 < q := hprime.one_lt.trans_le (Nat.le_of_mem_primeFactors hp)
  have hnone : ∀ j ∈ Icc 1 ((u n)^4), ¬p ∣ 2^j-1 :=
    fun j hj hd => hb ⟨p,hp,hlarge,j,hj,hd⟩
  have hm : 0 < (u n)^4 := by positivity
  have hcard := centers_le q (GB4Scale.length n) ((u n)^4) hq hm hL
    (fun _ _ hij _ heq => GB4Scale.separation hprime hp2 hpq hnone hij heq)
  change (centers n q:ℝ) ≤ _ at hcard
  push_cast at hcard
  unfold mass
  calc
    _ ≤ (centers n q:ℝ)/(q.totient:ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact (mul_le_mul_of_nonneg_right (min_le_left ..) (Nat.cast_nonneg _)).trans_eq (one_mul _)
    _ ≤ (18*(q:ℝ)/(u n:ℝ)^4)/(q.totient:ℝ)^2 :=
      div_le_div_of_nonneg_right hcard (sq_nonneg _)
    _ = _ := by ring

private theorem finite_bound (n : ℕ) (hu : 2 ≤ u n) (hL : (u n)^4 ≤ GB4Scale.length n) :
    ∑ q ∈ Icc 1 ((grid n)^2), mass n q ≤
      2*(∑ q ∈ (Icc 1 ((grid n)^2)).filter (smooth n), weight n q) +
      2*(∑ q ∈ (Icc 1 ((grid n)^2)).filter (shortLarge n), weight n q) +
      (18/(u n:ℝ)^4)*(96*(u n:ℝ)) := by
  classical
  let S := Icc 1 ((grid n)^2)
  have hsum : (∑ q ∈ S, mass n q) ≤
      ∑ q ∈ S, ((if smooth n q then 2*weight n q else 0) +
        (if shortLarge n q then 2*weight n q else 0) +
        (18/(u n:ℝ)^4)*((q:ℝ)/(q.totient:ℝ)^2)) := by
    apply sum_le_sum
    intro q hq
    have hw : 0 ≤ weight n q := by unfold weight; positivity
    have hr : 0 ≤ (18/(u n:ℝ)^4)*((q:ℝ)/(q.totient:ℝ)^2) := by positivity
    have ht := mass_trivial n q (mem_Icc.mp hq).1
    by_cases hs : smooth n q <;> by_cases hb : shortLarge n q
    · simp only [ite_eq_left hs, ite_eq_left hb]; linarith
    · simp only [ite_eq_left hs, ite_eq_right hb]; linarith
    · simp only [ite_eq_right hs, ite_eq_left hb]; linarith
    · simpa only [ite_eq_right hs, ite_eq_right hb, zero_add] using mass_long n q hu hL hs hb
  simp only [sum_add_distrib, ← sum_filter, ← mul_sum] at hsum
  have ht := GB4Totient.sum_totient (grid n)
  have hu' : (u n:ℝ) = 1+(Nat.log 2 (grid n):ℝ) := by simp [u]
  change (∑ q ∈ S, mass n q) ≤ _
  have last : (18/(u n:ℝ)^4)*(∑ q ∈ S, (q:ℝ)/(q.totient:ℝ)^2) ≤ (18/(u n:ℝ)^4)*(96*(u n:ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [hu'] using ht
  exact hsum.trans (add_le_add (le_refl _) last)

/-- The full family of reduced binary-orbit centers has vanishing weighted mass. -/
theorem all_centers (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ n ≥ N,
    (∑ q ∈ Icc 1 ((grid n)^2), mass n q) ≤ ε := by
  obtain ⟨A,hA⟩ := smooth_budget (ε/8) (by positivity)
  obtain ⟨B,hB⟩ := shortLarge_budget (ε/8) (by positivity)
  obtain ⟨b,hb⟩ := exists_nat_ge (3456/ε)
  obtain ⟨C,hC⟩ := GB4Scale.eventual_scales b
  refine ⟨max A (max B C),fun n hn => ?_⟩
  have ha := hA n ((le_max_left ..).trans hn)
  have hbc := (le_max_right ..).trans hn
  have hx := hB n ((le_max_left ..).trans hbc)
  obtain ⟨hu,hbu,hL⟩ := hC n ((le_max_right ..).trans hbc)
  change 2 ≤ u n at hu
  change b ≤ u n at hbu
  have hge : (2:ℝ) ≤ u n := by exact_mod_cast hu
  have hpos : (0:ℝ) < u n := by linarith
  have heps : 3456 ≤ (u n:ℝ)*ε :=
    (div_le_iff₀ hε).mp (hb.trans (by exact_mod_cast hbu))
  have hrate : 18/(u n:ℝ)^4*(96*(u n:ℝ)) ≤ ε/2 := by
    calc
      _ = 1728/(u n:ℝ)^3 := by field_simp; ring
      _ ≤ 1728/(u n:ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num) hpos
        have := pow_le_pow_right₀ (show (1:ℝ) ≤ u n by linarith) (show 1 ≤ 3 by decide)
        simpa using this
      _ ≤ _ := (div_le_iff₀ hpos).mpr (by linarith)
  linarith [finite_bound n hu hL]

end GB4Centers

theorem Conjectures.Goldbach.PacketRemainingCenterCount :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => ¬ o n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) * (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) / (Nat.totient q:ℝ)^2) ≤ ε := by
  classical
  intro Q L K o ε hε
  obtain ⟨N,hN⟩ := GB4Centers.all_centers ε hε
  refine ⟨N,fun n hn => ?_⟩
  apply le_trans _ (hN n hn)
  change (∑ q ∈ (Finset.Icc 1 ((GB4Bad.grid n)^2)).filter (fun q => ¬o n q), GB4Centers.mass n q) ≤ _
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
    (fun q _ _ => GB4Centers.mass_nonneg n q)

end PacketAllMassRemainingSupport

-- Adapted from PacketModelFromCenterCounts at 2ea34ceb47053e6df4f27deac26e84e19de38eff under the repository license.
namespace PacketAllMassReductionSupport

namespace Conjectures.Goldbach.PacketModelFromCenterCounts_aux

noncomputable section

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

private def gridQ (n : ℕ) := (Nat.log 2 (n + 2))^2

private def packet (m : ℕ) (t : ℝ) :=
  ∑ j ∈ Finset.range m, Real.cos (2 * Real.pi * (2 : ℝ)^(j + 1) * t)

private def length (n : ℕ) := max 1 (Nat.log 2 n / 2)

private def arcs (n : ℕ) : Set ℝ :=
  let Q := gridQ n
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (Q : ℝ) / ((q : ℝ) * (n : ℝ))}

private def resonant (n : ℕ) : Set ℝ :=
  {t : ℝ | t ∉ arcs n ∧
    (1 : ℝ) / 2 < packet (length n) t / (length n : ℝ)}

private def integralOn (s : Set ℝ) (f : ℝ → ℝ) :=
  intervalIntegral (s.indicator f) (0 : ℝ) 1 MeasureTheory.volume

private def profile (n q : ℕ) (c t : ℝ) :=
  4 * (n : ℝ)^2 /
    ((q.totient : ℝ)^2 * (1 + ((n : ℝ) * (t - c))^2))

private def lorentz (r c t : ℝ) := 1 / (r^2 + (t - c)^2)

private theorem lorentzContinuous {r : ℝ} (hr : 0 < r) (c : ℝ) :
    Continuous (lorentz r c) := by
  unfold lorentz
  fun_prop (disch := intro t; positivity)

private theorem lorentzIntegral {r : ℝ} (hr : 0 < r) (c : ℝ) :
    (∫ t in (0 : ℝ)..1, lorentz r c t) ≤ Real.pi / r := by
  let F := fun t : ℝ => Real.arctan ((t - c) / r) / r
  have deriv (t : ℝ) : HasDerivAt F (lorentz r c t) t := by
    have h := (((Real.hasDerivAt_arctan ((t - c) / r)).comp t
      (((hasDerivAt_id t).sub_const c).div_const r)).div_const r)
    have eq : lorentz r c t = 1 / (1 + ((t - c) / r)^2) * (1 / r) / r := by
      unfold lorentz
      field_simp <;> ring
    rw [eq]
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => deriv t)
    ((lorentzContinuous hr c).intervalIntegrable ..)]
  dsimp [F]
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ hr.le
  have ha := Real.arctan_lt_pi_div_two ((1 - c) / r)
  have hb := Real.neg_pi_div_two_lt_arctan ((0 - c) / r)
  linarith

private theorem measurableArcs (n : ℕ) : MeasurableSet (arcs n) := by
  let Q := gridQ n
  let Index := {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.1 ≤ Q ∧ p.2 ≤ p.1 ∧ p.2.Coprime p.1}
  have cover : arcs n = ⋃ i : Index,
      {t : ℝ | |t - (i.val.2 : ℝ) / (i.val.1 : ℝ)| ≤
        (Q : ℝ) / ((i.val.1 : ℝ) * (n : ℝ))} := by
    ext t
    constructor
    · rintro ⟨q, a, hq, hQ, ha, hc, ht⟩
      exact Set.mem_iUnion.mpr ⟨⟨(q, a), hq, hQ, ha, hc⟩, ht⟩
    · intro ht
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
      exact ⟨i.val.1, i.val.2, i.property.1, i.property.2.1, i.property.2.2.1,
        i.property.2.2.2, hi⟩
  rw [cover]
  exact MeasurableSet.iUnion fun _ =>
    (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const))
      continuous_const).measurableSet

private theorem measurableMask (n : ℕ) : MeasurableSet (resonant n) := by
  have hk : Continuous (fun t => packet (length n) t / (length n : ℝ)) := by
    unfold packet
    fun_prop
  exact (measurableArcs n).compl.inter
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ) / 2)) hk).measurableSet

private theorem onRegion {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → ℝ}
    (hf : Continuous f) :
    IntervalIntegrable (s.indicator f) MeasureTheory.volume (0 : ℝ) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 1)).indicator hs

private theorem onSubset {s v : Set ℝ} {f : ℝ → ℝ} (hs : MeasurableSet s)
    (hv : MeasurableSet v) (h : s ⊆ v) (hc : Continuous f) (hpos : ∀ t, 0 ≤ f t) :
    integralOn s f ≤ integralOn v f := by
  apply intervalIntegral.integral_mono_on (by norm_num) (onRegion hs hc) (onRegion hv hc)
  intro t _
  by_cases ht : t ∈ s
  · simp [ht, h ht]
  · by_cases ht' : t ∈ v <;> simp [ht, ht', hpos]

private theorem denominatorExclusion {n k d : ℕ} {t : ℝ} (hn : 0 < n)
    (hd : 0 < d) (hQ : d ≤ gridQ n) (hk : k ≤ d) (hm : t ∉ arcs n) :
    (gridQ n : ℝ) / (d * (n : ℝ)) < |t - (k : ℝ) / d| := by
  obtain ⟨g, a, q, hg, hcop, hk', hq'⟩ :=
    Nat.exists_coprime' (Nat.gcd_pos_of_pos_right k hd)
  have hq : 0 < q := by
    by_contra! hz
    have he : q = 0 := by omega
    rw [he, zero_mul] at hq'
    omega
  have hqd : q ≤ d := Nat.le_of_dvd hd ⟨g, hq'⟩
  have haq : a ≤ q := by
    exact (Nat.mul_le_mul_right_iff hg).mp (show a * g ≤ q * g by omega)
  have eq : (k : ℝ) / d = (a : ℝ) / (q : ℝ) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    have cross : k * q = a * d := by rw [hk', hq']; ring
    exact_mod_cast cross
  by_contra! h
  apply hm
  refine ⟨q, a, hq, hqd.trans hQ, haq, hcop, ?_⟩
  rw [← eq]
  exact h.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hqd : (q : ℝ) ≤ d) (Nat.cast_nonneg _)))

private theorem profileContinuous (n q : ℕ) (hq : 0 < q) (c : ℝ) :
    Continuous (profile n q c) := by
  have hf : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold profile
  fun_prop (disch := intro t; positivity)

private theorem profileNonneg (n q : ℕ) (c t : ℝ) : 0 ≤ profile n q c t := by
  unfold profile
  positivity

private theorem peakOutside (n q : ℕ) (hq : 0 < q) (c r : ℝ) (hr : 0 < r) :
    integralOn {t : ℝ | r < |t - c|} (profile n q c) ≤
      (8 / (q.totient : ℝ)^2) * (Real.pi / r) := by
  let f : ℝ := q.totient
  let s := {t : ℝ | r < |t - c|}
  have fp : 0 < f := by
    dsimp [f]
    exact_mod_cast Nat.totient_pos.mpr hq
  have hs : MeasurableSet s :=
    (isOpen_lt continuous_const
      (continuous_abs.comp (continuous_id.sub continuous_const))).measurableSet
  have hd : Continuous (fun t : ℝ => f^2 * (1 + ((n : ℝ) * (t - c))^2)) := by
    fun_prop
  have hc : Continuous (profile n q c) :=
    (continuous_const : Continuous (fun _ : ℝ => 4 * (n : ℝ)^2)).div hd
      (fun t => ne_of_gt (mul_pos (by positivity) (by positivity)))
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, (8 / f^2) * lorentz r c t := by
      apply intervalIntegral.integral_mono_on (by norm_num) (onRegion hs hc)
        (((lorentzContinuous hr c).intervalIntegrable ..).const_mul _)
      intro t _
      change s.indicator (profile n q c) t ≤ _
      by_cases ht : t ∈ s
      · rw [Set.indicator_of_mem ht]
        have d : r ≤ |t - c| := le_of_lt ht
        have sq := pow_le_pow_left₀ hr.le d 2
        rw [sq_abs] at sq
        have bound : (n : ℝ)^2 / (1 + ((n : ℝ) * (t - c))^2) ≤
            2 / (r^2 + (t - c)^2) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          nlinarith only [mul_le_mul_of_nonneg_left sq (sq_nonneg (n : ℝ))]
        calc
          profile n q c t =
              (4 / f^2) * ((n : ℝ)^2 / (1 + ((n : ℝ) * (t - c))^2)) := by
                unfold profile
                dsimp [f]
                field_simp <;> ring
          _ ≤ (4 / f^2) * (2 / (r^2 + (t - c)^2)) :=
            mul_le_mul_of_nonneg_left bound (by positivity)
          _ = _ := by unfold lorentz; ring
      · rw [Set.indicator_of_notMem ht]
        unfold lorentz
        positivity
    _ = (8 / f^2) * (∫ t in (0 : ℝ)..1, lorentz r c t) :=
      intervalIntegral.integral_const_mul ..
    _ ≤ (8 / f^2) * (Real.pi / r) :=
      mul_le_mul_of_nonneg_left (lorentzIntegral hr c) (by positivity)

private theorem oneCenterMass (n q a : ℕ) (hn : 0 < n) (hq : 0 < q)
    (hQ : 0 < gridQ n) (ha : a ≤ q) :
    integralOn (resonant n) (profile n q ((a : ℝ) / (q : ℝ))) ≤
      8 * Real.pi * (n : ℝ) * min 1 ((q : ℝ) / (gridQ n : ℝ)) /
        (q.totient : ℝ)^2 := by
  let c := (a : ℝ) / (q : ℝ)
  have hc := profileContinuous n q hq c
  have hf : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have nr : 0 < (n : ℝ) := by exact_mod_cast hn
  have qr : 0 < (gridQ n : ℝ) := by exact_mod_cast hQ
  by_cases small : q ≤ gridQ n
  · let r := (gridQ n : ℝ) / ((q : ℝ) * (n : ℝ))
    have hr : 0 < r := by dsimp [r]; positivity
    have hs : MeasurableSet {t : ℝ | r < |t - c|} :=
      (isOpen_lt continuous_const
        (continuous_abs.comp (continuous_id.sub continuous_const))).measurableSet
    have sub : resonant n ⊆ {t : ℝ | r < |t - c|} :=
      fun _ h => denominatorExclusion hn hq small ha h.1
    apply (onSubset (measurableMask n) hs sub hc (profileNonneg n q c)).trans
    apply (peakOutside n q hq c r hr).trans_eq
    rw [min_eq_right ((div_le_one qr).mpr (by exact_mod_cast small))]
    dsimp [r]
    field_simp <;> ring
  · have ht : 1 ≤ (q : ℝ) / (gridQ n : ℝ) :=
      (one_le_div qr).mpr (by exact_mod_cast (by omega : gridQ n ≤ q))
    rw [min_eq_left ht, mul_one]
    let r := 1 / (n : ℝ)
    have hr : 0 < r := by dsimp [r]; positivity
    have id (t : ℝ) : profile n q c t =
        (4 / (q.totient : ℝ)^2) * lorentz r c t := by
      dsimp [profile, lorentz, r]
      field_simp <;> ring
    calc
      _ ≤ ∫ t in (0 : ℝ)..1, (4 / (q.totient : ℝ)^2) * lorentz r c t := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (onRegion (measurableMask n) hc)
          (((lorentzContinuous hr c).intervalIntegrable ..).const_mul _)
        intro t _
        by_cases h : t ∈ resonant n
        · rw [Set.indicator_of_mem h, id]
        · rw [Set.indicator_of_notMem h]
          unfold lorentz
          positivity
      _ = (4 / (q.totient : ℝ)^2) * _ :=
        intervalIntegral.integral_const_mul ..
      _ ≤ (4 / (q.totient : ℝ)^2) * (Real.pi / r) :=
        mul_le_mul_of_nonneg_left (lorentzIntegral hr _) (by positivity)
      _ ≤ _ := by
        dsimp [r]
        field_simp <;> nlinarith only [mul_pos Real.pi_pos nr]

private def farPeak (n q : ℕ) (a : ℕ) :=
  integralOn {t : ℝ | (gridQ n : ℝ)^2 / (n : ℝ) < |t - (a : ℝ) / (q : ℝ)|}
    (profile n q ((a : ℝ) / (q : ℝ)))

private theorem singleFarPeak (n q : ℕ) (hn : 0 < n) (hq : 0 < q)
    (hQ : 0 < gridQ n) (a : ℕ) :
    farPeak n q a ≤
      (8 * Real.pi * ((n : ℝ) / (gridQ n : ℝ)^2)) / (q.totient : ℝ)^2 := by
  have hr : 0 < (gridQ n : ℝ)^2 / (n : ℝ) := by positivity
  apply (peakOutside n q hq ((a : ℝ) / (q : ℝ)) _ hr).trans_eq
  field_simp <;> ring

private def numerators (q : ℕ) :=
  (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q)

private theorem countNumerators (q : ℕ) (hq : 0 < q) :
    (numerators q).card ≤ 2 * q.totient := by
  have card : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    simp only [Nat.totient_eq_card_coprime, Nat.coprime_comm]
  have sub : numerators q ⊆
      insert q ((Finset.range q).filter (fun a => Nat.Coprime a q)) := by
    intro a ha
    obtain ⟨hr, hc⟩ := Finset.mem_filter.mp ha
    rcases eq_or_ne a q with rfl | h
    · simp
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
          (by have := Finset.mem_range.mp hr; omega), hc⟩)
  have bound := (Finset.card_le_card sub).trans (Finset.card_insert_le ..)
  rw [card] at bound
  have hp := Nat.totient_pos.mpr hq
  omega

private theorem totientSquare (q : ℕ) :
    q ≤ 2 * q.totient^2 ∧ (¬ 2 ∣ q → q ≤ q.totient^2) := by
  induction q using Nat.strong_induction_on with
  | ind q ih =>
    rcases eq_or_ne q 0 with rfl | h0
    · simp
    rcases eq_or_ne q 1 with rfl | h1
    · simp
    obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd h1
    have hp2 := hp.two_le
    have hm : 0 < m := Nat.pos_of_ne_zero (fun hz => h0 (by simp [hz]))
    have lt : m < p * m := by nlinarith [Nat.mul_le_mul_right m hp2]
    obtain ⟨all, odd⟩ := ih m lt
    have lift (f c : ℕ) (eq : (p * m).totient = f * m.totient) (hf : p ≤ f^2)
        (h : m ≤ c * m.totient^2) : p * m ≤ c * (p * m).totient^2 := by
      calc
        _ ≤ f^2 * (c * m.totient^2) := Nat.mul_le_mul hf h
        _ = _ := by rw [eq]; ring
    have both (f : ℕ) (eq : (p * m).totient = f * m.totient) (hf : p ≤ f^2) :
        p * m ≤ 2 * (p * m).totient^2 ∧
          (¬ 2 ∣ p * m → p * m ≤ (p * m).totient^2) := by
      refine ⟨lift f 2 eq hf all, ?_⟩
      intro hn
      have hodd := odd (fun h => hn (dvd_mul_of_dvd_right h p))
      simpa only [one_mul] using lift f 1 eq hf (by simpa using hodd)
    by_cases divides : p ∣ m
    · exact both p (Nat.totient_mul_of_dvd divides) (by nlinarith [Nat.le_mul_self p])
    · have eq := Nat.totient_mul_of_prime_of_not_dvd hp divides
      by_cases two : p = 2
      · subst p
        simp only [Nat.reduceSub, one_mul] at eq
        constructor
        · rw [eq]
          exact Nat.mul_le_mul_left 2 (odd divides)
        · simp
      · apply both (p - 1) eq
        have e : p = (p - 1) + 1 := by omega
        have g : 2 ≤ p - 1 := by omega
        nlinarith [Nat.mul_le_mul_right (p - 1) g]

private theorem totientSum (m : ℕ) :
    (∑ j ∈ Finset.range m, 1 / ((j + 1).totient : ℝ)) ≤
      4 * Real.sqrt (m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    let u := Real.sqrt (m : ℝ)
    let v := Real.sqrt ((m : ℝ) + 1)
    let f : ℝ := (m + 1).totient
    have fp : 0 < f := by
      dsimp [f]
      exact_mod_cast (Nat.totient_pos.mpr (Nat.succ_pos m))
    have hb : (m : ℝ) + 1 ≤ 2 * f^2 := by
      dsimp [f]
      exact_mod_cast (totientSquare (m + 1)).1
    have hu : u^2 = (m : ℝ) := Real.sq_sqrt (by positivity)
    have hv : v^2 = (m : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have uv : u ≤ v := Real.sqrt_le_sqrt (by linarith)
    have pos : 0 ≤ v := Real.sqrt_nonneg _
    have v2 : v ≤ 2 * f := by
      by_contra! hh
      have h := mul_pos (sub_pos.mpr hh) (show 0 < v + 2 * f by linarith)
      nlinarith only [hb, hv, h, sq_nonneg f]
    have bound : v + u ≤ 4 * f := by linarith
    have step : 1 / f ≤ 4 * (v - u) := by
      apply (div_le_iff₀ fp).mpr
      nlinarith only [mul_le_mul_of_nonneg_right bound (sub_nonneg.mpr uv), hu, hv]
    rw [Finset.sum_range_succ, Nat.cast_succ]
    change _ ≤ 4 * v
    linarith only [ih, step]

theorem farTailQuantitative (n : ℕ) (hn : 0 < n) (hQ : 0 < gridQ n) :
    (∑ q ∈ Finset.Icc 1 ((gridQ n)^2), ∑ a ∈ numerators q, farPeak n q a) ≤
      64 * Real.pi * (n : ℝ) / (gridQ n : ℝ) := by
  let Q := gridQ n
  let C := 8 * Real.pi * ((n : ℝ) / (Q : ℝ)^2)
  have pos : 0 ≤ C := by dsimp [C]; positivity
  have bb (q : ℕ) (hq : 0 < q) :
      (∑ a ∈ numerators q, farPeak n q a) ≤
        (2 * C) * (1 / (q.totient : ℝ)) := by
    have hf : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
    calc
      _ ≤ ∑ _a ∈ numerators q, C / (q.totient : ℝ)^2 :=
        Finset.sum_le_sum fun a _ => singleFarPeak n q hn hq hQ a
      _ = ((numerators q).card : ℝ) * (C / (q.totient : ℝ)^2) := by simp
      _ ≤ (2 * (q.totient : ℝ)) * (C / (q.totient : ℝ)^2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast countNumerators q hq
      _ = _ := by field_simp <;> ring
  have index : Finset.Icc 1 (Q^2) =
      (Finset.range (Q^2)).map (addRightEmbedding 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, addRightEmbedding_apply]
    constructor
    · intro h
      exact ⟨k - 1, by omega, by omega⟩
    · rintro ⟨j, h, rfl⟩
      omega
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 (Q^2), (2 * C) * (1 / (q.totient : ℝ)) :=
      Finset.sum_le_sum fun q h => bb q (Finset.mem_Icc.mp h).1
    _ = (2 * C) * (∑ j ∈ Finset.range (Q^2), 1 / ((j + 1).totient : ℝ)) := by
      rw [index, ← Finset.mul_sum, Finset.sum_map]
      rfl
    _ ≤ (2 * C) * (4 * Real.sqrt ((Q^2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (totientSum (Q^2)) (by positivity)
    _ = _ := by
      push_cast
      rw [Real.sqrt_sq (Nat.cast_nonneg _)]
      dsimp [C, Q]
      field_simp <;> ring

theorem farTails (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ Finset.Icc 1 ((gridQ n)^2),
        ∑ a ∈ numerators q, farPeak n q a) ≤ ε * (n : ℝ) := by
  obtain ⟨M, hM⟩ := exists_nat_ge (64 * Real.pi / ε)
  let B := max 1 M
  refine ⟨2^B, ?_⟩
  intro n hn
  have hn' : 0 < n := lt_of_lt_of_le (by positivity : 0 < 2^B) hn
  have hb : B ≤ Nat.log 2 (n + 2) :=
    Nat.le_log_of_pow_le (by decide) (by omega)
  have hq : B ≤ gridQ n := by
    unfold gridQ
    nlinarith [Nat.le_mul_self (Nat.log 2 (n + 2))]
  have hQ : 0 < gridQ n := lt_of_lt_of_le (by dsimp [B]; omega) hq
  apply (farTailQuantitative n hn' hQ).trans
  have hM' : 64 * Real.pi / ε ≤ (gridQ n : ℝ) :=
    hM.trans (by exact_mod_cast (le_trans (le_max_right 1 M) hq))
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp hM')
    (Nat.cast_nonneg (α := ℝ) n)
  linarith only [hh]

private theorem packetVariation (m : ℕ) (hm : 0 < m) (x y : ℝ) :
    |packet m x / (m : ℝ) - packet m y / (m : ℝ)| ≤
      2 * Real.pi * (2 : ℝ)^m * |x - y| := by
  have mr : (0 : ℝ) < m := by exact_mod_cast hm
  let C := 2 * Real.pi * (2 : ℝ)^m * |x - y|
  rw [← sub_div, abs_div, abs_of_pos mr]
  apply (div_le_iff₀ mr).mpr
  unfold packet
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range m,
        |Real.cos (2 * Real.pi * (2 : ℝ)^(j + 1) * x) -
          Real.cos (2 * Real.pi * (2 : ℝ)^(j + 1) * y)| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _j ∈ Finset.range m, C := by
      apply Finset.sum_le_sum
      intro j hj
      let f := 2 * Real.pi * (2 : ℝ)^(j + 1)
      apply (Real.abs_cos_sub_cos_le (f * x) (f * y)).trans
      rw [← mul_sub, abs_mul, abs_of_nonneg (by dsimp [f]; positivity : 0 ≤ f)]
      dsimp [f, C]
      gcongr <;> first | exact Finset.mem_range.mp hj | norm_num
    _ = _ := by simp [C] <;> ring

private theorem exponentialRoom (m : ℕ) (hm : 128 ≤ m) :
    48 * (2 * (m : ℝ) + 3)^4 ≤ (2 : ℝ)^m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction k with
  | zero => norm_num
  | succ k ih =>
    calc
      _ ≤ 2 * (48 * (2 * ((128 + k : ℕ) : ℝ) + 3)^4) := by
        apply sub_nonneg.mp
        push_cast
        ring_nf
        positivity
      _ ≤ 2 * (2 : ℝ)^(128 + k) := by linarith only [ih]
      _ = _ := by
        rw [show 128 + (k + 1) = (128 + k) + 1 by omega, pow_succ]
        ring

theorem rationalCenterStability :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x y : ℝ,
      |x - y| ≤ (gridQ n : ℝ)^2 / (n : ℝ) →
      (1 : ℝ) / 2 < packet (length n) x / (length n : ℝ) →
      (1 : ℝ) / 3 < packet (length n) y / (length n : ℝ) := by
  refine ⟨2^256, ?_⟩
  intro n hn x y hxy hpeak
  let k := Nat.log 2 n
  let m := length n
  have hk : 256 ≤ k := Nat.le_log_of_pow_le (by decide) hn
  have hlen : m = k / 2 := by dsimp [m, k, length]; omega
  have hm : 128 ≤ m := by omega
  have hn' : 0 < n := lt_of_lt_of_le (by positivity : 0 < 2^256) hn
  have nr : (0 : ℝ) < n := by exact_mod_cast hn'
  have top := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have base : 2^k ≤ n := Nat.pow_log_le_self 2 (by omega)
  have next : Nat.log 2 (n + 2) ≤ k + 1 := by
    by_contra! tooBig
    have pw := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show k + 2 ≤ Nat.log 2 (n + 2) by omega)
    have up := Nat.pow_log_le_self 2 (by omega : n + 2 ≠ 0)
    change n < 2^(k + 1) at top
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ] at pw
    have one : 2 ≤ 2^(k + 1) := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ k + 1 by omega)
    omega
  have qbound : (gridQ n : ℝ)^2 ≤ (2 * (m : ℝ) + 3)^4 := by
    have h : Nat.log 2 (n + 2) ≤ 2 * m + 3 := by omega
    have h' : (Nat.log 2 (n + 2) : ℝ) ≤ 2 * (m : ℝ) + 3 := by exact_mod_cast h
    unfold gridQ
    push_cast
    rw [← pow_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) h' 4
  have pn : ((2 : ℝ)^m)^2 ≤ n := by
    rw [← pow_mul]
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 2)
      (show m * 2 ≤ k by omega)).trans base
  have hq : 48 * (gridQ n : ℝ)^2 ≤ (2 : ℝ)^m := by
    linarith only [exponentialRoom m hm, qbound]
  have coeff : 12 * Real.pi * (gridQ n : ℝ)^2 ≤ (2 : ℝ)^m := by
    linarith only [hq,
      mul_le_mul_of_nonneg_right Real.pi_lt_four.le (sq_nonneg (gridQ n : ℝ))]
  have cost : 2 * Real.pi * (2 : ℝ)^m * |x - y| ≤ 1 / 6 := by
    apply (mul_le_mul_of_nonneg_left hxy
      (by positivity : 0 ≤ 2 * Real.pi * (2 : ℝ)^m)).trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ nr).mpr
    linarith only [mul_le_mul_of_nonneg_right coeff
      (by positivity : 0 ≤ (2 : ℝ)^m), pn]
  have bound := (packetVariation m (by omega) x y).trans cost
  change (1 : ℝ) / 2 < packet m x / (m : ℝ) at hpeak
  change (1 : ℝ) / 3 < packet m y / (m : ℝ)
  linarith only [le_abs_self (packet m x / (m : ℝ) - packet m y / (m : ℝ)),
    bound, hpeak]

private def peaks (n : ℕ) (t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ((gridQ n)^2),
    ∑ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a q),
      4 * (n : ℝ)^2 /
        ((Nat.totient q : ℝ)^2 * (1 + ((n : ℝ) * (t - (a : ℝ) / (q : ℝ)))^2))

private theorem onFiniteSum {ι : Type*} (T : Finset ι) {s : Set ℝ}
    (hs : MeasurableSet s) (f : ι → ℝ → ℝ) (hc : ∀ i ∈ T, Continuous (f i)) :
    integralOn s (fun t => ∑ i ∈ T, f i t) = ∑ i ∈ T, integralOn s (f i) := by
  have eq : s.indicator (fun t => ∑ i ∈ T, f i t) =
      fun t => ∑ i ∈ T, s.indicator (f i) t := by
    funext t
    by_cases h : t ∈ s <;> simp [h]
  unfold integralOn
  rw [eq, intervalIntegral.integral_finsetSum (fun i hi => onRegion hs (hc i hi))]

private abbrev detected (n q a : ℕ) :=
  (1 : ℝ) / 3 < packet (length n) ((a : ℝ) / (q : ℝ)) / (length n : ℝ)

private def centerWeight (n q : ℕ) :=
  min (1 : ℝ) ((q : ℝ) / (gridQ n : ℝ)) *
    (((Finset.range (q + 1)).filter
      (fun a => Nat.Coprime a q ∧ detected n q a)).card : ℝ) /
        (q.totient : ℝ)^2

theorem modelFromCenters
    (counts : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ Finset.Icc 1 ((gridQ n)^2), centerWeight n q) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      integralOn (resonant n) (peaks n) ≤ ε * (n : ℝ) := by
  intro ε hε
  obtain ⟨C, hC⟩ := counts (ε / (16 * Real.pi)) (by positivity)
  obtain ⟨F, hF⟩ := farTails (ε / 2) (by positivity)
  obtain ⟨K, hK⟩ := rationalCenterStability
  refine ⟨max 1 (max K (max F C)), ?_⟩
  intro n hn
  have hn' : 0 < n := by omega
  have g : 1 ≤ Nat.log 2 (n + 2) :=
    Nat.le_log_of_pow_le (by decide) (by norm_num <;> omega)
  have hQ : 0 < gridQ n := by unfold gridQ; positivity
  let D := Finset.Icc 1 ((gridQ n)^2)
  let P := 8 * Real.pi * (n : ℝ)
  let V := fun q : ℕ =>
    P * min 1 ((q : ℝ) / (gridQ n : ℝ)) / (q.totient : ℝ)^2
  have bound (q : ℕ) (hq : 0 < q) (a : ℕ) (ha : a ≤ q) :
      integralOn (resonant n) (profile n q ((a : ℝ) / (q : ℝ))) ≤
        farPeak n q a + (if detected n q a then V q else 0) := by
    let c := (a : ℝ) / (q : ℝ)
    let r := (gridQ n : ℝ)^2 / (n : ℝ)
    by_cases h : detected n q a
    · rw [if_pos h]
      apply (oneCenterMass n q a hn' hq hQ ha).trans
      apply le_add_of_nonneg_left
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro t _
      change 0 ≤ ({t : ℝ | r < |t - c|}.indicator (profile n q c)) t
      by_cases ht : t ∈ {t : ℝ | r < |t - c|}
      · rw [Set.indicator_of_mem ht]
        exact profileNonneg n q c t
      · rw [Set.indicator_of_notMem ht]
    · rw [if_neg h, add_zero]
      have sub : resonant n ⊆ {t : ℝ | r < |t - c|} := by
        intro t ht
        change r < |t - c|
        by_contra! hh
        exact h (hK n (by omega) t c hh ht.2)
      have hs : MeasurableSet {t : ℝ | r < |t - c|} :=
        (isOpen_lt continuous_const
          (continuous_abs.comp (continuous_id.sub continuous_const))).measurableSet
      exact onSubset (measurableMask n) hs sub (profileContinuous n q hq c)
        (profileNonneg n q c)
  have accumulate (q : ℕ) (hq : q ∈ D) :
      integralOn (resonant n)
          (fun t => ∑ a ∈ numerators q, profile n q ((a : ℝ) / (q : ℝ)) t) ≤
        (∑ a ∈ numerators q, farPeak n q a) + P * centerWeight n q := by
    have pos := (Finset.mem_Icc.mp hq).1
    rw [onFiniteSum (numerators q) (measurableMask n) _
      (fun a _ => profileContinuous n q pos _)]
    apply (Finset.sum_le_sum (fun a (ha : a ∈ numerators q) =>
      bound q pos a
        (by have h := Finset.mem_range.mp (Finset.mem_filter.mp ha).1; omega))).trans_eq
    rw [Finset.sum_add_distrib, ← Finset.sum_filter]
    congr 1
    simp only [numerators, Finset.filter_filter, Finset.sum_const, nsmul_eq_mul,
      centerWeight, V]
    ring
  calc
    _ = ∑ q ∈ D, integralOn (resonant n)
        (fun t => ∑ a ∈ numerators q, profile n q ((a : ℝ) / (q : ℝ)) t) := by
      apply onFiniteSum D (measurableMask n)
      intro q hq
      apply continuous_finsetSum
      intro a _
      exact profileContinuous n q (Finset.mem_Icc.mp hq).1 _
    _ ≤ ∑ q ∈ D,
        ((∑ a ∈ numerators q, farPeak n q a) + P * centerWeight n q) :=
      Finset.sum_le_sum accumulate
    _ = (∑ q ∈ D, ∑ a ∈ numerators q, farPeak n q a) +
        P * (∑ q ∈ D, centerWeight n q) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ε / 2 * (n : ℝ) + P * (ε / (16 * Real.pi)) := by
      apply add_le_add (hF n (by omega))
        (mul_le_mul_of_nonneg_left (hC n (by omega))
          (by dsimp [P]; positivity))
    _ = _ := by
      dsimp [P]
      field_simp <;> ring

private abbrev lowOrderTest (n q : ℕ) := q % 2 = 1 ∧
  ((Finset.Icc 1 ((Nat.log 2 (gridQ n) + 1)^2)).filter
    (fun j => q ∣ 2^j - 1)).Nonempty

theorem combineCenterCounts
    (slow : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ (Finset.Icc 1 ((gridQ n)^2)).filter
        (fun q => lowOrderTest n q), centerWeight n q) ≤ ε)
    (rest : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ (Finset.Icc 1 ((gridQ n)^2)).filter
        (fun q => ¬ lowOrderTest n q), centerWeight n q) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (∑ q ∈ Finset.Icc 1 ((gridQ n)^2), centerWeight n q) ≤ ε := by
  intro ε hε
  obtain ⟨A, hA⟩ := slow (ε / 2) (by positivity)
  obtain ⟨B, hB⟩ := rest (ε / 2) (by positivity)
  refine ⟨max A B, ?_⟩
  intro n hn
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 1 ((gridQ n)^2)) (lowOrderTest n)]
  linarith only [hA n (by omega), hB n (by omega)]

end
end Conjectures.Goldbach.PacketModelFromCenterCounts_aux

theorem Conjectures.Goldbach.PacketModelFromCenterCounts :
    (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
     let L := fun n : ℕ => max 1 (Nat.log 2 n / 2);
     let K := fun (n : ℕ) (t : ℝ) =>
       (∑ j ∈ Finset.range (L n),
         Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ);
     let o := fun n q : ℕ => q % 2 = 1 ∧
       ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter
         (fun j => q ∣ 2^j-1)).Nonempty;
     ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
       (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q),
         min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) *
           (((Finset.range (q+1)).filter (fun a =>
             Nat.Coprime a q ∧
             (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) /
             (Nat.totient q:ℝ)^2) ≤ ε) →
    (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
     let L := fun n : ℕ => max 1 (Nat.log 2 n / 2);
     let K := fun (n : ℕ) (t : ℝ) =>
       (∑ j ∈ Finset.range (L n),
         Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ);
     let o := fun n q : ℕ => q % 2 = 1 ∧
       ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter
         (fun j => q ∣ 2^j-1)).Nonempty;
     ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
       (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => ¬ o n q),
         min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) *
           (((Finset.range (q+1)).filter (fun a =>
             Nat.Coprime a q ∧
             (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) /
             (Nat.totient q:ℝ)^2) ≤ ε) →
    (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
     let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ,
       1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧
       |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
     let L := fun n : ℕ => max 1 (Nat.log 2 n / 2);
     let K := fun (n : ℕ) (t : ℝ) =>
       (∑ j ∈ Finset.range (L n),
         Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ);
     let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t};
     let G := fun (n : ℕ) (t : ℝ) =>
       ∑ q ∈ Finset.Icc 1 ((Q n)^2),
         ∑ a ∈ (Finset.range (q+1)).filter
           (fun a => Nat.Coprime a q),
           4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 *
             (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2));
     let m := fun (s : Set ℝ) (f : ℝ → ℝ) =>
       intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume;
     ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
       m (B n) (G n) ≤ ε*(n:ℝ)) := by
  intro slow rest
  apply Conjectures.Goldbach.PacketModelFromCenterCounts_aux.modelFromCenters
  exact Conjectures.Goldbach.PacketModelFromCenterCounts_aux.combineCenterCounts slow rest

end PacketAllMassReductionSupport

theorem Conjectures.Goldbach.PacketAllRationalModelMass :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, m (B n) (G n) ≤ ε*(n:ℝ) := by
  exact PacketAllMassReductionSupport.Conjectures.Goldbach.PacketModelFromCenterCounts
    PacketAllMassShortSupport.Conjectures.Goldbach.PacketShortOrderCenterCount
    PacketAllMassRemainingSupport.Conjectures.Goldbach.PacketRemainingCenterCount

end PacketRemainingOverlapFullSupport

-- Adapted from PacketRemainingPeakOverlapFromFull at d6a99bb8abd251067076daeeea81b5ed03697183 under the repository license.
namespace PacketRemainingOverlapSupport

open MeasureTheory

namespace Conjectures.Goldbach.PacketRemainingPeakOverlapFromFull_aux

/-- Monotonicity of the interval integral of a set indicator in the set, for a nonnegative
integrand. Only the larger set needs to be measurable. -/
lemma intervalIntegral_indicator_mono {s t : Set ℝ} {f : ℝ → ℝ} (hsub : s ⊆ t)
    (hmt : MeasurableSet t) (hcont : Continuous f) (hnonneg : ∀ x, 0 ≤ f x) :
    intervalIntegral (s.indicator f) (0:ℝ) 1 volume ≤
      intervalIntegral (t.indicator f) (0:ℝ) 1 volume := by
  have hInt : IntegrableOn f (Set.Icc (0:ℝ) 1) (volume : Measure ℝ) := hcont.integrableOn_Icc
  have hbig : IntegrableOn (t.indicator f) (Set.Ioc (0:ℝ) 1) (volume : Measure ℝ) :=
    (hInt.mono_set Set.Ioc_subset_Icc_self).indicator hmt
  have hle : ∀ x, s.indicator f x ≤ t.indicator f x := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hsub hx)]
    · rw [Set.indicator_of_notMem hx]
      by_cases hy : x ∈ t
      · rw [Set.indicator_of_mem hy]
        exact hnonneg x
      · rw [Set.indicator_of_notMem hy]
  have hnn : ∀ x, 0 ≤ t.indicator f x := by
    intro x
    by_cases hx : x ∈ t
    · rw [Set.indicator_of_mem hx]
      exact hnonneg x
    · rw [Set.indicator_of_notMem hx]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  by_cases hint : IntegrableOn (s.indicator f) (Set.Ioc (0:ℝ) 1) (volume : Measure ℝ)
  · exact setIntegral_mono_ae hint hbig (Filter.Eventually.of_forall hle)
  · have hzero : (∫ x in Set.Ioc (0:ℝ) 1, s.indicator f x ∂volume) = 0 :=
      MeasureTheory.integral_undef
        (show ¬ Integrable (s.indicator f) (volume.restrict (Set.Ioc (0:ℝ) 1)) from hint)
    rw [hzero]
    exact MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall hnn)

/-- Positivity of the totient factor for `q ≥ 1`. -/
lemma totient_cast_pos {q : ℕ} (hq : 1 ≤ q) : (0:ℝ) < (Nat.totient q : ℝ) := by
  have h : 0 < Nat.totient q := Nat.totient_pos.mpr (Nat.lt_of_lt_of_le (by omega) hq)
  exact_mod_cast h

/-- Every summand of the model integrand is nonnegative. -/
lemma model_summand_nonneg (n q a : ℕ) (hq : 1 ≤ q) (t : ℝ) :
    0 ≤ 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)) := by
  have hφ : (0:ℝ) < (Nat.totient q : ℝ) := totient_cast_pos hq
  have hden : (0:ℝ) < (Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2) := by positivity
  exact div_nonneg (by positivity) (le_of_lt hden)

/-- The model integrand is nonnegative. -/
lemma model_nonneg (n X : ℕ) (t : ℝ) :
    0 ≤ ∑ q ∈ Finset.Icc 1 X, ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)) := by
  refine Finset.sum_nonneg fun q hq => ?_
  refine Finset.sum_nonneg fun a _ => ?_
  exact model_summand_nonneg n q a (Finset.mem_Icc.mp hq).1 t

/-- The model integrand is continuous. -/
lemma model_continuous (n X : ℕ) :
    Continuous (fun t : ℝ => ∑ q ∈ Finset.Icc 1 X,
      ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2))) := by
  refine continuous_finsetSum _ fun q hq => ?_
  refine continuous_finsetSum _ fun a _ => ?_
  have hφ : (0:ℝ) < (Nat.totient q : ℝ) := totient_cast_pos (Finset.mem_Icc.mp hq).1
  have hden : ∀ t : ℝ, ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)) ≠ 0 := by
    intro t
    have hpos : (0:ℝ) < (Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2) := by positivity
    linarith
  refine continuous_const.div ?_ hden
  exact continuous_const.mul (continuous_const.add
    ((continuous_const.mul (continuous_id.sub continuous_const)).pow 2))

/-- A closed interval is a measurable set. -/
lemma measurableSet_abs_le (c r : ℝ) :
    MeasurableSet {t : ℝ | |t - c| ≤ r} :=
  (isClosed_le ((continuous_id.sub continuous_const).abs) continuous_const).measurableSet

end Conjectures.Goldbach.PacketRemainingPeakOverlapFromFull_aux

open Conjectures.Goldbach.PacketRemainingPeakOverlapFromFull_aux

theorem Conjectures.Goldbach.PacketRemainingPeakOverlapFromFull :
(let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, m (B n) (G n) ≤ ε*(n:ℝ)) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) \ W n (o n)) (G n) ≤ (n:ℝ)/4608) := by
  intro h
  dsimp only at h
  obtain ⟨N, hN⟩ := h (1/4608) (by norm_num)
  intro Q arcs L K B W o G m
  refine ⟨N, fun n hn _ => ?_⟩
  have hsub : (B n ∩ W n (fun _ => True)) \ W n (o n) ⊆ B n := fun _ ht => ht.1.1
  have hnonneg : ∀ t, 0 ≤ G n t := by
    intro t
    show 0 ≤ ∑ q ∈ Finset.Icc 1 ((Q n)^2),
      ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2))
    exact model_nonneg n ((Q n)^2) t
  have hcont : Continuous (G n) := by
    show Continuous (fun t : ℝ => ∑ q ∈ Finset.Icc 1 ((Q n)^2),
      ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q),
        4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)))
    exact model_continuous n ((Q n)^2)
  have hK : Continuous (K n) := by
    show Continuous (fun t : ℝ =>
      (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ))
    have hnum : Continuous (fun t : ℝ =>
        ∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t)) := by
      refine continuous_finsetSum _ fun j _ => ?_
      exact Real.continuous_cos.comp (continuous_const.mul continuous_id)
    have hL : (0:ℝ) < (L n : ℝ) := by
      have h1 : (1:ℕ) ≤ L n := le_max_left _ _
      have h2 : (1:ℝ) ≤ (L n : ℝ) := by exact_mod_cast h1
      linarith
    exact hnum.div continuous_const (fun _ => hL.ne')
  have hA : MeasurableSet (arcs n) := by
    have hset : arcs n = ⋃ q : ℕ, ⋃ a : ℕ,
        {t : ℝ | 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧
          |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))} := by
      ext t
      simp only [arcs, Set.mem_iUnion, Set.mem_setOf_eq]
    rw [hset]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
    by_cases hcond : 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q
    · have hset2 : {t : ℝ | 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧
          |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}
          = {t : ℝ | |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))} := by
        apply Set.ext
        intro t
        constructor
        · intro ht
          exact ht.2.2.2.2
        · intro ht
          exact ⟨hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2, ht⟩
      rw [hset2]
      exact measurableSet_abs_le _ _
    · have hset2 : {t : ℝ | 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧
          |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))} = ∅ := by
        apply Set.Subset.antisymm
        · intro t ht
          exact False.elim (hcond ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩)
        · exact Set.empty_subset _
      rw [hset2]
      exact MeasurableSet.empty
  have hB : MeasurableSet (B n) := by
    have h2 : MeasurableSet {t : ℝ | (1:ℝ)/2 < K n t} :=
      measurableSet_lt measurable_const hK.measurable
    have h3 : MeasurableSet ((arcs n)ᶜ ∩ {t : ℝ | (1:ℝ)/2 < K n t}) := hA.compl.inter h2
    rw [show B n = (arcs n)ᶜ ∩ {t : ℝ | (1:ℝ)/2 < K n t} by
      apply Set.ext
      intro t
      show (t ∉ arcs n ∧ (1:ℝ)/2 < K n t) ↔
        (t ∈ (arcs n)ᶜ ∧ t ∈ {t : ℝ | (1:ℝ)/2 < K n t})
      constructor
      · intro h
        exact ⟨h.1, h.2⟩
      · intro h
        exact ⟨h.1, h.2⟩]
    exact h3
  have hN' : m (B n) (G n) ≤ (1/4608) * (n:ℝ) := hN n hn
  calc m ((B n ∩ W n (fun _ => True)) \ W n (o n)) (G n)
      ≤ m (B n) (G n) := intervalIntegral_indicator_mono hsub hB hcont hnonneg
    _ ≤ (1/4608) * (n:ℝ) := hN'
    _ = (n:ℝ)/4608 := by ring

end PacketRemainingOverlapSupport

theorem Conjectures.Goldbach.PacketRemainingPeakOverlap :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let W := fun (n : ℕ) (p : ℕ → Prop) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Q n)^2 ∧ a ≤ q ∧ Nat.Coprime a q ∧ p q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ ((Q n:ℝ)^2)/((q:ℝ)*(n:ℝ))}; let o := fun n q : ℕ => Odd q ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ (Nat.log 2 (Q n)+1)^2 ∧ q ∣ 2^j-1; let G := fun (n : ℕ) (t : ℝ) => ∑ q ∈ Finset.Icc 1 ((Q n)^2), ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), 4*(n:ℝ)^2 / ((Nat.totient q:ℝ)^2 * (1+((n:ℝ)*(t-(a:ℝ)/(q:ℝ)))^2)); let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m ((B n ∩ (W n (fun _ => True))) \ W n (o n)) (G n) ≤ (n:ℝ)/4608 := by
  exact PacketRemainingOverlapSupport.Conjectures.Goldbach.PacketRemainingPeakOverlapFromFull
    PacketRemainingOverlapFullSupport.Conjectures.Goldbach.PacketAllRationalModelMass
