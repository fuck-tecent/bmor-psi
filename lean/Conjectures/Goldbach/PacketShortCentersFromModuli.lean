import Mathlib

noncomputable section

namespace Conjectures.Goldbach.PacketShortCentersFromModuli_aux

def Qf (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2

abbrev smoothf (n q : ℕ) : Prop := ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Qf n))^8

abbrev ofun (n q : ℕ) : Prop :=
  q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Qf n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty

def Lf (n : ℕ) : ℕ := max 1 (Nat.log 2 n / 2)

def Kf (n : ℕ) (t : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (Lf n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/((Lf n:ℕ):ℝ)

def wf (n q : ℕ) : ℝ := min (1:ℝ) ((q:ℝ)/((Qf n:ℕ):ℝ))/((Nat.totient q:ℕ):ℝ)

def cardf (n q : ℕ) : ℕ :=
  ((Finset.range (q+1)).filter
    (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < Kf n ((a:ℝ)/(q:ℝ)))).card

def Sf (n : ℕ) : Finset ℕ := Finset.Icc 1 ((Qf n)^2)

lemma wf_nonneg (n q : ℕ) : 0 ≤ wf n q := by
  apply div_nonneg
  · exact le_min zero_le_one (div_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg (Qf n)))
  · exact Nat.cast_nonneg _

lemma card_coprime_le (q : ℕ) :
    ((Finset.range (q+1)).filter (fun a => Nat.Coprime a q)).card ≤ Nat.totient q + 1 := by
  have hsub : (Finset.range (q+1)).filter (fun a => Nat.Coprime a q) ⊆
      insert q ((Finset.range q).filter (fun a => Nat.Coprime q a)) := by
    intro a ha
    obtain ⟨har, hac⟩ := Finset.mem_filter.mp ha
    rw [Finset.mem_range] at har
    rcases Nat.lt_or_ge a q with h | h
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, hac.symm⟩)
    · exact Finset.mem_insert.mpr (Or.inl (by omega))
  calc ((Finset.range (q+1)).filter (fun a => Nat.Coprime a q)).card
      ≤ (insert q ((Finset.range q).filter (fun a => Nat.Coprime q a))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.range q).filter (fun a => Nat.Coprime q a)).card + 1 :=
        Finset.card_insert_le q _
    _ = Nat.totient q + 1 := by rw [Nat.totient_eq_card_coprime]

lemma cardf_le (n q : ℕ) (hq : 1 ≤ q) : cardf n q ≤ 2 * Nat.totient q := by
  have h1 : cardf n q ≤ ((Finset.range (q+1)).filter (fun a => Nat.Coprime a q)).card := by
    unfold cardf
    refine Finset.card_le_card ?_
    intro a ha
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2.1⟩
  have h2 := card_coprime_le q
  have h3 : 1 ≤ Nat.totient q := Nat.totient_pos.mpr (by omega)
  omega

lemma term_le (n q : ℕ) (hq : 1 ≤ q) :
    min (1:ℝ) ((q:ℝ)/((Qf n:ℕ):ℝ)) * ((cardf n q:ℕ):ℝ) / ((Nat.totient q:ℕ):ℝ)^2
      ≤ 2 * wf n q := by
  have hm : (0:ℝ) ≤ min (1:ℝ) ((q:ℝ)/((Qf n:ℕ):ℝ)) :=
    le_min zero_le_one (div_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg (Qf n)))
  have hc : ((cardf n q:ℕ):ℝ) ≤ 2 * ((Nat.totient q:ℕ):ℝ) := by
    exact_mod_cast cardf_le n q hq
  have hphipos : (0:ℝ) < ((Nat.totient q:ℕ):ℝ) := by
    have h : 0 < Nat.totient q := Nat.totient_pos.mpr (by omega)
    exact_mod_cast h
  have hphine : ((Nat.totient q:ℕ):ℝ) ≠ 0 := hphipos.ne'
  have hstep : min (1:ℝ) ((q:ℝ)/((Qf n:ℕ):ℝ)) * ((cardf n q:ℕ):ℝ) / ((Nat.totient q:ℕ):ℝ)^2
      ≤ min (1:ℝ) ((q:ℝ)/((Qf n:ℕ):ℝ)) * (2 * ((Nat.totient q:ℕ):ℝ))
        / ((Nat.totient q:ℕ):ℝ)^2 := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hc hm
  have hstep2 : min (1:ℝ) ((q:ℝ)/((Qf n:ℕ):ℝ)) * (2 * ((Nat.totient q:ℕ):ℝ))
      / ((Nat.totient q:ℕ):ℝ)^2 = 2 * wf n q := by
    unfold wf
    field_simp
  linarith

set_option maxHeartbeats 400000 in
lemma sum_bound (n : ℕ) :
    (∑ q ∈ (Sf n).filter (fun q => ofun n q),
        min (1:ℝ) ((q:ℝ)/((Qf n:ℕ):ℝ)) * ((cardf n q:ℕ):ℝ) / ((Nat.totient q:ℕ):ℝ)^2)
      ≤ 2 * ((∑ q ∈ (Sf n).filter (fun q => smoothf n q), wf n q)
        + ∑ q ∈ (Sf n).filter (fun q => ofun n q ∧ ¬ smoothf n q), wf n q) := by
  have hterm : ∀ q ∈ (Sf n).filter (fun q => ofun n q),
      min (1:ℝ) ((q:ℝ)/((Qf n:ℕ):ℝ)) * ((cardf n q:ℕ):ℝ) / ((Nat.totient q:ℕ):ℝ)^2
        ≤ 2 * wf n q := by
    intro q hq
    exact term_le n q (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
  have hC : (∑ q ∈ (Sf n).filter (fun q => ofun n q),
        min (1:ℝ) ((q:ℝ)/((Qf n:ℕ):ℝ)) * ((cardf n q:ℕ):ℝ) / ((Nat.totient q:ℕ):ℝ)^2)
      ≤ 2 * ∑ q ∈ (Sf n).filter (fun q => ofun n q), wf n q := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hsub : (Sf n).filter (fun q => ofun n q) ⊆
      (Sf n).filter (fun q => smoothf n q) ∪ (Sf n).filter (fun q => ofun n q ∧ ¬ smoothf n q) := by
    intro q hq
    obtain ⟨hqs, ho⟩ := Finset.mem_filter.mp hq
    rcases Classical.em (smoothf n q) with hs | hs
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hqs, hs⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hqs, ho, hs⟩))
  have hdisj : Disjoint ((Sf n).filter (fun q => smoothf n q))
      ((Sf n).filter (fun q => ofun n q ∧ ¬ smoothf n q)) := by
    refine Finset.disjoint_left.mpr ?_
    intro q hq1
    intro hq2
    exact (Finset.mem_filter.mp hq2).2.2 (Finset.mem_filter.mp hq1).2
  have hU : (∑ q ∈ (Sf n).filter (fun q => ofun n q), wf n q)
      ≤ (∑ q ∈ (Sf n).filter (fun q => smoothf n q), wf n q)
        + ∑ q ∈ (Sf n).filter (fun q => ofun n q ∧ ¬ smoothf n q), wf n q := by
    calc (∑ q ∈ (Sf n).filter (fun q => ofun n q), wf n q)
        ≤ ∑ q ∈ (Sf n).filter (fun q => smoothf n q) ∪
            (Sf n).filter (fun q => ofun n q ∧ ¬ smoothf n q), wf n q :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq hq' => wf_nonneg n q)
      _ = (∑ q ∈ (Sf n).filter (fun q => smoothf n q), wf n q)
          + ∑ q ∈ (Sf n).filter (fun q => ofun n q ∧ ¬ smoothf n q), wf n q :=
          Finset.sum_union hdisj
  exact le_trans hC (mul_le_mul_of_nonneg_left hU (by norm_num))

end Conjectures.Goldbach.PacketShortCentersFromModuli_aux

open Conjectures.Goldbach.PacketShortCentersFromModuli_aux (Sf wf Qf cardf ofun smoothf sum_bound)

set_option maxHeartbeats 400000 in
theorem Conjectures.Goldbach.PacketShortCentersFromModuli :
(let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let smooth := fun n q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^8; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => smooth n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ))/(Nat.totient q:ℝ)) ≤ ε) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty; let smooth := fun n q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^8; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q ∧ ¬smooth n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ))/(Nat.totient q:ℝ)) ≤ ε) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) * (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) / (Nat.totient q:ℝ)^2) ≤ ε) := by
  intro H1 H2
  dsimp only at H1 H2 ⊢
  intro ε hε
  obtain ⟨N1, hN1⟩ := H1 (ε/4) (by positivity)
  obtain ⟨N2, hN2⟩ := H2 (ε/4) (by positivity)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_max_left N1 N2) hn
  have hn2 : N2 ≤ n := le_trans (le_max_right N1 N2) hn
  have e1 : (∑ q ∈ (Sf n).filter (fun q => smoothf n q), wf n q) ≤ ε/4 := hN1 n hn1
  have e2 : (∑ q ∈ (Sf n).filter (fun q => ofun n q ∧ ¬ smoothf n q), wf n q) ≤ ε/4 := hN2 n hn2
  have key := sum_bound n
  show (∑ q ∈ (Sf n).filter (fun q => ofun n q),
      min (1:ℝ) ((q:ℝ)/((Qf n:ℕ):ℝ)) * ((cardf n q:ℕ):ℝ) / ((Nat.totient q:ℕ):ℝ)^2) ≤ ε
  linarith
