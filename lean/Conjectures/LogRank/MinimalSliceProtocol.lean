import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank

/- The rank-sized protocol and its supporting lemmas are from Hou Muyang's
   proof in goldbach-proofs PR #88, commit 94de74a4616ae7fb129c05b5a935bb51d6dbb7f6,
   under Apache-2.0. -/
namespace MinimalSliceProtocolSource

open scoped BigOperators

private lemma sum_zero_of_all_ksubsets (n k : ℕ) (w : Fin n → ℝ)
    (hk1 : 1 ≤ k) (hkn : k + 2 ≤ n)
    (hz : ∀ B : Finset (Fin n), B.card = k → Finset.sum B w = 0) :
    ∀ x, w x = 0 := by
  classical
  have hconst : ∀ e f : Fin n, w e = w f := by
    intro e f
    by_cases hef : e = f
    · rw [hef]
    · have hUcard : ((Finset.univ : Finset (Fin n)) \ ({e, f} : Finset (Fin n))).card = n - 2 := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
        have h2 : ({e, f} : Finset (Fin n)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simpa using hef), Finset.card_singleton]
        rw [h2]
        simp
      have hcard : k - 1 ≤ ((Finset.univ : Finset (Fin n)) \ ({e, f} : Finset (Fin n))).card := by
        rw [hUcard]
        omega
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcard
      have he_notT : e ∉ T := by
        intro h
        have h' := hTsub h
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ,
          true_and] at h'
        exact h' (by simp)
      have hf_notT : f ∉ T := by
        intro h
        have h' := hTsub h
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ,
          true_and] at h'
        exact h' (by simp)
      have hBcard : (insert e T).card = k := by
        rw [Finset.card_insert_of_notMem he_notT]
        omega
      have hB'card : (insert f T).card = k := by
        rw [Finset.card_insert_of_notMem hf_notT]
        omega
      have hzB := hz (insert e T) hBcard
      have hzB' := hz (insert f T) hB'card
      rw [Finset.sum_insert he_notT] at hzB
      rw [Finset.sum_insert hf_notT] at hzB'
      linarith
  have hne : (k : ℝ) ≠ 0 := by
    have hkpos : 0 < k := by omega
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hkpos)
  obtain ⟨B0, hB0card⟩ : ∃ B : Finset (Fin n), B.card = k := by
    have hle : k ≤ (Finset.univ : Finset (Fin n)).card := by
      simp
      omega
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hle
    exact ⟨B, hBcard⟩
  have hz0 := hz B0 hB0card
  intro x
  have hsum : Finset.sum B0 w = (k : ℝ) * w x := by
    have hstep : ∀ y ∈ B0, w y = w x := fun y _ => hconst y x
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, hB0card]
    simp [nsmul_eq_mul]
  rw [hsum] at hz0
  exact (mul_eq_zero.mp hz0).resolve_left hne



private lemma chi_diff_indep (n k : ℕ) (Y : Finset (Finset (Fin n)))
    (hk1 : 1 ≤ k) (hkn : k + 2 ≤ n)
    (huniq : ∀ (w : Fin n → ℝ) (C : ℝ), (∀ B ∈ Y, Finset.sum B w = C) →
      ∀ B : Finset (Fin n), B.card = k → Finset.sum B w = C)
    (S : Finset (Fin n)) (e0 : Fin n) (c : Fin n → ℝ)
    (hc : ∀ j : ↥Y, (∑ e ∈ S, c e * ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) -
      (if e0 ∈ (j:↥Y).val then (1:ℝ) else 0))) = 0) :
    ∀ e ∈ S, e ≠ e0 → c e = 0 := by
  classical
  have hA : ∀ B : Finset (Fin n),
      (∑ e ∈ S, c e * (if e ∈ B then (1:ℝ) else 0)) = ∑ x ∈ B, (if x ∈ S then c x else 0) := by
    intro B
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.inter_comm]
  set T : ℝ := ∑ e ∈ S, c e with hT
  have hBsum : ∀ B : Finset (Fin n),
      (∑ x ∈ B, (if x = e0 then T else 0)) = T * (if e0 ∈ B then (1:ℝ) else 0) := by
    intro B
    rw [Finset.sum_ite_eq']
    by_cases h : e0 ∈ B <;> simp [h]
  let w : Fin n → ℝ := fun x => (if x ∈ S then c x else 0) - (if x = e0 then T else 0)
  have hw : ∀ B ∈ Y, Finset.sum B w = 0 := by
    intro B hBmem
    have hcB := hc ⟨B, hBmem⟩
    have hexp : (∑ e ∈ S, c e * ((if e ∈ B then (1:ℝ) else 0) - (if e0 ∈ B then (1:ℝ) else 0)))
        = (∑ e ∈ S, c e * (if e ∈ B then (1:ℝ) else 0)) -
          (∑ e ∈ S, c e * (if e0 ∈ B then (1:ℝ) else 0)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      ring
    have h2 : (∑ e ∈ S, c e * (if e0 ∈ B then (1:ℝ) else 0))
        = T * (if e0 ∈ B then (1:ℝ) else 0) := by
      rw [hT, Finset.sum_mul]
    rw [hexp, h2, hA] at hcB
    have hsplit : Finset.sum B w = (∑ x ∈ B, (if x ∈ S then c x else 0)) -
        (∑ x ∈ B, (if x = e0 then T else 0)) := by
      simp only [w, Finset.sum_sub_distrib]
    rw [hsplit, hBsum]
    linarith
  have hw0 : ∀ B : Finset (Fin n), B.card = k → Finset.sum B w = 0 := by
    intro B hBc
    exact huniq w 0 hw B hBc
  have hwz : ∀ x, w x = 0 := sum_zero_of_all_ksubsets n k w hk1 hkn hw0
  intro e heS hene
  have hwe : w e = c e := by
    simp only [w]
    simp [heS, hene]
  rw [← hwe]
  exact hwz e

private theorem rank_sized_protocol :
    ∀ (n k m : ℕ) (A : Fin m → Finset (Fin n)) (Y : Finset (Finset (Fin n))) (a : ℤ), 2 ≤ k → k+2 ≤ n → let layer := (Finset.univ : Finset (Fin n)).powersetCard k; let adj := fun (A B : Finset (Fin n)) (a : ℤ) => ((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a+1; let detects := fun (Y : Finset (Finset (Fin n))) => ∀ A : Finset (Fin n), 2 ≤ A.card → A.card + 2 ≤ n → ∀ a : ℤ, ∃ B ∈ Y, ¬ adj A B a; let lin := fun (w : Fin n → ℝ) (B : Finset (Fin n)) => Finset.sum B w; let uniqueOn := fun (Y : Finset (Finset (Fin n))) => ∀ (w : Fin n → ℝ) (c : ℝ), (∀ B ∈ Y, lin w B = c) → ∀ B ∈ layer, lin w B = c; Y.Nonempty → Y ⊆ layer → detects Y → uniqueOn Y → (∀ i, ∀ B ∈ Y, adj (A i) B a) → let M : Matrix (Fin m) (↥Y) ℝ := fun i j => (((A i ∩ j.val).card : ℝ) - (a : ℝ)); ∃ send : Fin m → Fin (M.rank+1), ∃ reply : Fin (M.rank+1) → ↥Y → Bool, ∃ out : Fin m → Bool → Bool, ∀ i j, (out i (reply (send i) j) = true ↔ M i j = 1) := by
  intro n k m A Y a hk hkn
  classical
  unfold Matrix
  dsimp only
  intro hYne hYsub hdet huniq hrow
  set M : Matrix (Fin m) (↥Y) ℝ := fun i j => ((A i ∩ (j:↥Y).val).card : ℝ) - (a : ℝ) with hM
  have hMval : ∀ (i : Fin m) (j : ↥Y), M i j = ((A i ∩ (j:↥Y).val).card : ℝ) - (a : ℝ) := fun i j => by rw [hM]
  have hYcard : ∀ B ∈ Y, B.card = k := by
    intro B hB
    have h := hYsub hB
    simp only [Finset.mem_powersetCard] at h
    exact h.2
  have hM01 : ∀ (i : Fin m) (j : ↥Y), M i j = 0 ∨ M i j = 1 := by
    intro i j
    have h := hrow i (j:↥Y) j.2
    rcases h with h | h
    · left
      rw [hM]
      have h' : ((A i ∩ (j:↥Y).val).card : ℝ) = (a : ℝ) := by exact_mod_cast h
      linarith
    · right
      rw [hM]
      have h' : ((A i ∩ (j:↥Y).val).card : ℝ) = ((a + 1 : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      linarith
  have hclass : ∀ i : Fin m, (A i).card ≤ 1 ∨ n - 1 ≤ (A i).card := by
    intro i
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hle : (A i).card + 2 ≤ n := by omega
    obtain ⟨B, hBY, hBadj⟩ := hdet (A i) h1 hle a
    exact hBadj (hrow i B hBY)

  have hAcases : ∀ i : Fin m, A i = ∅ ∨ (∃ e : Fin n, A i = {e}) ∨ (∃ e : Fin n, A i = Finset.univ.erase e) ∨ A i = Finset.univ := by
    intro i
    rcases hclass i with hsmall | hbig
    · have hc : (A i).card = 0 ∨ (A i).card = 1 := by omega
      rcases hc with hc | hc
      · exact Or.inl (Finset.card_eq_zero.mp hc)
      · obtain ⟨e, he⟩ := Finset.card_eq_one.mp hc
        exact Or.inr (Or.inl ⟨e, he⟩)
    · have hle : (A i).card ≤ n := by
        have h2 := Finset.card_le_card (Finset.subset_univ (A i))
        simpa using h2
      have hc : (A i).card = n - 1 ∨ (A i).card = n := by omega
      rcases hc with hc | hc
      · have hcomp : (Finset.univ \ A i).card = 1 := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ (A i)), hc, Finset.card_univ,
            Fintype.card_fin]
          omega
        obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcomp
        refine Or.inr (Or.inr (Or.inl ⟨e, ?_⟩))
        ext x
        constructor
        · intro hx
          rw [Finset.mem_erase]
          refine ⟨?_, Finset.mem_univ x⟩
          intro hxe
          have hmem : e ∈ Finset.univ \ A i := by
            rw [he]
            simp
          rw [Finset.mem_sdiff] at hmem
          exact hmem.2 (hxe ▸ hx)
        · intro hx
          by_contra hxA
          have hmem : x ∈ Finset.univ \ A i := by
            rw [Finset.mem_sdiff]
            exact ⟨Finset.mem_univ x, hxA⟩
          rw [he] at hmem
          have hxe : x = e := by simpa using hmem
          have hne : x ≠ e := (Finset.mem_erase.mp hx).1
          exact hne hxe
      · exact Or.inr (Or.inr (Or.inr (Finset.eq_of_subset_of_card_le (Finset.subset_univ (A i)) (by simp [hc]))))
  have hrowkind : ∀ i : Fin m,
      (∃ v : ℝ, ∀ j : ↥Y, M i j = v) ∨
      (∃ e : Fin n, ∀ j : ↥Y, M i j = ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ))) ∨
      (∃ e : Fin n, ∀ j : ↥Y, M i j = ((k:ℝ) - (if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ))) := by
    intro i
    rcases hAcases i with hA | hA | hA | hA
    · left
      refine ⟨-(a:ℝ), ?_⟩
      intro j
      rw [hMval, hA]
      simp
    · obtain ⟨e, he⟩ := hA
      refine Or.inr (Or.inl ⟨e, ?_⟩)
      intro j
      rw [hMval, he]
      have hcard : (({e} ∩ (j:↥Y).val).card : ℝ) = (if e ∈ (j:↥Y).val then (1:ℝ) else 0) := by
        by_cases hmem : e ∈ (j:↥Y).val
        · have h1 : ({e} ∩ (j:↥Y).val) = {e} := by
            ext x
            simp only [Finset.mem_inter, Finset.mem_singleton]
            constructor
            · exact fun h => h.1
            · intro hx
              exact ⟨hx, hx ▸ hmem⟩
          rw [h1]
          simp [hmem]
        · have h1 : ({e} ∩ (j:↥Y).val) = ∅ := by
            ext x
            simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false,
              not_and]
            intro hxe hxb
            exact hmem (hxe ▸ hxb)
          rw [h1]
          simp [hmem]
      rw [hcard]
    · obtain ⟨e, he⟩ := hA
      refine Or.inr (Or.inr ⟨e, ?_⟩)
      intro j
      rw [hMval, he]
      have hinter : ((Finset.univ.erase e) ∩ (j:↥Y).val) = ((j:↥Y).val).erase e := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ]
        tauto
      have hcard : ((((j:↥Y).val).erase e).card : ℝ) = (k:ℝ) - (if e ∈ (j:↥Y).val then (1:ℝ) else 0) := by
        by_cases hmem : e ∈ (j:↥Y).val
        · rw [Finset.card_erase_of_mem hmem, hYcard (j:↥Y) j.2]
          simp only [hmem, ite_true]
          rw [Nat.cast_sub (by omega : (1:ℕ) ≤ k)]
          norm_num
        · rw [Finset.erase_eq_of_notMem hmem, hYcard (j:↥Y) j.2]
          simp [hmem]
      rw [hinter, hcard]
    · left
      refine ⟨(k:ℝ) - (a:ℝ), ?_⟩
      intro j
      rw [hMval, hA]
      have h1 : (Finset.univ ∩ (j:↥Y).val) = (j:↥Y).val := by simp
      rw [h1, hYcard (j:↥Y) j.2]
  have hUa : ∀ (i : Fin m) (e : Fin n), (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) →
      (∀ j : ↥Y, M i j = ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ))) → a = 0 := by
    intro i e hnc hrow_
    obtain ⟨B0, hB0⟩ := hYne
    let j0 : ↥Y := ⟨B0, hB0⟩
    obtain ⟨j1, hj1⟩ : ∃ j : ↥Y, M i j ≠ M i j0 := by
      by_contra hcon
      push Not at hcon
      exact hnc ⟨M i j0, fun j => hcon j⟩
    have hχ : (if e ∈ (j1:↥Y).val then (1:ℝ) else 0) ≠
        (if e ∈ (j0:↥Y).val then (1:ℝ) else 0) := by
      intro hh
      exact hj1 (by rw [hrow_ j1, hrow_ j0, hh])
    by_cases he1 : e ∈ (j1:↥Y).val
    · by_cases he0 : e ∈ (j0:↥Y).val
      · exact absurd (by simp [he1, he0]) hχ
      · have h1 := hM01 i j1
        have h2 := hM01 i j0
        rw [hrow_ j1] at h1
        rw [hrow_ j0] at h2
        simp only [he1, he0, ite_true, ite_false] at h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exfalso; linarith
        · exfalso; linarith
        · have hz : (a:ℝ) = 0 := by linarith
          exact_mod_cast hz
        · exfalso; linarith
    · by_cases he0 : e ∈ (j0:↥Y).val
      · have h1 := hM01 i j1
        have h2 := hM01 i j0
        rw [hrow_ j1] at h1
        rw [hrow_ j0] at h2
        simp only [he1, he0, ite_true, ite_false] at h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exfalso; linarith
        · have hz : (a:ℝ) = 0 := by linarith
          exact_mod_cast hz
        · exfalso; linarith
        · exfalso; linarith
      · exact absurd (by simp [he1, he0]) hχ
  have hWa : ∀ (i : Fin m) (e : Fin n), (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) →
      (∀ j : ↥Y, M i j = ((k:ℝ) - (if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ))) → a = k - 1 := by
    intro i e hnc hrow_
    obtain ⟨B0, hB0⟩ := hYne
    let j0 : ↥Y := ⟨B0, hB0⟩
    obtain ⟨j1, hj1⟩ : ∃ j : ↥Y, M i j ≠ M i j0 := by
      by_contra hcon
      push Not at hcon
      exact hnc ⟨M i j0, fun j => hcon j⟩
    have hχ : (if e ∈ (j1:↥Y).val then (1:ℝ) else 0) ≠
        (if e ∈ (j0:↥Y).val then (1:ℝ) else 0) := by
      intro hh
      exact hj1 (by rw [hrow_ j1, hrow_ j0, hh])
    by_cases he1 : e ∈ (j1:↥Y).val
    · by_cases he0 : e ∈ (j0:↥Y).val
      · exact absurd (by simp [he1, he0]) hχ
      · have h1 := hM01 i j1
        have h2 := hM01 i j0
        rw [hrow_ j1] at h1
        rw [hrow_ j0] at h2
        simp only [he1, he0, ite_true, ite_false] at h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exfalso; linarith
        · have hz : (a:ℝ) = (k:ℝ) - 1 := by linarith
          exact_mod_cast hz
        · exfalso; linarith
        · exfalso; linarith
    · by_cases he0 : e ∈ (j0:↥Y).val
      · have h1 := hM01 i j1
        have h2 := hM01 i j0
        rw [hrow_ j1] at h1
        rw [hrow_ j0] at h2
        simp only [he1, he0, ite_true, ite_false] at h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exfalso; linarith
        · exfalso; linarith
        · have hz : (a:ℝ) = (k:ℝ) - 1 := by linarith
          exact_mod_cast hz
        · exfalso; linarith
      · exact absurd (by simp [he1, he0]) hχ
  have hexcl : ¬ ((∃ i, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) ∧
      (∃ e : Fin n, ∀ j : ↥Y, M i j = ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ)))) ∧
      (∃ i, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) ∧
      (∃ e : Fin n, ∀ j : ↥Y, M i j = ((k:ℝ) - (if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ))))) := by
    rintro ⟨⟨i1, h1nc, e1, h1r⟩, ⟨i2, h2nc, e2, h2r⟩⟩
    have ha0 : a = 0 := hUa i1 e1 h1nc h1r
    have hak : a = k - 1 := hWa i2 e2 h2nc h2r
    omega
  have hχ01 : ∀ (e : Fin n) (j : ↥Y), ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 1) ∨
      ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 0) := by
    intro e j
    by_cases h : e ∈ (j:↥Y).val <;> simp [h]
  have hncdata : ∀ i : Fin m, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) →
      ∃ (e : Fin n) (jO jZ : ↥Y),
        ((if e ∈ (jO:↥Y).val then (1:ℝ) else 0) = 1) ∧
        ((if e ∈ (jZ:↥Y).val then (1:ℝ) else 0) = 0) ∧
        (∀ j : ↥Y, (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 1 → M i j = M i jO) ∧
        (∀ j : ↥Y, (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 0 → M i j = M i jZ) := by
    intro i hnc
    rcases hrowkind i with hC | ⟨e, he⟩ | ⟨e, he⟩
    · exact absurd hC hnc
    · have hrow : ∀ j : ↥Y, M i j = ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ)) := he
      have hex1 : ∃ j : ↥Y, (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 1 := by
        by_contra hcon
        push Not at hcon
        apply hnc
        refine ⟨-(a:ℝ), fun j => ?_⟩
        rw [hrow j]
        have h0 : (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 0 := by
          rcases hχ01 e j with h | h
          · exact absurd h (hcon j)
          · exact h
        rw [h0]; ring
      obtain ⟨jO, hjO⟩ := hex1
      have hex0 : ∃ j : ↥Y, (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 0 := by
        by_contra hcon
        push Not at hcon
        apply hnc
        refine ⟨1 - (a:ℝ), fun j => ?_⟩
        rw [hrow j]
        have h1 : (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 1 := by
          rcases hχ01 e j with h | h
          · exact h
          · exact absurd h (hcon j)
        rw [h1]
      obtain ⟨jZ, hjZ⟩ := hex0
      exact ⟨e, jO, jZ, hjO, hjZ,
        fun j hj => by rw [hrow j, hrow jO, hj, hjO],
        fun j hj => by rw [hrow j, hrow jZ, hj, hjZ]⟩
    · have hrow : ∀ j : ↥Y, M i j = ((k:ℝ) - (if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ)) := he
      have hex1 : ∃ j : ↥Y, (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 1 := by
        by_contra hcon
        push Not at hcon
        apply hnc
        refine ⟨(k:ℝ) - (a:ℝ), fun j => ?_⟩
        rw [hrow j]
        have h0 : (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 0 := by
          rcases hχ01 e j with h | h
          · exact absurd h (hcon j)
          · exact h
        rw [h0]; ring
      obtain ⟨jO, hjO⟩ := hex1
      have hex0 : ∃ j : ↥Y, (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 0 := by
        by_contra hcon
        push Not at hcon
        apply hnc
        refine ⟨(k:ℝ) - 1 - (a:ℝ), fun j => ?_⟩
        rw [hrow j]
        have h1 : (if e ∈ (j:↥Y).val then (1:ℝ) else 0) = 1 := by
          rcases hχ01 e j with h | h
          · exact h
          · exact absurd h (hcon j)
        rw [h1]
      obtain ⟨jZ, hjZ⟩ := hex0
      exact ⟨e, jO, jZ, hjO, hjZ,
        fun j hj => by rw [hrow j, hrow jO, hj, hjO],
        fun j hj => by rw [hrow j, hrow jZ, hj, hjZ]⟩
  have hnpos : 0 < n := by omega
  let dfin : Fin n := ⟨0, hnpos⟩
  have hUformAll : (∃ i : Fin m, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) ∧
      (∃ e : Fin n, ∀ j : ↥Y, M i j = ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ)))) →
      ∀ i, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) →
      ∃ e : Fin n, ∀ j : ↥Y, M i j = ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ)) := by
    intro hU i hnc
    rcases hrowkind i with hC | hU' | hW'
    · exact absurd hC hnc
    · exact hU'
    · exact absurd ⟨hU, ⟨i, hnc, hW'⟩⟩ hexcl
  have hWformAll : (¬ ∃ i : Fin m, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) ∧
      (∃ e : Fin n, ∀ j : ↥Y, M i j = ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ)))) →
      ∀ i, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) →
      ∃ e : Fin n, ∀ j : ↥Y, M i j = ((k:ℝ) - (if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ)) := by
    intro hU i hnc
    rcases hrowkind i with hC | hU' | hW'
    · exact absurd hC hnc
    · exact absurd ⟨i, hnc, hU'⟩ hU
    · exact hW'
  obtain ⟨sb, cc, hsign, hrowu⟩ : ∃ (sb : Bool) (cc : Fin m → Fin n), (sb = true ∨ sb = false) ∧
      ∀ i, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) → ∀ j : ↥Y,
        M i j = (if sb then (if cc i ∈ (j:↥Y).val then (1:ℝ) else 0)
          else (if cc i ∈ (j:↥Y).val then (0:ℝ) else 1)) := by
    by_cases hU : ∃ i : Fin m, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) ∧
        (∃ e : Fin n, ∀ j : ↥Y, M i j = ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ)))
    · let cc' : Fin m → Fin n := fun i => if h : (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) then
          Classical.choose (hUformAll hU i h) else dfin
      refine ⟨true, cc', Or.inl rfl, ?_⟩
      intro i hnc j
      have hcc' : cc' i = Classical.choose (hUformAll hU i hnc) := by
        simp only [cc']
        exact dite_eq_left hnc
      set c : Fin n := Classical.choose (hUformAll hU i hnc) with hc_def
      rw [show cc' i = c from hcc']
      have hspec : M i j = (if c ∈ (j:↥Y).val then (1:ℝ) else 0) - (a:ℝ) := by
        rw [hc_def]
        exact Classical.choose_spec (hUformAll hU i hnc) j
      have ha0 : a = 0 := by
        rw [hc_def] at *
        exact hUa i _ hnc (Classical.choose_spec (hUformAll hU i hnc))
      rw [hspec, ha0]
      simp only [Int.cast_zero, sub_zero]
      by_cases hmem : c ∈ (j:↥Y).val <;> simp [hmem]
    · let cc' : Fin m → Fin n := fun i => if h : (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) then
          Classical.choose (hWformAll hU i h) else dfin
      refine ⟨false, cc', Or.inr rfl, ?_⟩
      intro i hnc j
      have hcc' : cc' i = Classical.choose (hWformAll hU i hnc) := by
        simp only [cc']
        exact dite_eq_left hnc
      set c : Fin n := Classical.choose (hWformAll hU i hnc) with hc_def
      rw [show cc' i = c from hcc']
      have hspec : M i j = ((k:ℝ) - (if c ∈ (j:↥Y).val then (1:ℝ) else 0)) - (a:ℝ) := by
        rw [hc_def]
        exact Classical.choose_spec (hWformAll hU i hnc) j
      have hak : a = k - 1 := by
        rw [hc_def] at *
        exact hWa i _ hnc (Classical.choose_spec (hWformAll hU i hnc))
      have hk' : ((a:ℝ)) = (k:ℝ) - 1 := by
        have h2 : ((a:ℝ)) = ((((k:ℤ) - 1 : ℤ)) : ℝ) := by rw [hak]
        simpa using h2
      rw [hspec, hk']
      by_cases hmem : c ∈ (j:↥Y).val <;> simp [hmem]
  let S : Finset (Fin n) := (Finset.univ.filter (fun i : Fin m =>
    ¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v)).image cc
  have hcval : ∀ i, (∃ v : ℝ, ∀ j : ↥Y, M i j = v) → ∀ j : ↥Y, M i j = (if h : (∃ v : ℝ, ∀ j : ↥Y, M i j = v) then Classical.choose h else 0) := by
    intro i h j
    rw [dite_eq_left h]
    exact Classical.choose_spec h j

  have huniq' : ∀ (w : Fin n → ℝ) (C : ℝ), (∀ B ∈ Y, Finset.sum B w = C) →
      ∀ B : Finset (Fin n), B.card = k → Finset.sum B w = C := by
    intro w C hw B hB
    exact huniq w C hw B (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ B, hB⟩)
  have hSrank : S.card ≤ M.rank + 1 := by
    by_cases hzero : S.card = 0
    · omega
    · have hpos : 0 < S.card := by omega
      obtain ⟨e0, he0S⟩ := Finset.card_pos.mp hpos
      have hwit : ∀ e ∈ S, ∃ i : Fin m, (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) ∧ cc i = e := by
        intro e he
        have he' : e ∈ (Finset.univ.filter (fun i : Fin m =>
            ¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v)).image cc := by
          simpa only [S] using he
        obtain ⟨i, hi, hci⟩ := Finset.mem_image.mp he'
        exact ⟨i, (Finset.mem_filter.mp hi).2, hci⟩
      let iw : (e : Fin n) → e ∈ S → Fin m := fun e he => Classical.choose (hwit e he)
      have hiw : ∀ (e : Fin n) (he : e ∈ S), (¬ ∃ v : ℝ, ∀ j : ↥Y, M (iw e he) j = v) ∧ cc (iw e he) = e := by
        intro e he
        exact Classical.choose_spec (hwit e he)
      let sv : ℝ := if sb then (1:ℝ) else -1
      have hsvne : sv ≠ 0 := by
        simp only [sv]
        split_ifs <;> norm_num
      -- rows at witnesses are affine in the coordinate indicator
      have hform : ∀ (e : Fin n) (he : e ∈ S) (j : ↥Y),
          M (iw e he) j - M (iw e0 he0S) j = sv * ((if e ∈ (j:↥Y).val then (1:ℝ) else 0) -
            (if e0 ∈ (j:↥Y).val then (1:ℝ) else 0)) := by
        intro e he j
        have h1 := hrowu (iw e he) (hiw e he).1 j
        have h2 := hrowu (iw e0 he0S) (hiw e0 he0S).1 j
        rw [h1, h2, (hiw e he).2, (hiw e0 he0S).2]
        simp only [sv]
        by_cases hb : sb
        · simp only [hb, ite_true, ite_true]
          by_cases hq : e ∈ (j:↥Y).val <;> by_cases hq2 : e0 ∈ (j:↥Y).val <;> simp [hq, hq2]
        · simp only [hb, Bool.false_eq_true, ite_false]
          by_cases hq : e ∈ (j:↥Y).val <;> by_cases hq2 : e0 ∈ (j:↥Y).val <;> simp [hq, hq2]
      let u : ↥(S.erase e0) → (↥Y → ℝ) := fun t => fun j =>
        M (iw t.1 (Finset.mem_of_mem_erase t.2)) j - M (iw e0 he0S) j
      have hind : LinearIndependent ℝ u := by
        rw [linearIndependent_iff']
        intro T g hsum t ht
        set c : Fin n → ℝ := fun x => sv * (∑ i ∈ T, if (i.1 : Fin n) = x then g i else 0) with hcdef
        have hchi : ∀ j : ↥Y, (∑ x ∈ S, c x * ((if x ∈ (j:↥Y).val then (1:ℝ) else 0) -
            (if e0 ∈ (j:↥Y).val then (1:ℝ) else 0))) = 0 := by
          intro j
          set F : Fin n → ℝ := fun x => (if x ∈ (j:↥Y).val then (1:ℝ) else 0) -
            (if e0 ∈ (j:↥Y).val then (1:ℝ) else 0) with hF
          have hpt : (∑ i ∈ T, g i * u i j) = 0 := by
            have h2 : (∑ i ∈ T, g i • u i) j = ((0 : ↥Y → ℝ)) j := by rw [hsum]
            simpa [Pi.smul_apply, smul_eq_mul] using h2
          have h1 : (∑ x ∈ S, c x * F x) =
              sv * (∑ x ∈ S, (∑ i ∈ T, if (i.1 : Fin n) = x then g i else 0) * F x) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            simp only [hcdef]
            ring
          have h2 : (∑ x ∈ S, (∑ i ∈ T, if (i.1 : Fin n) = x then g i else 0) * F x) =
              ∑ i ∈ T, g i * F (i.1) := by
            simp only [Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            simp only [ite_mul, zero_mul]
            rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_of_mem_erase i.2)]
          have h3 : (∑ i ∈ T, g i * u i j) = sv * (∑ i ∈ T, g i * F (i.1)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            have hrow := hform i.1 (Finset.mem_of_mem_erase i.2) j
            simp only [u, hF]
            rw [hrow]
            ring
          calc (∑ x ∈ S, c x * F x) = sv * (∑ x ∈ S, (∑ i ∈ T, if (i.1 : Fin n) = x then g i else 0) * F x) := h1
            _ = sv * (∑ i ∈ T, g i * F (i.1)) := by rw [h2]
            _ = ∑ i ∈ T, g i * u i j := h3.symm
            _ = 0 := hpt
        have hk1 : 1 ≤ k := by omega
        have hcz := chi_diff_indep n k Y hk1 hkn huniq' S e0 c hchi
        have hct : c t.1 = 0 :=
          hcz t.1 (Finset.mem_of_mem_erase t.2) (Finset.ne_of_mem_erase t.2)
        have hsumt : c t.1 = sv * g t := by
          simp only [hcdef]
          congr 1
          rw [Finset.sum_eq_single t]
          · simp
          · intro i hi hit
            by_cases hh : (i.1 : Fin n) = t.1
            · exact absurd (Subtype.ext hh) hit
            · simp [hh]
          · intro ht'; exact absurd ht ht'
        rw [hsumt] at hct
        exact (mul_eq_zero.mp hct).resolve_left hsvne
      have hfin : Module.finrank ℝ (Submodule.span ℝ (Set.range u)) = S.card - 1 := by
        rw [finrank_span_eq_card hind, Fintype.card_coe, Finset.card_erase_of_mem he0S]
      have hle : Submodule.span ℝ (Set.range u) ≤ Submodule.span ℝ (Set.range M.row) := by
        rw [Submodule.span_le]
        rintro _ ⟨t, rfl⟩
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
      have hmono := Submodule.finrank_mono hle
      rw [M.rank_eq_finrank_span_row]
      omega
  let crow : Fin m → ℝ := fun i => if h : (∃ v : ℝ, ∀ j : ↥Y, M i j = v) then Classical.choose h else 0
  have hcrow : ∀ i, (h : ∃ v : ℝ, ∀ j : ↥Y, M i j = v) → ∀ j : ↥Y, M i j = crow i := by
    intro i h j
    simp only [crow]
    rw [dite_eq_left h]
    exact Classical.choose_spec h j
  by_cases hzero : S.card = 0
  · -- all rows constant
    refine ⟨fun _ => 0, fun _ _ => false, fun i _ => decide (crow i = 1), ?_⟩
    intro i j
    have hPC : (∃ v : ℝ, ∀ j : ↥Y, M i j = v) := by
      by_contra hnc
      have hmem : cc i ∈ S := by
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hnc⟩, rfl⟩
      have hempty : S = ∅ := Finset.card_eq_zero.mp hzero
      rw [hempty] at hmem
      exact absurd hmem (Finset.notMem_empty _)
    have h1 := hcrow i hPC j
    rw [decide_eq_true_iff, ← h1]
  · -- nontrivial: build the coding
    have hpos : 0 < S.card := Nat.pos_of_ne_zero hzero
    obtain ⟨e0, he0S⟩ := Finset.card_pos.mp hpos
    have hcardle : Fintype.card ↥S ≤ M.rank + 1 := by
      rwa [Fintype.card_coe]
    let enc : ↥S → Fin (M.rank + 1) := fun a => Fin.castLE hcardle (Fintype.equivFin ↥S a)
    have henc_inj : Function.Injective enc := by
      intro a b hab
      exact (Fintype.equivFin ↥S).injective (Fin.castLE_injective hcardle hab)
    let dec : Fin (M.rank + 1) → Fin n := fun m =>
      if h : ∃ a : ↥S, enc a = m then (Classical.choose h).1 else e0
    have hdec : ∀ a : ↥S, dec (enc a) = a.1 := by
      intro a
      have hex : ∃ b : ↥S, enc b = enc a := ⟨a, rfl⟩
      simp only [dec]
      rw [dite_eq_left hex]
      exact congrArg Subtype.val (henc_inj (Classical.choose_spec hex))
    let sendF : Fin m → Fin (M.rank + 1) := fun i =>
      if h : (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) then
        enc ⟨cc i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩, rfl⟩⟩
      else 0
    let replyF : Fin (M.rank + 1) → ↥Y → Bool := fun m j => decide (dec m ∈ (j:↥Y).val)
    let outF : Fin m → Bool → Bool := fun i b =>
      if h : (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v) then (if sb then b else !b)
      else decide (crow i = 1)
    refine ⟨sendF, replyF, outF, ?_⟩
    intro i j
    by_cases hnc : (¬ ∃ v : ℝ, ∀ j : ↥Y, M i j = v)
    · have hrow := hrowu i hnc j
      have hsend : sendF i = enc ⟨cc i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hnc⟩, rfl⟩⟩ := by
        simp only [sendF]
        exact dite_eq_left hnc
      have hrep : replyF (sendF i) j = decide (cc i ∈ (j:↥Y).val) := by
        simp only [replyF]
        rw [hsend, hdec]
      have hout : outF i (replyF (sendF i) j) =
          (if sb then replyF (sendF i) j else !(replyF (sendF i) j)) := by
        simp only [outF]
        exact dite_eq_left hnc
      change (outF i (replyF (sendF i) j) = true) ↔ M i j = 1
      rw [hout, hrep, hrow]
      by_cases hsb : sb
      · simp only [hsb, ite_true, decide_eq_true_iff]
        by_cases hmem : cc i ∈ (j:↥Y).val <;> simp [hmem]
      · simp only [hsb, Bool.false_eq_true, ite_false]
        by_cases hmem : cc i ∈ (j:↥Y).val <;> simp [hmem]
    · have hPC : (∃ v : ℝ, ∀ j : ↥Y, M i j = v) := by
        by_contra h2
        exact hnc h2
      have hout : outF i (replyF (sendF i) j) = decide (crow i = 1) := by
        simp only [outF]
        exact dite_eq_right hnc
      change (outF i (replyF (sendF i) j) = true) ↔ M i j = 1
      have h1 := hcrow i hPC j
      rw [hout, decide_eq_true_iff, ← h1]

end MinimalSliceProtocolSource

/- Select an independent tuple of k columns and then extend it to a basis.
   At each extension of the tuple, its span rules out at most 2^k columns.
   To count tuples that miss a row, split according to the smaller of the
   row and its complement. A large row has many comparable intersection
   buckets near the mode. For small rows, the three buckets at 0, 1 and 2
   give a uniform gap from one, and the number of rows grows polynomially. -/

namespace MinimalSlice

open scoped Classical

private def mass (k l j : ℕ) : ℝ :=
  (l.choose j : ℝ) * ((3*k+1-l).choose (k-j) : ℝ)

private theorem mass_nonneg (k l j : ℕ) : 0 ≤ mass k l j := by
  unfold mass
  positivity

private theorem mass_step {k l j : ℕ} (hl : 2*l ≤ 3*k+1) (hj : j < k) (hjl : j ≤ l) :
    mass k l (j+1) * ((j : ℝ)+1) * ((3*(k : ℝ)+1-l)-k+j+1) =
    mass k l j * ((l : ℝ)-j) * ((k : ℝ)-j) := by
  have h₁ := congrArg (fun z : ℕ => (z : ℝ)) (Nat.choose_succ_right_eq l j)
  have h₂ := congrArg (fun z : ℕ => (z : ℝ))
    (Nat.choose_succ_right_eq (3*k+1-l) (k-(j+1)))
  have hidx : k - (j+1) + 1 = k-j := by omega
  rw [hidx] at h₂
  push_cast [Nat.cast_sub hjl, Nat.cast_sub (show j ≤ k by omega),
    Nat.cast_sub (show j+1 ≤ k by omega), Nat.cast_sub (show l ≤ 3*k+1 by omega),
    Nat.cast_sub (show k-(j+1) ≤ 3*k+1-l by omega)] at h₁ h₂
  unfold mass
  linear_combination
    (((3*k+1-l).choose (k-(j+1)) : ℝ) * ((3*(k : ℝ)+1-l)-k+j+1)) * h₁ +
      (-(l.choose j : ℝ) * ((l : ℝ)-j)) * h₂

private theorem mass_mode {k l j : ℕ} (hl : 2*l ≤ 3*k+1) (hjk : j ≤ k) :
    mass k l j ≤ mass k l ((l+1)/3) := by
  let m := (l+1)/3
  have hstep : ∀ i < min k l,
      (i < m → mass k l i ≤ mass k l (i+1)) ∧
      (m ≤ i → mass k l (i+1) ≤ mass k l i) := by
    intro i hi
    have hi₁ : i < k := lt_of_lt_of_le hi (min_le_left _ _)
    have hi₂ : i < l := lt_of_lt_of_le hi (min_le_right _ _)
    have he := mass_step hl hi₁ hi₂.le
    have he' : mass k l (i+1) * (((i : ℝ)+1)*((3*(k : ℝ)+1-l)-k+i+1)) =
        mass k l i * (((l : ℝ)-i)*((k : ℝ)-i)) := by
      simpa only [mul_assoc] using he
    have hden : 0 < ((i : ℝ)+1)*((3*(k : ℝ)+1-l)-k+i+1) := by
      apply mul_pos
      · positivity
      · have hl' : 2*(l : ℝ) ≤ 3*(k : ℝ)+1 := by exact_mod_cast hl
        linarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) i]
    have hdiff : ((i : ℝ)+1)*((3*(k : ℝ)+1-l)-k+i+1) -
        ((l : ℝ)-i)*((k : ℝ)-i) = ((k : ℝ)+1)*(3*(i : ℝ)+2-l) := by ring
    constructor
    · intro h
      apply le_of_mul_le_mul_right _ hden
      rw [he']
      apply mul_le_mul_of_nonneg_left _ (mass_nonneg ..)
      have h' : 3*i+2 ≤ l := by dsimp [m] at h; omega
      have hr : (3 : ℝ)*i+2 ≤ l := by exact_mod_cast h'
      linarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (k : ℝ)+1 by positivity)
        (sub_nonpos.mpr hr)]
    · intro h
      apply le_of_mul_le_mul_right _ hden
      rw [he']
      apply mul_le_mul_of_nonneg_left _ (mass_nonneg ..)
      have h' : l ≤ 3*i+2 := by dsimp [m] at h; omega
      have hr : (l : ℝ) ≤ 3*(i : ℝ)+2 := by exact_mod_cast h'
      linarith [mul_nonneg (show 0 ≤ (k : ℝ)+1 by positivity) (sub_nonneg.mpr hr)]
  change mass k l j ≤ mass k l m
  by_cases hj : j ≤ min k l
  · have hm : m ≤ min k l := by dsimp [m]; omega
    rcases le_total j m with hjm | hmj
    · refine (Nat.le_induction (motive := fun t _ => t ≤ m → mass k l j ≤ mass k l t)
          (fun _ => le_rfl) ?_ m hjm) le_rfl
      intro i _ ih him
      exact (ih (by omega)).trans ((hstep i (by omega)).1 (by omega))
    · refine (Nat.le_induction (motive := fun t _ => t ≤ min k l → mass k l t ≤ mass k l m)
          (fun _ => le_rfl) ?_ j hmj) hj
      intro i hi ih hib
      exact ((hstep i (by omega)).2 hi).trans (ih (by omega))
  · rw [mass, Nat.choose_eq_zero_of_lt (show l < j by omega)]
    simpa using mass_nonneg k l m

private theorem near_mode_step {k l i : ℕ} (hl : 2*l ≤ 3*k+1) (hlbig : 1000000 ≤ l)
    (hi₁ : (l+1)/3 ≤ i) (hi₂ : i ≤ (l+1)/3+63) :
    (255/256 : ℝ) * mass k l i ≤ mass k l (i+1) := by
  have hik : i < k := by omega
  have hil : i ≤ l := by omega
  have he := mass_step hl hik hil
  let d : ℝ := ((i : ℝ)+1)*((3*(k : ℝ)+1-l)-k+i+1)
  let u : ℝ := ((l : ℝ)-i)*((k : ℝ)-i)
  have hdiff : d - u = ((k : ℝ)+1)*(3*(i : ℝ)+2-l) := by dsimp [d,u]; ring
  have hr₁ : (l : ℝ) ≤ 3*(i : ℝ)+2 := by
    exact_mod_cast (show l ≤ 3*i+2 by omega)
  have hr₂ : 3*(i : ℝ)+2 ≤ l+192 := by
    exact_mod_cast (show 3*i+2 ≤ l+192 by omega)
  have hibig : (330000 : ℝ) ≤ (i : ℝ)+1 := by
    exact_mod_cast (show 330000 ≤ i+1 by omega)
  have hhalf : 2*(l : ℝ) ≤ 3*(k : ℝ)+1 := by exact_mod_cast hl
  have hother : 0 < ((3*(k : ℝ)+1-l)-k+i+1) := by
    linarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) i]
  have hother' : (k : ℝ)+1 ≤ 2*((3*(k : ℝ)+1-l)-k+i+1) := by
    linarith [Nat.cast_nonneg (α := ℝ) i]
  have hd : 0 < d := mul_pos (by positivity) hother
  have hbound : 256 * (d-u) ≤ d := by
    rw [hdiff]
    have h₁ : ((k : ℝ)+1)*(3*(i : ℝ)+2-l) ≤ ((k : ℝ)+1)*192 := by
      gcongr; linarith
    have h₂ := mul_le_mul_of_nonneg_left hother' (show (0 : ℝ) ≤ 49152 by norm_num)
    have h₃ := mul_le_mul_of_nonneg_right hibig hother.le
    dsimp [d]
    nlinarith only [h₁, h₂, h₃, hother]
  have hu : (255/256 : ℝ)*d ≤ u := by linarith
  apply le_of_mul_le_mul_right _ hd
  have hprod := mul_le_mul_of_nonneg_left hu (mass_nonneg k l i)
  have hm : mass k l (i+1) * d = mass k l i * u := by
    dsimp [d,u]
    simpa only [mul_assoc] using he
  rw [hm]
  convert hprod using 1
  ring

private theorem mass_sum (k l : ℕ) (hl : l ≤ 3*k+1) :
    ∑ i ∈ Finset.range (k+1), mass k l i = ((3*k+1).choose k : ℝ) := by
  have hs := Nat.add_choose_eq l (3*k+1-l) k
  rw [show l+(3*k+1-l) = 3*k+1 by omega,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hs
  unfold mass
  exact_mod_cast hs.symm

theorem mass_upper {k l j : ℕ} (hl : 2*l ≤ 3*k+1) (hlbig : 1000000 ≤ l) (hj : j ≤ k) :
    32 * mass k l j ≤ ((3*k+1).choose k : ℝ) := by
  let m := (l+1)/3
  have hiter : ∀ r ≤ 63, (255/256 : ℝ)^r * mass k l m ≤ mass k l (m+r) := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      intro hr
      have he := near_mode_step hl hlbig (show (l+1)/3 ≤ m+r by dsimp [m]; omega)
        (show m+r ≤ (l+1)/3+63 by dsimp [m]; omega)
      calc
        _ = (255/256 : ℝ) * ((255/256 : ℝ)^r * mass k l m) := by rw [pow_succ]; ring
        _ ≤ (255/256 : ℝ) * mass k l (m+r) := by gcongr; exact ih (by omega)
        _ ≤ _ := he
  have hhalf : ∀ r ≤ 63, (1/2 : ℝ) * mass k l m ≤ mass k l (m+r) := by
    intro r hr
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (mass_nonneg ..)) (hiter r hr)
    have hr' : (r : ℝ) ≤ 63 := by exact_mod_cast hr
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(1/256) by norm_num) r
    norm_num at hb ⊢
    linarith
  let W := (Finset.range 64).image (fun r => m+r)
  have hW : W ⊆ Finset.range (k+1) := by
    intro t ht
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
    have hr' := Finset.mem_range.mp hr
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have hWcard : W.card = 64 := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h), Finset.card_range]
  calc
    32 * mass k l j ≤ 32 * mass k l m := by gcongr; exact mass_mode hl hj
    _ = ∑ t ∈ W, (1/2 : ℝ) * mass k l m := by
      rw [Finset.sum_const, hWcard, nsmul_eq_mul]
      norm_num
      ring
    _ ≤ ∑ t ∈ W, mass k l t := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
      exact hhalf r (by have := Finset.mem_range.mp hr; omega)
    _ ≤ ∑ t ∈ Finset.range (k+1), mass k l t :=
      Finset.sum_le_sum_of_subset_of_nonneg hW (fun i _ _ => mass_nonneg k l i)
    _ = _ := mass_sum k l (by omega)

private theorem mass_zero_lower {k l : ℕ} (hl : l ≤ k) :
    ((3*k+1).choose k : ℝ) ≤ (2 : ℝ)^l * mass k l 0 := by
  have hchoose : ∀ r ≤ k, (3*k+1-l).choose r ≤ (3*k+1-l).choose k := by
    intro r hr
    refine (Nat.le_induction (motive := fun t _ => t ≤ k →
      (3*k+1-l).choose r ≤ (3*k+1-l).choose t) (fun _ => le_rfl) ?_ k hr) le_rfl
    intro i _ ih hi
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  have hs := mass_sum k l (by omega)
  rw [← hs]
  have hp : ∑ i ∈ Finset.range (k+1), (l.choose i : ℝ) = (2 : ℝ)^l := by
    have h : ∑ i ∈ Finset.range (l+1), (l.choose i : ℝ) = (2 : ℝ)^l := by
      exact_mod_cast Nat.sum_range_choose l
    rw [← h]
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i _ hi
    rw [Nat.choose_eq_zero_of_lt (by rw [Finset.mem_range] at hi; omega), Nat.cast_zero]
  simp only [mass, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  rw [← hp, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  gcongr
  exact_mod_cast hchoose (k-i) (Nat.sub_le ..)

private theorem mass_small_step {k l j : ℕ} (hk : 4 ≤ k) (hl : 2 ≤ l) (hl' : l ≤ k)
    (hj : j ≤ 1) : (1/8 : ℝ) * mass k l j ≤ mass k l (j+1) := by
  have he := mass_step (show 2*l ≤ 3*k+1 by omega) (show j < k by omega) (show j ≤ l by omega)
  have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hl₁ : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hl₂ : (l : ℝ) ≤ k := by exact_mod_cast hl'
  interval_cases j <;> push_cast at he ⊢
  · have hd : 0 < (3*(k : ℝ)+1-l)-k+0+1 := by linarith
    apply le_of_mul_le_mul_right _ hd
    have hcoef : (1/8 : ℝ) * ((3*(k : ℝ)+1-l)-k+0+1) ≤ (l : ℝ)*k := by
      have hh := mul_nonneg (show 0 ≤ (l : ℝ)-2 by linarith) (show 0 ≤ (k : ℝ) by positivity)
      nlinarith only [hl₁, hk', hh]
    have hv := mul_le_mul_of_nonneg_left hcoef (mass_nonneg k l 0)
    nlinarith only [he, hv]
  · have hd : 0 < (2 : ℝ)*((3*(k : ℝ)+1-l)-k+1+1) := by positivity [show 0 < 3*(k : ℝ)+1-l-k+1+1 by linarith]
    apply le_of_mul_le_mul_right _ hd
    have hcoef : (1/8 : ℝ) * (2*((3*(k : ℝ)+1-l)-k+1+1)) ≤ ((l : ℝ)-1)*((k : ℝ)-1) := by
      have hh := mul_nonneg (show 0 ≤ (l : ℝ)-2 by linarith) (show 0 ≤ (k : ℝ)-1 by linarith)
      nlinarith only [hl₁, hk', hh]
    have hv := mul_le_mul_of_nonneg_left hcoef (mass_nonneg k l 1)
    nlinarith only [he, hv]

private theorem mass_lower_small {k l j : ℕ} (hk : 1000000 ≤ k) (hl₁ : 2 ≤ l)
    (hl₂ : l ≤ 1000000) (hj : j ≤ 2) :
    ((3*k+1).choose k : ℝ) ≤ (64 * (2 : ℝ)^1000000) * mass k l j := by
  have h₀ := mass_zero_lower (show l ≤ k by omega)
  have h₁ := mass_small_step (show 4 ≤ k by omega) hl₁ (show l ≤ k by omega) (show 0 ≤ 1 by decide)
  have h₂ := mass_small_step (show 4 ≤ k by omega) hl₁ (show l ≤ k by omega) (show 1 ≤ 1 by decide)
  have hr : mass k l 0 ≤ 64 * mass k l j := by
    interval_cases j
    · linarith [mass_nonneg k l 0]
    · change (1/8 : ℝ) * mass k l 0 ≤ mass k l 1 at h₁
      linarith [mass_nonneg k l 1]
    · change (1/8 : ℝ) * mass k l 0 ≤ mass k l 1 at h₁
      change (1/8 : ℝ) * mass k l 1 ≤ mass k l 2 at h₂
      linarith
  calc
    _ ≤ (2 : ℝ)^l * mass k l 0 := h₀
    _ ≤ (2 : ℝ)^1000000 * (64 * mass k l j) :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num) hl₂) hr (mass_nonneg ..) (by positivity)
    _ = _ := by rw [← mul_assoc, mul_comm ((2 : ℝ)^1000000) 64]

private theorem exists_small_mass_bound : ∃ C : ℝ, 2 ≤ C ∧
    ∀ k l j : ℕ, 1000000 ≤ k → 2 ≤ l → l ≤ 1000000 → j ≤ 2 →
      ((3*k+1).choose k : ℝ) ≤ C * mass k l j := by
  have aux (u : ℝ) (hu : 1 ≤ u) : (2 : ℝ) ≤ 64 * u := by linarith
  refine ⟨64 * (2 : ℝ)^1000000, aux _ (one_le_pow₀ (by norm_num)), ?_⟩
  exact fun _ _ _ => mass_lower_small

noncomputable def slice (k : ℕ) : Finset (Finset (Fin (3*k+1))) :=
  (Finset.univ : Finset (Fin (3*k+1))).powersetCard k

private theorem card_intersection_bucket {k j : ℕ} (hj : j ≤ k)
    (A : Finset (Fin (3*k+1))) :
    ({B ∈ slice k | (A ∩ B).card = j}.card : ℝ) = mass k A.card j := by
  classical
  let U : Finset (Fin (3*k+1)) := Finset.univ \ A
  have hU : U.card = 3*k+1-A.card := by
    simp [U, Finset.card_sdiff_of_subset]
  have hc : {B ∈ slice k | (A ∩ B).card = j}.card =
      ((A.powersetCard j) ×ˢ (U.powersetCard (k-j))).card := by
    apply Finset.card_bij' (fun B _ => (A ∩ B, B \ A)) (fun p _ => p.1 ∪ p.2)
    · intro B hB
      obtain ⟨hBk, hBi⟩ := Finset.mem_filter.mp hB
      have hcard := (Finset.mem_powersetCard.mp (show B ∈ Finset.univ.powersetCard k from hBk)).2
      simp only [Finset.mem_product, Finset.mem_powersetCard]
      refine ⟨⟨Finset.inter_subset_left, hBi⟩, ?_, ?_⟩
      · intro x hx
        simp [U, (Finset.mem_sdiff.mp hx).2]
      · rw [Finset.card_sdiff, hcard, hBi]
    · rintro ⟨s,t⟩ hp
      obtain ⟨⟨hs,hsj⟩, ⟨ht,htj⟩⟩ := Finset.mem_product.mp hp |>.imp
        Finset.mem_powersetCard.mp Finset.mem_powersetCard.mp
      have hd : Disjoint s t := by
        refine Finset.disjoint_left.mpr fun x hx hy => ?_
        exact (Finset.mem_sdiff.mp (ht hy)).2 (hs hx)
      have hT : A ∩ t = ∅ := by
        apply Finset.disjoint_iff_inter_eq_empty.mp
        exact Finset.disjoint_sdiff.mono_right ht
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
      · rw [Finset.card_union_of_disjoint hd, hsj, htj]; omega
      · rw [Finset.inter_union_distrib_left, Finset.inter_eq_right.mpr hs, hT, Finset.union_empty, hsj]
    · intro B hB
      rw [Finset.inter_comm A B, Finset.union_comm, Finset.sdiff_union_inter]
    · rintro ⟨s,t⟩ hp
      obtain ⟨⟨hs,hsj⟩, ⟨ht,htj⟩⟩ := Finset.mem_product.mp hp |>.imp
        Finset.mem_powersetCard.mp Finset.mem_powersetCard.mp
      have hT : A ∩ t = ∅ := Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_sdiff.mono_right ht)
      have hS : s \ A = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hs
      have hT' : t \ A = t := by
        ext x
        simp only [Finset.mem_sdiff]
        exact ⟨fun hx => hx.1, fun hx => ⟨hx, (Finset.mem_sdiff.mp (ht hx)).2⟩⟩
      simp [Finset.inter_union_distrib_left, Finset.inter_eq_right.mpr hs, hT,
        Finset.union_sdiff_distrib, hS, hT']
  rw [hc, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard, hU]
  simp [mass]

private theorem card_slice (k : ℕ) : (slice k).card = (3*k+1).choose k := by
  simp [slice]

private theorem slice_card_of_mem {k : ℕ} {B : Finset (Fin (3*k+1))} (h : B ∈ slice k) : B.card = k :=
  (Finset.mem_powersetCard.mp (show B ∈ Finset.univ.powersetCard k from h)).2

noncomputable def band {k : ℕ} (A : Finset (Fin (3*k+1))) (a : ℕ) : Finset (Finset (Fin (3*k+1))) :=
  (slice k).filter (fun B => (A ∩ B).card = a ∨ (A ∩ B).card = a+1)

theorem band_large {k a : ℕ} (A : Finset (Fin (3*k+1))) (hA : 2*A.card ≤ 3*k+1)
    (hAbig : 1000000 ≤ A.card) (ha : a < k) :
    (band A a).card ≤ (1/16 : ℝ) * (slice k).card := by
  classical
  have h₀ := mass_upper hA hAbig ha.le
  have h₁ := mass_upper hA hAbig (show a+1 ≤ k by omega)
  have hc₀ := card_intersection_bucket ha.le A
  have hc₁ := card_intersection_bucket (show a+1 ≤ k by omega) A
  have hsplit : band A a = {B ∈ slice k | (A∩B).card=a} ∪ {B ∈ slice k | (A∩B).card=a+1} := by
    ext B
    simp [band]
    tauto
  have hcard := Finset.card_union_le (s := {B ∈ slice k | (A∩B).card=a})
    (t := {B ∈ slice k | (A∩B).card=a+1})
  rw [← hsplit] at hcard
  have hr : ((band A a).card : ℝ) ≤ ({B ∈ slice k | (A∩B).card=a}.card : ℝ) +
      ({B ∈ slice k | (A∩B).card=a+1}.card : ℝ) := by exact_mod_cast hcard
  rw [hc₀, hc₁] at hr
  rw [card_slice]
  linarith only [h₀, h₁, hr]

theorem band_small {k a : ℕ} (A : Finset (Fin (3*k+1))) {C : ℝ} (hpos : 0 < C)
    (hbound : ∀ j ≤ 2, ((3*k+1).choose k : ℝ) ≤ C * mass k A.card j)
    (hk : 1000000 ≤ k) : (band A a).card ≤ (1 - 1/C) * (slice k).card := by
  classical
  have hex : ∃ j : ℕ, j ≤ 2 ∧ j ≠ a ∧ j ≠ a+1 := by
    by_cases h : a = 0
    · exact ⟨2, by omega, by omega, by omega⟩
    · exact ⟨0, by omega, by omega, by omega⟩
  obtain ⟨j,hj,h₀,h₁⟩ := hex
  have hlow := hbound j hj
  rw [← card_intersection_bucket (by omega) A] at hlow
  let T := {B ∈ slice k | (A∩B).card=j}
  have hdis : Disjoint (band A a) T := by
    refine Finset.disjoint_left.mpr (fun b hb ht => ?_)
    have he := (Finset.mem_filter.mp ht).2
    rcases (Finset.mem_filter.mp hb).2 with eq | eq <;> omega
  have hsubset : band A a ∪ T ⊆ slice k :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_union_of_disjoint hdis] at hcard
  have hcr : ((band A a).card : ℝ) + (T.card : ℝ) ≤ (slice k).card := by exact_mod_cast hcard
  have hdiv : (slice k).card / C ≤ (T.card : ℝ) := by
    rw [div_le_iff₀ hpos, card_slice, mul_comm (T.card : ℝ) C]
    exact hlow
  rw [sub_mul, one_mul, div_mul_eq_mul_div, one_mul]
  linarith only [hcr, hdiv]

private theorem cube_count {n : ℕ} (P : Submodule ℝ (Fin n → ℝ))
    (S : Finset (Fin n → ℝ)) (hbit : ∀ x ∈ S, ∀ i, x i = 0 ∨ x i = 1)
    (hdiff : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ P) : S.card ≤ 2^(Module.finrank ℝ P) := by
  classical
  generalize hd : Module.finrank ℝ P = d
  induction d using Nat.strong_induction_on generalizing P S with
  | ind d ih =>
    by_cases hsmall : S.card ≤ 1
    · exact hsmall.trans (Nat.succ_le_of_lt (by positivity))
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    have hrest : (S.erase x).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hx]; omega)
    obtain ⟨y,hy⟩ := hrest
    have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
    have hyS := (Finset.mem_erase.mp hy).2
    obtain ⟨i,hi⟩ : ∃ i, x i ≠ y i := by
      by_contra! h
      exact hyx ((funext h).symm)
    let E : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i
    let f : P →ₗ[ℝ] ℝ := E.comp P.subtype
    let Q := f.ker.map P.subtype
    have hQ : Module.finrank ℝ Q = Module.finrank ℝ f.ker := P.finrank_map_subtype_eq _
    have hfr : 0 < Module.finrank ℝ f.range := by
      apply Module.finrank_pos_iff_exists_ne_zero.mpr
      have hxy : x-y ∈ P := hdiff x hx y hyS
      let u : f.range := ⟨f ⟨x-y,hxy⟩, ⟨⟨x-y,hxy⟩,rfl⟩⟩
      refine ⟨u,fun h => hi (sub_eq_zero.mp ?_)⟩
      exact congrArg (fun z : f.range => (z : ℝ)) h
    have hdim := f.finrank_range_add_finrank_ker
    have hlt : Module.finrank ℝ Q < d := by omega
    let L := S.filter (fun u => u i = 0)
    let R := S.filter (fun u => u i ≠ 0)
    have hfiber (p : ℝ → Prop) [DecidablePred p] (c : ℝ)
        (hc : ∀ u ∈ S, p (u i) → u i = c) :
        (S.filter (fun u => p (u i))).card ≤ 2^(Module.finrank ℝ Q) := by
      apply ih (Module.finrank ℝ Q) hlt Q
      · exact fun u hu => hbit u (Finset.mem_filter.mp hu).1
      · intro u hu v hv
        obtain ⟨hu,hui⟩ := Finset.mem_filter.mp hu
        obtain ⟨hv,hvi⟩ := Finset.mem_filter.mp hv
        have huvp := hdiff u hu v hv
        refine Submodule.mem_map.mpr ⟨⟨u-v,huvp⟩, ?_, rfl⟩
        change u i - v i = 0
        rw [hc u hu hui, hc v hv hvi, sub_self]
      · rfl
    have hL : L.card ≤ 2^(Module.finrank ℝ Q) := hfiber (· = 0) 0 (fun _ _ h => h)
    have hR : R.card ≤ 2^(Module.finrank ℝ Q) := hfiber (· ≠ 0) 1 (fun u hu h => (hbit u hu i).resolve_left h)
    have hs : L.card + R.card = S.card := Finset.card_filter_add_card_filter_not (s := S) _
    rw [← hs]
    calc
      _ ≤ 2^(Module.finrank ℝ Q) + 2^(Module.finrank ℝ Q) := Nat.add_le_add hL hR
      _ = 2^(Module.finrank ℝ Q + 1) := by rw [pow_succ, Nat.mul_two]
      _ ≤ 2^d := Nat.pow_le_pow_right (by decide) (by omega)

noncomputable def indVec {n : ℕ} (B : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ B then 1 else 0

private theorem indVec_injective (n : ℕ) : Function.Injective (@indVec n) := by
  intro A B he
  ext i
  have hi := congrFun he i
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp_all [indVec]

private theorem cube_columns {k : ℕ} (P : Submodule ℝ (Fin (3*k+1) → ℝ)) :
    ({B ∈ slice k | indVec B ∈ P}).card ≤ 2^(Module.finrank ℝ P) := by
  classical
  let W := {B ∈ slice k | indVec B ∈ P}
  let S := W.image indVec
  have hc : S.card = W.card := Finset.card_image_of_injective _ (indVec_injective _)
  change W.card ≤ _
  rw [← hc]
  apply cube_count P
  · rintro x hx i
    obtain ⟨B,_,rfl⟩ := Finset.mem_image.mp hx
    by_cases h : i ∈ B <;> simp [indVec,h]
  · rintro x hx y hy
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hy
    exact P.sub_mem (Finset.mem_filter.mp hA).2 (Finset.mem_filter.mp hB).2

private theorem three_pow_le_slice (k : ℕ) : 3^k ≤ (slice k).card := by
  simp only [card_slice]
  induction k with
  | zero => decide
  | succ k ih =>
    have he : 3*(k+1)+1 = (3*k+1)+3 := by omega
    rw [he, Nat.add_choose_eq, pow_succ]
    refine (Nat.mul_le_mul_right 3 ih).trans ?_
    have hpair : (k,1) ∈ Finset.antidiagonal (k+1) := by simp
    simpa using (Finset.single_le_sum
      (f := fun p : ℕ × ℕ => (3*k+1).choose p.1 * Nat.choose 3 p.2)
      (fun _ _ => Nat.zero_le _) hpair)

abbrev Col (k : ℕ) := ↥(slice k)

private noncomputable def colVec {k : ℕ} (B : Col k) : Fin (3*k+1) → ℝ := indVec B.val

private noncomputable def independentTuples (k m : ℕ) : Finset (Fin m → Col k) :=
  Finset.univ.filter (fun f => LinearIndependent ℝ (colVec ∘ f))

private noncomputable def available {k m : ℕ} (f : Fin m → Col k) : Finset (Col k) :=
  Finset.univ.filter (fun B => colVec B ∉ Submodule.span ℝ (Set.range (colVec ∘ f)))

private theorem available_card_lower {k m : ℕ} (f : Fin m → Col k) (hm : m ≤ k) :
    (slice k).card - 2^k ≤ (available f).card := by
  classical
  let P := Submodule.span ℝ (Set.range (colVec ∘ f))
  let D : Finset (Col k) := Finset.univ.filter (fun B => colVec B ∈ P)
  have hcount : D.card = {B ∈ slice k | indVec B ∈ P}.card := by
    refine Finset.card_bij' (fun b _ => b.val)
      (fun B hB => ⟨B,(Finset.mem_filter.mp hB).1⟩) ?_ ?_ ?_ ?_
    · intro b hb
      refine Finset.mem_filter.mpr ⟨b.property,?_⟩
      change colVec b ∈ P
      exact (Finset.mem_filter.mp hb).2
    · intro B hB
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      change indVec B ∈ P
      exact (Finset.mem_filter.mp hB).2
    · intro b hb
      rfl
    · intro b hb
      rfl
  have hd : Module.finrank ℝ P ≤ m := by
    simpa [P, Set.finrank] using (finrank_range_le_card (R := ℝ) (colVec ∘ f))
  have hbad : D.card ≤ 2^k := calc
    _ ≤ 2^(Module.finrank ℝ P) := hcount ▸ cube_columns P
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (hd.trans hm)
  have hs : D.card + (available f).card = (slice k).card := by
    simpa only [D, available, Finset.card_univ, Fintype.card_coe] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Col k)))
        (fun B => colVec B ∈ P))
  omega

private theorem independent_card_lower (k m : ℕ) (hm : m ≤ k) :
    ((slice k).card - 2^k)^m ≤ (independentTuples k m).card := by
  classical
  induction m with
  | zero =>
    simp only [pow_zero]
    refine Finset.card_pos.mpr ⟨Fin.elim0,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    exact linearIndependent_empty_type
  | succ m ih =>
    let F : (Σ f : ↥(independentTuples k m), ↥(available f.val)) → ↥(independentTuples k (m+1)) :=
      fun u => ⟨Fin.snoc u.1.val u.2.val, by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        have hf : LinearIndependent ℝ (colVec ∘ u.1.val) := (Finset.mem_filter.mp u.1.property).2
        have hb : colVec u.2.val ∉ Submodule.span ℝ (Set.range (colVec ∘ u.1.val)) :=
          (Finset.mem_filter.mp u.2.property).2
        have he : colVec ∘ Fin.snoc u.1.val u.2.val = Fin.snoc (colVec ∘ u.1.val) (colVec u.2.val) := by
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Function.comp_def]
        rw [he]
        exact hf.finSnoc hb⟩
    have hF : Function.Injective F := by
      rintro ⟨f,b⟩ ⟨g,c⟩ he
      have hv := congrArg Subtype.val he
      change Fin.snoc (α := fun _ => Col k) f.val b.val = Fin.snoc g.val c.val at hv
      obtain ⟨hp,hq⟩ := Fin.snoc_injective2 hv
      have hf : f = g := Subtype.ext hp
      subst g
      have hb : b = c := Subtype.ext hq
      subst c
      rfl
    have hs := Fintype.card_le_of_injective F hF
    simp only [Fintype.card_sigma, Fintype.card_coe] at hs
    calc
      _ = ((slice k).card - 2^k)^m * ((slice k).card - 2^k) := pow_succ ..
      _ ≤ (independentTuples k m).card * ((slice k).card - 2^k) :=
        Nat.mul_le_mul_right _ (ih (by omega))
      _ = ∑ f : ↥(independentTuples k m), ((slice k).card - 2^k) := by
        simp
      _ ≤ ∑ f : ↥(independentTuples k m), (available f.val).card :=
        Finset.sum_le_sum (fun f _ => available_card_lower f.val (by omega))
      _ ≤ _ := hs

private noncomputable def allIn {k : ℕ} (m : ℕ) (X : Finset (Finset (Fin (3*k+1)))) :
    Finset (Fin m → Col k) := Finset.univ.filter (fun f => ∀ i, (f i).val ∈ X)

private theorem card_allIn {k m : ℕ} {X : Finset (Finset (Fin (3*k+1)))} (hX : X ⊆ slice k) :
    (allIn m X).card = X.card^m := by
  classical
  let e : ↥(allIn m X) ≃ (Fin m → ↥X) :=
    { toFun := fun f i => ⟨(f.val i).val,(Finset.mem_filter.mp f.property).2 i⟩
      invFun := fun f => ⟨fun i => ⟨(f i).val,hX (f i).property⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => (f i).property⟩⟩
      left_inv := fun f => Subtype.ext (funext (fun _ => Subtype.ext rfl))
      right_inv := fun f => funext (fun _ => Subtype.ext rfl) }
  simpa [Fintype.card_coe] using Fintype.card_congr e

private noncomputable def SmallRows (k M : ℕ) : Finset (Finset (Fin (3*k+1))) :=
  Finset.univ.filter (fun A => 2 ≤ A.card ∧ A.card ≤ M)

private noncomputable def LargeRows (k : ℕ) : Finset (Finset (Fin (3*k+1))) :=
  Finset.univ.filter (fun A => 1000000 ≤ A.card ∧ 2*A.card ≤ 3*k+1)

private theorem large_rows_card (k : ℕ) : (LargeRows k).card ≤ 2^(3*k+1) := by
  simpa [LargeRows, Fintype.card_finset] using (Finset.card_filter_le Finset.univ
    (fun A : Finset (Fin (3*k+1)) => 1000000 ≤ A.card ∧ 2*A.card ≤ 3*k+1))

private theorem rows_bounded_card (n M : ℕ) (hn : 0 < n)
    (R : Finset (Finset (Fin n))) (hR : ∀ A ∈ R, A.card ≤ M) :
    R.card ≤ (M+1)*n^M := by
  classical
  let W := (Finset.range (M+1)).biUnion fun j =>
    (Finset.univ : Finset (Fin n)).powersetCard j
  have hW : R ⊆ W := by
    intro A hA
    have ha := hR A hA
    exact Finset.mem_biUnion.mpr ⟨A.card, Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,rfl⟩⟩
  calc
    _ ≤ W.card := Finset.card_le_card hW
    _ ≤ ∑ j ∈ Finset.range (M+1), ((Finset.univ : Finset (Fin n)).powersetCard j).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.range (M+1), n^M := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      have hle : j ≤ M := by have := Finset.mem_range.mp hj; omega
      exact (Nat.choose_le_pow ..).trans (Nat.pow_le_pow_right hn hle)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; rfl

private theorem small_rows_card (k M : ℕ) : (SmallRows k M).card ≤ (M+1)*(3*k+1)^M :=
  rows_bounded_card (3*k+1) M (by omega) (SmallRows k M)
    (fun _ hA => (Finset.mem_filter.mp hA).2.2)

private noncomputable def badFor {k : ℕ} (R : Finset (Finset (Fin (3*k+1)))) :
    Finset (Fin k → Col k) :=
  (R ×ˢ (Finset.univ : Finset (Fin k))).biUnion fun (A,a) => allIn k (band A a.val)

private theorem badFor_le {k : ℕ} {R : Finset (Finset (Fin (3*k+1)))} (L : ℝ)
    (hb : ∀ A ∈ R, ∀ a < k, (band A a).card ≤ L) :
    ((badFor R).card : ℝ) ≤ (R.card : ℝ) * k * L^k := by
  classical
  let J := R ×ˢ (Finset.univ : Finset (Fin k))
  have hu := Finset.card_biUnion_le (s := J) (t := fun p => allIn k (band p.1 p.2.val))
  have hu' : ((badFor R).card : ℝ) ≤ ∑ p ∈ J, ((allIn k (band p.1 p.2.val)).card : ℝ) := by
    exact_mod_cast hu
  refine hu'.trans ?_
  calc
    _ ≤ ∑ p ∈ J, L^k := by
      apply Finset.sum_le_sum
      rintro ⟨A,a⟩ hp
      have hs : band A a.val ⊆ slice k := Finset.filter_subset _ _
      rw [card_allIn hs, Nat.cast_pow]
      exact pow_le_pow_left₀ (by positivity) (hb A (Finset.mem_product.mp hp).1 a.val a.isLt) _
    _ = _ := by simp [J, nsmul_eq_mul]

open Filter Topology

private theorem eventual_band_bounds (M : ℕ) {r δ : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, 1000000 ≤ k ∧ (2/3 : ℝ)^k ≤ δ ∧
      ((M+1 : ℕ) : ℝ)*(k : ℝ)*(3*(k : ℝ)+1)^M*r^k < 1/2 ∧
      (2 : ℝ)^(3*k+1)*(k : ℝ)*(1/12 : ℝ)^k < 1/2 := by
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2/3)
    (by norm_num : (2/3 : ℝ) < 1)).eventually_le_const hδ
  have hsmall := ((tendsto_pow_const_mul_const_pow_of_lt_one (M+1) hr₀ hr₁).const_mul
    (((M+1 : ℕ) : ℝ)*(4 : ℝ)^M))
  rw [mul_zero] at hsmall
  have hlarge := (tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0 : ℝ) ≤ 2/3)
    (by norm_num : (2/3 : ℝ) < 1)).const_mul (2 : ℝ)
  rw [mul_zero] at hlarge
  filter_upwards [eventually_ge_atTop (1000000 : ℕ), hpow,
    hsmall.eventually_lt_const (by norm_num : (0 : ℝ) < 1/2),
    hlarge.eventually_lt_const (by norm_num : (0 : ℝ) < 1/2)] with k hk hp hs hl
  refine ⟨hk,hp,?_,?_⟩
  · refine lt_of_le_of_lt ?_ hs
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hp' : (3*(k : ℝ)+1)^M ≤ (4*(k : ℝ))^M := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    calc
      _ ≤ ((M+1 : ℕ) : ℝ)*(k : ℝ)*(4*(k : ℝ))^M*r^k := by gcongr
      _ = ((M+1 : ℕ) : ℝ)*(4 : ℝ)^M*((k : ℝ)^(M+1)*r^k) := by
        rw [mul_pow, pow_succ]
        ring
  · have he : (2 : ℝ)^(3*k+1)*(k : ℝ)*(1/12 : ℝ)^k = 2*((k : ℝ)*(2/3 : ℝ)^k) := by
      rw [pow_succ, pow_mul, ← show (2 : ℝ)^3 * (1/12 : ℝ) = 2/3 by norm_num, mul_pow]
      ring
    exact he ▸ hl

private theorem selected_tuple (M : ℕ) (hM : M ≤ 1000000) : ∃ K : ℕ, ∀ k ≥ K,
    ∃ f : Fin k → Col k, LinearIndependent ℝ (colVec ∘ f) ∧
      f ∉ badFor (SmallRows k M) ∧ f ∉ badFor (LargeRows k) := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_small_mass_bound
  have hCpos : 0 < C := by linarith
  let δ : ℝ := 1/(2*C)
  let r : ℝ := 1-δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ₄ : δ ≤ 1/4 := by
    dsimp [δ]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2*C)]
    linarith
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hr₁ : r < 1 := by dsimp [r]; linarith
  obtain ⟨K,hK⟩ := eventually_atTop.mp (eventual_band_bounds M hr hr₁ hδ)
  refine ⟨K,fun k hk => ?_⟩
  obtain ⟨hkbig,hkp,hks,hkl⟩ := hK k hk
  let c : ℝ := (slice k).card
  let q : ℝ := ((slice k).card - 2^k : ℕ)
  have hc_nat := three_pow_le_slice k
  have hc_pos : 0 < c := by
    dsimp [c]
    exact_mod_cast lt_of_lt_of_le (show 0 < 3^k by positivity) hc_nat
  have hpowNat : (2 : ℕ)^k ≤ 3^k := Nat.pow_le_pow_left (by decide) k
  have hdiff : q = c-(2 : ℝ)^k := by
    dsimp [q,c]
    rw [Nat.cast_sub (hpowNat.trans hc_nat), Nat.cast_pow, Nat.cast_ofNat]
  have hqc : r*c ≤ q := by
    have hcb : (3 : ℝ)^k ≤ c := by dsimp [c]; exact_mod_cast hc_nat
    have hp := mul_le_mul hkp hcb (by positivity) hδ.le
    have he : (2/3 : ℝ)^k * (3 : ℝ)^k = (2 : ℝ)^k := by
      rw [← mul_pow]
      congr 1
      norm_num
    rw [he] at hp
    rw [hdiff]
    dsimp [r]
    nlinarith only [hp]
  have hqpos : 0 < q := by
    have hr₃ : (3/4 : ℝ) ≤ r := by dsimp [r]; linarith
    exact (mul_pos (by linarith) hc_pos).trans_le hqc
  have hsmallband : ∀ A ∈ SmallRows k M, ∀ a < k, (band A a).card ≤ r*q := by
    intro A hA a _
    obtain ⟨hA₁,hA₂⟩ := (Finset.mem_filter.mp hA).2
    have hb : ((band A a).card : ℝ) ≤ (1 - 1/C)*c :=
      band_small A hCpos (fun j hj => hbound k A.card j hkbig hA₁ (hA₂.trans hM) hj) hkbig
    have he : 1 - 1/C = 1 - 2*δ := by dsimp [δ]; ring
    have hsq : 1 - 2*δ ≤ r*r := by dsimp [r]; nlinarith only [sq_nonneg δ]
    calc
      _ ≤ (1 - 2*δ)*c := he ▸ hb
      _ ≤ (r*r)*c := mul_le_mul_of_nonneg_right hsq hc_pos.le
      _ ≤ r*q := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hqc hr
  have hlargeband : ∀ A ∈ LargeRows k, ∀ a < k, (band A a).card ≤ q/12 := by
    intro A hA a ha
    obtain ⟨hA₁,hA₂⟩ := (Finset.mem_filter.mp hA).2
    have hb : ((band A a).card : ℝ) ≤ (1/16 : ℝ)*c := band_large A hA₂ hA₁ ha
    have hr₃ : (3/4 : ℝ) ≤ r := by dsimp [r]; linarith
    have hp := (mul_le_mul_of_nonneg_right hr₃ hc_pos.le).trans hqc
    linarith only [hb,hp]
  have hs := badFor_le (r*q) hsmallband
  have hl := badFor_le (q/12) hlargeband
  have hs' : ((badFor (SmallRows k M)).card : ℝ) < (1/2 : ℝ)*q^k := by
    have hc' : ((SmallRows k M).card : ℝ) ≤ ((M+1 : ℕ) : ℝ)*(3*(k : ℝ)+1)^M := by
      exact_mod_cast small_rows_card k M
    have hprod : ((SmallRows k M).card : ℝ) * k ≤
        ((M+1 : ℕ) : ℝ)*(k : ℝ)*(3*(k : ℝ)+1)^M := by
      calc
        _ ≤ ((M+1 : ℕ) : ℝ)*(3*(k : ℝ)+1)^M*(k : ℝ) := mul_le_mul_of_nonneg_right hc' (by positivity)
        _ = _ := by ring
    apply lt_of_le_of_lt hs
    rw [mul_pow, ← mul_assoc]
    exact mul_lt_mul_of_pos_right ((mul_le_mul_of_nonneg_right
      hprod (pow_nonneg hr _)).trans_lt hks) (pow_pos hqpos _)
  have hl' : ((badFor (LargeRows k)).card : ℝ) < (1/2 : ℝ)*q^k := by
    have hc' : ((LargeRows k).card : ℝ) ≤ (2 : ℝ)^(3*k+1) := by exact_mod_cast large_rows_card k
    apply lt_of_le_of_lt hl
    rw [show q/12 = (1/12 : ℝ)*q by ring, mul_pow, ← mul_assoc]
    exact mul_lt_mul_of_pos_right ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc' (by positivity)) (by positivity)).trans_lt hkl) (pow_pos hqpos _)
  have hlo : q^k ≤ ((independentTuples k k).card : ℝ) := by
    dsimp [q]
    exact_mod_cast independent_card_lower k k le_rfl
  have hsum : (badFor (SmallRows k M)).card + (badFor (LargeRows k)).card < (independentTuples k k).card := by
    exact_mod_cast (show ((badFor (SmallRows k M)).card : ℝ) + (badFor (LargeRows k)).card <
      (independentTuples k k).card by linarith only [hs',hl',hlo])
  have hsubset : ¬independentTuples k k ⊆ badFor (SmallRows k M) ∪ badFor (LargeRows k) :=
    fun h => (not_le_of_gt hsum) ((Finset.card_le_card h).trans (Finset.card_union_le _ _))
  obtain ⟨f,hf,hout⟩ := Finset.not_subset.mp hsubset
  exact ⟨f, (Finset.mem_filter.mp hf).2, (fun h => hout (Finset.mem_union_left _ h)),
    (fun h => hout (Finset.mem_union_right _ h))⟩

private theorem some_outside_band {k : ℕ} (f : Fin k → Col k)
    (hsmall : f ∉ badFor (SmallRows k 1000000)) (hlarge : f ∉ badFor (LargeRows k))
    (A : Finset (Fin (3*k+1))) (hA : 2 ≤ A.card) (hAh : 2*A.card ≤ 3*k+1)
    (a : Fin k) : ∃ i, (f i).val ∉ band A a.val := by
  have aux (R : Finset (Finset (Fin (3*k+1)))) (hR : A ∈ R)
      (hf : f ∉ badFor R) : ∃ i, (f i).val ∉ band A a.val := by
    by_contra! he
    apply hf
    exact Finset.mem_biUnion.mpr ⟨(A,a), Finset.mem_product.mpr ⟨hR,Finset.mem_univ _⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩⟩
  by_cases hs : A.card ≤ 1000000
  · exact aux (SmallRows k 1000000) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hA,hs⟩) hsmall
  · exact aux (LargeRows k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega,hAh⟩) hlarge

def Adj {n : ℕ} (A B : Finset (Fin n)) (a : ℤ) : Prop :=
  ((A∩B).card : ℤ) = a ∨ ((A∩B).card : ℤ) = a+1

def Detects {n : ℕ} (Y : Finset (Finset (Fin n))) : Prop :=
  ∀ A : Finset (Fin n), 2 ≤ A.card → A.card+2 ≤ n → ∀ a : ℤ, ∃ B ∈ Y, ¬ Adj A B a

private theorem detects_tuple {k : ℕ} (hk : 2 ≤ k) (f : Fin k → Col k)
    (hsmall : f ∉ badFor (SmallRows k 1000000)) (hlarge : f ∉ badFor (LargeRows k)) :
    Detects (Finset.univ.image (fun i => (f i).val)) := by
  classical
  have hn : (0 : ℤ) < (k : ℤ) := by exact_mod_cast (show 0 < k by omega)
  have half (A : Finset (Fin (3*k+1))) (hA : 2 ≤ A.card) (hAh : 2*A.card ≤ 3*k+1) (a : ℤ) :
      ∃ i, ¬ Adj A (f i).val a := by
    let b : ℤ := max 0 (min a ((k : ℤ)-1))
    have hb₀ : 0 ≤ b := le_max_left ..
    have hb₁ : b < (k : ℤ) := max_lt_iff.mpr ⟨hn,(min_le_right ..).trans_lt (by omega)⟩
    have hb_eq : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb₀
    let j : Fin k := ⟨b.toNat, by omega⟩
    obtain ⟨i,hi⟩ := some_outside_band f hsmall hlarge A hA hAh j
    refine ⟨i, fun ha => hi (Finset.mem_filter.mpr ⟨(f i).property,?_⟩)⟩
    have hle : (A∩(f i).val).card ≤ k :=
      (Finset.card_le_card Finset.inter_subset_right).trans_eq (slice_card_of_mem (f i).property)
    change (A∩(f i).val).card = b.toNat ∨ (A∩(f i).val).card = b.toNat+1
    dsimp only [Adj] at ha
    dsimp [b] at hb_eq
    omega
  intro A hA hA' a
  by_cases hhalf : 2*A.card ≤ 3*k+1
  · obtain ⟨i,hi⟩ := half A hA hhalf a
    exact ⟨(f i).val, Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩, hi⟩
  · have hc : Aᶜ.card = 3*k+1-A.card := by simp [Finset.card_compl]
    obtain ⟨i,hi⟩ := half Aᶜ (by rw [hc]; omega) (by rw [hc]; omega) ((k : ℤ)-a-1)
    refine ⟨(f i).val, Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩, fun ha => hi ?_⟩
    have hsum : (((A ∩ (f i).val).card : ℕ) : ℤ) + (((Aᶜ ∩ (f i).val).card : ℕ) : ℤ) = k := by
      exact_mod_cast (show (A ∩ (f i).val).card + (Aᶜ ∩ (f i).val).card = k by
        rw [Finset.inter_comm A _, Finset.inter_comm Aᶜ _, ← Finset.sdiff_eq_inter_compl,
          Finset.card_inter_add_card_sdiff, slice_card_of_mem (f i).property])
    dsimp only [Adj] at ha ⊢
    omega

end MinimalSlice

namespace MinimalSlice

open scoped BigOperators

private theorem indVec_apply_sum {n : ℕ} (B : Finset (Fin n)) (φ : (Fin n → ℝ) →ₗ[ℝ] ℝ) :
    φ (indVec B) = ∑ i ∈ B, φ (Pi.basisFun ℝ (Fin n) i) := by
  classical
  let e := Pi.basisFun ℝ (Fin n)
  have hs := congrArg φ (e.sum_repr (indVec B))
  simp only [map_sum, map_smul, smul_eq_mul, Pi.basisFun_repr, e, indVec, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_mem, Finset.univ_inter] at hs
  exact hs.symm

private theorem span_slice {k : ℕ} (hk : 2 ≤ k) :
    Submodule.span ℝ (indVec '' (slice k : Set (Finset (Fin (3*k+1))))) = ⊤ := by
  classical
  by_contra h
  let P := Submodule.span ℝ (indVec '' (slice k : Set (Finset (Fin (3*k+1)))))
  obtain ⟨φ,hφ,hmap⟩ := P.exists_dual_map_eq_bot_of_lt_top
    (show P < ⊤ from lt_top_iff_ne_top.mpr h) inferInstance
  let w (i : Fin (3*k+1)) := φ (Pi.basisFun ℝ (Fin (3*k+1)) i)
  have hw : ∀ B : Finset (Fin (3*k+1)), B.card = k → ∑ i ∈ B, w i = 0 := by
    intro B hB
    have hmem : B ∈ slice k := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hB⟩
    have hP : indVec B ∈ P := Submodule.subset_span ⟨B,hmem,rfl⟩
    have hm : φ (indVec B) ∈ P.map φ := Submodule.mem_map.mpr ⟨indVec B,hP,rfl⟩
    rw [hmap, Submodule.mem_bot] at hm
    rwa [indVec_apply_sum] at hm
  have hw₀ := MinimalSliceProtocolSource.sum_zero_of_all_ksubsets (3*k+1) k w (by omega) (by omega) hw
  apply hφ
  apply (Pi.basisFun ℝ (Fin (3*k+1))).ext
  intro i
  exact hw₀ i

private noncomputable def sumForm {n : ℕ} (w : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i, w i • LinearMap.proj i

private theorem sumForm_indVec {n : ℕ} (w : Fin n → ℝ) (B : Finset (Fin n)) :
    sumForm w (indVec B) = ∑ i ∈ B, w i := by
  classical
  simp [sumForm, LinearMap.sum_apply, indVec, mul_ite, Finset.sum_ite_mem]

private theorem completed_basis {k : ℕ} (hk : 2 ≤ k) (f : Fin k → Col k)
    (hf : LinearIndependent ℝ (colVec ∘ f)) :
    ∃ Y : Finset (Finset (Fin (3*k+1))),
      Y.Nonempty ∧ Y ⊆ slice k ∧ Y.card = 3*k+1 ∧
      (Finset.univ.image (fun i => (f i).val)) ⊆ Y ∧
      ∀ (w : Fin (3*k+1) → ℝ) (c : ℝ), (∀ B ∈ Y, ∑ i ∈ B, w i = c) →
        ∀ B ∈ slice k, ∑ i ∈ B, w i = c := by
  classical
  let g (i : Fin k) := (f i).val
  have hi : Function.Injective g := fun i j h => hf.injective (congrArg indVec h)
  have ht : LinearIndepOn ℝ indVec (Set.range g) :=
    (linearIndepOn_range_iff hi indVec).2 hf
  have hsub : Set.range g ⊆ (slice k : Set (Finset (Fin (3*k+1)))) := by
    rintro _ ⟨i,rfl⟩
    exact (f i).property
  let U := ht.extend hsub
  have hU : U ⊆ (slice k : Set _) := ht.extend_subset hsub
  have hfin := (slice k).finite_toSet.subset hU
  let Y := hfin.toFinset
  have hY : (Y : Set _) = U := hfin.coe_toFinset
  have hmem {B : Finset (Fin (3*k+1))} : B ∈ Y ↔ B ∈ U :=
    Iff.of_eq (congrArg (fun S : Set (Finset (Fin (3*k+1))) => B ∈ S) hY)
  have hind : LinearIndepOn ℝ (@indVec (3*k+1)) (Y : Set (Finset (Fin (3*k+1)))) := by
    rw [hY]
    exact ht.linearIndepOn_extend hsub
  have hspan : Submodule.span ℝ (Set.range (fun B : ↥Y => indVec B.val)) = ⊤ := by
    rw [show Set.range (fun B : ↥Y => indVec B.val) = indVec '' (Y : Set (Finset (Fin (3*k+1)))) by
      ext x; simp only [Set.mem_range, Set.mem_image, SetLike.mem_coe];
      exact ⟨fun ⟨B,h⟩ => ⟨B.val,B.property,h⟩, fun ⟨B,hB,h⟩ => ⟨⟨B,hB⟩,h⟩⟩,
      hY, ht.span_image_extend_eq_span_image hsub, span_slice hk]
  have hyind : LinearIndependent ℝ (fun B : ↥Y => indVec B.val) := hind
  have hcard := finrank_span_eq_card hyind
  rw [hspan, finrank_top, Module.finrank_pi, Fintype.card_fin, Fintype.card_coe] at hcard
  refine ⟨Y, Finset.card_pos.mp (by omega), (fun B hB => hU (hmem.mp hB)), hcard.symm, ?_, ?_⟩
  · intro B hB
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hB
    have hm : g i ∈ U := ht.subset_extend hsub ⟨i,rfl⟩
    exact hmem.mpr hm
  · intro w c hw B hB
    let u (i : Fin (3*k+1)) := w i-c/(k : ℝ)
    have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hsum (V : Finset (Fin (3*k+1))) (hV : V.card = k) :
        sumForm u (indVec V) = (∑ i ∈ V, w i)-c := by
      rw [sumForm_indVec]
      simp only [u, Finset.sum_sub_distrib, Finset.sum_const, hV, nsmul_eq_mul]
      field_simp
    have hker : Submodule.span ℝ (Set.range (fun B : ↥Y => indVec B.val)) ≤ (sumForm u).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨V,rfl⟩
      change sumForm u (indVec V.val) = 0
      rw [hsum _ (slice_card_of_mem (hU (hmem.mp V.property))), hw V V.property, sub_self]
    have hv : indVec B ∈ (sumForm u).ker := hker (hspan.symm ▸ Submodule.mem_top)
    rw [LinearMap.mem_ker, hsum _ (slice_card_of_mem hB)] at hv
    exact sub_eq_zero.mp hv

end MinimalSlice

theorem Conjectures.LogRank.MinimalSliceProtocol :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 2 ≤ k →
    let n := 3*k+1
    let layer := (Finset.univ : Finset (Fin n)).powersetCard k
    let adj := fun (A B : Finset (Fin n)) (a : ℤ) => ((A ∩ B).card : ℤ) = a ∨ ((A ∩ B).card : ℤ) = a+1
    let detects := fun (Y : Finset (Finset (Fin n))) =>
      ∀ A : Finset (Fin n), 2 ≤ A.card → A.card + 2 ≤ n → ∀ a : ℤ, ∃ B ∈ Y, ¬ adj A B a
    let lin := fun (w : Fin n → ℝ) (B : Finset (Fin n)) => Finset.sum B w
    let uniqueOn := fun (Y : Finset (Finset (Fin n))) =>
      ∀ (w : Fin n → ℝ) (c : ℝ), (∀ B ∈ Y, lin w B = c) → ∀ B ∈ layer, lin w B = c
    ∃ Y : Finset (Finset (Fin n)), Y.Nonempty ∧ Y ⊆ layer ∧ Y.card = n ∧ detects Y ∧ uniqueOn Y ∧
      ∀ (m : ℕ) (A : Fin m → Finset (Fin n)) (a : ℤ), (∀ i, ∀ B ∈ Y, adj (A i) B a) →
        let M : Matrix (Fin m) (↥Y) ℝ := fun i j => (((A i ∩ j.val).card : ℝ) - (a : ℝ))
        ∃ send : Fin m → Fin (M.rank+1), ∃ reply : Fin (M.rank+1) → ↥Y → Bool,
          ∃ out : Fin m → Bool → Bool, ∀ i j, (out i (reply (send i) j) = true ↔ M i j = 1) := by
  obtain ⟨K,hK⟩ := MinimalSlice.selected_tuple 1000000 le_rfl
  refine ⟨K,fun k hk hk₂ => ?_⟩
  dsimp only
  obtain ⟨f,hfi,hfs,hfl⟩ := hK k hk
  obtain ⟨Y,hYn,hYs,hYc,hYf,hYu⟩ := MinimalSlice.completed_basis hk₂ f hfi
  have hd : MinimalSlice.Detects Y := by
    intro A hA hA' a
    obtain ⟨B,hB,hBa⟩ := MinimalSlice.detects_tuple hk₂ f hfs hfl A hA hA' a
    exact ⟨B,hYf hB,hBa⟩
  refine ⟨Y,hYn,hYs,hYc,hd,hYu,?_⟩
  intro m A a hA
  exact MinimalSliceProtocolSource.rank_sized_protocol (3*k+1) k m A Y a hk₂ (by omega)
    hYn hYs hd hYu hA
