import Mathlib

namespace Conjectures.Goldbach.RoughFifthBridge_aux

theorem minFac_pow_cardFactors_le (m : ℕ) (hm : 1 < m) :
    m.minFac ^ ArithmeticFunction.cardFactors m ≤ m := by
  rw [ArithmeticFunction.cardFactors_apply]
  have hlist : ∀ l : List ℕ, (∀ a ∈ l, m.minFac ≤ a) →
      m.minFac ^ l.length ≤ l.prod := by
    intro l
    induction l with
    | nil =>
        intro _
        simp
    | cons a l ih =>
        intro h
        have ha : m.minFac ≤ a := h a (by simp)
        have hl : ∀ b ∈ l, m.minFac ≤ b := by
          intro b hb
          exact h b (by simp [hb])
        calc
          m.minFac ^ (a :: l).length =
              m.minFac * m.minFac ^ l.length := by simp [pow_succ, Nat.mul_comm]
          _ ≤ a * l.prod := Nat.mul_le_mul ha (ih hl)
          _ = (a :: l).prod := by simp
  calc
    m.minFac ^ m.primeFactorsList.length ≤ m.primeFactorsList.prod := by
      apply hlist
      intro a ha
      exact Nat.minFac_le_of_dvd
        (Nat.prime_of_mem_primeFactorsList ha).two_le
        (Nat.dvd_of_mem_primeFactorsList ha)
    _ = m := Nat.prod_primeFactorsList (by omega)

theorem cardFactors_le_four (m N : ℕ) (hm : 1 < m) (hN : m < N)
    (h5 : N < m.minFac ^ 5) : ArithmeticFunction.cardFactors m ≤ 4 := by
  have hmin : 1 < m.minFac := (Nat.minFac_prime (by omega)).one_lt
  have hpow : m.minFac ^ ArithmeticFunction.cardFactors m < m.minFac ^ 5 :=
    (minFac_pow_cardFactors_le m hm).trans_lt (hN.trans h5)
  have hcard : ArithmeticFunction.cardFactors m < 5 :=
    (Nat.pow_lt_pow_iff_right hmin).mp hpow
  omega

end Conjectures.Goldbach.RoughFifthBridge_aux

theorem Conjectures.Goldbach.RoughFifthBridge :
    let C := fun N : ℕ => (Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5); ∀ N : ℕ, 2*(((C N).filter (fun p => Nat.Prime (N-p))).card:ℝ) = ((C N).card:ℝ) - (C N).sum (fun p => (ArithmeticFunction.liouville (N-p) : ℝ)) - 2*(((C N).filter (fun p => ArithmeticFunction.cardFactors (N-p) = 3)).card:ℝ) := by
  dsimp only
  intro N
  set S : Finset ℕ := (Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5) with hSdef
  have hmem : ∀ p ∈ S, Nat.Prime p ∧ p < N ∧ 1 < N - p ∧ N < (N - p).minFac ^ 5 := by
    intro p hp
    have hmemS : p ∈ (Finset.range N).filter
        (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5) := by
      rw [← hSdef]
      exact hp
    have h := Finset.mem_filter.1 hmemS
    exact ⟨h.2.1, Finset.mem_range.1 h.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  have hpt : ∀ p ∈ S, 2 * (if Nat.Prime (N - p) then (1:ℝ) else 0)
      = (1:ℝ) - ((ArithmeticFunction.liouville (N - p) : ℝ))
        - 2 * (if ArithmeticFunction.cardFactors (N - p) = 3 then (1:ℝ) else 0) := by
    intro p hp
    obtain ⟨hpp, hpN, hm1, hm5⟩ := hmem p hp
    have hp0 : 0 < p := hpp.pos
    have hk1 : 1 ≤ ArithmeticFunction.cardFactors (N - p) :=
      ArithmeticFunction.cardFactors_pos_iff_one_lt.2 hm1
    have hk4 : ArithmeticFunction.cardFactors (N - p) ≤ 4 :=
      Conjectures.Goldbach.RoughFifthBridge_aux.cardFactors_le_four (N - p) N hm1 (by omega) hm5
    have hP : Nat.Prime (N - p) ↔ ArithmeticFunction.cardFactors (N - p) = 1 :=
      ArithmeticFunction.cardFactors_eq_one_iff_prime.symm
    have hrw : (if Nat.Prime (N - p) then (1:ℝ) else 0)
        = (if ArithmeticFunction.cardFactors (N - p) = 1 then (1:ℝ) else 0) := by
      by_cases h : Nat.Prime (N - p)
      · simp [h, hP.1 h]
      · simp [h, fun hk : ArithmeticFunction.cardFactors (N - p) = 1 => h (hP.2 hk)]
    have hL : ((ArithmeticFunction.liouville (N - p) : ℝ))
        = (-1:ℝ) ^ ArithmeticFunction.cardFactors (N - p) := by
      rw [ArithmeticFunction.liouville_apply (n := N - p) (by omega : N - p ≠ 0)]
      push_cast
      ring
    rw [hrw, hL]
    interval_cases h : ArithmeticFunction.cardFactors (N - p) <;> norm_num
  have hcard1 : (((S.filter (fun p => Nat.Prime (N - p))).card : ℝ))
      = S.sum (fun p => if Nat.Prime (N - p) then (1:ℝ) else 0) :=
    Finset.natCast_card_filter _ _
  have hcard3 : (((S.filter (fun p => ArithmeticFunction.cardFactors (N - p) = 3)).card : ℝ))
      = S.sum (fun p => if ArithmeticFunction.cardFactors (N - p) = 3 then (1:ℝ) else 0) :=
    Finset.natCast_card_filter _ _
  have hcardS : ((S.card : ℝ)) = S.sum (fun _ => (1:ℝ)) := by
    rw [Finset.card_eq_sum_ones]
    push_cast
    rfl
  rw [hcard1, hcard3, hcardS]
  calc
    2 * S.sum (fun p => if Nat.Prime (N - p) then (1:ℝ) else 0)
        = S.sum (fun p => 2 * (if Nat.Prime (N - p) then (1:ℝ) else 0)) := by
          rw [Finset.mul_sum]
    _ = S.sum (fun p => (1:ℝ) - ((ArithmeticFunction.liouville (N - p) : ℝ))
          - 2 * (if ArithmeticFunction.cardFactors (N - p) = 3 then (1:ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hpt p hp
    _ = (S.sum (fun _ => (1:ℝ))
          - S.sum (fun p => ((ArithmeticFunction.liouville (N - p) : ℝ))))
          - S.sum (fun p => 2 * (if ArithmeticFunction.cardFactors (N - p) = 3 then (1:ℝ) else 0)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = S.sum (fun _ => (1:ℝ))
          - S.sum (fun p => ((ArithmeticFunction.liouville (N - p) : ℝ)))
          - 2 * S.sum (fun p => if ArithmeticFunction.cardFactors (N - p) = 3 then (1:ℝ) else 0) := by
          rw [Finset.mul_sum]
