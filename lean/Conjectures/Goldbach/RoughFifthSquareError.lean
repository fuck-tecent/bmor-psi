import Mathlib

open Finset

namespace Conjectures.Goldbach.RoughFifth

private theorem tail (z k : ℕ) (hz : 1 ≤ z) :
    (∑ i ∈ range k, (1:ℝ) / ((z+i+1:ℕ):ℝ)^2) ≤ 1/(z:ℝ) - 1/((z+k:ℕ):ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have hstep : (1:ℝ)/((z+k+1:ℕ):ℝ)^2 ≤ 1/((z+k:ℕ):ℝ) - 1/((z+k+1:ℕ):ℝ) := by
      let x : ℝ := z+k
      have hx : 0 < x := by dsimp [x]; exact_mod_cast (show 0 < z+k by omega)
      push_cast
      change 1/(x+1)^2 ≤ 1/x - 1/(x+1)
      field_simp
      nlinarith
    change _ ≤ 1/(z:ℝ) - 1/((z+k+1:ℕ):ℝ)
    linarith

private theorem multiples (N d : ℕ) :
    ((Icc 1 N).filter (fun n => d ∣ n)).card = N/d := by
  have hs : (Icc 1 N).filter (fun n => d ∣ n) = (range N.succ).filter (fun n => n ≠ 0 ∧ d ∣ n) := by
    ext n
    simp only [mem_filter,mem_Icc,mem_range]
    omega
  rw [hs,Nat.card_multiples']

private theorem cost (N z : ℕ) (hz : 1 ≤ z) :
    (∑ i ∈ range N, ((N/(z+i+1)^2 : ℕ) : ℝ)) ≤ (N:ℝ)/z := by
  let w (i : ℕ) : ℝ := 1/((z+i+1:ℕ):ℝ)^2
  have term (i : ℕ) : ((N/(z+i+1)^2:ℕ):ℝ) ≤ (N:ℝ)*w i := by
    change ((N/(z+i+1)^2:ℕ):ℝ) ≤ (N:ℝ)*(1/((z+i+1:ℕ):ℝ)^2)
    rw [mul_one_div, ← Nat.cast_pow]
    exact Nat.cast_div_le
  have h := sum_le_sum (s:=range N) (fun i _ => term i)
  rw [← Finset.mul_sum] at h
  have ht : ∑ i ∈ range N, w i ≤ 1/(z:ℝ) :=
    (tail z N hz).trans (sub_le_self _ (by positivity))
  simpa only [mul_one_div] using h.trans (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg N))

theorem bound :
    let C := fun N : ℕ => (Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5)
    ∀ N z : ℕ, 1 ≤ z → z^5 ≤ N → z*((C N).filter (fun p => ¬ Squarefree (N-p))).card ≤ N := by
  classical
  intro C N z hz hN
  let B := (C N).filter (fun p => ¬ Squarefree (N-p))
  let D (i : ℕ) := (Icc 1 N).filter (fun m => (z+i+1)^2 ∣ m)
  have hcover : B.card ≤ ((range N).biUnion D).card := by
    apply card_le_card_of_injOn (fun p => N-p)
    · intro p hp
      obtain ⟨hpC,hnot⟩ := mem_filter.mp hp
      obtain ⟨hpr,_,_,_,hgt,hrough⟩ := mem_filter.mp hpC
      rw [Nat.squarefree_iff_prime_squarefree] at hnot
      push Not at hnot
      obtain ⟨q,hq,hdiv⟩ := hnot
      have hqm : q ∣ N-p := dvd_trans (dvd_mul_right q q) hdiv
      have hfac := Nat.minFac_le_of_dvd hq.two_le hqm
      have hqz : z < q := by
        by_contra! h
        exact (not_lt_of_ge (le_trans (Nat.pow_le_pow_left (hfac.trans h) 5) hN)) hrough
      have hqN := Nat.le_of_dvd (by omega : 0<N-p) hqm
      refine mem_biUnion.mpr ⟨q-z-1,mem_range.mpr (by omega),?_⟩
      change N-p ∈ D (q-z-1)
      apply mem_filter.mpr
      exact ⟨mem_Icc.mpr ⟨by omega,Nat.sub_le ..⟩,by simpa only [show z+(q-z-1)+1=q by omega,sq] using hdiv⟩
    · intro p hp q hq he
      have hpN := mem_range.mp (mem_filter.mp (mem_filter.mp hp).1).1
      have hqN := mem_range.mp (mem_filter.mp (mem_filter.mp hq).1).1
      change N-p=N-q at he
      omega
  have hcards : B.card ≤ ∑ i ∈ range N, N/(z+i+1)^2 := by
    have h := hcover.trans card_biUnion_le
    simpa only [D,multiples] using h
  have hcast : (B.card:ℝ) ≤ ∑ i ∈ range N, ((N/(z+i+1)^2:ℕ):ℝ) := by exact_mod_cast hcards
  have hR := hcast.trans (cost N z hz)
  have h := (le_div_iff₀ (by exact_mod_cast (show 0<z by omega))).mp hR
  exact_mod_cast (show (z:ℝ)*B.card ≤ N by linarith only [h])

end Conjectures.Goldbach.RoughFifth

theorem Conjectures.Goldbach.RoughFifthSquareError :
    let C := fun N : ℕ => (Finset.range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧ 1 < N-p ∧ N < (N-p).minFac^5)
    ∀ N z : ℕ, 1 ≤ z → z^5 ≤ N → z*((C N).filter (fun p => ¬ Squarefree (N-p))).card ≤ N :=
  Conjectures.Goldbach.RoughFifth.bound
