import Mathlib

theorem Conjectures.Goldbach.OddSignedSubsetFloor :
∀ (m : ℕ) (c : Finset ℕ → ℝ), c ∅ = 1 → (∀ T ∈ (Finset.range m).powerset, -1 ≤ c T) → (1 / 2 : ℝ) < Finset.sum (Finset.range m).powerset (fun T => c T * Finset.prod T (fun j => 1 / (4 * ((j : ℝ) + 1)^2))) := by
  intro m c hc hl
  let f (j : ℕ) := 1/(4*((j:ℝ)+1)^2)
  let F (k : ℕ) := ∏ j ∈ Finset.range k,(1+f j)
  have hprod (n : ℕ) : F (n+1) ≤ (3/2:ℝ)*(1-1/(4*((n:ℝ)+1)+2)) := by
    induction n with
    | zero => norm_num [F,f]
    | succ n ih =>
      have eq : F (n+1+1) = F (n+1)*(1+f (n+1)) := Finset.prod_range_succ ..
      rw [eq]
      apply (mul_le_mul_of_nonneg_right ih (show 0 ≤ 1+f (n+1) by dsimp [f]; positivity)).trans
      dsimp [f]
      push_cast
      field_simp
      nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hF : F m < 3/2 := by
    cases m with
    | zero => norm_num [F]
    | succ n =>
      refine (hprod n).trans_lt ?_
      have : (0:ℝ)<1/(4*((n:ℝ)+1)+2) := by positivity
      linarith
  let P := (Finset.range m).powerset
  let w (T : Finset ℕ) := ∏ j ∈ T,f j
  have hf (T : Finset ℕ) : 0 ≤ w T := Finset.prod_nonneg (fun j _ => by dsimp [f]; positivity)
  have hsum : ∑ T ∈ P, w T = F m := (Finset.prod_one_add (Finset.range m)).symm
  have hzero : ∅ ∈ P := Finset.empty_mem_powerset _
  have he : w ∅=1 := Finset.prod_empty
  have h1 := Finset.sum_erase_add P w hzero
  have h2 := Finset.sum_erase_add P (fun T => c T*w T) hzero
  rw [he] at h1
  rw [hc,he,one_mul] at h2
  have hlo : -(∑ T ∈ P.erase ∅,w T) ≤ ∑ T ∈ P.erase ∅,c T*w T := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun T h => by
      simpa only [neg_one_mul] using mul_le_mul_of_nonneg_right (hl T (Finset.mem_of_mem_erase h)) (hf T)
  change (1/2:ℝ) < ∑ T ∈ P,c T*w T
  linarith only [h1,h2,hsum,hlo,hF]
