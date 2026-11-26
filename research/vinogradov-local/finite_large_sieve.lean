import Mathlib

open scoped BigOperators
open Finset AddChar ZMod

namespace PEqualNP.Outside

noncomputable section

lemma sum_stdAddChar_mul (Q : ℕ) [NeZero Q] (b : ZMod Q) :
    (∑ r : ZMod Q, ZMod.stdAddChar (r * b)) =
      if b = 0 then (Q : ℂ) else 0 := by
  simpa [ZMod.card] using
    (AddChar.sum_mulShift (ψ := ZMod.stdAddChar) b (ZMod.isPrimitive_stdAddChar Q))

lemma star_stdAddChar (Q : ℕ) [NeZero Q] (x : ZMod Q) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv]
  symm
  apply Complex.inv_eq_conj
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

lemma parseval_zmod (Q : ℕ) [NeZero Q] (A : ZMod Q → ℂ) :
    (∑ r : ZMod Q,
        ‖∑ c : ZMod Q, A c * ZMod.stdAddChar (r * c)‖ ^ 2) =
      (Q : ℝ) * ∑ c : ZMod Q, ‖A c‖ ^ 2 := by
  classical
  let F : ZMod Q → ℂ := fun r => ∑ c : ZMod Q, A c * ZMod.stdAddChar (r * c)
  have hcast : ((∑ r : ZMod Q, ‖F r‖ ^ 2 : ℝ) : ℂ) =
      ∑ r : ZMod Q, F r * star (F r) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro r _
    push_cast
    exact (Complex.mul_conj' (F r)).symm
  have hstar : ∀ r : ZMod Q, star (F r) =
      ∑ c : ZMod Q, star (A c) * ZMod.stdAddChar (r * (-c)) := by
    intro r
    dsimp only [F]
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [star_mul, star_stdAddChar, mul_comm]
    congr 1
    ring_nf
  have hexpand : ∀ r : ZMod Q, F r * star (F r) =
      ∑ c : ZMod Q, ∑ d : ZMod Q,
        A c * star (A d) * ZMod.stdAddChar (r * (c - d)) := by
    intro r
    rw [hstar]
    dsimp only [F]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    calc
      (A c * ZMod.stdAddChar (r * c)) *
          (star (A d) * ZMod.stdAddChar (r * (-d)))
          = A c * star (A d) *
              (ZMod.stdAddChar (r * c) * ZMod.stdAddChar (r * (-d))) := by ring
      _ = A c * star (A d) * ZMod.stdAddChar (r * (c - d)) := by
        rw [← AddChar.map_add_eq_mul]
        congr 2
        ring_nf
  have hcomplex : ((∑ r : ZMod Q, ‖F r‖ ^ 2 : ℝ) : ℂ) =
      (Q : ℂ) * ∑ c : ZMod Q, ((‖A c‖ ^ 2 : ℝ) : ℂ) := by
    rw [hcast]
    simp_rw [hexpand]
    rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single c]
    · rw [← Finset.mul_sum, sum_stdAddChar_mul]
      simp [Complex.mul_conj', mul_comm]
    · intro d _ hne
      have hcd : c ≠ d := fun h => hne h.symm
      rw [← Finset.mul_sum, sum_stdAddChar_mul]
      simp [sub_ne_zero.mpr hcd]
    · intro hc
      simp at hc
  have hreal : ((∑ r : ZMod Q, ‖F r‖ ^ 2 : ℝ) : ℂ) =
      ((Q : ℝ) * ∑ c : ZMod Q, ‖A c‖ ^ 2 : ℝ) := by
    simpa [Complex.ofReal_mul, Complex.ofReal_sum] using hcomplex
  exact Complex.ofReal_injective hreal

end

end PEqualNP.Outside


open scoped BigOperators
open Finset

namespace PEqualNP.Outside

noncomputable section

lemma fiber_card_le (N Q : ℕ) [NeZero Q] (c : ZMod Q) :
    ((Finset.range (N + 1)).filter (fun n : ℕ => (n : ZMod Q) = c)).card ≤ N / Q + 1 := by
  classical
  let s : Finset ℕ := (Finset.range (N + 1)).filter (fun n : ℕ => (n : ZMod Q) = c)
  have hinj : Set.InjOn (fun n : ℕ => n / Q) (s : Set ℕ) := by
    intro n hn m hm hdiv
    have hn' : n ∈ s := hn
    have hm' : m ∈ s := hm
    simp only [s, Finset.mem_filter, Finset.mem_range] at hn' hm'
    have hnmod : n % Q = c.val := by
      have h := congrArg ZMod.val hn'.2
      simpa [ZMod.val_natCast] using h
    have hmmod : m % Q = c.val := by
      have h := congrArg ZMod.val hm'.2
      simpa [ZMod.val_natCast] using h
    have hdiv' : n / Q = m / Q := hdiv
    have hn_decomp : Q * (n / Q) + n % Q = n := Nat.div_add_mod n Q
    have hm_decomp : Q * (m / Q) + m % Q = m := Nat.div_add_mod m Q
    rw [hdiv', hnmod] at hn_decomp
    rw [hmmod] at hm_decomp
    omega
  have himage : s.image (fun n : ℕ => n / Q) ⊆ Finset.range (N / Q + 1) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
    simp only [s, Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  calc
    s.card = (s.image (fun n : ℕ => n / Q)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (N / Q + 1)).card := Finset.card_le_card himage
    _ = N / Q + 1 := Finset.card_range _

end

end PEqualNP.Outside


namespace PEqualNP.Outside

noncomputable section

open Finset AddChar ZMod

def folded (N Q : ℕ) [NeZero Q] (a : ℕ → ℂ) (c : ZMod Q) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), if (n : ZMod Q) = c then a n else 0

lemma S_eq_folded (N Q : ℕ) [NeZero Q] (a : ℕ → ℂ) (r : ZMod Q) :
    (∑ n ∈ Finset.range (N + 1), a n * ZMod.stdAddChar (r * (n : ZMod Q))) =
      ∑ c : ZMod Q, folded N Q a c * ZMod.stdAddChar (r * c) := by
  classical
  dsimp only [folded]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_eq_single (c : ZMod Q)]
  · simp
  · intro x _ hx
    have hxc : (c : ZMod Q) ≠ x := fun h => hx h.symm
    simp [hxc]
  · intro hc
    simp at hc

lemma folded_normSq_le (N Q : ℕ) [NeZero Q] (a : ℕ → ℂ) :
    (∑ c : ZMod Q, ‖folded N Q a c‖ ^ 2) ≤
      ((N / Q + 1 : ℕ) : ℝ) * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 := by
  classical
  let fiber : ZMod Q → Finset ℕ := fun c =>
    (Finset.range (N + 1)).filter (fun n : ℕ => (n : ZMod Q) = c)
  have hbound : ∀ c : ZMod Q,
      ‖folded N Q a c‖ ^ 2 ≤
        (fiber c).card * ∑ n ∈ fiber c, ‖a n‖ ^ 2 := by
    intro c
    have hnorm : ‖folded N Q a c‖ ≤ ∑ n ∈ fiber c, ‖a n‖ := by
      have hfold : folded N Q a c = ∑ n ∈ fiber c, a n := by
        dsimp only [folded, fiber]
        rw [Finset.sum_filter]
      rw [hfold]
      exact norm_sum_le (fiber c) (fun n => a n)
    have hsum : (∑ n ∈ fiber c, ‖a n‖) ^ 2 ≤
        ((fiber c).card : ℝ) * ∑ n ∈ fiber c, ‖a n‖ ^ 2 := by
      simpa using
        (Finset.sum_mul_sq_le_sq_mul_sq (fiber c) (fun _ => (1 : ℝ))
          (fun n => ‖a n‖))
    calc
      ‖folded N Q a c‖ ^ 2 ≤ (∑ n ∈ fiber c, ‖a n‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ ≤ _ := hsum
  calc
    (∑ c : ZMod Q, ‖folded N Q a c‖ ^ 2) ≤
        ∑ c : ZMod Q, (fiber c).card * ∑ n ∈ fiber c, ‖a n‖ ^ 2 :=
      Finset.sum_le_sum fun c _ => hbound c
    _ ≤ ∑ c : ZMod Q, ((N / Q + 1 : ℕ) : ℝ) * ∑ n ∈ fiber c, ‖a n‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast fiber_card_le N Q c
    _ = ((N / Q + 1 : ℕ) : ℝ) *
        ∑ c : ZMod Q, ∑ n ∈ fiber c, ‖a n‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ = ((N / Q + 1 : ℕ) : ℝ) * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 := by
      congr 1
      simpa only [fiber] using
        (Finset.sum_fiberwise_of_maps_to (s := Finset.range (N + 1))
          (t := Finset.univ) (g := fun n : ℕ => (n : ZMod Q))
          (f := fun n => ‖a n‖ ^ 2) (by simp))

theorem L_goldbach_finite_large_sieve (N Q : ℕ) [NeZero Q] (a : ℕ → ℂ) :
    (∑ r : ZMod Q,
        ‖∑ n ∈ Finset.range (N + 1), a n * ZMod.stdAddChar (r * (n : ZMod Q))‖ ^ 2) ≤
      (N + Q : ℝ) * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 := by
  classical
  calc
    (∑ r : ZMod Q,
        ‖∑ n ∈ Finset.range (N + 1), a n * ZMod.stdAddChar (r * (n : ZMod Q))‖ ^ 2)
        = ∑ r : ZMod Q, ‖∑ c : ZMod Q, folded N Q a c * ZMod.stdAddChar (r * c)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro r _
          rw [S_eq_folded]
    _ = (Q : ℝ) * ∑ c : ZMod Q, ‖folded N Q a c‖ ^ 2 :=
      parseval_zmod Q (folded N Q a)
    _ ≤ (Q : ℝ) * (((N / Q + 1 : ℕ) : ℝ) *
        ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left (folded_normSq_le N Q a)
      positivity
    _ ≤ (N + Q : ℝ) * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 := by
      have hdiv : (Q : ℝ) * ((N / Q : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Nat.mul_div_le N Q
      have hcoef : (Q : ℝ) * (((N / Q + 1 : ℕ) : ℝ)) ≤ (N : ℝ) + Q := by
        have hQ : (0 : ℝ) ≤ Q := by positivity
        push_cast
        nlinarith
      have hS : (0 : ℝ) ≤ ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 := by positivity
      calc
        (Q : ℝ) * ((((N / Q + 1 : ℕ) : ℝ)) *
            ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2)
            = ((Q : ℝ) * (((N / Q + 1 : ℕ) : ℝ))) *
                ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 := by ring
        _ ≤ ((N : ℝ) + Q) * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef hS

end

end PEqualNP.Outside
