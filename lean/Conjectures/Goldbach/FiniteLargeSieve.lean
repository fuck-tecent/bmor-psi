import Mathlib

theorem Conjectures.Goldbach.FiniteLargeSieve :
    ∀ (N Q : ℕ) [NeZero Q] (a : ℕ → ℂ), (∑ r : ZMod Q, ‖∑ n ∈ Finset.range (N + 1), a n * ZMod.stdAddChar (r * (n : ZMod Q))‖ ^ 2) ≤ (N + Q : ℝ) * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 := by
  intro N Q _ a
  classical
  let ψ : AddChar (ZMod Q) ℂ := ZMod.stdAddChar
  have hprim : ψ.IsPrimitive := ZMod.isPrimitive_stdAddChar Q
  let c : ℕ → ZMod Q := fun n => (n : ZMod Q)
  let S : ZMod Q → ℂ := fun r => ∑ n ∈ Finset.range (N + 1), a n * ψ (r * c n)
  let T : ZMod Q → ℂ := fun t =>
    ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => c n = t), a n
  have hL : (∑ r : ZMod Q,
      ‖∑ n ∈ Finset.range (N + 1), a n * ZMod.stdAddChar (r * (n : ZMod Q))‖ ^ 2) =
      ∑ r : ZMod Q, ‖S r‖ ^ 2 := rfl
  rw [hL]
  have hnorm : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    intro z
    rw [Complex.star_def, Complex.ofReal_pow]
    exact (RCLike.mul_conj z).symm
  have hstar : ∀ r, star (S r) =
      ∑ m ∈ Finset.range (N + 1), star (a m) * star (ψ (r * c m)) := by
    intro r
    dsimp only [S]
    rw [star_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [star_mul, mul_comm]
  have hSr : ∀ r, S r * star (S r) =
      ∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
        a n * star (a m) * (ψ (r * c n) * star (ψ (r * c m))) := by
    intro r
    rw [hstar r]
    dsimp only [S]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun m hm => ?_))
    ring
  have hψprod : ∀ (r : ZMod Q) (n m : ℕ), ψ (r * c n) * star (ψ (r * c m)) =
      ψ (r * (c n - c m)) := by
    intro r n m
    rw [Complex.star_def]
    rw [← AddChar.map_neg_eq_conj]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hsum_r : ∀ n m : ℕ, (∑ r : ZMod Q, ψ (r * (c n - c m))) =
      if (c n = c m) then (Q : ℂ) else 0 := by
    intro n m
    rw [AddChar.sum_mulShift (c n - c m) hprim, ZMod.card Q]
    push_cast
    by_cases h : (c n = c m)
    · rw [if_pos (sub_eq_zero.mpr h), if_pos h]
    · rw [if_neg (fun hz => h (sub_eq_zero.mp hz)), if_neg h]
  have hdouble : (∑ r : ZMod Q, ∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
        a n * star (a m) * (ψ (r * c n) * star (ψ (r * c m))))
      = ∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
          a n * star (a m) * (if (c n = c m) then (Q : ℂ) else 0) := by
    simp_rw [hψprod]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [← Finset.mul_sum, hsum_r n m]
  have hTstar : ∀ t : ZMod Q, star (T t) =
      ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => c n = t), star (a n) := by
    intro t
    dsimp only [T]
    rw [star_sum]
  have hTprod : ∀ t : ZMod Q, T t * star (T t) =
      ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => c n = t),
        ∑ m ∈ (Finset.range (N + 1)).filter (fun m : ℕ => c m = t), a n * star (a m) := by
    intro t
    rw [hTstar t]
    dsimp only [T]
    rw [Finset.sum_mul_sum]
  have hclassA : (∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
        a n * star (a m) * (if (c n = c m) then (Q : ℂ) else 0))
      = (Q : ℂ) * ∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
          a n * star (a m) * (if (c n = c m) then (1 : ℂ) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    by_cases h : (c n = c m)
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  have hinner : ∀ n : ℕ, (∑ m ∈ Finset.range (N + 1),
        a n * star (a m) * (if (c n = c m) then (1 : ℂ) else 0))
      = ∑ m ∈ (Finset.range (N + 1)).filter (fun m : ℕ => c m = c n), a n * star (a m) := by
    intro n
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    rw [show (Finset.range (N + 1)).filter (fun m : ℕ => c n = c m)
        = (Finset.range (N + 1)).filter (fun m : ℕ => c m = c n) from by
      ext m
      simp only [Finset.mem_filter]
      exact and_congr_right (fun _ => eq_comm)]
  have hclassB : (∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
        a n * star (a m) * (if (c n = c m) then (1 : ℂ) else 0))
      = ∑ t : ZMod Q, T t * star (T t) := by
    simp_rw [hinner]
    rw [← Finset.sum_fiberwise (s := Finset.range (N + 1)) (g := c)
      (f := fun n : ℕ => ∑ m ∈ (Finset.range (N + 1)).filter (fun m : ℕ => c m = c n),
        a n * star (a m))]
    have hcongr : ∀ j : ZMod Q, (∑ i ∈ (Finset.range (N + 1)).filter (fun i : ℕ => c i = j),
        ∑ m ∈ (Finset.range (N + 1)).filter (fun m : ℕ => c m = c i), a i * star (a m))
        = ∑ i ∈ (Finset.range (N + 1)).filter (fun i : ℕ => c i = j),
            ∑ m ∈ (Finset.range (N + 1)).filter (fun m : ℕ => c m = j), a i * star (a m) := by
      intro j
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_filter] at hi
      rw [hi.2]
    simp_rw [hcongr]
    exact (Finset.sum_congr rfl (fun t _ => hTprod t)).symm
  have hclass : (∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
        a n * star (a m) * (if (c n = c m) then (Q : ℂ) else 0))
      = (Q : ℂ) * ∑ t : ZMod Q, T t * star (T t) := by
    rw [hclassA, hclassB]
  have hreal : (∑ r : ZMod Q, ‖S r‖ ^ 2) = (Q : ℝ) * ∑ t : ZMod Q, ‖T t‖ ^ 2 := by
    have hQ : (Q : ℂ) = ((Q : ℝ) : ℂ) := by push_cast; rfl
    have key : (∑ r : ZMod Q, ((‖S r‖ ^ 2 : ℝ) : ℂ)) =
        ((Q : ℝ) : ℂ) * ∑ t : ZMod Q, ((‖T t‖ ^ 2 : ℝ) : ℂ) := by
      calc (∑ r : ZMod Q, ((‖S r‖ ^ 2 : ℝ) : ℂ))
          = ∑ r : ZMod Q, S r * star (S r) :=
              Finset.sum_congr rfl (fun r _ => hnorm (S r))
        _ = ∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
              a n * star (a m) * (if (c n = c m) then (Q : ℂ) else 0) := by
              rw [Finset.sum_congr rfl (fun r _ => hSr r)]
              exact hdouble
        _ = (Q : ℂ) * ∑ t : ZMod Q, T t * star (T t) := hclass
        _ = ((Q : ℝ) : ℂ) * ∑ t : ZMod Q, ((‖T t‖ ^ 2 : ℝ) : ℂ) := by
              rw [hQ]
              congr 1
              exact Finset.sum_congr rfl (fun t _ => (hnorm (T t)).symm)
    apply Complex.ofReal_inj.mp
    rw [Complex.ofReal_mul]
    simp only [Complex.ofReal_sum]
    exact key
  have hT_each : ∀ t : ZMod Q, ‖T t‖ ^ 2 ≤
      (((Finset.range (N + 1)).filter (fun n : ℕ => c n = t)).card : ℝ) *
        ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => c n = t), ‖a n‖ ^ 2 := by
    intro t
    have hTdef : T t = ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => c n = t), a n := rfl
    have h1 : ‖T t‖ ≤ ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => c n = t), ‖a n‖ := by
      rw [hTdef]
      exact norm_sum_le _ _
    have h2 : ‖T t‖ ^ 2 ≤
        (∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => c n = t), ‖a n‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => c n = t), ‖a n‖) ^ 2 ≤
        (((Finset.range (N + 1)).filter (fun n : ℕ => c n = t)).card : ℝ) *
          ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => c n = t), ‖a n‖ ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq
        (s := (Finset.range (N + 1)).filter (fun n : ℕ => c n = t))
        (f := fun n : ℕ => ‖a n‖)
      simpa using h
    exact h2.trans h3
  have hcard : ∀ t : ZMod Q, (((Finset.range (N + 1)).filter (fun n : ℕ => c n = t)).card : ℝ) ≤
      ((N / Q : ℕ) + 1 : ℝ) := by
    intro t
    have hnat : ((Finset.range (N + 1)).filter (fun n : ℕ => c n = t)).card ≤ N / Q + 1 := by
      have h : ((Finset.range (N + 1)).filter (fun n : ℕ => c n = t)).card ≤
          (Finset.range (N / Q + 1)).card := by
        refine Finset.card_le_card_of_injOn
          (s := (Finset.range (N + 1)).filter (fun n : ℕ => c n = t))
          (t := Finset.range (N / Q + 1)) (f := fun n : ℕ => n / Q) ?_ ?_
        · intro n hn
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
          simp only [Finset.mem_coe, Finset.mem_range]
          have hnN : n ≤ N := Nat.lt_succ_iff.mp hn.1
          exact Nat.lt_succ_of_le (Nat.div_le_div_right hnN)
        · intro n1 hn1 n2 hn2 hdiv
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn1 hn2
          have hdiv' : n1 / Q = n2 / Q := hdiv
          have hmod : n1 % Q = n2 % Q := by
            have h : (n1 : ZMod Q) = (n2 : ZMod Q) := by
              rw [show (n1 : ZMod Q) = t from hn1.2,
                  show (n2 : ZMod Q) = t from hn2.2]
            exact (ZMod.natCast_eq_natCast_iff n1 n2 Q).mp h
          calc n1 = Q * (n1 / Q) + n1 % Q := (Nat.div_add_mod n1 Q).symm
            _ = Q * (n2 / Q) + n2 % Q := by rw [hdiv', hmod]
            _ = n2 := Nat.div_add_mod n2 Q
      simpa using h
    exact_mod_cast hnat
  have hT_bound : ∑ t : ZMod Q, ‖T t‖ ^ 2 ≤
      ((N / Q : ℕ) + 1 : ℝ) * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 := by
    have hstep : (∑ t : ZMod Q, ‖T t‖ ^ 2) ≤
        ∑ t : ZMod Q, ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => c n = t),
          (((N / Q : ℕ) + 1 : ℝ)) * ‖a n‖ ^ 2 := by
      calc ∑ t : ZMod Q, ‖T t‖ ^ 2
          ≤ ∑ t : ZMod Q, (((Finset.range (N + 1)).filter (fun n : ℕ => c n = t)).card : ℝ) *
              ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => c n = t), ‖a n‖ ^ 2 :=
            Finset.sum_le_sum (fun t _ => hT_each t)
        _ = ∑ t : ZMod Q, ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => c n = t),
              (((Finset.range (N + 1)).filter (fun n : ℕ => c n = t)).card : ℝ) * ‖a n‖ ^ 2 := by
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [Finset.mul_sum]
        _ ≤ ∑ t : ZMod Q, ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => c n = t),
              (((N / Q : ℕ) + 1 : ℝ)) * ‖a n‖ ^ 2 := by
            refine Finset.sum_le_sum (fun t _ => Finset.sum_le_sum (fun n hn => ?_))
            exact mul_le_mul_of_nonneg_right (hcard t) (by positivity)
    calc ∑ t : ZMod Q, ‖T t‖ ^ 2
        ≤ ∑ t : ZMod Q, ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => c n = t),
            (((N / Q : ℕ) + 1 : ℝ)) * ‖a n‖ ^ 2 := hstep
      _ = ((N / Q : ℕ) + 1 : ℝ) * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 := by
            rw [Finset.mul_sum]
            rw [← Finset.sum_fiberwise (s := Finset.range (N + 1)) (g := c)
              (f := fun n : ℕ => ((N / Q : ℕ) + 1 : ℝ) * ‖a n‖ ^ 2)]
  have hC : (Q : ℝ) * ((N / Q : ℕ) + 1 : ℝ) ≤ (N : ℝ) + Q := by
    have h1 : (Q : ℝ) * ((N / Q : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (Nat.mul_div_le N Q)
    have h2 : (Q : ℝ) * ((N / Q : ℕ) : ℝ) + (Q : ℝ) ≤ (N : ℝ) + Q := by linarith
    calc (Q : ℝ) * ((N / Q : ℕ) + 1 : ℝ) = (Q : ℝ) * ((N / Q : ℕ) : ℝ) + (Q : ℝ) := by
          push_cast; ring
      _ ≤ (N : ℝ) + Q := h2
  calc ∑ r : ZMod Q, ‖S r‖ ^ 2
      = (Q : ℝ) * ∑ t : ZMod Q, ‖T t‖ ^ 2 := hreal
    _ ≤ (Q : ℝ) * (((N / Q : ℕ) + 1 : ℝ) * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hT_bound (Nat.cast_nonneg Q)
    _ = ((Q : ℝ) * ((N / Q : ℕ) + 1 : ℝ)) * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 := by
          ring
    _ ≤ ((N : ℝ) + Q) * ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right hC (Finset.sum_nonneg (fun n _ => by positivity))
