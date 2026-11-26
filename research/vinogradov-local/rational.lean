import Mathlib
open scoped BigOperators
noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma z_ne_one (t : ℝ) (hsin : Real.sin (Real.pi * t) ≠ 0) : E t ≠ 1 := by
  intro h
  unfold E at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  have hR : (m : ℂ) * (2 * Real.pi * Complex.I) =
      (((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hR] at hm
  have hm' : ((2 * Real.pi * t : ℝ) : ℂ) = (((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) :=
    mul_right_cancel₀ Complex.I_ne_zero hm
  have ht : t = (m : ℝ) := by
    have hreal : 2 * Real.pi * t = (m : ℝ) * (2 * Real.pi) := Complex.ofReal_injective hm'
    field_simp [Real.pi_ne_zero] at hreal
    linarith
  have hsin0 : Real.sin (Real.pi * t) = 0 := by
    rw [show Real.pi * t = (m : ℝ) * Real.pi by rw [ht]; ring]
    exact Real.sin_int_mul_pi m
  exact hsin hsin0

lemma norm_geometric_sum_le (n : ℕ) (t : ℝ) (hsin : Real.sin (Real.pi * t) ≠ 0) :
    ‖∑ k ∈ Finset.range (n + 1), E ((k : ℝ) * t)‖ ≤
      1 / |Real.sin (Real.pi * t)| := by
  classical
  let z := E t
  have hz : z ≠ 1 := z_ne_one t hsin
  have hsum : ∑ k ∈ Finset.range (n + 1), E ((k : ℝ) * t) =
      ∑ k ∈ Finset.range (n + 1), z ^ k := by
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [z]
    unfold E
    rw [show (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I) =
        (k : ℂ) * (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring]
    rw [Complex.exp_nat_mul]
  rw [hsum, geom_sum_eq hz (n + 1), norm_div]
  have hnum : ‖z ^ (n + 1) - 1‖ ≤ 2 := by
    have hz1 : ‖z‖ = 1 := by
      dsimp only [z, E]
      simpa only [mul_comm] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t)
    calc
      ‖z ^ (n + 1) - 1‖ ≤ ‖z ^ (n + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_pow, hz1]; simp
      _ = 2 := by norm_num
  have hden : ‖z - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
    dsimp only [z, E]
    rw [show (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) =
        Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) by rw [mul_comm]]
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    have harg : 2 * Real.pi * t / 2 = Real.pi * t := by ring
    rw [harg]
    rw [Real.norm_eq_abs, abs_mul, abs_two]
  rw [hden]
  have hsinpos : 0 < |Real.sin (Real.pi * t)| := abs_pos.mpr hsin
  field_simp [hsinpos.ne']
  nlinarith


lemma norm_geom_prefix_le (k : ℕ) (t : ℝ) (hsin : Real.sin (Real.pi * t) ≠ 0) :
    ‖∑ j ∈ Finset.range k, E ((j : ℝ) * t)‖ ≤ 1 / |Real.sin (Real.pi * t)| := by
  rcases k with _ | m
  · simp
  · simpa [Nat.succ_eq_add_one] using norm_geometric_sum_le m t hsin

lemma norm_weighted_geometric_sum_le (n : ℕ) (a : ℕ → ℝ) (t : ℝ)
    (hsin : Real.sin (Real.pi * t) ≠ 0) :
    ‖∑ k ∈ Finset.range (n + 1), (a k : ℂ) * E ((k : ℝ) * t)‖ ≤
      (|a n| + ∑ k ∈ Finset.range n, |a k - a (k + 1)|) /
        |Real.sin (Real.pi * t)| := by
  classical
  let z := E t
  have hz : z ≠ 1 := z_ne_one t hsin
  have hterm : ∀ k : ℕ, E ((k : ℝ) * t) = z ^ k := by
    intro k
    dsimp only [z]
    unfold E
    rw [show (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I) =
        (k : ℂ) * (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring]
    rw [Complex.exp_nat_mul]
  simp_rw [hterm]
  let G : ℕ → ℂ := fun k => ∑ j ∈ Finset.range k, z ^ j
  have hG (k : ℕ) : ‖G k‖ ≤ 1 / |Real.sin (Real.pi * t)| := by
    dsimp only [G]
    simpa only [← hterm] using norm_geom_prefix_le k t hsin
  have hparts := Finset.sum_range_by_parts (fun i : ℕ => (a i : ℂ)) (fun i : ℕ => z ^ i) (n + 1)
  simp only [Nat.add_sub_cancel] at hparts
  have hparts' : ∑ i ∈ Finset.range (n + 1), (a i : ℂ) * z ^ i =
      (a n : ℂ) * (∑ i ∈ Finset.range (n + 1), z ^ i) -
        ∑ i ∈ Finset.range n, ((a (i + 1) : ℂ) - (a i : ℂ)) *
          (∑ j ∈ Finset.range (i + 1), z ^ j) := by
    simpa only [smul_eq_mul] using hparts
  rw [hparts']
  have hbound := norm_sub_le ((a n : ℂ) * G (n + 1))
    (∑ i ∈ Finset.range n, ((a (i + 1) : ℂ) - (a i : ℂ)) * G (i + 1))
  have hsumBound :
      ‖∑ i ∈ Finset.range n, ((a (i + 1) : ℂ) - (a i : ℂ)) * G (i + 1)‖ ≤
        ∑ i ∈ Finset.range n, |a i - a (i + 1)| * (1 / |Real.sin (Real.pi * t)|) := by
    calc
      _ ≤ ∑ i ∈ Finset.range n,
          ‖((a (i + 1) : ℂ) - (a i : ℂ)) * G (i + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range n,
          |a i - a (i + 1)| * (1 / |Real.sin (Real.pi * t)|) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        have hcoef : ‖((a (i + 1) : ℂ) - (a i : ℂ))‖ = |a i - a (i + 1)| := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        rw [hcoef]
        exact mul_le_mul_of_nonneg_left (hG (i + 1)) (abs_nonneg _)
  have hfirst : ‖(a n : ℂ) * G (n + 1)‖ = |a n| * ‖G (n + 1)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hBs : 0 ≤ 1 / |Real.sin (Real.pi * t)| := by positivity
  calc
    ‖(a n : ℂ) * G (n + 1) -
        ∑ i ∈ Finset.range n, ((a (i + 1) : ℂ) - (a i : ℂ)) * G (i + 1)‖
        ≤ ‖(a n : ℂ) * G (n + 1)‖ +
            ‖∑ i ∈ Finset.range n, ((a (i + 1) : ℂ) - (a i : ℂ)) * G (i + 1)‖ := hbound
    _ ≤ |a n| * (1 / |Real.sin (Real.pi * t)|) +
          ∑ i ∈ Finset.range n, |a i - a (i + 1)| * (1 / |Real.sin (Real.pi * t)|) := by
      apply add_le_add
      · rw [hfirst]
        exact mul_le_mul_of_nonneg_left (hG (n + 1)) (abs_nonneg _)
      · exact hsumBound
    _ = (|a n| + ∑ i ∈ Finset.range n, |a i - a (i + 1)|) /
          |Real.sin (Real.pi * t)| := by
      rw [div_eq_mul_inv, ← Finset.sum_mul]
      ring


noncomputable def S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (u k : ℂ) * E ((k : ℝ) * t)

lemma E_add (x y : ℝ) : E x * E y = E (x + y) := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma E_nat (m : ℕ) : E (m : ℝ) = 1 := by
  unfold E
  rw [show ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I =
      (m : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast
    ring]
  rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

lemma S_residue_decomp (n q : ℕ) (hq : 0 < q) (u : ℕ → ℝ) (t : ℝ) :
    S n u t =
      ∑ r ∈ Finset.range (min q (n + 1)),
        E ((r : ℝ) * t) *
          ∑ j ∈ Finset.range ((n - r) / q + 1),
            (u (r + j * q) : ℂ) * E (((j * q : ℕ) : ℝ) * t) := by
  classical
  rw [S]
  let s : Finset (Σ _ : ℕ, ℕ) :=
    (Finset.range (min q (n + 1))).sigma
      (fun r => Finset.range ((n - r) / q + 1))
  let f : (Σ _ : ℕ, ℕ) → ℂ := fun p =>
    (u (p.1 + p.2 * q) : ℂ) * E (((p.1 + p.2 * q : ℕ) : ℝ) * t)
  have hR : (∑ r ∈ Finset.range (min q (n + 1)),
        E ((r : ℝ) * t) *
          ∑ j ∈ Finset.range ((n - r) / q + 1),
            (u (r + j * q) : ℂ) * E (((j * q : ℕ) : ℝ) * t)) =
      ∑ p ∈ s, f p := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [f]
    have hE : E ((r : ℝ) * t) * E (((j * q : ℕ) : ℝ) * t) =
        E (((r + j * q : ℕ) : ℝ) * t) := by
      rw [E_add]
      congr 1
      push_cast
      ring
    calc
      E ((r : ℝ) * t) * ((u (r + j * q) : ℂ) * E (((j * q : ℕ) : ℝ) * t))
          = (u (r + j * q) : ℂ) *
              (E ((r : ℝ) * t) * E (((j * q : ℕ) : ℝ) * t)) := by ring
      _ = (u (r + j * q) : ℂ) * E (((r + j * q : ℕ) : ℝ) * t) := by rw [hE]
  rw [hR]
  symm
  refine Finset.sum_bij' (s := s) (t := Finset.range (n + 1))
    (fun p _ => p.1 + p.2 * q)
    (fun k _ => ⟨k % q, k / q⟩) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [s, Finset.mem_sigma, Finset.mem_range] at hp
    rcases hp with ⟨hrq, hrj⟩
    have hrmin : p.1 < min q (n + 1) := hrq
    have hrn : p.1 ≤ n := by
      have : p.1 < n + 1 := lt_of_lt_of_le hrmin (min_le_right _ _)
      omega
    have hj : p.2 ≤ (n - p.1) / q := by omega
    have hk : p.1 + p.2 * q ≤ n := by
      have h1 : p.2 * q ≤ ((n - p.1) / q) * q := Nat.mul_le_mul_right _ hj
      have h2 : ((n - p.1) / q) * q ≤ n - p.1 := Nat.div_mul_le_self _ _
      omega
    exact Finset.mem_range.mpr (by omega)
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [s, Finset.mem_sigma, Finset.mem_range]
    constructor
    · exact lt_min (Nat.mod_lt k hq) (lt_of_le_of_lt (Nat.mod_le k q) hk)
    · have hdecomp : k % q + q * (k / q) = k := Nat.mod_add_div k q
      have hk' : k ≤ n := by omega
      have hqk : q * (k / q) = k - k % q := by omega
      have hle : q * (k / q) ≤ n - k % q := by
        calc
          q * (k / q) = k - k % q := hqk
          _ ≤ n - k % q := Nat.sub_le_sub_right hk' _
      have hquot : k / q ≤ (n - k % q) / q := by
        rw [Nat.le_div_iff_mul_le hq]
        simpa [mul_comm] using hle
      rw [Nat.div_lt_iff_lt_mul hq]
      have hmodlt : k % q < q := Nat.mod_lt _ hq
      have hmul : q * (k / q) ≤ q * ((n - k % q) / q) :=
        Nat.mul_le_mul_left q hquot
      calc
        k = k % q + q * (k / q) := hdecomp.symm
        _ < q + q * ((n - k % q) / q) := by omega
        _ = ((n - k % q) / q + 1) * q := by ring
  · intro p hp
    simp only [s, Finset.mem_sigma, Finset.mem_range] at hp
    rcases hp with ⟨hrq, hrj⟩
    have hrlt : p.1 < q := lt_of_lt_of_le hrq (min_le_left _ _)
    cases p with
    | mk r j =>
      rw [Sigma.mk.injEq]
      constructor
      · rw [mul_comm j q, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt]
      · simp only [Sigma.mk.injEq]
        rw [mul_comm j q, Nat.add_mul_div_left _ _ hq]
        simp [Nat.div_eq_of_lt hrlt]
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only
    simpa [mul_comm] using Nat.mod_add_div k q
  · intro p hp
    rfl


namespace PEqualNP.Outside

noncomputable section

lemma norm_expSum_rational_le (n q : ℕ) (hq : 0 < q) (u : ℕ → ℝ)
    (a : ℕ) (β : ℝ) (hsin : Real.sin (Real.pi * ((q : ℝ) * β)) ≠ 0) :
    ‖S n u ((a : ℝ) / (q : ℝ) + β)‖ ≤
      ∑ r ∈ Finset.range (min q (n + 1)),
        ((|u (r + ((n - r) / q) * q)| +
            ∑ j ∈ Finset.range ((n - r) / q),
              |u (r + j * q) - u (r + (j + 1) * q)|) /
          |Real.sin (Real.pi * ((q : ℝ) * β))|) := by
  classical
  let Q := min q (n + 1)
  have hdec := S_residue_decomp n q hq u ((a : ℝ) / (q : ℝ) + β)
  rw [hdec]
  calc
    ‖∑ r ∈ Finset.range Q,
        E ((r : ℝ) * ((a : ℝ) / (q : ℝ) + β)) *
          ∑ j ∈ Finset.range ((n - r) / q + 1),
            (u (r + j * q) : ℂ) * E (((j * q : ℕ) : ℝ) *
              ((a : ℝ) / (q : ℝ) + β))‖
        ≤ ∑ r ∈ Finset.range Q,
            ‖E ((r : ℝ) * ((a : ℝ) / (q : ℝ) + β)) *
              ∑ j ∈ Finset.range ((n - r) / q + 1),
                (u (r + j * q) : ℂ) * E (((j * q : ℕ) : ℝ) *
                  ((a : ℝ) / (q : ℝ) + β))‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.range Q,
        ((|u (r + ((n - r) / q) * q)| +
            ∑ j ∈ Finset.range ((n - r) / q),
              |u (r + j * q) - u (r + (j + 1) * q)|) /
          |Real.sin (Real.pi * ((q : ℝ) * β))|) := by
      apply Finset.sum_le_sum
      intro r hr
      have hinner :
          (∑ j ∈ Finset.range ((n - r) / q + 1),
            (u (r + j * q) : ℂ) * E (((j * q : ℕ) : ℝ) *
              ((a : ℝ) / (q : ℝ) + β))) =
          ∑ j ∈ Finset.range ((n - r) / q + 1),
            (u (r + j * q) : ℂ) * E ((j : ℝ) * ((q : ℝ) * β)) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        rw [show (((j * q : ℕ) : ℝ) * ((a : ℝ) / (q : ℝ) + β)) =
            (j : ℝ) * (a : ℝ) + (j : ℝ) * ((q : ℝ) * β) by
          push_cast
          field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)]]
        have hja : E ((j : ℝ) * (a : ℝ)) = 1 := by
          simpa [Nat.cast_mul] using E_nat (j * a)
        rw [← E_add, hja, one_mul]
      have hphase : ‖E ((r : ℝ) * ((a : ℝ) / (q : ℝ) + β))‖ = 1 := by
        dsimp only [E]
        simpa only [mul_comm] using
          Complex.norm_exp_ofReal_mul_I (2 * Real.pi * ((r : ℝ) * ((a : ℝ) / (q : ℝ) + β)))
      rw [hinner]
      simpa [norm_mul, hphase] using
        (norm_weighted_geometric_sum_le ((n - r) / q)
          (fun j => u (r + j * q)) ((q : ℝ) * β) hsin)

end

end PEqualNP.Outside
