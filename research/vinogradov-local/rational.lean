import Mathlib
import finite_large_sieve
import separated_large_sieve
open scoped BigOperators
noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- The additive character `E (n/q)` is `ZMod.stdAddChar n`. -/
lemma E_eq_stdAddChar (q n : ℕ) [NeZero q] :
    E ((n : ℝ) / (q : ℝ)) = ZMod.stdAddChar (n : ZMod q) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  unfold E
  congr 1
  push_cast
  ring

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

/-- If every fiber of `g : ι → κ` over `s` has at most `C` elements, then a
sum of `G (g i)` is at most `C` times the total mass of `G`. -/
lemma sum_le_card_mul_sum_of_fiber_bound {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : Finset ι) (g : ι → κ) (G : κ → ℝ) (C : ℝ)
    (hG : ∀ k, 0 ≤ G k)
    (hcard : ∀ k, (((s.filter (fun i => g i = k)).card : ℝ) ≤ C)) :
    ∑ i ∈ s, G (g i) ≤ C * ∑ k, G k := by
  classical
  have hfiber : (∑ k : κ, ∑ i ∈ s.filter (fun i => g i = k), G (g i))
      = ∑ i ∈ s, G (g i) :=
    Finset.sum_fiberwise s g (fun i => G (g i))
  rw [← hfiber]
  have hcongr : ∀ k : κ,
      ∑ i ∈ s.filter (fun i => g i = k), G (g i) =
        ((s.filter (fun i => g i = k)).card : ℝ) * G k := by
    intro k
    rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
  calc
    ∑ k : κ, ∑ i ∈ s.filter (fun i => g i = k), G (g i)
        = ∑ k : κ, ((s.filter (fun i => g i = k)).card : ℝ) * G k := by
      apply Finset.sum_congr rfl
      intro k _
      exact hcongr k
    _ ≤ ∑ k : κ, C * G k := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (hcard k) (hG k)
    _ = C * ∑ k : κ, G k := by
      rw [Finset.mul_sum]

/-- Bridge from the separated large sieve's half phase to our full phase. -/
lemma sieveHalfPhase_two_mul (y : ℝ) :
    GoldbachBDHSharp.OAI.Ostmann.sieveHalfPhase (2 * y) = E y := by
  unfold GoldbachBDHSharp.OAI.Ostmann.sieveHalfPhase E
  congr 1
  push_cast
  ring

/-- Fixed-length energy bound for an arbitrary separated frequency set,
using the sharp separated additive large sieve.  This covers the `β ≠ 0`
major-arc perturbation, at the cost of a fixed coefficient length. -/
theorem separated_frequency_energy (D L : ℕ) (x : Fin (D + 1) → ℝ) (δ : ℝ)
    (hδ : 0 < δ)
    (hx : GoldbachBDHSharp.OAI.Ostmann.CircleSeparated x δ)
    (c : Fin (L + 1) → ℂ) :
    ∑ d : Fin (D + 1),
      ‖∑ n : Fin (L + 1), c n * E ((n : ℝ) * x d)‖ ^ 2
      ≤ ((L + 1 : ℝ) + 1 / δ) * ∑ n : Fin (L + 1), ‖c n‖ ^ 2 := by
  have h := GoldbachBDHSharp.OAI.Ostmann.separated_additive_sieve
    (x := x) (δ := δ) hδ hx (L + 1) 0 c
  have hLHS : (∑ d : Fin (D + 1),
      ‖∑ n : Fin (L + 1), c n * E ((n : ℝ) * x d)‖ ^ 2)
      = ∑ d : Fin (D + 1),
          ‖∑ n : Fin (L + 1),
            c n * GoldbachBDHSharp.OAI.Ostmann.sieveHalfPhase
              (2 * (0 + (n : ℝ)) * x d)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro d _
    have hinner : (∑ n : Fin (L + 1), c n * E ((n : ℝ) * x d))
        = ∑ n : Fin (L + 1),
            c n * GoldbachBDHSharp.OAI.Ostmann.sieveHalfPhase
              (2 * (0 + (n : ℝ)) * x d) := by
      apply Finset.sum_congr rfl
      intro n _
      have harg : 2 * (0 + (n : ℝ)) * x d = 2 * ((n : ℝ) * x d) := by ring
      rw [harg, sieveHalfPhase_two_mul]
    rw [hinner]
  rw [hLHS]
  have hfactor : ((L + 1 : ℕ) : ℝ) + 1 / δ = (L : ℝ) + 1 + 1 / δ := by
    push_cast
    ring
  rw [hfactor] at h
  exact h

/- Fixed-length frequency-energy form of the finite large sieve: for
`gcd(a,q) = 1`, summing the squared Fourier transforms at the frequencies
`d * a / q` over `d <= D` costs at most `(D/q + 1) (L + q)` times the
coefficient energy. -/
set_option maxHeartbeats 2000000 in
theorem largeSieve_frequency_energy (q D L : ℕ) [NeZero q] (a : ℕ) (c : ℕ → ℂ)
    (hcop : Nat.Coprime a q) :
    ∑ d ∈ Finset.range (D + 1),
      ‖∑ l ∈ Finset.range (L + 1),
        c l * E ((l : ℝ) * ((d : ℝ) * ((a : ℝ) / (q : ℝ))))‖ ^ 2
      ≤ ((D / q + 1 : ℕ) : ℝ) * ((L + q : ℝ) *
          ∑ l ∈ Finset.range (L + 1), ‖c l‖ ^ 2) := by
  classical
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime a hcop
  have hu : ((u : ZMod q)) = (a : ZMod q) := ZMod.coe_unitOfCoprime a hcop
  let G : ZMod q → ℝ := fun s =>
    ‖∑ l ∈ Finset.range (L + 1), c l * ZMod.stdAddChar (s * (l : ZMod q))‖ ^ 2
  have hterm : ∀ d ∈ Finset.range (D + 1),
      ‖∑ l ∈ Finset.range (L + 1),
        c l * E ((l : ℝ) * ((d : ℝ) * ((a : ℝ) / (q : ℝ))))‖ ^ 2
      = G ((d : ZMod q) * (a : ZMod q)) := by
    intro d _
    have hargh : ∀ l : ℕ,
        E ((l : ℝ) * ((d : ℝ) * ((a : ℝ) / (q : ℝ))))
        = ZMod.stdAddChar (((d : ZMod q) * (a : ZMod q)) * (l : ZMod q)) := by
      intro l
      have harg : (l : ℝ) * ((d : ℝ) * ((a : ℝ) / (q : ℝ))) =
          ((l * d * a : ℕ) : ℝ) / (q : ℝ) := by
        push_cast
        ring
      rw [harg, E_eq_stdAddChar]
      congr 1
      push_cast
      ring
    dsimp only [G]
    simp only [hargh]
  have hsum1 : (∑ d ∈ Finset.range (D + 1),
      ‖∑ l ∈ Finset.range (L + 1),
        c l * E ((l : ℝ) * ((d : ℝ) * ((a : ℝ) / (q : ℝ))))‖ ^ 2)
      = ∑ d ∈ Finset.range (D + 1), G ((d : ZMod q) * (a : ZMod q)) :=
    Finset.sum_congr rfl hterm
  rw [hsum1]
  have hcard : ∀ s : ZMod q,
      (((Finset.range (D + 1)).filter
        (fun d : ℕ => (d : ZMod q) * (a : ZMod q) = s)).card : ℝ) ≤
        ((D / q + 1 : ℕ) : ℝ) := by
    intro s
    have hset : (Finset.range (D + 1)).filter
        (fun d : ℕ => (d : ZMod q) * (a : ZMod q) = s)
        = (Finset.range (D + 1)).filter
            (fun d : ℕ => (d : ZMod q) = ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * s) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hd, hEq⟩
        refine ⟨hd, ?_⟩
        have hEq' : (d : ZMod q) * (u : ZMod q) = s := by
          simpa [hu] using hEq
        calc
          (d : ZMod q) =
              (d : ZMod q) * ((u : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
            rw [Units.mul_inv, mul_one]
          _ = ((d : ZMod q) * (u : ZMod q)) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) := by ring
          _ = s * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) := by rw [hEq']
          _ = ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * s := by ring
      · rintro ⟨hd, hEq⟩
        refine ⟨hd, ?_⟩
        calc
          (d : ZMod q) * (a : ZMod q) = (d : ZMod q) * (u : ZMod q) := by rw [← hu]
          _ = (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * s) * (u : ZMod q) := by rw [hEq]
          _ = s * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (u : ZMod q)) := by ring
          _ = s := by rw [Units.inv_mul, mul_one]
    rw [hset]
    exact_mod_cast PEqualNP.Outside.fiber_card_le D q (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * s)
  calc
    ∑ d ∈ Finset.range (D + 1), G ((d : ZMod q) * (a : ZMod q))
        ≤ ((D / q + 1 : ℕ) : ℝ) * ∑ s : ZMod q, G s :=
      sum_le_card_mul_sum_of_fiber_bound (s := Finset.range (D + 1))
        (g := fun d => (d : ZMod q) * (a : ZMod q)) (G := G)
        (C := ((D / q + 1 : ℕ) : ℝ)) (fun s => sq_nonneg _) hcard
    _ ≤ ((D / q + 1 : ℕ) : ℝ) *
          ((L + q : ℝ) * ∑ l ∈ Finset.range (L + 1), ‖c l‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [G] using PEqualNP.Outside.L_goldbach_finite_large_sieve L q c

/-- Reducing the numerator modulo `q` does not change the sine, up to sign. -/
lemma abs_sin_pi_mul_natCast_div_eq_mod (q A : ℕ) (hq : 0 < q) :
    |Real.sin (Real.pi * (A : ℝ) / (q : ℝ))| =
      |Real.sin (Real.pi * ((A % q : ℕ) : ℝ) / (q : ℝ))| := by
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hA : (q:ℝ) * ((A/q:ℕ):ℝ) + ((A%q:ℕ):ℝ) = (A:ℝ) := by
    rw [← Nat.cast_mul, ← Nat.cast_add, Nat.div_add_mod]
  have harg : Real.pi * (A:ℝ)/(q:ℝ) =
      Real.pi * (((A%q:ℕ):ℝ)/(q:ℝ)) + ((A/q:ℕ):ℝ) * Real.pi := by
    field_simp
    rw [← hA]
    ring
  have hargZ : Real.pi * (A:ℝ)/(q:ℝ) =
      Real.pi * (((A%q:ℕ):ℝ)/(q:ℝ)) + (((A/q:ℕ):ℤ):ℝ) * Real.pi := by
    rw [Int.cast_natCast]
    exact harg
  rw [hargZ, Real.sin_add_int_mul_pi, abs_mul]
  have h1 : |((-1:ℝ) ^ (((A/q:ℕ):ℤ)))| = 1 := by
    rw [abs_zpow]
    simp
  rw [h1, one_mul]
  have hphase : Real.pi * (((A % q : ℕ) : ℝ) / (q : ℝ)) =
      Real.pi * ((A % q : ℕ) : ℝ) / (q : ℝ) := by ring
  rw [hphase]

/-- A lower bound for `|sin (u + v)|` in terms of `|sin u|` and `|sin v|`. -/
lemma abs_sin_add_ge_sub (u v : ℝ) :
    |Real.sin u| - |Real.sin v| ≤ |Real.sin (u + v)| := by
  have h := Real.abs_sin_add_le (u + v) (-v)
  rw [show u + v + -v = u by ring, Real.sin_neg, abs_neg] at h
  linarith

/-- Jordan's inequality for the rational angle `pi * s / q` when `2 s <= q`. -/
private lemma sin_pi_mul_div_ge_of_two_mul_le (q s : ℕ) (hs1 : 1 ≤ s)
    (hsq : 2 * s ≤ q) :
    2 / (q : ℝ) ≤ Real.sin (Real.pi * (s : ℝ) / (q : ℝ)) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hs2q : (2 : ℝ) * (s : ℝ) ≤ (q : ℝ) := by exact_mod_cast hsq
  have hyhalf : Real.pi * (s : ℝ) / (q : ℝ) ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hqpos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_le_sin (x := Real.pi * (s : ℝ) / (q : ℝ))
    (by positivity) hyhalf
  have hval : (2 / Real.pi) * (Real.pi * (s : ℝ) / (q : ℝ)) =
      2 * (s : ℝ) / (q : ℝ) := by
    field_simp
  rw [hval] at hsin
  have hs2 : (2 : ℝ) / (q : ℝ) ≤ 2 * (s : ℝ) / (q : ℝ) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hqpos)
    have : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
    nlinarith
  exact hs2.trans hsin

/-- For a reduced fraction `r / q` with `1 <= r < q`, the sine is at least
`2 / q` in absolute value. -/
lemma abs_sin_pi_mul_div_ge (q r : ℕ) (hr1 : 1 ≤ r) (hrq : r < q) :
    2 / (q : ℝ) ≤ |Real.sin (Real.pi * (r : ℝ) / (q : ℝ))| := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := by omega
    exact_mod_cast this
  have h2q : (0 : ℝ) ≤ 2 / (q : ℝ) := div_nonneg (by norm_num) (le_of_lt hqpos)
  by_cases hhalf : 2 * r ≤ q
  · have h := sin_pi_mul_div_ge_of_two_mul_le q r hr1 hhalf
    rwa [abs_of_nonneg (le_trans h2q h)]
  · have hqr : r ≤ q := le_of_lt hrq
    have hs1 : 1 ≤ q - r := by omega
    have hsmall : 2 * (q - r) ≤ q := by omega
    have h := sin_pi_mul_div_ge_of_two_mul_le q (q - r) hs1 hsmall
    have hcast : ((q - r : ℕ) : ℝ) = (q : ℝ) - (r : ℝ) := Nat.cast_sub hqr
    have harg : Real.pi * (r : ℝ) / (q : ℝ) =
        Real.pi - Real.pi * ((q - r : ℕ) : ℝ) / (q : ℝ) := by
      rw [hcast]
      field_simp
      ring
    rw [harg, Real.sin_pi_sub]
    rwa [abs_of_nonneg (le_trans h2q h)]

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


/-- Geometric sum over the interval `{1, ..., M}` (with the `m = 0` term
removed). -/
lemma norm_geometric_sum_Icc_le (M : ℕ) (t : ℝ)
    (hsin : Real.sin (Real.pi * t) ≠ 0) :
    ‖∑ m ∈ Finset.Icc 1 M, E ((m : ℝ) * t)‖ ≤
      1 + 1 / |Real.sin (Real.pi * t)| := by
  have hrange : Finset.range (M + 1) = insert 0 (Finset.Icc 1 M) := by
    ext m
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hsplit : (∑ m ∈ Finset.range (M + 1), E ((m : ℝ) * t)) =
      1 + ∑ m ∈ Finset.Icc 1 M, E ((m : ℝ) * t) := by
    rw [hrange, Finset.sum_insert (by simp)]
    simp [E]
  have hgeom := norm_geometric_sum_le M t hsin
  rw [hsplit] at hgeom
  have hS : (∑ m ∈ Finset.Icc 1 M, E ((m : ℝ) * t)) =
      (1 + ∑ m ∈ Finset.Icc 1 M, E ((m : ℝ) * t)) - 1 := by ring
  rw [hS]
  calc
    ‖(1 + ∑ m ∈ Finset.Icc 1 M, E ((m : ℝ) * t)) - 1‖
        ≤ ‖1 + ∑ m ∈ Finset.Icc 1 M, E ((m : ℝ) * t)‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ 1 / |Real.sin (Real.pi * t)| + 1 := by
      exact add_le_add hgeom (by norm_num)
    _ = 1 + 1 / |Real.sin (Real.pi * t)| := by ring

/-- Crude form of the `Icc` geometric bound: at most `2 / |sin (π t)|`. -/
lemma norm_geometric_sum_Icc_le_two (M : ℕ) (t : ℝ)
    (hsin : Real.sin (Real.pi * t) ≠ 0) :
    ‖∑ m ∈ Finset.Icc 1 M, E ((m : ℝ) * t)‖ ≤
      2 / |Real.sin (Real.pi * t)| := by
  have h := norm_geometric_sum_Icc_le M t hsin
  have hs : 0 < |Real.sin (Real.pi * t)| := abs_pos.mpr hsin
  have hs1 : |Real.sin (Real.pi * t)| ≤ 1 := Real.abs_sin_le_one _
  have hone : (1 : ℝ) ≤ 1 / |Real.sin (Real.pi * t)| := by
    rw [le_div_iff₀ hs]
    simpa using hs1
  calc
    ‖∑ m ∈ Finset.Icc 1 M, E ((m : ℝ) * t)‖ ≤
        1 + 1 / |Real.sin (Real.pi * t)| := h
    _ ≤ 2 / |Real.sin (Real.pi * t)| := by
      rw [show (2 : ℝ) / |Real.sin (Real.pi * t)| =
        1 / |Real.sin (Real.pi * t)| + 1 / |Real.sin (Real.pi * t)| by ring]
      linarith

/-- The log-weighted Abel bound: the total variation of `log` telescopes, so the
weighted exponential sum is bounded by `2 log L / |sin (pi t)|`. -/
lemma norm_log_weighted_geometric_sum_le (L : ℕ) (t : ℝ)
    (hsin : Real.sin (Real.pi * t) ≠ 0) :
    ‖∑ l ∈ Finset.range (L + 1), (Real.log l : ℂ) * E ((l : ℝ) * t)‖ ≤
      2 * Real.log (L : ℝ) / |Real.sin (Real.pi * t)| := by
  have h := norm_weighted_geometric_sum_le L (fun l => Real.log l) t hsin
  have hlogL : |Real.log (L : ℝ)| = Real.log (L : ℝ) :=
    abs_of_nonneg (Real.log_natCast_nonneg L)
  have hterm : ∀ l ∈ Finset.range L,
      |Real.log (l : ℝ) - Real.log ((l + 1 : ℕ) : ℝ)| =
        Real.log ((l + 1 : ℕ) : ℝ) - Real.log (l : ℝ) := by
    intro l _
    have hle : Real.log (l : ℝ) ≤ Real.log ((l + 1 : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos l with h0 | hpos
      · subst l
        simp
      · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast Nat.le_succ l)
    rw [abs_sub_comm]
    exact abs_of_nonneg (sub_nonneg.mpr hle)
  have hvar : ∑ l ∈ Finset.range L,
      |Real.log (l : ℝ) - Real.log ((l + 1 : ℕ) : ℝ)| = Real.log (L : ℝ) := by
    calc
      ∑ l ∈ Finset.range L,
          |Real.log (l : ℝ) - Real.log ((l + 1 : ℕ) : ℝ)|
          = ∑ l ∈ Finset.range L,
              (Real.log ((l + 1 : ℕ) : ℝ) - Real.log (l : ℝ)) :=
        Finset.sum_congr rfl hterm
      _ = Real.log (L : ℝ) - Real.log ((0 : ℕ) : ℝ) :=
        Finset.sum_range_sub (fun n : ℕ => Real.log (n : ℝ)) L
      _ = Real.log (L : ℝ) := by simp
  rw [hvar, hlogL] at h
  simpa [two_mul] using h

/-- Major-arc sine separation: for `t = a/q + β` with `gcd(a,q) = 1`,
`1 <= d <= U < q` and `|β| <= 1/(16 q U)`, one has `|sin (π d t)| >= 1/q`. -/
lemma abs_sin_pi_mul_majorArc_ge (q U a : ℕ) (β : ℝ) (hq : 0 < q)
    (hcop : Nat.Coprime a q) (hU1 : 1 ≤ U) (hUq : U < q)
    (hβ : |β| ≤ 1 / (16 * (q:ℝ) * (U:ℝ))) :
    ∀ d ∈ Finset.Icc 1 U,
      (1:ℝ)/(q:ℝ) ≤
        |Real.sin (Real.pi * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)))| := by
  intro d hd
  obtain ⟨hd1, hdU⟩ := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := hd1
  have hdltq : d < q := lt_of_le_of_lt hdU hUq
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hqne : (q:ℝ) ≠ 0 := hqR.ne'
  have hUpos : (0:ℝ) < (U:ℝ) := by exact_mod_cast hU1
  have hUne : (U:ℝ) ≠ 0 := hUpos.ne'
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hdpos
  set A : ℕ := d * a with hAdef
  have hmodne : A % q ≠ 0 := by
    intro h0
    have hdvd : q ∣ A := Nat.dvd_of_mod_eq_zero h0
    have hdvd' : q ∣ d * a := by simpa [hAdef] using hdvd
    have hqd : q ∣ d := hcop.symm.dvd_of_dvd_mul_right hdvd'
    have := Nat.le_of_dvd hdpos hqd
    omega
  have hmodlt : A % q < q := Nat.mod_lt A hq
  have hmod1 : 1 ≤ A % q := by omega
  have hrat0 := abs_sin_pi_mul_div_ge q (A % q) hmod1 hmodlt
  have hred := abs_sin_pi_mul_natCast_div_eq_mod q A hq
  have hAeq : Real.pi * (d:ℝ) * ((a:ℝ)/(q:ℝ)) = Real.pi * (A:ℝ)/(q:ℝ) := by
    rw [hAdef]
    push_cast
    ring
  have hrat : (2:ℝ)/(q:ℝ) ≤
      |Real.sin (Real.pi * (d:ℝ) * ((a:ℝ)/(q:ℝ)))| := by
    rw [hAeq, hred]
    exact hrat0
  have ht : Real.pi * ((d:ℝ) * ((a:ℝ)/(q:ℝ) + β)) =
      Real.pi * (d:ℝ) * ((a:ℝ)/(q:ℝ)) + Real.pi * (d:ℝ) * β := by ring
  rw [ht]
  have hsmallU : (U:ℝ) * |β| ≤ 1/(16*(q:ℝ)) := by
    calc
      (U:ℝ) * |β| ≤ (U:ℝ) * (1/(16*(q:ℝ)*(U:ℝ))) :=
        mul_le_mul_of_nonneg_left hβ hUpos.le
      _ = 1/(16*(q:ℝ)) := by
        field_simp
  have hsmalld : (d:ℝ) * |β| ≤ 1/(16*(q:ℝ)) := by
    have hdU' : (d:ℝ) ≤ (U:ℝ) := by exact_mod_cast hdU
    exact (mul_le_mul_of_nonneg_right hdU' (abs_nonneg β)).trans hsmallU
  have hv : |Real.sin (Real.pi * (d:ℝ) * β)| ≤ 1/(4*(q:ℝ)) := by
    have h1 : |Real.sin (Real.pi * (d:ℝ) * β)| ≤ |Real.pi * (d:ℝ) * β| :=
      Real.abs_sin_le_abs
    have h2 : |Real.pi * (d:ℝ) * β| = Real.pi * ((d:ℝ) * |β|) := by
      rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hdR]
      ring
    calc
      |Real.sin (Real.pi * (d:ℝ) * β)| ≤ |Real.pi * (d:ℝ) * β| := h1
      _ = Real.pi * ((d:ℝ) * |β|) := h2
      _ ≤ Real.pi * (1/(16*(q:ℝ))) :=
        mul_le_mul_of_nonneg_left hsmalld Real.pi_pos.le
      _ ≤ 1/(4*(q:ℝ)) := by
        rw [show Real.pi * (1/(16*(q:ℝ))) = Real.pi/(16*(q:ℝ)) by ring]
        rw [show (1:ℝ)/(4*(q:ℝ)) = 4/(16*(q:ℝ)) by field_simp; ring]
        rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 16*(q:ℝ))]
        exact le_of_lt Real.pi_lt_four
  have hlow := abs_sin_add_ge_sub
    (Real.pi * (d:ℝ) * ((a:ℝ)/(q:ℝ))) (Real.pi * (d:ℝ) * β)
  have hone : (1:ℝ)/(q:ℝ) ≤
      |Real.sin (Real.pi * (d:ℝ) * ((a:ℝ)/(q:ℝ)))| -
        |Real.sin (Real.pi * (d:ℝ) * β)| := by
    have hnum : (2:ℝ)/(q:ℝ) - 1/(4*(q:ℝ)) = 7/(4*(q:ℝ)) := by
      field_simp
      ring
    have htarget : (1:ℝ)/(q:ℝ) ≤ (2:ℝ)/(q:ℝ) - 1/(4*(q:ℝ)) := by
      rw [hnum]
      rw [show (1:ℝ)/(q:ℝ) = 4/(4*(q:ℝ)) by field_simp]
      rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 4*(q:ℝ))]
      norm_num
    linarith
  linarith

/-- Log-weighted geometric sum over the interval `{1, ..., N}`. -/
lemma norm_log_weighted_geometric_sum_Icc_le (N : ℕ) (t : ℝ)
    (hsin : Real.sin (Real.pi * t) ≠ 0) :
    ‖∑ l ∈ Finset.Icc 1 N, (Real.log l : ℂ) * E ((l : ℝ) * t)‖ ≤
      2 * Real.log (N : ℝ) / |Real.sin (Real.pi * t)| := by
  have hrange : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext l
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hdrop : (∑ l ∈ Finset.range (N + 1), (Real.log l : ℂ) * E ((l : ℝ) * t)) =
      ∑ l ∈ Finset.Icc 1 N, (Real.log l : ℂ) * E ((l : ℝ) * t) := by
    rw [hrange, Finset.sum_insert (by simp)]
    simp
  rw [← hdrop]
  exact norm_log_weighted_geometric_sum_le N t hsin

/-- The Type-I bilinear exponential sum with logarithmic weights is bounded by
the sum of the per-residue weighted Abel bounds. -/
lemma norm_type1_bilinear_log_le (n U : ℕ) (a : ℕ → ℝ) (t : ℝ)
    (hsin : ∀ d ∈ Finset.Icc 1 U, Real.sin (Real.pi * ((d : ℝ) * t)) ≠ 0) :
    ‖∑ d ∈ Finset.Icc 1 U, (a d : ℂ) *
        ∑ l ∈ Finset.Icc 1 (n / d),
          (Real.log l : ℂ) * E (((d * l : ℕ) : ℝ) * t)‖ ≤
      ∑ d ∈ Finset.Icc 1 U, |a d| *
        (2 * Real.log ((n / d : ℕ) : ℝ) /
          |Real.sin (Real.pi * ((d : ℝ) * t))|) := by
  calc
    ‖∑ d ∈ Finset.Icc 1 U, (a d : ℂ) *
        ∑ l ∈ Finset.Icc 1 (n / d),
          (Real.log l : ℂ) * E (((d * l : ℕ) : ℝ) * t)‖
        ≤ ∑ d ∈ Finset.Icc 1 U,
            ‖(a d : ℂ) * ∑ l ∈ Finset.Icc 1 (n / d),
              (Real.log l : ℂ) * E (((d * l : ℕ) : ℝ) * t)‖ :=
      norm_sum_le _ _
    _ = ∑ d ∈ Finset.Icc 1 U, |a d| *
          ‖∑ l ∈ Finset.Icc 1 (n / d),
            (Real.log l : ℂ) * E (((d * l : ℕ) : ℝ) * t)‖ := by
      apply Finset.sum_congr rfl
      intro d _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ d ∈ Finset.Icc 1 U, |a d| *
          (2 * Real.log ((n / d : ℕ) : ℝ) /
            |Real.sin (Real.pi * ((d : ℝ) * t))|) := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hphase : (∑ l ∈ Finset.Icc 1 (n / d),
            (Real.log l : ℂ) * E (((d * l : ℕ) : ℝ) * t)) =
          ∑ l ∈ Finset.Icc 1 (n / d),
            (Real.log l : ℂ) * E ((l : ℝ) * ((d : ℝ) * t)) := by
        apply Finset.sum_congr rfl
        intro l _
        have hargh : ((d * l : ℕ) : ℝ) * t = (l : ℝ) * ((d : ℝ) * t) := by
          push_cast
          ring
        rw [hargh]
      rw [hphase]
      exact norm_log_weighted_geometric_sum_Icc_le (n / d) ((d : ℝ) * t) (hsin d hd)

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
