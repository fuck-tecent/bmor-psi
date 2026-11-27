import Mathlib

namespace BeaumontCountBridge

def Window30Bound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
    ∀ a : ℕ, a < 30 → a.Coprime 30 →
    ∀ l u : ℕ, X ≤ 4*l → l ≤ u → u ≤ 2*X →
    (((Finset.Icc l u).filter (fun p : ℕ => p.Prime ∧ p % 30 = a)).card : ℝ) ≤
      (((u : ℝ) - (l : ℝ) + 1) / (8 * Real.log (X : ℝ))) +
        ε * ((X : ℝ) / Real.log (X : ℝ))

private def piMod30 (a n : ℕ) : ℕ :=
  ((Finset.Ioc 0 n).filter (fun p : ℕ => p.Prime ∧ p ≡ a [MOD 30])).card

private lemma totient_30 : Nat.totient 30 = 8 := by
  have h30 : (30 : ℕ) = 2 * 15 := by norm_num
  have h15 : (15 : ℕ) = 3 * 5 := by norm_num
  rw [h30, Nat.totient_mul (by decide), h15, Nat.totient_mul (by decide),
    Nat.totient_prime Nat.prime_two, Nat.totient_prime Nat.prime_three,
    Nat.totient_prime (by decide)]

private lemma card_Icc_eq_sub_piMod30 {a l u : ℕ} (ha_lt : a < 30) (hl : 1 ≤ l) (hlu : l ≤ u) :
    (((Finset.Icc l u).filter (fun p : ℕ => p.Prime ∧ p % 30 = a)).card : ℝ) =
      (piMod30 a u : ℝ) - (piMod30 a (l - 1) : ℝ) := by
  have hfilt :
      (Finset.Icc l u).filter (fun p : ℕ => p.Prime ∧ p % 30 = a) =
        (Finset.Icc l u).filter (fun p : ℕ => p.Prime ∧ p ≡ a [MOD 30]) := by
    ext p
    simp [Nat.ModEq, Nat.mod_eq_of_lt ha_lt]
  rw [hfilt]
  have hdisj : Disjoint (Finset.Ioc 0 (l - 1)) (Finset.Icc l u) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hp1 hp2
    omega
  have hunion : Finset.Ioc 0 (l - 1) ∪ Finset.Icc l u = Finset.Ioc 0 u := by
    ext p
    simp only [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hcard :
      ((Finset.Ioc 0 (l - 1)).filter (fun p : ℕ => p.Prime ∧ p ≡ a [MOD 30])).card +
        ((Finset.Icc l u).filter (fun p : ℕ => p.Prime ∧ p ≡ a [MOD 30])).card =
        ((Finset.Ioc 0 u).filter (fun p : ℕ => p.Prime ∧ p ≡ a [MOD 30])).card := by
    rw [← Finset.card_union_of_disjoint
          (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
        ← Finset.filter_union, hunion]
  have hcard_real :
      (piMod30 a (l - 1) : ℝ) +
        (((Finset.Icc l u).filter (fun p : ℕ => p.Prime ∧ p ≡ a [MOD 30])).card : ℝ) =
        (piMod30 a u : ℝ) := by
    unfold piMod30
    exact_mod_cast hcard
  linarith

private lemma approx_uniform_of_coprime (a : ℕ) (ha : a.Coprime 30) (δ : ℝ) (hδ : 0 < δ) :
    ∃ X₁ : ℕ, ∀ X : ℕ, X₁ ≤ X →
      ∀ t : ℕ, X ≤ 5 * t → t ≤ 2 * X →
        |(piMod30 a t : ℝ) - (t : ℝ) / (8 * Real.log (X : ℝ))| ≤
          δ * ((X : ℝ) / Real.log (X : ℝ)) := by
  have h_lim : Filter.Tendsto
      (fun x : ℝ => (piMod30 a ⌊x⌋₊ : ℝ) * Real.log x / x)
      Filter.atTop (nhds ((8 : ℝ)⁻¹)) := by
    have h0 : Filter.Tendsto
        (fun x : ℝ => (piMod30 a ⌊x⌋₊ : ℝ) * Real.log x / x)
        Filter.atTop (nhds ((Nat.totient 30 : ℝ)⁻¹)) :=
      Nat.tendsto_card_prime_modEq_mul_log_div_atTop (q := 30) ha
    simpa [totient_30] using h0
  obtain ⟨R, hR⟩ := Metric.tendsto_atTop.mp h_lim (δ / 8) (by positivity)
  refine ⟨max 25 (max (Nat.ceil (5 * R)) (Nat.ceil (Real.exp (Real.log 5 / δ)))), ?_⟩
  intro X hX t h5t ht2X
  have hX25 : 25 ≤ X := le_trans (le_max_left _ _) hX
  have hX_R : Nat.ceil (5 * R) ≤ X :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
  have hX_exp : Nat.ceil (Real.exp (Real.log 5 / δ)) ≤ X :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have ht5 : 5 ≤ t := by omega
  have hX25_real : (25 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX25
  have hX_pos : (0 : ℝ) < (X : ℝ) := by linarith
  have ht5_real : (5 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht5
  have ht_pos : (0 : ℝ) < (t : ℝ) := by linarith
  have ht_le : (t : ℝ) ≤ 2 * (X : ℝ) := by exact_mod_cast ht2X
  have hX_le_5t : (X : ℝ) ≤ 5 * (t : ℝ) := by exact_mod_cast h5t
  have hlog5_pos : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hlog25 : Real.log (25 : ℝ) = 2 * Real.log 5 := by
    have h25 : (25 : ℝ) = (5 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h25, Real.log_pow]
    norm_num
  have hlogX_ge : 2 * Real.log 5 ≤ Real.log (X : ℝ) := by
    rw [← hlog25]
    exact Real.log_le_log (by norm_num) hX25_real
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
  have hlogt_ge : Real.log (X : ℝ) - Real.log 5 ≤ Real.log (t : ℝ) := by
    have hdiv : (X : ℝ) / 5 ≤ (t : ℝ) := by linarith
    have h := Real.log_le_log (by linarith : (0 : ℝ) < (X : ℝ) / 5) hdiv
    rwa [Real.log_div (ne_of_gt hX_pos) (by norm_num)] at h
  have hlogt_half : Real.log (X : ℝ) / 2 ≤ Real.log (t : ℝ) := by linarith
  have hlogt_pos : 0 < Real.log (t : ℝ) := by linarith
  have hlogt_le : Real.log (t : ℝ) ≤ Real.log (X : ℝ) + Real.log 5 := by
    have h1 := Real.log_le_log ht_pos ht_le
    rw [Real.log_mul (by norm_num) (ne_of_gt hX_pos)] at h1
    have h2 : Real.log 2 ≤ Real.log 5 := Real.log_le_log (by norm_num) (by norm_num)
    linarith
  have h_log_diff : |Real.log (X : ℝ) - Real.log (t : ℝ)| ≤ Real.log 5 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have ht_ge_R : R ≤ (t : ℝ) := by
    have h5R : 5 * R ≤ (X : ℝ) := le_trans (Nat.le_ceil (5 * R)) (by exact_mod_cast hX_R)
    linarith
  have h_dist := hR (t : ℝ) ht_ge_R
  rw [Real.dist_eq, Nat.floor_natCast] at h_dist
  have hX_ge_exp : Real.exp (Real.log 5 / δ) ≤ (X : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hX_exp)
  have hlog_ge_div : Real.log 5 / δ ≤ Real.log (X : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (Real.log 5 / δ)) hX_ge_exp
    rwa [Real.log_exp] at h
  have hlog5_le_δlogX : Real.log 5 ≤ δ * Real.log (X : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlog_ge_div (le_of_lt hδ)
    have hmul : δ * (Real.log 5 / δ) = Real.log 5 := by
      field_simp <;> ring
    rwa [hmul] at h
  have h_eq1 :
      (piMod30 a t : ℝ) - (t : ℝ) / (8 * Real.log (t : ℝ)) =
        ((t : ℝ) / Real.log (t : ℝ)) *
          ((piMod30 a t : ℝ) * Real.log (t : ℝ) / (t : ℝ) - (8 : ℝ)⁻¹) := by
    field_simp <;> ring
  have h_ratio : (t : ℝ) / Real.log (t : ℝ) ≤ 4 * ((X : ℝ) / Real.log (X : ℝ)) := by
    apply le_of_mul_le_mul_right _ (mul_pos hlogt_pos hlogX_pos)
    have hL :
        (t : ℝ) / Real.log (t : ℝ) * (Real.log (t : ℝ) * Real.log (X : ℝ)) =
          (t : ℝ) * Real.log (X : ℝ) := by
      field_simp <;> ring
    have hR' :
        4 * ((X : ℝ) / Real.log (X : ℝ)) * (Real.log (t : ℝ) * Real.log (X : ℝ)) =
          4 * (X : ℝ) * Real.log (t : ℝ) := by
      field_simp <;> ring
    rw [hL, hR']
    calc (t : ℝ) * Real.log (X : ℝ)
        ≤ (2 * (X : ℝ)) * Real.log (X : ℝ) :=
          mul_le_mul_of_nonneg_right ht_le (le_of_lt hlogX_pos)
      _ = (4 * (X : ℝ)) * (Real.log (X : ℝ) / 2) := by ring
      _ ≤ (4 * (X : ℝ)) * Real.log (t : ℝ) :=
          mul_le_mul_of_nonneg_left hlogt_half (by positivity)
  have h_term1 :
      |(piMod30 a t : ℝ) - (t : ℝ) / (8 * Real.log (t : ℝ))| ≤
        (δ / 2) * ((X : ℝ) / Real.log (X : ℝ)) := by
    rw [h_eq1, abs_mul, abs_of_pos (div_pos ht_pos hlogt_pos)]
    calc ((t : ℝ) / Real.log (t : ℝ)) *
            |(piMod30 a t : ℝ) * Real.log (t : ℝ) / (t : ℝ) - (8 : ℝ)⁻¹|
        ≤ ((t : ℝ) / Real.log (t : ℝ)) * (δ / 8) :=
          mul_le_mul_of_nonneg_left (le_of_lt h_dist) (le_of_lt (div_pos ht_pos hlogt_pos))
      _ ≤ (4 * ((X : ℝ) / Real.log (X : ℝ))) * (δ / 8) :=
          mul_le_mul_of_nonneg_right h_ratio (by positivity)
      _ = (δ / 2) * ((X : ℝ) / Real.log (X : ℝ)) := by ring
  have h_eq2 :
      (t : ℝ) / (8 * Real.log (t : ℝ)) - (t : ℝ) / (8 * Real.log (X : ℝ)) =
        ((t : ℝ) / (8 * Real.log (t : ℝ) * Real.log (X : ℝ))) *
          (Real.log (X : ℝ) - Real.log (t : ℝ)) := by
    field_simp <;> ring
  have h_term2 :
      |(t : ℝ) / (8 * Real.log (t : ℝ)) - (t : ℝ) / (8 * Real.log (X : ℝ))| ≤
        (δ / 2) * ((X : ℝ) / Real.log (X : ℝ)) := by
    rw [h_eq2, abs_mul, abs_of_pos (by positivity)]
    have h_step1 :
        ((t : ℝ) / (8 * Real.log (t : ℝ) * Real.log (X : ℝ))) *
            |Real.log (X : ℝ) - Real.log (t : ℝ)| ≤
          ((t : ℝ) / (8 * Real.log (t : ℝ) * Real.log (X : ℝ))) * Real.log 5 :=
      mul_le_mul_of_nonneg_left h_log_diff (by positivity)
    refine le_trans h_step1 ?_
    apply le_of_mul_le_mul_right _
      (show (0 : ℝ) < 8 * Real.log (t : ℝ) * Real.log (X : ℝ) by positivity)
    have hL :
        ((t : ℝ) / (8 * Real.log (t : ℝ) * Real.log (X : ℝ))) * Real.log 5 *
            (8 * Real.log (t : ℝ) * Real.log (X : ℝ)) =
          (t : ℝ) * Real.log 5 := by
      field_simp <;> ring
    have hR' :
        (δ / 2) * ((X : ℝ) / Real.log (X : ℝ)) * (8 * Real.log (t : ℝ) * Real.log (X : ℝ)) =
          4 * δ * (X : ℝ) * Real.log (t : ℝ) := by
      field_simp <;> ring
    rw [hL, hR']
    calc (t : ℝ) * Real.log 5
        ≤ (2 * (X : ℝ)) * Real.log 5 :=
          mul_le_mul_of_nonneg_right ht_le (le_of_lt hlog5_pos)
      _ ≤ (2 * (X : ℝ)) * (δ * Real.log (X : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog5_le_δlogX (by positivity)
      _ = (2 * δ * (X : ℝ)) * Real.log (X : ℝ) := by ring
      _ ≤ (2 * δ * (X : ℝ)) * (2 * Real.log (t : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 * δ * (X : ℝ) * Real.log (t : ℝ) := by ring
  have h_split :
      (piMod30 a t : ℝ) - (t : ℝ) / (8 * Real.log (X : ℝ)) =
        ((piMod30 a t : ℝ) - (t : ℝ) / (8 * Real.log (t : ℝ))) +
          ((t : ℝ) / (8 * Real.log (t : ℝ)) - (t : ℝ) / (8 * Real.log (X : ℝ))) := by
    ring
  rw [h_split]
  calc |((piMod30 a t : ℝ) - (t : ℝ) / (8 * Real.log (t : ℝ))) +
          ((t : ℝ) / (8 * Real.log (t : ℝ)) - (t : ℝ) / (8 * Real.log (X : ℝ)))|
      ≤ |(piMod30 a t : ℝ) - (t : ℝ) / (8 * Real.log (t : ℝ))| +
          |(t : ℝ) / (8 * Real.log (t : ℝ)) - (t : ℝ) / (8 * Real.log (X : ℝ))| :=
        abs_add_le _ _
    _ ≤ (δ / 2) * ((X : ℝ) / Real.log (X : ℝ)) + (δ / 2) * ((X : ℝ) / Real.log (X : ℝ)) := add_le_add h_term1 h_term2
    _ = δ * ((X : ℝ) / Real.log (X : ℝ)) := by ring

theorem window30Bound : Window30Bound := by
  intro ε hε
  let f : Fin 30 → ℕ := fun i =>
    if hi : i.1.Coprime 30 then
      Classical.choose (approx_uniform_of_coprime i.1 hi (ε / 2) (half_pos hε))
    else 0
  refine ⟨max 20 (Finset.univ.sup f), ?_⟩
  intro X hX a ha_lt ha_cop l u hXl hlu huX
  have hX20 : 20 ≤ X := le_trans (le_max_left _ _) hX
  have hl1 : 1 ≤ l := by omega
  have h5u : X ≤ 5 * u := by omega
  have h5lm1 : X ≤ 5 * (l - 1) := by omega
  have hlm1_le : l - 1 ≤ 2 * X := by omega
  have hXf : f ⟨a, ha_lt⟩ ≤ X :=
    le_trans (Finset.le_sup (f := f) (Finset.mem_univ (⟨a, ha_lt⟩ : Fin 30)))
      (le_trans (le_max_right _ _) hX)
  have hX_a :
      Classical.choose (approx_uniform_of_coprime a ha_cop (ε / 2) (half_pos hε)) ≤ X := by
    dsimp only [f] at hXf
    rw [dif_pos ha_cop] at hXf
    exact hXf
  have hspec :=
    Classical.choose_spec (approx_uniform_of_coprime a ha_cop (ε / 2) (half_pos hε)) X hX_a
  have hu_err := hspec u h5u huX
  have hlm1_err := hspec (l - 1) h5lm1 hlm1_le
  have hu_up :
      (piMod30 a u : ℝ) - (u : ℝ) / (8 * Real.log (X : ℝ)) ≤
        (ε / 2) * ((X : ℝ) / Real.log (X : ℝ)) :=
    (abs_le.mp hu_err).2
  have hlm1_lo :
      -((ε / 2) * ((X : ℝ) / Real.log (X : ℝ))) ≤
        (piMod30 a (l - 1) : ℝ) - ((l - 1 : ℕ) : ℝ) / (8 * Real.log (X : ℝ)) :=
    (abs_le.mp hlm1_err).1
  have hcast_lm1 : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
    rw [Nat.cast_sub hl1, Nat.cast_one]
  rw [hcast_lm1] at hlm1_lo
  rw [card_Icc_eq_sub_piMod30 ha_lt hl1 hlu]
  have h_main :
      (u : ℝ) / (8 * Real.log (X : ℝ)) - ((l : ℝ) - 1) / (8 * Real.log (X : ℝ)) =
        ((u : ℝ) - (l : ℝ) + 1) / (8 * Real.log (X : ℝ)) := by
    ring
  linarith

end BeaumontCountBridge

/-!
# Beaumont Frozen Refutation: Finite Counting Assembly

Assembles the full refutation of the frozen Beaumont central-prediction statement from
the analytic interface `BeaumontCountBridge.Window30Bound`.

## Provenance
The finite modular arithmetic and interval-covering lemmas in
`BeaumontCentralPredictionArithmetic` are adapted from Apache-2.0 project PR #3724,
commit `ec2fc2fe`.
-/

namespace BeaumontCentralPredictionArithmetic

/-- Reduced residues modulo 30, with the first coordinate of the ordered pair first. -/
def units30 : List Nat := [1, 7, 11, 13, 17, 19, 23, 29]

def pairsAt (target : Nat) : List (Nat × Nat) :=
  (units30.flatMap fun a => units30.map fun b => (a, b)).filter
    fun (a, b) => (a + b) % 30 == target

theorem classes26 : pairsAt 26 = [(7, 19), (13, 13), (19, 7)] := by decide
theorem classes28 : pairsAt 28 = [(11, 17), (17, 11), (29, 29)] := by decide

/-- Check that these eight classes are exactly the possible reduced residues. -/
theorem units_complete :
    (List.range 30).filter (fun a => Nat.gcd a 30 == 1) = units30 := by decide

theorem residue_mem {p : Nat} (hp : Nat.gcd p 30 = 1) : p % 30 ∈ units30 := by
  rw [← units_complete, List.mem_filter]
  refine ⟨List.mem_range.mpr (Nat.mod_lt _ (by decide)), ?_⟩
  have h := Nat.gcd_rec 30 p
  rw [Nat.gcd_comm 30 p, hp] at h
  simp [h.symm]

/-- A represented target restricts the ordered pair to its enumerated list. -/
theorem represented_mem {p q s : Nat} (hp : Nat.gcd p 30 = 1)
    (hq : Nat.gcd q 30 = 1) (hs : p + q = s) :
    (p % 30, q % 30) ∈ pairsAt (s % 30) := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_flatMap.mpr ⟨p % 30, residue_mem hp,
      List.mem_map.mpr ⟨q % 30, residue_mem hq, rfl⟩⟩, ?_⟩
  change ((p % 30 + q % 30) % 30 == s % 30) = true
  rw [← Nat.add_mod, hs]
  simp

/-- The p interval uses a ceiling at its lower end and a floor at its upper end. -/
def lowerP (X s : Nat) := (X + s + 2) / 3
def upperP (X s : Nat) := 2 * ((65 * X) / 64 + s) / 3

theorem central_cover {X n p q s : Nat} (hlo : X ≤ n)
    (hhi : n ≤ (65 * X) / 64) (hadd : p + q = n + s)
    (hc₁ : n + s ≤ 3 * p) (hc₂ : 3 * p ≤ 2 * (n + s)) :
    lowerP X s ≤ p ∧ p ≤ upperP X s ∧
      X + s - p ≤ q ∧ q ≤ (65 * X) / 64 + s - p := by
  unfold lowerP upperP
  omega

/-- Uniformity interval [X/4, 2X] for the four endpoints of both shifts. -/
theorem endpoints_in_range {X p s : Nat} (hX : 24 ≤ X) (hs : s = 0 ∨ s = 2)
    (hlo : lowerP X s ≤ p) (hhi : p ≤ upperP X s) :
    X ≤ 4 * lowerP X s ∧ upperP X s ≤ 2 * X ∧
      X ≤ 4 * (X + s - p) ∧ (65 * X) / 64 + s - p ≤ 2 * X := by
  unfold lowerP upperP at *
  omega

/-- 192 times the integral p width is bounded by 66X + 64s; the q width is X / 64. -/
theorem interval_widths {X p s : Nat}
    (hhi : p ≤ upperP X s) :
    192 * (upperP X s - lowerP X s) ≤ 66 * X + 64 * s ∧
      ((65 * X) / 64 + s - p) - (X + s - p) = X / 64 := by
  unfold lowerP upperP at *
  omega

theorem lowerP_le_upperP {X s : Nat} (hX : 24 ≤ X) (hs : s = 0 ∨ s = 2) :
    lowerP X s ≤ upperP X s := by
  unfold lowerP upperP
  omega

end BeaumontCentralPredictionArithmetic

section BeaumontFiniteAssembly

open BeaumontCentralPredictionArithmetic

private def H_set (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter
    (fun p => p.Prime ∧ p ≤ n ∧ (n - p).Prime ∧ n ≤ 3 * p ∧ 3 * p ≤ 2 * n)

private def H_fn (n : ℕ) : ℕ :=
  (H_set n).card

private def E_set (X : ℕ) : Finset ℕ :=
  (Finset.Icc X (2 * X)).filter (fun n => Even n)

private noncomputable def M_fn (X : ℕ) : ℝ :=
  (X : ℝ) / (Real.log (X : ℝ)) ^ 2

private def R_fn (n : ℕ) : ℝ :=
  ((H_fn n + H_fn (n + 2)) : ℝ)

private def A_set (K : ℕ) : Finset ℕ :=
  (Finset.range K).image (fun j => 1920 * K + 26 + 30 * j)

private def classList (s : ℕ) : Finset (ℕ × ℕ) :=
  if s = 0 then {(7, 19), (13, 13), (19, 7)}
  else {(11, 17), (17, 11), (29, 29)}

private def P_set (X s a : ℕ) : Finset ℕ :=
  (Finset.Icc (lowerP X s) (upperP X s)).filter (fun p => p.Prime ∧ p % 30 = a)

private def Q_set (X s p b : ℕ) : Finset ℕ :=
  (Finset.Icc (X + s - p) (65 * X / 64 + s - p)).filter (fun q => q.Prime ∧ q % 30 = b)

private def pairSet (X s a b : ℕ) : Finset (ℕ × ℕ) :=
  (P_set X s a).biUnion (fun p => (Q_set X s p b).image (fun q => (p, q)))

private lemma prime_coprime_30 {p : ℕ} (hp : p.Prime) (h5 : 5 < p) : p.Coprime 30 := by
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  have h30 : p ∣ 2 * (3 * 5) := hdvd
  rcases hp.dvd_mul.mp h30 with h2 | h15
  · have := Nat.le_of_dvd (by decide) h2
    omega
  · rcases hp.dvd_mul.mp h15 with h3 | h5'
    · have := Nat.le_of_dvd (by decide) h3
      omega
    · have := Nat.le_of_dvd (by decide) h5'
      omega

private lemma A_set_card (K : ℕ) : (A_set K).card = K := by
  unfold A_set
  rw [Finset.card_image_of_injective]
  · exact Finset.card_range K
  · intro u v h
    dsimp at h
    omega

private lemma A_set_mem_props {K n : ℕ} (hn : n ∈ A_set K) :
    1920 * K ≤ n ∧ n ≤ 65 * (1920 * K) / 64 ∧ n ≤ 2 * (1920 * K) ∧ Even n ∧ n % 30 = 26 := by
  rcases Finset.mem_image.mp hn with ⟨j, hj, rfl⟩
  have hjlt : j < K := Finset.mem_range.mp hj
  refine ⟨by omega, by omega, by omega, ?_, by omega⟩
  exact ⟨960 * K + 13 + 15 * j, by omega⟩

private lemma A_set_subset_E (K : ℕ) : A_set K ⊆ E_set (1920 * K) := by
  intro n hn
  rcases A_set_mem_props hn with ⟨hlo, _, hhi, heven, _⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, hhi⟩, heven⟩

private lemma classList_card {s : ℕ} (hs : s = 0 ∨ s = 2) : (classList s).card = 3 := by
  rcases hs with rfl | rfl <;> decide

private lemma classList_coprime {s a b : ℕ} (hs : s = 0 ∨ s = 2)
    (hab : (a, b) ∈ classList s) :
    a < 30 ∧ a.Coprime 30 ∧ b < 30 ∧ b.Coprime 30 := by
  rcases hs with rfl | rfl
  · have h : ∀ ab ∈ classList 0, ab.1 < 30 ∧ ab.1.Coprime 30 ∧
        ab.2 < 30 ∧ ab.2.Coprime 30 := by decide
    exact h (a, b) hab
  · have h : ∀ ab ∈ classList 2, ab.1 < 30 ∧ ab.1.Coprime 30 ∧
        ab.2 < 30 ∧ ab.2.Coprime 30 := by decide
    exact h (a, b) hab

private lemma sum_H_le_sum_pairSet {K s : ℕ} (hK : 1 ≤ K) (hs : s = 0 ∨ s = 2) :
    ∑ n ∈ A_set K, H_fn (n + s) ≤
      ∑ ab ∈ classList s, (pairSet (1920 * K) s ab.1 ab.2).card := by
  set X : ℕ := 1920 * K
  have hX : 24 ≤ X := by omega
  have hsum : ∑ n ∈ A_set K, H_fn (n + s) =
      ((A_set K).sigma (fun n => H_set (n + s))).card := by
    rw [Finset.card_sigma]
    rfl
  rw [hsum]
  let T : Finset (ℕ × ℕ) := (classList s).biUnion (fun ab => pairSet X s ab.1 ab.2)
  refine le_trans ?_ (Finset.card_biUnion_le)
  refine Finset.card_le_card_of_injOn (fun x : Σ _ : ℕ, ℕ => (x.2, x.1 + s - x.2)) ?_ ?_
  · intro x hx
    rcases Finset.mem_sigma.mp (Finset.mem_coe.mp hx) with ⟨hnA, hpH⟩
    rcases A_set_mem_props hnA with ⟨hlo, hhi, _, _, hn30⟩
    rcases (Finset.mem_filter.mp hpH).2 with ⟨hp_prime, hp_le, hq_prime, hc1, hc2⟩
    set n : ℕ := x.1
    set p : ℕ := x.2
    set q : ℕ := n + s - p
    have hadd : p + q = n + s := by omega
    rcases central_cover hlo hhi hadd hc1 hc2 with ⟨hp_lo, hp_hi, hq_lo, hq_hi⟩
    rcases endpoints_in_range hX hs hp_lo hp_hi with ⟨h4lp, _, h4lq, _⟩
    have hp5 : 5 < p := by omega
    have hq5 : 5 < q := by omega
    have hp_cop : Nat.gcd p 30 = 1 := prime_coprime_30 hp_prime hp5
    have hq_cop : Nat.gcd q 30 = 1 := prime_coprime_30 hq_prime hq5
    have hmem_list : (p % 30, q % 30) ∈ pairsAt ((n + s) % 30) :=
      represented_mem hp_cop hq_cop hadd
    have hclass : (p % 30, q % 30) ∈ classList s := by
      rcases hs with rfl | rfl
      · have hmod : (n + 0) % 30 = 26 := by omega
        rw [hmod, classes26] at hmem_list
        simp [classList] at hmem_list ⊢
        exact hmem_list
      · have hmod : (n + 2) % 30 = 28 := by omega
        rw [hmod, classes28] at hmem_list
        simp [classList] at hmem_list ⊢
        exact hmem_list
    have hpP : p ∈ P_set X s (p % 30) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_lo, hp_hi⟩, hp_prime, rfl⟩
    have hqQ : q ∈ Q_set X s p (q % 30) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq_lo, hq_hi⟩, hq_prime, rfl⟩
    exact Finset.mem_coe.mpr <|
      Finset.mem_biUnion.mpr ⟨(p % 30, q % 30), hclass,
        Finset.mem_biUnion.mpr ⟨p, hpP, Finset.mem_image.mpr ⟨q, hqQ, rfl⟩⟩⟩
  · intro x₁ hx₁ x₂ hx₂ heq
    rcases Finset.mem_sigma.mp (Finset.mem_coe.mp hx₁) with ⟨_, hpH₁⟩
    rcases Finset.mem_sigma.mp (Finset.mem_coe.mp hx₂) with ⟨_, hpH₂⟩
    have hle₁ : x₁.2 ≤ x₁.1 + s := (Finset.mem_filter.mp hpH₁).2.2.1
    have hle₂ : x₂.2 ≤ x₂.1 + s := (Finset.mem_filter.mp hpH₂).2.2.1
    have hp_eq : x₁.2 = x₂.2 := congrArg Prod.fst heq
    have hq_eq : x₁.1 + s - x₁.2 = x₂.1 + s - x₂.2 := congrArg Prod.snd heq
    have hn_eq : x₁.1 = x₂.1 := by omega
    cases x₁
    cases x₂
    simp_all

private lemma card_pairSet_le (X s a b : ℕ) :
    (pairSet X s a b).card ≤ ∑ p ∈ P_set X s a, (Q_set X s p b).card := by
  unfold pairSet
  calc
    ((P_set X s a).biUnion (fun p => (Q_set X s p b).image (fun q => (p, q)))).card
        ≤ ∑ p ∈ P_set X s a, ((Q_set X s p b).image (fun q => (p, q))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ p ∈ P_set X s a, (Q_set X s p b).card :=
      Finset.sum_le_sum (fun _ _ => Finset.card_image_le)

private lemma Q_set_bound {X s p a b : ℕ}
    (hWinX : ∀ c : ℕ, c < 30 → c.Coprime 30 →
      ∀ l u : ℕ, X ≤ 4 * l → l ≤ u → u ≤ 2 * X →
      (((Finset.Icc l u).filter (fun q : ℕ => q.Prime ∧ q % 30 = c)).card : ℝ) ≤
        (((u : ℝ) - (l : ℝ) + 1) / (8 * Real.log (X : ℝ))) +
          (1 / 100000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)))
    (hX : 100000 ≤ X) (hs : s = 0 ∨ s = 2)
    (hp : p ∈ P_set X s a) (hb_lt : b < 30) (hb_cop : b.Coprime 30) :
    ((Q_set X s p b).card : ℝ) ≤
      (1 / 512 + 1 / 50000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := by
  have hp_mem : lowerP X s ≤ p ∧ p ≤ upperP X s :=
    Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
  rcases endpoints_in_range (by omega : 24 ≤ X) hs hp_mem.1 hp_mem.2 with ⟨_, _, h4lq, huq_hi⟩
  have hlq_le_uq : X + s - p ≤ 65 * X / 64 + s - p := by omega
  have hQ := hWinX b hb_lt hb_cop (X + s - p) (65 * X / 64 + s - p) h4lq hlq_le_uq huq_hi
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hX_real : (100000 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hdiff_nat : (65 * X / 64 + s - p) - (X + s - p) = X / 64 :=
    (interval_widths hp_mem.2).2
  have hdiff_real : ((65 * X / 64 + s - p : ℕ) : ℝ) - ((X + s - p : ℕ) : ℝ) ≤ (X : ℝ) / 64 := by
    rw [← Nat.cast_sub hlq_le_uq, hdiff_nat]
    have hmul : (64 : ℝ) * ((X / 64 : ℕ) : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast Nat.mul_div_le X 64
    linarith
  have hnum : ((65 * X / 64 + s - p : ℕ) : ℝ) - ((X + s - p : ℕ) : ℝ) + 1 ≤
      (1 / 64 + 1 / 100000 : ℝ) * (X : ℝ) := by
    linarith
  have hdiv :
      (((65 * X / 64 + s - p : ℕ) : ℝ) - ((X + s - p : ℕ) : ℝ) + 1) / (8 * Real.log (X : ℝ)) ≤
        ((1 / 64 + 1 / 100000 : ℝ) * (X : ℝ)) / (8 * Real.log (X : ℝ)) :=
    div_le_div_of_nonneg_right hnum (by positivity)
  have hrewrite :
      ((1 / 64 + 1 / 100000 : ℝ) * (X : ℝ)) / (8 * Real.log (X : ℝ)) +
        (1 / 100000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) =
      (1 / 512 + 9 / 800000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := by
    ring
  have hratio_nonneg : 0 ≤ (X : ℝ) / Real.log (X : ℝ) :=
    div_nonneg (by linarith) (le_of_lt hlog)
  have hcoef : (1 / 512 + 9 / 800000 : ℝ) ≤ 1 / 512 + 1 / 50000 := by norm_num
  calc
    ((Q_set X s p b).card : ℝ)
        ≤ (((65 * X / 64 + s - p : ℕ) : ℝ) - ((X + s - p : ℕ) : ℝ) + 1) / (8 * Real.log (X : ℝ)) +
            (1 / 100000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := hQ
    _ ≤ ((1 / 64 + 1 / 100000 : ℝ) * (X : ℝ)) / (8 * Real.log (X : ℝ)) +
          (1 / 100000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := by linarith
    _ = (1 / 512 + 9 / 800000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := hrewrite
    _ ≤ (1 / 512 + 1 / 50000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef hratio_nonneg

private lemma P_set_bound {X s a : ℕ}
    (hWinX : ∀ c : ℕ, c < 30 → c.Coprime 30 →
      ∀ l u : ℕ, X ≤ 4 * l → l ≤ u → u ≤ 2 * X →
      (((Finset.Icc l u).filter (fun q : ℕ => q.Prime ∧ q % 30 = c)).card : ℝ) ≤
        (((u : ℝ) - (l : ℝ) + 1) / (8 * Real.log (X : ℝ))) +
          (1 / 100000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)))
    (hX : 100000 ≤ X) (hs : s = 0 ∨ s = 2)
    (ha_lt : a < 30) (ha_cop : a.Coprime 30) :
    ((P_set X s a).card : ℝ) ≤
      (11 / 256 + 1 / 50000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := by
  have hlp_le_up : lowerP X s ≤ upperP X s := lowerP_le_upperP (by omega : 24 ≤ X) hs
  rcases endpoints_in_range (by omega : 24 ≤ X) hs (le_refl _) hlp_le_up with ⟨h4lp, hup_hi, _, _⟩
  have hP := hWinX a ha_lt ha_cop (lowerP X s) (upperP X s) h4lp hlp_le_up hup_hi
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hX_real : (100000 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hwidth_nat : 192 * (upperP X s - lowerP X s) ≤ 66 * X + 128 := by
    have hw := (interval_widths (le_refl (upperP X s))).1
    omega
  have hwidth_real : ((upperP X s : ℕ) : ℝ) - ((lowerP X s : ℕ) : ℝ) ≤
      (66 * (X : ℝ) + 128) / 192 := by
    rw [← Nat.cast_sub hlp_le_up]
    have hcast : (192 : ℝ) * ((upperP X s - lowerP X s : ℕ) : ℝ) ≤ 66 * (X : ℝ) + 128 := by
      exact_mod_cast hwidth_nat
    linarith
  have hnum : ((upperP X s : ℕ) : ℝ) - ((lowerP X s : ℕ) : ℝ) + 1 ≤
      (11 / 32 + 1 / 50000 : ℝ) * (X : ℝ) := by
    linarith
  have hdiv :
      (((upperP X s : ℕ) : ℝ) - ((lowerP X s : ℕ) : ℝ) + 1) / (8 * Real.log (X : ℝ)) ≤
        ((11 / 32 + 1 / 50000 : ℝ) * (X : ℝ)) / (8 * Real.log (X : ℝ)) :=
    div_le_div_of_nonneg_right hnum (by positivity)
  have hrewrite :
      ((11 / 32 + 1 / 50000 : ℝ) * (X : ℝ)) / (8 * Real.log (X : ℝ)) +
        (1 / 100000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) =
      (11 / 256 + 1 / 80000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := by
    ring
  have hratio_nonneg : 0 ≤ (X : ℝ) / Real.log (X : ℝ) :=
    div_nonneg (by linarith) (le_of_lt hlog)
  have hcoef : (11 / 256 + 1 / 80000 : ℝ) ≤ 11 / 256 + 1 / 50000 := by norm_num
  calc
    ((P_set X s a).card : ℝ)
        ≤ (((upperP X s : ℕ) : ℝ) - ((lowerP X s : ℕ) : ℝ) + 1) / (8 * Real.log (X : ℝ)) +
            (1 / 100000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := hP
    _ ≤ ((11 / 32 + 1 / 50000 : ℝ) * (X : ℝ)) / (8 * Real.log (X : ℝ)) +
          (1 / 100000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := by linarith
    _ = (11 / 256 + 1 / 80000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := hrewrite
    _ ≤ (11 / 256 + 1 / 50000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef hratio_nonneg

private lemma pairSet_bound {X s a b : ℕ}
    (hWinX : ∀ c : ℕ, c < 30 → c.Coprime 30 →
      ∀ l u : ℕ, X ≤ 4 * l → l ≤ u → u ≤ 2 * X →
      (((Finset.Icc l u).filter (fun q : ℕ => q.Prime ∧ q % 30 = c)).card : ℝ) ≤
        (((u : ℝ) - (l : ℝ) + 1) / (8 * Real.log (X : ℝ))) +
          (1 / 100000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)))
    (hX : 100000 ≤ X) (hs : s = 0 ∨ s = 2)
    (ha_lt : a < 30) (ha_cop : a.Coprime 30)
    (hb_lt : b < 30) (hb_cop : b.Coprime 30) :
    ((pairSet X s a b).card : ℝ) ≤
      (11 / 256 + 1 / 50000 : ℝ) * (1 / 512 + 1 / 50000 : ℝ) * ((X : ℝ) * M_fn X) := by
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hQ_nonneg : 0 ≤ (1 / 512 + 1 / 50000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) := by
    positivity
  have hcard : ((pairSet X s a b).card : ℝ) ≤ ∑ p ∈ P_set X s a, ((Q_set X s p b).card : ℝ) := by
    exact_mod_cast card_pairSet_le X s a b
  have hP := P_set_bound hWinX hX hs ha_lt ha_cop
  calc
    ((pairSet X s a b).card : ℝ)
        ≤ ∑ p ∈ P_set X s a, ((Q_set X s p b).card : ℝ) := hcard
    _ ≤ ∑ _p ∈ P_set X s a, ((1 / 512 + 1 / 50000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ))) :=
      Finset.sum_le_sum (fun p hp => Q_set_bound hWinX hX hs hp hb_lt hb_cop)
    _ = ((P_set X s a).card : ℝ) * ((1 / 512 + 1 / 50000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((11 / 256 + 1 / 50000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ))) *
          ((1 / 512 + 1 / 50000 : ℝ) * ((X : ℝ) / Real.log (X : ℝ))) :=
      mul_le_mul_of_nonneg_right hP hQ_nonneg
    _ = (11 / 256 + 1 / 50000 : ℝ) * (1 / 512 + 1 / 50000 : ℝ) * ((X : ℝ) * M_fn X) := by
      unfold M_fn
      ring

private lemma sum_H_bound {K s : ℕ}
    (hWinX : ∀ c : ℕ, c < 30 → c.Coprime 30 →
      ∀ l u : ℕ, 1920 * K ≤ 4 * l → l ≤ u → u ≤ 2 * (1920 * K) →
      (((Finset.Icc l u).filter (fun q : ℕ => q.Prime ∧ q % 30 = c)).card : ℝ) ≤
        (((u : ℝ) - (l : ℝ) + 1) / (8 * Real.log ((1920 * K : ℕ) : ℝ))) +
          (1 / 100000 : ℝ) * (((1920 * K : ℕ) : ℝ) / Real.log ((1920 * K : ℕ) : ℝ)))
    (hK : 100000 ≤ K) (hs : s = 0 ∨ s = 2) :
    ((∑ n ∈ A_set K, H_fn (n + s) : ℕ) : ℝ) ≤
      3 * ((11 / 256 + 1 / 50000 : ℝ) * (1 / 512 + 1 / 50000 : ℝ) *
        (((1920 * K : ℕ) : ℝ) * M_fn (1920 * K))) := by
  have hX : 100000 ≤ 1920 * K := by omega
  have hnat : ((∑ n ∈ A_set K, H_fn (n + s) : ℕ) : ℝ) ≤
      ∑ ab ∈ classList s, ((pairSet (1920 * K) s ab.1 ab.2).card : ℝ) := by
    exact_mod_cast sum_H_le_sum_pairSet (by omega : 1 ≤ K) hs
  calc
    ((∑ n ∈ A_set K, H_fn (n + s) : ℕ) : ℝ)
        ≤ ∑ ab ∈ classList s, ((pairSet (1920 * K) s ab.1 ab.2).card : ℝ) := hnat
    _ ≤ ∑ _ab ∈ classList s,
          ((11 / 256 + 1 / 50000 : ℝ) * (1 / 512 + 1 / 50000 : ℝ) *
            (((1920 * K : ℕ) : ℝ) * M_fn (1920 * K))) := by
      refine Finset.sum_le_sum (fun ab hab => ?_)
      rcases classList_coprime hs hab with ⟨ha_lt, ha_cop, hb_lt, hb_cop⟩
      exact pairSet_bound hWinX hX hs ha_lt ha_cop hb_lt hb_cop
    _ = ((classList s).card : ℝ) *
          ((11 / 256 + 1 / 50000 : ℝ) * (1 / 512 + 1 / 50000 : ℝ) *
            (((1920 * K : ℕ) : ℝ) * M_fn (1920 * K))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = 3 * ((11 / 256 + 1 / 50000 : ℝ) * (1 / 512 + 1 / 50000 : ℝ) *
          (((1920 * K : ℕ) : ℝ) * M_fn (1920 * K))) := by
      rw [classList_card hs]
      norm_num

private lemma sum_R_bound {K : ℕ}
    (hWinX : ∀ c : ℕ, c < 30 → c.Coprime 30 →
      ∀ l u : ℕ, 1920 * K ≤ 4 * l → l ≤ u → u ≤ 2 * (1920 * K) →
      (((Finset.Icc l u).filter (fun q : ℕ => q.Prime ∧ q % 30 = c)).card : ℝ) ≤
        (((u : ℝ) - (l : ℝ) + 1) / (8 * Real.log ((1920 * K : ℕ) : ℝ))) +
          (1 / 100000 : ℝ) * (((1920 * K : ℕ) : ℝ) / Real.log ((1920 * K : ℕ) : ℝ)))
    (hK : 100000 ≤ K) :
    ∑ n ∈ A_set K, R_fn n ≤
      (63 / 64 : ℝ) * M_fn (1920 * K) * ((A_set K).card : ℝ) := by
  have h0 := sum_H_bound hWinX hK (Or.inl rfl)
  have h2 := sum_H_bound hWinX hK (Or.inr rfl)
  have hR_split : ∑ n ∈ A_set K, R_fn n =
      ((∑ n ∈ A_set K, H_fn n : ℕ) : ℝ) + ((∑ n ∈ A_set K, H_fn (n + 2) : ℕ) : ℝ) := by
    simp only [R_fn, Nat.cast_add, Finset.sum_add_distrib, Nat.cast_sum]
  have hlog : 0 < Real.log ((1920 * K : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 1920 * K))
  have hM_nonneg : 0 ≤ M_fn (1920 * K) := by
    unfold M_fn
    positivity
  have hfactor_nonneg : 0 ≤ M_fn (1920 * K) * ((A_set K).card : ℝ) := by
    positivity
  have hX_cast : ((1920 * K : ℕ) : ℝ) = 1920 * ((A_set K).card : ℝ) := by
    rw [A_set_card K]
    push_cast
    ring
  have hcoef :
      (6 * 1920 * (11 / 256 + 1 / 50000 : ℝ) * (1 / 512 + 1 / 50000 : ℝ)) ≤ 63 / 64 := by
    norm_num
  calc
    ∑ n ∈ A_set K, R_fn n
        = ((∑ n ∈ A_set K, H_fn n : ℕ) : ℝ) + ((∑ n ∈ A_set K, H_fn (n + 2) : ℕ) : ℝ) :=
      hR_split
    _ ≤ 3 * ((11 / 256 + 1 / 50000 : ℝ) * (1 / 512 + 1 / 50000 : ℝ) *
            (((1920 * K : ℕ) : ℝ) * M_fn (1920 * K))) +
        3 * ((11 / 256 + 1 / 50000 : ℝ) * (1 / 512 + 1 / 50000 : ℝ) *
            (((1920 * K : ℕ) : ℝ) * M_fn (1920 * K))) := by
      exact add_le_add (by simpa only [Nat.add_zero] using h0) h2
    _ = (6 * 1920 * (11 / 256 + 1 / 50000 : ℝ) * (1 / 512 + 1 / 50000 : ℝ)) *
          (M_fn (1920 * K) * ((A_set K).card : ℝ)) := by
      rw [hX_cast]
      ring
    _ ≤ (63 / 64 : ℝ) * (M_fn (1920 * K) * ((A_set K).card : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef hfactor_nonneg
    _ = (63 / 64 : ℝ) * M_fn (1920 * K) * ((A_set K).card : ℝ) := by ring

private lemma finset_mean_to_energy {ι : Type*} (s : Finset ι) (d : ι → ℝ) (a : ℝ)
    (ha : 0 ≤ a) (hmean : (s.card : ℝ) * a ≤ ∑ i ∈ s, d i) :
    (s.card : ℝ) * a ^ 2 ≤ ∑ i ∈ s, (d i) ^ 2 := by
  have htan : ∀ i ∈ s, 2 * a * d i - a ^ 2 ≤ (d i) ^ 2 := by
    intro i _
    nlinarith [sq_nonneg (d i - a)]
  have hsum : ∑ i ∈ s, (2 * a * d i - a ^ 2) ≤ ∑ i ∈ s, (d i) ^ 2 :=
    Finset.sum_le_sum htan
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hsum
  have hmul : 2 * a * ((s.card : ℝ) * a) ≤ 2 * a * ∑ i ∈ s, d i :=
    mul_le_mul_of_nonneg_left hmean (by linarith)
  linarith

end BeaumontFiniteAssembly

theorem beaumontRefute_of_window30 (hWindow : BeaumontCountBridge.Window30Bound) :
    ¬ (let H := fun n : ℕ => ((Finset.range (n+1)).filter (fun p => p.Prime ∧ p ≤ n ∧ (n-p).Prime ∧ n ≤ 3*p ∧ 3*p ≤ 2*n)).card;
       let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n);
       let M := fun X : ℕ => (X:ℝ)/(Real.log (X:ℝ))^2;
       let R := fun n : ℕ => ((H n + H (n+2)):ℝ);
       ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀, ∃ b : ℕ → ℝ,
         (∀ n ∈ E X, M X ≤ b n) ∧
         (∑ n ∈ E X, (R n-b n)^2) ≤ ε*(X:ℝ)*(M X)^2) := by
  intro hMain
  change ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀, ∃ b : ℕ → ℝ,
    (∀ n ∈ E_set X, M_fn X ≤ b n) ∧
    (∑ n ∈ E_set X, (R_fn n - b n) ^ 2) ≤ ε * (X : ℝ) * (M_fn X) ^ 2 at hMain
  rcases hWindow (1 / 100000 : ℝ) (by norm_num) with ⟨Xw, hXw⟩
  rcases hMain ((1 / 64 : ℝ) / (120 * 64 ^ 2)) (by norm_num) with ⟨X₁, hX₁⟩
  let K : ℕ := max (max Xw X₁) 100000
  let X : ℕ := 1920 * K
  have hK : 100000 ≤ K := by omega
  have hXw_le : Xw ≤ X := by omega
  have hX1_le : X₁ ≤ X := by omega
  rcases hX₁ X hX1_le with ⟨b, hb, hEnergy⟩
  have hR_sum : ∑ n ∈ A_set K, R_fn n ≤ (63 / 64 : ℝ) * M_fn X * ((A_set K).card : ℝ) :=
    sum_R_bound (hXw X hXw_le) hK
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hM_pos : 0 < M_fn X := by
    unfold M_fn
    have hX_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
    exact div_pos hX_pos (sq_pos_of_pos hlog)
  have hb_sum : ((A_set K).card : ℝ) * M_fn X ≤ ∑ n ∈ A_set K, b n := by
    calc
      ((A_set K).card : ℝ) * M_fn X = ∑ _n ∈ A_set K, M_fn X := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ A_set K, b n :=
        Finset.sum_le_sum (fun n hn => hb n (A_set_subset_E K hn))
  have hmean : ((A_set K).card : ℝ) * ((1 / 64 : ℝ) * M_fn X) ≤
      ∑ n ∈ A_set K, (b n - R_fn n) := by
    rw [Finset.sum_sub_distrib]
    linarith
  have hlb : ((A_set K).card : ℝ) * ((1 / 64 : ℝ) * M_fn X) ^ 2 ≤
      ∑ n ∈ A_set K, (R_fn n - b n) ^ 2 := by
    have h := finset_mean_to_energy (A_set K) (fun n => b n - R_fn n)
      ((1 / 64 : ℝ) * M_fn X) (by positivity) hmean
    refine le_trans h (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun _ _ => by ring)
  have hsub : ∑ n ∈ A_set K, (R_fn n - b n) ^ 2 ≤ ∑ n ∈ E_set X, (R_fn n - b n) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (A_set_subset_E K) (fun _ _ _ => sq_nonneg _)
  have hchain : ((A_set K).card : ℝ) * ((1 / 64 : ℝ) * M_fn X) ^ 2 ≤
      ((1 / 64 : ℝ) / (120 * 64 ^ 2)) * (X : ℝ) * (M_fn X) ^ 2 :=
    le_trans hlb (le_trans hsub hEnergy)
  have hpos : 0 < (X : ℝ) * (M_fn X) ^ 2 :=
    mul_pos (by exact_mod_cast (by omega : 0 < X)) (sq_pos_of_pos hM_pos)
  have hcontra_lhs :
      ((A_set K).card : ℝ) * ((1 / 64 : ℝ) * M_fn X) ^ 2 =
        (1 / (1920 * 64 ^ 2 : ℝ)) * ((X : ℝ) * (M_fn X) ^ 2) := by
    rw [A_set_card K]
    have hX_cast : (X : ℝ) = 1920 * (K : ℝ) := by
      dsimp [X]
      push_cast
      ring
    rw [hX_cast]
    ring
  have hcontra_rhs :
      ((1 / 64 : ℝ) / (120 * 64 ^ 2)) * (X : ℝ) * (M_fn X) ^ 2 =
        (1 / (7680 * 64 ^ 2 : ℝ)) * ((X : ℝ) * (M_fn X) ^ 2) := by
    ring
  nlinarith

theorem Conjectures.Goldbach.BeaumontCentralLocalPredictionRefute :
¬ (let H := fun n : ℕ => ((Finset.range (n+1)).filter (fun p => p.Prime ∧ p ≤ n ∧ (n-p).Prime ∧ n ≤ 3*p ∧ 3*p ≤ 2*n)).card; let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let M := fun X : ℕ => (X:ℝ)/(Real.log (X:ℝ))^2; let R := fun n : ℕ => ((H n + H (n+2)):ℝ); ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ X₀, ∃ b : ℕ → ℝ, (∀ n ∈ E X, M X ≤ b n) ∧ (∑ n ∈ E X, (R n-b n)^2) ≤ ε*(X:ℝ)*(M X)^2) :=
  beaumontRefute_of_window30 BeaumontCountBridge.window30Bound
