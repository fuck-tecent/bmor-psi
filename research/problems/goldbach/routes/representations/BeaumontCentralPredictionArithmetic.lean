import Std

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

/-- The divisor property of a prime greater than 5 puts it in a reduced class. -/
theorem prime_residue {p : Nat} (h5 : 5 < p)
    (hp : ∀ d, d ∣ p → d = 1 ∨ d = p) : p % 30 ∈ units30 := by
  have h2 : ¬ 2 ∣ p := fun h => by have := hp 2 h; omega
  have h3 : ¬ 3 ∣ p := fun h => by have := hp 3 h; omega
  have h5' : ¬ 5 ∣ p := fun h => by have := hp 5 h; omega
  have finite_check : ∀ a : Fin 30, ¬ 2 ∣ a.val → ¬ 3 ∣ a.val →
      ¬ 5 ∣ a.val → a.val ∈ units30 := by decide
  refine finite_check ⟨p % 30, Nat.mod_lt _ (by decide)⟩ ?_ ?_ ?_
  · exact fun h => h2 ((Nat.dvd_mod_iff (by decide : 2 ∣ 30)).mp h)
  · exact fun h => h3 ((Nat.dvd_mod_iff (by decide : 3 ∣ 30)).mp h)
  · exact fun h => h5' ((Nat.dvd_mod_iff (by decide : 5 ∣ 30)).mp h)

/-- On the selected progression, the shifted target is 28 mod 30 and n lies
    in the even dyadic interval used in the statement. -/
theorem target_properties {X n : Nat} (hlo : X ≤ n)
    (hhi : n ≤ 65 * X / 64) (hn : n % 30 = 26) :
    X ≤ n ∧ n ≤ 2 * X ∧ n % 2 = 0 ∧ (n + 2) % 30 = 28 := by omega

/-- For X=1920K the target set has exactly K indices, given by this bijection. -/
theorem target_indices {K n : Nat} :
    (1920 * K ≤ n ∧ n ≤ 1950 * K ∧ n % 30 = 26) ↔
      ∃ t, t < K ∧ n = 1920 * K + 30 * t + 26 := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(n - 1920 * K) / 30, ?_, ?_⟩ <;> omega
  · rintro ⟨t, ht, rfl⟩
    omega

theorem target_index_injective {K u v : Nat}
    (h : 1920 * K + 30 * u + 26 = 1920 * K + 30 * v + 26) : u = v := by omega

theorem unique_target {p q s n m : Nat}
    (hn : p + q = n + s) (hm : p + q = m + s) : n = m := by omega

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

/-- Uniformity interval [X/4,2X] for the four endpoints of both shifts.
    The last two inequalities also cover candidates p without a representation. -/
theorem endpoints_in_range {X p s : Nat} (hX : 24 ≤ X) (hs : s = 0 ∨ s = 2)
    (hlo : lowerP X s ≤ p) (hhi : p ≤ upperP X s) :
    X ≤ 4 * lowerP X s ∧ upperP X s ≤ 2 * X ∧
      X ≤ 4 * (X + s - p) ∧ (65 * X) / 64 + s - p ≤ 2 * X := by
  unfold lowerP upperP at *
  omega

/-- 192 times the integral p width is bounded by 66X+64s. Its leading
    term is (1+2/64)X/3. The q width is exactly floor(X/64). -/
theorem interval_widths {X p s : Nat}
    (hhi : p ≤ upperP X s) :
    192 * (upperP X s - lowerP X s) ≤ 66 * X + 64 * s ∧
      ((65 * X) / 64 + s - p) - (X + s - p) = X / 64 := by
  unfold lowerP upperP at *
  omega

/-- After both fixed-modulus PNT bounds, divide by the target density
    δ/30. The six ordered classes each contribute a factor 1/8². -/
theorem averaged_coefficient :
    let δ : Rat := 1 / 64
    6 * ((1 + 2 * δ) / (3 * 8)) * (δ / 8) / (δ / 30) = 495 / 512 := by decide +kernel

/-- The gap allows the o(1) term to be absorbed into the ceiling 63/64. -/
theorem strict_slack : (495 / 512 : Rat) < 63 / 64 ∧
    (1 : Rat) - 63 / 64 = 1 / 64 := by decide +kernel

theorem energy_constant :
    let δ : Rat := 1 / 64
    0 < δ / (120 * 64^2) ∧ δ / (120 * 64^2) < δ / (60 * 64^2) := by decide +kernel

open Lean.Grind Std

variable {R : Type u} [CommRing R] [LE R] [LT R] [IsLinearOrder R]
    [LawfulOrderLT R] [OrderedRing R]
attribute [local instance] Semiring.natCast

private theorem tangent (x a : R) : 2 * a * x - a^2 ≤ x^2 := by
  have h := OrderedRing.sq_nonneg (a := x - a)
  have he : x^2 - (2 * a * x - a^2) = (x - a)^2 := by grind
  grind

private theorem sum_tangent (ds : List R) (a : R) :
    2 * a * ds.sum - (ds.length : R) * a^2 ≤ (ds.map (fun x => x^2)).sum := by
  induction ds with
  | nil =>
    simp only [List.sum_nil, List.length_nil, List.map_nil]
    grind
  | cons d ds ih =>
    simp only [List.sum_cons, List.length_cons, List.map_cons]
    have he : 2 * a * (d + ds.sum) - ((ds.length + 1 : Nat) : R) * a^2 =
      (2 * a * d - a^2) + (2 * a * ds.sum - (ds.length : R) * a^2) := by
        rw [Semiring.natCast_succ]
        grind
    rw [he]
    exact OrderedAdd.add_le_add (tangent d a) ih

/-- If signed discrepancies have mean at least a ≥ 0, their sum of squares
    is at least the sample size times a², including for an empty sample. -/
theorem mean_to_energy (ds : List R) (a : R) (ha : 0 ≤ a)
    (hmean : (ds.length : R) * a ≤ ds.sum) :
    (ds.length : R) * a^2 ≤ (ds.map (fun x => x^2)).sum := by
  have hmul := OrderedRing.mul_le_mul_of_nonneg_left hmean (show 0 ≤ 2 * a by grind)
  have he : 2 * a * ((ds.length : R) * a) = 2 * ((ds.length : R) * a^2) := by grind
  rw [he] at hmul
  exact le_trans (by grind) (sum_tangent ds a)

end BeaumontCentralPredictionArithmetic
