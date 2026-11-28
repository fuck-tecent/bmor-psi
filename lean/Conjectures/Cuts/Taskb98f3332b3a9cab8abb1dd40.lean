import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/- Fixed-transition mean from the decomposition in Goldbach PR 4223.
The word family has exactly 85t transitions among 1000t gaps. Each complete
window is bounded by the endpoint of its 12-bit interval, after reflection
into the first half of the circle. Counts for the local flip patterns are
exact. The finite cosine estimate uses a rational Taylor bound and is
evaluated by the kernel. The last eleven terms use the lower bound -1.
OpenAI Codex produced this formalization.
-/

namespace GoldbachGridCertificate

def countOnes : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => n % 2 + countOnes k (n / 2)

def transitions (word : Nat) : Nat :=
  countOnes 11 (word ^^^ (word / 2))

def angleNum (word : Nat) : Int := 3927 * (Int.ofNat word + 1)

def taylorDen : Nat := 87178291200 * 2560000 ^ 14

def taylorShiftedNum (word : Nat) : Int :=
  let a := angleNum word
  let d : Int := 2560000
  2 * Int.ofNat taylorDen - 43589145600 * a ^ 2 * d ^ 12
    + 3632428800 * a ^ 4 * d ^ 10 - 121080960 * a ^ 6 * d ^ 8
    + 2162160 * a ^ 8 * d ^ 6 - 24024 * a ^ 10 * d ^ 4
    + 182 * a ^ 12 * d ^ 2 - a ^ 14

def shiftedCosineLower (word : Nat) : Nat :=
  if word = 2047 then 0
  else (1000000000 * (taylorShiftedNum word).toNat) / taylorDen

def falling (size length : Nat) : Nat :=
  (List.range length).foldl (fun acc i => acc * (size - i)) 1

def patternWeight (transitions : Nat) : Nat :=
  falling 170000 transitions * falling 1830000 (11 - transitions)

def aggregate : Nat :=
  (List.range 2048).foldl
    (fun acc word => acc + shiftedCosineLower word * patternWeight (transitions word)) 0

def aggregateDen : Nat := 1000000000 * 2000000 ^ 11

theorem falling_eq_descFactorial (size length : ℕ) :
    falling size length = size.descFactorial length := by
  unfold falling
  induction length with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.foldl_append, Nat.descFactorial_succ, ← ih]
      simp [Nat.mul_comm]

private theorem foldl_range_add_eq_sum (f : ℕ → ℕ) (length : ℕ) :
    (List.range length).foldl (fun total i => total + f i) 0 =
      ∑ i ∈ Finset.range length, f i := by
  induction length with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
      rfl

theorem aggregate_eq_sum :
    aggregate = ∑ q ∈ Finset.range 2048, shiftedCosineLower q *
      ((170000 : ℕ).descFactorial (transitions q) *
        (1830000 : ℕ).descFactorial (11 - transitions q)) := by
  unfold aggregate
  rw [foldl_range_add_eq_sum]
  simp only [patternWeight, falling_eq_descFactorial]

private def contribution (word : ℕ) : ℕ :=
  shiftedCosineLower word * patternWeight (transitions word)

private def blockAggregate (block : ℕ) : ℕ :=
  (List.range 128).foldl (fun acc i => acc + contribution (block * 128 + i)) 0

private theorem sum_eq_blocks (blocks : ℕ) :
    (∑ q ∈ Finset.range (blocks * 128), contribution q) =
      ∑ b ∈ Finset.range blocks, blockAggregate b := by
  induction blocks with
  | zero => simp
  | succ blocks ih =>
      rw [Nat.succ_mul, Finset.sum_range_add contribution, Finset.sum_range_succ blockAggregate, ih]
      have hblock : blockAggregate blocks =
          ∑ i ∈ Finset.range 128, contribution (blocks * 128 + i) :=
        foldl_range_add_eq_sum _ _
      rw [hblock]

private theorem aggregate_eq_blocks : aggregate = ∑ b ∈ Finset.range 16, blockAggregate b := by
  unfold aggregate
  rw [foldl_range_add_eq_sum]
  exact sum_eq_blocks 16

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem block0 : blockAggregate 0 =
    2868298174392570940229028640105237220403360175883156911101084026428099392000000 := by
  decide +kernel

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem block1 : blockAggregate 1 =
    257747124909522942139918818556247547570989380626536654605423201783440000000000 := by
  decide +kernel

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem block2 : blockAggregate 2 =
    23672174637751363791723083923872553405762778322892732517685987544608000000000 := by
  decide +kernel

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem block3 : blockAggregate 3 =
    230095979552673617431464128936585606055483452800372004909450237452128000000000 := by
  decide +kernel

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem block4 : blockAggregate 4 =
    20873934890490560930947265192867843352680039191159863001923403701648000000000 := by
  decide +kernel

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem block5 : blockAggregate 5 =
    1619910137987875037402848564748144476529732922352086514155623522400000000000 := by
  decide +kernel

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem block6 : blockAggregate 6 =
    16783762378642295331096092006409811174908202510956887789519617423248000000000 := by
  decide +kernel

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem block7 : blockAggregate 7 =
    137060413616166129079260094642531404591887388419227425662362172943168000000000 := by
  decide +kernel

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem block8 : blockAggregate 8 =
    12024351657604602562070880414750076772548398849702632254620515599152000000000 := by
  decide +kernel

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem block9 : blockAggregate 9 =
    740760183588528938985771943023907726010906973026212067488174665024000000000 := by
  decide +kernel

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem block10 : blockAggregate 10 =
    63170046447779413611816718754192605687373005887354877355148599250624000000 := by
  decide +kernel

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem block11 : blockAggregate 11 =
    361170396022449012551076436100175706661758328562897783879428396736000000000 := by
  decide +kernel

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem block12 : blockAggregate 12 =
    3387711468652726332560226312091397503568956578791602784893163891232000000000 := by
  decide +kernel

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem block13 : blockAggregate 13 =
    101790516094332107119305750232651670151658233654268402751748040176000000000 := by
  decide +kernel

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem block14 : blockAggregate 14 =
    825331833266441072527161794729731506126549208663363353050062918752000000000 := by
  decide +kernel

set_option maxRecDepth 1500 in
set_option maxHeartbeats 0 in
private theorem block15 : blockAggregate 15 =
    244364532010364591182828236979210259557997886149719759073514871152000000000 := by
  decide +kernel

theorem aggregate_exact :
    aggregate =
      3573900125149492948001450039535161474781914749741092617384716027780214016000000 := by
  rw [aggregate_eq_blocks]
  norm_num [Finset.sum_range_succ, block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15]

set_option maxRecDepth 10000 in
theorem weighted_mean_lower :
    174506 * aggregateDen < 100000 * aggregate := by
  rw [aggregate_exact]
  decide +kernel

private noncomputable def cosTerm (x : ℝ) (m : ℕ) : ℝ :=
  x ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)

private theorem cosTerm_succ_le (x : ℝ) (hx : 0 ≤ x) (hx2 : x ^ 2 ≤ 12)
    (m : ℕ) (hm : 1 ≤ m) : cosTerm x (m + 1) ≤ cosTerm x m := by
  have key : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
  have exp_eq : 2 * m + 1 + 1 = 2 * m + 2 := by omega
  have h₁ : (3 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ 2 * m + 1 by omega)
  have h₂ : (4 : ℝ) ≤ ((2 * m + 1 + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 4 ≤ 2 * m + 1 + 1 by omega)
  have hmul : (12 : ℝ) ≤ ((2 * m + 1 + 1 : ℕ) : ℝ) * ((2 * m + 1 : ℕ) : ℝ) := by
    calc
      12 = (4 : ℝ) * 3 := by norm_num
      _ ≤ _ := mul_le_mul h₂ h₁ (by norm_num) (by positivity)
  have hf : 0 < (Nat.factorial (2 * m) : ℝ) := by positivity
  have h₁p : 0 < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have h₂p : 0 < ((2 * m + 1 + 1 : ℕ) : ℝ) := by positivity
  unfold cosTerm
  calc
    _ = x ^ (2 * m) * x ^ 2 /
        (((2 * m + 1 + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) * (Nat.factorial (2 * m) : ℝ))) := by
      rw [key, Nat.factorial_succ, Nat.factorial_succ, exp_eq, pow_add]
      push_cast
      ring
    _ ≤ x ^ (2 * m) * (((2 * m + 1 + 1 : ℕ) : ℝ) * ((2 * m + 1 : ℕ) : ℝ)) /
        (((2 * m + 1 + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) * (Nat.factorial (2 * m) : ℝ))) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hx2.trans hmul) (by positivity))
        (by positivity)
    _ = _ := by field_simp

private noncomputable def cosLowerPoly (x : ℝ) : ℝ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320
    - x ^ 10 / 3628800 + x ^ 12 / 479001600 - x ^ 14 / 87178291200

private theorem cosLowerPoly_le_cos (x : ℝ) (hx : 0 ≤ x) (hx2 : x ^ 2 ≤ 12) :
    cosLowerPoly x ≤ Real.cos x := by
  let f := fun n : ℕ => (-1 : ℝ) ^ n * cosTerm x n
  let a := fun n : ℕ => cosTerm x (n + 8)
  have ht : HasSum f (Real.cos x) := by simpa [f, cosTerm, mul_div_assoc] using Real.hasSum_cos x
  have has : Summable a :=
    (summable_nat_add_iff (f := cosTerm x) 8).2 (Real.hasSum_cosh x).summable
  have ha : Antitone a := antitone_nat_of_succ_le (fun n => by
    simpa [a, Nat.add_right_comm] using cosTerm_succ_le x hx hx2 (n + 8) (by omega))
  have hsign (n : ℕ) : (-1 : ℝ) ^ n * a n = f (n + 8) := by
    simp [f, a, pow_add, show (-1 : ℝ) ^ 8 = 1 by norm_num]
  have htail : 0 ≤ ∑' n, f (n + 8) := by
    have hh := Antitone.alternating_series_le_tendsto has.tendsto_alternating_series_tsum ha 0
    simpa [hsign] using hh
  have hsplit := ht.summable.sum_add_tsum_nat_add 8
  have hpoly : ∑ n ∈ Finset.range 8, f n = cosLowerPoly x := by
    norm_num [Finset.sum_range_succ, f, cosTerm, cosLowerPoly, Nat.factorial]
    ring
  rw [← hpoly, ← ht.tsum_eq, ← hsplit]
  linarith

set_option maxHeartbeats 1000000 in
theorem shiftedCosineLower_le (word : ℕ) (hword : word < 2048) :
    (shiftedCosineLower word : ℝ) / 1000000000 ≤
      1 + Real.cos (Real.pi * ((word : ℝ) + 1) / 2048) := by
  by_cases hlast : word = 2047
  · simp only [shiftedCosineLower, ite_eq_left hlast, Nat.cast_zero, zero_div]
    linarith only [Real.neg_one_le_cos (Real.pi * ((word : ℝ) + 1) / 2048)]
  let x : ℝ := (angleNum word : ℝ) / 2560000
  let y : ℝ := Real.pi * ((word : ℝ) + 1) / 2048
  have hy : 0 ≤ y := by positivity
  have hx' : x = 3.1416 * ((word : ℝ) + 1) / 2048 := by
    norm_num [x, angleNum]
    ring
  have hx : 0 ≤ x := by rw [hx']; positivity
  have hyx : y ≤ x := by
    rw [hx']
    unfold y
    gcongr
    exact Real.pi_lt_d4.le
  have hword' : (word : ℝ) ≤ 2046 := by exact_mod_cast (show word ≤ 2046 by omega)
  have hxpi : x ≤ Real.pi := by
    rw [hx']
    linarith only [Real.pi_gt_d4, hword']
  have hx2 : x ^ 2 ≤ 12 := by
    calc
      _ ≤ (3.1416 : ℝ) ^ 2 := pow_le_pow_left₀ hx (hxpi.trans Real.pi_lt_d4.le) 2
      _ ≤ _ := by norm_num
  have hpol : ((taylorShiftedNum word : ℤ) : ℝ) / (taylorDen : ℝ) = 1 + cosLowerPoly x := by
    norm_num [taylorShiftedNum, taylorDen, cosLowerPoly, x, angleNum]
    ring
  have hcos := (cosLowerPoly_le_cos x hx hx2).trans
    (Real.cos_le_cos_of_nonneg_of_le_pi hy hxpi hyx)
  by_cases hnum : 0 ≤ taylorShiftedNum word
  · rw [shiftedCosineLower, ite_eq_right hlast]
    calc
      _ ≤ ((taylorShiftedNum word : ℤ) : ℝ) / (taylorDen : ℝ) := by
        have hden : 0 < (taylorDen : ℝ) := by norm_num [taylorDen]
        apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 1000000000) hden).2
        have hfloor : ((1000000000 * (taylorShiftedNum word).toNat / taylorDen : ℕ) : ℝ) *
            (taylorDen : ℝ) ≤ (1000000000 : ℝ) * ((taylorShiftedNum word).toNat : ℝ) := by
          exact_mod_cast Nat.div_mul_le_self (1000000000 * (taylorShiftedNum word).toNat) taylorDen
        rw [← Int.cast_natCast (R := ℝ) (taylorShiftedNum word).toNat, Int.toNat_of_nonneg hnum] at hfloor
        simpa only [mul_comm] using hfloor
      _ = 1 + cosLowerPoly x := hpol
      _ ≤ 1 + Real.cos y := add_le_add_right hcos 1
  · have hzero : (taylorShiftedNum word).toNat = 0 := Int.toNat_eq_zero.mpr (le_of_not_ge hnum)
    rw [shiftedCosineLower, ite_eq_right hlast, hzero, Nat.mul_zero, Nat.zero_div, Nat.cast_zero, zero_div]
    linarith only [Real.neg_one_le_cos y]


end GoldbachGridCertificate

namespace DyadicWord

def prefix12 (N j k : ℕ) : ℕ := (k / 2 ^ (N - (j + 12))) % 4096

noncomputable def phase16 (N j k : ℕ) : ℝ :=
  (↑⌊(65536 : ℝ) * (2 : ℝ)^j * ((k : ℝ) / (2 : ℝ)^N)⌋ : ℝ) / 65536

noncomputable def endpoint12 (q : ℕ) : ℝ :=
  if q < 2048 then ((q : ℝ) + 1) / 4096 else (4096 - (q : ℝ)) / 4096

private theorem nat_div_interval (k d : ℕ) (hd : 0 < d) :
    ((k / d : ℕ) : ℝ) ≤ (k : ℝ) / (d : ℝ) ∧
      (k : ℝ) / (d : ℝ) < ((k / d : ℕ) : ℝ) + 1 := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hmod : ((k % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt k hd
  have hdecomp : (d : ℝ) * ((k / d : ℕ) : ℝ) + ((k % d : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast Nat.div_add_mod k d
  constructor
  · apply (le_div_iff₀ hd').2
    linarith only [hdecomp, Nat.cast_nonneg (α := ℝ) (k % d), mul_comm (d : ℝ) ((k / d : ℕ) : ℝ)]
  · apply (div_lt_iff₀ hd').2
    rw [add_mul, one_mul, mul_comm _ (d : ℝ)]
    linarith only [hdecomp, hmod]

theorem phase16_interval {N j k : ℕ} (hj : j + 12 ≤ N) :
    let c := k / 2 ^ (N - (j + 12)) / 4096
    let q := prefix12 N j k
    (q : ℝ) / 4096 ≤ phase16 N j k - (c : ℝ) ∧
      phase16 N j k - (c : ℝ) < ((q : ℝ) + 1) / 4096 := by
  let d : ℕ := 2 ^ (N - (j + 12))
  let a : ℕ := k / d
  let c : ℕ := a / 4096
  let q : ℕ := a % 4096
  change (q : ℝ) / 4096 ≤ phase16 N j k - (c : ℝ) ∧
      phase16 N j k - (c : ℝ) < ((q : ℝ) + 1) / 4096
  have hd : 0 < d := by positivity
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hpow : (2 : ℝ)^N = (2 : ℝ)^j * 4096 * (d : ℝ) := by
    calc
      (2 : ℝ)^N = (2 : ℝ)^(j+12+(N-(j+12))) := by
        rw [Nat.add_sub_of_le hj]
      _ = _ := by
        rw [pow_add, pow_add]
        norm_num [d]
  have hscale : (65536 : ℝ) * (2 : ℝ)^j * ((k : ℝ) / (2 : ℝ)^N) =
      16 * ((k : ℝ) / (d : ℝ)) := by
    rw [hpow]
    field_simp
    ring
  obtain ⟨hlo, hhi⟩ := nat_div_interval k d hd
  have hleft : (16 : ℤ) * (a : ℤ) ≤ ⌊(16 : ℝ) * ((k : ℝ) / (d : ℝ))⌋ := by
    apply Int.le_floor.2
    push_cast
    change 16 * ((k / d : ℕ) : ℝ) ≤ 16 * ((k : ℝ) / (d : ℝ))
    exact mul_le_mul_of_nonneg_left hlo (by norm_num)
  have hright : ⌊(16 : ℝ) * ((k : ℝ) / (d : ℝ))⌋ < (16 : ℤ) * ((a : ℤ) + 1) := by
    apply Int.floor_lt.2
    push_cast
    change 16 * ((k : ℝ) / (d : ℝ)) < 16 * (((k / d : ℕ) : ℝ) + 1)
    exact mul_lt_mul_of_pos_left hhi (by norm_num)
  have hleft' : (16 : ℝ) * (a : ℝ) ≤ (↑⌊(16 : ℝ) * ((k : ℝ) / (d : ℝ))⌋ : ℝ) := by
    exact_mod_cast hleft
  have hright' : (↑⌊(16 : ℝ) * ((k : ℝ) / (d : ℝ))⌋ : ℝ) < (16 : ℝ) * ((a : ℝ) + 1) := by
    exact_mod_cast hright
  have hq : (4096 : ℝ) * (c : ℝ) + (q : ℝ) = (a : ℝ) := by
    exact_mod_cast Nat.div_add_mod a 4096
  unfold phase16
  rw [hscale]
  constructor <;> linarith only [hq, hleft', hright']

theorem phase16_cos_lower {N j k : ℕ} (hj : j + 12 ≤ N) :
    Real.cos (2 * Real.pi * endpoint12 (prefix12 N j k)) ≤
      (Complex.exp (↑((2 : ℝ) * Real.pi *
        (↑⌊(65536 : ℝ) * 2^j * ((k : ℝ) / 2^N)⌋ : ℝ) / 65536) * Complex.I)).re := by
  let c : ℕ := k / 2^(N-(j+12)) / 4096
  let q : ℕ := prefix12 N j k
  let x : ℝ := phase16 N j k - (c : ℝ)
  obtain ⟨hlo, hhi⟩ : (q : ℝ) / 4096 ≤ x ∧ x < ((q : ℝ) + 1) / 4096 :=
    phase16_interval hj
  have hq : q < 4096 := by
    unfold q prefix12
    exact Nat.mod_lt _ (by decide)
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  have hq' : (q : ℝ) < 4096 := by exact_mod_cast hq
  have hx0 : 0 ≤ x := le_trans (by positivity) hlo
  have hx1 : x ≤ 1 := by linarith only [hhi, show (q : ℝ) + 1 ≤ 4096 by exact_mod_cast (show q+1 ≤ 4096 by omega)]
  rw [Complex.exp_ofReal_mul_I_re]
  have hphase :
      (2 : ℝ) * Real.pi * (↑⌊(65536 : ℝ) * 2^j * ((k : ℝ) / 2^N)⌋ : ℝ) / 65536 =
      2 * Real.pi * x + (c : ℝ) * (2 * Real.pi) := by
    unfold x phase16
    ring
  rw [hphase, Real.cos_add_nat_mul_two_pi]
  change Real.cos (2 * Real.pi * endpoint12 q) ≤ Real.cos (2 * Real.pi * x)
  unfold endpoint12
  split_ifs with hhalf
  · have hhalf' : (q : ℝ) + 1 ≤ 2048 := by exact_mod_cast (show q + 1 ≤ 2048 by omega)
    have hle : ((q : ℝ) + 1) / 4096 ≤ 1 / 2 := by linarith only [hhalf']
    have hpi : 0 ≤ 2 * Real.pi := by positivity
    apply Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg hpi hx0)
    · calc
        _ ≤ (2 * Real.pi) * (1 / 2) := mul_le_mul_of_nonneg_left hle hpi
        _ = Real.pi := by ring
    · exact mul_le_mul_of_nonneg_left hhi.le hpi
  · have hhalf' : (2048 : ℝ) ≤ q := by exact_mod_cast (show 2048 ≤ q by omega)
    have hle : (4096 - (q : ℝ)) / 4096 ≤ 1 / 2 := by linarith only [hhalf']
    have hpi : 0 ≤ 2 * Real.pi := by positivity
    have hreflect : Real.cos (2 * Real.pi * x) = Real.cos (2 * Real.pi * (1 - x)) := by
      rw [show 2 * Real.pi * (1 - x) = 2 * Real.pi - (2 * Real.pi * x) by ring,
        Real.cos_two_pi_sub]
    rw [hreflect]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg hpi (by linarith only [hx1]))
    · calc
        _ ≤ (2 * Real.pi) * (1 / 2) := mul_le_mul_of_nonneg_left hle hpi
        _ = Real.pi := by ring
    · apply mul_le_mul_of_nonneg_left _ hpi
      linarith only [hlo]

end DyadicWord


namespace GoldbachGrid

def prefixPattern (q : ℕ) : Finset ℕ :=
  (Finset.range 11).filter fun i => (q.testBit i ^^ q.testBit (i + 1)) = true

def canonical (q : ℕ) : ℕ :=
  if q < 2048 then q else 4095 - q

theorem canonical_lt (q : ℕ) (hq : q < 4096) : canonical q < 2048 := by
  unfold canonical
  split <;> omega

theorem prefixPattern_canonical (q : ℕ) (hq : q < 4096) :
    prefixPattern (canonical q) = prefixPattern q := by
  by_cases hl : q < 2048
  · simp [canonical, hl]
  · rw [canonical, ite_eq_right hl]
    have hq' : q < 2 ^ 12 := by exact hq
    have hs : 4095 - q = 2 ^ 12 - (q + 1) := by omega
    rw [hs]
    ext i
    by_cases hi : i < 11
    · have hi₁ : i < 12 := by omega
      have hi₂ : i + 1 < 12 := by omega
      have hi₁' : decide (i < 12) = true := decide_eq_true hi₁
      have hi₂' : decide (i + 1 < 12) = true := decide_eq_true hi₂
      simp only [prefixPattern, Finset.mem_filter, Finset.mem_range, hi, true_and,
        Nat.testBit_two_pow_sub_succ hq', hi₁', hi₂', Bool.true_and]
      cases q.testBit i <;> cases q.testBit (i + 1) <;> decide
    · simp [prefixPattern, hi]

private theorem bool_xor_right_inj (a b c : Bool) :
    (a ^^ c) = (b ^^ c) → a = b := by
  cases a <;> cases b <;> cases c <;> decide

theorem prefixPattern_injective {p q : ℕ} (hp : p < 2048) (hq : q < 2048)
    (h : prefixPattern p = prefixPattern q) : p = q := by
  have hchange (i : ℕ) (hi : i < 11) :
      (p.testBit i ^^ p.testBit (i + 1)) = (q.testBit i ^^ q.testBit (i + 1)) := by
    have hm : i ∈ prefixPattern p ↔ i ∈ prefixPattern q := by rw [h]
    simp only [prefixPattern, Finset.mem_filter, Finset.mem_range, hi, true_and] at hm
    exact Bool.eq_iff_iff.mpr hm
  have hb : ∀ d : ℕ, d ≤ 11 → p.testBit (11 - d) = q.testBit (11 - d) := by
    intro d
    induction d with
    | zero =>
      intro _
      simp only [Nat.sub_zero]
      rw [Nat.testBit_eq_false_of_lt hp, Nat.testBit_eq_false_of_lt hq]
    | succ d ih =>
      intro hd
      let i := 11 - (d + 1)
      have hi : i < 11 := by dsimp [i]; omega
      have he : i + 1 = 11 - d := by dsimp [i]; omega
      have hs := ih (by omega)
      rw [← he] at hs
      have ht := hchange i hi
      rw [hs] at ht
      exact bool_xor_right_inj _ _ _ ht
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i ≤ 11
  · have he : 11 - (11 - i) = i := by omega
    simpa only [he] using hb (11 - i) (by omega)
  · have hpow : 2048 ≤ 2 ^ i := by
      change 2 ^ 11 ≤ 2 ^ i
      exact Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_eq_false_of_lt (hp.trans_le hpow),
      Nat.testBit_eq_false_of_lt (hq.trans_le hpow)]

theorem prefixPattern_injOn : Set.InjOn prefixPattern {q : ℕ | q < 2048} := by
  intro p hp q hq h
  exact prefixPattern_injective hp hq h

theorem prefixPattern_subset (q : ℕ) : prefixPattern q ⊆ Finset.range 11 :=
  Finset.filter_subset _ _

def countOnes : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, word => word % 2 + countOnes n (word / 2)

private theorem countOnes_eq_card_filter (n word : ℕ) :
    countOnes n word = ((Finset.range n).filter fun i => word.testBit i = true).card := by
  induction n generalizing word with
  | zero => simp [countOnes]
  | succ n ih =>
    let step : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩
    have hRange : Finset.range (n + 1) = insert 0 ((Finset.range n).map step) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_map]
      constructor
      · intro hi
        by_cases h : i = 0
        · exact Or.inl h
        · exact Or.inr ⟨i - 1, by omega, by change i - 1 + 1 = i; omega⟩
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · omega
        · change j + 1 < n + 1
          omega
    have htail :
        (((Finset.range n).map step).filter fun i => word.testBit i = true) =
          ((Finset.range n).filter fun i => (word / 2).testBit i = true).map step := by
      rw [Finset.filter_map]
      simp [step, Nat.testBit_succ]
    have hzero : 0 ∉ ((Finset.range n).filter fun i =>
        (word / 2).testBit i = true).map step := by
      simp [Finset.mem_map, step]
    rw [countOnes, hRange, Finset.filter_insert, htail, ih]
    by_cases hb : word.testBit 0 = true
    · have hm := Nat.mod_two_eq_one_iff_testBit_zero.mpr hb
      simp [hb, hm, Finset.card_insert_of_notMem hzero, Nat.add_comm]
    · have hb' : word.testBit 0 = false := Bool.eq_false_iff.mpr hb
      have hm := Nat.mod_two_eq_zero_iff_testBit_zero.mpr hb'
      simp [hb, hm]

theorem card_prefixPattern (q : ℕ) :
    (prefixPattern q).card = countOnes 11 (q ^^^ (q / 2)) := by
  rw [countOnes_eq_card_filter]
  simp [prefixPattern, Nat.testBit_div_two]

end GoldbachGrid

open Finset

namespace GoldbachGrid

/-- A word is determined by its low bit and the gaps at which the bit changes. -/
def flipBit (start : Bool) (flips : ℕ → Bool) : ℕ → Bool
  | 0 => start
  | i + 1 => flipBit start flips i ^^ flips i

theorem flipBit_shift (start : Bool) (flips : ℕ → Bool) (i j : ℕ) :
    flipBit start flips (i+j) =
      flipBit (flipBit start flips i) (fun k => flips (i+k)) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (flipBit start flips (i+j) ^^ flips (i+j)) =
      (flipBit (flipBit start flips i) (fun k => flips (i+k)) j ^^ flips (i+j))
    rw [ih]

theorem flipBit_not (start : Bool) (flips : ℕ → Bool) (i : ℕ) :
    flipBit (!start) flips i = !(flipBit start flips i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [flipBit, ih]
    cases flipBit start flips i <;> cases flips i <;> decide

theorem flipBit_transition (start : Bool) (flips : ℕ → Bool) (i : ℕ) :
    (flipBit start flips i ^^ flipBit start flips (i+1)) = flips i := by
  simp only [flipBit]
  cases flipBit start flips i <;> cases flips i <;> decide

def flipEncoding (n : ℕ) (p : Bool × Finset ℕ) : ℕ :=
  Nat.ofBits (fun i : Fin n => flipBit p.1 (fun j => decide (j ∈ p.2)) i)

theorem flipEncoding_lt (n : ℕ) (p : Bool × Finset ℕ) : flipEncoding n p < 2^n := by
  exact Nat.ofBits_lt_two_pow _

theorem flipEncoding_testBit (n : ℕ) (p : Bool × Finset ℕ) (i : ℕ) (hi : i < n) :
    (flipEncoding n p).testBit i = flipBit p.1 (fun j => decide (j ∈ p.2)) i := by
  exact Nat.testBit_ofBits_lt _ _ hi

theorem flipEncoding_injOn (N : ℕ) :
    Set.InjOn (flipEncoding (N+1)) {p : Bool × Finset ℕ | p.2 ⊆ range N} := by
  intro x hx y hy he
  have bits_same (i : ℕ) (hi : i < N+1) :
      flipBit x.1 (fun j => decide (j ∈ x.2)) i =
        flipBit y.1 (fun j => decide (j ∈ y.2)) i := by
    have h := congrArg (fun u : ℕ => u.testBit i) he
    simpa only [flipEncoding_testBit _ _ _ hi] using h
  apply Prod.ext
  · exact bits_same 0 (by omega)
  · ext i
    by_cases hi : i < N
    · have hb := congrArg₂ (fun a b : Bool => a ^^ b)
        (bits_same i (by omega)) (bits_same (i+1) (by omega))
      rw [flipBit_transition, flipBit_transition] at hb
      simpa only [decide_eq_decide] using hb
    · have hxi : i ∉ x.2 := fun h => hi (mem_range.mp (hx h))
      have hyi : i ∉ y.2 := fun h => hi (mem_range.mp (hy h))
      simp [hxi, hyi]

def fixedFlips (N K : ℕ) : Finset (Bool × Finset ℕ) :=
  (univ : Finset Bool) ×ˢ (range N).powersetCard K

def fixedWords (N K : ℕ) : Finset ℕ :=
  (fixedFlips N K).image (flipEncoding (N+1))

theorem fixedFlips_valid (N K : ℕ) {p : Bool × Finset ℕ} (hp : p ∈ fixedFlips N K) :
    p.2 ⊆ range N :=
  (mem_powersetCard.mp (mem_product.mp hp).2).1

theorem fixedWords_card (N K : ℕ) : (fixedWords N K).card = 2 * N.choose K := by
  rw [fixedWords, card_image_of_injOn]
  · simp [fixedFlips]
  · intro a ha b hb h
    exact flipEncoding_injOn N (fixedFlips_valid N K ha) (fixedFlips_valid N K hb) h

theorem fixedWords_subset (N K : ℕ) : fixedWords N K ⊆ range (2^(N+1)) := by
  intro k hk
  obtain ⟨p, _, rfl⟩ := mem_image.mp hk
  exact mem_range.mpr (flipEncoding_lt (N+1) p)

end GoldbachGrid

open Finset

namespace GoldbachGrid

/-- Choosing k positions, with their intersection with a fixed window prescribed. -/
theorem card_inter_pattern {α : Type*} [DecidableEq α]
    (pool window pattern : Finset α) (k : ℕ)
    (hwu : window ⊆ pool) (hpw : pattern ⊆ window) (hpk : pattern.card ≤ k) :
    ((pool.powersetCard k).filter (fun s => s ∩ window = pattern)).card =
      (pool.card - window.card).choose (k - pattern.card) := by
  have hneg : window \ pattern ⊆ pool :=
    fun _ ha => hwu (Finset.mem_sdiff.mp ha).1
  have hpos : pattern ⊆ pool \ (window \ pattern) := by
    intro a ha
    exact mem_sdiff.mpr ⟨hwu (hpw ha), fun h => (mem_sdiff.mp h).2 ha⟩
  have hfilters :
      (pool.powersetCard k).filter (fun s => s ∩ window = pattern) =
        ((pool \ (window \ pattern)).powersetCard k).filter (pattern ⊆ ·) := by
    ext s
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨hsu, hsk⟩, h⟩
      refine ⟨⟨?_, hsk⟩, ?_⟩
      · intro x hx
        refine mem_sdiff.mpr ⟨hsu hx, ?_⟩
        intro hxs
        obtain ⟨hxw, hxp⟩ := mem_sdiff.mp hxs
        exact hxp (h ▸ mem_inter.mpr ⟨hx, hxw⟩)
      · intro x hx
        have hh : x ∈ s ∩ window := h.symm ▸ hx
        exact (mem_inter.mp hh).1
    · rintro ⟨⟨hsu, hsk⟩, hps⟩
      refine ⟨⟨fun x hx => (mem_sdiff.mp (hsu hx)).1, hsk⟩, ?_⟩
      ext x
      constructor
      · intro hx
        obtain ⟨hxs, hxw⟩ := mem_inter.mp hx
        by_contra hxp
        exact (mem_sdiff.mp (hsu hxs)).2 (mem_sdiff.mpr ⟨hxw, hxp⟩)
      · intro hx
        exact mem_inter.mpr ⟨hps hx, hpw hx⟩
  rw [hfilters, card_filter_powersetCard_subset _ _ _ hpos hpk,
    card_sdiff_of_subset hneg, card_sdiff_of_subset hpw]
  have hwcard : window.card ≤ pool.card := card_le_card hwu
  have hpcard : pattern.card ≤ window.card := card_le_card hpw
  rw [show pool.card - (window.card - pattern.card) - pattern.card =
    pool.card - window.card by omega]

/-- Counts for an exact finite-population pattern, with no divisions over naturals. -/
theorem choose_pattern (N K r s : ℕ) (hr : r ≤ K) (hs : s ≤ N - K) (hk : K ≤ N) :
    (N - (r+s)).choose (K - r) * N.descFactorial (r+s) =
      N.choose K * K.descFactorial r * (N-K).descFactorial s := by
  have hrest : (N - (r+s)) - (K-r) = (N-K)-s := by omega
  have hsize : K - r ≤ N - (r+s) := by omega
  have hwindow : r+s ≤ N := by omega
  have hleft := Nat.choose_mul_factorial_mul_factorial hsize
  rw [hrest] at hleft
  have hfull := Nat.choose_mul_factorial_mul_factorial hk
  have hwindowFact := Nat.factorial_mul_descFactorial hwindow
  have hyes := Nat.factorial_mul_descFactorial hr
  have hno := Nat.factorial_mul_descFactorial hs
  apply Nat.mul_right_cancel (m := (K-r).factorial * ((N-K)-s).factorial)
    (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
  calc
    _ = ((N-(r+s)).choose (K-r) * (K-r).factorial * ((N-K)-s).factorial) *
        N.descFactorial (r+s) := by ring
    _ = N.factorial := by rw [hleft, hwindowFact]
    _ = N.choose K * K.factorial * (N-K).factorial := hfull.symm
    _ = _ := by rw [← hyes, ← hno]; ring

/-- Lower bound for each normalized falling factorial at t >= 2000. -/
theorem normalized_factorial (a t r : ℕ) (ht : 2000 ≤ t) (ha : 1 ≤ a) (hr : r ≤ 11) :
    ((a*2000).descFactorial r : ℝ) / (2000000 : ℝ)^r ≤
      ((a*t).descFactorial r : ℝ) / ((1000*t : ℕ) : ℝ)^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have har : r ≤ a * 2000 := by nlinarith [Nat.zero_le ((a-1)*2000)]
    have hat : r ≤ a * t := har.trans (Nat.mul_le_mul_left a ht)
    have hpos : (0 : ℝ) < ((1000*t : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < 1000 * t by omega)
    have hfactor : ((a*2000-r : ℕ):ℝ) / 2000000 ≤
        ((a*t-r : ℕ):ℝ) / ((1000*t : ℕ):ℝ) := by
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ)<2000000) hpos]
      push_cast [Nat.cast_sub har, Nat.cast_sub hat]
      have hdiff : (0:ℝ) ≤ (r:ℝ) * ((t:ℝ)-2000) := by
        exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast ht))
      nlinarith only [hdiff]
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul,
      pow_succ', pow_succ', mul_div_mul_comm, mul_div_mul_comm]
    exact mul_le_mul hfactor (ih (by omega)) (by positivity) (by positivity)


noncomputable def probabilityLower (r : ℕ) : ℝ :=
  ((170000 : ℕ).descFactorial r : ℝ) * ((1830000 : ℕ).descFactorial (11-r) : ℝ)
    / (2000000 : ℝ)^11

theorem choose_lower (t r : ℕ) (ht : 2000 ≤ t) (hr : r ≤ 11) :
    probabilityLower r * ((1000*t).choose (85*t) : ℝ) ≤
      ((1000*t-11).choose (85*t-r) : ℝ) := by
  let N := 1000*t
  let K := 85*t
  let s := 11-r
  have hKN : K ≤ N := by dsimp [K, N]; omega
  have hrK : r ≤ K := by dsimp [K]; omega
  have hsK : s ≤ N-K := by dsimp [s, N, K]; omega
  have hrs : r+s = 11 := by dsimp [s]; omega
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by dsimp [N]; omega)
  have he := choose_pattern N K r s hrK hsK hKN
  rw [hrs] at he
  have hcast :
      (↑((N-11).choose (K-r)) : ℝ) * ↑(N.descFactorial 11) =
        (↑(N.choose K) : ℝ) * ↑(K.descFactorial r) * ↑((N-K).descFactorial s) := by
    exact_mod_cast he
  have hR := normalized_factorial 85 t r ht (by decide) hr
  have hS := normalized_factorial 915 t s ht (by decide) (by dsimp [s]; omega)
  have hdiff : 915*t = N-K := by dsimp [N, K]; omega
  rw [hdiff] at hS
  change probabilityLower r * (N.choose K : ℝ) ≤ (((N-11).choose (K-r)):ℝ)
  calc
    _ = ((↑((170000 : ℕ).descFactorial r) : ℝ) / (2000000 : ℝ)^r *
         ((1830000 : ℕ).descFactorial s : ℝ) / (2000000 : ℝ)^s) *
          (N.choose K : ℝ) := by
        unfold probabilityLower
        change (_ * _ / (2000000 : ℝ)^11) * _ = _
        have hp : (2000000 : ℝ)^11 = (2000000 : ℝ)^r * (2000000 : ℝ)^s := by
          rw [← pow_add, hrs]
        rw [hp]
        ring
    _ ≤ (((K.descFactorial r : ℝ) / (N : ℝ)^r) *
        (((N-K).descFactorial s : ℝ) / (N : ℝ)^s)) * (N.choose K : ℝ) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hR hS (by positivity) (by positivity)) (by positivity)
    _ = (((N-11).choose (K-r) : ℝ) * (N.descFactorial 11 : ℝ)) / (N : ℝ)^11 := by
      rw [hcast, ← hrs, pow_add]
      ring
    _ ≤ _ := by
      apply (div_le_iff₀ (pow_pos hN 11)).mpr
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.descFactorial_le_pow N 11))
        (by positivity)

end GoldbachGrid

namespace GoldbachGrid

/-- The real part of one term in the frozen grid sum. -/
noncomputable def phaseScore (L j k : ℕ) : ℝ :=
  (Complex.exp
    (↑((2 : ℝ) * Real.pi *
      (↑⌊(65536 : ℝ) * (2 : ℝ)^j * ((k : ℝ) / (2 : ℝ)^L)⌋ : ℝ) / 65536) * Complex.I)).re

private theorem neg_one_le_phaseScore (L j k : ℕ) : -1 ≤ phaseScore L j k := by
  unfold phaseScore
  rw [Complex.exp_ofReal_mul_I_re]
  exact Real.neg_one_le_cos _

/-- The phase-average estimate on full windows also bounds the sum over all phases.
The last eleven phases may be bounded individually by `-1`. -/
theorem mean_of_local (N K : ℕ) (hN : 2000000 ≤ N) (hK : K ≤ N)
    (hlocal : ∀ j : ℕ, j + 12 ≤ N + 1 →
      (74506 / 100000 : ℝ) * (fixedWords N K).card ≤
        ∑ k ∈ fixedWords N K, phaseScore (N+1) j k) :
    (745 / 1000 : ℝ) * ((N+1 : ℕ) : ℝ) * (fixedWords N K).card <
      ∑ k ∈ fixedWords N K, ∑ j ∈ Finset.range (N+1), phaseScore (N+1) j k := by
  let W := fixedWords N K
  let L := N+1
  let S (j : ℕ) : ℝ := ∑ k ∈ W, phaseScore L j k
  have hlen : L-11+11 = L := by dsimp [L]; omega
  have hcard : 0 < (W.card : ℝ) := by
    have : 0 < W.card := by
      rw [show W.card = 2*N.choose K from fixedWords_card N K]
      exact Nat.mul_pos (by decide) (Nat.choose_pos hK)
    exact_mod_cast this
  have hhead : ((L-11 : ℕ) : ℝ) * ((74506 / 100000 : ℝ) * W.card) ≤
      ∑ j ∈ Finset.range (L-11), S j := by
    calc
      _ = ∑ _j ∈ Finset.range (L-11), (74506 / 100000 : ℝ) * W.card := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have h := Finset.mem_range.mp hj
        exact hlocal j (by dsimp [L] at h; omega)
  have htail : (11 : ℝ) * (-(W.card : ℝ)) ≤
      ∑ j ∈ Finset.range 11, S (L-11+j) := by
    calc
      _ = ∑ _j ∈ Finset.range 11, -(W.card : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j _
        calc
          -(W.card : ℝ) = ∑ _k ∈ W, (-1 : ℝ) := by simp
          _ ≤ S (L-11+j) := Finset.sum_le_sum (fun k _ => neg_one_le_phaseScore _ _ k)
  have hstrict :
      (745 / 1000 : ℝ) * (L : ℝ) <
        ((L-11 : ℕ) : ℝ) * (74506 / 100000 : ℝ) - 11 := by
    have hlen' : ((L-11 : ℕ) : ℝ) + 11 = (L : ℝ) := by exact_mod_cast hlen
    have hN' : (2000001 : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast (show 2000001 ≤ L by dsimp [L]; omega)
    linarith only [hlen', hN']
  calc
    _ < (((L-11 : ℕ) : ℝ) * (74506 / 100000 : ℝ) - 11) * (W.card : ℝ) :=
      mul_lt_mul_of_pos_right hstrict hcard
    _ = ((L-11 : ℕ) : ℝ) * ((74506 / 100000 : ℝ) * W.card) +
        11 * (-(W.card : ℝ)) := by ring
    _ ≤ (∑ j ∈ Finset.range (L-11), S j) + (∑ j ∈ Finset.range 11, S (L-11+j)) :=
      (add_le_add hhead htail)
    _ = ∑ j ∈ Finset.range L, S j := by rw [← Finset.sum_range_add, hlen]
    _ = _ := Finset.sum_comm

theorem construct_from_local
    (hlocal : ∀ t : ℕ, 2000 ≤ t → ∀ j : ℕ, j + 12 ≤ 1000*t+1 →
      (74506 / 100000 : ℝ) * (fixedWords (1000*t) (85*t)).card ≤
        ∑ k ∈ fixedWords (1000*t) (85*t), phaseScore (1000*t+1) j k) :
    (have trunc : ℕ → ℝ → ℂ := fun n x =>
      ∑ j ∈ Finset.range n, Complex.exp
        (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ)^j * x⌋ / 65536) * Complex.I)
    ∀ t : ℕ, 2000 ≤ t → have N := 1000*t+1
      ∃ W ⊆ Finset.range (2^N), 2*(1000*t).choose (85*t) ≤ W.card ∧
      (745 / 1000 : ℝ) * (N : ℝ) * W.card < ∑ k ∈ W, (trunc N ((k : ℝ)/2^N)).re) := by
  dsimp only
  intro t ht
  refine ⟨fixedWords (1000*t) (85*t), fixedWords_subset _ _, (fixedWords_card _ _).ge, ?_⟩
  simpa only [phaseScore, Complex.re_sum] using
    mean_of_local (1000*t) (85*t) (by omega) (by omega) (hlocal t ht)

end GoldbachGrid

open Finset

namespace GoldbachGrid

open GoldbachGridCertificate

def window (d : ℕ) : Finset ℕ := (range 11).image (fun i => i+d)

def windowPattern (d q : ℕ) : Finset ℕ := (prefixPattern q).image (fun i => i+d)

theorem windowPattern_subset (d q : ℕ) : windowPattern d q ⊆ window d :=
  image_mono _ (prefixPattern_subset q)

theorem window_card (d : ℕ) : (window d).card = 11 := by
  rw [window, card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h), card_range]

theorem windowPattern_card (d q : ℕ) : (windowPattern d q).card = (prefixPattern q).card :=
  card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)

theorem window_subset {d N : ℕ} (hd : d+11 ≤ N) : window d ⊆ range N := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
  simp only [mem_range] at hi ⊢
  omega

theorem windowPattern_injective (d : ℕ) {a b : ℕ} (ha : a < 2048) (hb : b < 2048)
    (h : windowPattern d a = windowPattern d b) : a = b := by
  apply prefixPattern_injOn ha hb
  ext i
  have hmem (q : ℕ) : i+d ∈ windowPattern d q ↔ i ∈ prefixPattern q := by
    unfold windowPattern
    constructor
    · intro h
      obtain ⟨a, ha, he⟩ := mem_image.mp h
      exact (Nat.add_right_cancel he) ▸ ha
    · exact mem_image_of_mem _
  rw [← hmem a, ← hmem b, h]

def indexPrefix (N j : ℕ) (p : Bool × Finset ℕ) : ℕ :=
  DyadicWord.prefix12 (N+1) j (flipEncoding (N+1) p)

theorem indexPrefix_lt (N j : ℕ) (p : Bool × Finset ℕ) : indexPrefix N j p < 4096 :=
  Nat.mod_lt _ (by decide)

theorem indexPrefix_bit (N j : ℕ) {i : ℕ} (hj : j+12 ≤ N+1) (hi : i < 12)
    (p : Bool × Finset ℕ) :
    (indexPrefix N j p).testBit i =
      flipBit p.1 (fun x => decide (x ∈ p.2)) (i+(N+1-(j+12))) := by
  unfold indexPrefix DyadicWord.prefix12
  rw [show (4096 : ℕ) = 2^12 by decide, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp only [hi, decide_true, Bool.true_and]
  exact flipEncoding_testBit (N+1) p _ (by omega)

theorem indexPrefix_pattern (N j : ℕ) (hj : j+12 ≤ N+1) (p : Bool × Finset ℕ) :
    windowPattern (N+1-(j+12)) (canonical (indexPrefix N j p)) =
      p.2 ∩ window (N+1-(j+12)) := by
  let d := N+1-(j+12)
  have hlocal (i : ℕ) (hi : i < 11) :
      i ∈ prefixPattern (canonical (indexPrefix N j p)) ↔ i+d ∈ p.2 := by
    rw [prefixPattern_canonical _ (indexPrefix_lt _ _ _)]
    simp only [prefixPattern, mem_filter, mem_range, hi, true_and]
    rw [indexPrefix_bit _ _ hj (by omega), indexPrefix_bit _ _ hj (by omega),
      show i+1+(N+1-(j+12)) = i+(N+1-(j+12))+1 by omega, flipBit_transition]
    simp [d]
  ext a
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := mem_image.mp h
    have hr := mem_filter.mp hi |>.1
    exact mem_inter.mpr ⟨(hlocal i (mem_range.mp hr)).mp hi, mem_image_of_mem _ hr⟩
  · intro h
    obtain ⟨hp, hw⟩ := mem_inter.mp h
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hw
    exact mem_image_of_mem _ ((hlocal i (mem_range.mp hi)).mpr hp)

theorem indexPrefix_eq_iff (N j q : ℕ) (hj : j+12 ≤ N+1) (hq : q < 2048)
    (p : Bool × Finset ℕ) :
    canonical (indexPrefix N j p) = q ↔
      p.2 ∩ window (N+1-(j+12)) = windowPattern (N+1-(j+12)) q := by
  rw [← indexPrefix_pattern N j hj p]
  constructor
  · intro h
    rw [h]
  · exact windowPattern_injective _ (canonical_lt _ (indexPrefix_lt _ _ _)) hq

theorem prefix_fiber_card (t j q : ℕ) (_ht : 2000 ≤ t)
    (hj : j+12 ≤ 1000*t+1) (hq : q < 2048) :
    ((fixedFlips (1000*t) (85*t)).filter
        (fun p => canonical (indexPrefix (1000*t) j p) = q)).card =
      2 * (1000*t-11).choose (85*t - transitions q) := by
  let N := 1000*t
  let K := 85*t
  let d := N+1-(j+12)
  have hsubset : window d ⊆ range N := window_subset (by dsimp [d,N]; omega)
  have hpattern : (windowPattern d q).card ≤ K := by
    have hc := card_le_card (windowPattern_subset d q)
    rw [window_card] at hc
    dsimp [K]
    omega
  have hproducts :
      (fixedFlips N K).filter (fun p => canonical (indexPrefix N j p) = q) =
        (univ : Finset Bool) ×ˢ ((range N).powersetCard K).filter
              (fun s => s ∩ window d = windowPattern d q) := by
    ext p
    rw [mem_filter, fixedFlips, mem_product, mem_product, mem_filter,
      indexPrefix_eq_iff _ _ _ hj hq]
    simp only [mem_univ, true_and]
    rfl
  change _ = 2 * (N-11).choose (K-transitions q)
  rw [hproducts, card_product, card_inter_pattern _ _ _ _ hsubset
    (windowPattern_subset d q) hpattern]
  simp only [card_univ, Fintype.card_bool, card_range, window_card, windowPattern_card,
    card_prefixPattern]
  rfl

private theorem endpoint_canonical {q : ℕ} (hq : q < 4096) :
    DyadicWord.endpoint12 q = ((canonical q : ℝ)+1)/4096 := by
  unfold DyadicWord.endpoint12 canonical
  split_ifs with h
  · rfl
  · rw [Nat.cast_sub (show q ≤ 4095 by omega)]
    push_cast
    ring

theorem score_shifted_lower (N j : ℕ) (hj : j+12 ≤ N+1) (p : Bool × Finset ℕ) :
    (shiftedCosineLower (canonical (indexPrefix N j p)) : ℝ) / 1000000000 ≤
      1 + phaseScore (N+1) j (flipEncoding (N+1) p) := by
  have hq := indexPrefix_lt N j p
  refine (shiftedCosineLower_le _ (canonical_lt _ hq)).trans ?_
  have h := DyadicWord.phase16_cos_lower (k := flipEncoding (N+1) p) hj
  change Real.cos (2 * Real.pi * DyadicWord.endpoint12 (indexPrefix N j p)) ≤ _ at h
  rw [endpoint_canonical hq, show ∀ x : ℝ, 2*Real.pi*((x+1)/4096) =
    Real.pi*(x+1)/2048 by intro x; ring] at h
  exact add_le_add_right h 1


private theorem rational_average_lower :
    (174506 / 100000 : ℝ) ≤ ∑ q ∈ range 2048,
      (shiftedCosineLower q : ℝ) / 1000000000 * probabilityLower (transitions q) := by
  have h : (174506:ℝ) * (aggregateDen : ℝ) < 100000 * (aggregate : ℝ) := by
    exact_mod_cast weighted_mean_lower
  have hd : 0 < (aggregateDen : ℝ) := by
    norm_num [aggregateDen]
  calc
    _ ≤ (aggregate : ℝ) / (aggregateDen : ℝ) := by
      apply (div_le_div_iff₀ (by norm_num : (0:ℝ) < 100000) hd).mpr
      linarith only [h]
    _ = _ := by
      rw [aggregate_eq_sum, Nat.cast_sum, Finset.sum_div]
      apply sum_congr rfl
      intro q _
      simp only [probabilityLower, aggregateDen, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

theorem local_average (t : ℕ) (ht : 2000 ≤ t) (j : ℕ) (hj : j+12 ≤ 1000*t+1) :
    (74506 / 100000 : ℝ) * (fixedWords (1000*t) (85*t)).card ≤
      ∑ k ∈ fixedWords (1000*t) (85*t), phaseScore (1000*t+1) j k := by
  let N := 1000*t
  let K := 85*t
  let W := fixedFlips N K
  let label (p : Bool × Finset ℕ) := canonical (indexPrefix N j p)
  let C (q : ℕ) : ℝ := (shiftedCosineLower q : ℝ) / 1000000000
  have hcoeff (q : ℕ) : 0 ≤ C q := by dsimp [C]; positivity
  have hlabels (p : Bool × Finset ℕ) : label p ∈ range 2048 :=
    mem_range.mpr (canonical_lt _ (indexPrefix_lt _ _ _))
  have hcard : W.card = 2 * N.choose K := by simp [W, fixedFlips]
  have hfiber (q : ℕ) (hq : q ∈ range 2048) :
      probabilityLower (transitions q) * (W.card : ℝ) ≤
        ((W.filter fun p => label p = q).card : ℝ) := by
    have hc := prefix_fiber_card t j q ht hj (mem_range.mp hq)
    have htrans : transitions q ≤ 11 := by
      have hle := card_le_card (prefixPattern_subset q)
      rw [card_range, card_prefixPattern] at hle
      exact hle
    change _ ≤ (((fixedFlips N K).filter
      (fun p => canonical (indexPrefix N j p) = q)).card : ℝ)
    rw [hcard, hc]
    push_cast
    have hweight := choose_lower t (transitions q) ht htrans
    calc
      _ = 2 * (probabilityLower (transitions q) * (N.choose K : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hweight (by norm_num : (0:ℝ) ≤ 2)
  have hweighted : (174506 / 100000 : ℝ) * (W.card : ℝ) ≤
      ∑ p ∈ W, C (label p) := by
    calc
      _ ≤ (∑ q ∈ range 2048, C q * probabilityLower (transitions q)) * (W.card : ℝ) :=
        mul_le_mul_of_nonneg_right rational_average_lower (by positivity)
      _ = ∑ q ∈ range 2048, C q * (probabilityLower (transitions q) * (W.card : ℝ)) := by
        rw [Finset.sum_mul]
        apply sum_congr rfl
        intro q _
        ring
      _ ≤ ∑ q ∈ range 2048, C q * ((W.filter fun p => label p = q).card : ℝ) := by
        exact sum_le_sum (fun q hq => mul_le_mul_of_nonneg_left (hfiber q hq) (hcoeff q))
      _ = ∑ p ∈ W, C (label p) := by
        rw [← sum_fiberwise_of_maps_to (fun p _ => hlabels p) (fun p => C (label p))]
        apply sum_congr rfl
        intro q _
        rw [mul_comm]
        simp only [← nsmul_eq_mul, ← sum_const]
        apply sum_congr rfl
        intro p hp
        rw [(mem_filter.mp hp).2]
  have hscore :
      ∑ p ∈ W, C (label p) ≤
        ∑ p ∈ W, (1 + phaseScore (N+1) j (flipEncoding (N+1) p)) :=
    sum_le_sum (fun p _ => score_shifted_lower N j hj p)
  have hboth := hweighted.trans hscore
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one] at hboth
  have himage :
      ∑ k ∈ fixedWords N K, phaseScore (N+1) j k =
        ∑ p ∈ W, phaseScore (N+1) j (flipEncoding (N+1) p) := by
    unfold fixedWords
    apply sum_image
    intro a ha b hb h
    exact flipEncoding_injOn N (fixedFlips_valid N K ha) (fixedFlips_valid N K hb) h
  change (74506 / 100000 : ℝ) * (fixedWords N K).card ≤ _
  rw [himage, fixedWords_card, ← hcard]
  linarith only [hboth]

end GoldbachGrid

theorem Conjectures.Cuts.Taskb98f3332b3a9cab8abb1dd40 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => ∑ x3 ∈ Finset.range x1, Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ x3 * x2⌋ / (65536 : ℝ)) * Complex.I); ∀ (x2 : ℕ),   (2000 : ℕ) ≤ x2 →     have x4 : ℕ := (1000 : ℕ) * x2 + (1 : ℕ);     ∃ x5 ⊆ Finset.range ((2 : ℕ) ^ x4), (2 : ℕ) * ((1000 : ℕ) * x2).choose ((85 : ℕ) * x2) ≤ x5.card ∧ (745 / 1000 : ℝ) * ↑x4 * ↑x5.card < ∑ x6 ∈ x5, (x1 x4 (↑x6 / (2 : ℝ) ^ x4)).re) := by
  exact GoldbachGrid.construct_from_local GoldbachGrid.local_average
