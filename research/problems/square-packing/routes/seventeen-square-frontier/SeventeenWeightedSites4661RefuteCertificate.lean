import Mathlib

namespace OrbitWitness4661

/-- 与原冻结命题一致的开单位正方形内部谓词 -/
def inside (x y a b X Y : ℝ) : Prop :=
  |a * (X - x) + b * (Y - y)| < 1 / 2 ∧ |(-b) * (X - x) + a * (Y - y)| < 1 / 2

structure Orbit where
  cx : ℤ
  cy : ℤ
  p  : ℤ
  q  : ℤ
  r  : ℤ
  w  : ℕ
deriving Repr, DecidableEq

structure ExactSq where
  cx : ℤ
  cy : ℤ
  p  : ℤ
  q  : ℤ
  r  : ℤ
  w  : ℕ
deriving Repr, DecidableEq

/-- 70 行精确有理轨道代表（与已复算的原始 CSV 逐行一致） -/
def orbits70 : List Orbit := [
  ⟨500,500,1,0,1,4000000⟩, ⟨1500,500,1,0,1,5082998⟩, ⟨1500,1500,1,0,1,866484⟩,
  ⟨2150,2150,1,0,1,236301⟩, ⟨2150,500,1,0,1,1406728⟩, ⟨2330,1400,4,3,5,707697⟩,
  ⟨1400,1325,3,4,5,305645⟩, ⟨2075,1500,9,40,41,146025⟩, ⟨2175,1475,8,15,17,172119⟩,
  ⟨1425,1275,15,8,17,186547⟩, ⟨1400,1325,4,3,5,209273⟩, ⟨2150,1525,88,105,137,73155⟩,
  ⟨2025,1550,5,12,13,163297⟩, ⟨1450,1300,21,20,29,23217⟩, ⟨2175,1550,40,9,41,30479⟩,
  ⟨2175,707,20,21,29,4939⟩, ⟨2325,2300,4,3,5,19383⟩, ⟨2325,1375,4,3,5,70686⟩,
  ⟨1450,1225,15,8,17,16009⟩, ⟨2175,598,40,9,41,4939⟩, ⟨1375,1350,4,3,5,4939⟩,
  ⟨2325,2325,4,3,5,6372⟩, ⟨1400,1350,20,21,29,4939⟩, ⟨1400,1325,120,119,169,460426⟩,
  ⟨2100,1500,5,12,13,4939⟩, ⟨2325,1825,21,20,29,350429⟩, ⟨2330,1825,21,20,29,218615⟩,
  ⟨2200,1550,9,40,41,77533⟩, ⟨2150,1500,40,9,41,4939⟩, ⟨2175,1575,40,9,41,190355⟩,
  ⟨2125,2125,1,0,1,93698⟩, ⟨2330,2275,120,119,169,19383⟩, ⟨2200,1450,5,12,13,35375⟩,
  ⟨2325,1400,4,3,5,110131⟩, ⟨2150,707,21,20,29,13540⟩, ⟨1850,725,8,15,17,23417⟩,
  ⟨2325,1225,20,21,29,9239⟩, ⟨2250,1250,88,105,137,2469⟩, ⟨2100,1500,9,40,41,186498⟩,
  ⟨2100,1525,9,40,41,18595⟩, ⟨2325,1350,3,4,5,2391⟩, ⟨2175,1500,40,9,41,132420⟩,
  ⟨1475,1225,15,8,17,4939⟩, ⟨2275,1350,105,88,137,3741⟩, ⟨2175,1525,40,9,41,60843⟩,
  ⟨2225,1350,8,15,17,9799⟩, ⟨1525,1200,21,20,29,23417⟩, ⟨2075,1525,3,4,5,65349⟩,
  ⟨2075,1550,88,105,137,134962⟩, ⟨2100,1525,88,105,137,8333⟩, ⟨2225,2200,20,21,29,12269⟩,
  ⟨2275,2150,12,5,13,32735⟩, ⟨2250,2150,12,5,13,2469⟩, ⟨2225,1275,20,21,29,2469⟩,
  ⟨2200,707,20,21,29,297160⟩, ⟨2200,708,120,119,169,97178⟩, ⟨2200,677,8,15,17,103635⟩,
  ⟨2200,700,3,4,5,40314⟩, ⟨2330,2325,20,21,29,8345⟩, ⟨2200,700,4,3,5,4939⟩,
  ⟨2330,1250,120,119,169,2469⟩, ⟨1400,1350,3,4,5,153368⟩, ⟨2200,707,21,20,29,148430⟩,
  ⟨1400,1325,88,105,137,47303⟩, ⟨2330,1300,4,3,5,2469⟩, ⟨2150,700,4,3,5,18479⟩,
  ⟨2150,705,105,88,137,9877⟩, ⟨2275,1375,8,15,17,18557⟩, ⟨2275,1300,88,105,137,4939⟩,
  ⟨1375,1350,21,20,29,18479⟩
]

/-- 每条轨道保留全部 8 条 D4 像（带重数） -/
def expandOrbit (o : Orbit) : List ExactSq :=
  [ ⟨o.cx,        o.cy,         o.p,  o.q, o.r, o.w⟩
  , ⟨o.cx,        4661 - o.cy,  o.p, -o.q, o.r, o.w⟩
  , ⟨4661 - o.cx, o.cy,        -o.p,  o.q, o.r, o.w⟩
  , ⟨4661 - o.cx, 4661 - o.cy, -o.p, -o.q, o.r, o.w⟩
  , ⟨o.cy,        o.cx,         o.q,  o.p, o.r, o.w⟩
  , ⟨o.cy,        4661 - o.cx,  o.q, -o.p, o.r, o.w⟩
  , ⟨4661 - o.cy, o.cx,        -o.q,  o.p, o.r, o.w⟩
  , ⟨4661 - o.cy, 4661 - o.cx, -o.q, -o.p, o.r, o.w⟩ ]

def squares560 : List ExactSq := orbits70.flatMap expandOrbit

def CAP : ℕ := 8015919

/-! ### 一、基础整数校验（全部由 kernel `decide` 闭合） -/

set_option maxRecDepth 12000 in
theorem squares560_length : squares560.length = 560 := by decide

set_option maxRecDepth 12000 in
theorem squares560_total_weight : (squares560.map (·.w)).sum = 136270632 := by decide

set_option maxRecDepth 12000 in
theorem strict_over_17_witness : 17 * 8014706 < (squares560.map (·.w)).sum := by decide

set_option maxRecDepth 12000 in
theorem strict_over_17_cap : 17 * CAP < (squares560.map (·.w)).sum := by decide

/-! ### 二、560 条样本几何合法性证明 -/

def sqValidReal (s : ExactSq) : Prop :=
  let x : ℝ := (s.cx : ℝ) / 1000
  let y : ℝ := (s.cy : ℝ) / 1000
  let a : ℝ := (s.p : ℝ) / s.r
  let b : ℝ := (s.q : ℝ) / s.r
  0 < s.r ∧
  a ^ 2 + b ^ 2 = 1 ∧
  |a| + |b| ≤ 2 * x ∧
  |a| + |b| ≤ 2 * ((4661 / 1000 : ℝ) - x) ∧
  |a| + |b| ≤ 2 * y ∧
  |a| + |b| ≤ 2 * ((4661 / 1000 : ℝ) - y)

def sqValidInt (s : ExactSq) : Bool :=
  let ab : ℤ := (Int.natAbs s.p : ℤ) + (Int.natAbs s.q : ℤ)
  decide (0 < s.r) &&
  decide (s.p ^ 2 + s.q ^ 2 = s.r ^ 2) &&
  decide (ab * 1000 ≤ 2 * s.cx * s.r) &&
  decide (ab * 1000 ≤ 2 * (4661 - s.cx) * s.r) &&
  decide (ab * 1000 ≤ 2 * s.cy * s.r) &&
  decide (ab * 1000 ≤ 2 * (4661 - s.cy) * s.r)

set_option maxRecDepth 12000 in
theorem all_squares560_validInt : squares560.all sqValidInt = true := by decide

lemma int_natAbs_cast_eq_abs (z : ℤ) : ((Int.natAbs z : ℤ) : ℝ) = |(z : ℝ)| := by
  rw [Int.natCast_natAbs, Int.cast_abs]

lemma sqValidInt_sound (s : ExactSq) (h : sqValidInt s = true) : sqValidReal s := by
  simp only [sqValidInt, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hr, hpyth⟩, hx1⟩, hx2⟩, hy1⟩, hy2⟩
  have hrR : (0 : ℝ) < s.r := by exact_mod_cast hr
  have hrne : (s.r : ℝ) ≠ 0 := hrR.ne'
  have hpythR : (s.p : ℝ) ^ 2 + (s.q : ℝ) ^ 2 = (s.r : ℝ) ^ 2 := by exact_mod_cast hpyth
  have hab : |(s.p : ℝ) / s.r| + |(s.q : ℝ) / s.r| =
      (((Int.natAbs s.p : ℤ) + (Int.natAbs s.q : ℤ) : ℤ) : ℝ) / s.r := by
    rw [abs_div, abs_div, abs_of_pos hrR, ← add_div]
    simp [int_natAbs_cast_eq_abs]
  have wall : ∀ c : ℤ,
      (((Int.natAbs s.p : ℤ) + (Int.natAbs s.q : ℤ)) * 1000 ≤ 2 * c * s.r) →
      |(s.p : ℝ) / s.r| + |(s.q : ℝ) / s.r| ≤ 2 * ((c : ℝ) / 1000) := by
    intro c hc
    rw [hab]
    have hcR : (((Int.natAbs s.p : ℤ) + (Int.natAbs s.q : ℤ) : ℤ) : ℝ) * 1000 ≤ 2 * (c : ℝ) * s.r := by
      exact_mod_cast hc
    rw [div_le_iff₀ hrR]
    linarith
  refine ⟨hr, ?_, wall s.cx hx1, ?_, wall s.cy hy1, ?_⟩
  · field_simp [hrne]; linarith
  · have := wall (4661 - s.cx) hx2
    push_cast at this; linarith
  · have := wall (4661 - s.cy) hy2
    push_cast at this; linarith

theorem squares560_valid : ∀ s ∈ squares560, sqValidReal s := by
  intro s hs
  exact sqValidInt_sound s (List.all_eq_true.mp all_squares560_validInt s hs)

/-! ### 三、实数荷载定义与严格开半平面等价刻画 -/

def sqInside (s : ExactSq) (X Y : ℝ) : Prop :=
  inside ((s.cx : ℝ) / 1000) ((s.cy : ℝ) / 1000) ((s.p : ℝ) / s.r) ((s.q : ℝ) / s.r) X Y

noncomputable def loadList (L : List ExactSq) (X Y : ℝ) : ℕ := by
  classical
  exact (L.map fun s => if sqInside s X Y then s.w else 0).sum

/-- 严格开半平面 A*X + B*Y < C -/
structure HP where
  A : ℤ
  B : ℤ
  C : ℤ

def getHPs (s : ExactSq) : Fin 4 → HP
  | ⟨0, _⟩ => ⟨ 2000 * s.p,  2000 * s.q,  (2 * s.p * s.cx + 2 * s.q * s.cy) + 1000 * s.r⟩
  | ⟨1, _⟩ => ⟨-2000 * s.p, -2000 * s.q, -(2 * s.p * s.cx + 2 * s.q * s.cy) + 1000 * s.r⟩
  | ⟨2, _⟩ => ⟨-2000 * s.q,  2000 * s.p, (-2 * s.q * s.cx + 2 * s.p * s.cy) + 1000 * s.r⟩
  | ⟨3, _⟩ => ⟨ 2000 * s.q, -2000 * s.p, -(-2 * s.q * s.cx + 2 * s.p * s.cy) + 1000 * s.r⟩

lemma sqInside_iff_hps (s : ExactSq) (hr : 0 < s.r) (X Y : ℝ) :
    sqInside s X Y ↔ ∀ k : Fin 4, ((getHPs s k).A : ℝ) * X + ((getHPs s k).B : ℝ) * Y < ((getHPs s k).C : ℝ) := by
  have hrR : (0 : ℝ) < s.r := by exact_mod_cast hr
  have hpos : (0 : ℝ) < 2000 * (s.r : ℝ) := by positivity
  constructor
  · intro h k
    rcases h with ⟨h1, h2⟩
    rw [abs_lt] at h1 h2
    fin_cases k <;> simp only [getHPs, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_ofNat]
    · have := mul_lt_mul_of_pos_right h1.2 hpos; field_simp [hrR.ne'] at this; linarith
    · have := mul_lt_mul_of_pos_right h1.1 hpos; field_simp [hrR.ne'] at this; linarith
    · have := mul_lt_mul_of_pos_right h2.2 hpos; field_simp [hrR.ne'] at this; linarith
    · have := mul_lt_mul_of_pos_right h2.1 hpos; field_simp [hrR.ne'] at this; linarith
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    simp only [getHPs, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_ofNat] at h0 h1 h2 h3
    constructor <;> rw [abs_lt] <;> constructor
    · refine (mul_lt_mul_iff_of_pos_right hpos).mp ?_; field_simp [hrR.ne']; linarith
    · refine (mul_lt_mul_iff_of_pos_right hpos).mp ?_; field_simp [hrR.ne']; linarith
    · refine (mul_lt_mul_iff_of_pos_right hpos).mp ?_; field_simp [hrR.ne']; linarith
    · refine (mul_lt_mul_iff_of_pos_right hpos).mp ?_; field_simp [hrR.ne']; linarith

/-! ### 四、精确见证点 (3716655/1887000, 161574474/81141000) 荷载恰为 8014706 -/

def sqInsideAtRat (s : ExactSq) (Xn Yn D : ℤ) : Bool :=
  decide ((getHPs s 0).A * Xn + (getHPs s 0).B * Yn < (getHPs s 0).C * D) &&
  decide ((getHPs s 1).A * Xn + (getHPs s 1).B * Yn < (getHPs s 1).C * D) &&
  decide ((getHPs s 2).A * Xn + (getHPs s 2).B * Yn < (getHPs s 2).C * D) &&
  decide ((getHPs s 3).A * Xn + (getHPs s 3).B * Yn < (getHPs s 3).C * D)

def loadListAtRat (L : List ExactSq) (Xn Yn D : ℤ) : ℕ :=
  (L.map fun s => if sqInsideAtRat s Xn Yn D then s.w else 0).sum

lemma sqInside_rat_iff (s : ExactSq) (hr : 0 < s.r) (Xn Yn D : ℤ) (hD : 0 < D) :
    sqInside s ((Xn : ℝ) / D) ((Yn : ℝ) / D) ↔ sqInsideAtRat s Xn Yn D = true := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  rw [sqInside_iff_hps s hr]
  have hhp : ∀ k : Fin 4,
      ((getHPs s k).A : ℝ) * ((Xn : ℝ) / D) + ((getHPs s k).B : ℝ) * ((Yn : ℝ) / D) < ((getHPs s k).C : ℝ) ↔
      (getHPs s k).A * Xn + (getHPs s k).B * Yn < (getHPs s k).C * D := by
    intro k
    constructor
    · intro hlt
      have hmul := mul_lt_mul_of_pos_right hlt hDR
      have hmul' : (((getHPs s k).A * Xn + (getHPs s k).B * Yn : ℤ) : ℝ) < (((getHPs s k).C * D : ℤ) : ℝ) := by
        push_cast; field_simp [hDR.ne'] at hmul; linarith
      exact_mod_cast hmul'
    · intro hlt
      have hltR : (((getHPs s k).A * Xn + (getHPs s k).B * Yn : ℤ) : ℝ) < (((getHPs s k).C * D : ℤ) : ℝ) := by
        exact_mod_cast hlt
      refine (mul_lt_mul_iff_of_pos_right hDR).mp ?_
      push_cast at hltR; field_simp [hDR.ne']; linarith
  simp only [sqInsideAtRat, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨⟨⟨(hhp 0).mp (h 0), (hhp 1).mp (h 1)⟩, (hhp 2).mp (h 2)⟩, (hhp 3).mp (h 3)⟩
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ k
    fin_cases k
    · exact (hhp 0).mpr h0
    · exact (hhp 1).mpr h1
    · exact (hhp 2).mpr h2
    · exact (hhp 3).mpr h3

lemma loadList_atRat_eq (L : List ExactSq) (hr : ∀ s ∈ L, 0 < s.r) (Xn Yn D : ℤ) (hD : 0 < D) :
    loadList L ((Xn : ℝ) / D) ((Yn : ℝ) / D) = loadListAtRat L Xn Yn D := by
  induction L with
  | nil => simp [loadList, loadListAtRat]
  | cons s t ih =>
    have ih' := ih (fun u hu => hr u (List.mem_cons_of_mem _ hu))
    have hiff := sqInside_rat_iff s (hr s List.mem_cons_self) Xn Yn D hD
    simp only [loadList, loadListAtRat, List.map_cons, List.sum_cons] at ih' ⊢
    by_cases hb : sqInsideAtRat s Xn Yn D = true
    · simp [hb, hiff.mpr hb, ih']
    · have hbf : sqInsideAtRat s Xn Yn D = false := Bool.eq_false_iff.mpr hb
      have hnb : ¬ sqInside s ((Xn : ℝ) / D) ((Yn : ℝ) / D) := fun hin => hb (hiff.mp hin)
      simp [hbf, hnb, ih']

set_option maxRecDepth 12000 in
/-- 81141 = 43 * 1887，故 (3716655/1887000, 161574474/81141000) = (159816165/81141000, 161574474/81141000) -/
theorem witnessPoint_load_int :
    loadListAtRat squares560 159816165 161574474 81141000 = 8014706 := by decide

theorem witnessPoint_load_eq :
    loadList squares560 ((3716655 : ℝ) / 1887000) ((161574474 : ℝ) / 81141000) = 8014706 := by
  have hx : ((3716655 : ℝ) / 1887000) = ((159816165 : ℤ) : ℝ) / (81141000 : ℤ) := by norm_num
  have hy : ((161574474 : ℝ) / 81141000) = ((161574474 : ℤ) : ℝ) / (81141000 : ℤ) := by norm_num
  rw [hx, hy, loadList_atRat_eq squares560 (fun s hs => (squares560_valid s hs).1) _ _ _ (by norm_num)]
  exact witnessPoint_load_int


end OrbitWitness4661

namespace OrbitWitness4661

def boxMin (A B x0 x1 y0 y1 : ℤ) : ℤ :=
  min (A * x0) (A * x1) + min (B * y0) (B * y1)

def boxMax (A B x0 x1 y0 y1 : ℤ) : ℤ :=
  max (A * x0) (A * x1) + max (B * y0) (B * y1)

def hpBlocksBox (h : HP) (x0 x1 y0 y1 D : ℤ) : Bool :=
  decide (boxMin h.A h.B x0 x1 y0 y1 ≥ h.C * D)

def mayIntersect (s : ExactSq) (x0 x1 y0 y1 D : ℤ) : Bool :=
  !hpBlocksBox (getHPs s 0) x0 x1 y0 y1 D &&
  !hpBlocksBox (getHPs s 1) x0 x1 y0 y1 D &&
  !hpBlocksBox (getHPs s 2) x0 x1 y0 y1 D &&
  !hpBlocksBox (getHPs s 3) x0 x1 y0 y1 D

def strictlyContains (s : ExactSq) (x0 x1 y0 y1 D : ℤ) : Bool :=
  decide (boxMax (getHPs s 0).A (getHPs s 0).B x0 x1 y0 y1 < (getHPs s 0).C * D) &&
  decide (boxMax (getHPs s 1).A (getHPs s 1).B x0 x1 y0 y1 < (getHPs s 1).C * D) &&
  decide (boxMax (getHPs s 2).A (getHPs s 2).B x0 x1 y0 y1 < (getHPs s 2).C * D) &&
  decide (boxMax (getHPs s 3).A (getHPs s 3).B x0 x1 y0 y1 < (getHPs s 3).C * D)

def farkasPairComb (a b : HP) (m1 m2 x0 x1 y0 y1 D : ℤ) : Bool :=
  decide (0 < m1) && decide (0 < m2) &&
  decide (boxMin (m1 * a.A + m2 * b.A) (m1 * a.B + m2 * b.B) x0 x1 y0 y1 ≥
          (m1 * a.C + m2 * b.C) * D)

def localFarkasDisjoint (s1 s2 : ExactSq) (x0 x1 y0 y1 D : ℤ) : Bool :=
  (List.finRange 4).any fun i =>
    (List.finRange 4).any fun j =>
      let a := getHPs s1 i
      let b := getHPs s2 j
      (if (a.A > 0 && b.A < 0) || (a.A < 0 && b.A > 0)
       then farkasPairComb a b (Int.natAbs b.A) (Int.natAbs a.A) x0 x1 y0 y1 D
       else false) ||
      (if (a.B > 0 && b.B < 0) || (a.B < 0 && b.B > 0)
       then farkasPairComb a b (Int.natAbs b.B) (Int.natAbs a.B) x0 x1 y0 y1 D
       else false)

def hasFarkasCert (L : List ExactSq) (totalW : ℕ) (x0 x1 y0 y1 D : ℤ) : Bool :=
  match L with
  | [] => false
  | s1 :: rest =>
    (rest.any fun s2 =>
      decide (totalW - min s1.w s2.w ≤ CAP) &&
      localFarkasDisjoint s1 s2 x0 x1 y0 y1 D) ||
    hasFarkasCert rest totalW x0 x1 y0 y1 D

def verifyBox : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → List ExactSq → Bool
  | fuel, x0, x1, y0, y1, D, cand =>
    if y0 > x1 then true
    else
      let active := cand.filter fun s => mayIntersect s x0 x1 y0 y1 D
      let ub := (active.map (·.w)).sum
      if ub ≤ CAP then true
      else
        let bdry := active.filter fun s => !strictlyContains s x0 x1 y0 y1 D
        if hasFarkasCert bdry ub x0 x1 y0 y1 D then true
        else match fuel with
          | 0 => false
          | fuel' + 1 =>
            let mx := x0 + x1
            let my := y0 + y1
            let D2 := 2 * D
            verifyBox fuel' (2 * x0) mx       (2 * y0) my       D2 active &&
            verifyBox fuel' mx       (2 * x1) (2 * y0) my       D2 active &&
            verifyBox fuel' (2 * x0) mx       my       (2 * y1) D2 active &&
            verifyBox fuel' mx       (2 * x1) my       (2 * y1) D2 active

def gridPts : List ℤ := [0, 2000, 3250, 3300, 4000, 4022, 4072, 4661]

def gridPairs : List (ℤ × ℤ) := gridPts.zip gridPts.tail!

def verifyFundamental : Bool :=
  gridPairs.all fun (x0, x1) =>
    gridPairs.all fun (y0, y1) =>
      verifyBox 11 x0 x1 y0 y1 2000 squares560

end OrbitWitness4661

namespace OrbitWitness4661

lemma boxMin_le_eval (A B x0 x1 y0 y1 D : ℤ) (hD : (0 : ℝ) < D)
    {X Y : ℝ} (hx0 : (x0 : ℝ) / D ≤ X) (hx1 : X ≤ (x1 : ℝ) / D)
    (hy0 : (y0 : ℝ) / D ≤ Y) (hy1 : Y ≤ (y1 : ℝ) / D) :
    ((boxMin A B x0 x1 y0 y1 : ℤ) : ℝ) ≤ ((A : ℝ) * X + (B : ℝ) * Y) * D := by
  have hAx : (min ((A : ℝ) * x0) ((A : ℝ) * x1)) ≤ (A : ℝ) * (X * D) := by
    have hX0 : (x0 : ℝ) ≤ X * D := (div_le_iff₀ hD).mp hx0
    have hX1 : X * D ≤ (x1 : ℝ) := (le_div_iff₀ hD).mp hx1
    rcases le_or_gt (0 : ℝ) A with hA | hA
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hX0 hA)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hX1 hA.le)
  have hBy : (min ((B : ℝ) * y0) ((B : ℝ) * y1)) ≤ (B : ℝ) * (Y * D) := by
    have hY0 : (y0 : ℝ) ≤ Y * D := (div_le_iff₀ hD).mp hy0
    have hY1 : Y * D ≤ (y1 : ℝ) := (le_div_iff₀ hD).mp hy1
    rcases le_or_gt (0 : ℝ) B with hB | hB
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hY0 hB)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hY1 hB.le)
  simp only [boxMin, Int.cast_add, Int.cast_min, Int.cast_mul]
  linarith

lemma not_mayIntersect_imp_not_sqInside (s : ExactSq) (hr : 0 < s.r)
    (x0 x1 y0 y1 D : ℤ) (hD : (0 : ℝ) < D) {X Y : ℝ}
    (hx0 : (x0 : ℝ) / D ≤ X) (hx1 : X ≤ (x1 : ℝ) / D)
    (hy0 : (y0 : ℝ) / D ≤ Y) (hy1 : Y ≤ (y1 : ℝ) / D)
    (hmi : mayIntersect s x0 x1 y0 y1 D = false) :
    ¬ sqInside s X Y := by
  intro hin
  have hblock : ∀ k : Fin 4, hpBlocksBox (getHPs s k) x0 x1 y0 y1 D = false := by
    intro k
    by_contra hk
    simp only [Bool.not_eq_false] at hk
    have hge : ((getHPs s k).C : ℝ) * D ≤ ((boxMin (getHPs s k).A (getHPs s k).B x0 x1 y0 y1 : ℤ) : ℝ) := by
      have := of_decide_eq_true hk; exact_mod_cast this
    have hmin := boxMin_le_eval (getHPs s k).A (getHPs s k).B x0 x1 y0 y1 D hD hx0 hx1 hy0 hy1
    have hlt := mul_lt_mul_of_pos_right ((sqInside_iff_hps s hr X Y).mp hin k) hD
    linarith
  simp [mayIntersect, hblock 0, hblock 1, hblock 2, hblock 3] at hmi

lemma localFarkasDisjoint_sound (s1 s2 : ExactSq) (hr1 : 0 < s1.r) (hr2 : 0 < s2.r)
    (x0 x1 y0 y1 D : ℤ) (hD : (0 : ℝ) < D) {X Y : ℝ}
    (hx0 : (x0 : ℝ) / D ≤ X) (hx1 : X ≤ (x1 : ℝ) / D)
    (hy0 : (y0 : ℝ) / D ≤ Y) (hy1 : Y ≤ (y1 : ℝ) / D)
    (hf : localFarkasDisjoint s1 s2 x0 x1 y0 y1 D = true) :
    ¬ (sqInside s1 X Y ∧ sqInside s2 X Y) := by
  rintro ⟨h1, h2⟩
  simp only [localFarkasDisjoint, List.any_eq_true, List.mem_finRange, true_and] at hf
  rcases hf with ⟨i, j, hij⟩
  have hcomb : ∀ (m1 m2 : ℤ),
      farkasPairComb (getHPs s1 i) (getHPs s2 j) m1 m2 x0 x1 y0 y1 D = true → False := by
    intro m1 m2 hc
    simp only [farkasPairComb, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨⟨hm1, hm2⟩, hge⟩
    have hm1R : (0 : ℝ) < m1 := by exact_mod_cast hm1
    have hm2R : (0 : ℝ) < m2 := by exact_mod_cast hm2
    have hlt1 := mul_lt_mul_of_pos_left ((sqInside_iff_hps s1 hr1 X Y).mp h1 i) hm1R
    have hlt2 := mul_lt_mul_of_pos_left ((sqInside_iff_hps s2 hr2 X Y).mp h2 j) hm2R
    have hsum : ((m1 * (getHPs s1 i).A + m2 * (getHPs s2 j).A : ℤ) : ℝ) * X +
                ((m1 * (getHPs s1 i).B + m2 * (getHPs s2 j).B : ℤ) : ℝ) * Y <
                ((m1 * (getHPs s1 i).C + m2 * (getHPs s2 j).C : ℤ) : ℝ) := by
      push_cast; linarith
    have hsumD := mul_lt_mul_of_pos_right hsum hD
    have hmin := boxMin_le_eval (m1 * (getHPs s1 i).A + m2 * (getHPs s2 j).A)
                                (m1 * (getHPs s1 i).B + m2 * (getHPs s2 j).B) x0 x1 y0 y1 D hD hx0 hx1 hy0 hy1
    have hgeR : (((m1 * (getHPs s1 i).C + m2 * (getHPs s2 j).C : ℤ) : ℝ) * D) ≤
                ((boxMin (m1 * (getHPs s1 i).A + m2 * (getHPs s2 j).A)
                         (m1 * (getHPs s1 i).B + m2 * (getHPs s2 j).B) x0 x1 y0 y1 : ℤ) : ℝ) := by
      exact_mod_cast hge
    linarith
  simp only [Bool.or_eq_true] at hij
  rcases hij with hA | hB
  · split_ifs at hA
    exact hcomb _ _ hA
  · split_ifs at hB
    exact hcomb _ _ hB

/-- 未击中权重和 gapList：对 List.Sublist 单调 -/
noncomputable def gapList (L : List ExactSq) (X Y : ℝ) : ℕ := by
  classical
  exact (L.map fun s => if sqInside s X Y then 0 else s.w).sum

lemma loadList_cons_pos {s : ExactSq} {t : List ExactSq} {X Y : ℝ} (h : sqInside s X Y) :
    loadList (s :: t) X Y = s.w + loadList t X Y := by
  simp [loadList, h]

lemma loadList_cons_neg {s : ExactSq} {t : List ExactSq} {X Y : ℝ} (h : ¬ sqInside s X Y) :
    loadList (s :: t) X Y = loadList t X Y := by
  simp [loadList, h]

lemma gapList_cons_pos {s : ExactSq} {t : List ExactSq} {X Y : ℝ} (h : sqInside s X Y) :
    gapList (s :: t) X Y = gapList t X Y := by
  simp [gapList, h]

lemma gapList_cons_neg {s : ExactSq} {t : List ExactSq} {X Y : ℝ} (h : ¬ sqInside s X Y) :
    gapList (s :: t) X Y = s.w + gapList t X Y := by
  simp [gapList, h]

lemma loadList_add_gapList (L : List ExactSq) (X Y : ℝ) :
    loadList L X Y + gapList L X Y = (L.map (·.w)).sum := by
  induction L with
  | nil => simp [loadList, gapList]
  | cons s t ih =>
    by_cases h : sqInside s X Y
    · rw [loadList_cons_pos h, gapList_cons_pos h, List.map_cons, List.sum_cons]; omega
    · rw [loadList_cons_neg h, gapList_cons_neg h, List.map_cons, List.sum_cons]; omega

lemma gapList_le_of_sublist {A B : List ExactSq} (hsub : A.Sublist B) (X Y : ℝ) :
    gapList A X Y ≤ gapList B X Y := by
  induction hsub with
  | slnil => exact le_rfl
  | cons s _ ih =>
    by_cases h : sqInside s X Y
    · rw [gapList_cons_pos h]; exact ih
    · rw [gapList_cons_neg h]; omega
  | cons_cons s _ ih =>
    by_cases h : sqInside s X Y
    · rw [gapList_cons_pos h, gapList_cons_pos h]; exact ih
    · rw [gapList_cons_neg h, gapList_cons_neg h]; omega

lemma le_gapList_of_mem_not_sqInside {L : List ExactSq} {s : ExactSq} {X Y : ℝ}
    (hs : s ∈ L) (hns : ¬ sqInside s X Y) : s.w ≤ gapList L X Y := by
  induction L with
  | nil => cases hs
  | cons a t ih =>
    rcases List.mem_cons.mp hs with rfl | ht
    · rw [gapList_cons_neg hns]; omega
    · have hih := ih ht
      by_cases ha : sqInside a X Y
      · rw [gapList_cons_pos ha]; exact hih
      · rw [gapList_cons_neg ha]; omega

lemma hasFarkasCert_sound (L : List ExactSq) (hr : ∀ s ∈ L, 0 < s.r) (totalW : ℕ)
    (x0 x1 y0 y1 D : ℤ) (hD : (0 : ℝ) < D) {X Y : ℝ}
    (hx0 : (x0 : ℝ) / D ≤ X) (hx1 : X ≤ (x1 : ℝ) / D)
    (hy0 : (y0 : ℝ) / D ≤ Y) (hy1 : Y ≤ (y1 : ℝ) / D)
    (hc : hasFarkasCert L totalW x0 x1 y0 y1 D = true) :
    ∃ g : ℕ, g ≤ gapList L X Y ∧ totalW - g ≤ CAP := by
  induction L with
  | nil => simp [hasFarkasCert] at hc
  | cons s1 rest ih =>
    simp only [hasFarkasCert, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨s2, hs2, hcap, hf⟩ | hrest
    · have hnb := localFarkasDisjoint_sound s1 s2 (hr s1 List.mem_cons_self)
        (hr s2 (List.mem_cons_of_mem _ hs2)) x0 x1 y0 y1 D hD hx0 hx1 hy0 hy1 hf
      refine ⟨min s1.w s2.w, ?_, hcap⟩
      by_cases h1 : sqInside s1 X Y
      · have h2 : ¬ sqInside s2 X Y := fun h2 => hnb ⟨h1, h2⟩
        have hle := le_gapList_of_mem_not_sqInside hs2 h2
        rw [gapList_cons_pos h1]
        omega
      · rw [gapList_cons_neg h1]
        omega
    · rcases ih (fun u hu => hr u (List.mem_cons_of_mem _ hu)) hrest with ⟨g, hg, hcap⟩
      refine ⟨g, ?_, hcap⟩
      by_cases h1 : sqInside s1 X Y
      · rw [gapList_cons_pos h1]; exact hg
      · rw [gapList_cons_neg h1]; omega

lemma loadList_filter_eq (L : List ExactSq) (p : ExactSq → Bool) (X Y : ℝ)
    (h : ∀ s ∈ L, p s = false → ¬ sqInside s X Y) :
    loadList L X Y = loadList (L.filter p) X Y := by
  induction L with
  | nil => simp [loadList]
  | cons s t ih =>
    have iht := ih (fun u hu => h u (List.mem_cons_of_mem _ hu))
    rw [List.filter_cons]
    cases hp : p s
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [loadList_cons_neg (h s List.mem_cons_self hp), iht]
    · simp only [↓reduceIte]
      by_cases hs : sqInside s X Y
      · rw [loadList_cons_pos hs, loadList_cons_pos hs, iht]
      · rw [loadList_cons_neg hs, loadList_cons_neg hs, iht]

lemma verifyBox_sound : ∀ (fuel : ℕ) (x0 x1 y0 y1 D : ℤ) (cand : List ExactSq),
    (∀ s ∈ cand, 0 < s.r) → (0 : ℝ) < D →
    verifyBox fuel x0 x1 y0 y1 D cand = true →
    ∀ {X Y : ℝ}, Y ≤ X →
      (x0 : ℝ) / D ≤ X → X ≤ (x1 : ℝ) / D →
      (y0 : ℝ) / D ≤ Y → Y ≤ (y1 : ℝ) / D →
      loadList cand X Y ≤ CAP := by
  intro fuel
  induction fuel with
  | zero =>
    intro x0 x1 y0 y1 D cand hr hD hv X Y hYX hx0 hx1 hy0 hy1
    unfold verifyBox at hv
    dsimp only at hv
    by_cases hskip : y0 > x1
    · have hlt : (x1 : ℝ) < y0 := by exact_mod_cast hskip
      have : (x1 : ℝ) / D < (y0 : ℝ) / D := div_lt_div_of_pos_right hlt hD
      linarith
    · simp only [hskip, ↓reduceIte] at hv
      set active := cand.filter fun s => mayIntersect s x0 x1 y0 y1 D
      have heq : loadList cand X Y = loadList active X Y :=
        loadList_filter_eq cand _ X Y fun s hs hmi =>
          not_mayIntersect_imp_not_sqInside s (hr s hs) x0 x1 y0 y1 D hD hx0 hx1 hy0 hy1 hmi
      rw [heq]
      have hact_r : ∀ s ∈ active, 0 < s.r := fun s hs => hr s (List.mem_of_mem_filter hs)
      by_cases hub : (active.map (·.w)).sum ≤ CAP
      · have := loadList_add_gapList active X Y; omega
      · simp only [hub, ↓reduceIte] at hv
        set bdry := active.filter fun s => !strictlyContains s x0 x1 y0 y1 D
        cases hfc : hasFarkasCert bdry (active.map (·.w)).sum x0 x1 y0 y1 D with
        | true =>
          rcases hasFarkasCert_sound bdry (fun s hs => hact_r s (List.mem_of_mem_filter hs))
            (active.map (·.w)).sum x0 x1 y0 y1 D hD hx0 hx1 hy0 hy1 hfc with ⟨g, hg, hcap⟩
          have hsub : gapList bdry X Y ≤ gapList active X Y :=
            gapList_le_of_sublist List.filter_sublist X Y
          have htot := loadList_add_gapList active X Y
          omega
        | false =>
          simp [hfc] at hv
  | succ fuel' ih =>
    intro x0 x1 y0 y1 D cand hr hD hv X Y hYX hx0 hx1 hy0 hy1
    unfold verifyBox at hv
    dsimp only at hv
    by_cases hskip : y0 > x1
    · have hlt : (x1 : ℝ) < y0 := by exact_mod_cast hskip
      have : (x1 : ℝ) / D < (y0 : ℝ) / D := div_lt_div_of_pos_right hlt hD
      linarith
    · simp only [hskip, ↓reduceIte] at hv
      set active := cand.filter fun s => mayIntersect s x0 x1 y0 y1 D
      have heq : loadList cand X Y = loadList active X Y :=
        loadList_filter_eq cand _ X Y fun s hs hmi =>
          not_mayIntersect_imp_not_sqInside s (hr s hs) x0 x1 y0 y1 D hD hx0 hx1 hy0 hy1 hmi
      rw [heq]
      have hact_r : ∀ s ∈ active, 0 < s.r := fun s hs => hr s (List.mem_of_mem_filter hs)
      by_cases hub : (active.map (·.w)).sum ≤ CAP
      · have := loadList_add_gapList active X Y; omega
      · simp only [hub, ↓reduceIte] at hv
        set bdry := active.filter fun s => !strictlyContains s x0 x1 y0 y1 D
        cases hfc : hasFarkasCert bdry (active.map (·.w)).sum x0 x1 y0 y1 D with
        | true =>
          rcases hasFarkasCert_sound bdry (fun s hs => hact_r s (List.mem_of_mem_filter hs))
            (active.map (·.w)).sum x0 x1 y0 y1 D hD hx0 hx1 hy0 hy1 hfc with ⟨g, hg, hcap⟩
          have hsub : gapList bdry X Y ≤ gapList active X Y :=
            gapList_le_of_sublist List.filter_sublist X Y
          have htot := loadList_add_gapList active X Y
          omega
        | false =>
          simp only [hfc, Bool.false_eq_true, ↓reduceIte] at hv
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hv
          rcases hv with ⟨⟨⟨hv00, hv10⟩, hv01⟩, hv11⟩
          have hD2 : (0 : ℝ) < ((2 * D : ℤ) : ℝ) := by push_cast; linarith
          have hx0' : ((2 * x0 : ℤ) : ℝ) / ((2 * D : ℤ) : ℝ) ≤ X := by
            push_cast; rw [mul_div_mul_left _ _ (by norm_num)]; exact hx0
          have hx1' : X ≤ ((2 * x1 : ℤ) : ℝ) / ((2 * D : ℤ) : ℝ) := by
            push_cast; rw [mul_div_mul_left _ _ (by norm_num)]; exact hx1
          have hy0' : ((2 * y0 : ℤ) : ℝ) / ((2 * D : ℤ) : ℝ) ≤ Y := by
            push_cast; rw [mul_div_mul_left _ _ (by norm_num)]; exact hy0
          have hy1' : Y ≤ ((2 * y1 : ℤ) : ℝ) / ((2 * D : ℤ) : ℝ) := by
            push_cast; rw [mul_div_mul_left _ _ (by norm_num)]; exact hy1
          rcases le_total X (((x0 + x1 : ℤ) : ℝ) / ((2 * D : ℤ) : ℝ)) with hXl | hXr <;>
          rcases le_total Y (((y0 + y1 : ℤ) : ℝ) / ((2 * D : ℤ) : ℝ)) with hYl | hYr
          · exact ih _ _ _ _ _ active hact_r hD2 hv00 hYX hx0' hXl hy0' hYl
          · exact ih _ _ _ _ _ active hact_r hD2 hv01 hYX hx0' hXl hYr hy1'
          · exact ih _ _ _ _ _ active hact_r hD2 hv10 hYX hXr hx1' hy0' hYl
          · exact ih _ _ _ _ _ active hact_r hD2 hv11 hYX hXr hx1' hYr hy1'


end OrbitWitness4661

namespace OrbitWitness4661

lemma sqInside_imp_in_container (s : ExactSq) (hv : sqValidReal s) {X Y : ℝ} (hin : sqInside s X Y) :
    0 ≤ X ∧ X ≤ 4661 / 1000 ∧ 0 ≤ Y ∧ Y ≤ 4661 / 1000 := by
  rcases hv with ⟨_, hunit, hx1, hx2, hy1, hy2⟩
  rcases hin with ⟨hu, hv'⟩
  set x : ℝ := (s.cx : ℝ) / 1000
  set y : ℝ := (s.cy : ℝ) / 1000
  set a : ℝ := (s.p : ℝ) / s.r
  set b : ℝ := (s.q : ℝ) / s.r
  set U : ℝ := a * (X - x) + b * (Y - y)
  set V : ℝ := (-b) * (X - x) + a * (Y - y)
  have hXeq : X - x = a * U - b * V := by
    have : a * U - b * V = (a ^ 2 + b ^ 2) * (X - x) := by dsimp [U, V]; ring
    rw [this, hunit, one_mul]
  have hYeq : Y - y = b * U + a * V := by
    have : b * U + a * V = (a ^ 2 + b ^ 2) * (Y - y) := by dsimp [U, V]; ring
    rw [this, hunit, one_mul]
  have hXabs : |X - x| ≤ (|a| + |b|) / 2 := by
    rw [hXeq]
    calc |a * U - b * V| ≤ |a * U| + |b * V| := abs_sub _ _
      _ = |a| * |U| + |b| * |V| := by rw [abs_mul, abs_mul]
      _ ≤ |a| * (1 / 2) + |b| * (1 / 2) := by
          have h1 := mul_le_mul_of_nonneg_left hu.le (abs_nonneg a)
          have h2 := mul_le_mul_of_nonneg_left hv'.le (abs_nonneg b)
          linarith
      _ = (|a| + |b|) / 2 := by ring
  have hYabs : |Y - y| ≤ (|a| + |b|) / 2 := by
    rw [hYeq]
    calc |b * U + a * V| ≤ |b * U| + |a * V| := abs_add_le _ _
      _ = |b| * |U| + |a| * |V| := by rw [abs_mul, abs_mul]
      _ ≤ |b| * (1 / 2) + |a| * (1 / 2) := by
          have h1 := mul_le_mul_of_nonneg_left hu.le (abs_nonneg b)
          have h2 := mul_le_mul_of_nonneg_left hv'.le (abs_nonneg a)
          linarith
      _ = (|a| + |b|) / 2 := by ring
  rw [abs_le] at hXabs hYabs
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma loadList_zero_outside {X Y : ℝ}
    (hout : ¬ (0 ≤ X ∧ X ≤ 4661 / 1000 ∧ 0 ≤ Y ∧ Y ≤ 4661 / 1000)) :
    loadList squares560 X Y = 0 := by
  have h : ∀ L : List ExactSq, (∀ s ∈ L, sqValidReal s) → loadList L X Y = 0 := by
    intro L hL
    induction L with
    | nil => simp [loadList]
    | cons s t ih =>
      have hns : ¬ sqInside s X Y :=
        fun hin => hout (sqInside_imp_in_container s (hL s List.mem_cons_self) hin)
      have htail : loadList t X Y = 0 :=
        ih (fun u hu => hL u (List.mem_cons_of_mem _ hu))
      simp only [loadList] at htail ⊢
      simp [hns, htail]
  exact h squares560 squares560_valid

lemma loadList_append (L1 L2 : List ExactSq) (X Y : ℝ) :
    loadList (L1 ++ L2) X Y = loadList L1 X Y + loadList L2 X Y := by
  simp [loadList, List.map_append, List.sum_append]

lemma inside_reflectX (x y a b X Y : ℝ) :
    inside x y a b ((4661 / 1000 : ℝ) - X) Y ↔ inside ((4661 / 1000 : ℝ) - x) y (-a) b X Y := by
  unfold inside
  have h1 : a * (((4661 / 1000 : ℝ) - X) - x) + b * (Y - y) =
            (-a) * (X - ((4661 / 1000 : ℝ) - x)) + b * (Y - y) := by ring
  have h2 : (-b) * (((4661 / 1000 : ℝ) - X) - x) + a * (Y - y) =
            -((-b) * (X - ((4661 / 1000 : ℝ) - x)) + (-a) * (Y - y)) := by ring
  rw [h1, h2, abs_neg]

lemma inside_reflectY (x y a b X Y : ℝ) :
    inside x y a b X ((4661 / 1000 : ℝ) - Y) ↔ inside x ((4661 / 1000 : ℝ) - y) a (-b) X Y := by
  unfold inside
  have h1 : a * (X - x) + b * (((4661 / 1000 : ℝ) - Y) - y) =
            a * (X - x) + (-b) * (Y - ((4661 / 1000 : ℝ) - y)) := by ring
  have h2 : (-b) * (X - x) + a * (((4661 / 1000 : ℝ) - Y) - y) =
            -((-(-b)) * (X - x) + a * (Y - ((4661 / 1000 : ℝ) - y))) := by ring
  rw [h1, h2, abs_neg]

lemma inside_swapXY (x y a b X Y : ℝ) :
    inside x y a b Y X ↔ inside y x b a X Y := by
  unfold inside
  have h1 : a * (Y - x) + b * (X - y) = b * (X - y) + a * (Y - x) := by ring
  have h2 : (-b) * (Y - x) + a * (X - y) = -((-a) * (X - y) + b * (Y - x)) := by ring
  rw [h1, h2, abs_neg]

private lemma ite_dec_eq {P Q : Prop} {d1 : Decidable P} {d2 : Decidable Q}
    (h : P ↔ Q) (a b : ℕ) :
    @ite ℕ P d1 a b = @ite ℕ Q d2 a b := by
  cases d1 with
  | isTrue hp =>
    cases d2 with
    | isTrue _ => rfl
    | isFalse hq => exact False.elim (hq (h.mp hp))
  | isFalse hp =>
    cases d2 with
    | isTrue hq => exact False.elim (hp (h.mpr hq))
    | isFalse _ => rfl

private lemma sum8_perm_reflectX
    {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℕ}
    (h02 : a0 = b2) (h13 : a1 = b3) (h20 : a2 = b0) (h31 : a3 = b1)
    (h46 : a4 = b6) (h57 : a5 = b7) (h64 : a6 = b4) (h75 : a7 = b5) :
    a0 + (a1 + (a2 + (a3 + (a4 + (a5 + (a6 + (a7 + 0))))))) =
    b0 + (b1 + (b2 + (b3 + (b4 + (b5 + (b6 + (b7 + 0))))))) := by
  omega

private lemma sum8_perm_reflectY
    {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℕ}
    (h01 : a0 = b1) (h10 : a1 = b0) (h23 : a2 = b3) (h32 : a3 = b2)
    (h45 : a4 = b5) (h54 : a5 = b4) (h67 : a6 = b7) (h76 : a7 = b6) :
    a0 + (a1 + (a2 + (a3 + (a4 + (a5 + (a6 + (a7 + 0))))))) =
    b0 + (b1 + (b2 + (b3 + (b4 + (b5 + (b6 + (b7 + 0))))))) := by
  omega

private lemma sum8_perm_swapXY
    {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℕ}
    (h04 : a0 = b4) (h16 : a1 = b6) (h25 : a2 = b5) (h37 : a3 = b7)
    (h40 : a4 = b0) (h52 : a5 = b2) (h61 : a6 = b1) (h73 : a7 = b3) :
    a0 + (a1 + (a2 + (a3 + (a4 + (a5 + (a6 + (a7 + 0))))))) =
    b0 + (b1 + (b2 + (b3 + (b4 + (b5 + (b6 + (b7 + 0))))))) := by
  omega

lemma load_expandOrbit_reflectX (o : Orbit) (X Y : ℝ) :
    loadList (expandOrbit o) ((4661 / 1000 : ℝ) - X) Y = loadList (expandOrbit o) X Y := by
  classical
  simp only [expandOrbit, loadList, sqInside, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Int.cast_sub, Int.cast_neg, Int.cast_ofNat, sub_div, neg_div]
  have h02 := inside_reflectX ((o.cx:ℝ)/1000) ((o.cy:ℝ)/1000) ((o.p:ℝ)/o.r) ((o.q:ℝ)/o.r) X Y
  have h13 := inside_reflectX ((o.cx:ℝ)/1000) ((4661:ℝ)/1000 - (o.cy:ℝ)/1000) ((o.p:ℝ)/o.r) (-((o.q:ℝ)/o.r)) X Y
  have h20 := inside_reflectX ((4661:ℝ)/1000 - (o.cx:ℝ)/1000) ((o.cy:ℝ)/1000) (-((o.p:ℝ)/o.r)) ((o.q:ℝ)/o.r) X Y
  have h31 := inside_reflectX ((4661:ℝ)/1000 - (o.cx:ℝ)/1000) ((4661:ℝ)/1000 - (o.cy:ℝ)/1000) (-((o.p:ℝ)/o.r)) (-((o.q:ℝ)/o.r)) X Y
  have h46 := inside_reflectX ((o.cy:ℝ)/1000) ((o.cx:ℝ)/1000) ((o.q:ℝ)/o.r) ((o.p:ℝ)/o.r) X Y
  have h57 := inside_reflectX ((o.cy:ℝ)/1000) ((4661:ℝ)/1000 - (o.cx:ℝ)/1000) ((o.q:ℝ)/o.r) (-((o.p:ℝ)/o.r)) X Y
  have h64 := inside_reflectX ((4661:ℝ)/1000 - (o.cy:ℝ)/1000) ((o.cx:ℝ)/1000) (-((o.q:ℝ)/o.r)) ((o.p:ℝ)/o.r) X Y
  have h75 := inside_reflectX ((4661:ℝ)/1000 - (o.cy:ℝ)/1000) ((4661:ℝ)/1000 - (o.cx:ℝ)/1000) (-((o.q:ℝ)/o.r)) (-((o.p:ℝ)/o.r)) X Y
  simp only [sub_sub_cancel, neg_neg] at h20 h31 h64 h75
  exact sum8_perm_reflectX
    (ite_dec_eq h02 o.w 0) (ite_dec_eq h13 o.w 0) (ite_dec_eq h20 o.w 0) (ite_dec_eq h31 o.w 0)
    (ite_dec_eq h46 o.w 0) (ite_dec_eq h57 o.w 0) (ite_dec_eq h64 o.w 0) (ite_dec_eq h75 o.w 0)

lemma load_expandOrbit_reflectY (o : Orbit) (X Y : ℝ) :
    loadList (expandOrbit o) X ((4661 / 1000 : ℝ) - Y) = loadList (expandOrbit o) X Y := by
  classical
  simp only [expandOrbit, loadList, sqInside, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Int.cast_sub, Int.cast_neg, Int.cast_ofNat, sub_div, neg_div]
  have h01 := inside_reflectY ((o.cx:ℝ)/1000) ((o.cy:ℝ)/1000) ((o.p:ℝ)/o.r) ((o.q:ℝ)/o.r) X Y
  have h10 := inside_reflectY ((o.cx:ℝ)/1000) ((4661:ℝ)/1000 - (o.cy:ℝ)/1000) ((o.p:ℝ)/o.r) (-((o.q:ℝ)/o.r)) X Y
  have h23 := inside_reflectY ((4661:ℝ)/1000 - (o.cx:ℝ)/1000) ((o.cy:ℝ)/1000) (-((o.p:ℝ)/o.r)) ((o.q:ℝ)/o.r) X Y
  have h32 := inside_reflectY ((4661:ℝ)/1000 - (o.cx:ℝ)/1000) ((4661:ℝ)/1000 - (o.cy:ℝ)/1000) (-((o.p:ℝ)/o.r)) (-((o.q:ℝ)/o.r)) X Y
  have h45 := inside_reflectY ((o.cy:ℝ)/1000) ((o.cx:ℝ)/1000) ((o.q:ℝ)/o.r) ((o.p:ℝ)/o.r) X Y
  have h54 := inside_reflectY ((o.cy:ℝ)/1000) ((4661:ℝ)/1000 - (o.cx:ℝ)/1000) ((o.q:ℝ)/o.r) (-((o.p:ℝ)/o.r)) X Y
  have h67 := inside_reflectY ((4661:ℝ)/1000 - (o.cy:ℝ)/1000) ((o.cx:ℝ)/1000) (-((o.q:ℝ)/o.r)) ((o.p:ℝ)/o.r) X Y
  have h76 := inside_reflectY ((4661:ℝ)/1000 - (o.cy:ℝ)/1000) ((4661:ℝ)/1000 - (o.cx:ℝ)/1000) (-((o.q:ℝ)/o.r)) (-((o.p:ℝ)/o.r)) X Y
  simp only [sub_sub_cancel, neg_neg] at h10 h32 h54 h76
  exact sum8_perm_reflectY
    (ite_dec_eq h01 o.w 0) (ite_dec_eq h10 o.w 0) (ite_dec_eq h23 o.w 0) (ite_dec_eq h32 o.w 0)
    (ite_dec_eq h45 o.w 0) (ite_dec_eq h54 o.w 0) (ite_dec_eq h67 o.w 0) (ite_dec_eq h76 o.w 0)

lemma load_expandOrbit_swapXY (o : Orbit) (X Y : ℝ) :
    loadList (expandOrbit o) Y X = loadList (expandOrbit o) X Y := by
  classical
  simp only [expandOrbit, loadList, sqInside, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Int.cast_sub, Int.cast_neg, Int.cast_ofNat, sub_div, neg_div]
  have h04 := inside_swapXY ((o.cx:ℝ)/1000) ((o.cy:ℝ)/1000) ((o.p:ℝ)/o.r) ((o.q:ℝ)/o.r) X Y
  have h16 := inside_swapXY ((o.cx:ℝ)/1000) ((4661:ℝ)/1000 - (o.cy:ℝ)/1000) ((o.p:ℝ)/o.r) (-((o.q:ℝ)/o.r)) X Y
  have h25 := inside_swapXY ((4661:ℝ)/1000 - (o.cx:ℝ)/1000) ((o.cy:ℝ)/1000) (-((o.p:ℝ)/o.r)) ((o.q:ℝ)/o.r) X Y
  have h37 := inside_swapXY ((4661:ℝ)/1000 - (o.cx:ℝ)/1000) ((4661:ℝ)/1000 - (o.cy:ℝ)/1000) (-((o.p:ℝ)/o.r)) (-((o.q:ℝ)/o.r)) X Y
  have h40 := inside_swapXY ((o.cy:ℝ)/1000) ((o.cx:ℝ)/1000) ((o.q:ℝ)/o.r) ((o.p:ℝ)/o.r) X Y
  have h52 := inside_swapXY ((o.cy:ℝ)/1000) ((4661:ℝ)/1000 - (o.cx:ℝ)/1000) ((o.q:ℝ)/o.r) (-((o.p:ℝ)/o.r)) X Y
  have h61 := inside_swapXY ((4661:ℝ)/1000 - (o.cy:ℝ)/1000) ((o.cx:ℝ)/1000) (-((o.q:ℝ)/o.r)) ((o.p:ℝ)/o.r) X Y
  have h73 := inside_swapXY ((4661:ℝ)/1000 - (o.cy:ℝ)/1000) ((4661:ℝ)/1000 - (o.cx:ℝ)/1000) (-((o.q:ℝ)/o.r)) (-((o.p:ℝ)/o.r)) X Y
  exact sum8_perm_swapXY
    (ite_dec_eq h04 o.w 0) (ite_dec_eq h16 o.w 0) (ite_dec_eq h25 o.w 0) (ite_dec_eq h37 o.w 0)
    (ite_dec_eq h40 o.w 0) (ite_dec_eq h52 o.w 0) (ite_dec_eq h61 o.w 0) (ite_dec_eq h73 o.w 0)

lemma load_flatMap_inv (os : List Orbit) (f : ℝ → ℝ → ℝ × ℝ)
    (hf : ∀ o X Y, loadList (expandOrbit o) (f X Y).1 (f X Y).2 = loadList (expandOrbit o) X Y)
    (X Y : ℝ) :
    loadList (os.flatMap expandOrbit) (f X Y).1 (f X Y).2 = loadList (os.flatMap expandOrbit) X Y := by
  induction os with
  | nil => simp [loadList]
  | cons o t ih =>
    simp only [List.flatMap_cons, loadList_append, hf o X Y, ih]

lemma gridPairs_cover {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ (4661 : ℝ) / 2000) :
    ∃ p ∈ gridPairs, (p.1 : ℝ) / 2000 ≤ t ∧ t ≤ (p.2 : ℝ) / 2000 := by
  have hgp : gridPairs = [(0,2000),(2000,3250),(3250,3300),(3300,4000),(4000,4022),(4022,4072),(4072,4661)] := rfl
  rw [hgp]
  rcases le_total t ((2000 : ℝ) / 2000) with h1 | h1
  · exact ⟨(0, 2000), by simp, by norm_num; linarith, h1⟩
  rcases le_total t ((3250 : ℝ) / 2000) with h2 | h2
  · exact ⟨(2000, 3250), by simp, h1, h2⟩
  rcases le_total t ((3300 : ℝ) / 2000) with h3 | h3
  · exact ⟨(3250, 3300), by simp, h2, h3⟩
  rcases le_total t ((4000 : ℝ) / 2000) with h4 | h4
  · exact ⟨(3300, 4000), by simp, h3, h4⟩
  rcases le_total t ((4022 : ℝ) / 2000) with h5 | h5
  · exact ⟨(4000, 4022), by simp, h4, h5⟩
  rcases le_total t ((4072 : ℝ) / 2000) with h6 | h6
  · exact ⟨(4022, 4072), by simp, h5, h6⟩
  exact ⟨(4072, 4661), by simp, h6, ht1⟩

/-- 全域荷载上界健全性定理：给定单盒健全性 `hbox` 与有限布尔检验 `hcert`，全平面所有实点荷载均 ≤ `CAP`。 -/
theorem verifyFundamental_sound_of_box_sound
    (hbox :
      ∀ (fuel : ℕ) (x0 x1 y0 y1 D : ℤ) (cand : List ExactSq),
        (∀ s ∈ cand, 0 < s.r) → (0 : ℝ) < D →
        verifyBox fuel x0 x1 y0 y1 D cand = true →
        ∀ {X Y : ℝ}, Y ≤ X →
          (x0 : ℝ) / D ≤ X → X ≤ (x1 : ℝ) / D →
          (y0 : ℝ) / D ≤ Y → Y ≤ (y1 : ℝ) / D →
          loadList cand X Y ≤ CAP)
    (hcert : verifyFundamental = true) :
    ∀ X Y : ℝ, loadList squares560 X Y ≤ CAP := by
  have hfund : ∀ X Y : ℝ, 0 ≤ Y → Y ≤ X → X ≤ (4661 : ℝ) / 2000 → loadList squares560 X Y ≤ CAP := by
    intro X Y hY0 hYX hX1
    rcases gridPairs_cover (hY0.trans hYX) hX1 with ⟨⟨x0, x1⟩, hxmem, hx0, hx1⟩
    rcases gridPairs_cover hY0 (hYX.trans hX1) with ⟨⟨y0, y1⟩, hymem, hy0, hy1⟩
    have hv := List.all_eq_true.mp (List.all_eq_true.mp hcert (x0, x1) hxmem) (y0, y1) hymem
    exact hbox 11 x0 x1 y0 y1 2000 squares560
      (fun s hs => (squares560_valid s hs).1) (by norm_num) hv hYX hx0 hx1 hy0 hy1
  intro X Y
  by_cases hin : 0 ≤ X ∧ X ≤ 4661 / 1000 ∧ 0 ≤ Y ∧ Y ≤ 4661 / 1000
  · rcases hin with ⟨hX0, hX1, hY0, hY1⟩
    -- 第 1 步：X 折叠到 [0, 4661/2000]
    obtain ⟨X', hX'0, hX'1, hEq1⟩ :
        ∃ X' : ℝ, 0 ≤ X' ∧ X' ≤ 4661 / 2000 ∧ loadList squares560 X Y = loadList squares560 X' Y := by
      rcases le_total X (4661 / 2000) with h | h
      · exact ⟨X, hX0, h, rfl⟩
      · refine ⟨4661 / 1000 - X, by linarith, by linarith, ?_⟩
        exact (load_flatMap_inv orbits70 (fun a b => (4661 / 1000 - a, b)) load_expandOrbit_reflectX X Y).symm
    -- 第 2 步：Y 折叠到 [0, 4661/2000]
    obtain ⟨Y', hY'0, hY'1, hEq2⟩ :
        ∃ Y' : ℝ, 0 ≤ Y' ∧ Y' ≤ 4661 / 2000 ∧ loadList squares560 X' Y = loadList squares560 X' Y' := by
      rcases le_total Y (4661 / 2000) with h | h
      · exact ⟨Y, hY0, h, rfl⟩
      · refine ⟨4661 / 1000 - Y, by linarith, by linarith, ?_⟩
        exact (load_flatMap_inv orbits70 (fun a b => (a, 4661 / 1000 - b)) load_expandOrbit_reflectY X' Y).symm
    rw [hEq1, hEq2]
    -- 第 3 步：若 Y' > X'，交换 (X', Y')
    rcases le_total Y' X' with hYX | hXY
    · exact hfund X' Y' hY'0 hYX hX'1
    · have hEq3 : loadList squares560 X' Y' = loadList squares560 Y' X' :=
        (load_flatMap_inv orbits70 (fun a b => (b, a)) load_expandOrbit_swapXY X' Y').symm
      rw [hEq3]
      exact hfund Y' X' hX'0 hXY hY'1
  · rw [loadList_zero_outside hin]
    exact Nat.zero_le CAP

end OrbitWitness4661

namespace OrbitWitness4661
set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_0_0 : verifyBox 11 0 2000 0 2000 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_0_1 : verifyBox 11 0 2000 2000 3250 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_0_2 : verifyBox 11 0 2000 3250 3300 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_0_3 : verifyBox 11 0 2000 3300 4000 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_0_4 : verifyBox 11 0 2000 4000 4022 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_0_5 : verifyBox 11 0 2000 4022 4072 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_0_6 : verifyBox 11 0 2000 4072 4661 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_1_0 : verifyBox 11 2000 3250 0 2000 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_1_1 : verifyBox 11 2000 3250 2000 3250 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_1_2 : verifyBox 11 2000 3250 3250 3300 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_1_3 : verifyBox 11 2000 3250 3300 4000 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_1_4 : verifyBox 11 2000 3250 4000 4022 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_1_5 : verifyBox 11 2000 3250 4022 4072 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_1_6 : verifyBox 11 2000 3250 4072 4661 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_2_0 : verifyBox 11 3250 3300 0 2000 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_2_1 : verifyBox 11 3250 3300 2000 3250 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_2_2 : verifyBox 11 3250 3300 3250 3300 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_2_3 : verifyBox 11 3250 3300 3300 4000 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_2_4 : verifyBox 11 3250 3300 4000 4022 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_2_5 : verifyBox 11 3250 3300 4022 4072 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_2_6 : verifyBox 11 3250 3300 4072 4661 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_3_0 : verifyBox 11 3300 4000 0 2000 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_3_1 : verifyBox 11 3300 4000 2000 3250 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_3_2 : verifyBox 11 3300 4000 3250 3300 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_3_3 : verifyBox 11 3300 4000 3300 4000 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_3_4 : verifyBox 11 3300 4000 4000 4022 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_3_5 : verifyBox 11 3300 4000 4022 4072 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_3_6 : verifyBox 11 3300 4000 4072 4661 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_4_0 : verifyBox 11 4000 4022 0 2000 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_4_1 : verifyBox 11 4000 4022 2000 3250 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_4_2 : verifyBox 11 4000 4022 3250 3300 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_4_3 : verifyBox 11 4000 4022 3300 4000 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_4_4 : verifyBox 11 4000 4022 4000 4022 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_4_5 : verifyBox 11 4000 4022 4022 4072 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_4_6 : verifyBox 11 4000 4022 4072 4661 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_5_0 : verifyBox 11 4022 4072 0 2000 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_5_1 : verifyBox 11 4022 4072 2000 3250 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_5_2 : verifyBox 11 4022 4072 3250 3300 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_5_3 : verifyBox 11 4022 4072 3300 4000 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_5_4 : verifyBox 11 4022 4072 4000 4022 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_5_5 : verifyBox 11 4022 4072 4022 4072 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_5_6 : verifyBox 11 4022 4072 4072 4661 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_6_0 : verifyBox 11 4072 4661 0 2000 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_6_1 : verifyBox 11 4072 4661 2000 3250 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_6_2 : verifyBox 11 4072 4661 3250 3300 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_6_3 : verifyBox 11 4072 4661 3300 4000 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_6_4 : verifyBox 11 4072 4661 4000 4022 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_6_5 : verifyBox 11 4072 4661 4022 4072 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem gridBoxCertificate_6_6 : verifyBox 11 4072 4661 4072 4661 2000 squares560 = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 15000000 in
theorem checkFundamentalByGrid : verifyFundamental = true := by
  change (((verifyBox 11 0 2000 0 2000 2000 squares560) && ((verifyBox 11 0 2000 2000 3250 2000 squares560) && ((verifyBox 11 0 2000 3250 3300 2000 squares560) && ((verifyBox 11 0 2000 3300 4000 2000 squares560) && ((verifyBox 11 0 2000 4000 4022 2000 squares560) && ((verifyBox 11 0 2000 4022 4072 2000 squares560) && ((verifyBox 11 0 2000 4072 4661 2000 squares560) && (true)))))))) && (((verifyBox 11 2000 3250 0 2000 2000 squares560) && ((verifyBox 11 2000 3250 2000 3250 2000 squares560) && ((verifyBox 11 2000 3250 3250 3300 2000 squares560) && ((verifyBox 11 2000 3250 3300 4000 2000 squares560) && ((verifyBox 11 2000 3250 4000 4022 2000 squares560) && ((verifyBox 11 2000 3250 4022 4072 2000 squares560) && ((verifyBox 11 2000 3250 4072 4661 2000 squares560) && (true)))))))) && (((verifyBox 11 3250 3300 0 2000 2000 squares560) && ((verifyBox 11 3250 3300 2000 3250 2000 squares560) && ((verifyBox 11 3250 3300 3250 3300 2000 squares560) && ((verifyBox 11 3250 3300 3300 4000 2000 squares560) && ((verifyBox 11 3250 3300 4000 4022 2000 squares560) && ((verifyBox 11 3250 3300 4022 4072 2000 squares560) && ((verifyBox 11 3250 3300 4072 4661 2000 squares560) && (true)))))))) && (((verifyBox 11 3300 4000 0 2000 2000 squares560) && ((verifyBox 11 3300 4000 2000 3250 2000 squares560) && ((verifyBox 11 3300 4000 3250 3300 2000 squares560) && ((verifyBox 11 3300 4000 3300 4000 2000 squares560) && ((verifyBox 11 3300 4000 4000 4022 2000 squares560) && ((verifyBox 11 3300 4000 4022 4072 2000 squares560) && ((verifyBox 11 3300 4000 4072 4661 2000 squares560) && (true)))))))) && (((verifyBox 11 4000 4022 0 2000 2000 squares560) && ((verifyBox 11 4000 4022 2000 3250 2000 squares560) && ((verifyBox 11 4000 4022 3250 3300 2000 squares560) && ((verifyBox 11 4000 4022 3300 4000 2000 squares560) && ((verifyBox 11 4000 4022 4000 4022 2000 squares560) && ((verifyBox 11 4000 4022 4022 4072 2000 squares560) && ((verifyBox 11 4000 4022 4072 4661 2000 squares560) && (true)))))))) && (((verifyBox 11 4022 4072 0 2000 2000 squares560) && ((verifyBox 11 4022 4072 2000 3250 2000 squares560) && ((verifyBox 11 4022 4072 3250 3300 2000 squares560) && ((verifyBox 11 4022 4072 3300 4000 2000 squares560) && ((verifyBox 11 4022 4072 4000 4022 2000 squares560) && ((verifyBox 11 4022 4072 4022 4072 2000 squares560) && ((verifyBox 11 4022 4072 4072 4661 2000 squares560) && (true)))))))) && (((verifyBox 11 4072 4661 0 2000 2000 squares560) && ((verifyBox 11 4072 4661 2000 3250 2000 squares560) && ((verifyBox 11 4072 4661 3250 3300 2000 squares560) && ((verifyBox 11 4072 4661 3300 4000 2000 squares560) && ((verifyBox 11 4072 4661 4000 4022 2000 squares560) && ((verifyBox 11 4072 4661 4022 4072 2000 squares560) && ((verifyBox 11 4072 4661 4072 4661 2000 squares560) && (true)))))))) && (true)))))))) = true
  simp only [gridBoxCertificate_0_0, gridBoxCertificate_0_1, gridBoxCertificate_0_2, gridBoxCertificate_0_3, gridBoxCertificate_0_4, gridBoxCertificate_0_5, gridBoxCertificate_0_6, gridBoxCertificate_1_0, gridBoxCertificate_1_1, gridBoxCertificate_1_2, gridBoxCertificate_1_3, gridBoxCertificate_1_4, gridBoxCertificate_1_5, gridBoxCertificate_1_6, gridBoxCertificate_2_0, gridBoxCertificate_2_1, gridBoxCertificate_2_2, gridBoxCertificate_2_3, gridBoxCertificate_2_4, gridBoxCertificate_2_5, gridBoxCertificate_2_6, gridBoxCertificate_3_0, gridBoxCertificate_3_1, gridBoxCertificate_3_2, gridBoxCertificate_3_3, gridBoxCertificate_3_4, gridBoxCertificate_3_5, gridBoxCertificate_3_6, gridBoxCertificate_4_0, gridBoxCertificate_4_1, gridBoxCertificate_4_2, gridBoxCertificate_4_3, gridBoxCertificate_4_4, gridBoxCertificate_4_5, gridBoxCertificate_4_6, gridBoxCertificate_5_0, gridBoxCertificate_5_1, gridBoxCertificate_5_2, gridBoxCertificate_5_3, gridBoxCertificate_5_4, gridBoxCertificate_5_5, gridBoxCertificate_5_6, gridBoxCertificate_6_0, gridBoxCertificate_6_1, gridBoxCertificate_6_2, gridBoxCertificate_6_3, gridBoxCertificate_6_4, gridBoxCertificate_6_5, gridBoxCertificate_6_6, Bool.and_true]
end OrbitWitness4661

open scoped BigOperators

namespace SquarePackingDiagnostic

abbrev inside (x y a b X Y : ℝ) : Prop :=
  |a * (X - x) + b * (Y - y)| < 1 / 2 ∧
    |(-b) * (X - x) + a * (Y - y)| < 1 / 2

def admissible (x y a b : ℝ) : Prop :=
  a ^ 2 + b ^ 2 = 1 ∧
    |a| + |b| ≤ 2 * x ∧ |a| + |b| ≤ 2 * ((4661 / 1000 : ℝ) - x) ∧
    |a| + |b| ≤ 2 * y ∧ |a| + |b| ≤ 2 * ((4661 / 1000 : ℝ) - y)

theorem no_weighted_sites_of_fractional_packing
    (p : ℕ) (cx cy ca cb : Fin p → ℝ) (v : Fin p → ℕ) (cap : ℕ)
    (hcap : 0 < cap) (hof : 17 * cap ≤ ∑ i, v i)
    (hgeom : ∀ i, admissible (cx i) (cy i) (ca i) (cb i))
    (hdepth : ∀ X Y : ℝ, ∑ i, (if inside (cx i) (cy i) (ca i) (cb i) X Y then v i else 0) ≤ cap) :
    ¬ (let inside := fun (x y a b X Y : ℝ) =>
          |a*(X-x)+b*(Y-y)| < 1/2 ∧ |(-b)*(X-x)+a*(Y-y)| < 1/2
       ∃ (k : ℕ) (X Y : Fin k → ℚ) (w : Fin k → ℕ) (q : ℕ), 0 < q ∧
         (∑ j, w j) < 17*q ∧ ∀ x y a b : ℝ,
           (a ^ 2 + b ^ 2 = 1 ∧ |a| + |b| ≤ 2*x ∧ |a| + |b| ≤ 2*((4661/1000:ℝ)-x) ∧
             |a| + |b| ≤ 2*y ∧ |a| + |b| ≤ 2*((4661/1000:ℝ)-y)) →
           q ≤ (∑ j : Fin k, (if inside x y a b (X j) (Y j) then w j else 0))) := by
  rintro ⟨k, X, Y, w, q, _, hw, hcover⟩
  let hit (i : Fin p) (j : Fin k) : Prop :=
    inside (cx i) (cy i) (ca i) (cb i) (X j) (Y j)
  have hrow (i : Fin p) : q ≤ ∑ j : Fin k, if hit i j then w j else 0 :=
    hcover _ _ _ _ (hgeom i)
  have hcol (j : Fin k) : (∑ i : Fin p, if hit i j then v i else 0) ≤ cap :=
    hdepth (X j) (Y j)
  have hbudget : (∑ i, v i) * q ≤ cap * ∑ j, w j := by
    calc
      (∑ i, v i) * q = ∑ i, v i * q := Finset.sum_mul _ _ _
      _ ≤ ∑ i : Fin p, v i * ∑ j : Fin k, if hit i j then w j else 0 :=
        Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left (v i) (hrow i))
      _ = ∑ j : Fin k, (∑ i : Fin p, if hit i j then v i else 0) * w j := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul, mul_zero, zero_mul]
        exact Finset.sum_comm
      _ ≤ ∑ j, cap * w j := Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_right (w j) (hcol j))
      _ = cap * ∑ j, w j := (Finset.mul_sum _ _ _).symm
  have hge : 17 * cap * q ≤ cap * ∑ j, w j :=
    (Nat.mul_le_mul_right q hof).trans hbudget
  have hlt : cap * ∑ j, w j < 17 * cap * q := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left hw hcap
  exact (Nat.not_lt_of_ge hge) hlt

end SquarePackingDiagnostic

open scoped BigOperators Classical

namespace OrbitWitness4661

private lemma sum_fin_get_eq_list_map_sum {α : Type*} (l : List α) (f : α → ℕ) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons]
    change (∑ i : Fin (t.length + 1), f ((a :: t).get i)) = f a + (t.map f).sum
    rw [Fin.sum_univ_succ]
    exact congrArg (f a + ·) ih

private lemma loadList_eq_map_sum (L : List _) (X Y : ℝ) :
    loadList L X Y = (L.map (fun s => if sqInside s X Y then s.w else 0)).sum := by
  induction L with
  | nil => simp [loadList]
  | cons s t ih =>
    simp only [List.map_cons, List.sum_cons, ← ih]
    by_cases h : sqInside s X Y <;> simp [loadList, h]

theorem refute_weighted_sites_of_depth
    (hdepth : ∀ X Y : ℝ, loadList squares560 X Y ≤ CAP) :
    ¬ (let inside := fun (x y a b X Y : ℝ) =>
          |a*(X-x)+b*(Y-y)| < 1/2 ∧ |(-b)*(X-x)+a*(Y-y)| < 1/2
       ∃ (k : ℕ) (X Y : Fin k → ℚ) (w : Fin k → ℕ) (q : ℕ), 0 < q ∧
         (∑ j, w j) < 17*q ∧ ∀ x y a b : ℝ,
           (a ^ 2 + b ^ 2 = 1 ∧ |a| + |b| ≤ 2*x ∧ |a| + |b| ≤ 2*((4661/1000:ℝ)-x) ∧
             |a| + |b| ≤ 2*y ∧ |a| + |b| ≤ 2*((4661/1000:ℝ)-y)) →
           q ≤ (∑ j : Fin k, (if inside x y a b (X j) (Y j) then w j else 0))) := by
  let cx : Fin squares560.length → ℝ := fun i => ((squares560.get i).cx : ℝ) / 1000
  let cy : Fin squares560.length → ℝ := fun i => ((squares560.get i).cy : ℝ) / 1000
  let ca : Fin squares560.length → ℝ := fun i => ((squares560.get i).p : ℝ) / (squares560.get i).r
  let cb : Fin squares560.length → ℝ := fun i => ((squares560.get i).q : ℝ) / (squares560.get i).r
  let v : Fin squares560.length → ℕ := fun i => (squares560.get i).w
  have hcap : 0 < CAP := by
    unfold CAP
    omega
  have hsum_w :
      (∑ i : Fin squares560.length, v i) = (squares560.map (fun s => s.w)).sum :=
    sum_fin_get_eq_list_map_sum squares560 (fun s => s.w)
  have hof : 17 * CAP ≤ ∑ i : Fin squares560.length, v i := by
    have htot := squares560_total_weight
    have hstrict := strict_over_17_cap
    rw [hsum_w]
    omega
  have hgeom : ∀ i : Fin squares560.length,
      SquarePackingDiagnostic.admissible (cx i) (cy i) (ca i) (cb i) := by
    intro i
    have hs : squares560.get i ∈ squares560 := by simp
    exact (squares560_valid (squares560.get i) hs).2
  have hdepth' : ∀ X Y : ℝ,
      (∑ i : Fin squares560.length,
        if SquarePackingDiagnostic.inside (cx i) (cy i) (ca i) (cb i) X Y then v i else 0) ≤ CAP := by
    intro X Y
    have hinside : ∀ i : Fin squares560.length,
        SquarePackingDiagnostic.inside (cx i) (cy i) (ca i) (cb i) X Y ↔
          sqInside (squares560.get i) X Y := by
      intro i
      rfl
    have hsum_load :
        (∑ i : Fin squares560.length,
          if SquarePackingDiagnostic.inside (cx i) (cy i) (ca i) (cb i) X Y then v i else 0) =
        loadList squares560 X Y := by
      calc
        (∑ i : Fin squares560.length,
            if SquarePackingDiagnostic.inside (cx i) (cy i) (ca i) (cb i) X Y then v i else 0)
          = ∑ i : Fin squares560.length,
              if sqInside (squares560.get i) X Y then (squares560.get i).w else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i _
              exact if_congr (hinside i) rfl rfl
        _ = (squares560.map (fun s => if sqInside s X Y then s.w else 0)).sum :=
              sum_fin_get_eq_list_map_sum squares560 (fun s => if sqInside s X Y then s.w else 0)
        _ = loadList squares560 X Y := (loadList_eq_map_sum squares560 X Y).symm
    rw [hsum_load]
    exact hdepth X Y
  exact SquarePackingDiagnostic.no_weighted_sites_of_fractional_packing
    squares560.length cx cy ca cb v CAP hcap hof hgeom hdepth'

end OrbitWitness4661

open scoped BigOperators Classical

theorem SquarePackingSeventeenWeightedSites4661Refutation :
    ¬ (let inside := fun (x y a b X Y : ℝ) => |a*(X-x)+b*(Y-y)| < 1/2 ∧ |(-b)*(X-x)+a*(Y-y)| < 1/2; ∃ (k : ℕ) (X Y : Fin k → ℚ) (w : Fin k → ℕ) (q : ℕ), 0 < q ∧ (∑ j, w j) < 17*q ∧ ∀ x y a b : ℝ, (a ^ 2 + b ^ 2 = 1 ∧ |a| + |b| ≤ 2*x ∧ |a| + |b| ≤ 2*((4661/1000:ℝ)-x) ∧ |a| + |b| ≤ 2*y ∧ |a| + |b| ≤ 2*((4661/1000:ℝ)-y)) → q ≤ (∑ j : Fin k, (if inside x y a b (X j) (Y j) then w j else 0))) :=
  OrbitWitness4661.refute_weighted_sites_of_depth
    (OrbitWitness4661.verifyFundamental_sound_of_box_sound
      OrbitWitness4661.verifyBox_sound OrbitWitness4661.checkFundamentalByGrid)

#print axioms SquarePackingSeventeenWeightedSites4661Refutation
