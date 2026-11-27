import Mathlib

private theorem sqr_pick (s c m w0 : ℝ) (hs : 0 < s) (hc : 0 < c) (hcs : c ^ 2 + s ^ 2 = 1)
    (hsc : s * c ≤ 1 / 2) (hh : 28 / 25 ≤ c + s) (hm1 : m ≤ 1 / 2) (hm2 : -1 / 2 < m) :
    ∃ i : ℤ, |c * m - s * ((i : ℝ) / 10 - w0)| < 1 / 2 ∧ |s * m + c * ((i : ℝ) / 10 - w0)| < 1 / 2 := by
  have hs1 : s ≤ 1 := by nlinarith [sq_nonneg c]
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg s]
  obtain ⟨l1, hl1⟩ : ∃ l1 : ℝ, s * l1 = c * m - 1 / 2 := ⟨(c * m - 1 / 2) / s, by field_simp⟩
  obtain ⟨u1, hu1⟩ : ∃ u1 : ℝ, s * u1 = c * m + 1 / 2 := ⟨(c * m + 1 / 2) / s, by field_simp⟩
  obtain ⟨l2, hl2⟩ : ∃ l2 : ℝ, c * l2 = -s * m - 1 / 2 := ⟨(-s * m - 1 / 2) / c, by field_simp⟩
  obtain ⟨u2, hu2⟩ : ∃ u2 : ℝ, c * u2 = -s * m + 1 / 2 := ⟨(-s * m + 1 / 2) / c, by field_simp⟩
  have hsc0 : 0 < s * c := mul_pos hs hc
  have a1 : l1 + 1 / 10 < u1 := by
    by_contra hn; push_neg at hn
    nlinarith [mul_nonneg hs.le (sub_nonneg.2 hn)]
  have a2 : l2 + 1 / 10 < u2 := by
    by_contra hn; push_neg at hn
    nlinarith [mul_nonneg hc.le (sub_nonneg.2 hn)]
  have a3 : l1 + 1 / 10 < u2 := by
    by_contra hn; push_neg at hn
    have e : (u2 - l1 - 1 / 10) * (s * c) = -m + (c + s) / 2 - s * c / 10 := by
      have : (u2 - l1 - 1 / 10) * (s * c) = s * (c * u2) - c * (s * l1) - s * c / 10 := by ring
      rw [this, hu2, hl1]; linear_combination (-m) * hcs
    nlinarith [mul_nonneg hsc0.le (sub_nonneg.2 hn)]
  have a4 : l2 + 1 / 10 < u1 := by
    by_contra hn; push_neg at hn
    have e : (u1 - l2 - 1 / 10) * (s * c) = m + (c + s) / 2 - s * c / 10 := by
      have : (u1 - l2 - 1 / 10) * (s * c) = c * (s * u1) - s * (c * l2) - s * c / 10 := by ring
      rw [this, hu1, hl2]; linear_combination m * hcs
    nlinarith [mul_nonneg hsc0.le (sub_nonneg.2 hn)]
  have hL1 : max l1 l2 + 1 / 10 < u1 := by
    rcases le_total l1 l2 with h | h
    · rw [max_eq_right h]; exact a4
    · rw [max_eq_left h]; exact a1
  have hL2 : max l1 l2 + 1 / 10 < u2 := by
    rcases le_total l1 l2 with h | h
    · rw [max_eq_right h]; exact a2
    · rw [max_eq_left h]; exact a3
  refine ⟨⌊10 * (w0 + max l1 l2)⌋ + 1, ?_⟩
  have f1 := Int.lt_floor_add_one (10 * (w0 + max l1 l2))
  have f2 := Int.floor_le (10 * (w0 + max l1 l2))
  push_cast
  set i : ℝ := (⌊10 * (w0 + max l1 l2)⌋ : ℝ) with hi
  have t1 : max l1 l2 < (i + 1) / 10 - w0 := by linarith
  have t2 : (i + 1) / 10 - w0 < u1 := by linarith
  have t3 : (i + 1) / 10 - w0 < u2 := by linarith
  have t4 : l1 < (i + 1) / 10 - w0 := lt_of_le_of_lt (le_max_left _ _) t1
  have t5 : l2 < (i + 1) / 10 - w0 := lt_of_le_of_lt (le_max_right _ _) t1
  have p1 := mul_lt_mul_of_pos_left t4 hs
  have p2 := mul_lt_mul_of_pos_left t2 hs
  have p3 := mul_lt_mul_of_pos_left t5 hc
  have p4 := mul_lt_mul_of_pos_left t3 hc
  have e1 : (i + 1) / 10 - w0 = ((i + 1 : ℝ) / 10 - w0) := rfl
  constructor
  · rw [abs_lt]; constructor <;> nlinarith
  · rw [abs_lt]; constructor <;> nlinarith

private theorem sqr_core (x y a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (h1 : a ^ 2 + b ^ 2 = 1)
    (hx1 : a + b ≤ 2 * x) (hx2 : a + b ≤ 2 * ((4661 / 1000 : ℝ) - x))
    (hy1 : a + b ≤ 2 * y) (hy2 : a + b ≤ 2 * ((4661 / 1000 : ℝ) - y)) :
    ∃ j n : ℕ, j < 8 ∧ n < 71 ∧
      |a * ((3 * (j : ℝ) / 5 - 2 * ((n : ℝ) - 40) / 25) - x)
        + b * ((4 * (j : ℝ) / 5 + 3 * ((n : ℝ) - 40) / 50) - y)| < 1 / 2 ∧
      |(-b) * ((3 * (j : ℝ) / 5 - 2 * ((n : ℝ) - 40) / 25) - x)
        + a * ((4 * (j : ℝ) / 5 + 3 * ((n : ℝ) - 40) / 50) - y)| < 1 / 2 := by
  have ha : 0 ≤ a := le_trans hb hba
  have ha2 : 1 / 2 ≤ a ^ 2 := by nlinarith
  have hab : b ^ 2 ≤ a * b := by nlinarith
  have h32 : 32 ≤ (7 * a + b) ^ 2 := by nlinarith
  have h7 : 28 / 5 ≤ 7 * a + b := by
    by_contra hlt; push_neg at hlt
    nlinarith
  have hapos : 0 < a := by nlinarith
  have hs : 0 < (4 * a - 3 * b) / 5 := by linarith
  have hc : 0 < (3 * a + 4 * b) / 5 := by linarith
  have hcs : ((3 * a + 4 * b) / 5) ^ 2 + ((4 * a - 3 * b) / 5) ^ 2 = 1 := by linear_combination h1
  have hsc : ((4 * a - 3 * b) / 5) * ((3 * a + 4 * b) / 5) ≤ 1 / 2 := by
    nlinarith [sq_nonneg ((3 * a + 4 * b) / 5 - (4 * a - 3 * b) / 5)]
  have hh : 28 / 25 ≤ (3 * a + 4 * b) / 5 + (4 * a - 3 * b) / 5 := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hu0 : 0 ≤ (3 * x + 4 * y) / 5 + 1 / 2 := by linarith
  have g1 := Nat.floor_le hu0
  have g2 := Nat.lt_floor_add_one ((3 * x + 4 * y) / 5 + 1 / 2)
  set j : ℕ := ⌊(3 * x + 4 * y) / 5 + 1 / 2⌋₊ with hj
  obtain ⟨i0, hi1, hi2⟩ := sqr_pick ((4 * a - 3 * b) / 5) ((3 * a + 4 * b) / 5) ((j : ℝ) - (3 * x + 4 * y) / 5)
    ((-4 * x + 3 * y) / 5) hs hc hcs hsc hh (by linarith) (by linarith)
  have e1 : a * ((3 * (j : ℝ) / 5 - 2 * (i0 : ℝ) / 25) - x)
      + b * ((4 * (j : ℝ) / 5 + 3 * (i0 : ℝ) / 50) - y)
      = ((3 * a + 4 * b) / 5) * ((j : ℝ) - (3 * x + 4 * y) / 5)
        - ((4 * a - 3 * b) / 5) * ((i0 : ℝ) / 10 - (-4 * x + 3 * y) / 5) := by ring
  have e2 : (-b) * ((3 * (j : ℝ) / 5 - 2 * (i0 : ℝ) / 25) - x)
      + a * ((4 * (j : ℝ) / 5 + 3 * (i0 : ℝ) / 50) - y)
      = ((4 * a - 3 * b) / 5) * ((j : ℝ) - (3 * x + 4 * y) / 5)
        + ((3 * a + 4 * b) / 5) * ((i0 : ℝ) / 10 - (-4 * x + 3 * y) / 5) := by ring
  rw [← e1] at hi1
  rw [← e2] at hi2
  set X : ℝ := 3 * (j : ℝ) / 5 - 2 * (i0 : ℝ) / 25 with hX
  set Y : ℝ := 4 * (j : ℝ) / 5 + 3 * (i0 : ℝ) / 50 with hY
  have hp := abs_lt.1 hi1
  have hq := abs_lt.1 hi2
  set p := a * (X - x) + b * (Y - y) with hpdef
  set q := (-b) * (X - x) + a * (Y - y) with hqdef
  have dX : X - x = a * p - b * q := by rw [hpdef, hqdef]; linear_combination (-(X - x)) * h1
  have dY : Y - y = b * p + a * q := by rw [hpdef, hqdef]; linear_combination (-(Y - y)) * h1
  have m1 := mul_le_mul_of_nonneg_left hp.2.le ha
  have m2 := mul_le_mul_of_nonneg_left hq.2.le hb
  have m3 := mul_le_mul_of_nonneg_left hp.1.le ha
  have m4 := mul_le_mul_of_nonneg_left hq.1.le hb
  have m5 := mul_le_mul_of_nonneg_left hp.2.le hb
  have m6 := mul_le_mul_of_nonneg_left hp.1.le hb
  have m7 := mul_le_mul_of_nonneg_left hq.2.le ha
  have m8 := mul_le_mul_of_nonneg_left hq.1.le ha
  have bX1 : X ≤ 4661 / 1000 := by linarith
  have bX3 : 0 ≤ X := by linarith
  have bY1 : Y ≤ 4661 / 1000 := by linarith
  have bY3 : 0 ≤ Y := by linarith
  have hi : (i0 : ℝ) = 2 * (-4 * X + 3 * Y) := by rw [hX, hY]; ring
  have hlo : (-40 : ℝ) ≤ i0 := by rw [hi]; linarith
  have hhi : (i0 : ℝ) ≤ 30 := by rw [hi]; linarith
  have hlo' : (-40 : ℤ) ≤ i0 := by exact_mod_cast hlo
  have hhi' : i0 ≤ (30 : ℤ) := by exact_mod_cast hhi
  have hj8 : j < 8 := by
    have : (j : ℝ) < 8 := by linarith
    exact_mod_cast this
  have hn : ((i0 + 40).toNat : ℤ) = i0 + 40 := Int.toNat_of_nonneg (by omega)
  have hnr : (((i0 + 40).toNat : ℕ) : ℝ) = (i0 : ℝ) + 40 := by exact_mod_cast hn
  refine ⟨j, (i0 + 40).toNat, hj8, by omega, ?_, ?_⟩
  · rw [hnr, add_sub_cancel_right]; exact hi1
  · rw [hnr, add_sub_cancel_right]; exact hi2

theorem Conjectures.SquarePacking.SeventeenChargeAngleRefutation :
    ¬ (let inside := fun (x y a b X Y : ℝ) => |a*(X-x)+b*(Y-y)| < 1/2 ∧ |(-b)*(X-x)+a*(Y-y)| < 1/2; ∀ (k q : ℕ) (X Y : Fin k → ℚ) (w : Fin k → ℕ), (∀ x y a b : ℝ, 0 ≤ b → b ≤ a → (a ^ 2 + b ^ 2 = 1 ∧ |a| + |b| ≤ 2*x ∧ |a| + |b| ≤ 2*((4661/1000:ℝ)-x) ∧ |a| + |b| ≤ 2*y ∧ |a| + |b| ≤ 2*((4661/1000:ℝ)-y)) → q ≤ (∑ j : Fin k, (if inside x y a b (X j) (Y j) then w j else 0))) → ∀ x y a b : ℝ, (a ^ 2 + b ^ 2 = 1 ∧ |a| + |b| ≤ 2*x ∧ |a| + |b| ≤ 2*((4661/1000:ℝ)-x) ∧ |a| + |b| ≤ 2*y ∧ |a| + |b| ≤ 2*((4661/1000:ℝ)-y)) → q ≤ (∑ j : Fin k, (if inside x y a b (X j) (Y j) then w j else 0))) := by
  intro h
  dsimp only at h
  have H := h (8 * 71) 1
    (fun n => (3 * (((n : ℕ) / 71 : ℕ) : ℚ) / 5 - 2 * ((((n : ℕ) % 71 : ℕ) : ℚ) - 40) / 25))
    (fun n => (4 * (((n : ℕ) / 71 : ℕ) : ℚ) / 5 + 3 * ((((n : ℕ) % 71 : ℕ) : ℚ) - 40) / 50))
    (fun _ => 1) (by
      intro x y a b hb hba hf
      obtain ⟨h1, h2, h3, h4, h5⟩ := hf
      rw [abs_of_nonneg (hb.trans hba), abs_of_nonneg hb] at h2 h3 h4 h5
      obtain ⟨j, n, hj, hn, c1, c2⟩ := sqr_core x y a b hb hba h1 h2 h3 h4 h5
      have hd : (j * 71 + n) / 71 = j := by omega
      have hm : (j * 71 + n) % 71 = n := by omega
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ (⟨j * 71 + n, by omega⟩ : Fin (8 * 71))))
      split_ifs with hc
      · exact le_rfl
      · exfalso
        apply hc
        simp only [Fin.val_mk, hd, hm]
        constructor
        · push_cast; exact c1
        · push_cast; exact c2)
  have H2 := H (3 / 2) 2 (3 / 5) (4 / 5)
    (by refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩ <;> norm_num [abs_of_pos])
  rw [Finset.sum_eq_zero] at H2
  · omega
  · intro n _
    rw [if_neg]
    rintro ⟨c1, c2⟩
    push_cast at c1
    rw [abs_lt] at c1
    obtain ⟨c1a, c1b⟩ := c1
    have k1 : (2 : ℝ) < (((n : ℕ) / 71 : ℕ) : ℝ) := by linarith
    have k2 : (((n : ℕ) / 71 : ℕ) : ℝ) < 3 := by linarith
    have k3 : 2 < (n : ℕ) / 71 := by exact_mod_cast k1
    have k4 : (n : ℕ) / 71 < 3 := by exact_mod_cast k2
    omega
