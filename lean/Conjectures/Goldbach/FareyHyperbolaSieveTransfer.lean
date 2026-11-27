import Mathlib

/- Apache-2.0, goldbach-proofs. The interval transfer below is by Hou Muyang
   (houmy555809), source 042694bdaac5916044fda60ababeefd4789ab06d. The CRT
   root count is by SaladDay, source a48cadcf205672e6e2dcaffaa27793e1fc971b85.
   Both are restricted to private helpers. The per-residue estimate, treatment
   of empty fibers, and summation into the stated rectangle bound are new. -/



/-!
# PREPUB goldbach gap: `L-goldbach-farey-hyperbola-shift`

For `n > 1`, `0 < d`, `b < d`, interval `[l,h] ⊆ [0,n)` and a shift `s` with
`d*s ≡ b (mod n)`, the Farey hyperbola count over the residue class `u ≡ b (mod d)`
is transported to a shifted interval `I = [lo+s, hi+s]` (with `lo = ceil((l-b)/d)`,
`hi = floor((h-b)/d)`): the shifted index satisfies `hi + s < n`, the coprime-inverse
count is preserved (`u*j ≡ 1` vs `v*j ≡ c` with `d*c ≡ 1`), and `#I` differs from
`(h-l+1)/d` by at most one.
-/

open scoped BigOperators
open Finset



/-- 区间 `[l,h]` 中与 `v` 同余模 `d` 的个数与 `(h-l+1)/d` 的偏差 ≤ 1。 -/
private lemma card_Icc_residue_abs (d v l h : ℕ) (hd : 0 < d) :
    |((((Finset.Icc l h).filter (fun u => u % d = v % d)).card : ℕ) : ℝ)
      - ((h - l + 1 : ℕ) : ℝ) / (d : ℝ)| ≤ 1 := by
  by_cases hlh : l ≤ h
  · have hIco : Finset.Ico l (h + 1) = Finset.Icc l h := Finset.Ico_succ_right_eq_Icc l h
    have hS : (Finset.Icc l h).filter (fun u => u % d = v % d)
        = (Finset.Ico l (h + 1)).filter (fun u => u ≡ v [MOD d]) := by
      rw [← hIco]
      exact Finset.filter_congr (fun u _ => Iff.rfl)
    rw [hS]
    have hform := Nat.Ico_filter_modEq_card l (h + 1) hd v
    set y : ℚ := (((h + 1 : ℕ) : ℚ) - (v : ℚ)) / (d : ℚ)
    set x : ℚ := (((l : ℕ) : ℚ) - (v : ℚ)) / (d : ℚ)
    set A : ℤ := ⌈y⌉
    set B : ℤ := ⌈x⌉
    have hform' : ((((Finset.Ico l (h + 1)).filter (fun u => u ≡ v [MOD d])).card : ℕ) : ℤ)
        = max (A - B) 0 := by
      simpa [A, B, y, x] using hform
    have hdQ : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
    have hxy : x ≤ y := by
      apply div_le_div_of_nonneg_right _ hdQ.le
      have hcast : ((l : ℚ)) ≤ ((h + 1 : ℕ) : ℚ) := by
        exact_mod_cast (Nat.le_succ_of_le hlh)
      linarith
    have hleA : y ≤ (A : ℚ) := by simpa [A] using Int.le_ceil y
    have hltA : ((A : ℚ)) < y + 1 := by simpa [A] using Int.ceil_lt_add_one y
    have hleB : x ≤ (B : ℚ) := by simpa [B] using Int.le_ceil x
    have hltB : ((B : ℚ)) < x + 1 := by simpa [B] using Int.ceil_lt_add_one x
    have hMx : y - x = (((h - l + 1 : ℕ) : ℚ)) / (d : ℚ) := by
      have hnum : (((h + 1 : ℕ) : ℚ) - (v : ℚ)) - (((l : ℕ) : ℚ) - (v : ℚ))
          = (((h - l + 1 : ℕ) : ℚ)) := by
        have hcast : (((h - l + 1 : ℕ) : ℚ)) = ((h + 1 : ℕ) : ℚ) - ((l : ℕ) : ℚ) := by
          rw [show h - l + 1 = (h + 1) - l by omega,
            Nat.cast_sub (by omega : l ≤ h + 1)]
        rw [hcast]
        ring
      calc y - x = ((((h + 1 : ℕ) : ℚ) - (v : ℚ)) - (((l : ℕ) : ℚ) - (v : ℚ))) / (d : ℚ) := by
            simp only [y, x, sub_div]
        _ = (((h - l + 1 : ℕ) : ℚ)) / (d : ℚ) := by rw [hnum]
    have hAB_nonneg : (0 : ℤ) ≤ A - B := by
      have hBA : (B : ℚ) < (A : ℚ) + 1 := by linarith [hltB, hxy, hleA]
      have hBA' : B < A + 1 := by exact_mod_cast hBA
      omega
    have hα_le : ((A : ℚ) - (B : ℚ)) < (((h - l + 1 : ℕ) : ℚ)) / (d : ℚ) + 1 := by
      linarith [hltA, hleB, hMx]
    have hα_ge : (((h - l + 1 : ℕ) : ℚ)) / (d : ℚ) - 1 < ((A : ℚ) - (B : ℚ)) := by
      linarith [hleA, hltB, hMx]
    have hform'' : ((((Finset.Ico l (h + 1)).filter (fun u => u ≡ v [MOD d])).card : ℕ) : ℤ)
        = A - B := by
      rw [hform', max_eq_left hAB_nonneg]
    have hcard_nat : (((Finset.Ico l (h + 1)).filter (fun u => u ≡ v [MOD d])).card : ℕ)
        = (A - B).toNat := by
      conv_rhs => rw [← hform'']
      exact (Int.toNat_natCast _).symm
    have hcardR : ((((Finset.Ico l (h + 1)).filter (fun u => u ≡ v [MOD d])).card : ℕ) : ℝ)
        = ((A : ℝ) - (B : ℝ)) := by
      rw [hcard_nat]
      have hcast1 : ((((A - B).toNat : ℕ)) : ℝ) = (((A - B : ℤ) : ℝ)) := by
        have h3 : ((A - B).toNat : ℤ) = A - B := Int.toNat_of_nonneg hAB_nonneg
        calc ((((A - B).toNat : ℕ)) : ℝ) = ((((A - B).toNat : ℤ)) : ℝ) := by push_cast; ring
          _ = ((A - B : ℤ) : ℝ) := by rw [h3]
      rw [hcast1]
      push_cast
      ring
    rw [hcardR]
    have hMdR : (((h - l + 1 : ℕ) : ℝ) / (d : ℝ))
        = ((((h - l + 1 : ℕ) : ℚ)) / (d : ℚ) : ℚ) := by push_cast; ring
    have hq : |((A : ℚ) - (B : ℚ)) - (((h - l + 1 : ℕ) : ℚ)) / (d : ℚ)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hα_ge, hα_le]
    have hcast : (((A : ℝ) - (B : ℝ)) - (((h - l + 1 : ℕ) : ℝ) / (d : ℝ)))
        = ((((A : ℚ) - (B : ℚ)) - (((h - l + 1 : ℕ) : ℚ)) / (d : ℚ))) := by
      push_cast
      ring
    rw [hcast]
    exact_mod_cast hq
  · push_neg at hlh
    have hempty : (Finset.Icc l h) = ∅ := by
      rcases Finset.eq_empty_or_nonempty (Finset.Icc l h) with h | ⟨u, hu⟩
      · exact h
      · exfalso
        rw [Finset.mem_Icc] at hu
        omega
    have hM1 : h - l + 1 = 1 := by omega
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have key : |(0 : ℝ) - (1 : ℝ) / (d : ℝ)| ≤ 1 := by
      rw [zero_sub, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (d : ℝ))]
      rw [div_le_one hdpos]
      exact_mod_cast hd
    simpa [hempty, hM1] using key


/-! ### 辅助引理 -/

/-- `u % d = b` 时 `u = b + d*(u/d)`。 -/
private lemma eq_b_add_mul_div {u d b : ℕ} (hud : u % d = b) : u = b + d * (u / d) := by
  have h := Nat.div_add_mod u d
  rw [hud] at h
  omega

/-- `l - b ≤ d * ((l+d-1-b)/d)`。 -/
private lemma lo_mul_ge (l b d : ℕ) (hd : 0 < d) : l - b ≤ d * ((l + d - 1 - b) / d) := by
  have h := Nat.div_add_mod (l + d - 1 - b) d
  have hrem : (l + d - 1 - b) % d ≤ d - 1 := by
    have := Nat.mod_lt (l + d - 1 - b) hd
    omega
  have hdX : d * ((l + d - 1 - b) / d) = (l + d - 1 - b) - ((l + d - 1 - b) % d) := by
    omega
  rw [hdX]
  omega

/-- `d * (hi) ≤ h - b`（`hi = (h-b)/d`）。 -/
private lemma hi_mul_le (h b d : ℕ) : d * ((h - b) / d) ≤ h - b := by
  have h := Nat.div_add_mod (h - b) d
  omega

/-- 双射核心：`d*(u/d + s) ≡ u (mod n)`（`u % d = b`，`d*s ≡ b`）。 -/
private lemma dvd_shift_modEq {n d b s u : ℕ} (hds : d * s ≡ b [MOD n]) (hud : u % d = b) :
    d * (u / d + s) ≡ u [MOD n] := by
  have hu : u = b + d * (u / d) := eq_b_add_mul_div hud
  have hmul : d * (u / d + s) = d * (u / d) + d * s := by ring
  rw [hmul]
  have h1 : d * (u / d) + d * s ≡ d * (u / d) + b [MOD n] :=
    (Nat.ModEq.refl (d * (u / d))).add hds
  have h2 : d * (u / d) + b = u := by omega
  rwa [h2] at h1



/-- `ceil((l-b)/d) ≤ u/d`（`u % d = b`、`l ≤ u`）。 -/
private lemma lo_le_div {d b u l : ℕ} (hd : 0 < d) (hu : u % d = b) (hul : l ≤ u) :
    (l + d - 1 - b) / d ≤ u / d := by
  have hu_eq : u = b + d * (u / d) := eq_b_add_mul_div hu
  have hL : l - b ≤ d * (u / d) := by omega
  rw [Nat.div_le_iff_le_mul_add_pred hd]
  omega

/-- `u/d ≤ floor((h-b)/d)`（`u % d = b`、`u ≤ h`）。 -/
private lemma div_le_hi_div {d b u h : ℕ} (hd : 0 < d) (hu : u % d = b) (huh : u ≤ h) :
    u / d ≤ (h - b) / d := by
  rw [Nat.le_div_iff_mul_le hd]
  have hu_eq : u = b + d * (u / d) := eq_b_add_mul_div hu
  have hsub : (u / d) * d = u - b := by rw [Nat.mul_comm]; omega
  rw [hsub]
  exact Nat.sub_le_sub_right huh b

/-- `l - b ≤ d*t` 时 `ceil((l-b)/d) ≤ t`。 -/
private lemma lo_le_t {d b l t : ℕ} (hd : 0 < d) (h : l - b ≤ d * t) :
    (l + d - 1 - b) / d ≤ t := by
  rw [Nat.div_le_iff_le_mul_add_pred hd]
  omega

/-- `d*t ≤ h - b` 时 `t ≤ floor((h-b)/d)`。 -/
private lemma t_le_hi {d b h t : ℕ} (hd : 0 < d) (hp : d * t ≤ h - b) :
    t ≤ (h - b) / d := by
  rw [Nat.le_div_iff_mul_le hd]
  rw [Nat.mul_comm]
  exact hp

/-- PREPUB gap `L-goldbach-farey-hyperbola-shift`（statement 与 `statements/` 去空白逐字一致）。 -/
private theorem L_goldbach_farey_hyperbola_shift :
    ∀ (n d b l h s c : ℕ) (J : Finset ℕ), 1 < n → 0 < d → b < d → b ≤ h → l ≤ h → h < n →
      s < n → (d * s) % n = b % n → (d * c) % n = 1 →
      let lo := (l + d - 1 - b) / d; let hi := (h - b) / d;
      let I := Finset.Icc (lo + s) (hi + s);
      let count := fun (I : Finset ℕ) (k : ℕ) =>
        ((I.product J).filter (fun (x : ℕ × ℕ) => (x.1 * x.2) % n = k % n)).card;
      hi + s < n ∧
        count ((Finset.Icc l h).filter (fun u => u % d = b)) 1 = count I c ∧
        |(I.card : ℝ) - ((h - l + 1 : ℕ) : ℝ) / d| ≤ 1 := by
  intro n d b l h s c J hn hd hb hbh hlh hhn hs hds hdc
  dsimp only
  have hnpos : 0 < n := by omega
  have hbn : b < n := by omega
  have hmodb : b % n = b := Nat.mod_eq_of_lt hbn
  have hP : (d * s) % n = b := by rw [hds, hmodb]
  have hds_mod : d * s ≡ b [MOD n] := by
    show (d * s) % n = b % n
    rw [hP, hmodb]
  have hdc_mod : d * c ≡ 1 [MOD n] := by
    show (d * c) % n = 1 % n
    rw [hdc, Nat.mod_eq_of_lt (by omega : 1 < n)]
  set q := (d * s) / n with hq
  have hdecomp : d * s = q * n + b := by
    have h := Nat.div_add_mod (d * s) n
    rw [Nat.mul_comm n ((d * s) / n), ← hq, hP] at h
    exact h.symm
  -- (1) `hi + s < n`
  have hT1 : (h - b) / d + s < n := by
    have hqle : q + 1 ≤ d := by
      have hsle : s ≤ n - 1 := by omega
      have h1 : d * s ≤ d * (n - 1) := Nat.mul_le_mul_left d hsle
      have h2 : d * (n - 1) = d * n - d := by
        rw [Nat.mul_sub, Nat.mul_one]
      have h3 : q * n + b ≤ d * n - d := by
        rw [← hdecomp]
        rw [h2] at h1
        exact h1
      have hqlt : q < d := by
        have h1' : q * n ≤ d * n - d := le_trans (Nat.le_add_right (q * n) b) h3
        have hdn : d ≤ d * n := by
          have : 1 ≤ n := by omega
          simpa using Nat.mul_le_mul_left d this
        have h2' : d * n - d < d * n := by omega
        exact (Nat.mul_lt_mul_right hnpos).mp (lt_of_le_of_lt h1' h2')
      omega
    have h3' : (n - 1 - b) + d * s + 1 = (q + 1) * n := by
      rw [hdecomp]
      have hbn1 : b ≤ n - 1 := by omega
      have hsub : (n - 1 - b) + b = n - 1 := Nat.sub_add_cancel hbn1
      calc (n - 1 - b) + (q * n + b) + 1
          = ((n - 1 - b) + b) + q * n + 1 := by ring
        _ = (n - 1) + q * n + 1 := by rw [hsub]
        _ = ((n - 1) + 1) + q * n := by omega
        _ = n + q * n := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
        _ = (q + 1) * n := by ring
    have h3 : (n - 1 - b) + d * s = (q + 1) * n - 1 := by
      have := h3'
      omega
    have hidx : (h - b) / d + s ≤ ((q + 1) * n - 1) / d := by
      have h1 : (h - b) / d ≤ (n - 1 - b) / d := Nat.div_le_div_right (by omega)
      have h2 : (n - 1 - b) / d + s = ((n - 1 - b) + d * s) / d :=
        (Nat.add_mul_div_left (n - 1 - b) s hd).symm
      calc (h - b) / d + s ≤ (n - 1 - b) / d + s := by omega
        _ = ((n - 1 - b) + d * s) / d := h2
        _ = ((q + 1) * n - 1) / d := by rw [h3]
    have hfin : ((q + 1) * n - 1) / d < n := by
      rw [Nat.div_lt_iff_lt_mul hd]
      have h1 : (q + 1) * n - 1 < (q + 1) * n := by omega
      have h2 : (q + 1) * n ≤ d * n := Nat.mul_le_mul_right n hqle
      have h2' : (q + 1) * n ≤ n * d := by simpa [Nat.mul_comm] using h2
      omega
    omega
  refine ⟨hT1, ?_, ?_⟩
  · -- (2) 计数相等
    have hcount : ((((Finset.Icc l h).filter (fun u => u % d = b)).product J).filter
          (fun x : ℕ × ℕ => (x.1 * x.2) % n = 1 % n)).card
        = (((Finset.Icc ((l + d - 1 - b) / d + s) ((h - b) / d + s)).product J).filter
          (fun x : ℕ × ℕ => (x.1 * x.2) % n = c % n)).card := by
      classical
      apply Finset.card_bij (fun x _ => (x.1 / d + s, x.2))
      · intro x hx
        obtain ⟨hxprod, hxP⟩ := Finset.mem_filter.mp hx
        obtain ⟨hxS, hxJ⟩ := Finset.mem_product.mp hxprod
        obtain ⟨hxIcc, hxd⟩ := Finset.mem_filter.mp hxS
        obtain ⟨hxl, hxh⟩ := Finset.mem_Icc.mp hxIcc
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, hxJ⟩, ?_⟩
        · have h1 := lo_le_div hd hxd hxl
          have h2 := div_le_hi_div hd hxd hxh
          exact Finset.mem_Icc.mpr ⟨Nat.add_le_add_right h1 s, Nat.add_le_add_right h2 s⟩
        · have hdv : d * (x.1 / d + s) ≡ x.1 [MOD n] := dvd_shift_modEq hds_mod hxd
          have hstep : ((x.1 / d + s) * x.2) ≡ (d * c) * ((x.1 / d + s) * x.2) [MOD n] := by
            have h := hdc_mod.mul (Nat.ModEq.refl ((x.1 / d + s) * x.2))
            simpa using h.symm
          have hstep2 : (d * c) * ((x.1 / d + s) * x.2)
              = c * (d * ((x.1 / d + s) * x.2)) := by ring
          have hstep3 : c * (d * ((x.1 / d + s) * x.2)) ≡ c * (x.1 * x.2) [MOD n] := by
            apply Nat.ModEq.mul_left
            have h := hdv.mul_right x.2
            simpa [mul_assoc] using h
          have hstep4 : c * (x.1 * x.2) ≡ c * 1 [MOD n] := by
            apply Nat.ModEq.mul_left
            exact hxP
          calc (x.1 / d + s) * x.2
              ≡ (d * c) * ((x.1 / d + s) * x.2) [MOD n] := hstep
            _ = c * (d * ((x.1 / d + s) * x.2)) := hstep2
            _ ≡ c * (x.1 * x.2) [MOD n] := hstep3
            _ ≡ c * 1 [MOD n] := hstep4
            _ = c := by ring
      · intro x1 hx1 x2 hx2 heq
        obtain ⟨hx1prod, _⟩ := Finset.mem_filter.mp hx1
        obtain ⟨hx2prod, _⟩ := Finset.mem_filter.mp hx2
        obtain ⟨hx1S, _⟩ := Finset.mem_product.mp hx1prod
        obtain ⟨hx2S, _⟩ := Finset.mem_product.mp hx2prod
        have hxd1 : x1.1 % d = b := (Finset.mem_filter.mp hx1S).2
        have hxd2 : x2.1 % d = b := (Finset.mem_filter.mp hx2S).2
        have hsum : x1.1 / d + s = x2.1 / d + s := by
          have := congrArg Prod.fst heq
          simpa using this
        have hd' : x1.1 / d = x2.1 / d := Nat.add_right_cancel hsum
        have hj : x1.2 = x2.2 := by
          have := congrArg Prod.snd heq
          simpa using this
        have h1 : x1.1 = b + d * (x1.1 / d) := eq_b_add_mul_div hxd1
        have h2 : x2.1 = b + d * (x2.1 / d) := eq_b_add_mul_div hxd2
        exact Prod.ext (by rw [h1, h2, hd']) hj
      · intro y hy
        obtain ⟨hyprod, hyP⟩ := Finset.mem_filter.mp hy
        obtain ⟨hyI, hyJ⟩ := Finset.mem_product.mp hyprod
        obtain ⟨hy1, hy2⟩ := Finset.mem_Icc.mp hyI
        have hys : s ≤ y.1 := le_trans (Nat.le_add_left s _) hy1
        refine ⟨(b + d * (y.1 - s), y.2), ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, hyJ⟩, ?_⟩
          · refine Finset.mem_filter.mpr
              ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
            · have hlo : (l + d - 1 - b) / d ≤ y.1 - s := le_tsub_of_add_le_right hy1
              have h1 := lo_mul_ge l b d hd
              have h2 : d * ((l + d - 1 - b) / d) ≤ d * (y.1 - s) := Nat.mul_le_mul_left d hlo
              have h3 : l - b ≤ d * (y.1 - s) := le_trans h1 h2
              omega
            · have hhi : y.1 - s ≤ (h - b) / d := by
                simpa using Nat.sub_le_sub_right hy2 s
              have h1 := hi_mul_le h b d
              have h2 : d * (y.1 - s) ≤ d * ((h - b) / d) := Nat.mul_le_mul_left d hhi
              have h3 : d * (y.1 - s) ≤ h - b := le_trans h2 h1
              omega
            · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
          · have hdv : d * y.1 ≡ b + d * (y.1 - s) [MOD n] := by
              have hdecomp2 : d * y.1 = d * (y.1 - s) + d * s := by
                rw [← Nat.mul_add]
                congr 1
                omega
              rw [hdecomp2]
              have h1 : d * (y.1 - s) + d * s ≡ d * (y.1 - s) + b [MOD n] :=
                (Nat.ModEq.refl _).add hds_mod
              have h2 : d * (y.1 - s) + b = b + d * (y.1 - s) := by ring
              rwa [h2] at h1
            have h1 : (b + d * (y.1 - s)) * y.2 ≡ (d * y.1) * y.2 [MOD n] := by
              have h := hdv.mul_right y.2
              exact h.symm
            have h2 : (d * y.1) * y.2 = d * (y.1 * y.2) := by ring
            have h3 : d * (y.1 * y.2) ≡ d * c [MOD n] := Nat.ModEq.mul_left d hyP
            calc (b + d * (y.1 - s)) * y.2 ≡ (d * y.1) * y.2 [MOD n] := h1
              _ = d * (y.1 * y.2) := h2
              _ ≡ d * c [MOD n] := h3
              _ ≡ 1 [MOD n] := hdc_mod
        · have hdiv : (b + d * (y.1 - s)) / d = y.1 - s := by
            rw [Nat.add_mul_div_left b (y.1 - s) hd, Nat.div_eq_of_lt hb, Nat.zero_add]
          have hfirst : (b + d * (y.1 - s)) / d + s = y.1 := by
            rw [hdiv, Nat.sub_add_cancel hys]
          exact Prod.ext hfirst rfl
    exact hcount
  · -- (3)
    have hcardS : ((Finset.Icc l h).filter (fun u => u % d = b)).card
        = (Finset.Icc ((l + d - 1 - b) / d + s) ((h - b) / d + s)).card := by
      classical
      apply Finset.card_bij (fun u _ => u / d + s)
      · intro u hu
        obtain ⟨huIcc, hud⟩ := Finset.mem_filter.mp hu
        obtain ⟨hul, huh⟩ := Finset.mem_Icc.mp huIcc
        have h1 := lo_le_div hd hud hul
        have h2 := div_le_hi_div hd hud huh
        exact Finset.mem_Icc.mpr ⟨Nat.add_le_add_right h1 s, Nat.add_le_add_right h2 s⟩
      · intro u1 hu1 u2 hu2 heq
        have hxd1 : u1 % d = b := (Finset.mem_filter.mp hu1).2
        have hxd2 : u2 % d = b := (Finset.mem_filter.mp hu2).2
        have h1 : u1 = b + d * (u1 / d) := eq_b_add_mul_div hxd1
        have h2 : u2 = b + d * (u2 / d) := eq_b_add_mul_div hxd2
        have hdiv : u1 / d = u2 / d := Nat.add_right_cancel heq
        rw [h1, h2, hdiv]
      · intro v hv
        obtain ⟨hv1, hv2⟩ := Finset.mem_Icc.mp hv
        have hvs : s ≤ v := le_trans (Nat.le_add_left s _) hv1
        refine ⟨b + d * (v - s), ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
          · have hlo : (l + d - 1 - b) / d ≤ v - s := le_tsub_of_add_le_right hv1
            have h1 := lo_mul_ge l b d hd
            have h2 : d * ((l + d - 1 - b) / d) ≤ d * (v - s) := Nat.mul_le_mul_left d hlo
            have h3 : l - b ≤ d * (v - s) := le_trans h1 h2
            omega
          · have hhi : v - s ≤ (h - b) / d := by
              simpa using Nat.sub_le_sub_right hv2 s
            have h1 := hi_mul_le h b d
            have h2 : d * (v - s) ≤ d * ((h - b) / d) := Nat.mul_le_mul_left d hhi
            have h3 : d * (v - s) ≤ h - b := le_trans h2 h1
            omega
          · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
        · have hdiv : (b + d * (v - s)) / d = v - s := by
            rw [Nat.add_mul_div_left b (v - s) hd, Nat.div_eq_of_lt hb, Nat.zero_add]
          omega
    have hle := card_Icc_residue_abs d b l h hd
    have hfilt : ((Finset.Icc l h).filter (fun u => u % d = b))
        = ((Finset.Icc l h).filter (fun u => u % d = b % d)) := by
      apply Finset.filter_congr
      intro u _
      rw [Nat.mod_eq_of_lt hb]
    have hle' : |((((Finset.Icc l h).filter (fun u => u % d = b)).card : ℕ) : ℝ)
        - ((h - l + 1 : ℕ) : ℝ) / (d : ℝ)| ≤ 1 := by
      rw [hfilt]
      exact hle
    rw [← hcardS]
    exact hle'


/-- Residues `x : ZMod d` with `x * (n - x) = 0`. -/
private def Root (d n : ℕ) : Finset (ZMod d) :=
  match d with
  | 0 => {0, (n : ZMod 0)}
  | d + 1 => Finset.univ.filter (fun x => x * ((n : ZMod (d + 1)) - x) = 0)

private theorem mem_Root (d n : ℕ) [NeZero d] (x : ZMod d) :
    x ∈ Root d n ↔ x * ((n : ZMod d) - x) = 0 := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ d => simp [Root]

/-- For `u ≤ n`, the natural-number divisibility `d ∣ u * (n - u)` is the same condition. -/
private theorem mem_Root_iff (d n u : ℕ) (hu : u ≤ n) :
    (u : ZMod d) ∈ Root d n ↔ d ∣ u * (n - u) := by
  cases d with
  | zero =>
      simp only [Root, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · have hu0 : u = 0 := by exact_mod_cast h
          simp [hu0]
        · have hun : u = n := by exact_mod_cast h
          simp [hun]
      · intro h
        have hprod : u * (n - u) = 0 := zero_dvd_iff.mp h
        rcases Nat.mul_eq_zero.mp hprod with hu0 | hsub
        · exact Or.inl (by exact_mod_cast hu0)
        · have hun : u = n := by omega
          exact Or.inr (by exact_mod_cast hun)
  | succ d =>
      rw [mem_Root]
      rw [← Nat.cast_sub hu, ← Nat.cast_mul]
      exact ZMod.natCast_eq_zero_iff _ _

private theorem mem_Root_crt (q r n : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (h : Nat.Coprime q r) (x : ZMod (q * r)) :
    ZMod.chineseRemainder h x ∈ Root q n ×ˢ Root r n ↔ x ∈ Root (q * r) n := by
  set e := ZMod.chineseRemainder h
  have hnat : e ((n : ℕ) : ZMod (q * r)) =
      (((n : ℕ) : ZMod q), ((n : ℕ) : ZMod r)) := by
    rw [map_natCast]
    rfl
  have hmul : e (x * (((n : ℕ) : ZMod (q * r)) - x)) =
      ((e x).1 * (((n : ℕ) : ZMod q) - (e x).1),
        (e x).2 * (((n : ℕ) : ZMod r) - (e x).2)) := by
    rw [map_mul, map_sub, hnat]
    rfl
  simp only [Finset.mem_product, mem_Root]
  constructor
  · rintro ⟨h1, h2⟩
    apply e.injective
    rw [hmul, map_zero]
    exact Prod.ext h1 h2
  · intro hx
    have he : e (x * (((n : ℕ) : ZMod (q * r)) - x)) = 0 := by
      rw [hx, map_zero]
    rw [hmul] at he
    exact ⟨by simpa using congrArg Prod.fst he, by simpa using congrArg Prod.snd he⟩

/-- Multiplicativity of the root count via CRT. -/
private theorem card_Root_mul (q r n : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (h : Nat.Coprime q r) :
    (Root (q * r) n).card = (Root q n).card * (Root r n).card := by
  have hbij : (Root (q * r) n).card = (Root q n ×ˢ Root r n).card := by
    refine Finset.card_bij' (fun x (_ : x ∈ Root (q * r) n) => ZMod.chineseRemainder h x)
      (fun y (_ : y ∈ Root q n ×ˢ Root r n) => (ZMod.chineseRemainder h).symm y) ?_ ?_ ?_ ?_
    · intro x hx
      exact (mem_Root_crt q r n h x).2 hx
    · intro y hy
      refine (mem_Root_crt q r n h ((ZMod.chineseRemainder h).symm y)).1 ?_
      rwa [RingEquiv.apply_symm_apply]
    · intro x _
      exact RingEquiv.symm_apply_apply _ _
    · intro y _
      exact RingEquiv.apply_symm_apply _ _
  rw [hbij, Finset.card_product]

/-- Prime case: exactly two roots, namely `0` and `n`. -/
private theorem card_Root_prime (p n : ℕ) (hp : Nat.Prime p) (hn : ¬p ∣ n) :
    (Root p n).card = 2 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hn0 : (n : ZMod p) ≠ 0 := by
    intro h
    exact hn ((ZMod.natCast_eq_zero_iff n p).1 h)
  have hroots : Root p n = {0, (n : ZMod p)} := by
    ext x
    simp only [mem_Root, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with hx | hsub
      · exact Or.inl hx
      · exact Or.inr (sub_eq_zero.mp hsub).symm
    · rintro (rfl | rfl)
      · simp
      · simp
  rw [hroots, Finset.card_pair (Ne.symm hn0)]

private theorem card_Root_prod (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p)
    (hn : ∀ p ∈ s, ¬p ∣ n) :
    (Root (∏ p ∈ s, p) n).card = 2 ^ s.card := by
  revert hs hn
  induction s using Finset.induction_on with
  | empty =>
      intro _ _
      have hroot : Root 1 n = (univ : Finset (ZMod 1)) := by
        ext x
        simp only [Finset.mem_univ, iff_true]
        rw [mem_Root]
        have hx : x = 0 := Subsingleton.elim x 0
        subst x
        simp
      simp only [prod_empty, pow_zero]
      rw [hroot, Finset.card_univ, ZMod.card, Finset.card_empty, pow_zero]
  | @insert a s ha ih =>
      intro hs hn
      have hpa : Nat.Prime a := hs a (Finset.mem_insert_self a s)
      have hs' : ∀ p ∈ s, Nat.Prime p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have hn' : ∀ p ∈ s, ¬p ∣ n := fun p hp => hn p (Finset.mem_insert_of_mem hp)
      have hprodpos : 0 < ∏ p ∈ s, p := Finset.prod_pos fun p hp => (hs' p hp).pos
      have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
        apply Nat.Coprime.prod_right
        intro p hp
        apply (Nat.coprime_primes hpa (hs' p hp)).2
        intro h
        subst p
        exact ha hp
      letI : NeZero a := ⟨hpa.ne_zero⟩
      letI : NeZero (∏ p ∈ s, p) := ⟨hprodpos.ne'⟩
      letI : NeZero (a * ∏ p ∈ s, p) := ⟨(Nat.mul_pos hpa.pos hprodpos).ne'⟩
      calc
        (Root (∏ p ∈ insert a s, p) n).card =
            (Root (a * ∏ p ∈ s, p) n).card := by
              rw [Finset.prod_insert ha]
        _ = (Root a n).card * (Root (∏ p ∈ s, p) n).card :=
          card_Root_mul a (∏ p ∈ s, p) n hcop
        _ = 2 * 2 ^ s.card := by
          rw [card_Root_prime a n hpa (hn a (Finset.mem_insert_self a s)), ih hs' hn']
        _ = 2 ^ (insert a s).card := by
          rw [Finset.card_insert_of_notMem ha, pow_succ]
          omega

/-- The main count. -/
private theorem card_Root (d n : ℕ) (hd : 0 < d) (hsq : Squarefree d)
    (hcop : Nat.Coprime d n) :
    (Root d n).card = 2 ^ d.primeFactors.card := by
  have hs : ∀ p ∈ d.primeFactors, Nat.Prime p := fun _ hp =>
    Nat.prime_of_mem_primeFactors hp
  have hn : ∀ p ∈ d.primeFactors, ¬p ∣ n := by
    intro p hp
    have hpn : Nat.Coprime p n :=
      Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_primeFactors hp) hcop
    exact (hs p hp).coprime_iff_not_dvd.mp hpn
  have h := card_Root_prod d.primeFactors hs hn
  rw [Nat.prod_primeFactors_of_squarefree hsq] at h
  exact h


theorem Conjectures.Goldbach.FareyHyperbolaSieveTransfer : ∀ (n d l h a b : ℕ) (E : ℝ), 1 < n → 0 < d → d.Coprime n → Squarefree d → l ≤ h → h < n → b < n → 0 ≤ E → ( ∀ c l h a b : ℕ, c.Coprime n → h < n → b < n → let I := Finset.Icc l h; let J := Finset.Icc a b; |((((I.product J).filter (fun (x : ℕ × ℕ) => (x.1*x.2) % n = c % n)).card : ℝ) - (I.card:ℝ)*(J.card:ℝ)*(n.totient:ℝ)/(n:ℝ)^2)| ≤ E) → let I := (Finset.Icc l h).filter (fun u => d ∣ u*(n-u)); let J := Finset.Icc a b; let R : ℝ := (2 : ℝ)^d.primeFactors.card; |((((I.product J).filter (fun (x : ℕ × ℕ) => (x.1*x.2) % n = 1)).card : ℝ) - ((h-l+1 : ℕ):ℝ)*(J.card:ℝ)*(n.totient:ℝ)*R/((d:ℝ)*(n:ℝ)^2))| ≤ R*(E+1) := by
  classical
  intro n d l h a b E hn hd hcop hsq hlh hhn hbn hE hyp
  haveI : NeZero d := ⟨hd.ne'⟩
  haveI : NeZero n := ⟨by omega⟩
  let I := Finset.Icc l h
  let J := Finset.Icc a b
  let L : ℝ := (h-l+1:ℕ)
  let W : ℝ := (J.card:ℝ) * n.totient / (n:ℝ)^2
  let pair := fun (s : Finset ℕ) (t : ℕ) => (s ×ˢ J).filter (fun z => (z.1*z.2) % n = t % n)
  let F := fun x : ZMod d => pair (I.filter (fun u => u % d = x.val)) 1
  let U := pair (I.filter (fun u => d ∣ u*(n-u))) 1
  have hn1 : 1 % n = 1 := Nat.mod_eq_of_lt hn
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hW1 : W ≤ 1 := by
    have hj : J.card ≤ n := by dsimp [J]; rw [Nat.card_Icc]; omega
    have hnR : (0:ℝ)<n := by exact_mod_cast (by omega : 0 < n)
    have hφ := Nat.totient_le n
    apply (div_le_iff₀ (sq_pos_of_pos hnR)).mpr
    rw [one_mul,sq]
    exact mul_le_mul (by exact_mod_cast hj) (by exact_mod_cast hφ) (by positivity) hnR.le
  obtain ⟨c,_,hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hn
  have co : c.Coprime n := by
    apply (ZMod.isUnit_iff_coprime c n).mp
    apply isUnit_iff_exists_inv'.mpr
    refine ⟨(d:ZMod n),?_⟩
    simpa only [Nat.cast_mul,Nat.cast_one] using (ZMod.natCast_eq_natCast_iff' (d*c) 1 n).mpr (hc.trans hn1.symm)
  have per (x : ZMod d) : |((F x).card:ℝ) - (L/d)*W| ≤ E+1 := by
    by_cases hit : x.val ≤ h
    · obtain ⟨s,hs,hs'⟩ := Nat.exists_mul_mod_eq_of_coprime x.val hcop (NeZero.ne n)
      obtain ⟨hend,heq,herr⟩ := L_goldbach_farey_hyperbola_shift n d x.val l h s c J hn hd
        (ZMod.val_lt x) hit hlh hhn hs hs' hc
      let lo := (l+d-1-x.val)/d+s
      let hi := (h-x.val)/d+s
      let T := Finset.Icc lo hi
      have hh := hyp c lo hi a b co hend hbn
      change |((pair T c).card:ℝ) - _| ≤ E at hh
      have eq1 : (F x).card = (pair T c).card := heq
      change |(T.card:ℝ)-L/d| ≤ 1 at herr
      have b1 : |((pair T c).card:ℝ) - (T.card:ℝ)*W| ≤ E := by
        convert hh using 2 <;> dsimp [W,T,J] <;> ring
      have b2 : |((T.card:ℝ)-L/d)*W| ≤ 1 := by
        rw [abs_mul,abs_of_nonneg hW]; exact (mul_le_mul_of_nonneg_right herr hW).trans (by simpa using hW1)
      rw [eq1]
      calc _ = |(((pair T c).card:ℝ)-(T.card:ℝ)*W) + (((T.card:ℝ)-L/d)*W)| := by congr 1; ring
           _ ≤ _ := (abs_add_le _ _).trans (add_le_add b1 b2)
    · have empty : I.filter (fun u => u % d=x.val) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        obtain ⟨hi,he⟩ := Finset.mem_filter.mp hu
        have := (Finset.mem_Icc.mp hi).2
        have := Nat.mod_le u d
        omega
      have ed : (F x).card=0 := by simp [F,empty,pair]
      have len : L/(d:ℝ) ≤ 1 := by
        apply (div_le_one (by exact_mod_cast hd)).mpr
        dsimp [L]; exact_mod_cast (by have := ZMod.val_lt x; omega : h-l+1≤d)
      rw [ed,Nat.cast_zero,zero_sub,abs_neg,abs_of_nonneg (by dsimp [L]; positivity)]
      exact (mul_le_mul_of_nonneg_right len hW).trans (by linarith)
  have sums : U.card = ∑ x ∈ Root d n, (F x).card := by
    have maps : ∀ z ∈ U, (z.1 : ZMod d) ∈ Root d n := by
      intro z hz
      have hi := Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1
      exact (mem_Root_iff d n z.1 ((Finset.mem_Icc.mp hi.1).2.trans hhn.le)).mpr hi.2
    rw [Finset.card_eq_sum_card_fiberwise maps]
    apply Finset.sum_congr rfl; intro x hx
    congr 1
    ext ⟨u,v⟩
    simp only [U,F,pair,Finset.mem_filter,Finset.mem_product,Prod.fst,Prod.snd]
    have val : (u:ZMod d)=x ↔ u % d = x.val := by
      rw [← (ZMod.val_injective d).eq_iff,ZMod.val_natCast]
    constructor
    · rintro ⟨⟨⟨⟨hi,_⟩,hj⟩,hm⟩,he⟩
      exact ⟨⟨⟨hi,val.mp he⟩,hj⟩,hm⟩
    · rintro ⟨⟨⟨hi,he⟩,hj⟩,hm⟩
      have hmem := (val.mpr he).symm ▸ hx
      have hdvd := (mem_Root_iff d n u ((Finset.mem_Icc.mp hi).2.trans hhn.le)).mp hmem
      exact ⟨⟨⟨⟨hi,hdvd⟩,hj⟩,hm⟩,val.mpr he⟩
  have fin : |(U.card:ℝ) - ((Root d n).card:ℝ)*((L/d)*W)| ≤ ((Root d n).card:ℝ)*(E+1) := by
    rw [sums,Nat.cast_sum, ← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun x _ => per x)).trans_eq (by simp; ring))
  rw [card_Root d n hd hsq hcop, Nat.cast_pow, Nat.cast_ofNat] at fin
  dsimp only
  dsimp [U,pair,I,J,L,W] at fin
  rw [hn1] at fin
  convert fin using 2 <;> congr 1 <;> first | rfl | ring
