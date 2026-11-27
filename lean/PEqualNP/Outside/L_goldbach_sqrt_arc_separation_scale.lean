import Mathlib

private theorem pow_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    a ^ n ≤ b ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow ha hab (Nat.cast_nonneg n)

private theorem pow24_step (L : ℕ) (hL : 200 ≤ L) :
    ((L + 1 : ℕ) : ℝ) ^ 24 ≤ 2 * (L : ℝ) ^ 24 := by
  have hLr : (200 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h1 : ((L + 1 : ℕ) : ℝ) ≤ (201 / 200 : ℝ) * (L : ℝ) := by
    push_cast
    nlinarith
  have h2 : ((L + 1 : ℕ) : ℝ) ^ 24 ≤ ((201 / 200 : ℝ) * (L : ℝ)) ^ 24 :=
    pow_mono (by positivity) h1 24
  rw [mul_pow] at h2
  have h3 : (201 / 200 : ℝ) ^ 24 ≤ 2 := by norm_num
  calc ((L + 1 : ℕ) : ℝ) ^ 24 ≤ (201 / 200 : ℝ) ^ 24 * (L : ℝ) ^ 24 := h2
    _ ≤ 2 * (L : ℝ) ^ 24 := mul_le_mul_of_nonneg_right h3 (by positivity)

private theorem key_aux :
    ∀ k : ℕ, 64 * ((200 + k : ℕ) : ℝ) ^ 24 ≤ (2 : ℝ) ^ ((200 + k : ℕ) - 1) := by
  intro k
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hL : (200 : ℕ) ≤ 200 + k := by omega
    have hstep := pow24_step (200 + k) hL
    have hrw : (200 + (k + 1) : ℕ) = (200 + k) + 1 := by omega
    rw [hrw]
    calc 64 * (((200 + k) + 1 : ℕ) : ℝ) ^ 24 ≤ 64 * (2 * ((200 + k : ℕ) : ℝ) ^ 24) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = 2 * (64 * ((200 + k : ℕ) : ℝ) ^ 24) := by ring
      _ ≤ 2 * (2 : ℝ) ^ ((200 + k : ℕ) - 1) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (2 : ℝ) ^ (((200 + k) + 1 : ℕ) - 1) := by
          calc 2 * (2 : ℝ) ^ ((200 + k : ℕ) - 1) = (2 : ℝ) ^ (((200 + k : ℕ) - 1) + 1) := by
                rw [pow_succ]; ring
            _ = (2 : ℝ) ^ (((200 + k) + 1 : ℕ) - 1) := by congr 1; omega

private theorem key (L : ℕ) (hL : 200 ≤ L) :
    64 * (L : ℝ) ^ 24 ≤ (2 : ℝ) ^ (L - 1) := by
  have h := key_aux (L - 200)
  rwa [Nat.add_sub_of_le hL] at h
theorem PEqualNP.Outside.L_goldbach_sqrt_arc_separation_scale :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let Q₂ := fun n : ℕ => ⌊Real.sqrt (n:ℝ)/((Nat.log 2 (n+2):ℝ)^4)⌋₊; ∃ N : ℕ, ∀ n ≥ N, Q₁ n < Q₂ n ∧ 2*(256*Q₂ n*Q n)*Q₂ n < n := by
  refine ⟨2 ^ 200, fun n hn => ?_⟩
  set L := Nat.log 2 (n + 2) with hLdef
  set m := ⌊Real.sqrt (n:ℝ) / ((L:ℝ)^4)⌋₊ with hmdef
  have hp200 : (0:ℕ) < 2 ^ 200 := by positivity
  have hn0 : 0 < n := lt_of_lt_of_le hp200 hn
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn0
  have hn2 : (2:ℕ)^200 ≤ n + 2 := by omega
  have hL200 : 200 ≤ L := Nat.le_log_of_pow_le (by norm_num) hn2
  have hL200r : (200:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL200
  have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hLne : (L:ℝ) ≠ 0 := ne_of_gt hLpos
  have hpow : (2:ℕ)^L ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
  have hkey : 64 * (L:ℝ)^24 ≤ (2:ℝ)^(L-1) := key L hL200
  have h2L : (2:ℝ)^L = 2 * (2:ℝ)^(L-1) := by
    have h : (L - 1) + 1 = L := by omega
    conv_lhs => rw [← h]
    rw [pow_succ]
    ring
  have hcastL : ((2:ℕ)^L : ℝ) = (2:ℝ)^L := by push_cast; ring
  have hlow : 128 * (L:ℝ)^24 ≤ (n:ℝ) + 2 := by
    have h1 : (128:ℝ) * (L:ℝ)^24 ≤ (2:ℝ)^L := by
      rw [h2L]; linarith
    have h2 : ((2:ℕ)^L : ℝ) ≤ (n:ℝ) + 2 := by exact_mod_cast hpow
    rw [hcastL] at h2
    linarith
  have h64 : (2:ℝ) ≤ 64 * (L:ℝ)^24 := by
    have h1 : (200:ℝ)^24 ≤ (L:ℝ)^24 := pow_mono (by norm_num) hL200r 24
    have h2 : (1:ℝ) ≤ (200:ℝ)^24 := by norm_num
    linarith
  have hnreal : (64:ℝ) * (L:ℝ)^24 ≤ (n:ℝ) := by linarith
  have h64r : (64:ℝ)^(1/6:ℝ) = 2 := by
    rw [show (64:ℝ) = (2:ℝ)^6 by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (2:ℝ)),
      show ((6:ℕ):ℝ) * (1/6:ℝ) = 1 by norm_num, Real.rpow_one]
  have hL24 : ((L:ℝ)^24)^(1/6:ℝ) = (L:ℝ)^4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (L:ℝ)),
      show ((24:ℕ):ℝ) * (1/6:ℝ) = ((4:ℕ):ℝ) by norm_num]
    rw [Real.rpow_natCast]
  have hroot : 2 * (L:ℝ)^4 ≤ (n:ℝ)^(1/6:ℝ) := by
    have h1 : (64 * (L:ℝ)^24)^(1/6:ℝ) ≤ (n:ℝ)^(1/6:ℝ) :=
      Real.rpow_le_rpow (by positivity) hnreal (by norm_num)
    rw [Real.mul_rpow (by norm_num) (by positivity), h64r, hL24] at h1
    exact h1
  have hn13 : 1 ≤ (n:ℝ)^(1/3:ℝ) := by
    have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    calc (1:ℝ) = (1:ℝ)^(1/3:ℝ) := by rw [Real.one_rpow]
      _ ≤ (n:ℝ)^(1/3:ℝ) := Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
  have hsqrt : Real.sqrt (n:ℝ) = (n:ℝ)^(1/3:ℝ) * (n:ℝ)^(1/6:ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity : (0:ℝ) < (n:ℝ))]
    congr 1
    norm_num
  have hmain : (n:ℝ)^(1/3:ℝ) + 1 ≤ Real.sqrt (n:ℝ) / ((L:ℝ)^4) := by
    rw [hsqrt, le_div_iff₀ (by positivity : (0:ℝ) < (L:ℝ)^4)]
    have hA : (0:ℝ) ≤ (n:ℝ)^(1/3:ℝ) := by positivity
    have hL4 : (0:ℝ) ≤ (L:ℝ)^4 := by positivity
    have key1 : (L:ℝ)^4 ≤ (n:ℝ)^(1/3:ℝ) * (L:ℝ)^4 := by
      calc (L:ℝ)^4 = 1 * (L:ℝ)^4 := by ring
        _ ≤ (n:ℝ)^(1/3:ℝ) * (L:ℝ)^4 := mul_le_mul_of_nonneg_right hn13 hL4
    have key2 : (n:ℝ)^(1/3:ℝ) * (2 * (L:ℝ)^4) ≤ (n:ℝ)^(1/3:ℝ) * (n:ℝ)^(1/6:ℝ) :=
      mul_le_mul_of_nonneg_left hroot hA
    calc ((n:ℝ)^(1/3:ℝ) + 1) * (L:ℝ)^4
        = (n:ℝ)^(1/3:ℝ) * (L:ℝ)^4 + (L:ℝ)^4 := by ring
      _ ≤ (n:ℝ)^(1/3:ℝ) * (L:ℝ)^4 + (n:ℝ)^(1/3:ℝ) * (L:ℝ)^4 := by
          linarith [key1]
      _ = (n:ℝ)^(1/3:ℝ) * (2 * (L:ℝ)^4) := by ring
      _ ≤ (n:ℝ)^(1/3:ℝ) * (n:ℝ)^(1/6:ℝ) := key2
  have hfloor1 : ⌊(n:ℝ)^(1/3:ℝ)⌋₊ < m := by
    have h1 := Nat.floor_le (by positivity : (0:ℝ) ≤ (n:ℝ)^(1/3:ℝ))
    have h2 := Nat.lt_floor_add_one (Real.sqrt (n:ℝ) / ((L:ℝ)^4))
    have h3 : ((⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ Real.sqrt (n:ℝ) / ((L:ℝ)^4) := by
      linarith
    have h4 : Real.sqrt (n:ℝ) / ((L:ℝ)^4) < ((m : ℕ) : ℝ) + 1 := h2
    have h6 : ((⌊(n:ℝ)^(1/3:ℝ)⌋₊ : ℕ) : ℝ) < ((m : ℕ) : ℝ) := by linarith
    exact_mod_cast h6
  have hbound : 512 * (m:ℝ)^2 * (L:ℝ)^2 < (n:ℝ) := by
    have hmle : (m:ℝ) ≤ Real.sqrt (n:ℝ) / ((L:ℝ)^4) := Nat.floor_le (by positivity)
    have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg _
    have hy0 : (0:ℝ) ≤ Real.sqrt (n:ℝ) / ((L:ℝ)^4) := by positivity
    have hm2 : (m:ℝ)^2 ≤ (Real.sqrt (n:ℝ) / ((L:ℝ)^4))^2 := by
      have hx := mul_self_le_mul_self hm0 hmle
      simpa [pow_two] using hx
    have hsq : (Real.sqrt (n:ℝ))^2 = (n:ℝ) := Real.sq_sqrt (by positivity)
    have hL6 : (512:ℝ) < (L:ℝ)^6 := by
      have h1 : (200:ℝ)^6 ≤ (L:ℝ)^6 := pow_mono (by norm_num) hL200r 6
      have h2 : (512:ℝ) < (200:ℝ)^6 := by norm_num
      linarith
    calc 512 * (m:ℝ)^2 * (L:ℝ)^2 ≤ 512 * ((Real.sqrt (n:ℝ) / ((L:ℝ)^4))^2) * (L:ℝ)^2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm2 (by norm_num)) (by positivity)
      _ = 512 * (n:ℝ) / (L:ℝ)^6 := by
          rw [div_pow, hsq]
          field_simp [hLne]
      _ < (n:ℝ) := by
          rw [div_lt_iff₀ (by positivity : (0:ℝ) < (L:ℝ)^6)]
          have h3 := mul_lt_mul_of_pos_right hL6 hnpos
          linarith
  have hfloor2 : 2 * (256 * m * (L^2)) * m < n := by
    have hcast : ((2 * (256 * m * (L^2)) * m : ℕ) : ℝ) = 512 * (m:ℝ)^2 * (L:ℝ)^2 := by
      push_cast
      ring
    have h1 : ((2 * (256 * m * (L^2)) * m : ℕ) : ℝ) < (n:ℝ) := by
      rw [hcast]; exact hbound
    exact_mod_cast h1
  exact ⟨hfloor1, hfloor2⟩
