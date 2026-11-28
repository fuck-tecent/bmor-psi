import Mathlib

-- child 1 zh: 在一千倍长度的间隙中，恰取百分之八点五作为翻转位置，所得二项式系数满足显式指数下界。
-- child 1 en: Bound the number of ways to choose exactly 85t transition positions among 1000t gaps.
-- child 2 zh: 在长度为 1000t+1 的网格字中，构造大小至少为对应固定翻转字族的集合，使截断指数和的平均实部大于 0.745 倍字长。
-- child 2 en: On lengths 1000t+1, construct a family of fixed-transition cardinality or larger with mean real part above 0.745 times the length.

open Finset
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem Conjectures.Cuts.Cut8df52032ad4d7879a39d7090
    (hEntropy : ∀ t : ℕ, 2^(419*t) ≤ (1000*t+1) * (1000*t).choose (85*t))
    (hMean : let T := fun (n : ℕ) (x : ℝ) => ∑ j ∈ Finset.range n, Complex.exp (((2*Real.pi*↑⌊(65536:ℝ)*2^j*x⌋ / 65536 : ℝ) : ℂ)*Complex.I)
      ∀ t : ℕ, 2000 ≤ t → let N := 1000*t+1
        ∃ A ⊆ Finset.range (2^N), 2*(1000*t).choose (85*t) ≤ A.card ∧
          (745/1000:ℝ)*N*A.card < ∑ k ∈ A, (T N ((k:ℝ)/2^N)).re) : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => ∑ x3 ∈ Finset.range x1, Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ x3 * x2⌋ / (65536 : ℝ)) * Complex.I); ∃ (x2 : ℕ), ∀ x3 ≥ x2, ∃ x5 ⊆ Finset.range ((2 : ℕ) ^ x3), (2 : ℝ) ^ (-((291 / 500 : ℝ) * ↑x3)) ≤ ↑x5.card / (2 : ℝ) ^ x3 ∧ ∀ x6 ∈ x5, (93 / 125 : ℝ) * ↑x3 + (2 : ℝ) * Real.pi / (65536 : ℝ) * ↑x3 + (2 : ℝ) * Real.pi < ‖x1 x3 (↑x6 / (2 : ℝ) ^ x3)‖) := by
  classical
  let truncated (L : ℕ) (x : ℝ) : ℂ :=
    ∑ j ∈ range L, Complex.exp (((2*Real.pi*↑⌊(65536:ℝ)*2^j*x⌋ / 65536 : ℝ) : ℂ)*Complex.I)

  have many_high_words (A : Finset ℕ) (Y : ℕ → ℝ) {N : ℝ}
      (hN : 0 < N) (hu : ∀ i ∈ A, Y i ≤ N)
      (hm : (745/1000 : ℝ)*N*A.card < ∑ i ∈ A, Y i) :
      (A.card : ℝ)/1000 < (A.filter fun i => (7442/10000:ℝ)*N < Y i).card := by
    let G := A.filter fun i => (7442/10000:ℝ)*N < Y i
    have hG : G ⊆ A := filter_subset _ _
    have bound : ∑ i ∈ A, Y i ≤ (A.card-G.card : ℝ)*((7442/10000:ℝ)*N) + G.card*N := by
      rw [← sum_sdiff hG]
      have bad := sum_le_sum (s := A \ G) (g := fun _ => (7442/10000:ℝ)*N)
        (f := Y) (by
          intro i hi
          obtain ⟨ha,hb⟩ := mem_sdiff.mp hi
          exact le_of_not_gt fun h => hb (mem_filter.mpr ⟨ha,h⟩))
      have good := sum_le_sum (s := G) (g := fun _ => N) (f := Y) (fun i hi => hu i (hG hi))
      convert add_le_add bad good using 1
      simp [card_sdiff_of_subset hG, Nat.cast_sub (card_le_card hG)]
    have hA : 0 ≤ (A.card : ℝ) := Nat.cast_nonneg _
    change (A.card : ℝ)/1000 < (G.card : ℝ)
    apply (mul_lt_mul_iff_left₀ hN).mp
    nlinarith [mul_nonneg hN.le hA]

  have pad_truncated (N s k : ℕ) :
      truncated (N+s) ((k:ℝ)/2^N) = truncated N ((k:ℝ)/2^N) + (s:ℂ) := by
    dsimp only [truncated]
    rw [sum_range_add]
    congr 1
    calc
      _ = ∑ _j ∈ range s, (1:ℂ) := by
        apply sum_congr rfl
        intro j _
        have arg : (65536:ℝ)*2^(N+j)*((k:ℝ)/2^N) = (↑(65536 * 2^j * k : ℕ):ℝ) := by
          push_cast
          rw [pow_add]
          field_simp
        rw [arg, Int.floor_natCast]
        push_cast
        convert Complex.exp_nat_mul_two_pi_mul_I (2^j*k) using 2
        push_cast
        ring
      _ = _ := by simp



  have absorb (t : ℕ) (ht : 2000 ≤ t) :
      2^418 * (500 * (1000*t+1)) ≤ 2^t := by
    induction t, ht using Nat.le_induction with
    | base => decide +kernel
    | succ t ht ih =>
      rw [pow_succ (2:ℕ) t]
      have ht' : (500:ℕ)*(1000*(t+1)+1) ≤ 500*(1000*t+1)*2 := by omega
      exact (Nat.mul_le_mul_left ((2:ℕ)^(418:ℕ)) ht').trans (by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_right 2 ih)

  have density_exponent (L t : ℕ) (ht : 2000 ≤ t) (hL : L ≤ 1000*t+1000) :
      (2:ℝ)^((209/500:ℝ)*L) * (500*(1000*(t:ℝ)+1)) ≤ (2:ℝ)^(419*t) := by
    have le : (209/500:ℝ)*L ≤ ((418*t+418:ℕ):ℝ) := by
      have h := Nat.cast_le (α := ℝ).mpr hL
      push_cast at h ⊢
      linarith
    have rpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) le
    rw [Real.rpow_natCast] at rpow
    have a : (2:ℝ)^418 * (500*(1000*(t:ℝ)+1)) ≤ (2:ℝ)^t := by
      exact_mod_cast absorb t ht
    calc
      _ ≤ (2:ℝ)^(418*t+418) * (500*(1000*(t:ℝ)+1)) :=
        mul_le_mul_of_nonneg_right rpow (by positivity)
      _ = (2:ℝ)^(418*t) * ((2:ℝ)^418 * (500*(1000*(t:ℝ)+1))) := by
        rw [pow_add, mul_assoc]
      _ ≤ (2:ℝ)^(418*t) * 2^t := mul_le_mul_of_nonneg_left a (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega


  have high_set_from_word_mean
      (L : ℕ) (hL : 2000001 ≤ L) :
      ∃ S ⊆ range (2^L),
        (2:ℝ)^(-((291/500:ℝ)*L)) ≤ (S.card:ℝ)/(2:ℝ)^L ∧
          ∀ k ∈ S, (93/125:ℝ)*L + (2*Real.pi/65536)*L + 2*Real.pi <
            ‖truncated L ((k:ℝ)/2^L)‖ := by
    let t := (L-1)/1000
    let N := 1000*t+1
    let s := L-N
    have ht : 2000 ≤ t := by dsimp [t]; omega
    have hn : N ≤ L := by dsimp [N,t]; omega
    have hns : N+s = L := by dsimp [s]; omega
    have hceiling : L ≤ 1000*t + 1000 := by dsimp [t]; omega
    obtain ⟨A,hA,hcard,hm⟩ := hMean t ht
    let Y (k : ℕ) := (truncated N ((k:ℝ)/2^N)).re
    let G := A.filter fun i => (7442/10000:ℝ)*N < Y i
    have hpos : 0 < (N:ℝ) := by dsimp [N]; positivity
    have upper (k : ℕ) (_hk : k ∈ A) : Y k ≤ (N:ℝ) := by
      apply (Complex.re_le_norm _).trans
      dsimp only [truncated]
      refine (norm_sum_le _ _).trans ?_
      simp [Complex.norm_exp]
    have high : (A.card:ℝ)/1000 < (G.card:ℝ) := many_high_words A Y hpos upper hm
    have ent : (2:ℝ)^(419*t) ≤ (1000*(t:ℝ)+1)*((1000*t).choose (85*t):ℝ) := by
      exact_mod_cast hEntropy t
    have bound : (2:ℝ)^((209/500:ℝ)*L) ≤ (G.card:ℝ) := by
      have hc := Nat.cast_le (α := ℝ).mpr hcard
      push_cast at hc
      have a : ((1000*t).choose (85*t):ℝ) ≤ 500*(G.card:ℝ) := by linarith
      have hb := (density_exponent L t ht hceiling).trans (ent.trans
        (mul_le_mul_of_nonneg_left a (by positivity)))
      apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < 500*(1000*(t:ℝ)+1))).mp
      linarith only [hb]
    let S := G.image fun k => k*2^s
    refine ⟨S,?_,?_,?_⟩
    · intro k hk
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hk
      have ha' := mem_range.mp (hA (mem_filter.mp ha).1)
      rw [mem_range, ←hns, pow_add]
      exact (Nat.mul_lt_mul_right (by positivity)).mpr ha'
    · have hinj : Function.Injective (fun k : ℕ => k*2^s) :=
        fun i j h => Nat.eq_of_mul_eq_mul_right (by positivity) h
      rw [show S.card = G.card from card_image_of_injective _ hinj]
      apply (le_div_iff₀ (by positivity)).mpr
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      convert bound using 2; ring
    · intro k hk
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hk
      have height := (mem_filter.mp ha).2
      change _ < (truncated N ((a:ℝ)/2^N)).re at height
      have grid : (↑(a*2^s:ℕ):ℝ)/2^L = (a:ℝ)/2^N := by
        push_cast
        rw [←hns, pow_add]
        field_simp
      rw [grid, ←hns, pad_truncated]
      apply lt_of_lt_of_le _ (Complex.re_le_norm _)
      simp only [Complex.add_re, Complex.natCast_re, Nat.cast_add]
      have hπ := Real.pi_lt_d4
      have hb : (2000001:ℝ) ≤ (N:ℝ) := by
        exact_mod_cast (show 2000001 ≤ N by dsimp [N]; omega)
      have hn' := mul_le_mul_of_nonneg_right hπ.le hpos.le
      have hs' := mul_le_mul_of_nonneg_right hπ.le (Nat.cast_nonneg (α := ℝ) s)
      nlinarith only [height, hπ, hn', hs', hb, Nat.cast_nonneg (α := ℝ) s]
  exact ⟨2000001, high_set_from_word_mean⟩
