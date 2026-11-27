import Mathlib

/-- The number of proper prime powers up to `Y` grows like `√Y log Y`. Adapted from the accepted
`L-twin-primes-power-count` proof of the same route (TP-0001). -/
private lemma proper_prime_power_count (Y : ℕ) (hY : 2 ≤ Y) :
    (((Finset.range (Y+1)).filter (fun n => IsPrimePow n ∧ ¬n.Prime)).card : ℝ)
      ≤ 3 * Real.sqrt Y * Real.log (2+(Y:ℝ)) := by
  classical
  have hY0 : 0 < Y := by omega
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℕ := Nat.log 2 Y + 1 with hKdef
  set R : ℕ := Nat.sqrt Y + 1 with hRdef
  set S : Finset ℕ := (Finset.range (Y+1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) with hS
  have hex : ∀ n ∈ S, ∃ q : ℕ × ℕ, q.1 ∈ Finset.Icc 2 K ∧ q.2 ∈ Finset.range R ∧ n = q.2 ^ q.1 := by
    intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hnrange : n ∈ Finset.range (Y+1) := hmem.1
    have his : IsPrimePow n := hmem.2.1
    have hnprime : ¬ n.Prime := hmem.2.2
    have hnY : n ≤ Y := by
      have := Finset.mem_range.mp hnrange
      omega
    obtain ⟨k, hkle, hkpos, p, hpn, hnpow, hpprime⟩ := (isPrimePow_nat_iff_bounded_log n).mp his
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with hlt | hge
      · have hk1 : k = 1 := by omega
        refine absurd ?_ hnprime
        rw [hnpow, hk1, pow_one]
        exact hpprime
      · exact hge
    have hkK : k ∈ Finset.Icc 2 K := by
      rw [Finset.mem_Icc]
      refine ⟨hk2, ?_⟩
      have h2 : Nat.log 2 n ≤ Nat.log 2 Y := Nat.log_mono_right hnY
      simp only [hKdef]
      omega
    have hpnR : p ∈ Finset.range R := by
      rw [Finset.mem_range]
      have hppow : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hpprime.pos hk2
      have hp2n : p ^ 2 ≤ n := by
        rw [hnpow]
        exact hppow
      have hpsqrt : p ≤ Nat.sqrt n := Nat.le_sqrt'.mpr hp2n
      have hsqrtmono : Nat.sqrt n ≤ Nat.sqrt Y := Nat.sqrt_le_sqrt hnY
      simp only [hRdef]
      omega
    exact ⟨(k, p), hkK, hpnR, hnpow⟩
  let φ : ℕ → ℕ × ℕ := fun n => if hn : n ∈ S then Classical.choose (hex n hn) else (0, 0)
  have hφprop : ∀ n (hn : n ∈ S), (φ n).1 ∈ Finset.Icc 2 K ∧ (φ n).2 ∈ Finset.range R ∧ n = (φ n).2 ^ (φ n).1 := by
    intro n hn
    have hφeq : φ n = Classical.choose (hex n hn) := by
      dsimp only [φ]
      rw [dif_pos hn]
    rw [hφeq]
    exact Classical.choose_spec (hex n hn)
  have hmain : S.card ≤ (Finset.Icc 2 K).card * R := by
    have hmaps : Set.MapsTo φ (S : Set ℕ) (((Finset.Icc 2 K).product (Finset.range R)) : Set (ℕ × ℕ)) := by
      intro n hn
      exact Finset.mem_product.mpr ⟨(hφprop n hn).1, (hφprop n hn).2.1⟩
    have hinj : (S : Set ℕ).InjOn φ := by
      intro n hn m hm heq
      have hn' := (hφprop n hn).2.2
      have hm' := (hφprop m hm).2.2
      calc n = (φ n).2 ^ (φ n).1 := hn'
        _ = (φ m).2 ^ (φ m).1 := by rw [heq]
        _ = m := hm'.symm
    calc S.card ≤ ((Finset.Icc 2 K).product (Finset.range R)).card :=
          Finset.card_le_card_of_injOn φ hmaps hinj
      _ = (Finset.Icc 2 K).card * (Finset.range R).card := Finset.card_product _ _
      _ = (Finset.Icc 2 K).card * R := by rw [Finset.card_range]
  have hKcard : ((Finset.Icc 2 K).card : ℝ) = (Nat.log 2 Y : ℝ) := by
    have hnat : (Finset.Icc 2 K).card = Nat.log 2 Y := by
      rw [Nat.card_Icc]
      simp only [hKdef]
      omega
    exact_mod_cast hnat
  have hmainR : (S.card : ℝ) ≤ (Nat.log 2 Y : ℝ) * (R : ℝ) := by
    have h := hmain
    calc (S.card : ℝ) ≤ (((Finset.Icc 2 K).card * R : ℕ) : ℝ) := by exact_mod_cast h
      _ = ((Finset.Icc 2 K).card : ℝ) * (R : ℝ) := by push_cast; ring
      _ = (Nat.log 2 Y : ℝ) * (R : ℝ) := by rw [hKcard]
  have hpowY : (2:ℕ) ^ Nat.log 2 Y ≤ Y := Nat.pow_log_le_self 2 (by omega)
  have hpowY' : (2:ℝ) ^ Nat.log 2 Y ≤ (Y:ℝ) := by exact_mod_cast hpowY
  have hlogY : (Nat.log 2 Y : ℝ) * Real.log 2 ≤ Real.log (Y:ℝ) :=
    Real.le_log_of_pow_le (by norm_num) hpowY'
  have hlogYle : Real.log (Y:ℝ) ≤ Real.log (2 + (Y:ℝ)) := by
    apply Real.log_le_log (by positivity)
    linarith [(Nat.cast_nonneg Y : (0:ℝ) ≤ (Y:ℝ))]
  have hKreal : (Nat.log 2 Y : ℝ) ≤ Real.log (2 + (Y:ℝ)) / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    linarith
  have hsqrtY : (Nat.sqrt Y : ℝ) ≤ Real.sqrt (Y:ℝ) := by
    have h1 : (Nat.sqrt Y : ℝ) ^ 2 ≤ (Y:ℝ) := by
      have := Nat.sqrt_le' Y
      exact_mod_cast this
    exact Real.le_sqrt_of_sq_le h1
  have hsqrt1 : (1:ℝ) ≤ Real.sqrt (Y:ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (show 1 ≤ Y by omega)
  have hRreal : (R : ℝ) ≤ 2 * Real.sqrt (Y:ℝ) := by
    simp only [hRdef]
    push_cast
    linarith
  have hcoef : (2:ℝ) / Real.log 2 ≤ 3 := by
    rw [div_le_iff₀ hlog2pos]
    nlinarith [Real.log_two_gt_d9]
  have hRnonneg : (0:ℝ) ≤ (R:ℝ) := by positivity
  have hbdnonneg : (0:ℝ) ≤ Real.log (2 + (Y:ℝ)) / Real.log 2 := by
    apply div_nonneg
    · apply Real.log_nonneg
      linarith [(Nat.cast_nonneg Y : (0:ℝ) ≤ (Y:ℝ))]
    · exact le_of_lt hlog2pos
  have hsqrtYnonneg : 0 ≤ Real.sqrt (Y:ℝ) := Real.sqrt_nonneg _
  have hlogYnonneg : 0 ≤ Real.log (2 + (Y:ℝ)) := by
    apply Real.log_nonneg
    linarith [(Nat.cast_nonneg Y : (0:ℝ) ≤ (Y:ℝ))]
  calc (S.card : ℝ) ≤ (Nat.log 2 Y : ℝ) * (R : ℝ) := hmainR
    _ ≤ (Real.log (2 + (Y:ℝ)) / Real.log 2) * (2 * Real.sqrt (Y:ℝ)) := by
        exact mul_le_mul hKreal hRreal hRnonneg hbdnonneg
    _ = (2 / Real.log 2) * (Real.sqrt (Y:ℝ) * Real.log (2 + (Y:ℝ))) := by ring
    _ ≤ 3 * (Real.sqrt (Y:ℝ) * Real.log (2 + (Y:ℝ))) := by
        apply mul_le_mul_of_nonneg_right hcoef
        positivity
    _ = 3 * Real.sqrt (Y:ℝ) * Real.log (2 + (Y:ℝ)) := by ring

/-- Summing over a union costs at most the sum over the two parts. -/
private lemma sum_union_le_of_nonneg {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) : (s ∪ t).sum f ≤ s.sum f + t.sum f := by
  classical
  have hsub : s ⊆ s ∪ t := Finset.subset_union_left
  have hsplit := Finset.sum_sdiff (f := f) hsub
  have hle : ((s ∪ t) \ s).sum f ≤ t.sum f := by
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun x _ _ => hf x)
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rcases hx with ⟨hx1, hx2⟩
    rcases Finset.mem_union.mp hx1 with h | h
    · exact absurd h hx2
    · exact h
  linarith

/-- The normalized narrow-window contamination is `O(log³(2+X)/√X)`. -/
private lemma contamination_core (X : ℕ) (hX : 2 ≤ X) :
    ((((Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum
        (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)))
      / (X : ℝ) ≤ 1000 * (Real.log (2+(X:ℝ))^3 / Real.sqrt (X:ℝ)) := by
  classical
  set Y : ℕ := 2*X+2 with hYdef
  have hY2 : 2 ≤ Y := by simp only [hYdef]; omega
  have hXpos : (0:ℝ) < (X:ℝ) := by exact_mod_cast (show 0 < X by omega)
  set L : ℝ := Real.log (2 + (Y:ℝ)) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    apply Real.log_pos
    push_cast
    have : (0:ℝ) ≤ (Y:ℝ) := Nat.cast_nonneg Y
    linarith
  set PP : Finset ℕ := (Finset.range (Y+1)).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) with hPPdef
  have hPPcard : (PP.card : ℝ) ≤ 3 * Real.sqrt (Y:ℝ) * L := by
    have h := proper_prime_power_count Y hY2
    rw [hPPdef, hLdef]
    exact h
  set B : Finset ℕ := ((Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime)) with hBdef
  have hBW : ∀ n ∈ B, X < n ∧ 50*n < 51*X := by
    intro n hn
    rw [hBdef] at hn
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
  have hBn : ∀ n ∈ B, n ≤ 2*X := by
    intro n hn
    rw [hBdef] at hn
    have := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    omega
  have hBL2 : ∀ n ∈ B, ArithmeticFunction.vonMangoldt (n+2) ≤ L := by
    intro n hn
    have hn3 : (0:ℝ) < ((n+2 : ℕ) : ℝ) := by positivity
    have h1 : ArithmeticFunction.vonMangoldt (n+2) ≤ Real.log ((n+2 : ℕ) : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log
    have h2 : Real.log ((n+2 : ℕ) : ℝ) ≤ L := by
      rw [hLdef]
      apply Real.log_le_log hn3
      have hn2x : (n:ℝ) ≤ 2*(X:ℝ) := by exact_mod_cast hBn n hn
      simp only [hYdef]
      push_cast
      linarith
    linarith
  have hBL1 : ∀ n ∈ B, ArithmeticFunction.vonMangoldt n ≤ L := by
    intro n hn
    have hnpos : (0:ℝ) < (n:ℝ) := by
      have := (hBW n hn).1
      exact_mod_cast (show 0 < n by omega)
    have h1 : ArithmeticFunction.vonMangoldt n ≤ Real.log (n:ℝ) := ArithmeticFunction.vonMangoldt_le_log
    have h2 : Real.log (n:ℝ) ≤ L := by
      rw [hLdef]
      apply Real.log_le_log hnpos
      have hn2x : (n:ℝ) ≤ 2*(X:ℝ) := by exact_mod_cast hBn n hn
      simp only [hYdef]
      push_cast
      linarith
    linarith
  -- split the bad set by the left end and by the right end
  have hbad_of_mem : ∀ n ∈ B, ¬ (n.Prime ∧ (n+2).Prime) := by
    intro n hn
    rw [hBdef] at hn
    exact (Finset.mem_filter.mp hn).2
  have hsplit : B.sum (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))
      ≤ (B.filter (fun n => ¬ n.Prime)).sum (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))
        + (B.filter (fun n => ¬ (n+2).Prime)).sum (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)) := by
    have hcover : B ⊆ B.filter (fun n => ¬ n.Prime) ∪ B.filter (fun n => ¬ (n+2).Prime) := by
      intro n hn
      have hbad : ¬ (n.Prime ∧ (n+2).Prime) := hbad_of_mem n hn
      rcases not_and_or.mp hbad with h | h
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hn, h⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hn, h⟩))
    have h1 : B.sum (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))
        ≤ (B.filter (fun n => ¬ n.Prime) ∪ B.filter (fun n => ¬ (n+2).Prime)).sum
            (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ => by positivity)
    have h2 := sum_union_le_of_nonneg (B.filter (fun n => ¬ n.Prime)) (B.filter (fun n => ¬ (n+2).Prime))
      (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)) (fun n => by positivity)
    linarith
  -- bound each part
  have hB1 : (B.filter (fun n => ¬ n.Prime)).sum (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))
      ≤ L^2 * (PP.card : ℝ) := by
    have hstep1 : (B.filter (fun n => ¬ n.Prime)).sum (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))
        ≤ (B.filter (fun n => ¬ n.Prime)).sum (fun n => ArithmeticFunction.vonMangoldt n * L) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnB : n ∈ B := (Finset.mem_filter.mp hn).1
      exact mul_le_mul_of_nonneg_left (hBL2 n hnB) ArithmeticFunction.vonMangoldt_nonneg
    have hstep2 : (B.filter (fun n => ¬ n.Prime)).sum (fun n => ArithmeticFunction.vonMangoldt n)
        ≤ L * (PP.card : ℝ) := by
      set S1 : Finset ℕ := (B.filter (fun n => ¬ n.Prime)).filter (fun n => n ∈ PP) with hS1def
      have hS1PP : S1 ⊆ PP := fun n hn => (Finset.mem_filter.mp hn).2
      have hS1B : ∀ n ∈ S1, n ∈ B := by
        intro n hn
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
      have heq : (B.filter (fun n => ¬ n.Prime)).sum (fun n => ArithmeticFunction.vonMangoldt n)
          = S1.sum (fun n => ArithmeticFunction.vonMangoldt n) := by
        conv_rhs => rw [hS1def, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n hn
        by_cases h : n ∈ PP
        · simp [h]
        · have hz : ArithmeticFunction.vonMangoldt n = 0 := by
            by_contra hne
            have his : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne
            have hnB : n ∈ B := (Finset.mem_filter.mp hn).1
            have hnnotprime : ¬ n.Prime := (Finset.mem_filter.mp hn).2
            have hnY : n ≤ Y := by have := hBn n hnB; simp only [hYdef]; omega
            have : n ∈ PP := by
              rw [hPPdef]
              exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), his, hnnotprime⟩
            exact h this
          simp [h, hz]
      rw [heq]
      calc S1.sum (fun n => ArithmeticFunction.vonMangoldt n)
          ≤ S1.sum (fun _ => L) := by
            apply Finset.sum_le_sum
            intro n hn
            exact hBL1 n (hS1B n hn)
        _ = L * (S1.card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
        _ ≤ L * (PP.card : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hLpos)
            exact_mod_cast Finset.card_le_card hS1PP
    calc (B.filter (fun n => ¬ n.Prime)).sum (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))
        ≤ (B.filter (fun n => ¬ n.Prime)).sum (fun n => ArithmeticFunction.vonMangoldt n * L) := hstep1
      _ = L * (B.filter (fun n => ¬ n.Prime)).sum (fun n => ArithmeticFunction.vonMangoldt n) := by
            rw [← Finset.sum_mul]
            ring
      _ ≤ L * (L * (PP.card : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hstep2 (le_of_lt hLpos)
      _ = L^2 * (PP.card : ℝ) := by ring
  have hB2 : (B.filter (fun n => ¬ (n+2).Prime)).sum (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))
      ≤ L^2 * (PP.card : ℝ) := by
    have hstep1 : (B.filter (fun n => ¬ (n+2).Prime)).sum (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))
        ≤ (B.filter (fun n => ¬ (n+2).Prime)).sum (fun n => L * ArithmeticFunction.vonMangoldt (n+2)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnB : n ∈ B := (Finset.mem_filter.mp hn).1
      exact mul_le_mul_of_nonneg_right (hBL1 n hnB) ArithmeticFunction.vonMangoldt_nonneg
    have hstep2 : (B.filter (fun n => ¬ (n+2).Prime)).sum (fun n => ArithmeticFunction.vonMangoldt (n+2))
        ≤ L * (PP.card : ℝ) := by
      set S2 : Finset ℕ := (B.filter (fun n => ¬ (n+2).Prime)).filter (fun n => ArithmeticFunction.vonMangoldt (n+2) ≠ 0) with hS2def
      have hS2B : ∀ n ∈ S2, n ∈ B := by
        intro n hn
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
      have hS2nn : ∀ n ∈ S2, ¬ (n+2).Prime := by
        intro n hn
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
      have hmaps : Set.MapsTo (fun n : ℕ => n + 2) (S2 : Set ℕ) (PP : Set ℕ) := by
        intro n hn
        have hnB : n ∈ B := hS2B n hn
        have hne : ArithmeticFunction.vonMangoldt (n+2) ≠ 0 := (Finset.mem_filter.mp hn).2
        have his : IsPrimePow (n+2) := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne
        have hn2x : n ≤ 2*X := hBn n hnB
        have hnY : n + 2 ≤ Y := by rw [hYdef]; omega
        have hnY' : n + 2 < Y + 1 := Nat.lt_succ_of_le hnY
        rw [hPPdef]
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnY', his, hS2nn n hn⟩
      have hinj : (S2 : Set ℕ).InjOn (fun n : ℕ => n + 2) := by
        intro a _ b _ h
        have h' : a + 2 = b + 2 := h
        omega
      have hcard : S2.card ≤ PP.card := Finset.card_le_card_of_injOn _ hmaps hinj
      have heq : (B.filter (fun n => ¬ (n+2).Prime)).sum (fun n => ArithmeticFunction.vonMangoldt (n+2))
          = S2.sum (fun n => ArithmeticFunction.vonMangoldt (n+2)) := by
        conv_rhs => rw [hS2def, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n hn
        by_cases h : ArithmeticFunction.vonMangoldt (n+2) = 0
        · simp [h]
        · simp [h]
      rw [heq]
      calc S2.sum (fun n => ArithmeticFunction.vonMangoldt (n+2))
          ≤ S2.sum (fun _ => L) := by
            apply Finset.sum_le_sum
            intro n hn
            exact hBL2 n (hS2B n hn)
        _ = L * (S2.card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
        _ ≤ L * (PP.card : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hLpos)
            exact_mod_cast hcard
    calc (B.filter (fun n => ¬ (n+2).Prime)).sum (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))
        ≤ (B.filter (fun n => ¬ (n+2).Prime)).sum (fun n => L * ArithmeticFunction.vonMangoldt (n+2)) := hstep1
      _ = L * (B.filter (fun n => ¬ (n+2).Prime)).sum (fun n => ArithmeticFunction.vonMangoldt (n+2)) := by
            rw [Finset.mul_sum]
      _ ≤ L * (L * (PP.card : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hstep2 (le_of_lt hLpos)
      _ = L^2 * (PP.card : ℝ) := by ring
  -- total bound
  have hbads : B.sum (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))
      ≤ 6 * L^3 * Real.sqrt (Y:ℝ) := by
    have h1 : B.sum (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))
        ≤ 2 * L^2 * (PP.card : ℝ) := by linarith
    calc B.sum (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))
        ≤ 2 * L^2 * (PP.card : ℝ) := h1
      _ ≤ 2 * L^2 * (3 * Real.sqrt (Y:ℝ) * L) := by
            apply mul_le_mul_of_nonneg_left hPPcard (by positivity)
      _ = 6 * L^3 * Real.sqrt (Y:ℝ) := by ring
  -- arithmetic: pass from `L` to the window logarithm
  have hApos : 0 < Real.log (2 + (X:ℝ)) := by
    apply Real.log_pos
    push_cast
    have : (0:ℝ) ≤ (X:ℝ) := Nat.cast_nonneg X
    linarith
  have hsqrtXpos : 0 < Real.sqrt (X:ℝ) := Real.sqrt_pos.mpr hXpos
  have hYle : (Y:ℝ) ≤ 4*(X:ℝ) := by
    have hXr : (2:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
    simp only [hYdef]
    push_cast
    linarith
  have hsqrtY : Real.sqrt (Y:ℝ) ≤ 2*Real.sqrt (X:ℝ) := by
    calc Real.sqrt (Y:ℝ) ≤ Real.sqrt (4*(X:ℝ)) := Real.sqrt_le_sqrt hYle
      _ = 2 * Real.sqrt (X:ℝ) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
          norm_num
  have hLle : L ≤ 2 * Real.log (2+(X:ℝ)) := by
    rw [hLdef]
    have hle : 2 + (Y:ℝ) ≤ (2+(X:ℝ))^2 := by
      have hXr : (2:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
      simp only [hYdef]
      push_cast
      nlinarith
    calc Real.log (2 + (Y:ℝ)) ≤ Real.log ((2+(X:ℝ))^2) := Real.log_le_log (by positivity) hle
      _ = 2 * Real.log (2+(X:ℝ)) := by rw [Real.log_pow]; norm_num
  have hratio : 6 * L^3 * Real.sqrt (Y:ℝ) / (X:ℝ) ≤ 96 * Real.log (2+(X:ℝ))^3 / Real.sqrt (X:ℝ) := by
    have hLnn : 0 ≤ L := le_of_lt hLpos
    have hstep : 6 * L^3 * Real.sqrt (Y:ℝ) ≤ 6 * (2*Real.log (2+(X:ℝ)))^3 * (2*Real.sqrt (X:ℝ)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLnn hLle 3) (by norm_num)) hsqrtY
        (Real.sqrt_nonneg _) (by positivity)
    have hdiv := div_le_div_of_nonneg_right hstep (le_of_lt hXpos)
    have heq : 6 * (2*Real.log (2+(X:ℝ)))^3 * (2*Real.sqrt (X:ℝ)) / (X:ℝ)
        = 96 * Real.log (2+(X:ℝ))^3 / Real.sqrt (X:ℝ) := by
      rw [eq_div_iff (ne_of_gt hsqrtXpos)]
      field_simp
      rw [Real.sq_sqrt (le_of_lt hXpos)]
      ring
    linarith [hdiv, heq ▸ hdiv]
  calc B.sum (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)) / (X:ℝ)
      ≤ 6 * L^3 * Real.sqrt (Y:ℝ) / (X:ℝ) := div_le_div_of_nonneg_right hbads (le_of_lt hXpos)
    _ ≤ 96 * Real.log (2+(X:ℝ))^3 / Real.sqrt (X:ℝ) := hratio
    _ = 96 * (Real.log (2+(X:ℝ))^3 / Real.sqrt (X:ℝ)) := by ring
    _ ≤ 1000 * (Real.log (2+(X:ℝ))^3 / Real.sqrt (X:ℝ)) := by
        have hnn : 0 ≤ Real.log (2+(X:ℝ))^3 / Real.sqrt (X:ℝ) := by positivity
        linarith

theorem PEqualNP.Outside.L_twin_primes_window_contamination :
    (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let E := fun (X : ℕ) => ((w X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum v / (X : ℝ); let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → E X ≤ C * e X) := by
  dsimp only
  refine ⟨1000, by norm_num, ?_⟩
  intro X hX
  exact contamination_core X hX
