import Mathlib
import Conjectures.Goldbach.Type2MovingDiagonalMoment

private theorem mixed_product_error (x y u v : ℂ) (T a b : ℝ)
    (hu : ‖u‖ ≤ T) (hx : ‖x-u‖ ≤ a) (hy : ‖y-v‖ ≤ b) :
    ‖x*y-u*v‖ ≤ a*‖y‖ + T*b := by
  calc
    _ = ‖(x-u)*y + u*(y-v)‖ := by ring_nf
    _ ≤ ‖(x-u)*y‖ + ‖u*(y-v)‖ := norm_add_le _ _
    _ ≤ _ := by
      simp only [norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
        (mul_le_mul hu hy (norm_nonneg _) ((norm_nonneg _).trans hu))

open MeasureTheory TypeTwoDiagonal GoldbachTransitionSquare

private theorem mixed_clipped_error (A : Set ℝ) (hA : MeasurableSet A)
    (x y u v : ℝ → ℂ) (hx : Continuous x) (hy : Continuous y)
    (hu : Continuous u) (hv : Continuous v) (n : ℕ) {T s : ℝ}
    (hT : 0 < T) (hs : 0 < s)
    (cap : ∀ t ∈ Set.Ioc (0:ℝ) 1, t ∈ A → ‖x t‖ ≤ T) :
    ‖coefficient A (fun t => x t*y t) n - coefficient A (fun t => clip T (u t)*v t) n‖ ≤
      2*s*(mass Set.univ (fun t => x t-u t) + mass Set.univ (fun t => y t-v t)) +
      s⁻¹*(mass Set.univ y + mass Set.univ u) := by
  let g t := clip T (u t)
  have hg : Continuous g := (clip_continuous hT).comp hu
  have ep : Continuous (TypeTwoDiagonal.phase n) := by unfold TypeTwoDiagonal.phase; fun_prop
  let b (t : ℝ) := 2*s*(‖x t-u t‖^2+‖y t-v t‖^2)+s⁻¹*(‖y t‖^2+‖u t‖^2)
  have hb : Continuous b := by dsimp [b]; fun_prop
  have hxy : Integrable (A.indicator (fun t => x t*y t*TypeTwoDiagonal.phase n t)) unitMeasure := (continuous_unit_integrable ((hx.mul hy).mul ep)).indicator hA
  have hgv : Integrable (A.indicator (fun t => g t*v t*TypeTwoDiagonal.phase n t)) unitMeasure := (continuous_unit_integrable ((hg.mul hv).mul ep)).indicator hA
  unfold coefficient
  rw [← integral_sub hxy hgv]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ t, b t ∂unitMeasure := by
      apply integral_mono_ae (hxy.sub hgv).norm (continuous_unit_integrable hb)
      filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioc (a:=(0:ℝ)) (b:=1))] with t ht
      change ‖A.indicator (fun z => x z*y z*TypeTwoDiagonal.phase n z) t - A.indicator (fun z => g z*v z*TypeTwoDiagonal.phase n z) t‖ ≤ b t
      by_cases ha : t ∈ A
      · simp only [Set.indicator_of_mem ha, ← sub_mul, norm_mul, show ‖TypeTwoDiagonal.phase n t‖ = 1 from GoldbachTransitionSquare.norm_phase _, mul_one]
        have err := mixed_product_error (x t) (y t) (g t) (v t) ‖u t‖
          (2*‖x t-u t‖) ‖y t-v t‖ (clip_bounds hT (u t)).2
          (clip_near hT (cap t ht ha)) le_rfl
        have h1 := GoldbachTransitionFourier.scaled_young (x:=‖x t-u t‖) (y:=‖y t‖) hs
        have h2 := GoldbachTransitionFourier.scaled_young (x:=‖y t-v t‖) (y:=‖u t‖) hs
        dsimp [b]
        nlinarith [mul_nonneg (inv_nonneg.mpr hs.le) (sq_nonneg ‖u t‖), mul_nonneg (norm_nonneg (y t-v t)) (norm_nonneg (u t)),
          mul_nonneg hs.le (sq_nonneg ‖x t-u t‖),mul_nonneg hs.le (sq_nonneg ‖y t-v t‖)]
      · simp only [Set.indicator_of_notMem ha,sub_self,norm_zero]
        dsimp [b]
        positivity
    _ = _ := by
      simp only [b,mass,Set.indicator_univ]
      rw [integral_add,integral_const_mul,integral_const_mul,integral_add,integral_add] <;>
        apply continuous_unit_integrable <;> fun_prop

open Finset

private theorem mixed_short_row_bound (n B H k D : ℕ) (hn : 0 < n) (hH : 0 < H)
    (t : ℝ) (ht : t ∈ Set.Icc 0 1) (hm : t ∉ wide n B H)
    (A : Finset ℕ) (hA : ∀ a ∈ A, a ≤ B) (hc : A.card ≤ 2*D)
    (w c : ℕ → ℂ) (cut : ℕ → ℕ) (hcut : ∀ a ∈ A, cut a ≤ 2^k)
    {W V : ℝ} (hw : ∀ a ∈ A, ‖w a‖ ≤ W) (hv : ∀ j < 2^k, ‖c j‖ ≤ V) :
    ‖∑ a ∈ A, w a * ∑ j ∈ range (cut a), c j * DyadicMixedB4Fourier.mode (j:ℤ) ((a:ℝ)*t)‖^2 ≤
    (2*D*W^2) * (((k:ℝ)+1)^2 *
       (3/(min 1 ((H:ℝ)/n)) + 6*(1+2*Real.pi*(2^k:ℕ))) * ((2^k:ℕ)*V^2)) := by
  let f a := ∑ j ∈ range (cut a), c j * DyadicMixedB4Fourier.mode (j:ℤ) ((a:ℝ)*t)
  have rows : ∑ a ∈ A, ‖w a‖^2 ≤ 2*D*W^2 := by
    calc
      _ ≤ ∑ _a ∈ A, W^2 := sum_le_sum fun a ha => pow_le_pow_left₀ (norm_nonneg _) (hw a ha) 2
      _ = (A.card:ℝ)*W^2 := by simp
      _ ≤ _ := by gcongr; exact_mod_cast hc
  have cols : ∑ j ∈ range (2^k), ‖c j‖^2 ≤ (2^k:ℕ)*V^2 := by
    calc
      _ ≤ ∑ _j ∈ range (2^k), V^2 := sum_le_sum fun j hj =>
        pow_le_pow_left₀ (norm_nonneg _) (hv j (mem_range.mp hj)) 2
      _ = _ := by simp
  have sieve := deep_prefix_sieve n B H k hn hH t ht hm A hA c cut
  have ident : (∑ a ∈ A, ‖f a‖^2) = _ := Finset.sum_congr rfl
    (fun a (ha : a ∈ A) => show ‖f a‖^2 =
      ‖∑ j ∈ range (min (2^k) (cut a)), c j * DyadicMixedB4Fourier.mode (j:ℤ) ((a:ℝ)*t)‖^2 by
        rw [min_eq_right (hcut a ha)])
  have est := (le_of_eq ident).trans sieve
  have cs := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le A (fun a => w a*f a)) 2
  simp only [norm_mul] at cs
  exact (cs.trans (sum_mul_sq_le_sq_mul_sq A (fun a => ‖w a‖) (fun a => ‖f a‖))).trans
    (mul_le_mul rows (est.trans (mul_le_mul_of_nonneg_left cols (by positivity)))
      (sum_nonneg fun a _ => sq_nonneg _) (by positivity))

private theorem mangoldt_rows :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n U B H k D : ℕ, 0 < n → 0 < H →
    ∀ t ∈ Set.Icc (0:ℝ) 1, t ∉ wide n B H →
    ∀ A : Finset ℕ, (∀ a ∈ A, D ≤ a ∧ a ≤ B ∧ a ≤ n) →
    A.card ≤ 2*D → n/D+1 ≤ 2^k →
    ‖∑ a ∈ A, (lowMoebiusWeight U a : ℂ) *
      ∑ j ∈ range (n/a+1), (if U < j ∧ j ≤ n then
        ((ArithmeticFunction.vonMangoldt j : ℝ) : ℂ) else 0) *
          DyadicMixedB4Fourier.mode (j:ℤ) ((a:ℝ)*t)‖^2 ≤
    (2*D*(C*(n:ℝ)^(1/3072:ℝ))^2) * (((k:ℝ)+1)^2 *
       (3/(min 1 ((H:ℝ)/n)) + 6*(1+2*Real.pi*(2^k:ℕ))) * ((2^k:ℕ)*(Real.log n)^2)) := by
  obtain ⟨C,hC,hτ⟩ := fine_divisor_envelope
  refine ⟨C,hC,?_⟩
  intro n U B H k D hn hH t ht hm A hA hc hcover
  by_cases hD : D = 0
  · have hempty : A = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [hempty,hD]
  apply mixed_short_row_bound n B H k D hn hH t ht hm A (fun a ha => (hA a ha).2.1) hc
  · intro a ha
    have hd : n/a ≤ n/D := Nat.div_le_div_left (hA a ha).1 (Nat.pos_of_ne_zero hD)
    omega
  · intro a ha
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact (abs_lowMoebiusWeight_le U a).trans (hτ n a (hA a ha).2.2)
  · intro j hj
    split_ifs with h
    · rw [Complex.norm_real,Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast (show 0 < j by omega)) (by exact_mod_cast h.2))
    · simp only [norm_zero]
      exact Real.log_nonneg (by exact_mod_cast hn)

private theorem row_budget_saving {D N W V K Z R X C : ℝ}
    (hD : 0 ≤ D) (hN : 0 ≤ N) (hR : 0 ≤ R) (hX : 1 ≤ X)
    (hblock : D*N ≤ 4*X^3072) (hlen : N ≤ 8*X^2880)
    (hsep : Z ≤ 4*X^2880) (hw : W^2 ≤ C^2*X^2) :
    (2*D*W^2)*(K^2*(3*Z+6*(1+2*R*N))*(N*V^2)) ≤
      8*(18+96*R)*C^2*K^2*V^2*X^5954 := by
  have hx : 0 ≤ X := by linarith
  have h1 : 1 ≤ X^2880 := one_le_pow₀ hX
  have ha : 3*Z+6*(1+2*R*N) ≤ (18+96*R)*X^2880 := by
    nlinarith only [hsep,h1,mul_le_mul_of_nonneg_left hlen hR]
  calc
    _ = (2*(D*N)*W^2*K^2*V^2)*(3*Z+6*(1+2*R*N)) := by ring
    _ ≤ (2*(4*X^3072)*(C^2*X^2)*K^2*V^2)*((18+96*R)*X^2880) := by
      apply le_trans (mul_le_mul_of_nonneg_left ha (by positivity))
      gcongr
    _ = _ := by ring

private theorem actual_row_geometry {n a : ℕ} (ha : a ≤ n)
    (hU : ⌊(n:ℝ)^(1/16:ℝ)⌋₊ < a) :
    let D := 2^(Nat.log 2 a)
    let k := Nat.log 2 (n/D+1)+1
    let N := 2^k
    let X := (n:ℝ)^(1/3072:ℝ)
    D ≤ a ∧ a < 2*D ∧ n/D+1 ≤ N ∧ D*N ≤ 4*n ∧ (N:ℝ) ≤ 8*X^2880 := by
  intro D k N X
  have ha0 : a ≠ 0 := by omega
  have hd : D ≤ a := Nat.pow_log_le_self _ ha0
  have had : a < 2*D := by
    simpa [D,pow_succ,Nat.mul_comm] using Nat.lt_pow_succ_log_self (by decide : 1<2) a
  have hN : n/D+1 ≤ N := (Nat.lt_pow_succ_log_self (by decide : 1<2) _).le
  have hh : N ≤ 2*(n/D+1) := by
    dsimp [N,k]
    rw [pow_succ,Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (Nat.succ_ne_zero (n/D)))
  have prod : D*N ≤ 4*n := by
    calc
      _ ≤ D*(2*(n/D+1)) := Nat.mul_le_mul_left _ hh
      _ = 2*((n/D)*D)+2*D := by ring
      _ ≤ _ := by have := Nat.div_mul_le_self n D; omega
  refine ⟨hd, had, hN, prod, ?_⟩
  have npos : 0 < n := by omega
  have hX : 0 < X := Real.rpow_pos_of_pos (by exact_mod_cast npos) _
  have xp (i : ℕ) : X^i = (n:ℝ)^((i:ℝ)/3072) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  have hx192 : X^192 ≤ 2*(D:ℝ) := by
    have h := Nat.lt_floor_add_one ((n:ℝ)^(1/16:ℝ))
    have h' : ((⌊(n:ℝ)^(1/16:ℝ)⌋₊:ℕ):ℝ)+1 ≤ a := by exact_mod_cast hU
    rw [xp]; norm_num
    exact h.le.trans (h'.trans (by exact_mod_cast had.le))
  have hnum : X^3072 = (n:ℝ) := by rw [xp]; norm_num
  have hprod : (D:ℝ)*N ≤ 4*n := by exact_mod_cast prod
  apply le_of_mul_le_mul_right (a := X^192)
  · calc
      (N:ℝ)*X^192 ≤ N*(2*(D:ℝ)) := mul_le_mul_of_nonneg_left hx192 (Nat.cast_nonneg N)
      _ ≤ 8*(n:ℝ) := by linarith
      _ = (8*X^2880)*X^192 := by rw [← hnum]; ring
  · positivity

private theorem actual_arc_spacing {n : ℕ} (hn : 1 ≤ n) :
    let H : ℕ := 256 * ⌊(n:ℝ)^(1/3:ℝ)⌋₊ * (Nat.log 2 (n+2))^2
    let X := (n:ℝ)^(1/3072:ℝ)
    0 < H ∧ (min 1 ((H:ℝ)/n))⁻¹ ≤ 4*X^2880 := by
  intro H X
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hX : 1 ≤ X := Real.one_le_rpow hn' (by norm_num)
  have xp (i : ℕ) : X^i = (n:ℝ)^((i:ℝ)/3072) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg n)]; congr 1; ring
  let B := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
  have hb : 1 ≤ B := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hn' (by norm_num))
  have hlog : 0 < Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have hBH : B ≤ H := (show B ≤ 256*B by omega).trans
    (Nat.le_mul_of_pos_right _ (pow_pos hlog 2))
  have hh : 0 < H := by omega
  refine ⟨hh, ?_⟩
  have hr : X^1024 ≤ 2*(H:ℝ) := by
    rw [xp]; norm_num
    have hf := Nat.lt_floor_add_one ((n:ℝ)^(1/3:ℝ))
    change _ < (B:ℝ)+1 at hf
    have h1 : (1:ℝ) ≤ B := by exact_mod_cast hb
    have h2 : (B:ℝ) ≤ H := by exact_mod_cast hBH
    linarith
  have bound : (n:ℝ)/H ≤ 2*X^2048 := by
    apply (div_le_iff₀ (show (0:ℝ)<H by exact_mod_cast hh)).mpr
    have e : X^3072 = (n:ℝ) := by rw [xp]; norm_num
    rw [←e]
    calc
      _ = X^2048 * X^1024 := by ring
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hr (show 0≤X^2048 by positivity)]
  have hmono : X^2048 ≤ X^2880 := pow_le_pow_right₀ hX (by decide)
  rcases le_total 1 ((H:ℝ)/n) with h|h
  · rw [min_eq_left h,inv_one]; linarith [one_le_pow₀ hX (n:=2880)]
  · rw [min_eq_right h,inv_div]; linarith [one_le_pow₀ hX (n:=2880)]

private theorem range_to_positive (n : ℕ) (f : ℕ → ℂ) (hz : f 0 = 0) :
    ∑ m ∈ range (n+1), f m = ∑ m ∈ Icc 1 n, f m := by
  symm
  apply sum_subset
  · intro i hi
    exact mem_range.mpr (by have := (mem_Icc.mp hi).2; omega)
  · intro i hi ho
    have h := mem_range.mp hi
    have : i = 0 := by simp only [mem_Icc,not_and] at ho; omega
    simpa [this] using hz

private theorem mangoldt_band_rows (n U L B : ℕ) (hB : B ≤ n) (t : ℝ) :
    fourierSum n (band U L B ArithmeticFunction.vonMangoldt) t =
      ∑ a ∈ Ioc L B, (lowMoebiusWeight U a : ℂ) *
        ∑ j ∈ range (n/a+1), (if U < j ∧ j ≤ n then
          ((ArithmeticFunction.vonMangoldt j : ℝ) : ℂ) else 0) *
          DyadicMixedB4Fourier.mode (j:ℤ) ((a:ℝ)*t) := by
  classical
  let signal (j : ℕ) : ℂ := if U < j ∧ j ≤ n then (ArithmeticFunction.vonMangoldt j : ℝ) else 0
  let term (a j : ℕ) : ℂ := if L < a ∧ a ≤ B then
    (lowMoebiusWeight U a : ℂ)* (signal j * DyadicMixedB4Fourier.mode (j:ℤ) ((a:ℝ)*t)) else 0
  unfold fourierSum
  rw [range_to_positive _ _ (by simp [band])]
  calc
    _ = ∑ m ∈ Icc 1 n, ∑ a ∈ m.divisors, term a (m/a) := by
      apply sum_congr rfl
      intro m hm
      simp only [band, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, Finset.sum_filter]
      apply sum_congr rfl
      intro a ha
      have hmn := (mem_Icc.mp hm).2
      have hj := (Nat.div_le_self m a).trans hmn
      have prod := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)
      have phaseEq : GoldbachTransitionSquare.phase ((m:ℝ)*t) =
          DyadicMixedB4Fourier.mode ((m/a:ℕ):ℤ) ((a:ℝ)*t) := by
        unfold GoldbachTransitionSquare.phase DyadicMixedB4Fourier.mode DyadicMixedB4Fourier.frequency
        congr 1
        have eqr : (a:ℂ)*((m/a:ℕ):ℂ) = (m:ℂ) := by exact_mod_cast prod
        generalize m/a = j at eqr ⊢
        push_cast
        rw [←eqr]
        ring
      simp only [term,signal,phaseEq]
      split_ifs <;> simp_all [mul_assoc]
    _ = ∑ a ∈ Icc 1 n, ∑ j ∈ Icc 1 (n/a), term a j := finite_divisor_hyperbola n term
    _ = ∑ a ∈ Ioc L B, ∑ j ∈ Icc 1 (n/a), term a j := by
      symm
      apply sum_subset
      · intro a ha
        obtain ⟨h1,h2⟩ := mem_Ioc.mp ha
        exact mem_Icc.mpr ⟨by omega,by omega⟩
      · intro a ha ho
        simp only [mem_Ioc] at ho
        simp [term,ho]
    _ = _ := by
      refine sum_congr rfl fun a ha => ?_
      rw [range_to_positive _ _ (by simp), Finset.mul_sum]
      simp [term,mem_Ioc.mp ha,signal]

private theorem dyadic_band_sum {L B : ℕ} (w : ℕ → ℂ) :
    ∑ a ∈ Ioc L B, w a =
    ∑ i ∈ range (Nat.log 2 B+1), ∑ a ∈ (Ioc L B).filter (fun a => Nat.log 2 a = i), w a := by
  symm
  apply sum_fiberwise_of_maps_to
  intro a ha
  exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (mem_Ioc.mp ha).2))

private theorem dyadic_band_size (L B i : ℕ) :
    ((Ioc L B).filter (fun a => Nat.log 2 a = i)).card ≤ 2*2^i := by
  calc
    _ ≤ (range (2*2^i)).card := by
      apply card_le_card
      intro a ha
      obtain ⟨_, hi⟩ := mem_filter.mp ha
      apply mem_range.mpr
      simpa [←hi,pow_succ,Nat.mul_comm] using Nat.lt_pow_succ_log_self (by decide : 1<2) a
    _ = _ := card_range _

private theorem first_band_cap :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n P B : ℕ, 1 ≤ n → P ≤ B → P ≤ n →
    let U := ⌊(n:ℝ)^(1/16:ℝ)⌋₊
    let H := 256 * ⌊(n:ℝ)^(1/3:ℝ)⌋₊ * (Nat.log 2 (n+2))^2
    let X := (n:ℝ)^(1/3072:ℝ)
    ∀ t ∈ Set.Icc (0:ℝ) 1, t ∉ wide n B H →
      ‖fourierSum n (band U U P ArithmeticFunction.vonMangoldt) t‖ ≤
        (Nat.log 2 P+1 : ℕ) * Real.sqrt (8*(18+96*Real.pi)*C^2*
          ((Nat.log 2 (n+1):ℝ)+2)^2*(Real.log n)^2*X^5954) := by
  obtain ⟨C,hC,rows⟩ := mangoldt_rows
  refine ⟨C,hC,?_⟩
  intro n P B hn hPB hPn U H X t ht hm
  let w (a : ℕ) := (lowMoebiusWeight U a : ℂ) *
    ∑ j ∈ range (n/a+1), (if U < j ∧ j ≤ n then
      ((ArithmeticFunction.vonMangoldt j : ℝ) : ℂ) else 0) *
      DyadicMixedB4Fourier.mode (j:ℤ) ((a:ℝ)*t)
  let budget := 8*(18+96*Real.pi)*C^2*((Nat.log 2 (n+1):ℝ)+2)^2*(Real.log n)^2*X^5954
  have hX : 1 ≤ X := Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have xn : X^3072 = (n:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg n)]; norm_num
  obtain ⟨hH,hsep⟩ := actual_arc_spacing hn
  have block (i : ℕ) :
      ‖∑ a ∈ (Ioc U P).filter (fun a => Nat.log 2 a = i), w a‖ ≤ Real.sqrt budget := by
    let A := (Ioc U P).filter (fun a => Nat.log 2 a = i)
    by_cases hempty : A = ∅
    · change ‖∑ a ∈ A, w a‖ ≤ _
      simp [hempty]
    obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨haI,hi⟩ := mem_filter.mp ha
    obtain ⟨hau,hap⟩ := mem_Ioc.mp haI
    let D := 2^i
    let k := Nat.log 2 (n/D+1)+1
    have geo := actual_row_geometry (hap.trans hPn) hau
    simp only [hi] at geo
    have member (j : ℕ) (hj : j ∈ A) : D ≤ j ∧ j ≤ B ∧ j ≤ n := by
      obtain ⟨hI,hjlog⟩ := mem_filter.mp hj
      obtain ⟨hj1,hj2⟩ := mem_Ioc.mp hI
      exact ⟨by dsimp [D]; rw [←hjlog]; exact Nat.pow_log_le_self 2 (by omega),hj2.trans hPB,hj2.trans hPn⟩
    have raw := rows n U B H k D hn hH t ht hm A member (dyadic_band_size U P i) geo.2.2.1
    have hsize : (D:ℝ) * ((2^k:ℕ):ℝ) ≤ 4*X^3072 := by rw [xn]; exact_mod_cast geo.2.2.2.1
    have save := row_budget_saving (C:=C) (W:=C*X) (K:=(k:ℝ)+1) (V:=Real.log n)
      (Nat.cast_nonneg D) (Nat.cast_nonneg (2^k)) Real.pi_pos.le hX hsize geo.2.2.2.2 hsep (by ring_nf; rfl)
    have hk : (k:ℝ)+1 ≤ (Nat.log 2 (n+1):ℝ)+2 := by
      have h := Nat.log_mono_right (Nat.succ_le_succ (Nat.div_le_self n D)) (b:=2)
      change Nat.log 2 (n/D+1) ≤ Nat.log 2 (n+1) at h
      dsimp [k]; push_cast; exact_mod_cast (by omega : Nat.log 2 (n/D+1)+1+1 ≤ Nat.log 2 (n+1)+2)
    apply Real.le_sqrt_of_sq_le
    change ‖∑ a ∈ A, w a‖^2 ≤ budget
    apply raw.trans
    simp only [div_eq_mul_inv] at *
    apply save.trans
    dsimp [budget]
    gcongr
  rw [mangoldt_band_rows n U U P hPn t]
  change ‖∑ a ∈ Ioc U P, w a‖ ≤ _
  rw [dyadic_band_sum]
  exact (norm_sum_le _ _).trans ((sum_le_sum (fun i _ => block i)).trans_eq (by simp [budget]))


private noncomputable def fullBand (P : BandParams) (m : ℕ) : ℝ :=
  if m ≤ P.top then band P.mob P.lo P.hi ArithmeticFunction.vonMangoldt m else 0

private theorem full_band_eq_off_changes {N m : ℕ} (P Q : BandParams) (hmN : m ≤ N)
    (hout : m ∉ changes N P Q) : fullBand P m = fullBand Q m := by
  classical
  by_cases h0 : m=0
  · subst m
    simp [fullBand,band]
  have hm : m ∈ Ioc 0 N := mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h0,hmN⟩
  simp only [changes,mem_union,not_or] at hout
  obtain ⟨⟨⟨⟨ht,hu⟩,hl⟩,hb⟩,hp⟩ := hout
  have top : m ≤ P.top ↔ m ≤ Q.top := by simp only [mem_Ioc] at ht; omega
  unfold fullBand
  rw [if_congr top rfl rfl]
  by_cases hq : m ≤ Q.top
  · simp only [if_pos hq,band]
    have membership (a : ℕ) (ha : a ∈ m.divisors) :
        (P.lo < a ∧ a ≤ P.hi ∧ P.mob < m/a) ↔ (Q.lo < a ∧ a ≤ Q.hi ∧ Q.mob < m/a) := by
      have div := Nat.dvd_of_mem_divisors ha
      have lo := same_side hm hl div
      have hi := same_side hm hb div
      have mo := same_side hm hu (Nat.div_dvd_of_dvd div)
      omega
    rw [filter_congr membership]
    apply sum_congr rfl
    intro a ha
    have div := Nat.dvd_of_mem_divisors (mem_filter.mp ha).1
    have weights : lowMoebiusWeight P.mob a = lowMoebiusWeight Q.mob a := by
      unfold lowMoebiusWeight
      congr 1
      apply filter_congr
      intro d hd
      have h := same_side hm hu ((Nat.dvd_of_mem_divisors hd).trans div)
      omega
    rw [weights]
  · simp [hq]

private theorem full_band_frozen_l2 {N M : ℕ} (P Q : BandParams) {W : ℝ}
    (hp : ∀ m ≤ N, |fullBand P m| ≤ W) (hq : ∀ m ≤ N, |fullBand Q m| ≤ W)
    (small : M*(changes N P Q).card ≤ 5*N) :
    (M:ℝ)*(∑ m ∈ range (N+1), (fullBand P m-fullBand Q m)^2) ≤ 20*N*W^2 := by
  classical
  let ch := changes N P Q
  have step (m : ℕ) (hm : m ∈ range (N+1)) :
      (fullBand P m - fullBand Q m)^2 ≤ if m ∈ ch then 4*W^2 else 0 := by
    have mn : m ≤ N := Nat.le_of_lt_succ (mem_range.mp hm)
    split_ifs with hc
    · have h := (abs_sub _ _).trans (add_le_add (hp m mn) (hq m mn))
      have hh := pow_le_pow_left₀ (abs_nonneg _) h 2
      rw [sq_abs] at hh
      linarith only [hh]
    · rw [full_band_eq_off_changes P Q mn hc]
      simp
  have count : ((range (N+1)).filter (fun m => m ∈ ch)).card ≤ ch.card :=
    card_le_card (fun m hm => (mem_filter.mp hm).2)
  have sumBd := sum_le_sum step
  rw [←sum_filter,sum_const,nsmul_eq_mul] at sumBd
  have small' : (M:ℝ) * (ch.card:ℝ) ≤ 5*(N:ℝ) := by exact_mod_cast small
  have cmp : (M:ℝ) * (((range (N+1)).filter (fun m => m ∈ ch)).card:ℝ) ≤ M*(ch.card:ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast count) (Nat.cast_nonneg M)
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left sumBd (Nat.cast_nonneg M)
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right (cmp.trans small') (sq_nonneg W)]

private def bandView (third : Bool) (P : BandParams) : BandParams :=
  if third then ⟨P.top,P.mob,P.hi,P.primeLo,P.mob⟩ else ⟨P.top,P.mob,P.mob,P.lo,P.mob⟩

private theorem band_changes_subset (third : Bool) (N : ℕ) (P Q : BandParams) :
    changes N (bandView third P) (bandView third Q) ⊆ changes N P Q := by
  intro m hm
  cases third <;> simp only [changes,bandView,Bool.false_eq_true,ite_false,ite_true,mem_union] at * <;> tauto

private theorem mixed_band_freeze (third : Bool) (N M : ℕ) (P Q : BandParams) {W : ℝ}
    (hp : ∀ m ≤ N, |fullBand (bandView third P) m| ≤ W)
    (hq : ∀ m ≤ N, |fullBand (bandView third Q) m| ≤ W)
    (small : M*(changes N P Q).card ≤ 5*N) :
    (M:ℝ)*(∑ m ∈ range (N+1),
      (fullBand (bandView third P) m-fullBand (bandView third Q) m)^2) ≤ 20*N*W^2 := by
  apply full_band_frozen_l2 _ _ hp hq
  exact (Nat.mul_le_mul_left _ (card_le_card (band_changes_subset third N P Q))).trans small

private noncomputable def mixedParams (n : ℕ) : BandParams :=
  ⟨n,cutoffU n,cutoffL n,cutoffB n,⌊(n:ℝ)^(2/3:ℝ)⌋₊⟩

private theorem mixed_ordered {n m : ℕ} (h : n ≤ m) : Below (mixedParams n) (mixedParams m) := by
  refine ⟨h,?_,?_,?_,?_⟩ <;>
    exact Nat.floor_mono (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast h) (by norm_num))

private theorem mixed_positive {X : ℕ} (hx : 0 < X) : Below ⟨1,1,1,1,1⟩ (mixedParams X) := by
  have fr (e : ℝ) (he : 0 ≤ e) : 1 ≤ ⌊(X:ℝ)^e⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow (by exact_mod_cast hx) he)
  exact ⟨hx, fr _ (by norm_num), fr _ (by norm_num), fr _ (by norm_num), fr _ (by norm_num)⟩

private theorem actual_mixed_freeze (third : Bool) {N M X i j : ℕ}
    (hx : 0 < X) (hN : X ≤ N) (hi : X ≤ i) (hj : X ≤ j)
    (eq : label M (mixedParams X) (mixedParams i) = label M (mixedParams X) (mixedParams j))
    {W : ℝ} (hw : ∀ m ≤ N, |fullBand (bandView third (mixedParams i)) m| ≤ W)
    (hv : ∀ m ≤ N, |fullBand (bandView third (mixedParams j)) m| ≤ W) :
    (M:ℝ)*(∑ m ∈ range (N+1), (fullBand (bandView third (mixedParams i)) m -
      fullBand (bandView third (mixedParams j)) m)^2) ≤ 20*N*W^2 := by
  apply mixed_band_freeze _ _ _ _ _ hw hv
  apply changes_count (mixedParams X) _ _ (mixed_ordered hi) (mixed_ordered hj) (mixed_positive hx) hN
  rcases le_total i j with h|h
  · exact ordered_buckets (mixed_ordered h) eq
  · exact (ordered_buckets (mixed_ordered h) eq.symm).symm

private noncomputable def mixSpec (N : ℕ) (b : Bool) (i : ℕ) :=
  fourierSum N (fullBand (bandView b (mixedParams i)))

private theorem mix_mass (N : ℕ) (b : Bool) (i : ℕ) {W : ℝ}
    (h : ∀ m ≤ N, |fullBand (bandView b (mixedParams i)) m| ≤ W) :
    mass Set.univ (mixSpec N b i) ≤ ((N:ℝ)+1)*W^2 := by
  have hP := GoldbachTransitionFourier.continuous_parseval N (fullBand (bandView b (mixedParams i)))
  change mass Set.univ (fourierSum N _) ≤ _
  simp only [mass, Set.indicator_univ,unitMeasure,fourierSum,GoldbachTransitionSquare.phase,
    intervalIntegral.integral_of_le zero_le_one] at hP ⊢
  rw [hP]
  calc
    _ ≤ ∑ _m ∈ range (N+1), W^2 := sum_le_sum fun m hm => by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
        (h m (Nat.le_of_lt_succ (mem_range.mp hm))) 2
    _ = _ := by simp

private theorem mix_diff (b : Bool) {N M X i j : ℕ} (hM : 0 < M)
    (hx : 0 < X) (hN : X ≤ N) (hi : X ≤ i) (hj : X ≤ j)
    (eq : label M (mixedParams X) (mixedParams i) = label M (mixedParams X) (mixedParams j))
    {W : ℝ} (hw : ∀ m ≤ N, |fullBand (bandView b (mixedParams i)) m| ≤ W)
    (hv : ∀ m ≤ N, |fullBand (bandView b (mixedParams j)) m| ≤ W) :
    mass Set.univ (fun t => mixSpec N b i t - mixSpec N b j t) ≤ 20*N*W^2/M := by
  let v k m := fullBand (bandView b (mixedParams k)) m
  have sub : (fun t => mixSpec N b i t - mixSpec N b j t) =
      fourierSum N (fun m => v i m-v j m) := funext (fun t => (fourierSum_sub ..).symm)
  rw [sub,le_div_iff₀ (by exact_mod_cast hM : (0:ℝ)<M),mul_comm]
  have P := GoldbachTransitionFourier.continuous_parseval N (fun m => v i m-v j m)
  simp only [mass,Set.indicator_univ,unitMeasure,fourierSum,GoldbachTransitionSquare.phase,
    intervalIntegral.integral_of_le zero_le_one] at P ⊢
  rw [P]
  exact actual_mixed_freeze b hx hN hi hj eq hw hv

private theorem mix_clip_mass {T : ℝ} (hT : 0 < T) (u v : ℝ → ℂ)
    (hu : Continuous u) (hv : Continuous v) :
    mass Set.univ (fun t => clip T (u t)*v t) ≤ T^2*mass Set.univ v := by
  have hc := (clip_continuous hT).comp hu
  simp only [mass,Set.indicator_univ,←integral_const_mul]
  apply integral_mono (continuous_unit_integrable ((hc.mul hv).norm.pow 2))
    (continuous_unit_integrable (continuous_const.mul (hv.norm.pow 2)))
  intro t
  change ‖clip T (u t)*v t‖^2 ≤ T^2*‖v t‖^2
  rw [norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (clip_bounds hT _).1 2) (sq_nonneg _)

private noncomputable def mixVal (N i : ℕ) :=
  coefficient (deep i) (fun t => mixSpec N false i t * mixSpec N true i t) i

private noncomputable def mixCost (N M : ℕ) (W s : ℝ) :=
  2*s*(2*(20*N*W^2/M)) + s⁻¹*(2*(((N:ℝ)+1)*W^2))

private theorem mixed_cell (k M N j : ℕ) (hk : 32 ≤ k) (hM : 0 < M)
    (S : Finset ℕ) (hj : j ∈ S) (hN : octave k ≤ N)
    (hS : ∀ i ∈ S, octave k ≤ i ∧ i ≤ 8*octave k)
    (labels : ∀ i ∈ S, label M (mixedParams (octave k)) (mixedParams i) =
      label M (mixedParams (octave k)) (mixedParams j))
    {W T s : ℝ} (hT : 0 < T) (hs : 0 < s)
    (weights : ∀ b i, i ∈ S → ∀ m ≤ N, |fullBand (bandView b (mixedParams i)) m| ≤ W)
    (cap : ∀ i ∈ S, ∀ t ∈ Set.Ioc (0:ℝ) 1, t ∈ deep i → ‖mixSpec N false i t‖ ≤ T) :
    (∑ i ∈ S, ‖mixVal N i‖^2) ≤
    2*(S.card:ℝ)*(mixCost N M W s)^2 + 2*logCost k*T^2*(((N:ℝ)+1)*W^2) := by
  let g t := clip T (mixSpec N false j t)*mixSpec N true j t
  have cont (b : Bool) (i : ℕ) : Continuous (mixSpec N b i) := continuous_fourierSum ..
  have hg : Continuous g := ((clip_continuous hT).comp (cont false j)).mul (cont true j)
  have err i (hi : i ∈ S) :
      ‖mixVal N i - coefficient (deep i) g i‖ ≤ mixCost N M W s := by
    have df (b : Bool) := mix_diff b hM (show 0 < octave k by unfold octave; positivity)
      hN (hS i hi).1 (hS j hj).1 (labels i hi) (weights b i hi) (weights b j hj)
    apply (mixed_clipped_error (deep i) (wide_measurable .. |>.compl)
      _ _ _ _ (cont false i) (cont true i) (cont false j) (cont true j) i hT hs (cap i hi)).trans
    unfold mixCost
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith only [df false,df true]
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith only [mix_mass N true i (weights true i hi), mix_mass N false j (weights false j hj)]
  have bes := block_bessel k hk S hS g hg
  change _ ≤ logCost k * mass Set.univ g at bes
  have L : 0 ≤ logCost k := by unfold logCost; positivity
  have mg := (mix_clip_mass hT _ _ (cont false j) (cont true j)).trans
    (mul_le_mul_of_nonneg_left (mix_mass N true j (weights true j hj)) (sq_nonneg T))
  calc
    _ ≤ ∑ i ∈ S, 2*((mixCost N M W s)^2+‖coefficient (deep i) g i‖^2) := by
      apply sum_le_sum
      intro i hi
      exact (sq_triangle ..).trans (by gcongr; exact err i hi)
    _ = 2*((S.card:ℝ)*(mixCost N M W s)^2 + ∑ i ∈ S, ‖coefficient (deep i) g i‖^2) := by
      rw [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      change mass Set.univ g ≤ _ at mg
      nlinarith only [bes.trans (mul_le_mul_of_nonneg_left mg L)]

private theorem mixed_label {M X n : ℕ} (hx : 0<X) (hn : n ≤ 8*X) :
    label M (mixedParams X) (mixedParams n) ≤ 80*M := by
  have ratio (A b : ℕ) (ha : 0<A) (hb : b≤16*A) : bucket M A b ≤ 16*M := by
    have bound : M*b ≤ (16*M)*A := (Nat.mul_le_mul_left M hb).trans_eq (by ring)
    exact (Nat.div_le_div_right bound).trans_eq (Nat.mul_div_cancel _ ha)
  obtain ⟨hp,hu,hl,hb,hs⟩ := mixed_positive hx
  have top := ratio _ _ hp (show n ≤ 16*X by omega)
  have u := ratio _ _ hu (root_comparison hx hn (by norm_num : (0:ℝ)≤1/16) (by norm_num))
  have l := ratio _ _ hl (root_comparison hx hn (by norm_num : (0:ℝ)≤1/4) (by norm_num))
  have b := ratio _ _ hb (root_comparison hx hn (by norm_num : (0:ℝ)≤1/3) (by norm_num))
  have sq := root_comparison hx hn (by norm_num : (0:ℝ)≤2/3) (by norm_num : (2/3:ℝ)≤1)
  have p := ratio _ _ hs sq
  change bucket M X n + bucket M (cutoffU X) (cutoffU n) + bucket M (cutoffL X) (cutoffL n) +
    bucket M (cutoffB X) (cutoffB n) + bucket M ⌊(X:ℝ)^(2/3:ℝ)⌋₊ ⌊(n:ℝ)^(2/3:ℝ)⌋₊ ≤ _
  dsimp [mixedParams,cutoffU,cutoffL,cutoffB] at top u l b p ⊢
  omega

private theorem mixed_classes (k M : ℕ) (hk : 32 ≤ k) (hM : 0<M) (S : Finset ℕ)
    (hS : ∀ i ∈ S, octave k ≤ i ∧ i ≤ 8*octave k)
    (T W s : ℝ) (hT : 0<T) (hs : 0<s)
    (hW : ∀ b i, i ∈ S → ∀ m ≤ 8*octave k, |fullBand (bandView b (mixedParams i)) m| ≤ W)
    (hcap : ∀ i ∈ S, ∀ t ∈ Set.Ioc (0:ℝ) 1, t ∈ deep i → ‖mixSpec (8*octave k) false i t‖ ≤ T) :
    (∑ i ∈ S, ‖mixVal (8*octave k) i‖^2) ≤
      2*(S.card:ℝ)*(mixCost (8*octave k) M W s)^2 +
      (80*(M:ℝ)+1)*(2*logCost k*T^2*((((8*octave k:ℕ):ℝ)+1)*W^2)) := by
  classical
  let key i := label M (mixedParams (octave k)) (mixedParams i)
  let B := range (80*M+1)
  let G j := S.filter (fun i => key i=j)
  let N := 8*octave k
  let err := (mixCost N M W s)^2
  let cost := 2*logCost k*T^2*(((N:ℝ)+1)*W^2)
  have Xpos : 0 < octave k := by unfold octave; positivity
  have maps : ∀ i ∈ S, key i ∈ B := fun i hi => mem_range.mpr
    (Nat.lt_succ_of_le (mixed_label Xpos (hS i hi).2))
  have each j : (∑ i ∈ G j, ‖mixVal (8*octave k) i‖^2) ≤ 2*((G j).card:ℝ)*err + cost := by
    by_cases h : (G j).Nonempty
    · obtain ⟨a,ha⟩ := h
      have ha' := (mem_filter.mp ha).1
      apply mixed_cell k M N a hk hM (G j) ha (by dsimp [N]; omega)
        (fun i hi => hS i (mem_filter.mp hi).1) _ hT hs
        (fun b i hi => hW b i (mem_filter.mp hi).1) (fun i hi => hcap i (mem_filter.mp hi).1)
      intro i hi
      exact (mem_filter.mp hi).2.trans (mem_filter.mp ha).2.symm
    · have empty := not_nonempty_iff_eq_empty.mp h
      simp only [empty,sum_empty,card_empty,Nat.cast_zero,mul_zero,zero_mul,zero_add]
      dsimp [cost,logCost]
      positivity
  have total : (∑ j ∈ B, ((G j).card:ℝ)) = (S.card:ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise (s:=S) (t:=B) (f:=key) maps).symm
  calc
    _ = ∑ j ∈ B, ∑ i ∈ G j, ‖mixVal (8*octave k) i‖^2 := (sum_fiberwise_of_maps_to maps _).symm
    _ ≤ ∑ j ∈ B, (2*((G j).card:ℝ)*err+cost) := sum_le_sum (fun j _ => each j)
    _ = _ := by
      rw [sum_add_distrib,←sum_mul,←mul_sum,total,sum_const,nsmul_eq_mul]
      simp [err,cost,N,B]


private theorem mixed_weight_bound : ∃ D : ℝ, 1 ≤ D ∧ ∀ N : ℕ, 0<N →
    ∀ P : BandParams, ∀ m ≤ N, |fullBand P m| ≤ D*(scale N)^3 := by
  obtain ⟨C,hC,h⟩ := fine_divisor_envelope
  refine ⟨3072*C^2,by nlinarith [sq_nonneg (C-1)],?_⟩
  intro N hN P m hm
  unfold fullBand
  split_ifs
  · have H := band_uniform_bound N P.mob P.lo P.hi m hm hN (h N)
      (fun b => (le_of_eq (abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n:=b)))))
    have lg : Real.log (N:ℝ) ≤ 3072*scale N :=
      (Real.log_le_rpow_div (x:=(N:ℝ)) (Nat.cast_nonneg N) (by norm_num : (0:ℝ)<1/3072)).trans_eq
        (by unfold scale; ring)
    exact H.trans ((mul_le_mul_of_nonneg_left lg (sq_nonneg (C*scale N))).trans_eq (by ring))
  · rw [abs_zero]; have hz := scale_one hN; positivity

private theorem mixed_spec_actual (b : Bool) {i N : ℕ} (hi : i ≤ N) :
    mixSpec N b i = fourierSum i (band (cutoffU i)
      (if b then cutoffB i else cutoffU i)
      (if b then ⌊(i:ℝ)^(2/3:ℝ)⌋₊ else cutoffL i) ArithmeticFunction.vonMangoldt) := by
  funext t
  unfold mixSpec fourierSum
  rw [←sum_subset (s₁:=range (i+1)) (s₂:=range (N+1)) (range_mono (Nat.succ_le_succ hi)) (by
    intro m hm ho
    have h : ¬m ≤ i := by simpa only [mem_range,Nat.lt_succ_iff] using ho
    cases b <;> simp [fullBand,bandView,mixedParams,h])]
  apply sum_congr rfl
  intro m hm
  have h := Nat.le_of_lt_succ (mem_range.mp hm)
  cases b <;> simp [fullBand,bandView,mixedParams,h]

private theorem mixed_log_est (n : ℕ) (hn : 2 ≤ n) : (Nat.log 2 (n + 2) : ℝ) ≤ 4 * Real.log n := by
  have hb := Real.natLog_le_logb (n + 2) 2
  rw [Real.logb] at hb
  push_cast at hb
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hx : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have square : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) (show 0 ≤ (n : ℝ) + 1 by positivity)]
  have logarithm := Real.log_le_log (by positivity : 0 < (n : ℝ) + 2) square
  rw [Real.log_pow] at logarithm
  norm_num at logarithm
  have divided := (le_div_iff₀ (by linarith : 0 < Real.log 2)).mp hb
  have multiplied := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (Nat.log 2 (n + 2)) : (0 : ℝ) ≤ _)
  linarith only [logarithm, divided, multiplied]


private theorem mixed_uniform_cap : ∃ K : ℝ, 0<K ∧ ∀ i N : ℕ, 2 ≤ i → i ≤ N →
    ∀ t ∈ Set.Ioc (0:ℝ) 1, t ∈ deep i → ‖mixSpec N false i t‖^2 ≤ K*(scale N)^5960 := by
  obtain ⟨C,hC,cap⟩ := first_band_cap
  let A := 8*(18+96*Real.pi)*C^2
  refine ⟨13000^4*3072^2*A, by dsimp [A]; positivity, ?_⟩
  intro i N hi hiN t ht hd
  let z := scale N
  have hz : 1 ≤ z := scale_one (by omega)
  have hreal : (1:ℝ) ≤ i := by exact_mod_cast (show 1 ≤ i by omega)
  have hPB : cutoffL i ≤ cutoffB i := Nat.floor_mono
    (Real.rpow_le_rpow_of_exponent_le hreal (by norm_num))
  have hPn : cutoffL i ≤ i := Nat.floor_le_of_le <|
    (Real.rpow_le_rpow_of_exponent_le hreal (show (1/4:ℝ) ≤ 1 by norm_num)).trans_eq (Real.rpow_one _)
  have raw := cap i (cutoffL i) (cutoffB i) (by omega) hPB hPn t ⟨ht.1.le,ht.2⟩ hd
  rw [mixed_spec_actual false hiN]
  simp only [Bool.false_eq_true,ite_false]
  have lN : Real.log (i:ℝ) ≤ 3072*z := (Real.log_le_log (by positivity) (by exact_mod_cast hiN)).trans
    ((Real.log_le_rpow_div (x:=(N:ℝ)) (Nat.cast_nonneg _) (by norm_num : (0:ℝ)<1/3072)).trans_eq
      (by dsimp [z,scale]; ring))
  have hlg := mixed_log_est i hi
  have lg₁ : (Nat.log 2 (cutoffL i):ℝ) ≤ Nat.log 2 (i+2) := by exact_mod_cast Nat.log_mono_right (hPn.trans (by omega : i ≤ i+2))
  have lg₂ : (Nat.log 2 (i+1):ℝ) ≤ Nat.log 2 (i+2) := by exact_mod_cast Nat.log_mono_right (by omega : i+1 ≤ i+2)
  have h₁ : ((Nat.log 2 (cutoffL i)+1:ℕ):ℝ) ≤ 13000*z := by push_cast; linarith
  have h₂ : (Nat.log 2 (i+1):ℝ)+2 ≤ 13000*z := by linarith
  have hm : (i:ℝ)^(1/3072:ℝ) ≤ z := Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hiN) (by norm_num)
  have h := pow_le_pow_left₀ (norm_nonneg _) raw 2
  rw [mul_pow,Real.sq_sqrt (by positivity)] at h
  apply h.trans
  calc
    _ ≤ (13000*z)^2*(A*(13000*z)^2*(3072*z)^2*z^5954) := by dsimp [A]; gcongr
    _ = _ := by dsimp [z]; ring

private theorem mix_cost_scale {N : ℕ} (hn : 0<N) (C : ℝ) :
    let z := scale N
    mixCost N ⌈z^96⌉₊ (C*z^3) (z^48) ≤ 88*C^2*z^3030 := by
  intro z
  have a := cost_bound hn C
  change freezeCost N ⌈z^96⌉₊ (C*z^3) (z^48) ≤ _ at a
  have hz : 0<z := zero_lt_one.trans_le (scale_one hn)
  have extra : 0 ≤ (z^48)⁻¹*(2*((N:ℝ)+1)*(C*z^3)^2) := by positivity
  unfold mixCost
  unfold freezeCost at a
  linarith only [a,extra]

set_option maxRecDepth 16000 in
private theorem aggregate_powers {z C K L : ℝ} (hz : 1 ≤ z) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    2*(2*z^3072)*(88*C^2*z^3030)^2 +
      (161*z^96)*(2*(L*z^4)*(K*z^5960)*((2*z^3072)*(C*z^3)^2)) ≤
      (4*(88*C^2)^2+644*L*K*C^2)*z^9138 := by
  calc
    _ = 4*(88*C^2)^2*z^9132 + (644*L*K*C^2)*z^9138 := by ring
    _ ≤ 4*(88*C^2)^2*z^9138 + (644*L*K*C^2)*z^9138 := by
      have hp : z^(9132:ℕ) ≤ z^(9138:ℕ) := pow_le_pow_right₀ hz (by decide)
      exact add_le_add (mul_le_mul_of_nonneg_left hp (by positivity)) le_rfl
    _ = _ := (add_mul _ _ _).symm

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1800000 in
private theorem mixed_octave : ∃ Ctotal : ℝ, 0<Ctotal ∧ ∀ k : ℕ, 32 ≤ k →
    ∀ S : Finset ℕ, (∀ i ∈ S, octave k ≤ i ∧ i ≤ 8*octave k) →
    (∑ i ∈ S, ‖mixVal i i‖^2) ≤ Ctotal*((8*octave k:ℕ):ℝ)^(1523/512:ℝ) := by
  obtain ⟨C,hC,weight⟩ := mixed_weight_bound
  obtain ⟨K,hK,cap⟩ := mixed_uniform_cap
  have L : 0<logConstant := by norm_num [logConstant]
  refine ⟨4*(88*C^2)^2+644*logConstant*K*C^2,by positivity,?_⟩
  intro k hk S hS
  let N := 8*octave k
  let z := scale N
  let M := ⌈z^96⌉₊
  let T := Real.sqrt (K*z^5960)
  have Npos : 0<N := by dsimp [N,octave]; positivity
  have hz : 1≤z := scale_one Npos
  have zpos : 0<z := zero_lt_one.trans_le hz
  have hM : 0<M := Nat.ceil_pos.mpr (pow_pos zpos _)
  have hT : 0<T := Real.sqrt_pos.mpr (by positivity)
  have hT2 : T^2 = K*z^5960 := Real.sq_sqrt (by positivity)
  have eqN : z^3072 = N := scale_exact N
  have plus : (N:ℝ)+1 ≤ 2*z^3072 := by
    rw [eqN]
    have h : (1:ℝ)≤N := by exact_mod_cast Npos
    linarith
  have labelBd : 80*(M:ℝ)+1 ≤ 161*z^96 := by
    have hm := Nat.ceil_lt_add_one (show 0≤z^96 by positivity)
    change (M:ℝ) < _ at hm
    linarith [one_le_pow₀ hz (n:=96)]
  have Nbd i (hi : i∈S) : i≤N := (hS i hi).2
  have two i (hi : i∈S) : 2 ≤ i := by
    have one : 1≤3*k := by omega
    have base := Nat.pow_le_pow_right (by decide : 1≤2) one
    rw [pow_one,←octave_eq] at base
    exact base.trans (hS i hi).1
  have cut i (hi : i∈S) (t : ℝ) (ht : t∈Set.Ioc (0:ℝ) 1) (hd : t∈deep i) :
      ‖mixSpec N false i t‖ ≤ T := by
    exact Real.le_sqrt_of_sq_le (cap i N (two i hi) (Nbd i hi) t ht hd)
  have main := mixed_classes k M hk hM S hS T (C*z^3) (z^48) hT (pow_pos zpos _)
    (fun b i _ m hm => weight N Npos _ m hm) cut
  change _ ≤ 2*(S.card:ℝ)*_ + (80*(M:ℝ)+1)*(2*logCost k*T^2*(((N:ℝ)+1)*(C*z^3)^2)) at main
  have card : (S.card:ℝ) ≤ 2*z^3072 := by
    have sub : S ⊆ range (N+1) := fun i hi => mem_range.mpr (Nat.lt_succ_of_le (Nbd i hi))
    have h := card_le_card sub
    rw [card_range] at h
    exact (show (S.card:ℝ) ≤ (N:ℝ)+1 by exact_mod_cast h).trans plus
  have cost := mix_cost_scale Npos C
  change mixCost N M (C*z^3) (z^48) ≤ _ at cost
  have free0 : 0 ≤ mixCost N M (C*z^3) (z^48) := by unfold mixCost; positivity
  have lc : 0≤logCost k := by unfold logCost; positivity
  have main' : (∑ i ∈ S, ‖mixVal N i‖^2) ≤
      2*(2*z^3072)*(88*C^2*z^3030)^2 +
        (161*z^96)*(2*(logConstant*z^4)*(K*z^5960)*((2*z^3072)*(C*z^3)^2)) := by
    apply main.trans
    rw [hT2]
    gcongr
    · exact block_log_cost k

  have idval i (hi : i∈S) : ‖mixVal i i‖^2 = ‖mixVal N i‖^2 := by
    unfold mixVal
    simp only [mixed_spec_actual _ (Nbd i hi),mixed_spec_actual _ (le_refl i)]
  rw [sum_congr rfl idval]
  apply main'.trans
  have exp : z^9138 = (N:ℝ)^(1523/512:ℝ) := (scale_power N 9138).trans (by norm_num)
  change _ ≤ _ * (N:ℝ)^(1523/512:ℝ)
  rw [←exp]
  exact aggregate_powers hz hK.le L.le

private theorem mixed_window : ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 2^96 ≤ X →
    (∑ n ∈ Icc X (2*X), ‖mixVal n n‖^2) ≤ C*(X:ℝ)^(1523/512:ℝ) := by
  obtain ⟨K,hK,block⟩ := mixed_octave
  let α : ℝ := 1523/512
  have hα : 0 ≤ α := by norm_num [α]
  refine ⟨K*((8:ℝ)^α+(16:ℝ)^α), by positivity,?_⟩
  intro X hX
  have hXpos : 0<X := lt_of_lt_of_le (by decide : 0<(2^96:ℕ)) hX
  let k := Nat.log 8 X
  have oct (r : ℕ) : octave r = 8^r := by
    rw [octave_eq, pow_mul]; rfl
  have hk : 32 ≤ k := (Nat.le_log_iff_pow_le (by decide) hXpos.ne').mpr (by exact hX)
  have hlo : octave k ≤ X := by rw [oct]; exact Nat.pow_log_le_self _ hXpos.ne'
  have hhi : X < 8*octave k := by
    simpa [oct,k,pow_succ,mul_comm] using (Nat.lt_pow_succ_log_self (by decide : 1<8) X)
  let S := Icc X (2*X)
  let A := S.filter (fun i => i ≤ 8*octave k)
  let B := S.filter (fun i => ¬i ≤ 8*octave k)
  have transfer (j : ℕ) (hj : 32 ≤ j) (T : Finset ℕ) (c : ℕ)
      (hT : ∀ i∈T, octave j ≤ i ∧ i ≤ 8*octave j) (hs : 8*octave j ≤ c*X) :
      (∑ i∈T, ‖mixVal i i‖^2) ≤ K*(c:ℝ)^α*(X:ℝ)^α := by
    refine (block j hj T hT).trans ?_
    have hp := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (8*octave j:ℕ))
      (show ((8*octave j:ℕ):ℝ) ≤ (c:ℝ)*X by exact_mod_cast hs) hα
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _) ] at hp
    simpa [mul_assoc,α] using (mul_le_mul_of_nonneg_left hp hK.le)
  have hA : (∑ i∈A, ‖mixVal i i‖^2) ≤ K*(8:ℝ)^α*(X:ℝ)^α := by
    apply transfer k hk A 8 _ (Nat.mul_le_mul_left 8 hlo)
    intro i hi
    obtain ⟨hs, hb⟩ := mem_filter.mp hi
    exact ⟨hlo.trans (mem_Icc.mp hs).1,hb⟩
  have hB : (∑ i∈B, ‖mixVal i i‖^2) ≤ K*(16:ℝ)^α*(X:ℝ)^α := by
    rcases B.eq_empty_or_nonempty with h | ⟨i,hi⟩
    · rw [h,sum_empty]; positivity
    obtain ⟨hmem,habove⟩ := mem_filter.mp hi
    have hscale : 8*octave (k+1) ≤ 16*X := by
      rw [octave_succ]
      have := (mem_Icc.mp hmem).2
      omega
    apply transfer (k+1) (by omega) B 16 _ hscale
    intro j hj
    obtain ⟨hs,ha⟩ := mem_filter.mp hj
    rw [octave_succ]
    have := (mem_Icc.mp hs).2
    omega
  change (∑ n∈S, ‖mixVal n n‖^2) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not S (fun i => i ≤ 8*octave k)]
  exact (add_le_add hA hB).trans_eq (by ring)

private theorem mean_le_block (f : ℕ → ℂ) (n : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.range (n+1), (‖f (n+2*j)‖ / (n+2*j : ℕ))^2) / (n+1 : ℕ) ≤
    ((∑ k ∈ Finset.Icc n (2*n), ‖f k‖^2) +
      (∑ k ∈ Finset.Icc (2*n) (4*n), ‖f k‖^2)) / (n:ℝ)^3 := by
  classical
  let I := Finset.range (n+1)
  let A := Finset.Icc n (2*n)
  let B := Finset.Icc (2*n) (4*n)
  let E := fun k => ‖f k‖^2
  have pos : (0:ℝ) < n := by exact_mod_cast hn
  have sumE : (∑ j ∈ I, E (n+2*j)) ≤ (∑ k ∈ A, E k) + ∑ k ∈ B, E k := by
    calc
      _ = ∑ k ∈ I.image (fun j => n+2*j), E k := by
        rw [Finset.sum_image]; intro a _ b _ hab; dsimp at hab; omega
      _ ≤ ∑ k ∈ A ∪ B, E k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
          have hj' : j < n+1 := Finset.mem_range.mp hj
          simp only [A,B,Finset.mem_union,Finset.mem_Icc]
          omega
        · intros; exact sq_nonneg _
      _ ≤ _ := by
        rw [← Finset.sum_union_inter]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have indiv (j : ℕ) : (‖f (n+2*j)‖ / (n+2*j : ℕ))^2 ≤ E (n+2*j) / (n:ℝ)^2 := by
    rw [div_pow]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    have h : (n:ℝ) ≤ (↑(n+2*j : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right n (2*j)
    gcongr
  have hsum := Finset.sum_le_sum (s := I) fun j _ => indiv j
  rw [← Finset.sum_div] at hsum
  have hnn : (0:ℝ) < ↑(n+1 : ℕ) := by positivity
  apply (div_le_iff₀ hnn).mpr
  calc
    _ ≤ _ := hsum
    _ ≤ ((∑ k ∈ A, E k) + ∑ k ∈ B, E k) / (n:ℝ)^2 := by gcongr
    _ ≤ _ := by
      change _ ≤ ((∑ k ∈ A, E k) + ∑ k ∈ B, E k) / (n:ℝ)^3 * ↑(n+1 : ℕ)
      field_simp
      push_cast
      have hE : 0 ≤ (∑ k ∈ A, E k) + ∑ k ∈ B, E k :=
        by exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      nlinarith [mul_nonneg hE (sq_nonneg (n:ℝ))]

private noncomputable def actualValue (n : ℕ) :=
  pairIntegral (deep n) n (band (cutoffU n) (cutoffU n) (cutoffL n) ArithmeticFunction.vonMangoldt)
    (band (cutoffU n) (cutoffB n) ⌊(n:ℝ)^(2/3:ℝ)⌋₊ ArithmeticFunction.vonMangoldt)

private theorem val_correct (n : ℕ) : actualValue n = mixVal n n := by
  unfold actualValue mixVal
  rw [mixed_spec_actual false (le_refl n),mixed_spec_actual true (le_refl n)]
  unfold pairIntegral coefficient
  rw [intervalIntegral.integral_of_le zero_le_one]
  rfl

open Filter Topology

private theorem mean_result (ε : ℝ) (he : 0<ε) :
    ∃ N : ℕ, ∀ n ≥ N, (∑ j ∈ range (n+1), (‖actualValue (n+2*j)‖ / (n+2*j : ℕ))^2) /
      (n+1 : ℕ) ≤ ε := by
  obtain ⟨C,hC,mom⟩ := mixed_window
  let α : ℝ := 1523/512
  let D := C*(1+(2:ℝ)^α)
  have lim : Tendsto (fun n : ℕ => D*(n:ℝ)^(-(13/512:ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<13/512)).comp
      tendsto_natCast_atTop_atTop |>.const_mul D
  obtain ⟨N,hN⟩ := eventually_atTop.mp (lim.eventually_le_const he)
  refine ⟨max N (2^96),fun n hn => ?_⟩
  have hn1 := (le_max_right N (2^96)).trans hn
  have hp : 0<n := lt_of_lt_of_le (by decide : 0<(2^96:ℕ)) hn1
  have h2 := mom (2*n) (hn1.trans (by omega))
  have h := mom n hn1
  simp only [←val_correct] at h h2
  rw [show 2*(2*n) = 4*n by ring] at h2
  have powN : ((2*n:ℕ):ℝ)^α = (2:ℝ)^α*(n:ℝ)^α := by
    push_cast; exact Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg n)
  apply (mean_le_block actualValue n hp).trans
  calc
    _ ≤ (C*(n:ℝ)^α+C*((2*n:ℕ):ℝ)^α)/(n:ℝ)^3 := by gcongr
    _ = D*(n:ℝ)^(-(13/512:ℝ)) := by
      rw [powN,show C*(n:ℝ)^α+C*((2:ℝ)^α*(n:ℝ)^α) = D*(n:ℝ)^α by dsimp [D];ring,
        mul_div_assoc,←Real.rpow_natCast (n:ℝ) 3,←Real.rpow_sub (by exact_mod_cast hp)]
      norm_num [α]
    _ ≤ ε := hN n ((le_max_left _ _).trans hn)

theorem Conjectures.Cuts.Task126814ce5d235509c8f080c5 : (have x1 : ℕ → ℝ → ℕ := fun (x1 : ℕ) (x2 : ℝ) => ⌊(↑x1 : ℝ) ^ x2⌋₊; have x2 : ℕ → ℕ := fun (x2 : ℕ) => x1 x2 (1 / 16 : ℝ); have x3 : ℝ → ℂ := fun (x3 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x3) : ℂ) * Complex.I); have x4 : ℕ → ℕ → ℕ → ℕ → ℝ := fun (x4 x5 x6 x7 : ℕ) => ∑ x8 ∈ x7.divisors with x5 < x8 ∧ x8 ≤ x6 ∧ x2 x4 < x7 / x8, (∑ x9 ∈ x8.divisors with x2 x4 < x9, (↑((ArithmeticFunction.moebius : ℕ → ℤ) x9) : ℝ)) * (ArithmeticFunction.vonMangoldt : ℕ → ℝ) (x7 / x8); have x5 : ℕ → ℕ → ℕ → ℝ → ℂ := fun (x5 x6 x7 : ℕ) (x8 : ℝ) => ∑ x9 ∈ Finset.range (x5 + (1 : ℕ)), (↑(x4 x5 x6 x7 x9) : ℂ) * x3 ((↑x9 : ℝ) * x8); have x6 : ℕ → Set ℝ := fun (x6 : ℕ) => {x7 : ℝ | ∃ (x8 : ℕ) (x9 : ℕ), (1 : ℕ) ≤ x8 ∧ x8 ≤ x1 x6 (1 / 3 : ℝ) ∧ x9 ≤ x8 ∧ x9.Coprime x8 ∧ |x7 - (↑x9 : ℝ) / (↑x8 : ℝ)| ≤ (↑((256 : ℕ) * x1 x6 (1 / 3 : ℝ) * Nat.log (2 : ℕ) (x6 + (2 : ℕ)) ^ (2 : ℕ)) : ℝ) / ((↑x8 : ℝ) * (↑x6 : ℝ))}; have x7 : ℕ → ℂ := fun (x7 : ℕ) => ∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (x6 x7)ᶜ.indicator (fun (x9 : ℝ) => x5 x7 (x2 x7) (x1 x7 (1 / 4 : ℝ)) x9 * x5 x7 (x1 x7 (1 / 3 : ℝ)) (x1 x7 (2 / 3 : ℝ)) x9 * x3 (-(↑x7 : ℝ) * x9)) x8; have x8 : ℕ → ℝ := fun (x8 : ℕ) => (‖x7 x8‖ / (↑x8 : ℝ)) ^ (2 : ℕ); have x9 : ℕ → ℕ → ℝ := fun (x9 x10 : ℕ) => (∑ x11 ∈ Finset.range (x10 + (1 : ℕ)), x8 (x9 + (2 : ℕ) * x11)) / (↑(x10 + (1 : ℕ)) : ℝ); ∀ (x10 : ℝ), (0 : ℝ) < x10 → ∃ (x12 : ℕ), ∀ (x13 : ℕ), x12 ≤ x13 → Even x13 → x9 x13 x13 ≤ x10) := by
  dsimp only
  intro ε he
  obtain ⟨N,hN⟩ := mean_result ε he
  exact ⟨N,fun n hn _ => hN n hn⟩
