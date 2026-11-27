import Mathlib
import Conjectures.TwinPrimes.CofactorTwoLinearSieve

open scoped BigOperators
open Conjectures.TwinPrimes.CofactorTwoLinearSieve_aux

/-
Adapted from the accepted module Conjectures.TwinPrimes.CofactorTwoLinearSieve
(lemma L-twin-primes-cofactor-two-linear-sieve): the primorial sifted-set bound below
reuses its Selberg upper sieve steps for the two forms s and r*s-2.
-/

private lemma cofactor_primorial_bound (Y r y : ℕ) (hY : 3 ≤ Y) (hrp : r.Prime) (hr2 : 2 < r)
    (hy : 2 ≤ y)
    (hlog : Real.log (Y:ℝ) ≤ 32 * Real.log ((y:ℝ)+1))
    (herr : (((y^8:ℕ):ℝ)^2*(1+Real.log ((y^8:ℕ):ℝ))^4 + 2*(y:ℝ)) * (Real.log (Y:ℝ))^2 ≤ 18*(Y:ℝ)) :
    ((((Finset.Ioc Y (2*Y)).filter (fun s => (primorial y).Coprime (s*(r*s-2)))).card : ℕ) : ℝ) ≤
      8210*(Y:ℝ)/(Real.log (Y:ℝ))^2 := by
  have hY1 : 1 ≤ Y := by omega
  have hr2le : 2 ≤ r := by omega
  have hro : Odd r := hrp.odd_of_ne_two (by omega)
  have hzpos : 1 ≤ y^8 := Nat.one_le_pow _ _ (by omega)
  have hlogYpos : 0 < Real.log (Y:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hsing := singular_two_mul_le r hrp hr2
  have hone := CentralSelberg.singular_one_le (2*r)
  have hEu := CentralSelberg.euler_mass (2*r) y ⟨r, rfl⟩ (by omega)
  have hcut := CentralSelberg.retained (2*r) y ⟨r, rfl⟩ hy
  change _ ≤ 2 * CentralSelberg.singular (2*r) * CentralSelberg.mass (2*r) y at hEu
  change CentralSelberg.mass (2*r) y ≤
    2 * OAI.Problem337.GoldbachSelberg.denominator (2*r) (primorial y) (y^8) at hcut
  have h1 : (Real.log ((y:ℝ)+1))^2 ≤
      4 * CentralSelberg.singular (2*r) *
        OAI.Problem337.GoldbachSelberg.denominator (2*r) (primorial y) (y^8) := by
    calc _ ≤ 2*CentralSelberg.singular (2*r)*CentralSelberg.mass (2*r) y := hEu
      _ ≤ 2*CentralSelberg.singular (2*r)*(2*OAI.Problem337.GoldbachSelberg.denominator (2*r)
            (primorial y) (y^8)) := by
          apply mul_le_mul_of_nonneg_left hcut
          nlinarith [hone]
      _ = _ := by ring
  have hDpos : 0 < OAI.Problem337.GoldbachSelberg.denominator (2*r) (primorial y) (y^8) :=
    cof_denominator_pos Y r _ (squarefree_primorial y) hzpos
  have h2 : (Real.log ((y:ℝ)+1))^2 ≤
      8 * OAI.Problem337.GoldbachSelberg.denominator (2*r) (primorial y) (y^8) := by
    calc _ ≤ 4*CentralSelberg.singular (2*r)*OAI.Problem337.GoldbachSelberg.denominator (2*r)
          (primorial y) (y^8) := h1
      _ ≤ 4*2*OAI.Problem337.GoldbachSelberg.denominator (2*r) (primorial y) (y^8) := by
          apply mul_le_mul_of_nonneg_right _ hDpos.le
          nlinarith [hsing]
      _ = _ := by ring
  have hsq : (Real.log (Y:ℝ))^2 ≤ (32*Real.log ((y:ℝ)+1))^2 :=
    pow_le_pow_left₀ hlogYpos.le hlog 2
  have hDen : (Real.log (Y:ℝ))^2 ≤
      8192 * OAI.Problem337.GoldbachSelberg.denominator (2*r) (primorial y) (y^8) := by
    calc _ ≤ (32*Real.log ((y:ℝ)+1))^2 := hsq
      _ = 1024 * (Real.log ((y:ℝ)+1))^2 := by ring
      _ ≤ 1024 * (8*OAI.Problem337.GoldbachSelberg.denominator (2*r) (primorial y) (y^8)) := by
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = _ := by ring
  have hfirst : ((Y:ℝ)/OAI.Problem337.GoldbachSelberg.denominator (2*r) (primorial y) (y^8))*
      (Real.log (Y:ℝ))^2 ≤ 8192*(Y:ℝ) := by
    calc _ ≤ ((Y:ℝ)/OAI.Problem337.GoldbachSelberg.denominator (2*r) (primorial y) (y^8)) *
          (8192*OAI.Problem337.GoldbachSelberg.denominator (2*r) (primorial y) (y^8)) := by
          exact mul_le_mul_of_nonneg_left hDen (by positivity)
      _ = _ := by field_simp
  have herr2 : (((y^8:ℕ):ℝ)^2*(1+Real.log ((y^8:ℕ):ℝ))^4)*(Real.log (Y:ℝ))^2 ≤ 18*(Y:ℝ) := by
    have h0 : (0:ℝ) ≤ 2*(y:ℝ)*(Real.log (Y:ℝ))^2 := by positivity
    nlinarith [herr]
  have hmain := cof_card_le_sifted Y r (primorial y) hY1 hr2le hro (squarefree_primorial y) hzpos
  rw [le_div_iff₀ (pow_pos hlogYpos 2)]
  have hmul := mul_le_mul_of_nonneg_right hmain (sq_nonneg (Real.log (Y:ℝ)))
  calc _ ≤ ((Y:ℝ)/OAI.Problem337.GoldbachSelberg.denominator (2*r) (primorial y) (y^8) +
        (((y^8:ℕ):ℝ)^2*(1+Real.log ((y^8:ℕ):ℝ))^4)) * (Real.log (Y:ℝ))^2 := hmul
    _ = ((Y:ℝ)/OAI.Problem337.GoldbachSelberg.denominator (2*r) (primorial y) (y^8))*
          (Real.log (Y:ℝ))^2 +
        (((y^8:ℕ):ℝ)^2*(1+Real.log ((y^8:ℕ):ℝ))^4)*(Real.log (Y:ℝ))^2 := by ring
    _ ≤ 8192*(Y:ℝ) + 18*(Y:ℝ) := add_le_add hfirst herr2
    _ = 8210*(Y:ℝ) := by ring

theorem Conjectures.TwinPrimes.FirstFactorDoubledFifthBand :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ X : ℕ, N≤X → (∑ p ∈ (Finset.Ioo X (2*X)).filter (fun p => 50*p<51*X ∧ p.Prime ∧ Nat.nthRoot 5 X ≤ (p+2).minFac ∧ (p+2).minFac < 2*Nat.nthRoot 5 X), Real.log p * Real.log (p+2)) ≤ C*X/Real.log X := by
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp CentralSelberg.scales2
  refine ⟨8210 * 16 * 12 * Real.log 4, by positivity, max (max (X₀^2) (32^5)) 1024, ?_⟩
  intro X hX
  have hX0sq : X₀^2 ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hX32 : 32^5 ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hX1024 : 1024 ≤ X := (le_max_right _ _).trans hX
  set z0 := Nat.nthRoot 5 X
  have hz0pow : z0^5 ≤ X := Nat.pow_nthRoot_le (Or.inl (by norm_num))
  have hz0ge : 32 ≤ z0 := (Nat.le_nthRoot_iff (by norm_num)).mpr hX32
  have hz8 : 8 * z0 ≤ X := by
    have h1 : (8:ℕ) ≤ z0^4 := le_trans (by norm_num) (Nat.pow_le_pow_left hz0ge 4)
    calc 8 * z0 ≤ z0^4 * z0 := Nat.mul_le_mul_right z0 h1
      _ = z0^5 := by ring
      _ ≤ X := hz0pow
  set S := (Finset.Ioo X (2*X)).filter (fun p => 50*p<51*X ∧ p.Prime ∧ z0 ≤ (p+2).minFac ∧
      (p+2).minFac < 2*z0) with hS
  have hmemS : ∀ p, p ∈ S ↔ X < p ∧ p < 2*X ∧ 50*p<51*X ∧ p.Prime ∧ z0 ≤ (p+2).minFac ∧
      (p+2).minFac < 2*z0 := by
    intro p
    rw [hS]
    simp only [Finset.mem_filter, Finset.mem_Ioo, and_assoc]
  let R : Finset ℕ := (Finset.Icc z0 (2*z0 - 1)).filter (fun r => r.Prime)
  let y : ℕ → ℕ := fun Y => if h : X₀ ≤ Y then Classical.choose (hX₀ Y h) else 0
  let T : ℕ → Finset ℕ := fun r => (Finset.Ioc (X/r) (2*(X/r))).filter
      (fun s => (primorial (y (X/r))).Coprime (s*(r*s-2)))
  have hyspec : ∀ Y : ℕ, X₀ ≤ Y →
      2 ≤ y Y ∧ y Y ≤ Y ∧ Real.log (Y:ℝ) ≤ 32 * Real.log ((y Y:ℝ)+1) ∧
        ((((y Y)^8:ℕ):ℝ)^2*(1+Real.log (((y Y)^8:ℕ):ℝ))^4 + 2*(y Y:ℝ))*(Real.log (Y:ℝ))^2 ≤
          18*(Y:ℝ) := by
    intro Y hY
    have h := Classical.choose_spec (hX₀ Y hY)
    simpa [y, hY] using h
  have hYsq : ∀ r : ℕ, z0 ≤ r → r < 2*z0 → X ≤ (X/r)^2 := by
    intro r hz0r hr2z
    have hrpos : 0 < r := by omega
    have h16 : 16 * r^2 ≤ X := by
      have h1 : r * r < (2*z0) * (2*z0) := by nlinarith
      have h2 : 16 * r^2 < 64 * z0^2 := by nlinarith
      have h3 : 64 * z0^2 ≤ z0^5 := by
        have h4 : (64:ℕ) ≤ z0^3 := le_trans (by norm_num) (Nat.pow_le_pow_left hz0ge 3)
        calc 64 * z0^2 ≤ z0^3 * z0^2 := Nat.mul_le_mul_right (z0^2) h4
          _ = z0^5 := by ring
      omega
    have hXlt : X < (X/r + 1) * r := (Nat.div_lt_iff_lt_mul hrpos).mp (Nat.lt_succ_self _)
    have hYge : 16 * r ≤ X/r + 1 := by
      have : (16*r) * r < (X/r + 1) * r := lt_of_le_of_lt (by nlinarith) hXlt
      exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right this)
    have hY1 : 1 ≤ X/r := by omega
    by_contra hlt
    have hlt' : (X/r)^2 < X := Nat.lt_of_not_ge hlt
    have hsq : (X/r+1)^2 = (X/r)^2 + 2*(X/r) + 1 := by ring
    have hA : 16 * (X/r)^2 < (X/r+1)^2 := by
      calc 16 * (X/r)^2 < 16 * ((X/r+1)*r) := by nlinarith [lt_trans hlt' hXlt]
        _ = (X/r+1) * (16*r) := by ring
        _ ≤ (X/r+1) * (X/r+1) := Nat.mul_le_mul_left _ hYge
        _ = (X/r+1)^2 := by ring
    nlinarith
  have hX0le : ∀ r : ℕ, z0 ≤ r → r < 2*z0 → X₀ ≤ X/r := by
    intro r hz0r hr2z
    have hYs : X ≤ (X/r)^2 := hYsq r hz0r hr2z
    have hYpos : 1 ≤ X/r := by
      have hne : X/r ≠ 0 := by
        intro h0
        have hz : (X/r)^2 = 0 := by rw [h0]; ring
        omega
      exact Nat.pos_of_ne_zero hne
    by_contra hlt
    have h1 : (X/r)^2 < X₀^2 := by
      have h2 : X/r + 1 ≤ X₀ := by omega
      calc (X/r)^2 < (X/r+1)^2 := by nlinarith
        _ ≤ X₀^2 := Nat.pow_le_pow_left h2 2
    nlinarith
  have hY3 : ∀ r : ℕ, z0 ≤ r → r < 2*z0 → 3 ≤ X/r := by
    intro r hz0r hr2z
    have := hYsq r hz0r hr2z
    by_contra hlt
    have : (X/r)^2 < 1024 := by
      have : X/r ≤ 31 := by omega
      calc (X/r)^2 ≤ 31^2 := Nat.pow_le_pow_left this 2
        _ < 1024 := by norm_num
    nlinarith
  have hper : ∀ p ∈ S, Real.log (p:ℝ) * Real.log ((p:ℝ)+2) ≤ 4 * (Real.log (X:ℝ))^2 := by
    intro p hp
    obtain ⟨hXp, hp2X, -, -, -, -⟩ := (hmemS p).mp hp
    have hpX : (p:ℝ) ≤ (X:ℝ)^2 := by
      have h : p ≤ X * X := by nlinarith
      have h' : (p:ℝ) ≤ (X:ℝ) * (X:ℝ) := by exact_mod_cast h
      linarith
    have hp2X' : (p:ℝ) + 2 ≤ (X:ℝ)^2 := by
      have h : p + 2 ≤ X * X := by nlinarith
      have h' : ((p+2:ℕ):ℝ) ≤ (X:ℝ) * (X:ℝ) := by exact_mod_cast h
      have h'' : ((p+2:ℕ):ℝ) = (p:ℝ) + 2 := by push_cast; ring
      linarith
    have hlogp : Real.log (p:ℝ) ≤ 2 * Real.log (X:ℝ) := by
      have h := Real.log_le_log (by exact_mod_cast (by omega : 0 < p)) hpX
      rwa [Real.log_pow] at h
    have hlogp2 : Real.log ((p:ℝ)+2) ≤ 2 * Real.log (X:ℝ) := by
      have h := Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) p]) hp2X'
      rwa [Real.log_pow] at h
    have h1 : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
    have h2 : 0 ≤ Real.log ((p:ℝ)+2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) p])
    calc Real.log (p:ℝ) * Real.log ((p:ℝ)+2) ≤ (2*Real.log (X:ℝ)) * (2*Real.log (X:ℝ)) :=
          mul_le_mul hlogp hlogp2 h2 (by linarith)
      _ = 4 * (Real.log (X:ℝ))^2 := by ring
  have hinj : S.card ≤ (R.sigma T).card := by
    apply Finset.card_le_card_of_injOn (fun p => ⟨(p+2).minFac, (p+2)/(p+2).minFac⟩)
    · intro p hp
      rw [Finset.mem_coe] at hp
      obtain ⟨hXp, hp2X, h50, hpP, hzlo, hzhi⟩ := (hmemS p).mp hp
      show (⟨(p+2).minFac, (p+2)/(p+2).minFac⟩ : Σ _ : ℕ, ℕ) ∈ R.sigma T
      set r := (p+2).minFac
      have hrlo : z0 ≤ r := hzlo
      have hr2z : r < 2*z0 := hzhi
      have hrp : r.Prime := Nat.minFac_prime (by omega)
      have hrdvd : r ∣ p+2 := Nat.minFac_dvd _
      have hrs : r * ((p+2)/r) = p+2 := Nat.mul_div_cancel' hrdvd
      have hrpos : 0 < r := by omega
      have hpr : p + r < 2*X := by
        have hp100 : 100 * p < 102 * X := by omega
        have hz200 : 200 * z0 ≤ 25 * X := by
          have := Nat.mul_le_mul_left 25 hz8
          omega
        have hr100 : 100 * r < 200 * z0 := by omega
        omega
      rw [Finset.mem_sigma]
      refine ⟨?_, ?_⟩
      · simp only [R, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hrlo, by omega⟩, hrp⟩
      · simp only [T, Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · have hle : X/r ≤ (p+2)/r :=
            Nat.div_le_div_right (le_trans hXp.le (Nat.le_add_right p 2))
          have hne : (p+2)/r ≠ X/r := by
            intro heq
            have hmul : p + 2 = r * (X/r) := by rw [← hrs, heq]
            have hself : r * (X/r) ≤ X := by
              rw [Nat.mul_comm]
              exact Nat.div_mul_le_self X r
            omega
          exact lt_of_le_of_ne hle (Ne.symm hne)
        · have hY : X + 1 ≤ (X/r) * r + r := by
            have h1 := Nat.div_add_mod X r
            rw [Nat.mul_comm] at h1
            have h2 := Nat.mod_lt X hrpos
            omega
          have hlt : p + 2 < (2*(X/r) + 1) * r := by
            have : (2*(X/r) + 1) * r = 2 * ((X/r) * r) + r := by ring
            rw [this]
            omega
          have : (p+2)/r < 2*(X/r) + 1 := (Nat.div_lt_iff_lt_mul hrpos).mpr hlt
          omega
        · have hY0 : X₀ ≤ X/r := hX0le r hrlo hr2z
          obtain ⟨hy2, hyY, hylog, hyerr⟩ := hyspec (X/r) hY0
          have hyr : y (X/r) < r := by
            by_contra hge
            have hge' : r ≤ y (X/r) := Nat.le_of_not_lt hge
            have hlogY1 : (1:ℝ) ≤ Real.log ((X/r:ℕ):ℝ) := by
              have hY3r : (3:ℕ) ≤ X/r := hY3 r hrlo hr2z
              have hY3r' : (3:ℝ) ≤ ((X/r:ℕ):ℝ) := by exact_mod_cast hY3r
              have hpos : (0:ℝ) < ((X/r:ℕ):ℝ) := by linarith
              rw [Real.le_log_iff_exp_le hpos]
              linarith [Real.exp_one_lt_d9]
            have hlogyy : 0 ≤ Real.log (((y (X/r))^8:ℕ):ℝ) :=
              Real.log_nonneg (by exact_mod_cast (Nat.one_le_pow _ _ (by omega : 1 ≤ y (X/r))))
            have hP1 : (1:ℝ) ≤ (1 + Real.log (((y (X/r))^8:ℕ):ℝ))^4 := by
              have : (1:ℝ) ≤ 1 + Real.log (((y (X/r))^8:ℕ):ℝ) := by linarith
              calc (1:ℝ) = 1^4 := by ring
                _ ≤ _ := pow_le_pow_left₀ (by norm_num) this 4
            have hL1 : (1:ℝ) ≤ (Real.log ((X/r:ℕ):ℝ))^2 := by nlinarith
            have hyy16 : ((y (X/r):ℕ):ℝ)^16 ≤ 18 * ((X/r:ℕ):ℝ) := by
              calc ((y (X/r):ℕ):ℝ)^16 = (((y (X/r))^8:ℕ):ℝ)^2 * 1 := by push_cast; ring
                _ ≤ (((y (X/r))^8:ℕ):ℝ)^2 * ((1 + Real.log (((y (X/r))^8:ℕ):ℝ))^4 *
                      (Real.log ((X/r:ℕ):ℝ))^2) := by
                    apply mul_le_mul_of_nonneg_left _ (by positivity)
                    calc (1:ℝ) ≤ (1 + Real.log (((y (X/r))^8:ℕ):ℝ))^4 := hP1
                      _ ≤ (1 + Real.log (((y (X/r))^8:ℕ):ℝ))^4 *
                          (Real.log ((X/r:ℕ):ℝ))^2 :=
                          le_mul_of_one_le_right (by positivity) hL1
                _ = ((((y (X/r))^8:ℕ):ℝ)^2*(1+Real.log (((y (X/r))^8:ℕ):ℝ))^4)*
                      (Real.log ((X/r:ℕ):ℝ))^2 := by ring
                _ ≤ ((((y (X/r))^8:ℕ):ℝ)^2*(1+Real.log (((y (X/r))^8:ℕ):ℝ))^4 +
                      2*((y (X/r):ℕ):ℝ))*(Real.log ((X/r:ℕ):ℝ))^2 := by
                    have h0 : (0:ℝ) ≤ 2*((y (X/r):ℕ):ℝ)*(Real.log ((X/r:ℕ):ℝ))^2 := by positivity
                    nlinarith
                _ ≤ 18 * ((X/r:ℕ):ℝ) := hyerr
            have hyy16N : (y (X/r))^16 ≤ 18 * (X/r) := by exact_mod_cast hyy16
            have hr16 : r^16 ≤ 18 * (X/r) := le_trans (Nat.pow_le_pow_left hge' 16) hyy16N
            have hz17 : z0^17 ≤ 18 * X := by
              calc z0^17 = z0^16 * z0 := by ring
                _ ≤ r^16 * z0 := Nat.mul_le_mul_right z0 (Nat.pow_le_pow_left hrlo 16)
                _ ≤ (18 * (X/r)) * z0 := Nat.mul_le_mul_right z0 hr16
                _ = 18 * ((X/r) * z0) := by ring
                _ ≤ 18 * X := by
                    apply Nat.mul_le_mul_left 18
                    calc (X/r) * z0 ≤ (X/r) * r := Nat.mul_le_mul_left _ hrlo
                      _ ≤ X := Nat.div_mul_le_self X r
            have hXlt : X < (z0+1)^5 := Nat.lt_pow_nthRoot_add_one (by norm_num) X
            have h18 : 18 * X < 576 * z0^5 := by
              have : (z0+1)^5 ≤ 32 * z0^5 := by
                calc (z0+1)^5 ≤ (2*z0)^5 := Nat.pow_le_pow_left (by omega) 5
                  _ = 32 * z0^5 := by ring
              omega
            have h12 : z0^12 < 576 := by
              have : z0^17 < 576 * z0^5 := lt_of_le_of_lt hz17 h18
              rw [show z0^17 = z0^12 * z0^5 by ring] at this
              exact Nat.lt_of_mul_lt_mul_right this
            have : 576 ≤ z0^12 := le_trans (by norm_num) (Nat.pow_le_pow_left hz0ge 12)
            omega
          have hs2 : 2 ≤ (p+2)/r := by
            by_contra hlt
            have hlt1 : (p+2)/r ≤ 1 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hlt)
            have hle : r * ((p+2)/r) ≤ r * 1 := Nat.mul_le_mul_left r hlt1
            have hpr2 : p + 2 ≤ r := by
              have : r * ((p+2)/r) = p + 2 := hrs
              omega
            have h2z : 2 * z0 ≤ X := by omega
            omega
          have hrough : r ≤ ((p+2)/r).minFac := by
            have hminp : ((p+2)/r).minFac.Prime := Nat.minFac_prime (by omega)
            have hdiv : ((p+2)/r).minFac ∣ p + 2 :=
              dvd_trans (Nat.minFac_dvd _) ⟨r, by rw [Nat.mul_comm]; exact hrs.symm⟩
            have := Nat.minFac_le_of_dvd hminp.two_le hdiv
            exact this
          have hcopS : (primorial (y (X/r))).Coprime ((p+2)/r) := by
            by_contra h
            obtain ⟨ℓ, hℓ, hℓ1, hℓ2⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
            have hmem : ℓ ∈ (primorial (y (X/r))).primeFactors :=
              Nat.mem_primeFactors.mpr ⟨hℓ, hℓ1, primorial_ne_zero _⟩
            rw [primeFactors_primorial] at hmem
            have hℓle : ℓ ≤ y (X/r) := (Nat.mem_primesLE.mp hmem).1
            have hmin : ((p+2)/r).minFac ≤ ℓ := Nat.minFac_le_of_dvd hℓ.two_le hℓ2
            omega
          have hcopP : (primorial (y (X/r))).Coprime p := by
            have hpy : y (X/r) < p := by
              have h1 : y (X/r) ≤ X/r := hyY
              have h2 : X/r ≤ X := Nat.div_le_self X (by omega)
              omega
            have hnd : ¬ (p ∣ primorial (y (X/r))) := by
              intro hd
              have hmem : p ∈ (primorial (y (X/r))).primeFactors :=
                Nat.mem_primeFactors.mpr ⟨hpP, hd, primorial_ne_zero _⟩
              rw [primeFactors_primorial] at hmem
              have := (Nat.mem_primesLE.mp hmem).1
              omega
            exact (hpP.coprime_iff_not_dvd.mpr hnd).symm
          have hsp : r*((p+2)/r) - 2 = p := by omega
          rw [hsp]
          exact hcopS.mul_right hcopP
    · intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      have h1 : (a+2).minFac = (b+2).minFac := congrArg Sigma.fst hab
      have h2 : (a+2)/(a+2).minFac = (b+2)/(b+2).minFac := congrArg Sigma.snd hab
      have hra : (a+2).minFac * ((a+2)/(a+2).minFac) = a+2 := Nat.mul_div_cancel' (Nat.minFac_dvd _)
      have hrb : (b+2).minFac * ((b+2)/(b+2).minFac) = b+2 := Nat.mul_div_cancel' (Nat.minFac_dvd _)
      have hab2 : a + 2 = b + 2 := by
        calc a + 2 = (a+2).minFac * ((a+2)/(a+2).minFac) := hra.symm
          _ = (b+2).minFac * ((b+2)/(b+2).minFac) := by rw [h2, h1]
          _ = b + 2 := hrb
      omega
  have hcard : S.card ≤ ∑ r ∈ R, (T r).card := by
    calc S.card ≤ (R.sigma T).card := hinj
      _ = ∑ r ∈ R, (T r).card := Finset.card_sigma R T
  have hcardT : ∀ r ∈ R, ((T r).card : ℝ) ≤
      8210 * ((X/r:ℕ):ℝ) / (Real.log ((X/r:ℕ):ℝ))^2 := by
    intro r hr
    simp only [R, Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨⟨hrlo, hrle⟩, hrp⟩ := hr
    have hr2z : r < 2*z0 := by omega
    have hY0 : X₀ ≤ X/r := hX0le r hrlo hr2z
    obtain ⟨hy2, hyY, hylog, hyerr⟩ := hyspec (X/r) hY0
    have h := cofactor_primorial_bound (X/r) r (y (X/r)) (hY3 r hrlo hr2z) hrp (by omega)
      hy2 hylog hyerr
    exact h
  have hsumr : (∑ r ∈ R, (r:ℝ)⁻¹) ≤ 12 * Real.log 4 / Real.log (X:ℝ) := by
    have hterm : ∀ r ∈ R, (r:ℝ)⁻¹ ≤ Real.log (r:ℝ) / (Real.log (z0:ℝ) * (z0:ℝ)) := by
      intro r hr
      simp only [R, Finset.mem_filter, Finset.mem_Icc] at hr
      obtain ⟨⟨hrlo, hrle⟩, hrp⟩ := hr
      have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
      have hz0pos : (0:ℝ) < (z0:ℝ) := by exact_mod_cast (by omega : 0 < z0)
      have hlogz : 0 < Real.log (z0:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z0))
      have hlog : Real.log (z0:ℝ) ≤ Real.log (r:ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hrlo)
      have h1 : Real.log (z0:ℝ) * (z0:ℝ) ≤ Real.log (r:ℝ) * (r:ℝ) :=
        mul_le_mul hlog (by exact_mod_cast hrlo) (by positivity) (by positivity)
      have h2 : (r:ℝ)⁻¹ * (Real.log (z0:ℝ) * (z0:ℝ)) ≤ Real.log (r:ℝ) := by
        calc (r:ℝ)⁻¹ * (Real.log (z0:ℝ) * (z0:ℝ)) ≤ (r:ℝ)⁻¹ * (Real.log (r:ℝ) * (r:ℝ)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = Real.log (r:ℝ) * ((r:ℝ)⁻¹ * (r:ℝ)) := by ring
          _ = Real.log (r:ℝ) := by rw [inv_mul_cancel₀ hrpos.ne']; ring
      have hcpos : (0:ℝ) < Real.log (z0:ℝ) * (z0:ℝ) := mul_pos hlogz hz0pos
      rw [le_div_iff₀ hcpos]
      exact h2
    have hsub : R ⊆ (2*z0).primesLE := by
      intro r hr
      simp only [R, Finset.mem_filter, Finset.mem_Icc] at hr
      exact Nat.mem_primesLE.mpr ⟨by omega, hr.2⟩
    calc (∑ r ∈ R, (r:ℝ)⁻¹) ≤ ∑ r ∈ R, Real.log (r:ℝ) / (Real.log (z0:ℝ) * (z0:ℝ)) :=
          Finset.sum_le_sum hterm
      _ = (∑ r ∈ R, Real.log (r:ℝ)) / (Real.log (z0:ℝ) * (z0:ℝ)) := by rw [← Finset.sum_div]
      _ ≤ (∑ q ∈ (2*z0).primesLE, Real.log (q:ℝ)) / (Real.log (z0:ℝ) * (z0:ℝ)) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq _ =>
            Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hq).one_le))
      _ = Chebyshev.theta ((2*z0:ℕ):ℝ) / (Real.log (z0:ℝ) * (z0:ℝ)) := by
          rw [Chebyshev.theta_eq_sum_primesLE_log]
      _ ≤ Real.log 4 * ((2*z0:ℕ):ℝ) / (Real.log (z0:ℝ) * (z0:ℝ)) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
      _ = 2 * Real.log 4 / Real.log (z0:ℝ) := by
          have hz0ne : (z0:ℝ) ≠ 0 := by positivity
          push_cast
          field_simp
      _ ≤ 12 * Real.log 4 / Real.log (X:ℝ) := by
          have hlogz : Real.log (X:ℝ) ≤ 6 * Real.log (z0:ℝ) := by
            have hXz6 : X ≤ z0^6 := by
              calc X ≤ (z0+1)^5 := (Nat.lt_pow_nthRoot_add_one (by norm_num) X).le
                _ ≤ (2*z0)^5 := Nat.pow_le_pow_left (by omega) 5
                _ = 32 * z0^5 := by ring
                _ ≤ z0 * z0^5 := Nat.mul_le_mul_right (z0^5) hz0ge
                _ = z0^6 := by ring
            have hR : (X:ℝ) ≤ (z0:ℝ)^6 := by exact_mod_cast hXz6
            have h := Real.log_le_log (by positivity) hR
            rwa [Real.log_pow] at h
          have hlogX : 0 < Real.log (X:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
          have hlogz' : 0 < Real.log (z0:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z0))
          have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
          rw [div_le_div_iff₀ hlogz' hlogX]
          nlinarith
  calc (∑ p ∈ S, Real.log (p:ℝ) * Real.log ((p:ℝ)+2))
      ≤ ∑ p ∈ S, 4 * (Real.log (X:ℝ))^2 := Finset.sum_le_sum hper
    _ = (S.card : ℝ) * (4 * (Real.log (X:ℝ))^2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((∑ r ∈ R, (T r).card : ℕ) : ℝ) * (4 * (Real.log (X:ℝ))^2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact Nat.cast_le.mpr hcard
    _ = ∑ r ∈ R, ((T r).card : ℝ) * (4 * (Real.log (X:ℝ))^2) := by
        push_cast
        rw [Finset.sum_mul]
    _ ≤ ∑ r ∈ R, (8210 * 16 * (X:ℝ) * (r:ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro r hr
        simp only [R, Finset.mem_filter, Finset.mem_Icc] at hr
        obtain ⟨⟨hrlo, hrle⟩, hrp⟩ := hr
        have hr2z : r < 2*z0 := by omega
        have hYcast : ((X/r:ℕ):ℝ) ≤ (X:ℝ) / (r:ℝ) := Nat.cast_div_le
        have hY3r : 3 ≤ X/r := hY3 r hrlo hr2z
        have hlogY : 0 < Real.log ((X/r:ℕ):ℝ) :=
          Real.log_pos (by exact_mod_cast (by omega : 1 < X/r))
        have hlogYpos : 0 < (Real.log ((X/r:ℕ):ℝ))^2 := sq_pos_of_pos hlogY
        have hlogsq : (Real.log (X:ℝ))^2 ≤ 4 * (Real.log ((X/r:ℕ):ℝ))^2 := by
          have hYsq' : X ≤ (X/r)^2 := hYsq r hrlo hr2z
          have hR : (X:ℝ) ≤ ((X/r:ℕ):ℝ)^2 := by exact_mod_cast hYsq'
          have h := Real.log_le_log (by positivity) hR
          rw [Real.log_pow] at h
          have hlogX0 : 0 ≤ Real.log (X:ℝ) :=
            Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
          nlinarith
        have hrR : r ∈ R := by
          simp only [R, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hrlo, hrle⟩, hrp⟩
        calc ((T r).card : ℝ) * (4 * (Real.log (X:ℝ))^2)
            ≤ (8210 * ((X/r:ℕ):ℝ) / (Real.log ((X/r:ℕ):ℝ))^2) * (4 * (Real.log (X:ℝ))^2) :=
              mul_le_mul_of_nonneg_right (hcardT r hrR) (by positivity)
          _ = 8210 * ((X/r:ℕ):ℝ) * (4 * (Real.log (X:ℝ))^2) / (Real.log ((X/r:ℕ):ℝ))^2 := by ring
          _ ≤ 8210 * ((X/r:ℕ):ℝ) * 16 := by
              rw [div_le_iff₀ hlogYpos]
              nlinarith [hlogsq]
          _ ≤ 8210 * ((X:ℝ)/(r:ℝ)) * 16 := by
              have : (0:ℝ) ≤ 8210 * 16 := by positivity
              nlinarith [hYcast]
          _ = 8210 * 16 * (X:ℝ) * (r:ℝ)⁻¹ := by rw [div_eq_mul_inv]; ring
    _ = 8210 * 16 * (X:ℝ) * ∑ r ∈ R, (r:ℝ)⁻¹ := by rw [← Finset.mul_sum]
    _ ≤ 8210 * 16 * (X:ℝ) * (12 * Real.log 4 / Real.log (X:ℝ)) := by
        apply mul_le_mul_of_nonneg_left hsumr (by positivity)
    _ = 8210 * 16 * 12 * Real.log 4 * (X:ℝ) / Real.log (X:ℝ) := by
        have hne : Real.log (X:ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < X))).ne'
        field_simp
