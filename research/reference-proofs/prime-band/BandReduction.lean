import BandPairs
import FrozenBulk
import UpstreamScale

/-! Eventual equivalence between the frozen high-high floor and the sum with the growing band removed. -/

namespace GoldbachMinor

open Filter GoldbachWeight FrozenBulk
open scoped Topology

/-- The usable bandwidth after averaging over frequencies and using the prime mass. -/
def primeBandWidth (n : ℕ) : ℕ := n/(logWidth n)^4

theorem logWidth_tends : Tendsto logWidth atTop atTop := by
  apply tendsto_atTop.mpr
  intro K
  filter_upwards [eventually_ge_atTop (2^K)] with n hn
  have h := Nat.le_log_of_pow_le (by decide : 1<2) (show 2^K ≤ n+2 by omega)
  unfold logWidth
  omega

/-- The band removed in the asymptotic equivalence has unbounded width. -/
theorem primeBandWidth_tends : Tendsto primeBandWidth atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  have hb : 0 < 4*((B:ℝ)+1) := by positivity
  have htail := (tendsto_pow_const_div_const_pow_of_one_lt 4 (by norm_num : (1:ℝ)<2)).eventually_lt_const
    (one_div_pos.mpr hb)
  filter_upwards [logWidth_tends.eventually htail, eventually_ge_atTop 2] with n h hn
  have hpow := Nat.pow_log_le_self 2 (show n+2≠0 by omega)
  have h2 : 2^(logWidth n) ≤ 4*n := by
    unfold logWidth
    rw [pow_succ]
    omega
  have hexp : (2:ℝ)^(logWidth n) ≤ 4*(n:ℝ) := by exact_mod_cast h2
  have h1 := (div_lt_div_iff₀ (by positivity : 0<(2:ℝ)^(logWidth n)) hb).1 h
  have hnon : 0 ≤ (logWidth n:ℝ)^4 := by positivity
  have hmul : (B:ℝ)*(logWidth n:ℝ)^4 ≤ n := by nlinarith only [h1,hexp,hnon]
  exact (Nat.le_div_iff_mul_le (pow_pos (by dsimp [logWidth]; omega) 4)).2 (by exact_mod_cast hmul)

private theorem high_matches : deskHigh = high := by
  funext n k
  simp only [deskHigh, high]
  split_ifs <;> simp_all

theorem catalogue_bulk_arithmetic (n : ℕ) (hn : 2*(catalogueCutoff n)^2<n) :
    (deskI n (deskHigh n) (deskHigh n)).re = arithmeticBulk (catalogueCutoff n) n (high n) := by
  have h : deskI n (deskHigh n) (deskHigh n) = (arithmeticBulk (catalogueCutoff n) n (deskHigh n):ℂ) :=
    integral_eq_arithmeticBulk (catalogueCutoff n) n hn (deskHigh n)
  rw [h,high_matches,Complex.ofReal_re]

/-- Any uniformly negligible band can be removed from the exact registered floor. -/
theorem catalogue_trimmed_iff_of_negligible (width : ℕ → ℕ)
    (small : ∀ ε : ℝ, 0<ε → ∃ M : ℕ, ∀ n ≥ M,
      |nearBulk (catalogueCutoff n) n (width n) (high n)| ≤ ε*n) : BulkFloor ↔ ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
    -(ε*(n:ℝ)) ≤ trimmedBulk (catalogueCutoff n) n (width n) (high n) := by
  obtain ⟨S,hS⟩ : ∃ S:ℕ, ∀ n≥S, 2*(catalogueCutoff n)^2<n :=
    PEqualNP.Outside.L_goldbach_arc_cutoff_scale
  change (∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
    -(ε*(n:ℝ)) ≤ (deskI n (deskHigh n) (deskHigh n)).re) ↔ _
  constructor <;> intro h ε hε <;>
    obtain ⟨N,hN⟩ := h (ε/2) (half_pos hε) <;>
    obtain ⟨M,hM⟩ := small (ε/2) (half_pos hε) <;>
    refine ⟨max S (max N M), fun n hn heven => ?_⟩ <;>
    have hi := catalogue_bulk_arithmetic n (hS n (by omega)) <;>
    have hs := split_near (catalogueCutoff n) n (width n) (high n) <;>
    obtain ⟨hl,hu⟩ := abs_le.mp (hM n (by omega)) <;>
    linarith only [hi,hs,hl,hu,hN n (by omega) heven]

private theorem width_pos (n : ℕ) : 0 < logWidth n := Nat.succ_pos _

private theorem log_n_le_width (n : ℕ) (hn : 0<n) : Real.log n ≤ (logWidth n:ℝ) := by
  have h := Nat.lt_pow_succ_log_self (by decide : 1<2) (n+2)
  have hpow : (n:ℝ) ≤ (2:ℝ)^(logWidth n) := by
    exact_mod_cast (show n ≤ 2^(logWidth n) by unfold logWidth; omega)
  have hh := Real.log_le_log (by exact_mod_cast hn) hpow
  rw [Real.log_pow] at hh
  have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  exact hh.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans_eq (mul_one _))

private theorem harmonic_le_log (Q : ℕ) : harmonicCutoff Q ≤ 1+Real.log Q := by
  simpa only [harmonicCutoff,one_div,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    using harmonic_le_one_add_log Q

theorem prime_band_uniform (n : ℕ) (hn : 0<n) :
    |nearBulk (catalogueCutoff n) n (primeBandWidth n) (high n)| ≤
    (4*Real.log 4)*n*((1+2*Real.log (logWidth n:ℝ))^2/(logWidth n:ℝ)) := by
  let L := (logWidth n:ℝ)
  have hL : 0<L := by dsimp only [L]; exact_mod_cast width_pos n
  have hL1 : 1≤L := by dsimp only [L]; exact_mod_cast (show 1≤logWidth n from width_pos n)
  have hq : (catalogueCutoff n:ℝ) ≤ L^2 := by
    dsimp [catalogueCutoff,L,logWidth]
    push_cast
    nlinarith [show 0≤(Nat.log 2 (n+2):ℝ) by positivity]
  have hm := Nat.le_log_of_pow_le (by decide : 1<2) (show 2^1 ≤ n+2 by omega)
  have hQ : 0 < (catalogueCutoff n:ℝ) := by unfold catalogueCutoff; positivity
  have hhl : harmonicCutoff (catalogueCutoff n) ≤ 1+2*Real.log L := by
    have hlog := Real.log_le_log hQ hq
    rw [Real.log_pow] at hlog
    exact (harmonic_le_log _).trans (add_le_add_right (by simpa using hlog) _)
  have hh : 0 ≤ harmonicCutoff (catalogueCutoff n) := by unfold harmonicCutoff; positivity
  have hK : (primeBandWidth n:ℝ)*L^4 ≤ n := by
    dsimp [primeBandWidth,L]
    exact_mod_cast Nat.div_mul_le_self n ((logWidth n)^4)
  calc
    _ ≤ _ := prime_band_bound _ _ _ hn
    _ ≤ 4*Real.log 4*L*(L^2)*(primeBandWidth n:ℝ)*(1+2*Real.log L)^2 := by
      gcongr
      exact log_n_le_width n hn
    _ = (4*Real.log 4)*((primeBandWidth n:ℝ)*L^4)*((1+2*Real.log L)^2/L) := by
      field_simp
    _ ≤ _ := by gcongr

private theorem log_bound_ratio :
    Tendsto (fun x : ℝ => (1+2*Real.log x)^2/x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => 1/Real.sqrt x) atTop (𝓝 0) := by
    simpa [one_div,Function.comp_def] using (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop)
  have h2 : Tendsto (fun x : ℝ => Real.log x/Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
  have hc : Tendsto (fun x : ℝ => (1/Real.sqrt x+2*(Real.log x/Real.sqrt x))^2) atTop (𝓝 0) := by
    simpa using (h1.add (h2.const_mul 2)).pow 2
  refine hc.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  calc
    _ = ((1+2*Real.log x)/Real.sqrt x)^2 := by ring
    _ = _ := by rw [div_pow,Real.sq_sqrt hx]

theorem prime_band_negligible (ε : ℝ) (hε : 0<ε) : ∃ N:ℕ, ∀ n ≥ N,
    |nearBulk (catalogueCutoff n) n (primeBandWidth n) (high n)| ≤ ε*n := by
  have hl : Tendsto (fun n : ℕ => (logWidth n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp logWidth_tends
  have lim := (log_bound_ratio.comp hl).const_mul (4*Real.log 4)
  rw [mul_zero] at lim
  obtain ⟨N,hN⟩ := eventually_atTop.mp (lim.eventually_lt_const hε)
  refine ⟨max 1 N,fun n hn => (prime_band_uniform n (by omega)).trans ?_⟩
  have h := mul_le_mul_of_nonneg_right (hN n (by omega)).le (show 0≤(n:ℝ) by positivity)
  dsimp only [Function.comp_apply] at h
  convert h using 1; ring

/-- This equivalence uses the verbatim frozen proposition, including every-even quantification. -/
theorem catalogue_prime_band_iff : FrozenBulk.BulkFloor ↔
    ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, Even n →
      -(ε*(n:ℝ)) ≤ trimmedBulk (catalogueCutoff n) n (primeBandWidth n) (high n) :=
  catalogue_trimmed_iff_of_negligible primeBandWidth prime_band_negligible

#print axioms prime_band_uniform
#print axioms primeBandWidth_tends
#print axioms catalogue_prime_band_iff

end GoldbachMinor
