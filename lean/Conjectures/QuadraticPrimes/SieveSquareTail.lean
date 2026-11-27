import Mathlib

namespace Conjectures.QuadraticPrimes.SieveSquareTail_aux

private theorem cast_div_le_real (a b : ℕ) (hb : 0 < b) : ((a / b : ℕ) : ℝ) ≤ (a:ℝ) / (b:ℝ) := by
  have h : (a / b : ℕ) * b ≤ a := Nat.div_mul_le_self a b
  have h' : ((a / b : ℕ) : ℝ) * (b:ℝ) ≤ (a:ℝ) := by exact_mod_cast h
  have hb0 : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  exact (le_div_iff₀ hb0).mpr h'

private theorem interval_residue_count (x q : ℕ) (hq : 0 < q) :
    ((Finset.Ioc x (2*x)).filter (fun n => q ∣ n^2+1)).card
      ≤ (x/q+1) * ((Finset.range q).filter (fun r => q ∣ r^2+1)).card := by
  let roots := (Finset.range q).filter (fun r => q ∣ r ^ 2 + 1)
  let solutions := (Finset.Ioc x (2 * x)).filter (fun n => q ∣ n ^ 2 + 1)
  let blockAndRoot := fun n : ℕ => ((n - x) / q, n % q)
  change solutions.card ≤ (x / q + 1) * roots.card
  rw [← Finset.card_range (x / q + 1), ← Finset.card_product]
  refine Finset.card_le_card_of_injOn blockAndRoot ?_ ?_
  · intro n hn
    have hn' : n ∈ solutions := hn
    obtain ⟨hnInterval, hnDvd⟩ := Finset.mem_filter.mp hn'
    obtain ⟨_, hnUpper⟩ := Finset.mem_Ioc.mp hnInterval
    apply Finset.mk_mem_product
    · apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega : n - x ≤ x))
    · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n hq), ?_⟩
      exact Nat.modEq_zero_iff_dvd.mp
        ((((Nat.mod_modEq n q).pow 2).add_right 1).trans hnDvd.modEq_zero_nat)
  · intro n hn m hm heq
    have hn' : n ∈ solutions := hn
    have hm' : m ∈ solutions := hm
    have hnx := ((Finset.mem_Ioc.mp (Finset.mem_filter.mp hn').1).1).le
    have hmx := ((Finset.mem_Ioc.mp (Finset.mem_filter.mp hm').1).1).le
    have hquot : (n - x) / q = (m - x) / q := congrArg Prod.fst heq
    have hmod : Nat.ModEq q n m := congrArg Prod.snd heq
    have hrem : (n - x) % q = (m - x) % q := hmod.sub_right hnx hmx
    have hdiff : n - x = m - x := by
      rw [← Nat.mod_add_div (n - x) q, ← Nat.mod_add_div (m - x) q, hrem, hquot]
    omega

private theorem sum_inv_sq_le (y M : ℕ) (hy : 1 ≤ y) :
    ∑ n ∈ Finset.Ioc y M, ((1:ℝ)/(n:ℝ)^2) ≤ 1/(y:ℝ) := by
  have key : ∀ m : ℕ, y ≤ m →
      ∑ n ∈ Finset.Ioc y m, ((1:ℝ)/(n:ℝ)^2) ≤ 1/(y:ℝ) - 1/(m:ℝ) := by
    intro m
    induction m with
    | zero =>
        intro h
        exact absurd h (by omega)
    | succ m ih =>
        intro h
        by_cases hym : y ≤ m
        · have hm1 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
          have hmp : (0:ℝ) < ((m + 1 : ℕ):ℝ) := by exact_mod_cast (show 0 < m + 1 by omega)
          have hle : (m:ℝ) ≤ ((m + 1 : ℕ):ℝ) := by exact_mod_cast Nat.le_succ m
          have hstep : (1:ℝ)/((m + 1 : ℕ):ℝ)^2 ≤ 1/(m:ℝ) - 1/((m + 1 : ℕ):ℝ) := by
            have h1 : (1:ℝ)/((m + 1 : ℕ):ℝ)^2 ≤ 1/((m:ℝ)*((m + 1 : ℕ):ℝ)) := by
              apply one_div_le_one_div_of_le (mul_pos hm1 hmp)
              calc (m:ℝ) * ((m + 1 : ℕ):ℝ)
                  ≤ ((m + 1 : ℕ):ℝ) * ((m + 1 : ℕ):ℝ) :=
                    mul_le_mul_of_nonneg_right hle hmp.le
                _ = ((m + 1 : ℕ):ℝ)^2 := by ring
            have h2 : (1:ℝ)/((m:ℝ)*((m + 1 : ℕ):ℝ)) = 1/(m:ℝ) - 1/((m + 1 : ℕ):ℝ) := by
              field_simp
              push_cast
              ring
            rw [h2] at h1
            exact h1
          rw [Finset.sum_Ioc_succ_top hym (fun n : ℕ => (1:ℝ)/(n:ℝ)^2)]
          have hih := ih hym
          linarith
        · have hy' : y = m + 1 := by omega
          subst hy'
          simp
  by_cases h : y ≤ M
  · have hM : (0:ℝ) ≤ 1/(M:ℝ) := by positivity
    have hk := key M h
    linarith
  · have hempty : Finset.Ioc y M = ∅ := by
      rw [Finset.Ioc_eq_empty_iff]
      omega
    rw [hempty]
    simp

/-- Two solutions of `X^2 + 1 = m Y^2` inside a dyadic window are separated by a factor `> 2`. -/
theorem pell_spacing :
    ∀ m a b u v : ℕ, 0 < m → 0 < a → a < b →
      a ^ 2 + 1 = m * u ^ 2 → b ^ 2 + 1 = m * v ^ 2 → 2 * a < b := by
  intro m a b u v hm ha hab hA hB
  have hm2 : 2 ≤ m := by
    have hm_ne_one : m ≠ 1 := by
      intro hm_one
      subst m
      have hu_gt : a < u := by
        by_contra hu_not_gt
        have hu_le : u ≤ a := Nat.le_of_not_gt hu_not_gt
        have hu_sq_le : u ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hu_le 2
        omega
      have ha_succ_le : a + 1 ≤ u := hu_gt
      have ha_succ_sq_le : (a + 1) ^ 2 ≤ u ^ 2 :=
        Nat.pow_le_pow_left ha_succ_le 2
      nlinarith
    omega
  have hu : 0 < u := by
    by_contra hu_not_pos
    have hu_zero : u = 0 := by omega
    subst u
    simp at hA
  have hAZ : (a : ℤ) ^ 2 + 1 = (m : ℤ) * (u : ℤ) ^ 2 := by
    exact_mod_cast hA
  have hBZ : (b : ℤ) ^ 2 + 1 = (m : ℤ) * (v : ℤ) ^ 2 := by
    exact_mod_cast hB
  have haZ : 0 ≤ (a : ℤ) := Int.natCast_nonneg a
  have hbZ : 0 ≤ (b : ℤ) := Int.natCast_nonneg b
  have huZ : 0 ≤ (u : ℤ) := Int.natCast_nonneg u
  have hvZ : 0 ≤ (v : ℤ) := Int.natCast_nonneg v
  have habZ : (a : ℤ) < b := by exact_mod_cast hab
  have huvZ : (u : ℤ) < v := by
    have huv_sq : u ^ 2 < v ^ 2 := by
      have hmul : m * u ^ 2 < m * v ^ 2 := by
        calc
          m * u ^ 2 = a ^ 2 + 1 := hA.symm
          _ < b ^ 2 + 1 := Nat.add_lt_add_right (by nlinarith [hab]) 1
          _ = m * v ^ 2 := hB
      exact (Nat.mul_lt_mul_left hm).mp hmul
    exact (sq_lt_sq₀ huZ hvZ).mp (by exact_mod_cast huv_sq)
  have hQdiffZ :
      ((b : ℤ) * u) ^ 2 - ((a : ℤ) * v) ^ 2 =
        (v : ℤ) ^ 2 - (u : ℤ) ^ 2 := by
    have ha_eq : (a : ℤ) ^ 2 = (m : ℤ) * (u : ℤ) ^ 2 - 1 := by linarith
    have hb_eq : (b : ℤ) ^ 2 = (m : ℤ) * (v : ℤ) ^ 2 - 1 := by linarith
    calc
      ((b : ℤ) * u) ^ 2 - ((a : ℤ) * v) ^ 2 =
          (b : ℤ) ^ 2 * (u : ℤ) ^ 2 - (a : ℤ) ^ 2 * (v : ℤ) ^ 2 := by ring
      _ = ((m : ℤ) * (v : ℤ) ^ 2 - 1) * (u : ℤ) ^ 2 -
          ((m : ℤ) * (u : ℤ) ^ 2 - 1) * (v : ℤ) ^ 2 := by
        rw [hb_eq, ha_eq]
      _ = (v : ℤ) ^ 2 - (u : ℤ) ^ 2 := by ring
  have hQsqZ : ((a : ℤ) * v) ^ 2 < ((b : ℤ) * u) ^ 2 := by
    have hright : 0 < (v : ℤ) ^ 2 - (u : ℤ) ^ 2 := by
      exact sub_pos.mpr ((sq_lt_sq₀ huZ hvZ).mpr huvZ)
    linarith
  have hQltZ : (a : ℤ) * v < b * u :=
    (sq_lt_sq₀ (mul_nonneg haZ hvZ) (mul_nonneg hbZ huZ)).mp hQsqZ
  have hQlt : a * v < b * u := by exact_mod_cast hQltZ
  have hPdiffZ :
      ((m : ℤ) * u * v) ^ 2 - ((a : ℤ) * b) ^ 2 =
        (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + 1 := by
    calc
      ((m : ℤ) * u * v) ^ 2 - ((a : ℤ) * b) ^ 2 =
          ((m : ℤ) * (u : ℤ) ^ 2) * ((m : ℤ) * (v : ℤ) ^ 2) -
            ((a : ℤ) * b) ^ 2 := by ring
      _ = ((a : ℤ) ^ 2 + 1) * ((b : ℤ) ^ 2 + 1) - ((a : ℤ) * b) ^ 2 := by
        rw [hAZ, hBZ]
      _ = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + 1 := by ring
  have hPsqZ : ((a : ℤ) * b) ^ 2 < ((m : ℤ) * u * v) ^ 2 := by
    have hright : 0 < (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + 1 := by
      nlinarith [sq_nonneg (a : ℤ), sq_nonneg (b : ℤ)]
    linarith
  have hPltZ : (a : ℤ) * b < (m : ℤ) * u * v := by
    apply (sq_lt_sq₀ (mul_nonneg haZ hbZ) ?_).mp hPsqZ
    positivity
  have hPlt : a * b < m * u * v := by exact_mod_cast hPltZ
  set P := m * u * v - a * b with hPdef
  set Q := b * u - a * v with hQdef
  have hP_one : 1 ≤ P := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hPlt)
  have hQ_one : 1 ≤ Q := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hQlt)
  have hPcast : (P : ℤ) = (m : ℤ) * u * v - (a : ℤ) * b := by
    simp [hPdef, Nat.cast_sub (Nat.le_of_lt hPlt)]
  have hQcast : (Q : ℤ) = (b : ℤ) * u - (a : ℤ) * v := by
    simp [hQdef, Nat.cast_sub (Nat.le_of_lt hQlt)]
  have hAfac : (m : ℤ) * (u : ℤ) ^ 2 - (a : ℤ) ^ 2 = 1 := by linarith
  have hBfac : (m : ℤ) * (v : ℤ) ^ 2 - (b : ℤ) ^ 2 = 1 := by linarith
  have hpellZ : (P : ℤ) ^ 2 - (m : ℤ) * (Q : ℤ) ^ 2 = 1 := by
    rw [hPcast, hQcast]
    calc
      ((m : ℤ) * u * v - (a : ℤ) * b) ^ 2 -
            (m : ℤ) * ((b : ℤ) * u - (a : ℤ) * v) ^ 2 =
          ((m : ℤ) * (u : ℤ) ^ 2 - (a : ℤ) ^ 2) *
            ((m : ℤ) * (v : ℤ) ^ 2 - (b : ℤ) ^ 2) := by ring
      _ = 1 * 1 := by rw [hAfac, hBfac]
      _ = 1 := by ring
  have hpellZ' : (P : ℤ) ^ 2 = 1 + (m : ℤ) * (Q : ℤ) ^ 2 := by linarith
  have hpell : P ^ 2 = 1 + m * Q ^ 2 := by exact_mod_cast hpellZ'
  have hP_two : 2 ≤ P := by
    have hP_ne_one : P ≠ 1 := by
      intro hP_eq_one
      have hQ_sq_one : 1 ≤ Q ^ 2 := by nlinarith
      have hprod : 2 ≤ m * Q ^ 2 := by
        calc
          2 = 2 * 1 := by norm_num
          _ ≤ m * Q ^ 2 := Nat.mul_le_mul hm2 hQ_sq_one
      rw [hP_eq_one] at hpell
      have hbad : (1 : ℕ) = 1 + m * Q ^ 2 := by simpa using hpell
      omega
    omega
  have hrecZ : (a : ℤ) * P + (m : ℤ) * u * Q = b := by
    rw [hPcast, hQcast]
    calc
      (a : ℤ) * ((m : ℤ) * u * v - (a : ℤ) * b) +
            (m : ℤ) * u * ((b : ℤ) * u - (a : ℤ) * v) =
          (b : ℤ) * ((m : ℤ) * (u : ℤ) ^ 2 - (a : ℤ) ^ 2) := by ring
      _ = b := by rw [hAfac]; ring
  have hrec : a * P + m * u * Q = b := by exact_mod_cast hrecZ
  have haP : 2 * a ≤ a * P := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left a hP_two
  have hmuQ : 2 ≤ m * u * Q := by
    have hmu : 2 ≤ m * u := by
      calc
        2 = 2 * 1 := by norm_num
        _ ≤ m * u := Nat.mul_le_mul hm2 hu
    calc
      2 = 2 * 1 := by norm_num
      _ ≤ (m * u) * Q := Nat.mul_le_mul hmu hQ_one
  have hlow : 2 * a + 2 ≤ a * P + m * u * Q := Nat.add_le_add haP hmuQ
  omega

private theorem oriented_root_pair
    (p x y : ℕ) (hp : Nat.Prime p) (hp2 : 2 < p)
    (hyx : y ≤ x) (hx_lt : x < p ^ 2)
    (hx_root : p ^ 2 ∣ x ^ 2 + 1) (hy_root : p ^ 2 ∣ y ^ 2 + 1) :
    y = x ∨ x + y = p ^ 2 := by
  have hp_generic : Prime p := Nat.prime_iff.mp hp
  have hroot_diff : p ^ 2 ∣ (x ^ 2 + 1) - (y ^ 2 + 1) :=
    Nat.dvd_sub hx_root hy_root
  have hsub_eq : (x ^ 2 + 1) - (y ^ 2 + 1) = x ^ 2 - y ^ 2 := by
    have hsq : y ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hyx 2
    omega
  have hprod : p ^ 2 ∣ (x - y) * (x + y) := by
    rw [hsub_eq, Nat.pow_two_sub_pow_two] at hroot_diff
    simpa [Nat.mul_comm] using hroot_diff
  have hp_not_two : ¬p ∣ 2 := by
    intro hp_two
    have hp_le_two : p ≤ 2 := Nat.le_of_dvd (by omega) hp_two
    omega
  have hnot_both : ¬(p ∣ x - y ∧ p ∣ x + y) := by
    rintro ⟨hdiff, hsum⟩
    have htwo_x : p ∣ 2 * x := by
      have hsum_eq : (x - y) + (x + y) = 2 * x := by omega
      exact hsum_eq ▸ Nat.dvd_add hdiff hsum
    have hpx : p ∣ x := (hp.dvd_mul.mp htwo_x).resolve_left hp_not_two
    have hpx_sq : p ∣ x ^ 2 := by
      rcases hpx with ⟨k, hk⟩
      refine ⟨p * k ^ 2, ?_⟩
      rw [hk]
      ring
    have hp_dvd_sq : p ∣ p ^ 2 := ⟨p, by ring⟩
    have hx_root_p : p ∣ x ^ 2 + 1 := dvd_trans hp_dvd_sq hx_root
    have hp_one : p ∣ 1 := by
      have hle : x ^ 2 ≤ x ^ 2 + 1 := by omega
      simpa using Nat.dvd_sub hx_root_p hpx_sq
    exact hp.not_dvd_one hp_one
  by_cases hdiff : p ∣ x - y
  · have hsum_not : ¬p ∣ x + y := by
      intro hsum
      exact hnot_both ⟨hdiff, hsum⟩
    have hdiff_sq : p ^ 2 ∣ x - y :=
      hp_generic.pow_dvd_of_dvd_mul_right 2 hsum_not hprod
    have hdiff_zero : x - y = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdiff_sq (by omega)
    left
    omega
  · have hsum_sq : p ^ 2 ∣ x + y :=
      hp_generic.pow_dvd_of_dvd_mul_left 2 hdiff hprod
    have hx_ne_zero : x ≠ 0 := by
      intro hx_zero
      subst x
      have hp_sq_le : p ^ 2 ≤ 1 := Nat.le_of_dvd (by omega) hx_root
      have hp_sq_gt : 1 < p ^ 2 := by nlinarith
      omega
    have hsum_ne_zero : x + y ≠ 0 := by omega
    have hsum_lt : x + y < 2 * p ^ 2 := by omega
    right
    exact Nat.eq_of_dvd_of_lt_two_mul hsum_ne_zero hsum_sq hsum_lt

/-- At most two residues modulo `p^2` satisfy `r^2 + 1 ≡ 0`. -/
theorem roots_sq_le_two (p : ℕ) (hp : Nat.Prime p) (hp2 : 2 < p) :
    ((Finset.range (p ^ 2)).filter (fun r => p ^ 2 ∣ r ^ 2 + 1)).card ≤ 2 := by
  classical
  set roots : Finset ℕ := (Finset.range (p ^ 2)).filter (fun r => p ^ 2 ∣ r ^ 2 + 1) with hrootsdef
  by_cases hroots_empty : roots = ∅
  · simp [hroots_empty]
  · obtain ⟨r₀, hr₀⟩ := Finset.nonempty_iff_ne_empty.mpr hroots_empty
    have hr₀_range : r₀ < p ^ 2 :=
      Finset.mem_range.mp (Finset.mem_filter.mp hr₀).1
    have hr₀_root : p ^ 2 ∣ r₀ ^ 2 + 1 :=
      (Finset.mem_filter.mp hr₀).2
    have hsubset : roots ⊆ {r₀, p ^ 2 - r₀} := by
      intro r hr
      have hr_range : r < p ^ 2 :=
        Finset.mem_range.mp (Finset.mem_filter.mp hr).1
      have hr_root : p ^ 2 ∣ r ^ 2 + 1 :=
        (Finset.mem_filter.mp hr).2
      have hpair : r = r₀ ∨ r + r₀ = p ^ 2 := by
        rcases Nat.le_total r₀ r with hr₀_le | hr_le
        · simpa [Nat.add_comm, eq_comm] using
            oriented_root_pair p r r₀ hp hp2 hr₀_le hr_range hr_root hr₀_root
        · simpa [Nat.add_comm] using
            oriented_root_pair p r₀ r hp hp2 hr_le hr₀_range hr₀_root hr_root
      rcases hpair with hr_eq | hsum
      · simp [hr_eq]
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        right
        omega
    have hcard : roots.card ≤ ({r₀, p ^ 2 - r₀} : Finset ℕ).card :=
      Finset.card_le_card hsubset
    have hpair_card : ({r₀, p ^ 2 - r₀} : Finset ℕ).card ≤ 2 :=
      Finset.card_le_two
    simpa [hrootsdef] using hcard.trans hpair_card

end Conjectures.QuadraticPrimes.SieveSquareTail_aux

open Conjectures.QuadraticPrimes.SieveSquareTail_aux

theorem Conjectures.QuadraticPrimes.SieveSquareTail :
let f := fun k : ℕ => 4*k^2+1; let block := fun x : ℕ => Finset.Ioc (x/2) x; let flagged := fun x y : ℕ => (block x).filter (fun k =>
  ((Finset.Ioc y (2*x)).filter (fun p => Nat.Prime p ∧ p^2 ∣ f k)).Nonempty);
∃ C : ℝ, 0<C ∧ ∀ x y : ℕ, 2≤x → 2≤y →
  ((flagged x y).card : ℝ) ≤ C*((x : ℝ)/y + (x : ℝ)^(2/3 : ℝ)) := by
  refine ⟨8, by norm_num, ?_⟩
  intro x y hx hy
  simp only []
  classical
  have hxR : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hxpos : (0:ℝ) < (x:ℝ) := by linarith
  have hypos : (0:ℝ) < (y:ℝ) := by exact_mod_cast (show 0 < y by omega)
  set T : ℝ := (x:ℝ)^(2/3:ℝ) with hTdef
  have hT1 : (1:ℝ) ≤ T := by
    rw [hTdef]; exact Real.one_le_rpow (by linarith : (1:ℝ) ≤ (x:ℝ)) (by norm_num)
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le one_pos hT1
  have hT2pos : (0:ℝ) < T^2 := by positivity
  have hT3 : T^3 = (x:ℝ)^2 := by
    have key : (T:ℝ)^((3:ℕ):ℝ) = (x:ℝ)^((2:ℕ):ℝ) := by
      rw [hTdef, ← Real.rpow_mul (le_of_lt hxpos),
        show (2/3:ℝ)*((3:ℕ):ℝ) = ((2:ℕ):ℝ) by norm_num]
    simpa only [Real.rpow_natCast] using key
  have hB_low : ∀ k ∈ Finset.Ioc (x/2) x, x < 2*k := by
    intro k hk; have h1 := (Finset.mem_Ioc.mp hk).1; omega
  have hB_up : ∀ k ∈ Finset.Ioc (x/2) x, 2*k ≤ 2*x := by
    intro k hk; have h2 := (Finset.mem_Ioc.mp hk).2; omega
  set M := Nat.floor T with hMdef
  set S := (Finset.Ioc y M).filter (fun p => Nat.Prime p) with hSdef
  set Small := S.biUnion (fun p => (Finset.Ioc (x/2) x).filter (fun k => p^2 ∣ 4*k^2+1)) with hSmalldef
  set N := Nat.ceil (4*T+1) with hNdef
  set LargeSet := (Finset.range N).biUnion (fun m =>
    (Finset.Ioc (x/2) x).filter (fun k => ∃ p, y < p ∧ p ≤ 2*x ∧ Nat.Prime p ∧ T < (p:ℝ) ∧ 4*k^2+1 = m*p^2))
    with hLargeSetdef
  have hsub : (Finset.Ioc (x/2) x).filter (fun k =>
      ((Finset.Ioc y (2*x)).filter (fun p => Nat.Prime p ∧ p^2 ∣ 4*k^2+1)).Nonempty) ⊆ Small ∪ LargeSet := by
    intro k hk
    obtain ⟨hkB, hkne⟩ := Finset.mem_filter.mp hk
    obtain ⟨p, hp⟩ := hkne
    obtain ⟨hpI, hprime, hdvd⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpy, hpx⟩ := Finset.mem_Ioc.mp hpI
    rcases le_or_gt (p:ℝ) T with hle | hgt
    · have hpM : p ≤ M := by rw [hMdef]; exact Nat.le_floor hle
      have hpS : p ∈ S := by
        rw [hSdef]; exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpy, hpM⟩, hprime⟩
      have hkSmall : k ∈ Small := by
        rw [hSmalldef]
        exact Finset.mem_biUnion.mpr ⟨p, hpS, Finset.mem_filter.mpr ⟨hkB, hdvd⟩⟩
      exact Finset.mem_union_left LargeSet hkSmall
    · set m := (4*k^2+1)/(p^2) with hmdef
      have hmeq : 4*k^2+1 = m*p^2 := by rw [hmdef]; exact (Nat.div_mul_cancel hdvd).symm
      have hmpos : 0 < m := by
        have h1 : 0 < m * p^2 := by rw [← hmeq]; positivity
        exact Nat.pos_of_mul_pos_right h1
      have hmreal : (m:ℝ) < 4*T+1 := by
        have hp0 : (0:ℝ) < (p:ℝ) := by have : (0:ℝ) ≤ T := le_of_lt hTpos; linarith
        have hp2gt : T^2 < (p:ℝ)^2 := by nlinarith
        have hmcast : (m:ℝ) * ((p:ℝ)^2) = 4*(k:ℝ)^2+1 := by exact_mod_cast hmeq.symm
        have hkx : (k:ℝ) ≤ (x:ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hkB).2
        have hle : 4*(k:ℝ)^2+1 ≤ 4*(x:ℝ)^2+1 := by nlinarith [sq_nonneg ((k:ℝ)-(x:ℝ))]
        have hT2one : (1:ℝ) ≤ T^2 := by nlinarith
        have hchain : (m:ℝ)*T^2 < (4*T+1)*T^2 := by
          calc (m:ℝ)*T^2 < (m:ℝ)*((p:ℝ)^2) :=
                mul_lt_mul_of_pos_left hp2gt (by exact_mod_cast hmpos)
            _ = 4*(k:ℝ)^2+1 := hmcast
            _ ≤ 4*(x:ℝ)^2+1 := hle
            _ = 4*T^3+1 := by rw [hT3]
            _ ≤ 4*T^3 + T^2 := by linarith
            _ = (4*T+1)*T^2 := by ring
        exact lt_of_mul_lt_mul_right hchain (le_of_lt hT2pos)
      have hmN : m ∈ Finset.range N := by
        apply Finset.mem_range.mpr
        have hceil : (4*T+1) ≤ (N:ℝ) := by rw [hNdef]; exact Nat.le_ceil _
        have hlt : (m:ℝ) < (N:ℝ) := lt_of_lt_of_le hmreal hceil
        exact_mod_cast hlt
      have hkLarge : k ∈ LargeSet := by
        rw [hLargeSetdef]
        exact Finset.mem_biUnion.mpr
          ⟨m, hmN, Finset.mem_filter.mpr ⟨hkB, p, hpy, hpx, hprime, hgt, hmeq⟩⟩
      exact Finset.mem_union_right Small hkLarge
  have hSmallcard : (Small.card : ℝ) ≤ 2*(x:ℝ)/(y:ℝ) + 2*T := by
    have hbi : Small.card ≤ ∑ p ∈ S, ((Finset.Ioc (x/2) x).filter (fun k => p^2 ∣ 4*k^2+1)).card := by
      rw [hSmalldef]; exact Finset.card_biUnion_le
    have hterm : ∀ p ∈ S, (((Finset.Ioc (x/2) x).filter (fun k => p^2 ∣ 4*k^2+1)).card : ℝ)
        ≤ 2*(x:ℝ)/(p:ℝ)^2 + 2 := by
      intro p hp
      have hpS : p ∈ Finset.Ioc y M := (Finset.mem_filter.mp hp).1
      have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
      have hp2 : 2 < p := by have h1 := (Finset.mem_Ioc.mp hpS).1; omega
      have hpp : 0 < p^2 := by positivity
      have hcard1 : ((Finset.Ioc (x/2) x).filter (fun k => p^2 ∣ 4*k^2+1)).card
          ≤ ((Finset.Ioc x (2*x)).filter (fun n => p^2 ∣ n^2+1)).card := by
        apply Finset.card_le_card_of_injOn (fun k => 2*k)
        · intro k hk
          obtain ⟨hkB, hkdvd⟩ := Finset.mem_filter.mp hk
          refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hB_low k hkB, hB_up k hkB⟩, ?_⟩
          have heq : (2*k)^2+1 = 4*k^2+1 := by ring
          rw [heq]; exact hkdvd
        · intro a _ b _ hab
          simp only at hab
          omega
      have hcard2 : ((Finset.Ioc x (2*x)).filter (fun n => p^2 ∣ n^2+1)).card ≤ (x/(p^2)+1)*2 := by
        calc _ ≤ (x/(p^2)+1) * ((Finset.range (p^2)).filter (fun r => p^2 ∣ r^2+1)).card :=
              interval_residue_count x (p^2) hpp
          _ ≤ (x/(p^2)+1)*2 := Nat.mul_le_mul_left _ (roots_sq_le_two p hprime hp2)
      calc (((Finset.Ioc (x/2) x).filter (fun k => p^2 ∣ 4*k^2+1)).card : ℝ)
          ≤ (((Finset.Ioc x (2*x)).filter (fun n => p^2 ∣ n^2+1)).card : ℝ) := by exact_mod_cast hcard1
        _ ≤ (((x/(p^2)+1)*2 : ℕ) : ℝ) := by exact_mod_cast hcard2
        _ = 2 * (((x/(p^2) : ℕ) : ℝ) + 1) := by push_cast; ring
        _ ≤ 2 * ((x:ℝ)/((p:ℝ)^2) + 1) := by
            have hdiv := cast_div_le_real x (p^2) hpp
            have hcast : ((p^2 : ℕ) : ℝ) = (p:ℝ)^2 := by push_cast; ring
            rw [hcast] at hdiv
            linarith
        _ = 2*(x:ℝ)/(p:ℝ)^2 + 2 := by ring
    have hsum : (∑ p ∈ S, (((Finset.Ioc (x/2) x).filter (fun k => p^2 ∣ 4*k^2+1)).card : ℝ))
        ≤ ∑ p ∈ S, (2*(x:ℝ)/(p:ℝ)^2 + 2) := Finset.sum_le_sum hterm
    have hsplit : (∑ p ∈ S, (2*(x:ℝ)/(p:ℝ)^2 + 2))
        = 2*(x:ℝ) * (∑ p ∈ S, (1/(p:ℝ)^2)) + 2*(S.card : ℝ) := by
      rw [Finset.sum_add_distrib]
      have e1 : ∑ p ∈ S, (2*(x:ℝ)/(p:ℝ)^2) = 2*(x:ℝ) * (∑ p ∈ S, (1/(p:ℝ)^2)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      have e2 : ∑ p ∈ S, (2:ℝ) = 2*(S.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
      rw [e1, e2]
    have hinv : (∑ p ∈ S, (1/(p:ℝ)^2)) ≤ 1/(y:ℝ) := by
      calc ∑ p ∈ S, (1/(p:ℝ)^2) ≤ ∑ n ∈ Finset.Ioc y M, ((1:ℝ)/(n:ℝ)^2) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro p hp; exact (Finset.mem_filter.mp hp).1
            · intro n _ _; positivity
        _ ≤ 1/(y:ℝ) := sum_inv_sq_le y M (by omega)
    have hScard : (S.card : ℝ) ≤ T := by
      have h1 : S.card ≤ (Finset.Ioc y M).card := Finset.card_le_card (Finset.filter_subset _ _)
      have h2 : (Finset.Ioc y M).card = M - y := Nat.card_Ioc y M
      have h3 : ((M - y : ℕ) : ℝ) ≤ (M:ℝ) := by exact_mod_cast Nat.sub_le M y
      have h4 : (M:ℝ) ≤ T := by rw [hMdef]; exact Nat.floor_le (le_of_lt hTpos)
      calc (S.card : ℝ) ≤ ((Finset.Ioc y M).card : ℝ) := by exact_mod_cast h1
        _ = ((M - y : ℕ) : ℝ) := by rw [h2]
        _ ≤ (M:ℝ) := h3
        _ ≤ T := h4
    calc (Small.card : ℝ)
        ≤ ((∑ p ∈ S, ((Finset.Ioc (x/2) x).filter (fun k => p^2 ∣ 4*k^2+1)).card : ℕ) : ℝ) := by
          exact_mod_cast hbi
      _ = ∑ p ∈ S, (((Finset.Ioc (x/2) x).filter (fun k => p^2 ∣ 4*k^2+1)).card : ℝ) := by
          push_cast; rfl
      _ ≤ ∑ p ∈ S, (2*(x:ℝ)/(p:ℝ)^2 + 2) := hsum
      _ = 2*(x:ℝ) * (∑ p ∈ S, (1/(p:ℝ)^2)) + 2*(S.card : ℝ) := hsplit
      _ ≤ 2*(x:ℝ) * (1/(y:ℝ)) + 2*T := by
          have h1 : (0:ℝ) ≤ 2*(x:ℝ) := by linarith
          exact add_le_add (mul_le_mul_of_nonneg_left hinv h1)
            (mul_le_mul_of_nonneg_left hScard (by norm_num))
      _ = 2*(x:ℝ)/(y:ℝ) + 2*T := by ring
  have hInner1 : ∀ m : ℕ, ((Finset.Ioc (x/2) x).filter (fun k =>
      ∃ p, y < p ∧ p ≤ 2*x ∧ Nat.Prime p ∧ T < (p:ℝ) ∧ 4*k^2+1 = m*p^2)).card ≤ 1 := by
    intro m
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haB, p, hpa⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbB, q, hqb⟩ := Finset.mem_filter.mp hb
    obtain ⟨hpa1, hpa2, hpa3, hpa4, hpa5⟩ := hpa
    obtain ⟨hqb1, hqb2, hqb3, hqb4, hqb5⟩ := hqb
    have hmpos : 0 < m := by
      have h1 : 0 < m * p^2 := by rw [← hpa5]; positivity
      exact Nat.pos_of_mul_pos_right h1
    have haI : x < 2*a := hB_low a haB
    have hbI : x < 2*b := hB_low b hbB
    have haU : 2*a ≤ 2*x := hB_up a haB
    have hbU : 2*b ≤ 2*x := hB_up b hbB
    have ha2 : (2*a)^2+1 = m*p^2 := by
      have h : (2*a)^2 = 4*a^2 := by ring
      rw [h]
      exact hpa5
    have hb2 : (2*b)^2+1 = m*q^2 := by
      have h : (2*b)^2 = 4*b^2 := by ring
      rw [h]
      exact hqb5
    have ha0 : 0 < 2*a := by omega
    have hb0 : 0 < 2*b := by omega
    rcases lt_trichotomy a b with h | h | h
    · exfalso
      have hpel := pell_spacing m (2*a) (2*b) p q hmpos ha0 (by omega) ha2 hb2
      omega
    · exact h
    · exfalso
      have hpel := pell_spacing m (2*b) (2*a) q p hmpos hb0 (by omega) hb2 ha2
      omega
  have hLargecard : (LargeSet.card : ℝ) ≤ 4*T + 2 := by
    have hbi : LargeSet.card ≤ ∑ m ∈ Finset.range N, ((Finset.Ioc (x/2) x).filter (fun k =>
        ∃ p, y < p ∧ p ≤ 2*x ∧ Nat.Prime p ∧ T < (p:ℝ) ∧ 4*k^2+1 = m*p^2)).card := by
      rw [hLargeSetdef]; exact Finset.card_biUnion_le
    have hsum : (∑ m ∈ Finset.range N, ((Finset.Ioc (x/2) x).filter (fun k =>
        ∃ p, y < p ∧ p ≤ 2*x ∧ Nat.Prime p ∧ T < (p:ℝ) ∧ 4*k^2+1 = m*p^2)).card)
        ≤ ∑ m ∈ Finset.range N, 1 := Finset.sum_le_sum (fun i _ => hInner1 i)
    calc (LargeSet.card : ℝ) ≤ ((∑ m ∈ Finset.range N, ((Finset.Ioc (x/2) x).filter (fun k =>
        ∃ p, y < p ∧ p ≤ 2*x ∧ Nat.Prime p ∧ T < (p:ℝ) ∧ 4*k^2+1 = m*p^2)).card : ℕ) : ℝ) := by
          exact_mod_cast hbi
      _ ≤ ((∑ m ∈ Finset.range N, (1:ℕ) : ℕ) : ℝ) := by exact_mod_cast hsum
      _ = (N:ℝ) := by simp
      _ ≤ 4*T+2 := by
          rw [hNdef]
          have hc := Nat.ceil_lt_add_one (R := ℝ) (show (0:ℝ) ≤ 4*T+1 by linarith)
          linarith
  calc (((Finset.Ioc (x/2) x).filter (fun k =>
        ((Finset.Ioc y (2*x)).filter (fun p => Nat.Prime p ∧ p^2 ∣ 4*k^2+1)).Nonempty)).card : ℝ)
      ≤ ((Small ∪ LargeSet).card : ℕ) := by exact_mod_cast (Finset.card_le_card hsub)
    _ ≤ ((Small.card + LargeSet.card : ℕ) : ℝ) := by exact_mod_cast (Finset.card_union_le _ _)
    _ = (Small.card : ℝ) + (LargeSet.card : ℝ) := by push_cast; ring
    _ ≤ (2*(x:ℝ)/(y:ℝ) + 2*T) + (4*T+2) := by linarith
    _ = (2*((x:ℝ)/(y:ℝ)) + 2*T) + (4*T+2) := by ring
    _ ≤ 8*((x:ℝ)/(y:ℝ) + T) := by
        have hxy : (0:ℝ) ≤ (x:ℝ)/(y:ℝ) := div_nonneg (le_of_lt hxpos) (le_of_lt hypos)
        have h2T : (2:ℝ) ≤ 2*T := by linarith
        linarith
