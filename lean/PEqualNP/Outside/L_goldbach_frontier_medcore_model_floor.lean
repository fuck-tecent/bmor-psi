import Mathlib

/- The finite Ramanujan identities, kernel identities, CRT and prime-power computations
used below adapt DFQDZZ's goldbach-proofs PR #316, commit
e4ab24712555ae8c2c926adf19d368a9fb392c35 (Apache-2.0). Original credits are
retained with the corresponding sections. The multiplicative averaging, sieve estimates,
convolution bounds and the moving-modulus-window argument are derived below. -/

section

/-!
# An explicit lower bound for the Ramanujan-weighted major-arc model

The arithmetic and kernel estimates below are extracted from DFQDZZ's
goldbach-proofs PR #316 (commit e4ab24712555ae8c2c926adf19d368a9fb392c35,
Apache-2.0). The CRT and prime-power computations are credited below.
The estimate applies to every positive even target.
-/

open Finset Filter MeasureTheory

namespace GoldbachExplicitModeledMajor
noncomputable section

def phase (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def cutoff (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

def kernel (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ range (n + 1), phase ((k : ℝ) * β)

def width (n q : ℕ) : ℝ := (cutoff n : ℝ) / ((q : ℝ) * n)

def kernelMass (n : ℕ) (b : ℝ) : ℝ := ∫ β in -b..b, ‖kernel n β‖ ^ 2

private theorem continuous_kernel (n : ℕ) : Continuous (kernel n) := by
  unfold kernel phase
  fun_prop

theorem kernelMass_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (n : ℕ) :
    kernelMass n u ≤ kernelMass n v :=
  intervalIntegral.integral_mono_interval (neg_le_neg huv) (by linarith) huv
    (Eventually.of_forall fun _ => sq_nonneg _) (((continuous_kernel n).norm.pow 2).intervalIntegrable _ _)

private theorem kernel_on_zero_arc {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (1 / (6 * (n : ℝ)))) : (n : ℝ) / 2 ≤ ‖kernel n t‖ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnt := (le_div_iff₀ (show 0 < 6 * (n : ℝ) by positivity)).mp ht.2
  have hc (k : ℕ) (hk : k ∈ range (n + 1)) :
      1 / 2 ≤ (phase ((k : ℝ) * t)).re := by
    rw [phase, Complex.exp_ofReal_mul_I_re, ← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) ht.1)
    · linarith [Real.pi_pos]
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hkt := mul_le_mul_of_nonneg_right hk' ht.1
    nlinarith only [mul_le_mul_of_nonneg_left hnt Real.pi_pos.le,
      mul_le_mul_of_nonneg_left hkt Real.pi_pos.le]
  calc
    _ ≤ ∑ _k ∈ range (n + 1), (1 / 2 : ℝ) := by simp; linarith
    _ ≤ ∑ k ∈ range (n + 1), (phase ((k : ℝ) * t)).re := sum_le_sum hc
    _ = (kernel n t).re := by rw [kernel, Complex.re_sum]
    _ ≤ _ := Complex.re_le_norm _

/-- Each width at least 1/(6n) captures a positive linear amount of the model's mass. -/
theorem kernelMass_floor {n : ℕ} (hn : 0 < n) {b : ℝ} (hb : 1 / (6 * (n : ℝ)) ≤ b) :
    (n : ℝ) / 24 ≤ kernelMass n b := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := 1 / (6 * (n : ℝ))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hb0 : 0 ≤ b := hu.trans hb
  have hc := (continuous_kernel n).norm.pow 2
  calc
    _ = ∫ _t in (0 : ℝ)..u, ((n : ℝ) / 2) ^ 2 := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul, u]
      field_simp
      ring
    _ ≤ ∫ t in (0 : ℝ)..u, ‖kernel n t‖ ^ 2 :=
      intervalIntegral.integral_mono_on hu (by simp) (hc.intervalIntegrable _ _) fun _ ht =>
        pow_le_pow_left₀ (by positivity) (kernel_on_zero_arc hn ht) 2
    _ ≤ _ := intervalIntegral.integral_mono_interval (neg_nonpos.mpr hb0) hu hb
      (Eventually.of_forall fun _ => sq_nonneg _) (hc.intervalIntegrable _ _)

theorem cutoff_positive (n : ℕ) : 1 ≤ cutoff n :=
  Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n+2)).ne')

theorem width_nonneg (n q : ℕ) : 0 ≤ width n q := by unfold width; positivity

end
end GoldbachExplicitModeledMajor

/- The finite CRT and prime-power calculations below adapt goldbach-proofs PRs #207 (XianWu18) and #203 (wzhxzkk), Apache-2.0. -/
namespace GoldbachExplicitModeledMajor.RamanujanCRT
private def unitsBelow (m : ℕ) := (Finset.range m).filter (fun a => Nat.Coprime a m)

private theorem unitsBelow_card (m : ℕ) : (unitsBelow m).card = m.totient := by
  unfold unitsBelow
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (fun _ => Nat.coprime_comm)

private noncomputable def phase (m h a : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((h : ℝ) * a / m) : ℝ) : ℂ) * Complex.I)

private theorem phase_character (m h a : ℕ) [NeZero m] :
    phase m h a = ZMod.stdAddChar ((h : ZMod m) * (a : ZMod m)) := by
  have ch := ZMod.stdAddChar_coe (N := m) ((h * a : ℕ) : ℤ)
  push_cast at ch
  rw [ch]
  unfold phase
  push_cast
  congr 1
  ring

private theorem phase_modulus (m h a : ℕ) [NeZero m] :
    phase m h (a % m) = phase m h a := by
  simp only [phase_character, ZMod.natCast_mod]

private theorem phase_pair (q r h a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    phase (q*r) h ((r*a + q*b) % (q*r)) = phase q h a * phase r h b := by
  have : NeZero (q*r) := ⟨Nat.ne_of_gt (Nat.mul_pos hq hr)⟩
  rw [phase_modulus]
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have qnz : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have rnz : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

theorem crt :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ q r h, 0<q → 0<r → Nat.Coprime q r → ram (q*r) h=ram q h*ram r h := by
  dsimp only
  intro q r h hq hr cop
  let combine (x : ℕ × ℕ) := (r*x.1 + q*x.2) % (q*r)
  let pairs := unitsBelow q ×ˢ unitsBelow r
  have member {m a : ℕ} : a ∈ unitsBelow m ↔ a < m ∧ Nat.Coprime a m := by
    simp only [unitsBelow, Finset.mem_filter, Finset.mem_range]
  have maps : pairs.image combine ⊆ unitsBelow (q*r) := by
    intro z hz
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    apply member.mpr
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hq hr), ?_⟩
    change Nat.gcd ((r*a + q*b) % (q*r)) (q*r) = 1
    rw [← Nat.gcd_rec]
    change Nat.Coprime (q*r) (r*a + q*b)
    apply Nat.coprime_mul_iff_left.mpr
    constructor
    · rw [Nat.coprime_add_mul_left_right]
      exact cop.mul_right (member.mp ha).2.symm
    · rw [add_comm, Nat.coprime_add_mul_left_right]
      exact cop.symm.mul_right (member.mp hb).2.symm
  have injective : Set.InjOn combine (↑pairs) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
    have congruence : r*a + q*b ≡ r*c + q*d [MOD q*r] := he
    apply Prod.ext
    · have hmod := congruence.of_dvd (dvd_mul_right q r)
      have reduced : r*a ≡ r*c [MOD q] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop reduced).eq_of_lt_of_lt
        (member.mp ha).1 (member.mp hc).1
    · have hmod := congruence.of_dvd (dvd_mul_left r q)
      have reduced : q*b ≡ q*d [MOD r] := by
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod] using hmod
      exact (Nat.ModEq.cancel_left_of_coprime cop.symm reduced).eq_of_lt_of_lt
        (member.mp hb).1 (member.mp hd).1
  have covers : pairs.image combine = unitsBelow (q*r) := by
    apply Finset.eq_of_subset_of_card_le maps
    rw [Finset.card_image_of_injOn injective, unitsBelow_card, Nat.totient_mul cop]
    simp only [pairs, Finset.card_product, unitsBelow_card]
    exact le_rfl
  change (∑ z ∈ unitsBelow (q*r), phase (q*r) h z) =
    (∑ a ∈ unitsBelow q, phase q h a) * ∑ b ∈ unitsBelow r, phase r h b
  rw [← covers, Finset.sum_image injective, Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  exact Finset.sum_congr rfl (fun x _ => phase_pair q r h x.1 x.2 hq hr)

end GoldbachExplicitModeledMajor.RamanujanCRT
namespace GoldbachExplicitModeledMajor.RamanujanPower
open Finset

theorem primePower :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ p j h, Nat.Prime p → ram (p^(j+1)) h = (if p^(j+1) ∣ h then ((p^(j+1):ℕ):ℂ) else 0) - (if p^j ∣ h then ((p^j:ℕ):ℂ) else 0) := by
  intro E ram p j h hp
  have full (q : ℕ) (hq : 0 < q) :
      ∑ a ∈ range q, E ((h:ℝ) * a / q) = if q ∣ h then (q:ℂ) else 0 := by
    let : NeZero q := ⟨hq.ne'⟩
    calc
      _ = ∑ x : ZMod q, ZMod.stdAddChar ((h : ZMod q) * x) := by
        apply Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q))
        · intro a ha
          exact mem_univ _
        · intro a ha b hb hab
          simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
            ZMod.val_natCast_of_lt (mem_range.mp hb)] using congrArg ZMod.val hab
        · intro x _
          exact ⟨x.val, mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
        · intro a _
          have cast_eq : (h : ZMod q) * a = ((h * a : ℕ) : ℤ) := by push_cast; rfl
          rw [cast_eq, ZMod.stdAddChar_coe]
          dsimp [E]
          congr 1
          push_cast
          ring
      _ = _ := by
        by_cases hd : q ∣ h
        · have hz : (h : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff h q).mpr hd
          simp [hd, hz, ZMod.card]
        · have hz : (h : ZMod q) ≠ 0 := fun hz => hd ((ZMod.natCast_eq_zero_iff h q).mp hz)
          rw [ite_eq_right hd]
          exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hz)
  let m := p ^ j
  have hm : 0 < m := pow_pos hp.pos _
  let mult := (range m).image (fun b => p * b)
  have hsub : mult ⊆ range (p^(j+1)) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    rw [mem_range, pow_succ']
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hp.pos
  have hfilter : (range (p^(j+1))).filter (fun a => Nat.Coprime a (p^(j+1))) =
      range (p^(j+1)) \ mult := by
    rw [sdiff_eq_filter]
    apply filter_congr
    intro a ha
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos j), Nat.coprime_comm, hp.coprime_iff_not_dvd]
    apply not_congr
    constructor
    · rintro ⟨b, rfl⟩
      apply mem_image.mpr
      refine ⟨b, mem_range.mpr ?_, rfl⟩
      rw [mem_range, pow_succ'] at ha
      exact (Nat.mul_lt_mul_left hp.pos).mp ha
    · intro ha'
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha'
      exact dvd_mul_right _ _
  have removed : ∑ a ∈ mult, E ((h:ℝ)*a/(p^(j+1):ℕ)) =
      ∑ b ∈ range m, E ((h:ℝ)*b/m) := by
    rw [show mult = (range m).image (fun b => p * b) from rfl,
      sum_image (mul_right_injective₀ hp.ne_zero).injOn]
    apply sum_congr rfl
    intro b _
    congr 1
    rw [pow_succ']
    push_cast
    dsimp [m]
    push_cast
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
  change ∑ a ∈ (range (p^(j+1))).filter _, E ((h:ℝ)*a/(p^(j+1):ℕ)) = _
  rw [hfilter, ← full _ (pow_pos hp.pos (j+1)), ← full _ hm, ← removed]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

end GoldbachExplicitModeledMajor.RamanujanPower

namespace GoldbachExplicitModeledMajor

open Finset
open scoped ComplexConjugate
noncomputable section

def ram (q h : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a => a.Coprime q), phase ((h : ℝ) * a / q)

theorem ram_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (h : ℕ) :
    ram (q * r) h = ram q h * ram r h := RamanujanCRT.crt q r h hq hr hc

theorem ram_primePower (p j h : ℕ) (hp : p.Prime) :
    ram (p ^ (j + 1)) h = (if p ^ (j + 1) ∣ h then ((p ^ (j + 1) : ℕ) : ℂ) else 0) -
      (if p ^ j ∣ h then ((p ^ j : ℕ) : ℂ) else 0) := RamanujanPower.primePower p j h hp

theorem ram_one (h : ℕ) : ram 1 h = 1 := by simp [ram, phase]

theorem ram_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    ram p h = (if p ∣ h then (p : ℂ) else 0) - 1 := by
  simpa using ram_primePower p 0 h hp

private theorem ram_unit_power {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [ram_primePower p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]

def localCoefficient (p n : ℕ) : ℝ :=
  if p ∣ n then 1 / ((p : ℝ) - 1) else -(1 / ((p : ℝ) - 1) ^ 2)

def coefficient (q n : ℕ) : ℂ := (ram q 1 / (q.totient : ℂ)) ^ 2 * conj (ram q n)

theorem coefficient_one (n : ℕ) : coefficient 1 n = 1 := by simp [coefficient, ram_one]

theorem coefficient_mul {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hc : q.Coprime r) (n : ℕ) :
    coefficient (q * r) n = coefficient q n * coefficient r n := by
  unfold coefficient
  rw [ram_mul hq hr hc, ram_mul hq hr hc, Nat.totient_mul hc, Nat.cast_mul, map_mul]
  ring

theorem coefficient_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    coefficient p n = (localCoefficient p n : ℂ) := by
  have hone : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
  have hne : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [coefficient, ram_prime hp, ram_prime hp, ite_eq_right hone, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  by_cases hd : p ∣ n <;> simp [localCoefficient, hd] <;> field_simp

theorem coefficient_higher_power {p : ℕ} (hp : p.Prime) (k n : ℕ) :
    coefficient (p ^ (k + 2)) n = 0 := by
  have h := ram_unit_power hp (k + 1) 1 (by simp)
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] at h
  simp [coefficient, h]

end
end GoldbachExplicitModeledMajor

namespace GoldbachExplicitModeledMajor

open Finset

noncomputable section
theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : coefficient q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact coefficient_higher_power hp j n
  | coprime a b ha hb hab ia ib =>
    rw [coefficient_mul (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h,h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]

theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    coefficient (∏ p ∈ s, p) n = ((∏ p ∈ s, localCoefficient p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [prod_insert hp, prod_insert hp, coefficient_mul hprime.pos (prod_pos fun r hr => (hs' r hr).pos) hcop,
      coefficient_prime hprime, ih hs', Complex.ofReal_mul]


end
end GoldbachExplicitModeledMajor

end

section

namespace BandTail
open Finset GoldbachExplicitModeledMajor
noncomputable section

private theorem coprime_prod_factors {p : ℕ} {s : Finset ℕ} (hp : p.Prime)
    (hs : ∀ r∈s, r.Prime) (hps : p∉s) : p.Coprime (∏ r∈s, r) :=
  Nat.coprime_prod_right_iff.mpr (fun r hr => (Nat.coprime_primes hp (hs r hr)).mpr (fun e => hps (e ▸ hr)))

theorem coeff_norm_le (q n : ℕ) (hq : 0<q) :
    ‖coefficient q n‖ ≤ 1/(q.totient:ℝ) := by
  by_cases hsf : Squarefree q
  · suffices H : ∀ s : Finset ℕ, (∀ p∈s, p.Prime) →
        ‖coefficient (∏ p∈s, p) n‖ ≤ 1/((∏ p∈s, p).totient:ℝ) by
      simpa only [Nat.prod_primeFactors_of_squarefree hsf] using H q.primeFactors
        (fun _ h => Nat.prime_of_mem_primeFactors h)
    intro s
    induction s using Finset.induction_on with
    | empty => simp [coefficient_one]
    | @insert p s hp ih =>
      intro hs
      have hprime := hs p (mem_insert_self ..)
      have hs' (r : ℕ) (hr : r∈s) := hs r (mem_insert_of_mem hr)
      have hc := coprime_prod_factors hprime hs' hp
      have hpos : 0<∏ r∈s, r := prod_pos fun i hi => (hs' i hi).pos
      rw [prod_insert hp,coefficient_mul hprime.pos hpos hc,Nat.totient_mul hc,Nat.cast_mul,norm_mul,
        coefficient_prime hprime, Complex.norm_real,Real.norm_eq_abs]
      have hR : (2:ℝ)≤p := by exact_mod_cast hprime.two_le
      have hp1 : 0≤(p:ℝ)-1 := by linarith
      have hf : |localCoefficient p n| ≤ 1/(p.totient:ℝ) := by
        rw [Nat.totient_prime hprime,Nat.cast_sub hprime.one_le,Nat.cast_one]
        dsimp [localCoefficient]
        split_ifs
        · rw [abs_of_nonneg (by positivity)]
        · rw [abs_neg,abs_of_nonneg (by positivity)]
          apply one_div_le_one_div_of_le (by linarith)
          nlinarith [mul_nonneg (show 0≤(p:ℝ)-1 by linarith) (show 0≤(p:ℝ)-2 by linarith)]
      exact (mul_le_mul hf (ih hs') (norm_nonneg _) (by positivity)).trans_eq (by ring)
  · rw [coefficient_not_squarefree n hq hsf, norm_zero]; positivity

theorem coeff_bad_prime (p r n : ℕ) (hp : p.Prime) (hpn : ¬p∣n) (hr : 0<r) :
    ‖coefficient (p*r) n‖ ≤ 1/((p:ℝ)-1)^2 * (1/(r.totient:ℝ)) := by
  by_cases hc : p.Coprime r
  · rw [coefficient_mul hp.pos hr hc,norm_mul,coefficient_prime hp,Complex.norm_real,Real.norm_eq_abs,
      localCoefficient,if_neg hpn,abs_neg,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (coeff_norm_le r n hr) (by positivity)
  · have hpr : p∣r := by simpa [hp.coprime_iff_not_dvd] using hc
    have hsf : ¬Squarefree (p*r) := fun h =>
      Nat.squarefree_iff_prime_squarefree.mp h p hp (Nat.mul_dvd_mul_left _ hpr)
    rw [coefficient_not_squarefree n (Nat.mul_pos hp.pos hr) hsf,norm_zero]
    positivity

theorem good_product {s : Finset ℕ} {n : ℕ} (hs : ∀ p∈s, p.Prime ∧ p∣n) :
    coefficient (∏ p∈s, p) n = ((1/((∏ p∈s, p).totient:ℝ):ℝ):ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := (hs p (mem_insert_self ..)).1
    have hpn := (hs p (mem_insert_self ..)).2
    have hs' (r : ℕ) (hr : r∈s) := hs r (mem_insert_of_mem hr)
    have hc := coprime_prod_factors hprime (fun r hr => (hs' r hr).1) hp
    have hpos : 0<∏ r∈s, r := prod_pos fun i hi => (hs' i hi).1.pos
    rw [prod_insert hp,coefficient_mul hprime.pos hpos hc,Nat.totient_mul hc,ih hs',coefficient_prime hprime,
      localCoefficient,if_pos hpn,Nat.totient_prime hprime,Nat.cast_mul,Nat.cast_sub hprime.one_le,Nat.cast_one,←Complex.ofReal_mul]
    congr 1
    simp only [div_eq_mul_inv, mul_inv, mul_pow, inv_pow]; ring

theorem bad_product {s : Finset ℕ} {n : ℕ} (hs : ∀ p∈s, p.Prime ∧ ¬p∣n) :
    coefficient (∏ p∈s, p) n =
      (((ArithmeticFunction.moebius (∏ p∈s, p):ℝ)/((∏ p∈s, p).totient:ℝ)^2:ℝ):ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := (hs p (mem_insert_self ..)).1
    have hpn := (hs p (mem_insert_self ..)).2
    have hs' (r : ℕ) (hr : r∈s) := hs r (mem_insert_of_mem hr)
    have hc := coprime_prod_factors hprime (fun r hr => (hs' r hr).1) hp
    have hpos : 0<∏ r∈s, r := prod_pos fun i hi => (hs' i hi).1.pos
    rw [prod_insert hp,coefficient_mul hprime.pos hpos hc,Nat.totient_mul hc,ih hs',coefficient_prime hprime,
      localCoefficient,if_neg hpn,Nat.totient_prime hprime,Nat.cast_mul,Nat.cast_sub hprime.one_le,Nat.cast_one,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,ArithmeticFunction.moebius_apply_prime hprime,←Complex.ofReal_mul]
    push_cast
    simp only [div_eq_mul_inv, mul_inv, mul_pow, inv_pow]; ring

theorem coefficient_factorization (q n : ℕ) (hsq : Squarefree q) (hn : 0<n) :
    ∃ d m : ℕ, q=d*m ∧ d∣n ∧ m.Coprime n ∧
      coefficient q n = (((ArithmeticFunction.moebius m:ℝ)/((d.totient:ℝ)*(m.totient:ℝ)^2):ℝ):ℂ) := by
  classical
  let G := q.primeFactors.filter (fun p => p∣n)
  let B := q.primeFactors \ G
  let d := ∏ p∈G, p
  let m := ∏ p∈B, p
  have hG (p : ℕ) (hp : p∈G) : p.Prime ∧ p∣n := by
    obtain ⟨h1,h2⟩ := mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors h1,h2⟩
  have hB (p : ℕ) (hp : p∈B) : p.Prime ∧ ¬p∣n := by
    obtain ⟨h1,h2⟩ := mem_sdiff.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors h1,fun hd => h2 (mem_filter.mpr ⟨h1,hd⟩)⟩
  have hqm : q=d*m := by
    have h := Finset.prod_sdiff (f:=id) (s₁:=G) (s₂:=q.primeFactors) (Finset.filter_subset ..)
    simpa [d,m,B,Nat.prod_primeFactors_of_squarefree hsq,mul_comm] using h.symm
  have hdn : d∣n := by
    have hsub : G ⊆ n.primeFactors := fun p hp => Nat.mem_primeFactors.mpr ⟨(hG p hp).1,(hG p hp).2,hn.ne'⟩
    exact dvd_trans (Finset.prod_dvd_prod_of_subset G n.primeFactors id hsub) (Nat.prod_primeFactors_dvd n)
  have hmn : m.Coprime n := Nat.coprime_prod_left_iff.mpr fun p hp => (hB p hp).1.coprime_iff_not_dvd.mpr (hB p hp).2
  refine ⟨d,m,hqm,hdn,hmn,?_⟩
  rw [hqm,coefficient_mul (prod_pos (fun p hp => (hG p hp).1.pos)) (prod_pos (fun p hp => (hB p hp).1.pos))
    (hmn.of_dvd_right hdn).symm, show coefficient d n = _ from good_product hG,
    show coefficient m n = _ from bad_product hB,←Complex.ofReal_mul]
  congr 1
  simp only [div_eq_mul_inv, mul_inv, mul_pow, inv_pow]; ring
end
end BandTail

end

section

namespace BandTail
open Finset ArithmeticFunction GoldbachExplicitModeledMajor
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
noncomputable section

def smooth (n k : ℕ) : Prop := ∀ p ∈ k.primeFactors, p∣n
instance smoothDec (n k : ℕ) : Decidable (smooth n k) := by unfold smooth; infer_instance

def g (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k=0 then 0 else if smooth n k then 1 else 0,by simp⟩

@[simp] theorem g_one (n : ℕ) : g n 1=1 := by simp [g,smooth]
theorem g_mul (n a b : ℕ) : g n (a*b)=g n a*g n b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hs : smooth n (a*b) ↔ smooth n a ∧ smooth n b := by
    simp only [smooth,Nat.primeFactors_mul ha hb,mem_union]
    constructor
    · intro h; exact ⟨fun p hp => h p (Or.inl hp),fun p hp => h p (Or.inr hp)⟩
    · rintro ⟨x,y⟩ p (h|h)
      · exact x p h
      · exact y p h
  simp only [g,coe_mk, mul_ne_zero ha hb,ha,hb,ite_false]
  by_cases h1 : smooth n a <;> by_cases h2 : smooth n b <;> simp [hs,h1,h2]
theorem g_mult (n : ℕ) : IsMultiplicative (g n) := ⟨g_one n, fun {_ _} _ => g_mul n _ _⟩
theorem g_prime (n p : ℕ) (hp : p.Prime) : g n p=if p∣n then 1 else 0 := by
  simp [g,smooth,hp.ne_zero,hp.primeFactors]

def F (n : ℕ) : ArithmeticFunction ℝ := ⟨fun q => (q:ℝ)*(coefficient q n).re,by simp⟩

theorem coeff_real {q : ℕ} (hq : 0<q) (n : ℕ) : coefficient q n = (((coefficient q n).re:ℝ):ℂ) := by
  by_cases hsf : Squarefree q
  · have he := coefficient_prime_product n q.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    rw [Nat.prod_primeFactors_of_squarefree hsf] at he
    rw [he]; rfl
  · rw [coefficient_not_squarefree n hq hsf]; simp
theorem F_mult (n : ℕ) : IsMultiplicative (F n) := by
  refine ⟨by simp [F,coefficient_one],fun {a b} hab => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hzero : (coefficient a n).im=0 := by rw [coeff_real ha.bot_lt n]; rfl
  simp [F,coefficient_mul ha.bot_lt hb.bot_lt hab,Complex.mul_re,hzero]
  ring
theorem F_prime (n p : ℕ) (hp : p.Prime) : F n p=(p:ℝ)*localCoefficient p n := by simp [F,coefficient_prime hp]
theorem F_higher (n p j : ℕ) (hp : p.Prime) : F n (p^(j+2))=0 := by simp [F,coefficient_higher_power hp j n]

def invG (n : ℕ) : ArithmeticFunction ℝ := pmul (μ : ArithmeticFunction ℝ) (g n)
def h (n : ℕ) : ArithmeticFunction ℝ := invG n * F n

theorem h_mult (n : ℕ) : IsMultiplicative (h n) :=
  (isMultiplicative_moebius.intCast.pmul (g_mult n)).mul (F_mult n)

theorem inverse_id (n : ℕ) : g n * invG n = 1 := by
  ext k
  have heq : (g n*invG n) k = g n k * (((ζ : ArithmeticFunction ℝ)*μ) k) := by
    simp only [ArithmeticFunction.mul_apply,Finset.mul_sum,invG,pmul_apply]
    apply Finset.sum_congr rfl
    intro ab hab
    have h0 : 0<ab.1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hab)
    have hG : g n k=g n ab.1*g n ab.2 := (Nat.mem_divisorsAntidiagonal.mp hab).1 ▸ g_mul n ab.1 ab.2
    rw [hG]
    simp [zeta_apply,h0.ne']; ring
  rw [heq,coe_zeta_mul_coe_moebius]
  by_cases hk : k=1 <;> simp [ArithmeticFunction.one_apply,hk]
theorem convolution (n : ℕ) : F n = g n*h n := by rw [h,←mul_assoc,inverse_id,one_mul]

theorem h_prime_recurrence (n p j : ℕ) (hp : p.Prime) :
    h n (p^(j+1))=F n (p^(j+1))-g n p*F n (p^j) := by
  let q := p^(j+1)
  have hq : q≠0 := pow_ne_zero _ hp.ne_zero
  let v := fun d : ℕ => invG n d * F n (q/d)
  have hv : h n q = ∑ d ∈ q.divisors, v d := by
    rw [h,ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b : ℕ => invG n a * F n b)]
  have h1 : ({1,p}:Finset ℕ) ⊆ q.divisors := by
    intro a ha
    simp only [mem_insert,mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨one_dvd _,hq⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_pow_self _ (by omega),hq⟩
  have hsum : ∑ d ∈ q.divisors,v d = ∑ d ∈ ({1,p}:Finset ℕ),v d := by
    symm; apply sum_subset h1
    intro d hd hn
    obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow hp).mp (Nat.dvd_of_mem_divisors hd)
    by_cases hi0 : i=0
    · exfalso; apply hn; simp [he,hi0]
    by_cases hi1 : i=1
    · exfalso; apply hn; simp [he,hi1]
    have hm : μ d=0 := by rw [he, moebius_apply_prime_pow hp hi0,if_neg hi1]
    simp [v,invG,pmul_apply,intCoe_apply,hm]
  have hdiv : q/p=p^j := by dsimp [q]; rw [pow_succ,Nat.mul_div_cancel _ hp.pos]
  change h n q = _
  rw [hv,hsum,Finset.sum_insert (by simpa using hp.ne_one.symm : (1:ℕ)∉({p}:Finset ℕ)),Finset.sum_singleton]
  simp [v,invG,pmul_apply,intCoe_apply,moebius_apply_prime hp,hdiv,q]
  ring

theorem h_prime (n p : ℕ) (hp : p.Prime) : h n p =
    if p∣n then 1/((p:ℝ)-1) else -(p:ℝ)/((p:ℝ)-1)^2 := by
  have he := h_prime_recurrence n p 0 hp
  have he1 : F n 1=1 := (F_mult n).map_one
  simp only [Nat.zero_add,pow_one,pow_zero,he1,F_prime n p hp,g_prime n p hp,mul_one] at he
  rw [he]; dsimp [localCoefficient]
  have hr1 : (p:ℝ)-1≠0 := by
    have ht : (2:ℝ)≤p := by exact_mod_cast hp.two_le
    linarith
  split_ifs <;> field_simp <;> ring
theorem h_square (n p : ℕ) (hp : p.Prime) : h n (p^2) =
    if p∣n then -(p:ℝ)/((p:ℝ)-1) else 0 := by
  have he := h_prime_recurrence n p 1 hp
  rw [F_higher n p 0 hp,pow_one,g_prime n p hp,F_prime n p hp] at he
  rw [he]; dsimp [localCoefficient]; split_ifs <;> ring
theorem h_cube (n p j : ℕ) (hp : p.Prime) : h n (p^(j+3))=0 := by
  have he := h_prime_recurrence n p (j+2) hp
  rw [F_higher n p j hp,show j+2+1=(j+1)+2 by omega,F_higher n p (j+1) hp] at he
  simpa [show j+2+1=j+3 by omega] using he

end
end BandTail

end

section

namespace BandTail
open Finset
noncomputable section

private theorem pairPos {q : ℕ} {v : ℕ × ℕ} (hv : v ∈ q.divisorsAntidiagonal) : 0<v.1 ∧ 0<v.2 :=
  ⟨Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hv),
   Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hv)⟩

theorem unpair (U : ℕ) (F : ℕ×ℕ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∑ q ∈ Icc 1 U, ∑ v ∈ q.divisorsAntidiagonal, F v) ≤
      ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 U, F (a,b) := by
  classical
  let S := Icc 1 U
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
        hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro h; exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp h).2,by omega⟩
  calc
    _ = ∑ q ∈ S, ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), F v :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), F v :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ v ∈ S ×ˢ S, F v := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun v _ _ => hF v)
    _ = _ := Finset.sum_product _ _ _

theorem invSquares (U : ℕ) : (∑ k ∈ Icc 1 U, ((k:ℝ)^2)⁻¹) ≤ 2 := by
  rcases U with _ | u
  · simp
  · have hUU : 1≤u+1 := by omega
    have H := sum_Ioc_inv_sq_le_sub (α:=ℝ) (by decide : 1 ≠ 0) hUU
    rw [← Finset.sum_Ioc_add_eq_sum_Icc hUU]
    norm_num at H ⊢
    linarith [show 0 ≤ ((u:ℝ)+1)⁻¹ by positivity]

theorem scaledInvSquares (X v U : ℕ) (hv : 0<v) :
    (X:ℝ) * (∑ k ∈ Icc 1 U, if X<v*k then ((k:ℝ)^2)⁻¹ else 0) ≤ 2*v := by
  by_cases h : X<v
  · have hc : (∑ k ∈ Icc 1 U, if X<v*k then ((k:ℝ)^2)⁻¹ else 0) ≤ 2 :=
      (sum_le_sum fun k _ => by split_ifs <;> first | rfl | positivity).trans (invSquares U)
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans (by exact_mod_cast (by omega : X*2 ≤ 2*v))
  have hm : 0<X/v := Nat.div_pos (by omega) hv
  have he : ∑ k ∈ Icc 1 U, (if X<v*k then ((k:ℝ)^2)⁻¹ else 0) =
      ∑ k ∈ Ioc (X/v) U, ((k:ℝ)^2)⁻¹ := by
    rw [← sum_filter]
    congr 1
    ext k
    simp only [mem_filter,mem_Icc,mem_Ioc,Nat.div_lt_iff_lt_mul hv]
    constructor <;> rintro h
    · exact ⟨by simpa [mul_comm] using h.2,h.1.2⟩
    · exact ⟨⟨by cases k <;> simp_all, h.2⟩,by simpa [mul_comm] using h.1⟩
  rw [he]
  by_cases hU : X/v≤U
  · have H := sum_Ioc_inv_sq_le_sub (α:=ℝ) hm.ne' hU
    have hc := H.trans (sub_le_self _ (by positivity))
    have hlim := Nat.div_add_mod X v
    have hmod := Nat.mod_lt X hv
    have hle : X ≤ 2*v*(X/v) := by nlinarith only [hlim,hmod,Nat.mul_le_mul_left v hm]
    have hr : 0<((X/v:ℕ):ℝ) := by exact_mod_cast hm
    refine (mul_le_mul_of_nonneg_left hc (by positivity : 0≤(X:ℝ))).trans ?_
    rw [←div_eq_mul_inv,div_le_iff₀ hr]
    exact_mod_cast hle
  · simp [Finset.Ioc_eq_empty_of_le (by omega : U≤X/v)]

theorem totient_series (U : ℕ) : (∑ q ∈ Icc 1 U, 1/((q:ℝ)*q.totient)) ≤ 4 := by
  let F := fun ab : ℕ×ℕ => ((ab.1:ℝ)^2)⁻¹ * ((ab.2:ℝ)^2)⁻¹
  calc
    _ ≤ ∑ q ∈ Icc 1 U, ∑ ab ∈ q.divisorsAntidiagonal, F ab := by
      apply sum_le_sum
      intro q hq
      have hq0 := (mem_Icc.mp hq).1
      have hφ := Nat.totient_pos.mpr hq0
      have hcount : q ≤ q.divisors.card*q.totient := calc
        _ = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
        _ ≤ ∑ _ ∈ q.divisors, q.totient := sum_le_sum fun d hd => Nat.le_of_dvd hφ (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
        _ = _ := by simp
      calc
        _ ≤ (q.divisors.card:ℝ)/(q:ℝ)^2 := by
          have hr : (0:ℝ)<q := by exact_mod_cast hq0
          have hφr : (0:ℝ)<q.totient := by exact_mod_cast hφ
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          have hc : (q:ℝ)≤q.divisors.card*q.totient := by exact_mod_cast hcount
          nlinarith only [mul_le_mul_of_nonneg_left hc hr.le]
        _ = ∑ ab ∈ q.divisorsAntidiagonal, ((q:ℝ)^2)⁻¹ := by
          rw [Nat.sum_divisorsAntidiagonal (fun _ _ => ((q:ℝ)^2)⁻¹)]; simp [div_eq_mul_inv]
        _ = _ := by
          apply sum_congr rfl; intro ab hab
          dsimp [F]
          rw [←(Nat.mem_divisorsAntidiagonal.mp hab).1,Nat.cast_mul,mul_pow,mul_inv]
    _ ≤ ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 U, F (a,b) := unpair U F (by intro x; dsimp [F]; positivity)
    _ = (∑ a ∈ Icc 1 U, ((a:ℝ)^2)⁻¹)^2 := by dsimp [F]; rw [sq,Finset.sum_mul_sum]
    _ ≤ 4 := by
      have h := pow_le_pow_left₀ (by exact sum_nonneg (fun _ _ => by positivity)) (invSquares U) 2
      norm_num at h ⊢; exact h

theorem totient_tail (X v U : ℕ) (hv : 0<v) :
    (X:ℝ)*(∑ q ∈ Icc 1 U, if X<v*q then 1/((q:ℝ)*q.totient) else 0) ≤ 8*v := by
  let F := fun ab : ℕ×ℕ => (1 / ((ab.1:ℝ)^2*ab.1.totient)) *
      (if X<v*ab.1*ab.2 then ((ab.2:ℝ)^2)⁻¹ else 0)
  have hF (x : ℕ×ℕ) : 0≤F x := by dsimp [F]; split_ifs <;> positivity
  have hh (q : ℕ) (hq : q ∈ Icc 1 U) :
      (if X<v*q then 1/((q:ℝ)*q.totient) else 0) ≤ ∑ ab ∈ q.divisorsAntidiagonal, F ab := by
    by_cases h : X<v*q
    · rw [if_pos h]
      have hq0 := (mem_Icc.mp hq).1
      have hqR : (0:ℝ)<q := by exact_mod_cast hq0
      have hφR : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
      have he : ∑ ab ∈ q.divisorsAntidiagonal, (ab.2.totient:ℝ) = (q:ℝ) := by
        exact_mod_cast (by rw [Nat.sum_divisorsAntidiagonal (fun (_ : ℕ) (b : ℕ) => b.totient), Nat.sum_div_divisors]; exact Nat.sum_totient q : ∑ ab ∈ q.divisorsAntidiagonal, ab.2.totient=q)
      calc
        _ = (∑ ab ∈ q.divisorsAntidiagonal, (ab.2.totient:ℝ))/((q:ℝ)^2*q.totient) := by rw [he]; field_simp
        _ = ∑ ab ∈ q.divisorsAntidiagonal, (ab.2.totient:ℝ)/((q:ℝ)^2*q.totient) := Finset.sum_div _ _ _
        _ ≤ _ := by
          apply sum_le_sum
          intro ab hab
          obtain ⟨ha,hb⟩ := pairPos hab
          have hprod := (Nat.mem_divisorsAntidiagonal.mp hab).1
          have habR : (ab.1:ℝ)*ab.2=q := by exact_mod_cast hprod
          have hφa : (0:ℝ)<ab.1.totient := by exact_mod_cast Nat.totient_pos.mpr ha
          have hbR : (0:ℝ)<ab.2 := by exact_mod_cast hb
          have haR : (0:ℝ)<ab.1 := by exact_mod_cast ha
          have hs := Nat.totient_super_multiplicative ab.1 ab.2
          rw [hprod] at hs
          have hs' : (ab.1.totient:ℝ)*ab.2.totient≤q.totient := by exact_mod_cast hs
          dsimp [F]
          rw [mul_assoc,hprod,if_pos h]
          rw [←habR,mul_pow]
          field_simp
          nlinarith only [hs']
    · rw [if_neg h]; exact sum_nonneg fun ab _ => hF ab
  calc
    _ ≤ (X:ℝ)*(∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 U, F (a,b)) :=
      mul_le_mul_of_nonneg_left ((sum_le_sum hh).trans (unpair U F hF)) (by positivity)
    _ = ∑ a ∈ Icc 1 U, (1 / ((a:ℝ)^2*a.totient)) *
        ((X:ℝ) * ∑ b ∈ Icc 1 U, if X<(v*a)*b then ((b:ℝ)^2)⁻¹ else 0) := by
      rw [Finset.mul_sum]
      apply sum_congr rfl; intro a _
      dsimp [F]
      rw [←Finset.mul_sum]; ring
    _ ≤ ∑ a ∈ Icc 1 U, 2*(v:ℝ)*(1/((a:ℝ)*a.totient)) := by
      apply sum_le_sum; intro a ha
      have ha0 := (Finset.mem_Icc.mp ha).1
      have hs := scaledInvSquares X (v*a) U (Nat.mul_pos hv ha0)
      refine (mul_le_mul_of_nonneg_left hs (by positivity : 0≤1/((a:ℝ)^2*a.totient))).trans_eq ?_
      push_cast
      have haR : (0:ℝ)<a := by exact_mod_cast ha0
      have hφR : (0:ℝ)<a.totient := by exact_mod_cast Nat.totient_pos.mpr ha0
      field_simp
    _ = 2*(v:ℝ)*(∑ a ∈ Icc 1 U, 1/((a:ℝ)*a.totient)) := (Finset.mul_sum ..).symm
    _ ≤ 8*v := by nlinarith only [mul_le_mul_of_nonneg_left (totient_series U) (show 0≤(v:ℝ) by positivity)]

end
end BandTail

end

section

/- The finite phase and Ramanujan identities in this section are adapted from
DFQDZZ's Apache-2.0 proof in goldbach-proofs PR #316,
commit e4ab24712555ae8c2c926adf19d368a9fb392c35. -/
namespace GoldbachExplicitModeledMajor
open Finset MeasureTheory
open scoped ComplexConjugate
noncomputable section

private theorem windowPhaseAdd (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

private theorem windowConjPhase (x : ℝ) : conj (phase x) = phase (-x) := by
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- Centering the square of the geometric sum makes its phase cancel exactly. -/
theorem windowKernelSquare (n : ℕ) (β : ℝ) :
    kernel n β ^ 2 * phase (-(n : ℝ) * β) = ((‖kernel n β‖ ^ 2 : ℝ) : ℂ) := by
  have hsym : kernel n β * phase (-(n : ℝ) * β) = conj (kernel n β) := by
    unfold kernel
    rw [sum_mul, map_sum]
    calc
      _ = ∑ k ∈ range (n + 1), conj (phase (((n - k : ℕ) : ℝ) * β)) := by
        refine sum_congr rfl fun k hk => ?_
        rw [windowConjPhase, ← windowPhaseAdd, Nat.cast_sub (Nat.lt_succ_iff.mp (mem_range.mp hk))]
        congr 1
        ring
      _ = _ := by
        simpa only [Nat.add_sub_cancel] using
          (Finset.sum_range_reflect (fun k => conj (phase ((k : ℝ) * β))) (n + 1))
  calc
    _ = kernel n β * (kernel n β * phase (-(n : ℝ) * β)) := by ring
    _ = _ := by rw [hsym, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem windowRamPower {p : ℕ} (hp : p.Prime) (j h : ℕ) (hc : h.Coprime p) :
    ram (p ^ (j + 1)) h = if j = 0 then -1 else 0 := by
  have hd := hp.coprime_iff_not_dvd.mp hc.symm
  have hpow (k : ℕ) : ¬ p ^ (k + 1) ∣ h :=
    fun hh => hd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans hh)
  rw [ram_primePower p j h hp, ite_eq_right (hpow j)]
  cases j with
  | zero => simp
  | succ k => simp [hpow k]

theorem windowRamUnit (q h : ℕ) (hc : h.Coprime q) : ram q h = ram q 1 := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [ram_one]
    | succ k =>
      have hc' := (Nat.coprime_pow_right_iff (Nat.succ_pos k) h p).mp hc
      rw [windowRamPower hp k h hc', windowRamPower hp k 1 (by simp)]
  | coprime q r hq hr hqr iq ir =>
    obtain ⟨h₁,h₂⟩ := Nat.coprime_mul_iff_right.mp hc
    rw [ram_mul (by omega) (by omega) hqr, ram_mul (by omega) (by omega) hqr, iq h₁, ir h₂]

def windowAvg (q a : ℕ) : ℂ := (∑ r ∈ (range q).filter (fun r => r.Coprime q),
  phase ((r:ℝ)*a/q))/(q.totient:ℂ)

private theorem avg_const (q a : ℕ) (ha : a.Coprime q) :
    windowAvg q a = ram q 1/(q.totient:ℂ) := by
  have hm : (∑ r ∈ (range q).filter (fun r => r.Coprime q), phase ((r:ℝ)*a/q)) = ram q a := by
    unfold ram; apply sum_congr rfl; intro r _; congr 1; ring
  rw [windowAvg,hm,windowRamUnit q a ha]

def windowModel (n A B : ℕ) : ℂ :=
  ∑ q ∈ Ioc A B, ∑ a ∈ (range (q+1)).filter (fun a => a.Coprime q),
    ∫ t in (a:ℝ)/q-width n q..(a:ℝ)/q+width n q,
      (windowAvg q a * kernel n (t-(a:ℝ)/q))^2 * phase (-(n:ℝ)*t)

private theorem windowIntegral (n : ℕ) (c b : ℝ) (z : ℂ) :
    (∫ t in c-b..c+b, (z*kernel n (t-c))^2*phase (-(n:ℝ)*t)) =
      z^2*phase (-(n:ℝ)*c)*(kernelMass n b:ℂ) := by
  have ht := intervalIntegral.integral_comp_add_left
    (fun t => (z*kernel n (t-c))^2*phase (-(n:ℝ)*t)) (a := -b) (b := b) c
  rw [sub_eq_add_neg,← ht]
  calc
    _ = ∫ x in -b..b, (z^2*phase (-(n:ℝ)*c))*((‖kernel n x‖^2:ℝ):ℂ) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [add_sub_cancel_left,mul_add,windowPhaseAdd,← windowKernelSquare]
      ring
    _ = _ := by rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal]; rfl

theorem windowModel_re (n A B : ℕ) (hA : 1≤A) :
    (windowModel n A B).re = ∑ q ∈ Ioc A B, (coefficient q n).re * kernelMass n (width n q) := by
  unfold windowModel
  simp_rw [windowIntegral]
  rw [Complex.re_sum]
  apply sum_congr rfl
  intro q hq
  have hq' : 1<q := lt_of_le_of_lt hA (mem_Ioc.mp hq).1
  have hrange : (range (q+1)).filter (fun a => a.Coprime q) = (range q).filter (fun a => a.Coprime q) := by
    ext a
    simp only [mem_filter,mem_range]
    constructor
    · rintro ⟨ha,hc⟩
      have hne : a ≠ q := by
        rintro rfl
        simp [Nat.Coprime] at hc
        omega
      exact ⟨by omega,hc⟩
    · rintro ⟨ha,hc⟩; exact ⟨by omega,hc⟩
  rw [hrange,← sum_mul]
  have hc : (∑ a ∈ (range q).filter (fun a => a.Coprime q),
      windowAvg q a ^ 2 * phase (-(n:ℝ)*((a:ℝ)/q))) = coefficient q n := by
    unfold coefficient ram
    rw [map_sum,mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [avg_const _ _ (mem_filter.mp ha).2,windowConjPhase]
    congr 2
    ring
  rw [hc,Complex.mul_re]; simp

end
end GoldbachExplicitModeledMajor

end

section

namespace BandTail
open Finset GoldbachExplicitModeledMajor MeasureTheory Filter Topology
noncomputable section

private theorem mass_nonneg (n q : ℕ) : 0 ≤ kernelMass n (width n q) := by
  apply intervalIntegral.integral_nonneg
  · linarith only [width_nonneg n q]
  · intro t _; positivity

theorem mass_upper (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) :
    kernelMass n (width n q) ≤ 8*(n:ℝ)*(cutoff n:ℝ)/q := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hK (x : ℝ) : ‖kernel n x‖ ≤ (n:ℝ)+1 := by
    unfold kernel
    exact (norm_sum_le ..).trans (by simp [phase,Complex.norm_exp])
  have hnn := mass_nonneg n q
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(width n q)) (b := width n q)
    (f := fun x : ℝ => ‖kernel n x‖^2) (C := ((n:ℝ)+1)^2) (fun t _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hK t) 2)
  change |kernelMass n (width n q)| ≤ _ at h
  rw [abs_of_nonneg hnn,abs_of_nonneg (by linarith only [width_nonneg n q])] at h
  refine h.trans ?_
  unfold width
  have hnpos : (0:ℝ) < n := by linarith
  have hQ : 0 ≤ (cutoff n:ℝ) := by positivity
  have hsq : ((n:ℝ)+1)^2 ≤ 4*(n:ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn') (show 0 ≤ 3*(n:ℝ)+1 by positivity)]
  field_simp
  nlinarith only [mul_le_mul_of_nonneg_right hsq hQ]

private def bandWeight (n q : ℕ) : ℝ := kernelMass n (width n q)/(q:ℝ)

private theorem weight_mono (n i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) : bandWeight n j ≤ bandWeight n i := by
  have hi' : (0:ℝ) < i := by exact_mod_cast hi
  have hj' : (0:ℝ) < j := by exact_mod_cast hi.trans hij
  have hr : (i:ℝ) ≤ j := by exact_mod_cast hij
  have hw : width n j ≤ width n i := by
    by_cases hn : n=0
    · simp [width,hn]
    · unfold width
      gcongr
  unfold bandWeight
  apply div_le_div₀ (mass_nonneg n i) (kernelMass_mono (width_nonneg n j) hw n) hi' hr

private theorem weighted_prefix_lower (A B : ℕ) (f w : ℕ → ℝ) (k : ℝ)
    (hab : A ≤ B) (hk : 0 ≤ k) (hw : ∀ i ≥ A,0 ≤ w i) (hm : ∀ i ≥ A,w (i+1) ≤ w i)
    (hp : ∀ i ≥ A,i ≤ B → -k ≤ ∑ j ∈ Ioc A i,f j) :
    -(k*w A) ≤ ∑ j ∈ Ioc A B,f j*w j := by
  have strong (i : ℕ) (hi : A ≤ i) (hiB : i ≤ B) :
      w i*((∑ j ∈ Ioc A i,f j)+k) ≤ (∑ j ∈ Ioc A i,f j*w j)+k*w A := by
    induction i,hi using Nat.le_induction with
    | base => simp [mul_comm]
    | succ i hi ih =>
      have h := ih (by omega)
      have hmono := hm i hi
      have hx := hp i hi (by omega)
      rw [sum_Ioc_succ_top hi,sum_Ioc_succ_top hi]
      nlinarith only [h,mul_nonneg (sub_nonneg.mpr hmono) (show 0 ≤ (∑ j ∈ Ioc A i,f j)+k by linarith)]
  have h := strong B hab le_rfl
  have v := hp B hab le_rfl
  nlinarith only [h,mul_nonneg (hw B hab) (show 0 ≤ (∑ j ∈ Ioc A B, f j)+k by linarith)]

theorem model_from_prefix (n B R : ℕ) (δ : ℝ) (hn : 1 ≤ n) (hR : 1 ≤ R) (hδ : 0 ≤ δ)
    (hprefix : ∀ i ≥ cutoff n,i ≤ R*cutoff n → -(δ*(cutoff n:ℝ)) ≤ ∑ q ∈ Ioc (cutoff n) i, F n q) :
    -((8*δ + 64/(R:ℝ))*(n:ℝ)) ≤ (windowModel n (cutoff n) B).re := by
  let A := cutoff n
  have ha : 1 ≤ A := cutoff_positive n
  have ha' : (0:ℝ) < A := by exact_mod_cast ha
  have hr' : (0:ℝ) < R := by exact_mod_cast hR
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [windowModel_re _ _ _ ha]
  change _ ≤ ∑ q ∈ Ioc A B, _
  by_cases hab : A ≤ B
  · let T := min B (R*A)
    have hT : A ≤ T := le_min hab (by dsimp [A]; nlinarith [Nat.mul_le_mul_right (cutoff n) hR])
    have hind := weighted_prefix_lower A T (F n) (bandWeight n) (δ*(A:ℝ)) hT (by positivity)
      (fun i _ => div_nonneg (mass_nonneg n i) (by positivity)) (fun i hi => weight_mono n _ _ (ha.trans hi) (by omega))
      (fun i hi hmax => hprefix i hi (hmax.trans (min_le_right _ _)))
    have hweight : bandWeight n A ≤ 8*(n:ℝ)/A := by
      have h := mass_upper n A hn ha
      change kernelMass n (width n A) ≤ 8*(n:ℝ)*A/A at h
      rw [mul_div_cancel_right₀ _ ha'.ne'] at h
      exact div_le_div_of_nonneg_right h ha'.le
    have hs : -(8*δ*(n:ℝ)) ≤ ∑ q ∈ Ioc A T, (coefficient q n).re * kernelMass n (width n q) := by
      calc
        _ ≤ -(δ*(A:ℝ)*bandWeight n A) := by
          have h := mul_le_mul_of_nonneg_left hweight (show 0 ≤ δ*(A:ℝ) by positivity)
          field_simp at h
          nlinarith only [h]
        _ ≤ _ := hind
        _ = _ := sum_congr rfl (fun q hq => by
          have hq' : (q:ℝ)≠0 := by exact_mod_cast (show q≠0 by have := (mem_Ioc.mp hq).1; omega)
          change (q:ℝ)*_ * (_/(q:ℝ)) = _
          field_simp)
    have ht : -(64*(n:ℝ)/R) ≤ ∑ q ∈ Ioc T B, (coefficient q n).re * kernelMass n (width n q) := by
      by_cases hB : B ≤ R*A
      · simp [T,min_eq_left hB]; positivity
      · rw [show T = R*A from min_eq_right (by omega)]
        have hsum := totient_tail (R*A) 1 B (by decide)
        let S := Ioc (R*A) B
        have he : ∑ q ∈ S, 1/((q:ℝ)*q.totient) ≤
          ∑ q ∈ Icc 1 B, if R*A < 1*q then 1/((q:ℝ)*q.totient) else 0 := by
          rw [← sum_filter]
          apply le_of_eq
          congr 1
          ext q; simp only [S,mem_Ioc,mem_filter,mem_Icc,one_mul]
          constructor <;> rintro h <;> omega
        have hsz : ((R:ℝ)*A)*(∑ q ∈ S,1/((q:ℝ)*q.totient)) ≤ 8 := by
          push_cast at hsum
          exact (mul_le_mul_of_nonneg_left he (by positivity)).trans (by simpa only [Nat.cast_one,mul_one] using hsum)
        have hterm (q : ℕ) (hq : q∈S) : -((8*(n:ℝ)*A)*(1/((q:ℝ)*q.totient))) ≤
            (coefficient q n).re * kernelMass n (width n q) := by
          have hq0 : 1 ≤ q := by have := (mem_Ioc.mp hq).1; omega
          have hq' : (0:ℝ) < q := by exact_mod_cast hq0
          have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
          have hc := (Complex.abs_re_le_norm (coefficient q n)).trans (coeff_norm_le q n hq0)
          have hmass := mass_upper n q hn hq0
          have hprod := mul_le_mul hc hmass (mass_nonneg n q) (by positivity)
          have habs : |(coefficient q n).re * kernelMass n (width n q)| ≤ (1/(q.totient:ℝ))*(8*(n:ℝ)*(cutoff n:ℝ)/q) := by
            simpa only [abs_mul,abs_of_nonneg (mass_nonneg n q)] using hprod
          have hneg := (neg_le_of_abs_le habs)
          convert hneg using 1 <;> dsimp [A] <;> ring
        have hsum' := sum_le_sum hterm
        rw [sum_neg_distrib,← mul_sum] at hsum'
        refine le_trans ?_ hsum'
        apply neg_le_neg
        apply (le_div_iff₀ hr').mpr
        nlinarith only [mul_le_mul_of_nonneg_left hsz (show 0 ≤ 8*(n:ℝ) by positivity)]
    rw [← sum_Ioc_consecutive _ hT (min_le_left _ _)]
    have hid : 64*(n:ℝ)/R = (64/(R:ℝ))*(n:ℝ) := by ring
    linarith
  · simp [Ioc_eq_empty (by omega : ¬ A < B)]
    positivity

end
end BandTail

end

section

namespace BandTail
open Finset GoldbachExplicitModeledMajor Filter Topology
noncomputable section

theorem floor_from_uniform
    (uniform : ∀ R : ℕ, 1 ≤ R → ∀ δ : ℝ, 0 < δ → ∃ A₀ : ℕ,
      ∀ A ≥ A₀, ∀ n i : ℕ, A ≤ i → i ≤ R*A → -(δ*(A:ℝ)) ≤ ∑ q ∈ Ioc A i, F n q) :
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ B : ℕ,
      -(e*(n:ℝ)) ≤ (windowModel n (cutoff n) B).re := by
  intro e he
  let R : ℕ := ⌈128/e⌉₊+1
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hR' : (0:ℝ) < R := by exact_mod_cast hR
  have hlarge : 128 / e ≤ (R:ℝ) := by
    dsimp [R]; push_cast; linarith only [Nat.le_ceil (128/e)]
  have hratio : 64/(R:ℝ) ≤ e/2 := (div_le_iff₀ hR').mpr (by
    have h := (div_le_iff₀ he).mp hlarge
    linarith)
  obtain ⟨A₀,hA⟩ := uniform R hR (e/16) (by positivity)
  refine ⟨2^A₀+1,?_⟩
  intro n hn B
  have hn' : 1 ≤ n := (Nat.succ_le_succ (Nat.zero_le (2^A₀))).trans hn
  have hlog : A₀ ≤ Nat.log 2 (n+2) := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by omega)
  have hl : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
  have hc : A₀ ≤ cutoff n := hlog.trans (by
    dsimp [cutoff]; nlinarith [Nat.mul_le_mul_left (Nat.log 2 (n+2)) hl])
  apply le_trans _ (model_from_prefix n B R (e/16) hn' hR (by positivity) (hA _ hc n))
  have hk : 8*(e/16)+64/(R:ℝ) ≤ e := by linarith
  exact neg_le_neg (mul_le_mul_of_nonneg_right hk (by positivity))

end
end BandTail

end

section

namespace BandTail
open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta
noncomputable section
def w (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => |h n d|/(d:ℝ)^(3/4:ℝ),by simp⟩
def z (n : ℕ) : ArithmeticFunction ℝ := ⟨fun d => h n d/(d:ℝ),by simp⟩
theorem w_mult (n : ℕ) : IsMultiplicative (w n) := by
  refine ⟨by simp [w,(h_mult n).map_one],fun {a b} hab => ?_⟩
  simp only [w,coe_mk,(h_mult n).map_mul_of_coprime hab,Nat.cast_mul,abs_mul,Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  ring
theorem z_mult (n : ℕ) : IsMultiplicative (z n) := by
  refine ⟨by simp [z,(h_mult n).map_one],fun {a b} hab => ?_⟩
  simp [z,(h_mult n).map_mul_of_coprime hab]; ring
theorem w_nonneg (n d : ℕ) : 0≤w n d := by dsimp [w]; positivity

theorem localReduce (f : ℕ → ℝ) (hf : ∀ j, f (j+3)=0) (k : ℕ) :
    (∑ i ∈ range (k+1), f i)=f 0 + (if k≥1 then f 1 else 0) + (if k≥2 then f 2 else 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ,ih]
    rcases k with _ | _ | j
    · simp
    · simp
    · simp [hf,show 2≤j+1+1 by omega,show 2≤j+1+1+1 by omega]

theorem wLocal (p n k : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p^k).divisors, w n d) ≤ 1+6/((p:ℝ)^(3/2:ℝ)) := by
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp1 : 0<(p:ℝ)-1 := by linarith
  have hpr : 0<(p:ℝ) := by linarith
  have hW1 : w n p ≤ 4/((p:ℝ)^(3/2:ℝ)) := by
    have h₁ : |h n p| ≤ 4/(p:ℝ) := by
      rw [h_prime n p hp]
      split_ifs
      · rw [abs_of_nonneg (by positivity)]; field_simp; linarith
      · rw [abs_div,abs_neg,abs_of_nonneg hpr.le,abs_of_nonneg (sq_nonneg _)]
        field_simp
        nlinarith [mul_nonneg (show 0≤(p:ℝ)-2 by linarith) (show 0≤3*(p:ℝ)-2 by linarith)]
    dsimp [w]
    calc
      _ ≤ (4/(p:ℝ))/((p:ℝ)^(3/4:ℝ)) := div_le_div_of_nonneg_right h₁ (by positivity)
      _ = 4/(p:ℝ)^(1+(3/4):ℝ) := by rw [Real.rpow_add hpr,Real.rpow_one,div_div]
      _ ≤ _ := by apply div_le_div_of_nonneg_left (by norm_num) (by positivity); exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hW2 : w n (p^2) ≤ 2/(p:ℝ)^(3/2:ℝ) := by
    have he : |h n (p^2)| ≤ 2 := by
      rw [h_square n p hp]; split_ifs
      · rw [abs_div,abs_neg,abs_of_nonneg hpr.le,abs_of_nonneg hp1.le]; apply (div_le_iff₀ hp1).mpr; linarith
      · norm_num
    change |h n (p^2)| / ((p^2:ℕ):ℝ)^(3/4:ℝ) ≤ _
    rw [Nat.cast_pow,←Real.rpow_natCast_mul hpr.le,show (↑(2:ℕ):ℝ)*(3/4)=3/2 by norm_num]
    exact div_le_div_of_nonneg_right he (by positivity)
  rw [Nat.sum_divisors_prime_pow hp,localReduce (fun j => w n (p^j)) (fun j => by simp [w,h_cube n p j hp])]
  simp only [pow_zero,pow_one,(w_mult n).map_one]
  simp only [div_eq_mul_inv] at hW1 hW2 ⊢
  split_ifs <;> linarith [w_nonneg n p,w_nonneg n (p^2)]

theorem zLocal (p n k : ℕ) (hp : p.Prime) : 0≤∑ d ∈ (p^k).divisors,z n d := by
  rw [Nat.sum_divisors_prime_pow hp,localReduce (fun j => z n (p^j)) (fun j => by simp [z,h_cube n p j hp])]
  simp only [pow_zero,pow_one,(z_mult n).map_one]
  have h2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp1 : 0<(p:ℝ)-1 := by linarith
  have hpr : 0<(p:ℝ) := by linarith
  have hsq : 1≤((p:ℝ)-1)^2 := by nlinarith [mul_nonneg (show 0≤(p:ℝ)-2 by linarith) (show 0≤(p:ℝ) by linarith)]
  simp only [z,coe_mk,h_prime n p hp,h_square n p hp,Nat.cast_pow]
  by_cases hpn : p∣n
  · simp only [hpn,ite_true]
    split_ifs with hk hk2
    · field_simp; nlinarith [mul_pos hpr hp1]
    · positivity
    · omega
    · norm_num
  · simp only [hpn,ite_false,zero_div,ite_self,add_zero]
    split_ifs
    · field_simp; nlinarith [mul_le_mul_of_nonneg_right hsq hpr.le]
    · norm_num

def universal : ℝ := Real.exp (6*∑' j : ℕ, ((j:ℝ)^(3/2:ℝ))⁻¹)

theorem uniformDivisors (n M : ℕ) (hM : 0<M) :
    (∑ d ∈ M.divisors, w n d) ≤ universal := by
  let A : ArithmeticFunction ℝ := w n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (w_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,w n d := coe_mul_zeta_apply
  have hprod := hA.multiplicative_factorization A hM.ne'
  rw [he] at hprod
  rw [hprod,Finsupp.prod]
  calc
    _ ≤ ∏ p ∈ M.factorization.support, Real.exp (6/((p:ℝ)^(3/2:ℝ))) := by
      refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
      · rw [he]; exact sum_nonneg fun d _ => w_nonneg n d
      · rw [he]
        have hh : p ∈ M.primeFactors := M.support_factorization ▸ hp
        exact (wLocal p n _ (Nat.prime_of_mem_primeFactors hh)).trans (by linarith [Real.add_one_le_exp (6/((p:ℝ)^(3/2:ℝ)))])
    _ ≤ universal := by
      rw [←Real.exp_sum,universal]
      apply Real.exp_le_exp.mpr
      simp_rw [div_eq_mul_inv,←mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤6)
      exact (Real.summable_nat_rpow_inv.mpr (by norm_num : (1:ℝ)<3/2)).sum_le_tsum _ (by intro _ _; positivity)

theorem signedDivisors (n M : ℕ) (hM : 0<M) :
    0 ≤ ∑ d ∈ M.divisors, z n d := by
  let A : ArithmeticFunction ℝ := z n * (ζ : ArithmeticFunction ℝ)
  have hA : IsMultiplicative A := (z_mult n).mul isMultiplicative_zeta.natCast
  have he (m : ℕ) : A m = ∑ d ∈ m.divisors,z n d := coe_mul_zeta_apply
  have hh := hA.multiplicative_factorization A hM.ne'
  rw [he] at hh
  rw [hh,Finsupp.prod]
  apply Finset.prod_nonneg
  intro p hp
  rw [he]
  exact zLocal p n _ (Nat.prime_of_mem_primeFactors (M.support_factorization ▸ hp))

theorem prefixDiv (J : ℕ) : Icc 1 J ⊆ J.factorial.divisors := by
  intro d hd
  obtain ⟨hd1, hdJ⟩ := mem_Icc.mp hd
  exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial hd1 hdJ,J.factorial_pos.ne'⟩

theorem uniformPrefix (n J : ℕ) : (∑ d ∈ Icc 1 J, w n d)≤universal :=
  (sum_le_sum_of_subset_of_nonneg (prefixDiv J) (fun d _ _ => w_nonneg n d)).trans
    (uniformDivisors n _ J.factorial_pos)

theorem tailTerm (n J d : ℕ) (hJ : 0<J) (hJd : J≤d) :
    |z n d| ≤ w n d / ((J:ℝ)^(1/4:ℝ)) := by
  have hd : 0<(d:ℝ) := by exact_mod_cast hJ.trans_le hJd
  have hJr : 0<(J:ℝ) := by exact_mod_cast hJ
  have he : (d:ℝ)^(3/4:ℝ)*(d:ℝ)^(1/4:ℝ)=d := by
    rw [←Real.rpow_add hd,show (3/4:ℝ)+1/4=1 by norm_num,Real.rpow_one]
  change |h n d / (d:ℝ)| ≤ |h n d| / _ / _
  rw [abs_div,abs_of_pos hd,div_div]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos (Real.rpow_pos_of_pos hd _) (Real.rpow_pos_of_pos hJr _))
  apply le_trans _ he.le
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hJd) (by norm_num)) (by positivity)

theorem uniformTail (n J : ℕ) (s : Finset ℕ) (hJ : 0<J) (hs : ∀ d ∈ s,J≤d) :
    (∑ d ∈ s, |z n d|) ≤ universal / (J:ℝ)^(1/4:ℝ) := by
  have hb : s⊆Icc 1 (s.sup id) := by
    intro d hd
    exact mem_Icc.mpr ⟨by have := hs d hd; omega, le_sup (f:=id) hd⟩
  calc
    _ ≤ ∑ d ∈ s, w n d / (J:ℝ)^(1/4:ℝ) := sum_le_sum fun d hd => tailTerm n J d hJ (hs d hd)
    _ = _ := (sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right ((sum_le_sum_of_subset_of_nonneg hb (fun d _ _ => w_nonneg n d)).trans (uniformPrefix n _)) (by positivity)

theorem signedPrefix (n J : ℕ) (hJ : 0<J) :
    -(universal / (J:ℝ)^(1/4:ℝ)) ≤ ∑ d ∈ Icc 1 J, z n d := by
  have hu := uniformTail n J (J.factorial.divisors \ Icc 1 J) hJ (by
    intro d hd
    obtain ⟨hd,hd'⟩ := mem_sdiff.mp hd
    have hpos := Nat.pos_of_mem_divisors hd
    simp only [mem_Icc,not_and] at hd'
    omega)
  have hh := signedDivisors n J.factorial J.factorial_pos
  rw [←sum_sdiff (s₁:=Icc 1 J) (s₂:=J.factorial.divisors) (prefixDiv J)] at hh
  have ht := sum_le_sum (s:=J.factorial.divisors \ Icc 1 J) (fun d _ => le_abs_self (z n d))
  linarith

end
end BandTail

end

section

namespace BandTail
open Finset ArithmeticFunction
noncomputable section

def gSum (n X : ℕ) : ℝ := ∑ k ∈ Icc 1 X, g n k
def gAvg (n X : ℕ) : ℝ := gSum n X / X
def fSum (n X : ℕ) : ℝ := ∑ k ∈ Icc 1 X, F n k

theorem g_sum_bounds (n X : ℕ) : 0≤gSum n X ∧ gSum n X≤X := by
  constructor
  · apply sum_nonneg
    intro k hk
    simp [g]; split_ifs <;> norm_num
  · calc
      _ ≤ ∑ k ∈ Icc 1 X,(1:ℝ) := by
        apply sum_le_sum
        intro k hk
        simp [g]; split_ifs <;> norm_num
      _ = _ := by simp

theorem g_avg_bounds (n X : ℕ) : 0≤gAvg n X ∧ gAvg n X≤1 := by
  have hb := g_sum_bounds n X
  exact ⟨div_nonneg hb.1 (Nat.cast_nonneg _),div_le_one_of_le₀ hb.2 (Nat.cast_nonneg _)⟩

theorem fSum_convolution (n X : ℕ) :
    fSum n X = ∑ d ∈ Icc 1 X,h n d * gSum n (X/d) := by
  classical
  let S := Icc 1 X
  let f := fun v : ℕ × ℕ => h n v.1 * g n v.2
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
        hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hh; exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hh).2,by omega⟩
  calc
    _ = ∑ q ∈ S,∑ v ∈ q.divisorsAntidiagonal,f v := by
      simp [fSum,S,convolution n,mul_comm (g n) (h n),ArithmeticFunction.mul_apply,f]
    _ = ∑ q ∈ S, ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), f v :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ v ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), f v :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ = _ := by
      rw [sum_filter,sum_product]
      apply sum_congr rfl
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hkd : (S.filter fun k => d*k∈S)=Icc 1 (X/d) := by
        ext k
        simp only [S,mem_filter,mem_Icc]
        constructor
        · rintro ⟨⟨hk,_⟩,_,hdk⟩
          exact ⟨hk,(Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hdk)⟩
        · rintro ⟨hk,hkx⟩
          exact ⟨⟨hk,hkx.trans (Nat.div_le_self _ _)⟩,Nat.mul_pos hd0 hk, by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp hkx⟩
      simp only [f,gSum,mul_sum]
      rw [←sum_filter,hkd]

theorem prefix_split (f : ℕ→ℝ) {J X : ℕ} (hJX : J≤X) :
    (∑ d ∈ Icc 1 X,f d)=(∑ d ∈ Icc 1 J,f d)+(∑ d ∈ Ioc J X,f d) := by
  have he : Icc 1 X=Icc 1 J ∪ Ioc J X := by ext k; simp only [mem_union,mem_Icc,mem_Ioc]; omega
  rw [he,sum_union (by rw [Finset.disjoint_left]; intro k hk hj; have := (mem_Icc.mp hk).2; have := (mem_Ioc.mp hj).1; omega)]

def scaleFactor (X d : ℕ) : ℝ := (d:ℝ)*(X/d:ℕ)/X

theorem scale_bounds (X d : ℕ) (hX : 0<X) (hd : 0<d) :
    0≤ scaleFactor X d ∧ scaleFactor X d ≤ 1 ∧ 1-scaleFactor X d ≤ (d:ℝ)/X := by
  have hx : 0<(X:ℝ) := by exact_mod_cast hX
  have hx0 : (d:ℝ)*(X/d:ℕ) ≤ X := by exact_mod_cast Nat.mul_div_le X d
  have hx1 : (X:ℝ) < (d:ℝ)*((X/d:ℕ)+1:ℝ) := by exact_mod_cast Nat.lt_mul_div_succ X hd
  unfold scaleFactor
  refine ⟨by positivity,(div_le_iff₀ hx).mpr (by linarith),?_⟩
  rw [sub_div' hx.ne',div_le_div_iff_of_pos_right hx]
  linarith

theorem scaled_piece (n X d : ℕ) (hd : 0<d) :
    h n d * gSum n (X/d) / X = z n d * (scaleFactor X d * gAvg n (X/d)) := by
  have hdr : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  by_cases hy : X/d=0
  · simp [gSum,gAvg,scaleFactor,hy]
  · have hyr : ((X/d:ℕ):ℝ)≠0 := by exact_mod_cast hy
    simp only [z,coe_mk,scaleFactor,gAvg]
    field_simp

theorem piece_approx (n X d : ℕ) (hX : 0<X) (hd : 0<d) (t e : ℝ)
    (he : |gAvg n (X/d)-t|≤e) (hdX : (d:ℝ)/X≤e) :
    |h n d * gSum n (X/d) / X - z n d * t| ≤ |z n d| *(2*e) := by
  obtain ⟨_,hs,hs'⟩ := scale_bounds X d hX hd
  have hg := g_avg_bounds n (X/d)
  have hc : |scaleFactor X d * gAvg n (X/d)-gAvg n (X/d)| ≤ e := by
    rw [←sub_one_mul,abs_mul,abs_of_nonpos (sub_nonpos.mpr hs),abs_of_nonneg hg.1]
    calc
      _ ≤ -(scaleFactor X d-1)*1 := mul_le_mul_of_nonneg_left hg.2 (by linarith)
      _ ≤ e := by linarith
  rw [scaled_piece n X d hd,←mul_sub,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (abs_sub_le _ (gAvg n (X/d)) _).trans (by linarith)

theorem dyadic_approx (n X J : ℕ) (hX : 0<X) (hJ : 0<J) (hJX : J≤X) (t e : ℝ) (he : 0≤e)
    (hne : ∀ d ∈ Icc 1 J,|gAvg n (X/d)-t|≤e) (hJr : (J:ℝ)/X ≤ e) :
    |fSum n X / X - (∑ d ∈ Icc 1 J,z n d)*t| ≤
      universal*(2*e)+universal/(J:ℝ)^(1/4:ℝ) := by
  let a := fun d => h n d * gSum n (X/d) / X
  have hsmall : |∑ d ∈ Icc 1 J,(a d-z n d*t)|≤universal*(2*e) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ d ∈ Icc 1 J, |z n d| *(2*e) := by
        refine sum_le_sum fun d hd => piece_approx n X d hX (mem_Icc.mp hd).1 t e (hne _ hd) ?_
        exact (div_le_div_of_nonneg_right (by exact_mod_cast (mem_Icc.mp hd).2) (Nat.cast_nonneg _)).trans hJr
      _ = _ := (sum_mul _ _ _).symm
      _ ≤ _ := by
        have hu := uniformTail n 1 (Icc 1 J) (by decide) (fun d hd => (mem_Icc.mp hd).1)
        norm_num at hu
        exact mul_le_mul_of_nonneg_right hu (by positivity)
  have hlarge : |∑ d ∈ Ioc J X,a d| ≤ universal/(J:ℝ)^(1/4:ℝ) := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply le_trans _ (uniformTail n J (Ioc J X) hJ (fun d hd => (mem_Ioc.mp hd).1.le))
    apply sum_le_sum
    intro d hd
    have hd0 : 0<d := hJ.trans (mem_Ioc.mp hd).1
    obtain ⟨hs,hs',_⟩ := scale_bounds X d hX hd0
    have hg := g_avg_bounds n (X/d)
    dsimp only [a]; rw [scaled_piece n X d hd0,abs_mul,abs_of_nonneg (mul_nonneg hs hg.1)]
    exact mul_le_of_le_one_right (abs_nonneg _) (mul_le_one₀ hs' hg.1 hg.2)
  have htotal : fSum n X / X = (∑ d ∈ Icc 1 J,a d)+(∑ d ∈ Ioc J X,a d) := by
    rw [fSum_convolution,sum_div]
    exact prefix_split a hJX
  rw [htotal,sum_mul]
  rw [show (∑ d ∈ Icc 1 J,a d)+(∑ d ∈ Ioc J X,a d)-(∑ d ∈ Icc 1 J,z n d*t)=
      (∑ d ∈ Icc 1 J,(a d-z n d*t))+(∑ d ∈ Ioc J X,a d) by rw [sum_sub_distrib]; ring]
  exact (abs_add_le _ _).trans (add_le_add hsmall hlarge)

end
end BandTail

end

section

namespace GoldbachModelMean

open Finset Filter Topology

private def modProd (s : Finset Nat.Primes) : ℕ := ∏ p ∈ s, (p:ℕ)

private theorem modProd_pos (s : Finset Nat.Primes) : 0 < modProd s :=
  Finset.prod_pos (fun p _ => p.property.pos)

private theorem totientProd (s : Finset Nat.Primes) :
    ((modProd s).totient:ℝ)*(1+∑ p ∈ s, 1/(p:ℝ)) ≤ modProd s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [modProd]
  | @insert p s hps ih =>
    have hcop : (p:ℕ).Coprime (modProd s) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply (Nat.coprime_primes p.property q.property).mpr
      intro h
      exact hps ((Subtype.ext h : p=q) ▸ hq)
    have heq : modProd (insert p s) = (p:ℕ)*modProd s := Finset.prod_insert hps
    have hp : (1:ℕ)≤p.val := p.property.one_lt.le
    have hp' : (0:ℝ)<p := by exact_mod_cast p.property.pos
    have hsum : 0 ≤ ∑ q ∈ s, (1:ℝ)/(q:ℝ) := sum_nonneg fun q _ => by positivity
    rw [heq,Nat.totient_mul hcop,Nat.totient_prime p.property,Finset.sum_insert hps]
    push_cast [Nat.cast_sub hp]
    calc
      _ ≤ (p:ℝ)*(((modProd s).totient:ℝ)*(1+∑ q ∈ s, 1/(q:ℝ))) := by
        have : ((p:ℝ)-1)*(1+(1/(p:ℝ)+∑ q ∈ s, 1/(q:ℝ))) ≤ (p:ℝ)*(1+∑ q ∈ s, 1/(q:ℝ)) := by
          field_simp
          nlinarith [mul_nonneg hp'.le hsum]
        nlinarith only [mul_le_mul_of_nonneg_right this (Nat.cast_nonneg (modProd s).totient (α:=ℝ))]
      _ ≤ _ := mul_le_mul_of_nonneg_left ih hp'.le

theorem exists_thin_modulus (e : ℝ) (he : 0<e) :
    ∃ D : ℕ, 0<D ∧ (D.totient:ℝ)/(D:ℝ)<e := by
  classical
  have hs : ∃ s : Finset Nat.Primes, (1/e:ℝ) < ∑ p ∈ s, 1/(p:ℝ) := by
    by_contra! h
    exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun p => by positivity) h)
  obtain ⟨s,hs⟩ := hs
  refine ⟨modProd s,modProd_pos s,(div_lt_iff₀ (by exact_mod_cast modProd_pos s)).mpr ?_⟩
  have h := totientProd s
  have ht : (0:ℝ) < (modProd s).totient := by exact_mod_cast Nat.totient_pos.mpr (modProd_pos s)
  have h1 := (div_lt_iff₀ he).mp hs
  nlinarith only [mul_le_mul_of_nonneg_right h he.le,
    mul_lt_mul_of_pos_right h1 ht,mul_pos he ht]

def fewFactors (k X : ℕ) : Finset ℕ :=
  (range X).filter fun n => 0 < n ∧ n.primeFactorsList.length ≤ k

private theorem few_step (k X D : ℕ) (hD : 0<D) :
    (fewFactors (k+1) X).card ≤ D.totient*(X/D+1)+(D+1)*(fewFactors k X).card := by
  classical
  let R := (range X).filter fun n => D.Coprime n
  let cover := (range (D+1)).biUnion fun p => (fewFactors k X).image fun y => p*y
  have hsub : fewFactors (k+1) X ⊆ R ∪ cover := by
    intro x hx
    obtain ⟨hxX,hxp,hxk⟩ := mem_filter.mp hx
    by_cases hc : D.Coprime x
    · exact mem_union_left _ (mem_filter.mpr ⟨hxX,hc⟩)
    obtain ⟨p,hp,hpd,hpx⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    obtain ⟨y,rfl⟩ := hpx
    have hy : y ≠ 0 := by intro hz; simp [hz] at hxp
    have hlen := (Nat.perm_primeFactorsList_mul hp.ne_zero hy).length_eq
    simp [Nat.primeFactorsList_prime hp] at hlen
    have hyX : y < X := lt_of_le_of_lt (by simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left y hp.pos) (mem_range.mp hxX)
    exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_range.mpr (by have := Nat.le_of_dvd hD hpd; omega),
      mem_image.mpr ⟨y,mem_filter.mpr ⟨mem_range.mpr hyX,by omega,by omega⟩,rfl⟩⟩)
  have hR : R.card ≤ D.totient*(X/D+1) := by
    simpa only [R,zero_add,← range_eq_Ico] using Nat.Ico_filter_coprime_le 0 X hD.ne'
  have hc : cover.card ≤ (D+1)*(fewFactors k X).card := calc
    _ ≤ ∑ p ∈ range (D+1), ((fewFactors k X).image fun y => p*y).card := card_biUnion_le
    _ ≤ ∑ _ ∈ range (D+1), (fewFactors k X).card := by exact Finset.sum_le_sum (fun p _ => card_image_le)
    _ = _ := by simp
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add hR hc))

theorem fewFactors_eventually (k : ℕ) (e : ℝ) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ((fewFactors k X).card:ℝ) ≤ e*X := by
  induction k generalizing e with
  | zero =>
    filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (1/e)] with X hX
    have hsub : fewFactors 0 X ⊆ {1} := by
      intro x hx
      obtain ⟨_,hp,hl⟩ := mem_filter.mp hx
      have hn := (Nat.primeFactorsList_eq_nil x).mp (List.length_eq_zero_iff.mp (by omega))
      simp only [mem_singleton]
      omega
    have hc : (fewFactors 0 X).card ≤ 1 := by simpa using card_le_card hsub
    change 1/e ≤ (X:ℝ) at hX
    have hh := (div_le_iff₀ he).mp hX
    exact (by exact_mod_cast hc : ((fewFactors 0 X).card:ℝ) ≤ 1) |>.trans (by linarith)
  | succ k ih =>
    obtain ⟨D,hD,hphi⟩ := exists_thin_modulus (e/4) (by positivity)
    have hD' : (0:ℝ)<D := by exact_mod_cast hD
    filter_upwards [ih (e/(4*(D+1))) (by positivity),
      (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (4*(D.totient:ℝ)/e)] with X hprev hlarge
    change 4*(D.totient:ℝ)/e ≤ X at hlarge
    have hr := (div_le_iff₀ he).mp hlarge
    have hp := (div_lt_iff₀ hD').mp hphi
    have hquot : ((X/D:ℕ):ℝ) ≤ (X:ℝ)/D := by
      apply (le_div_iff₀ hD').mpr
      exact_mod_cast Nat.div_mul_le_self X D
    have h := few_step k X D hD
    have h' : ((fewFactors (k+1) X).card:ℝ) ≤ D.totient*(((X/D:ℕ):ℝ)+1)+((D:ℝ)+1)*(fewFactors k X).card := by exact_mod_cast h
    have hf : ((D:ℝ)+1)*((fewFactors k X).card:ℝ) ≤ (e/4)*X := by
      calc
        _ ≤ ((D:ℝ)+1)*(e/(4*(D+1))*X) := mul_le_mul_of_nonneg_left hprev (by positivity)
        _ = _ := by field_simp
    have hg : (D.totient:ℝ)*((X/D:ℕ):ℝ) ≤ (e/4)*X := calc
      _ ≤ (D.totient:ℝ)*((X:ℝ)/D) := mul_le_mul_of_nonneg_left hquot (by positivity)
      _ = ((D.totient:ℝ)/D)*X := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hphi.le (by positivity)
    nlinarith only [h',hf,hg,hr,mul_nonneg he.le (Nat.cast_nonneg X (α:=ℝ))]

end GoldbachModelMean

end

section

noncomputable section
namespace GoldbachModelMean.Brun
open Finset Filter

def product (s : Finset ℕ) := ∏ p ∈ s, p
def hits (P : Finset ℕ) (m : ℕ) := P.filter (fun p => p ∣ m)
def count (P : Finset ℕ) (X : ℕ) : ℝ := ∑ m ∈ Ioc 0 X, if (hits P m).card=0 then 1 else 0
def harmonic (P : Finset ℕ) : ℝ := ∑ p ∈ P, 1/(p:ℝ)
def divisCount (P : Finset ℕ) (j X : ℕ) : ℝ :=
  ∑ s ∈ P.powersetCard j, ((X / product s : ℕ):ℝ)
def trunc (P : Finset ℕ) (r X : ℕ) : ℝ :=
  ∑ j ∈ range (r+1), (-1:ℝ)^j*divisCount P j X

lemma prodPos (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) : 0<product s :=
  prod_pos (fun p h => (hp p h).pos)

lemma prodDvd (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) (m : ℕ) :
    product s ∣ m ↔ ∀ p ∈ s, p ∣ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [product]
  | @insert p s hps ih =>
    have hp' := hp p (mem_insert_self _ _)
    have hs := fun q (hq : q∈s) => hp q (mem_insert_of_mem hq)
    have hc : p.Coprime (product s) := Nat.coprime_prod_right_iff.mpr (fun q hq =>
      (Nat.coprime_primes hp' (hs q hq)).mpr fun he => hps (he ▸ hq))
    rw [product,prod_insert hps,forall_mem_insert]
    change p*product s ∣ m ↔ _
    exact ⟨fun h => ⟨(dvd_mul_right p _).trans h,(ih hs).mp ((dvd_mul_left (product s) p).trans h)⟩,
      fun h => hc.mul_dvd_of_dvd_of_dvd h.1 ((ih hs).mpr h.2)⟩

lemma omegaProd (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) : (product s).primeFactorsList.length=s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [product]
  | @insert p s hps ih =>
    have hp' := hp p (mem_insert_self _ _)
    have hs := fun q (hq : q∈s) => hp q (mem_insert_of_mem hq)
    have he := (Nat.perm_primeFactorsList_mul hp'.ne_zero (prodPos s hs).ne').length_eq
    change (∏ q ∈ insert p s,q).primeFactorsList.length=_
    rw [prod_insert hps,card_insert_of_notMem hps]
    change (p*product s).primeFactorsList.length=_
    simpa [Nat.primeFactorsList_prime hp',ih hs,Nat.add_comm] using he

theorem divisAsChoose (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (j X : ℕ) :
    divisCount P j X = ∑ m ∈ Ioc 0 X, (((hits P m).card.choose j:ℕ):ℝ) := by
  classical
  have hs (m : ℕ) :
      (P.powersetCard j).filter (fun s => product s ∣ m) = (hits P m).powersetCard j := by
    ext s
    simp only [mem_filter,mem_powersetCard]
    constructor
    · rintro ⟨⟨hsub,hj⟩,hd⟩
      exact ⟨fun q hq => mem_filter.mpr ⟨hsub hq,(prodDvd s (fun p h => hp p (hsub h)) m).mp hd q hq⟩,hj⟩
    · rintro ⟨hsub,hj⟩
      have hP (q) (hq:q∈s) := (mem_filter.mp (hsub hq)).1
      exact ⟨⟨fun q hq => hP q hq,hj⟩,(prodDvd s (fun p h => hp p (hP p h)) m).mpr
        (fun q hq => (mem_filter.mp (hsub hq)).2)⟩
  unfold divisCount
  simp_rw [←Nat.Ioc_filter_dvd_card_eq_div, ←Finset.sum_boole]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro m _
  rw [Finset.sum_boole,hs,card_powersetCard]

private theorem localTrunc (k r : ℕ) :
    |(if k=0 then (1:ℝ) else 0) - ∑ j ∈ range (r+1), (-1:ℝ)^j*(k.choose j:ℕ)| ≤ k.choose r := by
  cases k with
  | zero =>
    have hy : (∑ j ∈ range (r+1), (-1:ℝ)^j*(((0:ℕ).choose j):ℕ))=1 := by
      rw [sum_eq_single 0]
      · simp
      · intro j _ hj
        have hh : (0:ℕ).choose j=0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hh];simp
      · simp
    simp [hy]
  | succ k =>
    have hi := @Int.alternating_sum_range_choose_eq_choose k r
    have hr : (∑ j ∈ range (r+1), (-1:ℝ)^j*(((k+1).choose j):ℕ))=(-1:ℝ)^r*(k.choose r:ℕ) := by exact_mod_cast hi
    rw [if_neg (by omega),zero_sub,abs_neg,hr,abs_mul,abs_pow]
    simpa using (show ((k.choose r:ℕ):ℝ) ≤ ((k+1).choose r:ℕ) by exact_mod_cast Nat.choose_le_succ k r)

theorem truncateError (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r X : ℕ) :
    |count P X-trunc P r X| ≤ divisCount P r X := by
  unfold count trunc
  simp_rw [divisAsChoose P hp,Finset.mul_sum]
  rw [Finset.sum_comm (s:=range (r+1)),←sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun m _ => localTrunc (hits P m).card r))

theorem reciprocalLayer (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r : ℕ) :
    (∑ s ∈ P.powersetCard r, 1/(product s:ℝ)) ≤ Real.exp (2*harmonic P)/(2:ℝ)^r := by
  apply (le_div_iff₀ (by positivity)).mpr
  rw [Finset.sum_mul]
  calc
    _ = ∑ s ∈ P.powersetCard r, ∏ p ∈ s, (2/(p:ℝ)) := by
      apply sum_congr rfl
      intro s hs
      rw [prod_div_distrib,prod_const,(mem_powersetCard.mp hs).2]
      simp [product,div_eq_mul_inv,mul_comm]
    _ ≤ ∑ s ∈ P.powerset, ∏ p ∈ s, (2/(p:ℝ)) :=
      sum_le_sum_of_subset_of_nonneg (fun s hs => mem_powerset.mpr (mem_powersetCard.mp hs).1)
        (fun s _ _ => prod_nonneg (fun _ _ => by positivity))
    _ = ∏ p ∈ P, (1+2/(p:ℝ)) := (prod_one_add ..).symm
    _ ≤ ∏ p ∈ P, Real.exp (2/(p:ℝ)) := by
      apply Finset.prod_le_prod₀ (fun p _ => by positivity)
      intro p hp
      simpa [add_comm] using (Real.add_one_le_exp (2/(p:ℝ)))
    _ = _ := by rw [←Real.exp_sum]; congr 1;unfold harmonic;rw [mul_sum];apply sum_congr rfl;intros;ring

theorem errorEnvelope (P : Finset ℕ) (hp : ∀ p∈P, p.Prime) (r X : ℕ) :
    |count P X-trunc P r X| ≤ (X:ℝ)*Real.exp (2*harmonic P)/(2:ℝ)^r := by
  apply (truncateError P hp r X).trans
  calc
    divisCount P r X ≤ (X:ℝ)*(∑ s ∈ P.powersetCard r, 1/(product s:ℝ)) := by
      unfold divisCount
      rw [mul_sum]
      apply sum_le_sum
      intro s _
      simpa only [mul_one_div] using (Nat.cast_div_le (m:=X) (n:=product s) : ((X/product s:ℕ):ℝ)≤X/(product s:ℝ))
    _ ≤ (X:ℝ)*(Real.exp (2*harmonic P)/(2:ℝ)^r) :=
      mul_le_mul_of_nonneg_left (reciprocalLayer P hp r) (Nat.cast_nonneg _)
    _ = _ := by ring
end GoldbachModelMean.Brun

end

section

noncomputable section
namespace GoldbachModelMean.Brun
open Finset Filter

private lemma floorIneq (m d : ℕ) (hd : 0<d) :
    (m:ℝ)/d-1 ≤ ((m/d:ℕ):ℝ) ∧ ((m/d:ℕ):ℝ) ≤ m/(d:ℝ) := by
  refine ⟨?_,Nat.cast_div_le⟩
  have h : (m:ℝ) < d * (((m/d:ℕ):ℝ)+1) := by exact_mod_cast Nat.lt_mul_div_succ m hd
  have hh : (m:ℝ)/d < ((m/d:ℕ):ℝ)+1 := (div_lt_iff₀ (by exact_mod_cast hd)).mpr (by linarith)
  linarith

private lemma floorDiff (X Y d : ℕ) (hd : 0<d) (hY : 0<Y) :
    |((X/d:ℕ):ℝ)-(X:ℝ)/Y*((Y/d:ℕ):ℝ)| ≤ 1+(X:ℝ)/Y := by
  have hY' : (0:ℝ)<Y := by exact_mod_cast hY
  have hpos : 0≤(X:ℝ)/Y := by positivity
  obtain ⟨a,b⟩ := floorIneq X d hd
  obtain ⟨c,e⟩ := floorIneq Y d hd
  have h : (X:ℝ)/Y*(Y/(d:ℝ))=X/(d:ℝ) := by field_simp
  have h1 := mul_le_mul_of_nonneg_left c hpos
  have h2 := mul_le_mul_of_nonneg_left e hpos
  rw [h] at h2
  rw [mul_sub,h,mul_one] at h1
  rw [abs_le]
  constructor <;> linarith

private lemma layerCard (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r j X : ℕ) (hj : j≤r) :
    ((P.powersetCard j).filter (fun s => product s ≤ X)).card ≤
      (GoldbachModelMean.fewFactors r (X+1)).card := by
  apply Finset.card_le_card_of_injOn product
  · intro s hs
    obtain ⟨hP,hX⟩ := mem_filter.mp hs
    obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hP
    have hPrime (q) (hq:q∈s) := hp q (hsub hq)
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),prodPos s hPrime,(omegaProd s hPrime).trans_le (hcard.trans_le hj)⟩
  · intro s hs t ht e
    have h1 := (mem_powersetCard.mp (mem_filter.mp hs).1).1
    have h2 := (mem_powersetCard.mp (mem_filter.mp ht).1).1
    have hs' : (product s).primeFactors=s := Nat.primeFactors_prod (fun q hq => hp q (h1 hq))
    have ht' : (product t).primeFactors=t := Nat.primeFactors_prod (fun q hq => hp q (h2 hq))
    rw [←hs',e,ht']

private lemma layerDiff (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r j X Y : ℕ)
    (hj : j≤r) (hY : 0<Y) (hYX : Y≤X) :
    |divisCount P j X-(X:ℝ)/Y*divisCount P j Y| ≤
      ((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
  classical
  unfold divisCount
  rw [mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ s ∈ P.powersetCard j, if product s≤X then 1+(X:ℝ)/Y else 0 := by
      apply sum_le_sum
      intro s hs
      split_ifs with h
      · exact floorDiff X Y (product s) (prodPos s (fun q hq => hp q ((mem_powersetCard.mp hs).1 hq))) hY
      · have hx : X<product s := by omega
        simp [Nat.div_eq_of_lt hx,Nat.div_eq_of_lt (hYX.trans_lt hx)]
    _ = (((P.powersetCard j).filter (fun s => product s ≤ X)).card:ℝ)*(1+(X:ℝ)/Y) := by
      rw [←sum_filter];simp;ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast layerCard P hp r j X hj) (by positivity)

theorem truncDiff (P : Finset ℕ) (hp : ∀ p∈P,p.Prime) (r X Y : ℕ)
    (hY : 0<Y) (hYX : Y≤X) :
    |trunc P r X-(X:ℝ)/Y*trunc P r Y| ≤
      ((r:ℝ)+1)*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
  unfold trunc
  rw [mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ range (r+1), ((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) := by
      apply sum_le_sum
      intro j hj
      have hh := layerDiff P hp r j X Y (by have := mem_range.mp hj;omega) hY hYX
      rw [show (X:ℝ)/Y*((-1:ℝ)^j*divisCount P j Y)=(-1:ℝ)^j*((X:ℝ)/Y*divisCount P j Y) by ring,
        ←mul_sub,abs_mul,abs_pow]
      simpa using hh
    _ = _ := by simp [mul_assoc]

end GoldbachModelMean.Brun

end

section

noncomputable section
namespace GoldbachModelMean.Brun
open Finset Filter

theorem uniform_lowH (H C e : ℝ) (hC : 1≤C) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ∀ Y : ℕ, 0<Y → Y≤X → (X:ℝ)≤C*Y →
    ∀ P : Finset ℕ, (∀ p∈P,p.Prime) → harmonic P≤H →
    |count P X/X - count P Y/Y| ≤ e := by
  obtain ⟨r,hr⟩ := pow_unbounded_of_one_lt (4*Real.exp (2*H)/e) (show (1:ℝ)<2 by norm_num)
  let A : ℝ := ((r:ℝ)+1)*(1+C)
  have hA : 0<A := by dsimp [A];positivity
  have heps : 0<e/(4*A) := by positivity
  obtain ⟨x₀,hx⟩ := eventually_atTop.mp (GoldbachModelMean.fewFactors_eventually r (e/(4*A)) heps)
  filter_upwards [eventually_ge_atTop x₀,eventually_ge_atTop 1] with X hX hX1
  intro Y hY hYX hscale P hp hH
  have hY' : (0:ℝ)<Y := by exact_mod_cast hY
  have hX' : (0:ℝ)<X := by exact_mod_cast hX1
  have hx1 : (1:ℝ)≤X := by exact_mod_cast hX1
  have hRatio : (X:ℝ)/Y≤C := (div_le_iff₀ hY').mpr hscale
  have hR : 0≤(X:ℝ)/Y := by positivity
  have hExp := Real.exp_le_exp.mpr (show 2*harmonic P≤2*H by linarith)
  have hcoeff : Real.exp (2*harmonic P)/(2:ℝ)^r ≤ e/4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have := (div_lt_iff₀ he).mp hr
    nlinarith
  have err (W : ℕ) : |count P W-trunc P r W| ≤ (W:ℝ)*(e/4) := by
    refine (errorEnvelope P hp r W).trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
  have hf := hx (X+1) (by omega)
  push_cast at hf
  have hL : ((r:ℝ)+1)*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+(X:ℝ)/Y) ≤ (X:ℝ)*(e/2) := by
    calc
      _ ≤ ((r:ℝ)+1)*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ)*(1+C) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = A*((GoldbachModelMean.fewFactors r (X+1)).card:ℝ) := by dsimp [A];ring
      _ ≤ A*(e/(4*A)*((X:ℝ)+1)) := mul_le_mul_of_nonneg_left hf hA.le
      _ = e/4*((X:ℝ)+1) := by field_simp
      _ ≤ _ := by nlinarith [mul_nonneg he.le (sub_nonneg.mpr hx1)]
  have ht := (truncDiff P hp r X Y hY hYX).trans hL
  have hE : |(X:ℝ)/Y*trunc P r Y-(X:ℝ)/Y*count P Y| ≤ (X:ℝ)*(e/4) := by
    rw [←mul_sub,abs_mul,abs_of_nonneg hR,abs_sub_comm]
    calc
      _ ≤ ((X:ℝ)/Y)*(Y*(e/4)) := mul_le_mul_of_nonneg_left (err _) hR
      _ = _ := by field_simp
  have hT := abs_sub_le (count P X) (trunc P r X) ((X:ℝ)/Y*count P Y)
  have hU := abs_sub_le (trunc P r X) ((X:ℝ)/Y*trunc P r Y) ((X:ℝ)/Y*count P Y)
  have hab : |count P X-(X:ℝ)/Y*count P Y|≤e*X := by linarith [err X]
  rw [show count P X/(X:ℝ)-count P Y/Y=(count P X-(X:ℝ)/Y*count P Y)/X by field_simp,
    abs_div,abs_of_pos hX']
  exact (div_le_iff₀ hX').mpr hab

end GoldbachModelMean.Brun

end

section

noncomputable section
namespace BandTail
open Finset Filter GoldbachModelMean.Brun

def exceptionalPrimes (n X : ℕ) : Finset ℕ := (Icc 1 X).filter (fun p => p.Prime ∧ ¬p∣n)
def meanG (n X : ℕ) : ℝ := (∑ k ∈ Icc 1 X,g n k)/X

theorem count_eq_g (n X T : ℕ) (hT : T≤X) :
    count (exceptionalPrimes n X) T = ∑ k ∈ Icc 1 T,g n k := by
  unfold count
  have hset : Ioc 0 T=Icc 1 T := by ext k;simp;omega
  rw [hset]
  apply sum_congr rfl
  intro k hk
  obtain ⟨hk1,hkT⟩ := mem_Icc.mp hk
  have h0 : k≠0 := by omega
  have he : (hits (exceptionalPrimes n X) k).card=0 ↔ smooth n k := by
    rw [Finset.card_eq_zero]
    constructor
    · intro h p hp
      by_contra hn
      obtain ⟨hp',hpk,_⟩ := Nat.mem_primeFactors.mp hp
      have hpX := (Nat.le_of_dvd (by omega : 0<k) hpk).trans (hkT.trans hT)
      have hmem : p ∈ hits (exceptionalPrimes n X) k := mem_filter.mpr
        ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp'.one_lt.le,hpX⟩,hp',hn⟩,hpk⟩
      simp [h] at hmem
    · intro hs
      apply eq_empty_iff_forall_notMem.mpr
      intro p hpm
      obtain ⟨hP,hpk⟩ := mem_filter.mp hpm
      obtain ⟨_,hp,hn⟩ := mem_filter.mp hP
      exact hn (hs p (Nat.mem_primeFactors.mpr ⟨hp,hpk,h0⟩))
  simp [g,h0,he]

theorem meanG_nonneg (n X : ℕ) : 0≤ meanG n X := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply sum_nonneg
  intro k _
  simp only [g,ArithmeticFunction.coe_mk];split_ifs <;> norm_num

theorem meanG_le_one (n X : ℕ) : meanG n X≤1 := by
  rcases eq_or_ne X 0 with rfl|hx
  · simp [meanG]
  · apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hx)).mpr
    calc
      _ ≤ ∑ k ∈ Icc 1 X, (1:ℝ) := by
        apply sum_le_sum
        intro k _
        simp only [g,ArithmeticFunction.coe_mk];split_ifs <;> norm_num
      _ = _ := by simp

end BandTail

end

section

namespace BandTail
open Finset
noncomputable section

def frequency (P : Finset ℕ) : ℝ := ∑ p ∈ P, (p:ℝ)⁻¹
def hit (p k : ℕ) : ℝ := if p ∣ k then 1 else 0
def hitCount (P : Finset ℕ) (k : ℕ) : ℝ := ∑ p ∈ P, hit p k

theorem hit_sum (p X : ℕ) : (∑ k ∈ Icc 1 X, hit p k) = (X/p : ℕ) := by
  have he : Icc 1 X=Ioc 0 X := by ext k; simp only [mem_Icc,mem_Ioc]; omega
  unfold hit
  rw [he,Finset.sum_boole,Nat.Ioc_filter_dvd_card_eq_div]

theorem firstMoment (P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, 0<p) :
    (X:ℝ)*frequency P-P.card ≤ ∑ k ∈ Icc 1 X,hitCount P k := by
  simp only [hitCount,Finset.sum_comm (s:=Icc 1 X) (t:=P),hit_sum]
  calc
    _ = ∑ p ∈ P, ((X:ℝ)*(p:ℝ)⁻¹-1) := by simp [frequency,mul_sum,sum_sub_distrib]
    _ ≤ _ := by
      apply sum_le_sum
      intro p hp
      have hpr : 0<(p:ℝ) := by exact_mod_cast hP p hp
      have hc : (X:ℝ) < (p:ℝ)*((X/p:ℕ)+1:ℝ) := by exact_mod_cast Nat.lt_mul_div_succ X (hP p hp)
      have hh : (X:ℝ)/(p:ℝ) ≤ ((X/p:ℕ):ℝ)+1 := (div_le_iff₀ hpr).mpr (by linarith)
      linarith [show (X:ℝ)*(p:ℝ)⁻¹ = X/p by rw [div_eq_mul_inv]]

theorem hitPair (X p r : ℕ) (hp : p.Prime) (hr : r.Prime) :
    (∑ k ∈ Icc 1 X,hit p k * hit r k) ≤
      (X:ℝ)*((p:ℝ)⁻¹*(r:ℝ)⁻¹) + (if p=r then (X:ℝ)*(p:ℝ)⁻¹ else 0) := by
  by_cases he : p=r
  · subst r
    have hh (k : ℕ) : hit p k*hit p k=hit p k := by by_cases hk : p∣k <;> simp [hit,hk]
    simp only [hh,hit_sum,ite_true]
    exact (Nat.cast_div_le (α:=ℝ)).trans (by rw [div_eq_mul_inv]; exact le_add_of_nonneg_left (by positivity))
  · have hh (k : ℕ) : hit p k*hit r k=hit (p*r) k := by
      have hc := (Nat.coprime_primes hp hr).mpr he
      have eqv : p*r∣k ↔ p∣k ∧ r∣k := ⟨fun hk => ⟨(dvd_mul_right p r).trans hk,(dvd_mul_left r p).trans hk⟩,fun hk => hc.mul_dvd_of_dvd_of_dvd hk.1 hk.2⟩
      by_cases ha : p∣k <;> by_cases hb : r∣k <;> simp [hit,eqv,ha,hb]
    simp only [hh,hit_sum,if_neg he,add_zero]
    exact (Nat.cast_div_le (α:=ℝ)).trans_eq (by simp [div_eq_mul_inv,mul_comm])

theorem secondMoment (P : Finset ℕ) (X : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ k ∈ Icc 1 X,(hitCount P k)^2) ≤ (X:ℝ)*(frequency P)^2+X*frequency P := by
  have hswap (f : ℕ → ℕ → ℕ → ℝ) :
      (∑ k ∈ Icc 1 X,∑ p ∈ P,∑ r ∈ P,f k p r)=∑ p ∈ P,∑ r ∈ P,∑ k ∈ Icc 1 X,f k p r := by
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_comm
  simp only [hitCount,sq,sum_mul_sum,hswap]
  calc
    _ ≤ ∑ p ∈ P,∑ r ∈ P, ((X:ℝ)*((p:ℝ)⁻¹*(r:ℝ)⁻¹)+(if p=r then (X:ℝ)*(p:ℝ)⁻¹ else 0)) :=
      sum_le_sum fun p hp => sum_le_sum fun r hr => hitPair X p r (hP p hp) (hP r hr)
    _ = _ := by
      simp only [sum_add_distrib,←mul_sum,sum_ite_eq]
      unfold frequency
      congr 1
      · rw [←Finset.sum_mul]
      · rw [mul_sum]
        exact sum_congr rfl fun p hp => by simp [hp]

theorem highH (n X : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ ¬p∣n) :
    frequency P * (∑ k ∈ Icc 1 X, g n k) ≤ (X:ℝ) + 2*P.card := by
  let H := frequency P
  have hH : 0≤H := sum_nonneg fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p)
  rcases hH.eq_or_lt with hz | hpos
  · change H*_ ≤ _
    rw [←hz,zero_mul]; positivity
  have h1 := firstMoment P X (fun p hp => (hP p hp).1.pos)
  have h2 := secondMoment P X (fun p hp => (hP p hp).1)
  have hdom : (∑ k ∈ Icc 1 X, g n k * H^2) ≤ ∑ k ∈ Icc 1 X, (hitCount P k-H)^2 := by
    apply sum_le_sum
    intro k hk
    have hk0 : k≠0 := by have := (mem_Icc.mp hk).1; omega
    by_cases hsm : smooth n k
    · have h0 : hitCount P k=0 := by
        apply sum_eq_zero
        intro p hp
        have hn := (hP p hp).2
        have hpk : ¬p∣k := fun hpk => hn (hsm p (Nat.mem_primeFactors.mpr ⟨(hP p hp).1,hpk,hk0⟩))
        simp [hit,hpk]
      simp [g,hk0,hsm,h0]
    · simp [g,hk0,hsm,sq_nonneg]
  have he (k : ℕ) : (hitCount P k-H)^2=(hitCount P k)^2 - hitCount P k*(2*H)+ H^2 := by ring
  simp only [he,sum_add_distrib,sum_sub_distrib,←sum_mul,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel] at hdom
  change (X:ℝ)*H-_≤_ at h1
  change _≤(X:ℝ)*H^2+X*H at h2
  have h3 := mul_le_mul_of_nonneg_right h1 (mul_nonneg (by norm_num : (0:ℝ)≤2) hpos.le)
  apply le_of_mul_le_mul_right (a:=H) _ hpos
  nlinarith only [hdom,h3,h2]
end
end BandTail

end

section

noncomputable section
namespace BandTail
open Finset Filter GoldbachModelMean.Brun

theorem mean_slow (C e : ℝ) (hC : 1≤C) (he : 0<e) :
    ∀ᶠ X : ℕ in atTop, ∀ Y : ℕ, 0<Y → Y≤X → (X:ℝ)≤C*Y →
    ∀ n, |meanG n X-meanG n Y|≤e := by
  let H : ℝ := (1+2*C)/e
  have hHpos : 0<H := by dsimp [H];positivity
  filter_upwards [uniform_lowH H C e hC he] with X hlow
  intro Y hY hYX hscale n
  let P := exceptionalPrimes n X
  have hprime (p) (hp : p∈P) : p.Prime ∧ ¬p∣n := (mem_filter.mp hp).2
  have hh : harmonic P=frequency P := by simp [GoldbachModelMean.Brun.harmonic,frequency,one_div]
  by_cases hc : harmonic P≤H
  · have hh := hlow Y hY hYX hscale P (fun p h => (hprime p h).1) hc
    rwa [count_eq_g n X X le_rfl,count_eq_g n X Y hYX] at hh
  · have hPH := lt_of_not_ge hc
    rw [hh] at hPH
    have hPcard : P.card≤X := (card_filter_le ..).trans_eq (by simp)
    have hX' : (0:ℝ)<X := by exact_mod_cast hY.trans_le hYX
    have hyp : (0:ℝ)<Y := by exact_mod_cast hY
    have hscaleX : (X:ℝ)≤C*X := by simpa using (mul_le_mul_of_nonneg_right hC hX'.le)
    have hb (T : ℕ) (ht : (0:ℝ)<T) (hscaleT : (X:ℝ)≤C*T) : meanG n T≤e := by
      have hcard' : (P.card:ℝ) ≤ C*T := (show (P.card:ℝ)≤X by exact_mod_cast hPcard).trans hscaleT
      have hbound := highH n T P hprime
      have hp : 0≤∑ k ∈ Icc 1 T,g n k := by
        have hh := meanG_nonneg n T
        unfold meanG at hh
        simpa [ht.ne'] using mul_nonneg hh ht.le
      have hlo := mul_le_mul_of_nonneg_right hPH.le hp
      have hHS : H*(∑ k ∈ Icc 1 T,g n k) ≤ (1+2*C)*T := by linarith
      have hid : (1+2*C)*T=H*(e*T) := by dsimp [H];field_simp
      rw [hid] at hHS
      exact (div_le_iff₀ ht).mpr ((mul_le_mul_iff_right₀ hHpos).mp hHS)
    have hx := hb X hX' hscaleX
    have hy := hb Y hyp hscale
    rw [abs_le]
    constructor <;> linarith [meanG_nonneg n X, meanG_nonneg n Y]

end BandTail

end

section

namespace BandTail
open Finset Filter
noncomputable section

theorem uniform_prefix_floor (R : ℕ) (hR : 1 ≤ R) (δ : ℝ) (hδ : 0<δ) :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∀ n i : ℕ, A ≤ i → i ≤ R*A →
      -(δ*(A:ℝ))  ≤  ∑ q ∈ Finset.Ioc A i,F n q := by
  have hr : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hu : 0<universal := Real.exp_pos _
  let τ : ℝ := δ/(8*((R:ℝ)+1))
  have hτ : 0<τ := by dsimp [τ]; positivity
  let e : ℝ := τ/(universal+1)
  have he : 0<e := by dsimp [e]; positivity
  have heu : universal*e  ≤  τ := by
    have heq : e*(universal+1)=τ := by dsimp [e]; field_simp
    nlinarith
  obtain ⟨N,hN⟩ := exists_nat_ge (universal/τ)
  let J := (N+1)^4
  have hJ : 0<J := by dsimp [J]; positivity
  have hj : (J:ℝ)^(1/4:ℝ)=(N:ℝ)+1 := by
    dsimp [J]; push_cast
    rw [←Real.rpow_natCast_mul (by positivity),show (↑(4:ℕ):ℝ)*(1/4)=1 by norm_num,Real.rpow_one]
  have ht : universal/(J:ℝ)^(1/4:ℝ)  ≤  τ := by
    rw [hj]
    apply (div_le_iff₀ (by positivity)).mpr
    have := (div_le_iff₀ hτ).mp hN
    nlinarith
  let C : ℝ := 2*(R:ℝ)*J
  have hjr : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [mul_le_mul hr hjr (by norm_num) (by positivity)]
  obtain ⟨M,hM⟩ := eventually_atTop.mp (mean_slow C e hC he)
  obtain ⟨L,hL⟩ := exists_nat_ge ((J:ℝ)/e)
  refine ⟨max J (max M L),?_⟩
  intro A hA n i hAi hiA
  have hJA : J ≤ A := by omega
  have hA0 : 0<A := hJ.trans_le hJA
  have hAr : (0:ℝ)<A := by exact_mod_cast hA0
  have hi0 : 0 < i := hA0.trans_le hAi
  have hir : (0:ℝ) < i := by exact_mod_cast hi0
  have hscale : (i:ℝ) ≤ R*(A:ℝ) := by exact_mod_cast hiA
  let t := gAvg n i
  let Z := ∑ d ∈ Icc 1 J,z n d
  have ht01 : 0 ≤ t ∧ t ≤ 1 := g_avg_bounds n i
  have hz : -τ ≤ Z := by have hz' := signedPrefix n J hJ; dsimp [Z]; linarith
  have hlin (X : ℕ) (hAX : A ≤ X) (hXi : X ≤ i) :
      |fSum n X-(X:ℝ)*(Z*t)|  ≤  X*(3*τ) := by
    have hX : 0<X := hA0.trans_le hAX
    have hxr : (0:ℝ)<X := by exact_mod_cast hX
    have hjx : (J:ℝ)/X ≤ e := by
      apply (div_le_iff₀ hxr).mpr
      have hLX : (L:ℝ) ≤ X := by exact_mod_cast (show L ≤ X by omega)
      have := (div_le_iff₀ he).mp (hL.trans hLX)
      linarith
    have hnear (d : ℕ) (hd : d∈Icc 1 J) : |gAvg n (X/d)-t| ≤ e := by
      obtain ⟨hd0,hdJ⟩ := mem_Icc.mp hd
      have hdX : d ≤ X := by omega
      have hy : 0<X/d := Nat.div_pos hdX hd0
      have hii : i ≤ R*X := hiA.trans (Nat.mul_le_mul_left R hAX)
      have hratio : X ≤ (2*J)*(X/d) := by
        calc
          X  ≤  d*(X/d+1) := (Nat.lt_mul_div_succ X hd0).le
          _  ≤  J*(2*(X/d)) := Nat.mul_le_mul hdJ (by omega)
          _ = _ := by ring
      have hcxy : (i:ℝ) ≤ C*(X/d:ℕ) := by
        dsimp [C]
        exact_mod_cast (show i ≤ 2*R*J*(X/d) from hii.trans (by calc
          R*X  ≤  R*((2*J)*(X/d)) := Nat.mul_le_mul_left R hratio
          _ = _ := by ring))
      rw [abs_sub_comm]
      exact hM i (by omega) (X/d) hy ((Nat.div_le_self X d).trans hXi) hcxy n
    have h := dyadic_approx n X J hX hJ (by omega) t e he.le hnear hjx
    have ha : |fSum n X / X - Z*t| ≤ 3*τ := h.trans (by linarith)
    have eqv : fSum n X-(X:ℝ)*(Z*t)=(X:ℝ)*(fSum n X/X-Z*t) := by field_simp
    rw [eqv,abs_mul,abs_of_pos hxr]
    exact mul_le_mul_of_nonneg_left ha hxr.le
  have ha := abs_le.mp (hlin A le_rfl hAi)
  have hb := abs_le.mp (hlin i hAi le_rfl)
  have htZ : -τ  ≤  Z*t := by
    calc
      -τ  ≤  -τ*t := by nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr ht01.2)]
      _  ≤  _ := mul_le_mul_of_nonneg_right hz ht01.1
  have hia : (A:ℝ) ≤ i := by exact_mod_cast hAi
  have hdiff := mul_le_mul_of_nonneg_left htZ (sub_nonneg.mpr hia)
  have heqτ : (8*((R:ℝ)+1))*τ=δ := by dsimp [τ]; field_simp
  have htot : (i:ℝ)*τ  ≤  R*A*τ := mul_le_mul_of_nonneg_right hscale hτ.le
  have hgood : -(δ*(A:ℝ)) ≤ fSum n i-fSum n A := by
    have δeq : δ*(A:ℝ)=(8*((R:ℝ)+1))*τ*A := by rw [heqτ]
    nlinarith only [ha.1,ha.2,hb.1,hb.2,hdiff,htot,δeq,
      mul_nonneg (Nat.cast_nonneg R) (mul_nonneg hAr.le hτ.le),mul_nonneg hAr.le hτ.le]
  have hsplit := prefix_split (fun q => F n q) hAi
  change fSum n i=fSum n A+_ at hsplit
  linarith

end
end BandTail

end


theorem PEqualNP.Outside.L_goldbach_frontier_medcore_model_floor : let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let K := fun (n : ℕ) (β : ℝ) => ∑ k ∈ Finset.range (n+1), E ((k:ℝ)*β); let modelBand := fun (n A B : ℕ) => ∑ q ∈ Finset.Ioc A B, ∑ a ∈ (Finset.range (q+1)).filter (fun a => Nat.Coprime a q), intervalIntegral (fun t => (((∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q), E ((r:ℝ)*(a:ℝ)/(q:ℝ))) / (Nat.totient q : ℂ)) * K n (t - (a:ℝ)/(q:ℝ)))^2 * E (-(n:ℝ)*t)) ((a:ℝ)/(q:ℝ) - (Q n:ℝ)/((q:ℝ)*(n:ℝ))) ((a:ℝ)/(q:ℝ) + (Q n:ℝ)/((q:ℝ)*(n:ℝ))) MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (modelBand n (Q n) (Q₁ n)).re := by
  change ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    -(e*(n:ℝ)) ≤ (GoldbachExplicitModeledMajor.windowModel n
      (GoldbachExplicitModeledMajor.cutoff n) ⌊(n:ℝ)^(1/3:ℝ)⌋₊).re
  intro e he
  obtain ⟨N,hN⟩ := BandTail.floor_from_uniform BandTail.uniform_prefix_floor e he
  exact ⟨N,fun n hn _ => hN n hn ⌊(n:ℝ)^(1/3:ℝ)⌋₊⟩
