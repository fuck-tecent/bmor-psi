import Mathlib

open Finset

namespace GoldbachFiniteSieve

noncomputable def centralMass (n : ℕ) : ℝ :=
  let w := fun p : ℕ => if p.Prime then Real.log (p : ℝ) else 0
  ∑ k ∈ (range (n+1)).filter (fun k => n ≤ 3*k ∧ 3*k ≤ 2*n), w k * w (n-k)

theorem log_weighted_error (n z : ℕ) (hn : 1 ≤ n) (hz : z^8 ≤ n) :
    (Real.log (n : ℝ))^2 * (2 * (z : ℝ)^4) ≤ 32 * (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  let s := Real.sqrt (Real.sqrt (n : ℝ))
  have hlog : Real.log (n : ℝ) ≤ 4 * s := by
    have hspos : 0 < s := by dsimp [s]; positivity
    have hb := Real.log_le_sub_one_of_pos hspos
    have hlogS : Real.log s = Real.log (n : ℝ) / 2 / 2 := by
      dsimp [s]
      rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hn0]
    linarith only [hb, hlogS]
  have hlog2 := (sq_le_sq₀ (Real.log_nonneg hnR) (show 0 ≤ 4*s by dsimp [s]; positivity)).mpr hlog
  have hzR : (z : ℝ)^8 ≤ n := by exact_mod_cast hz
  have hz4 : (z : ℝ)^4 ≤ Real.sqrt n := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hn0, ← pow_mul]
    exact hzR
  calc
    _ ≤ (4*s)^2 * (2 * Real.sqrt n) :=
      mul_le_mul hlog2 (by linarith only [hz4]) (by positivity) (sq_nonneg _)
    _ = 32 * s^2 * Real.sqrt n := by ring
    _ = 32 * (Real.sqrt n)^2 := by rw [show s^2 = Real.sqrt n from Real.sq_sqrt (Real.sqrt_nonneg _)]; ring
    _ = _ := by rw [Real.sq_sqrt hn0]

end GoldbachFiniteSieve

namespace GoldbachSieve

/-- Product of the chosen primes, including the empty product. -/
def modulus (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

/-- Multiplicative weight on a finite set of primes. -/
noncomputable def mass (g : ℕ → ℝ) (s : Finset ℕ) : ℝ := ∏ p ∈ s, g p

/-- Weight retained by a cutoff on the squarefree modulus. -/
noncomputable def retained (P : Finset ℕ) (g : ℕ → ℝ) (z : ℕ) : ℝ :=
  ∑ s ∈ P.powerset.filter (fun s => modulus s ≤ z), mass g s

private theorem mass_nonneg {g : ℕ → ℝ} {s : Finset ℕ} (h : ∀ p ∈ s, 0 ≤ g p) :
    0 ≤ mass g s := prod_nonneg h

theorem total_mass (P : Finset ℕ) (g : ℕ → ℝ) :
    ∑ s ∈ P.powerset, mass g s = ∏ p ∈ P, (1 + g p) := (prod_one_add P).symm

/-- The first moment of an additive cost in the product-weighted distribution. -/
theorem cost_moment (P : Finset ℕ) (g c : ℕ → ℝ) (hg : ∀ p ∈ P, 0 ≤ g p) :
    (∑ s ∈ P.powerset, mass g s * (∑ p ∈ s, c p)) =
      (∏ p ∈ P, (1 + g p)) * ∑ p ∈ P, (g p / (1 + g p)) * c p := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [mass]
  | @insert a P ha ih =>
    have hgP : ∀ p ∈ P, 0 ≤ g p := fun p hp => hg p (mem_insert_of_mem hp)
    have hga := hg a (mem_insert_self a P)
    have expand (s : Finset ℕ) (hs : s ∈ P.powerset) :
        mass g (insert a s) * (∑ p ∈ insert a s, c p) =
        (g a * c a) * mass g s + g a * (mass g s * ∑ p ∈ s, c p) := by
      have h : a ∉ s := fun h => ha (mem_powerset.mp hs h)
      rw [mass, prod_insert h, sum_insert h]; unfold mass; ring
    rw [sum_powerset_insert ha, sum_congr rfl expand, sum_add_distrib, ← mul_sum, ← mul_sum,
      total_mass, ih hgP, prod_insert ha, sum_insert ha]
    field_simp [show 1 + g a ≠ 0 by linarith]
    ring

private theorem log_modulus {P : Finset ℕ} (hp : ∀ p ∈ P, 0 < p) :
    Real.log (modulus P : ℝ) = ∑ p ∈ P, Real.log (p : ℝ) := by
  unfold modulus
  rw [Nat.cast_prod, Real.log_prod]
  exact fun p h => by exact_mod_cast (hp p h).ne'

/-- A log-cost budget of half the cutoff retains at least half the full Euler product. -/
theorem half_mass (P : Finset ℕ) (g : ℕ → ℝ) (z : ℕ) (hz : 1 < z)
    (hp : ∀ p ∈ P, 0 < p) (hg : ∀ p ∈ P, 0 ≤ g p)
    (hbudget : (∑ p ∈ P, (g p / (1 + g p)) * Real.log (p : ℝ)) ≤ Real.log z / 2) :
    (∏ p ∈ P, (1 + g p)) / 2 ≤ retained P g z := by
  have hcost := cost_moment P g (fun p => Real.log (p : ℝ)) hg
  let bad := P.powerset.filter (fun s => ¬modulus s ≤ z)
  let L := Real.log (z : ℝ)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hz)
  have htotal : 0 ≤ ∏ p ∈ P, (1 + g p) := prod_nonneg fun p h => by linarith [hg p h]
  have hbad : L * (∑ s ∈ bad, mass g s) ≤
      ∑ s ∈ P.powerset, mass g s * ∑ p ∈ s, Real.log (p : ℝ) := by
    rw [mul_sum]
    apply le_trans (sum_le_sum (g := fun s => mass g s * ∑ p ∈ s, Real.log (p : ℝ)) ?_) (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) ?_)
    · intro s hs
      obtain ⟨hsP, hsz⟩ := mem_filter.mp hs
      have hsub := mem_powerset.mp hsP
      rw [← log_modulus (fun p h => hp p (hsub h)), mul_comm L]
      apply mul_le_mul_of_nonneg_left _ (mass_nonneg (fun p h => hg p (hsub h)))
      exact Real.log_le_log (by exact_mod_cast (Nat.zero_lt_of_lt hz)) (by exact_mod_cast (le_of_not_ge hsz))
    · intro s hs _
      have hsub := mem_powerset.mp hs
      exact mul_nonneg (mass_nonneg fun p h => hg p (hsub h))
        (sum_nonneg fun p h => Real.log_nonneg (by exact_mod_cast hp p (hsub h)))
  have budget := mul_le_mul_of_nonneg_left hbudget htotal
  rw [hcost] at hbad
  have hsplit : retained P g z + (∑ s ∈ bad, mass g s) = ∏ p ∈ P, (1 + g p) :=
    (sum_filter_add_sum_filter_not P.powerset (fun s => modulus s ≤ z) (mass g)).trans (total_mass P g)
  have hsmall : (∑ s ∈ bad, mass g s) ≤ (∏ p ∈ P, (1 + g p)) / 2 := by
    apply le_of_mul_le_mul_left _ hL
    change L * _ ≤ L * _
    dsimp only [L] at *
    linarith only [hbad, budget]
  linarith only [hsplit, hsmall]

end GoldbachSieve

namespace GoldbachSieve

/-- All odd primes up to the indicated bound. -/
def oddPrimes (y : ℕ) : Finset ℕ := y.factorial.primeFactors.filter (fun p => 2 < p)

theorem mem_oddPrimes {p y : ℕ} : p ∈ oddPrimes y ↔ p.Prime ∧ 2 < p ∧ p ≤ y := by
  simp only [oddPrimes, mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, hd⟩, h⟩
    exact ⟨hp, h, hp.dvd_factorial.mp hd.1⟩
  · rintro ⟨hp, h, hle⟩
    exact ⟨⟨hp, hp.dvd_factorial.mpr hle, y.factorial_ne_zero⟩, h⟩

/-- Sum of prime logarithms with factorial multiplicities. -/
private theorem log_factorial_split (y : ℕ) :
    (∑ p ∈ y.factorial.primeFactors, (y.factorial.factorization p : ℝ) * Real.log p) =
      Real.log (y.factorial : ℝ) := by
  have hn := Nat.prod_primeFactors_pow_factorization y.factorial_ne_zero
  have hr : (y.factorial : ℝ) = ∏ p ∈ y.factorial.primeFactors, (p : ℝ) ^ y.factorial.factorization p := by
    exact_mod_cast hn
  rw [hr, Real.log_prod]
  · simp only [Real.log_pow]
  · intro p hp
    exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)

/-- An elementary upper bound on the logarithmic cost of the prime sieve. -/
theorem prime_log_cost (y : ℕ) (hy : 1 ≤ y) :
    (∑ p ∈ oddPrimes y, Real.log (p : ℝ) / p) ≤ 2 * Real.log y := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hsum : (y : ℝ) * (∑ p ∈ oddPrimes y, Real.log (p : ℝ) / p) ≤
      2 * Real.log (y.factorial : ℝ) := by
    rw [← log_factorial_split, mul_sum, mul_sum]
    apply le_trans (sum_le_sum (g := fun p => 2 * ((y.factorial.factorization p : ℝ) * Real.log p)) ?_)
    · apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro p hp _
      exact mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)))
    · intro p hm
      obtain ⟨hp, -, hpy⟩ := mem_oddPrimes.mp hm
      have he : y / p ≤ y.factorial.factorization p := by
        rw [Nat.factorization_factorial hp (show Nat.log p y < Nat.log p y + 2 by omega)]
        simpa using single_le_sum (f := fun i : ℕ => y / p^i) (fun _ _ => Nat.zero_le _) (show 1 ∈ Ico 1 (Nat.log p y + 2) by simp)
      have hpq : p ≤ (y / p) * p := by simpa using Nat.mul_le_mul_right p (Nat.div_pos hpy hp.pos)
      have hdiv := Nat.mod_add_div y p
      have hrem := Nat.mod_lt y hp.pos
      have hfloor : y ≤ 2 * ((y / p) * p) := by rw [Nat.mul_comm p] at hdiv; omega
      have hnat : y ≤ 2 * (y.factorial.factorization p * p) := hfloor.trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right p he))
      have hc : (y : ℝ) ≤ 2 * ((y.factorial.factorization p : ℝ) * (p : ℝ)) := by exact_mod_cast hnat
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hlog := Real.log_nonneg (show (1 : ℝ) ≤ p by exact_mod_cast hp.one_le)
      rw [← mul_div_assoc, div_le_iff₀ hpR]
      nlinarith only [mul_le_mul_of_nonneg_right hc hlog]
  have hfac := Real.log_le_log (show (0 : ℝ) < y.factorial by exact_mod_cast y.factorial_pos)
    (show (y.factorial : ℝ) ≤ (y : ℝ)^y by exact_mod_cast y.factorial_le_pow)
  rw [Real.log_pow] at hfac
  apply le_of_mul_le_mul_left _ hyR
  linarith only [hsum, hfac]

/-- A finite Euler product over the prime divisors of a positive integer. -/
private theorem divisor_reciprocal_le (m : ℕ) (hm : m ≠ 0) :
    (∑ d ∈ m.divisors, (d : ℝ)⁻¹) ≤ ∏ p ∈ m.primeFactors, ((p : ℝ) / (p-1)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hsum : (∑ d ∈ m.divisors, (d : ℝ)⁻¹) * m = ∑ d ∈ m.divisors, (d : ℝ) := by
    rw [sum_mul, ← Nat.sum_div_divisors m (fun d => (d : ℝ))]
    apply sum_congr rfl
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    have hdn := Nat.dvd_of_mem_divisors hd
    rw [Nat.cast_div hdn hd0]
    ring
  have hsig : (∑ d ∈ m.divisors, (d : ℝ)) =
      ∏ p ∈ m.primeFactors, (∑ k ∈ range (m.factorization p + 1), (p : ℝ)^k) := by
    simpa only [Nat.cast_sum, Nat.cast_prod, Nat.cast_pow] using congrArg (fun k : ℕ => (k : ℝ)) (Nat.sum_divisors hm)
  have hmprod : (m : ℝ) = ∏ p ∈ m.primeFactors, (p : ℝ) ^ m.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hm
  apply le_of_mul_le_mul_right _ hmR
  rw [hsum, hsig]
  conv_rhs => rw [hmprod, ← prod_mul_distrib]
  refine prod_le_prod₀ ?_ ?_
  · intro p hp
    exact sum_nonneg fun _ _ => by positivity
  intro p hp
  have hpR : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  rw [geom_sum_eq (ne_of_gt hpR), div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by linarith)]
  rw [pow_succ]; linarith only

/-- The full one-dimensional Euler product dominates the harmonic sum up to `y`. -/
theorem log_le_twice_odd_product (y : ℕ) (hy : 2 ≤ y) :
    Real.log (y : ℝ) ≤ 2 * ∏ p ∈ oddPrimes y, ((p : ℝ) / (p-1)) := by
  have incl : Icc 1 y ⊆ y.factorial.divisors := fun d hd =>
    Nat.mem_divisors.mpr ⟨Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2, y.factorial_ne_zero⟩
  have hbound := (sum_le_sum_of_subset_of_nonneg (f := fun d : ℕ => (d : ℝ)⁻¹) incl
    (fun _ _ _ => by positivity)).trans (divisor_reciprocal_le _ y.factorial_ne_zero)
  have htwo : 2 ∈ y.factorial.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, Nat.prime_two.dvd_factorial.mpr hy, y.factorial_ne_zero⟩
  have odd : y.factorial.primeFactors.erase 2 = oddPrimes y := by
    ext p
    simp only [mem_erase, oddPrimes, mem_filter]
    constructor
    · rintro ⟨hne, hp⟩
      exact ⟨hp, by have := (Nat.prime_of_mem_primeFactors hp).two_le; omega⟩
    · rintro ⟨hp, hlt⟩
      exact ⟨by omega, hp⟩
  have hprod := mul_prod_erase y.factorial.primeFactors (fun p : ℕ => (p : ℝ) / (p-1)) htwo
  rw [odd] at hprod
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, div_one] at hprod
  have hlog := log_add_one_le_harmonic y
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hlog
  exact (Real.log_le_log (by exact_mod_cast Nat.zero_lt_of_lt hy) (by exact_mod_cast Nat.le_succ y)).trans (hlog.trans (hbound.trans_eq hprod.symm))

end GoldbachSieve

namespace GoldbachSieve

/-- Number of forbidden residue classes at a prime. -/
def rho (n p : ℕ) : ℕ := if p ∣ n then 1 else 2

noncomputable def gain (n p : ℕ) : ℝ := (rho n p : ℝ) / (p - (rho n p : ℝ))

noncomputable def singular (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ)-2))

theorem rho_bounds (n p : ℕ) : 1 ≤ rho n p ∧ rho n p ≤ 2 := by unfold rho; split_ifs <;> decide

theorem gain_bounds (n p : ℕ) (hp : 2 < p) : 0 ≤ gain n p ∧ gain n p ≤ 2 := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hlo : (1 : ℝ) ≤ rho n p := by exact_mod_cast (rho_bounds n p).1
  have hhi : (rho n p : ℝ) ≤ 2 := by exact_mod_cast (rho_bounds n p).2
  have hd : 0 < (p : ℝ) - rho n p := by linarith
  exact ⟨div_nonneg (by linarith) hd.le, (div_le_iff₀ hd).mpr (by linarith)⟩

theorem gain_relation (n p : ℕ) (hp : 2 < p) :
    gain n p * ((p : ℝ) - rho n p) = (rho n p : ℝ) := by
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  have hr : (rho n p : ℝ) ≤ 2 := by exact_mod_cast (rho_bounds n p).2
  exact div_mul_cancel₀ _ (by linarith)

end GoldbachSieve

namespace GoldbachSieve

theorem modulus_pos {P : Finset ℕ} (hp : ∀ p ∈ P, p.Prime) : 0 < modulus P :=
  prod_pos fun p h => (hp p h).pos

theorem prime_dvd_modulus {P : Finset ℕ} {p : ℕ} (h : p ∈ P) : p ∣ modulus P :=
  Finset.dvd_prod_of_mem (fun p : ℕ => p) h

/-- A local test is evaluated at the canonical representative modulo each prime. -/
noncomputable def localTest (P : Finset ℕ) (f : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  ∏ p ∈ P, f p (k % p)

private theorem localTest_mod (P : Finset ℕ) (f : ℕ → ℕ → ℝ) (k : ℕ) :
    localTest P f (k % modulus P) = localTest P f k := by
  apply prod_congr rfl
  intro p hp
  rw [Nat.mod_mod_of_dvd k (prime_dvd_modulus hp)]

/-- A two-coordinate CRT change of variables in a finite sum. -/
private theorem sum_crt {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : a.Coprime b)
    (f g : ℕ → ℝ) : (∑ k ∈ range (a*b), f (k % a) * g (k % b)) =
    (∑ i ∈ range a, f i) * (∑ j ∈ range b, g j) := by
  calc
    _ = ∑ t ∈ (range a) ×ˢ (range b), f t.1 * g t.2 := by
      apply sum_bij (fun k _ => (k % a, k % b))
      · intro k hk
        exact mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ ha), mem_range.mpr (Nat.mod_lt _ hb)⟩
      · intro k hk l hl h
        have hm : k ≡ l [MOD a*b] := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp
          ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
        simpa only [Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp hk), Nat.mod_eq_of_lt (mem_range.mp hl)] using hm
      · rintro ⟨i,j⟩ ht
        obtain ⟨hi,hj⟩ := mem_product.mp ht
        let k := Nat.chineseRemainder hc i j
        exact ⟨k.val, mem_range.mpr (Nat.chineseRemainder_lt_mul hc i j ha.ne' hb.ne'),
          Prod.ext (Eq.trans k.property.1 (Nat.mod_eq_of_lt (mem_range.mp hi)))
            (Eq.trans k.property.2 (Nat.mod_eq_of_lt (mem_range.mp hj)))⟩
      · intro _ _; rfl
    _ = _ := by rw [sum_product]; simp_rw [← mul_sum]; rw [sum_mul]

/-- Independence of all prime coordinates over one full period. -/
theorem sum_localTest (P : Finset ℕ) (f : ℕ → ℕ → ℝ) (hp : ∀ p ∈ P, p.Prime) :
    (∑ k ∈ range (modulus P), localTest P f k) = ∏ p ∈ P, ∑ j ∈ range p, f p j := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [modulus, localTest]
  | @insert a P ha ih =>
    have hP : ∀ p ∈ P, p.Prime := fun p h => hp p (mem_insert_of_mem h)
    have hprime := hp a (mem_insert_self _ _)
    have hc : a.Coprime (modulus P) := Nat.coprime_prod_right_iff.mpr fun p h =>
      (Nat.coprime_primes hprime (hP p h)).mpr (fun e => ha (e ▸ h))
    have hmod : modulus (insert a P) = a * modulus P := by simp [modulus, ha]
    have step (k : ℕ) : localTest (insert a P) f k = f a (k % a) * localTest P f (k % modulus P) := by
      rw [localTest_mod]; simp [localTest, ha]
    simp_rw [hmod, step]
    rw [sum_crt hprime.pos (modulus_pos hP) hc, ih hP, prod_insert ha]

/-- One incomplete period costs at most `q * B` when the complete-period mean is nonnegative. -/
theorem interval_le_mean_error (x q : ℕ) (hq : 0 < q) (f : ℕ → ℝ) (hperiod : Function.Periodic f q)
    (m B : ℝ) (hm : 0 ≤ m) (hB : 0 ≤ B) (hf : ∀ k, f k ≤ B)
    (hmean : (∑ k ∈ range q, f k) = q*m) :
    (∑ k ∈ range x, f k) ≤ x*m + q*B := by
  have complete (a b : ℕ) : (∑ k ∈ range (a*q+b), f k) = (a : ℝ)*((q : ℝ)*m) + ∑ k ∈ range b, f k := by
    induction a with
    | zero => simp
    | succ a ih =>
      rw [show (a+1)*q+b = q+(a*q+b) by ring, sum_range_add, hmean]
      have hshift (k : ℕ) : f (q+k) = f k := by rw [Nat.add_comm]; exact hperiod k
      simp_rw [hshift]
      rw [ih, Nat.cast_succ]; ring
  have hx := Nat.div_add_mod x q
  rw [Nat.mul_comm] at hx
  have split := complete (x/q) (x % q)
  rw [hx] at split
  have hxR : ((x / q : ℕ) : ℝ) * q ≤ x := by exact_mod_cast Nat.div_mul_le_self x q
  have htail : (∑ k ∈ range (x % q), f k) ≤ ((x % q : ℕ) : ℝ)*B := by
    calc _ ≤ ∑ _k ∈ range (x % q), B := sum_le_sum fun k _ => hf k
         _ = _ := by simp [nsmul_eq_mul]
  have hrem : ((x % q : ℕ) : ℝ) ≤ q := by exact_mod_cast (Nat.mod_lt x hq).le
  rw [split]
  linarith only [mul_le_mul_of_nonneg_right hxR hm, mul_le_mul_of_nonneg_right hrem hB, htail]

end GoldbachSieve

namespace GoldbachSieve

theorem singular_ge_one (n : ℕ) : 1 ≤ singular n := by
  apply one_le_prod₀
  intro p hp
  have h : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
  exact le_add_of_nonneg_right (by positivity)

private noncomputable def correction (n p : ℕ) : ℝ := if p ∣ n then 1 + 1 / ((p : ℝ)-2) else 1

private theorem euler_comparison (n p : ℕ) (hp : 2 < p) :
    ((p : ℝ) / (p-1))^2 ≤ (1 + gain n p) * correction n p := by
  have h : (2 : ℝ) < p := by exact_mod_cast hp
  have ha : (0 : ℝ) < p-1 := by linarith
  have hb : (0 : ℝ) < p-2 := by linarith
  have heq : (1 + gain n p) * correction n p = (p : ℝ) / (p-2) := by
    by_cases hd : p ∣ n <;> simp only [gain, rho, correction, hd, ite_true, ite_false, Nat.cast_one, Nat.cast_ofNat, mul_one]
    all_goals field_simp [ha.ne', hb.ne']
    all_goals ring
  rw [heq, div_pow, div_le_div_iff₀ (sq_pos_of_pos ha) hb]
  nlinarith only [h]

private theorem prod_correction_le (n y : ℕ) (hn : n ≠ 0) :
    (∏ p ∈ oddPrimes y, correction n p) ≤ singular n := by
  change (∏ p ∈ oddPrimes y, if p ∣ n then 1 + 1/((p:ℝ)-2) else 1) ≤ _
  rw [← prod_filter]
  apply prod_le_prod_of_subset_of_one_le₀
  · intro p hp
    rcases mem_filter.mp hp with ⟨hm, hdiv⟩
    obtain ⟨hpp, h2, -⟩ := mem_oddPrimes.mp hm
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp,hdiv,hn⟩,h2⟩
  · intro p hp
    have h : (2 : ℝ) < p := by exact_mod_cast (mem_oddPrimes.mp (mem_filter.mp hp).1).2.1
    positivity
  · intro p hp _
    have h : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    exact le_add_of_nonneg_right (by positivity)

/-- The lower bound on the truncated, two-dimensional sieve denominator. -/
theorem denominator_lower (n y z : ℕ) (hn : n ≠ 0) (hy : 2 ≤ y) (hyz : y^8 ≤ z) :
    (Real.log (y : ℝ))^2 ≤ 8 * singular n * retained (oddPrimes y) (gain n) z := by
  let P := oddPrimes y
  have hp (p : ℕ) (h : p ∈ P) := mem_oddPrimes.mp h
  have hg (p : ℕ) (h : p ∈ P) := gain_bounds n p (hp p h).2.1
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast (by omega : 1 ≤ y)
  have hlog := Real.log_nonneg hyR
  have hz : 1 < z := lt_of_lt_of_le (one_lt_pow₀ (by omega : 1 < y) (by decide : (8:ℕ) ≠ 0)) hyz
  have hpow := Real.log_le_log (show (0 : ℝ) < (y : ℝ)^8 by positivity) (show (y : ℝ)^8 ≤ z by exact_mod_cast hyz)
  rw [Real.log_pow] at hpow
  norm_num only [Nat.cast_ofNat] at hpow
  have hbudget : (∑ p ∈ P, (gain n p / (1+gain n p)) * Real.log (p : ℝ)) ≤ Real.log z / 2 := by
    have hsum : (∑ p ∈ P, (gain n p / (1+gain n p)) * Real.log (p : ℝ)) ≤
        2 * (∑ p ∈ P, Real.log (p : ℝ) / p) := by
      rw [mul_sum]; apply sum_le_sum
      intro p h
      have hrel := gain_relation n p (hp p h).2.1
      have hd : 0 < 1 + gain n p := by linarith [(hg p h).1]
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hp p h).1.pos
      have hfrac : gain n p / (1+gain n p) = (rho n p : ℝ) / p := by
        apply (div_eq_div_iff hd.ne' hp0.ne').mpr; linarith only [hrel]
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (hp p h).1.one_le)
      have hρ : (rho n p : ℝ) ≤ 2 := by exact_mod_cast (rho_bounds n p).2
      rw [hfrac]
      calc _ ≤ (2 / (p : ℝ)) * Real.log p := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hρ hp0.le) hlogp
           _ = _ := by ring
    have hprime := prime_log_cost y (by omega)
    dsimp [P] at hsum ⊢; linarith only [hsum, hprime, hpow]
  have hhalf := half_mass P (gain n) z hz (fun p h => (hp p h).1.pos) (fun p h => (hg p h).1) hbudget
  have htot : 0 ≤ ∏ p ∈ P, (1 + gain n p) := prod_nonneg fun p h => by linarith [(hg p h).1]
  have hloc : (∏ p ∈ P, ((p:ℝ)/(p-1)))^2 ≤ (∏ p ∈ P, (1+gain n p)) * singular n := calc
    _ = ∏ p ∈ P, ((p:ℝ)/(p-1))^2 := (prod_pow _ _ _).symm
    _ ≤ ∏ p ∈ P, ((1+gain n p) * correction n p) := prod_le_prod₀ (fun _ _ => sq_nonneg _) (fun p h => euler_comparison n p (hp p h).2.1)
    _ = _ := prod_mul_distrib
    _ ≤ _ := mul_le_mul_of_nonneg_left (prod_correction_le n y hn) htot
  have hbase := log_le_twice_odd_product y hy
  have hsquare := mul_self_le_mul_self hlog hbase
  have hscaled := mul_le_mul_of_nonneg_right hhalf (le_trans (by norm_num) (singular_ge_one n))
  change (Real.log (y : ℝ))^2 ≤ 8 * singular n * retained P (gain n) z
  change Real.log (y : ℝ) * Real.log y ≤ (2 * (∏ p ∈ P, ((p:ℝ)/(p-1)))) * _ at hsquare
  nlinarith only [hsquare, hloc, hscaled]

end GoldbachSieve

namespace GoldbachSieve

/-- The local centered test takes the value `gain` at each surviving residue. -/
noncomputable def atom (n p j : ℕ) : ℝ := if j = 0 ∨ j = n % p then -1 else gain n p

private theorem count_bad (n p : ℕ) (hp : 0 < p) :
    ((range p).filter (fun j => j = 0 ∨ j = n % p)).card = rho n p := by
  have hs : (range p).filter (fun j => j = 0 ∨ j = n % p) = {0, n % p} := by
    ext j
    simp only [mem_filter, mem_range, mem_insert, mem_singleton]
    exact ⟨And.right, fun h => ⟨by rcases h with rfl | rfl; exact hp; exact Nat.mod_lt _ hp, h⟩⟩
  rw [hs, rho]
  by_cases h : p ∣ n
  · simp [h, Nat.mod_eq_zero_of_dvd h]
  · have hn : 0 ≠ n % p := Ne.symm (mt Nat.dvd_of_mod_eq_zero h)
    simp [h, hn]

private theorem sum_classes (n p : ℕ) (hp : 0 < p) (a b : ℝ) :
    (∑ j ∈ range p, if j = 0 ∨ j = n % p then b else a) =
      (rho n p : ℝ)*b + ((p : ℝ) - rho n p)*a := by
  have expand (j : ℕ) : (if j = 0 ∨ j = n % p then b else a) =
      a + (b-a) * (if j = 0 ∨ j = n % p then 1 else 0) := by split_ifs <;> ring
  simp_rw [expand]
  rw [sum_add_distrib, ← mul_sum, sum_boole, count_bad n p hp, sum_const, card_range, nsmul_eq_mul]
  ring

private theorem sum_atom (n p : ℕ) (hp : 2 < p) : (∑ j ∈ range p, atom n p j) = 0 := by
  unfold atom
  rw [sum_classes n p (by omega)]
  linarith only [gain_relation n p hp]

private theorem sum_atom_sq (n p : ℕ) (hp : 2 < p) :
    (∑ j ∈ range p, atom n p j * atom n p j) = (p : ℝ) * gain n p := by
  have step (j : ℕ) : atom n p j * atom n p j =
      (if j = 0 ∨ j = n % p then (1:ℝ) else gain n p * gain n p) := by
    unfold atom; split_ifs <;> ring
  simp_rw [step]
  rw [sum_classes n p (by omega)]
  have h := gain_relation n p hp
  nlinarith only [h, congrArg (fun x : ℝ => x * gain n p) h]

noncomputable def test (n : ℕ) (s : Finset ℕ) (k : ℕ) : ℝ := localTest s (atom n) k

private noncomputable def both (n : ℕ) (s t : Finset ℕ) (p j : ℕ) : ℝ :=
  (if p ∈ s then atom n p j else 1) * (if p ∈ t then atom n p j else 1)

private theorem test_pair (n : ℕ) (s t : Finset ℕ) (k : ℕ) :
    test n s k * test n t k = localTest (s ∪ t) (both n s t) k := by
  simp only [test, localTest, both, prod_mul_distrib, prod_ite_mem, inter_eq_right.mpr (show s ⊆ s ∪ t from subset_union_left),
    inter_eq_right.mpr (show t ⊆ s ∪ t from subset_union_right)]

private theorem test_abs (n : ℕ) (s : Finset ℕ) (k : ℕ) (hodd : ∀ p ∈ s, 2 < p) :
    |test n s k| ≤ (modulus s : ℝ) := by
  unfold test localTest modulus
  rw [abs_prod, Nat.cast_prod]
  refine prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun p h => ?_)
  have hp : (2 : ℝ) < p := by exact_mod_cast hodd p h
  have hG := gain_bounds n p (hodd p h)
  unfold atom; split_ifs
  · rw [abs_neg, abs_one]; linarith
  · rw [abs_of_nonneg hG.1]; linarith

/-- Orthogonality of two squarefree tests over their common period. -/
theorem pair_period_sum (n : ℕ) (s t : Finset ℕ) (hp : ∀ p ∈ s ∪ t, p.Prime ∧ 2 < p) :
    (∑ k ∈ range (modulus (s ∪ t)), test n s k * test n t k) =
      (modulus (s ∪ t) : ℝ) * (if s = t then mass (gain n) s else 0) := by
  simp_rw [test_pair]
  rw [sum_localTest _ _ (fun p h => (hp p h).1)]
  by_cases hst : s = t
  · subst t
    simp only [union_idempotent, eq_self, ite_true] at *
    unfold modulus mass
    rw [Nat.cast_prod, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p h
    simpa only [both, h, ite_true] using sum_atom_sq n p (hp p h).2
  · rw [ite_eq_right hst, mul_zero]
    apply prod_eq_zero_iff.mpr
    by_cases h : s ⊆ t
    · obtain ⟨p, ht, hs⟩ := Finset.not_subset.mp (fun hh : t ⊆ s => hst (Subset.antisymm h hh))
      have hu : p ∈ s ∪ t := mem_union_right _ ht
      exact ⟨p, hu, by simpa only [both, hs, ht, ite_false, ite_true, one_mul] using sum_atom n p (hp p hu).2⟩
    · obtain ⟨p, hs, ht⟩ := Finset.not_subset.mp h
      have hu : p ∈ s ∪ t := mem_union_left _ hs
      exact ⟨p, hu, by simpa only [both, hs, ht, ite_false, ite_true, mul_one] using sum_atom n p (hp p hu).2⟩

/-- Orthogonality on an initial segment, with an error uniform in the two tests. -/
theorem pair_interval (n x z : ℕ) (s t : Finset ℕ) (hs : modulus s ≤ z) (ht : modulus t ≤ z)
    (hp : ∀ p ∈ s ∪ t, p.Prime ∧ 2 < p) :
    (∑ k ∈ range x, test n s k * test n t k) ≤
      x * (if s = t then mass (gain n) s else 0) + (z : ℝ)^4 := by
  let u := s ∪ t
  have hsp (p : ℕ) (h : p ∈ s) := hp p (mem_union_left _ h)
  have htp (p : ℕ) (h : p ∈ t) := hp p (mem_union_right _ h)
  have hq : 0 < modulus u := modulus_pos (fun p h => (hp p h).1)
  have hperiod : Function.Periodic (fun k => test n s k * test n t k) (modulus u) := by
    intro k
    simp only [test_pair, localTest]
    apply prod_congr rfl
    intro p h
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (prime_dvd_modulus (show p ∈ u from h)), Nat.add_zero, Nat.mod_mod]
  have hm : 0 ≤ (if s = t then mass (gain n) s else 0) := by
    split_ifs
    · exact prod_nonneg fun p h => (gain_bounds n p (hsp p h).2).1
    · exact le_rfl
  have hsR : (modulus s : ℝ) ≤ z := by exact_mod_cast hs
  have htR : (modulus t : ℝ) ≤ z := by exact_mod_cast ht
  have hB (k : ℕ) : test n s k * test n t k ≤ (z : ℝ)^2 := calc
    _ ≤ |test n s k * test n t k| := le_abs_self _
    _ = _ := abs_mul _ _
    _ ≤ (z : ℝ)*(z : ℝ) := mul_le_mul ((test_abs n s k (fun p h => (hsp p h).2)).trans hsR)
      ((test_abs n t k (fun p h => (htp p h).2)).trans htR) (abs_nonneg _) (Nat.cast_nonneg _)
    _ = _ := (sq _).symm
  have hqle : (modulus u : ℝ) ≤ (z : ℝ)^2 := by
    have hmuls : modulus u * modulus (s ∩ t) = modulus s * modulus t := prod_union_inter
    have hpos : 1 ≤ modulus (s ∩ t) := modulus_pos (fun p h => (hsp p (mem_inter.mp h).1).1)
    exact_mod_cast (calc modulus u ≤ modulus u * modulus (s ∩ t) := by simpa using Nat.mul_le_mul_left (modulus u) hpos
                         _ = _ := hmuls
                         _ ≤ z^2 := by simpa [sq] using Nat.mul_le_mul hs ht)
  have hinter := interval_le_mean_error x (modulus u) hq _ hperiod _ _ hm (sq_nonneg _) hB (pair_period_sum n s t hp)
  apply hinter.trans
  apply add_le_add le_rfl
  calc _ ≤ (z : ℝ)^2 * (z : ℝ)^2 := mul_le_mul_of_nonneg_right hqle (sq_nonneg _)
       _ = _ := by ring

end GoldbachSieve

namespace GoldbachSieve

def family (y z : ℕ) := (oddPrimes y).powerset.filter (fun s => modulus s ≤ z)

private theorem family_mem {s : Finset ℕ} {y z : ℕ} (h : s ∈ family y z) :
    s ⊆ oddPrimes y ∧ modulus s ≤ z := ⟨mem_powerset.mp (mem_filter.mp h).1, (mem_filter.mp h).2⟩

private theorem family_card (y z : ℕ) : (family y z).card ≤ z := by
  have hprime {s : Finset ℕ} (h : s ∈ family y z) : ∀ p ∈ s, p.Prime :=
    fun p h' => (mem_oddPrimes.mp ((family_mem h).1 h')).1
  calc
    _ = ((family y z).image modulus).card := by
      symm; apply card_image_of_injOn
      intro s hs t ht heq
      simpa only [modulus, Nat.primeFactors_prod (hprime hs), Nat.primeFactors_prod (hprime ht)] using congrArg Nat.primeFactors heq
    _ ≤ (Icc 1 z).card := by
      apply card_le_card
      intro d hd
      obtain ⟨s,hs,rfl⟩ := mem_image.mp hd
      exact mem_Icc.mpr ⟨modulus_pos (hprime hs), (family_mem hs).2⟩
    _ = _ := by simp

theorem retained_one_le (n y z : ℕ) (hz : 1 ≤ z) : 1 ≤ retained (oddPrimes y) (gain n) z := by
  have h0 : ∅ ∈ family y z := mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), by simpa [modulus] using hz⟩
  change 1 ≤ ∑ s ∈ family y z, mass (gain n) s
  calc
    1 = mass (gain n) ∅ := by simp [mass]
    _ ≤ _ := single_le_sum (fun s h => prod_nonneg (fun p hp =>
      (gain_bounds n p (mem_oddPrimes.mp ((family_mem h).1 hp)).2.1).1)) h0

/-- The energy of the sum of centered local tests on an arbitrary initial segment. -/
theorem sieve_energy (n x y z : ℕ) :
    (∑ k ∈ range x, (∑ s ∈ family y z, test n s k)^2) ≤
      x * retained (oddPrimes y) (gain n) z + (z : ℝ)^6 := by
  let K := family y z
  have gram : (∑ k ∈ range x, (∑ s ∈ K, test n s k)^2) =
      ∑ s ∈ K, ∑ t ∈ K, ∑ k ∈ range x, test n s k * test n t k := by
    simp_rw [sq, sum_mul, mul_sum]
    rw [sum_comm]; apply sum_congr rfl; intro s hs; rw [sum_comm]
  have hpair (s : Finset ℕ) (hs : s ∈ K) (t : Finset ℕ) (ht : t ∈ K) :=
    pair_interval n x z s t (family_mem hs).2 (family_mem ht).2 (fun p h => by
      have hm : p ∈ oddPrimes y := (mem_union.mp h).elim (fun h => (family_mem hs).1 h) (fun h => (family_mem ht).1 h)
      exact ⟨(mem_oddPrimes.mp hm).1, (mem_oddPrimes.mp hm).2.1⟩)
  have row (s : Finset ℕ) (hs : s ∈ K) : (∑ t ∈ K,
      ((x : ℝ) * (if s = t then mass (gain n) s else 0) + (z : ℝ)^4)) =
      (x : ℝ)*mass (gain n) s + (K.card : ℝ)*(z : ℝ)^4 := by
    rw [sum_add_distrib, ← mul_sum]
    simp [hs, nsmul_eq_mul]
  change (∑ k ∈ range x, (∑ s ∈ K, test n s k)^2) ≤ _
  rw [gram]
  calc
    _ ≤ _ := sum_le_sum fun s hs => sum_le_sum fun t ht => hpair s hs t ht
    _ = _ := sum_congr rfl row
    _ = (x : ℝ) * retained (oddPrimes y) (gain n) z + (K.card : ℝ)^2 * (z : ℝ)^4 := by
      rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      congr 1
      ring
    _ ≤ _ := by
      have hc : (K.card : ℝ) ≤ z := by exact_mod_cast family_card y z
      apply add_le_add le_rfl
      calc _ ≤ (z : ℝ)^2 * (z : ℝ)^4 := by gcongr
           _ = _ := by ring

/-- Each central prime pair makes every retained test equal its surviving mass. -/
private theorem pair_survives {n k y z : ℕ} (hscale : 3*y < n) (hk : k ≤ n)
    (hc : n ≤ 3*k ∧ 3*k ≤ 2*n) (hkprime : k.Prime) (hlprime : (n-k).Prime)
    (s : Finset ℕ) (hs : s ∈ family y z) : test n s k = mass (gain n) s := by
  unfold test localTest mass
  apply prod_congr rfl
  intro p hp
  obtain ⟨hpp,h2,hpy⟩ := mem_oddPrimes.mp ((family_mem hs).1 hp)
  have hpd (l : ℕ) (hl : l.Prime) (hpl : p < l) : ¬p ∣ l := by
    intro hd
    rcases (Nat.dvd_prime hl).mp hd with h | h <;> omega
  have hbad : ¬(k % p = 0 ∨ k % p = n % p) := by
    rintro (h | h)
    · exact hpd _ hkprime (by omega) (Nat.dvd_of_mod_eq_zero h)
    · exact hpd _ hlprime (by omega) ((Nat.modEq_iff_dvd' hk).mp h)
  simp [atom, hbad]

/-- Weighted central mass times the squared denominator is controlled by the finite test energy. -/
theorem central_times_denominator (n y z : ℕ) (hscale : 3*y < n) :
    GoldbachFiniteSieve.centralMass n * (retained (oddPrimes y) (gain n) z)^2 ≤
      (Real.log (n : ℝ))^2 * (((n+1 : ℕ) : ℝ) * retained (oddPrimes y) (gain n) z + (z : ℝ)^6) := by
  let G := retained (oddPrimes y) (gain n) z
  apply le_trans _ (mul_le_mul_of_nonneg_left (sieve_energy n (n+1) y z) (sq_nonneg _))
  unfold GoldbachFiniteSieve.centralMass
  rw [sum_filter, sum_mul, mul_sum]
  apply sum_le_sum
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
  have hnn := mul_nonneg (sq_nonneg (Real.log (n : ℝ))) (sq_nonneg (∑ s ∈ family y z, test n s k))
  by_cases hc : n ≤ 3*k ∧ 3*k ≤ 2*n
  · simp only [hc]
    by_cases hkp : k.Prime
    · by_cases hlp : (n-k).Prime
      · have hG : (∑ s ∈ family y z, test n s k) = G := sum_congr rfl (pair_survives hscale hkn hc hkp hlp)
        simp only [hkp, hlp, ite_true, hG]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        rw [sq]
        have hlog (p : ℕ) (hp : p.Prime) (hle : p ≤ n) : Real.log p ≤ Real.log n :=
          Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hle)
        exact mul_le_mul (hlog _ hkp hkn) (hlog _ hlp (Nat.sub_le _ _))
          (Real.log_nonneg (by exact_mod_cast hlp.one_le)) (Real.log_nonneg (by exact_mod_cast hkp.one_le.trans hkn))
      · simpa [hlp] using hnn
    · simpa [hkp] using hnn
  · simpa [hc] using hnn

end GoldbachSieve

namespace GoldbachSieve

/-- Exact integer levels with room for the squarefree-modulus sum and the correlation error. -/
theorem levels (n : ℕ) (hn : 2^128 ≤ n) :
    ∃ y z : ℕ, 2 ≤ y ∧ 3*y < n ∧ y^8 ≤ z ∧ 1 ≤ z ∧ z^16 ≤ n ∧
      Real.log (n : ℝ) ≤ 256 * Real.log (y : ℝ) := by
  let e := Nat.log 2 n / 128
  let y := 2^e
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity : 0 < (2:ℕ)^128) hn
  have hlg : 128 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) hnpos.ne').mpr hn
  have he : 1 ≤ e := by dsimp [e]; omega
  have hy : 2 ≤ y := by
    change 2^1 ≤ (2:ℕ)^e
    exact Nat.pow_le_pow_right (by decide) he
  have hy128 : y^128 ≤ n := by
    change ((2:ℕ)^e)^128 ≤ n
    rw [← pow_mul]
    exact Nat.pow_le_of_le_log hnpos.ne' (Nat.div_mul_le_self _ _)
  have hy3 : y^3 ≤ n := (Nat.pow_le_pow_right (by omega : 0 < y) (by decide : 3 ≤ 128)).trans hy128
  have hy2 : 4 ≤ y^2 := by nlinarith only [Nat.mul_self_le_mul_self hy]
  have h3 : 3*y < n := by
    have := Nat.mul_le_mul_right y hy2
    rw [pow_succ] at hy3
    omega
  refine ⟨y, y^8, hy, h3, le_rfl, Nat.one_le_pow _ _ (by omega), ?_, ?_⟩
  · simpa only [← pow_mul] using hy128
  · have hnext : n ≤ 2^(256*e) := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le.trans
        (Nat.pow_le_pow_right (by decide) (show (Nat.log 2 n).succ ≤ 256*e by dsimp [e] at *; omega))
    have hscale : n ≤ y^256 := by simpa [y, ← pow_mul, Nat.mul_comm e 256] using hnext
    have hlog := Real.log_le_log (show (0 : ℝ) < n by exact_mod_cast hnpos)
      (show (n : ℝ) ≤ (y : ℝ)^256 by exact_mod_cast hscale)
    simpa [Real.log_pow] using hlog

end GoldbachSieve

namespace GoldbachSieve

/-- A uniform upper bound obtained by summing the centered squarefree tests. -/
theorem uniform_upper (n : ℕ) (hn : 2^128 ≤ n) :
    GoldbachFiniteSieve.centralMass n ≤ 1048608 * (n : ℝ) * singular n := by
  obtain ⟨y,z,hy,hscale,hyz,hz,hzn,hlog⟩ := levels n hn
  have hn0 : 0 < n := by omega
  let G := retained (oddPrimes y) (gain n) z
  let S := singular n
  let L := Real.log (n : ℝ)
  have hG : 1 ≤ G := retained_one_le n y z hz
  have hS : 1 ≤ S := singular_ge_one n
  have hG0 : 0 ≤ G := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hn0)
  have hden : (Real.log (y : ℝ))^2 ≤ 8 * S * G := denominator_lower n y z hn0.ne' hy hyz
  have hL : L^2 ≤ 524288 * S * G := by
    have hh := mul_self_le_mul_self hL0 hlog
    nlinarith only [hh, hden]
  have henergy : GoldbachFiniteSieve.centralMass n * G^2 ≤ L^2 * (((n+1 : ℕ) : ℝ) * G + (z : ℝ)^6) :=
    central_times_denominator n y z hscale
  have herr := GoldbachFiniteSieve.log_weighted_error n (z^2) hn0 (by simpa only [← pow_mul] using hzn)
  have hzR : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have herr' : L^2 * (z : ℝ)^6 ≤ 32 * (n : ℝ) := by
    apply le_trans _ herr
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    rw [Nat.cast_pow, ← pow_mul]
    change (z : ℝ)^6 ≤ 2 * (z : ℝ)^8
    linarith only [pow_le_pow_right₀ hzR (by decide : 6 ≤ 8), show (0 : ℝ) ≤ (z : ℝ)^8 by positivity]
  have hnR : ((n+1 : ℕ) : ℝ) ≤ 2*(n : ℝ) := by exact_mod_cast (by omega : n+1 ≤ 2*n)
  have hfirst : L^2 * (((n+1 : ℕ) : ℝ) * G) ≤ (1048576 * (n : ℝ) * S) * G^2 := calc
    _ ≤ (524288*S*G) * ((2*(n:ℝ))*G) :=
      mul_le_mul hL (mul_le_mul_of_nonneg_right hnR hG0) (mul_nonneg (Nat.cast_nonneg _) hG0) (by positivity)
    _ = _ := by ring
  have hG2 : 1 ≤ G^2 := one_le_pow₀ hG
  have hsecond : L^2 * (z : ℝ)^6 ≤ (32*(n : ℝ)*S) * G^2 := calc
    _ ≤ 32 * (n : ℝ) := herr'
    _ ≤ _ := by calc
      32*(n : ℝ) = (32*(n:ℝ)*1) * 1 := by ring
      _ ≤ _ := by gcongr
  have hsum : GoldbachFiniteSieve.centralMass n * G^2 ≤ (1048608 * (n : ℝ) * S) * G^2 := by
    rw [mul_add] at henergy
    linarith only [henergy, hfirst, hsecond]
  exact le_of_mul_le_mul_right hsum (sq_pos_of_pos (by linarith only [hG]))

end GoldbachSieve

namespace GoldbachSquareMean

private def oddFactors (n : ℕ) : Finset ℕ := n.primeFactors.filter (2 < ·)

private noncomputable def singular (n : ℕ) : ℝ :=
  ∏ p ∈ oddFactors n, (1 + 1 / ((p : ℝ) - 2))

private noncomputable def increment (p : ℕ) : ℝ := (1 + 1 / ((p : ℝ) - 2))^2 - 1

private theorem increment_nonneg {p : ℕ} (hp : 3 ≤ p) : 0 ≤ increment p := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h : 0 ≤ 1 / ((p : ℝ) - 2) := div_nonneg zero_le_one (by linarith)
  unfold increment
  nlinarith [sq_nonneg (1 / ((p : ℝ) - 2))]

/-- A telescoping rational product bounds the averaged Euler factors at integers from 5 onwards. -/
private theorem tail_product (N : ℕ) (hN : 4 ≤ N) :
    ∏ p ∈ Icc 5 N, (1 + increment p / (p : ℝ)) ≤ 2 * ((N : ℝ) - 2) / N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hI : Icc 5 (k + 1) = insert (k + 1) (Icc 5 k) := by
      ext j
      simp only [mem_Icc, mem_insert]
      omega
    rw [hI, prod_insert (by simp)]
    have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
    have hinc := increment_nonneg (p := k + 1) (by omega)
    calc
      _ ≤ (1 + increment (k+1) / ((k+1 : ℕ) : ℝ)) * (2 * ((k : ℝ) - 2) / k) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ _ := by
        simp only [increment, Nat.cast_succ]
        rw [show (k : ℝ) + 1 - 2 = (k : ℝ) - 1 by ring]
        have h0 : (k : ℝ) ≠ 0 := by linarith
        have h1 : (k : ℝ) - 1 ≠ 0 := by linarith
        have h2 : (k : ℝ) + 1 ≠ 0 := by linarith
        calc
          _ = 2 * ((k : ℝ) - 1) / (k + 1) - 2 / ((k + 1) * (k - 1 : ℝ)^2) := by
            field_simp [h0, h1, h2]
            ring
          _ ≤ _ := sub_le_self _ (by positivity)

/-- Every odd prime factor of a positive integer at most `M` is 3 or lies in this tail. -/
private def candidates (M : ℕ) : Finset ℕ := insert 3 (Icc 5 (M+4))

private theorem candidates_ge_three {M p : ℕ} (hp : p ∈ candidates M) : 3 ≤ p := by
  rcases mem_insert.mp hp with rfl | hp
  · decide
  · have := (mem_Icc.mp hp).1
    omega

private theorem candidates_product (M : ℕ) :
    ∏ p ∈ candidates M, (1 + increment p / (p : ℝ)) ≤ 4 := by
  have htail := tail_product (M+4) (by omega)
  have hpos : (0 : ℝ) < (M+4 : ℕ) := by positivity
  have hbound : 2 * (((M+4 : ℕ) : ℝ) - 2) / (M+4 : ℕ) ≤ 2 :=
    (div_le_iff₀ hpos).mpr (by linarith)
  rw [candidates, prod_insert (by simp)]
  have hthree : 1 + increment 3 / (3 : ℝ) = 2 := by norm_num [increment]
  change (1 + increment 3 / (3 : ℝ)) * _ ≤ 4
  rw [hthree]
  linarith [htail.trans hbound]

private theorem oddFactors_subset {M n : ℕ} (hn : n ≤ M) : oddFactors n ⊆ candidates M := by
  intro p hp
  obtain ⟨hdiv, hodd⟩ := mem_filter.mp hp
  have hpN := Nat.le_of_mem_primeFactors hdiv
  have hfour : p ≠ 4 := by
    rintro rfl
    exact (by decide : ¬ Nat.Prime 4) (Nat.prime_of_mem_primeFactors hdiv)
  by_cases h : p = 3
  · exact mem_insert.mpr (Or.inl h)
  · exact mem_insert.mpr (Or.inr (mem_Icc.mpr ⟨by omega, by omega⟩))

private def divisorProduct (t : Finset ℕ) : ℕ := ∏ p ∈ t, p

private noncomputable def subsetWeight (t : Finset ℕ) : ℝ := ∏ p ∈ t, increment p

/-- A subset of the odd prime factors contributes only at multiples of its product. -/
private theorem square_le_divisor_sum {n M : ℕ} (hn : n ≤ M) :
    singular n ^ 2 ≤ ∑ t ∈ (candidates M).powerset,
      if divisorProduct t ∣ n then subsetWeight t else 0 := by
  classical
  let A := oddFactors n
  have hdiv (t : Finset ℕ) (ht : t ∈ A.powerset) : divisorProduct t ∣ n := by
    have hsub : t ⊆ n.primeFactors :=
      (mem_powerset.mp ht).trans (filter_subset _ _)
    exact (Finset.prod_dvd_prod_of_subset t n.primeFactors id hsub).trans n.prod_primeFactors_dvd
  calc
    singular n ^ 2 = ∏ p ∈ A, (1 + increment p) := by
      unfold singular
      rw [← Finset.prod_pow]
      apply prod_congr rfl
      intro p _
      dsimp [increment]
      ring
    _ = ∑ t ∈ A.powerset, subsetWeight t := Finset.prod_one_add A
    _ = ∑ t ∈ A.powerset, if divisorProduct t ∣ n then subsetWeight t else 0 := by
      exact sum_congr rfl fun t ht ↦ (ite_eq_left (hdiv t ht)).symm
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact fun t ht ↦ mem_powerset.mpr ((mem_powerset.mp ht).trans (oddFactors_subset hn))
      · intro t ht _
        split_ifs
        · exact prod_nonneg fun p hp ↦ increment_nonneg (candidates_ge_three (mem_powerset.mp ht hp))
        · exact le_rfl

private theorem multiples_count (M d : ℕ) : ((Icc 1 M).filter (fun n ↦ d ∣ n)).card = M / d := by
  have sets : (Icc 1 M).filter (fun n ↦ d ∣ n) = (range M.succ).filter (fun n ↦ n ≠ 0 ∧ d ∣ n) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_range]
    omega
  rw [sets, Nat.card_multiples']

/-- Average the expanded factors using the exact count `M / d` of positive multiples. -/
private theorem prefix_square (M : ℕ) : (∑ n ∈ Icc 1 M, singular n ^ 2) ≤ 4*(M : ℝ) := by
  classical
  let P := candidates M
  calc
    (∑ n ∈ Icc 1 M, singular n ^ 2) ≤ ∑ n ∈ Icc 1 M, ∑ t ∈ P.powerset,
        if divisorProduct t ∣ n then subsetWeight t else 0 :=
      sum_le_sum fun n hn ↦ square_le_divisor_sum (mem_Icc.mp hn).2
    _ = ∑ t ∈ P.powerset, ∑ n ∈ Icc 1 M,
        if divisorProduct t ∣ n then subsetWeight t else 0 := Finset.sum_comm
    _ ≤ ∑ t ∈ P.powerset, (M : ℝ) * (∏ p ∈ t, increment p / (p : ℝ)) := by
      apply sum_le_sum
      intro t ht
      have hw : 0 ≤ subsetWeight t := prod_nonneg fun p hp ↦
        increment_nonneg (candidates_ge_three (mem_powerset.mp ht hp))
      rw [← sum_filter, sum_const, multiples_count, nsmul_eq_mul]
      calc
        _ ≤ ((M : ℝ) / (divisorProduct t : ℝ)) * subsetWeight t :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le hw
        _ = _ := by
          rw [Finset.prod_div_distrib]
          simp only [divisorProduct, Nat.cast_prod, subsetWeight]
          ring
    _ = (M : ℝ) * ∏ p ∈ P, (1 + increment p / (p : ℝ)) := by
      rw [← Finset.mul_sum, Finset.prod_one_add]
    _ ≤ 4 * (M : ℝ) := by
      rw [mul_comm (4 : ℝ)]
      exact mul_le_mul_of_nonneg_left (candidates_product M) (Nat.cast_nonneg _)

/-- Doubling changes only the prime factor 2, which is excluded from the local factors. -/
private theorem singular_double (m : ℕ) : singular (2*m) = singular m := by
  by_cases hm : m = 0
  · simp [hm]
  · have hfac : oddFactors (2*m) = oddFactors m := by
      ext p
      by_cases hp : p = 2
      · subst p
        simp [oddFactors]
      · simp [oddFactors, Nat.primeFactors_mul (by decide : 2 ≠ 0) hm, Nat.prime_two.primeFactors, hp]
    unfold singular
    rw [hfac]

theorem factor_square :
    let S := fun n : ℕ => ∏ p ∈ n.primeFactors.filter (fun p => 2<p), (1+1/((p:ℝ)-2)); let I := fun x : ℕ => (Finset.Icc x (2*x)).filter (fun n => Even n); ∃ K : ℝ, 0<K ∧ ∀ x : ℕ, 1≤x → (∑ n ∈ I x, (S n)^2) ≤ K*(x:ℝ) := by
  change ∃ K : ℝ, 0 < K ∧ ∀ x : ℕ, 1 ≤ x →
    (∑ n ∈ (Icc x (2*x)).filter Even, singular n ^ 2) ≤ K*(x : ℝ)
  refine ⟨4, by norm_num, fun x hx ↦ ?_⟩
  let half (n : ℕ) := n / 2
  have double_half {n : ℕ} (hn : n ∈ (Icc x (2*x)).filter Even) : 2 * half n = n := by
    obtain ⟨a, ha⟩ := (mem_filter.mp hn).2
    dsimp [half]
    omega
  refine le_trans ?_ (prefix_square x)
  apply Finset.sum_le_sum_of_injOn half
  · intro a ha b hb he
    rw [← double_half ha, he, double_half hb]
  · intro m hm
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
    have hinterval := mem_Icc.mp (mem_filter.mp hn).1
    have hdouble := double_half hn
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro n hn
    exact le_of_eq (congrArg (fun y : ℝ ↦ y^2)
      ((congrArg singular (double_half hn).symm).trans (singular_double _)))
  · exact fun m _ _ ↦ sq_nonneg _

end GoldbachSquareMean

namespace GoldbachSieve

private theorem weighted_nonneg (n : ℕ) : 0 ≤ GoldbachFiniteSieve.centralMass n := by
  have hw (p : ℕ) : 0 ≤ (if p.Prime then Real.log (p : ℝ) else 0) := by
    by_cases hp : p.Prime
    · simpa [hp] using Real.log_nonneg (show (1 : ℝ) ≤ p by exact_mod_cast hp.one_le)
    · simp [hp]
  exact sum_nonneg fun p _ => mul_nonneg (hw p) (hw _)

end GoldbachSieve

namespace PEqualNP.Outside

/-- Cubic second moment obtained from a uniform squarefree sieve and the mean square of its local factor. -/
theorem L_goldbach_central_second_moment :
    let w := fun p : ℕ => if p.Prime then Real.log (p : ℝ) else 0; let C := fun n : ℕ => ∑ p ∈ (Finset.range (n+1)).filter (fun p => n≤3*p ∧ 3*p≤2*n), w p*w (n-p); let I := fun x : ℕ => (Finset.Icc x (2*x)).filter (fun n => Even n); ∃ K : ℝ, 0<K ∧ ∃ X : ℕ, ∀ x≥X, (∑ n ∈ I x, (C n)^2) ≤ K*(x:ℝ)^3 := by
  let I := fun x : ℕ => (Icc x (2*x)).filter (fun n => Even n)
  let A : ℝ := 1048608
  have hA : 0 < A := by norm_num [A]
  change ∃ B : ℝ, 0 < B ∧ ∃ X : ℕ, ∀ x ≥ X,
    (∑ n ∈ I x, (GoldbachFiniteSieve.centralMass n)^2) ≤ B*(x : ℝ)^3
  have factor : ∃ K : ℝ, 0 < K ∧ ∀ x : ℕ, 1 ≤ x →
      (∑ n ∈ I x, (GoldbachSieve.singular n)^2) ≤ K * (x : ℝ) := GoldbachSquareMean.factor_square
  obtain ⟨K,hK,hfactor⟩ := factor
  refine ⟨4*A^2*K, by positivity, 2^128, fun x hx => ?_⟩
  have point (n : ℕ) (hn : n ∈ I x) : (GoldbachFiniteSieve.centralMass n)^2 ≤
      (2*A*(x : ℝ))^2 * (GoldbachSieve.singular n)^2 := by
    obtain ⟨hlo,hhi⟩ := mem_Icc.mp (mem_filter.mp hn).1
    have hnr : (n : ℝ) ≤ 2*x := by exact_mod_cast hhi
    have hs : 0 ≤ GoldbachSieve.singular n := le_trans (by norm_num) (GoldbachSieve.singular_ge_one n)
    have bound : GoldbachFiniteSieve.centralMass n ≤ (2*A*(x : ℝ))*GoldbachSieve.singular n := by
      apply (GoldbachSieve.uniform_upper n (hx.trans hlo)).trans
      apply mul_le_mul_of_nonneg_right _ hs
      change A*(n : ℝ) ≤ 2*A*x
      linarith only [mul_le_mul_of_nonneg_left hnr hA.le]
    simpa only [sq, mul_mul_mul_comm] using mul_self_le_mul_self (GoldbachSieve.weighted_nonneg n) bound
  calc
    _ ≤ ∑ n ∈ I x, (2*A*(x : ℝ))^2 * (GoldbachSieve.singular n)^2 := sum_le_sum point
    _ = (2*A*(x : ℝ))^2 * ∑ n ∈ I x, (GoldbachSieve.singular n)^2 := (mul_sum ..).symm
    _ ≤ (2*A*(x : ℝ))^2 * (K*x) := mul_le_mul_of_nonneg_left (hfactor x (by omega)) (sq_nonneg _)
    _ = _ := by ring

end PEqualNP.Outside
