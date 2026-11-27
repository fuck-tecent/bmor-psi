import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

private lemma cert_filter_eq (p : ℕ) (hp : p.Prime) :
    (Finset.range p).filter (fun b => Nat.Coprime b p) = (Finset.range p).erase 0 := by
  ext b
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
  constructor
  · rintro ⟨hb, hc⟩
    refine ⟨?_, hb⟩
    rintro rfl
    have := hp.one_lt
    simp [Nat.coprime_zero_left] at hc
    omega
  · rintro ⟨hb0, hb⟩
    refine ⟨hb, ?_⟩
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    exact hb0 (Nat.eq_zero_of_dvd_of_lt hd hb)

private lemma cert_prime_sum (p : ℕ) (hp : p.Prime) (a : ℕ) (h : Nat.Coprime a p) :
    (∑ b ∈ (Finset.range p).filter (fun b => Nat.Coprime b p),
      Complex.exp (((2*Real.pi*(a:ℝ)*b/p:ℝ):ℂ)*Complex.I)) / ((p - 1 : ℕ) : ℂ)
      = (-1:ℂ) / ((p - 1 : ℕ) : ℂ) := by
  have hprim := Complex.isPrimitiveRoot_exp_of_coprime a p hp.ne_zero h
  set ζ := Complex.exp (2 * Real.pi * Complex.I * (a / (p:ℕ))) with hζ
  have hsum : ∀ b : ℕ, Complex.exp (((2*Real.pi*(a:ℝ)*b/p:ℝ):ℂ)*Complex.I) = ζ ^ b := by
    intro b
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hsum]
  rw [cert_filter_eq p hp, Finset.sum_erase_eq_sub (Finset.mem_range.mpr hp.pos)]
  rw [hprim.geom_sum_eq_zero hp.one_lt]
  simp

theorem PEqualNP.Outside.L_goldbach_cert_131 :
    ∀ a:ℕ, Nat.Coprime a 131 → (∑ b ∈ (Finset.range 131).filter (fun b => Nat.Coprime b 131), Complex.exp (((2*Real.pi*(a:ℝ)*b/131:ℝ):ℂ)*Complex.I))/(130:ℂ)=(-1:ℂ)/130 := by
  intro a h
  have := cert_prime_sum 131 (by norm_num) a h
  simpa using this
