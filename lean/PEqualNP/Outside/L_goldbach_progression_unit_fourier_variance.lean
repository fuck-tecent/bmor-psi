import Mathlib

/-
SPDX-License-Identifier: Apache-2.0
Finite Fourier orthogonality and the Parseval proof are adapted from
houmy555809's PR #208 (dcfadb86851309af7a32ea86bafabb81491bb206):
https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/208
The final theorem specializes that identity to real progression errors.
-/
open scoped BigOperators

private lemma phase_add (s t : ℝ) :
    Complex.exp (((2*Real.pi*(s+t):ℝ):ℂ)*Complex.I)
      = Complex.exp (((2*Real.pi*s:ℝ):ℂ)*Complex.I) * Complex.exp (((2*Real.pi*t:ℝ):ℂ)*Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma phase_norm (x : ℝ) :
    ‖Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (((2*Real.pi*x:ℝ):ℂ)*Complex.I).re = 0 := by simp
  rw [h, Real.exp_zero]

private lemma phase_star (x : ℝ) :
    star (Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I))
      = Complex.exp (((2*Real.pi*(-x):ℝ):ℂ)*Complex.I) := by
  have h1 : (Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I))⁻¹
      = star (Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)) := Complex.inv_eq_conj (phase_norm x)
  rw [← h1, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- E(a) * conj(E(b)) = conj(E(b-a))。 -/
private lemma phase_star_mul (a b : ℝ) :
    Complex.exp (((2*Real.pi*a:ℝ):ℂ)*Complex.I)
      * star (Complex.exp (((2*Real.pi*b:ℝ):ℂ)*Complex.I))
      = star (Complex.exp (((2*Real.pi*(b-a):ℝ):ℂ)*Complex.I)) := by
  rw [phase_star, ← phase_add, phase_star]
  congr 1
  push_cast
  ring

private lemma phase_pow (x : ℝ) (j : ℕ) :
    Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)^j
      = Complex.exp (((2*Real.pi*((j:ℝ)*x):ℝ):ℂ)*Complex.I) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- 单位根正交性（ℕ 版）：Σ_{j<M} E(jk/M) = if M ∣ k then M else 0。 -/
private lemma char_orth (M k : ℕ) (hM : 0 < M) :
    Finset.sum (Finset.range M) (fun j : ℕ =>
      Complex.exp (((2*Real.pi*((j:ℝ)*(k:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))
      = if M ∣ k then (M:ℂ) else 0 := by
  have hMne : M ≠ 0 := by omega
  set ζ : ℂ := Complex.exp (2 * ((Real.pi:ℝ):ℂ) * Complex.I / (M:ℂ)) with hζ
  have hprim : IsPrimitiveRoot ζ M := Complex.isPrimitiveRoot_exp M hMne
  have hterm : ∀ j : ℕ, Complex.exp (((2*Real.pi*((j:ℝ)*(k:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I) = ζ^(j*k) := by
    intro j
    have harg : (((2*Real.pi*((j:ℝ)*(k:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)
        = (j*k:ℕ) * (2 * ((Real.pi:ℝ):ℂ) * Complex.I / (M:ℂ)) := by
      push_cast
      ring
    rw [harg, Complex.exp_nat_mul]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  by_cases hdvd : M ∣ k
  · obtain ⟨t, rfl⟩ := hdvd
    have hone : ∀ j : ℕ, ζ^(j*(M*t)) = 1 := by
      intro j
      rw [show j*(M*t) = M*(j*t) by ring, pow_mul, hprim.pow_eq_one, one_pow]
    rw [Finset.sum_congr rfl (fun j _ => hone j)]
    simp
  · have hζk_ne : ζ^k ≠ 1 := fun h => hdvd ((hprim.pow_eq_one_iff_dvd k).mp h)
    have hpow : (ζ^k)^M = 1 := by
      rw [← pow_mul, Nat.mul_comm k M, pow_mul, hprim.pow_eq_one, one_pow]
    have hsum : Finset.sum (Finset.range M) (fun j : ℕ => ζ^(j*k)) = 0 := by
      have hstep : ∀ j : ℕ, ζ^(j*k) = (ζ^k)^j := by
        intro j
        rw [show (ζ^k)^j = ζ^(k*j) by rw [pow_mul], Nat.mul_comm]
      rw [Finset.sum_congr rfl (fun j _ => hstep j), geom_sum_eq hζk_ne M, hpow]
      simp
    rw [hsum, if_neg hdvd]

/-- 两指标正交性：Σ_{j<M} E(jl/M)·conj(E(jk/M)) = if l=k then M else 0。 -/
private lemma pair_orth (M l k : ℕ) (hM : 0 < M) (hl : l < M) (hk : k < M) :
    Finset.sum (Finset.range M) (fun j : ℕ =>
      Complex.exp (((2*Real.pi*((j:ℝ)*(l:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)
        * star (Complex.exp (((2*Real.pi*((j:ℝ)*(k:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
      = if l = k then (M:ℂ) else 0 := by
  rcases le_total k l with hle | hle
  · -- l ≥ k：项 = E(j(l-k)/M)
    have hstep : ∀ j : ℕ,
        Complex.exp (((2*Real.pi*((j:ℝ)*(l:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)
          * star (Complex.exp (((2*Real.pi*((j:ℝ)*(k:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))
        = Complex.exp (((2*Real.pi*((j:ℝ)*((l-k:ℕ):ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I) := by
      intro j
      rw [phase_star_mul, phase_star]
      congr 1
      have hsub : ((l-k:ℕ):ℝ) = (l:ℝ) - (k:ℝ) := by
        push_cast [Nat.cast_sub hle]
        ring
      rw [hsub]
      push_cast
      field_simp
      ring
    rw [Finset.sum_congr rfl (fun j _ => hstep j), char_orth M (l-k) hM]
    by_cases hlk : l = k
    · subst hlk; simp
    · have hne : ¬ M ∣ l - k := by
        intro h
        have hpos : 0 < l - k := Nat.sub_pos_of_lt (lt_of_le_of_ne hle (Ne.symm hlk))
        have := Nat.le_of_dvd hpos h
        omega
      rw [if_neg hne, if_neg hlk]
  · -- l ≤ k：项 = conj(E(j(k-l)/M))
    have hstep : ∀ j : ℕ,
        Complex.exp (((2*Real.pi*((j:ℝ)*(l:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)
          * star (Complex.exp (((2*Real.pi*((j:ℝ)*(k:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))
        = star (Complex.exp (((2*Real.pi*((j:ℝ)*((k-l:ℕ):ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)) := by
      intro j
      rw [phase_star_mul]
      congr 1
      have hsub : ((k-l:ℕ):ℝ) = (k:ℝ) - (l:ℝ) := by
        push_cast [Nat.cast_sub hle]
        ring
      rw [hsub]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl (fun j _ => hstep j)]
    have hsum_eq : Finset.sum (Finset.range M) (fun j : ℕ =>
        star (Complex.exp (((2*Real.pi*((j:ℝ)*((k-l:ℕ):ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
        = star (Finset.sum (Finset.range M) (fun j : ℕ =>
          Complex.exp (((2*Real.pi*((j:ℝ)*((k-l:ℕ):ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))) := by simp
    rw [hsum_eq, char_orth M (k-l) hM]
    by_cases hlk : l = k
    · subst hlk; simp
    · have hne : ¬ M ∣ k - l := by
        intro h
        have hpos : 0 < k - l := Nat.sub_pos_of_lt (lt_of_le_of_ne hle hlk)
        have := Nat.le_of_dvd hpos h
        omega
      simp [hne, hlk]


private theorem discrete_parseval :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let c := fun (M j k : ℕ) => E ((j:ℝ)*(k:ℝ)/(M:ℝ)); let F := fun (M : ℕ) (f : ℕ → ℂ) (j : ℕ) => Finset.sum (Finset.range M) (fun k => f k*c M j k); ∀ M f, Finset.sum (Finset.range M) (fun j => ‖F M f j‖^2) = (M:ℝ)*Finset.sum (Finset.range M) (fun k => ‖f k‖^2) := by
  intro E c F M f
  simp only [E, c, F]
  by_cases hM0 : M = 0
  · subst hM0
    simp
  have hM : 0 < M := Nat.pos_of_ne_zero hM0
  -- 缩写：A j k = exp(2πi·j·k/M)
  have hcompl : Finset.sum (Finset.range M) (fun j : ℕ =>
      (Finset.sum (Finset.range M) (fun u : ℕ =>
        f u * Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
        * star (Finset.sum (Finset.range M) (fun v : ℕ =>
          f v * Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))))
      = (M:ℂ) * Finset.sum (Finset.range M) (fun k : ℕ => f k * star (f k)) := by
    -- star 推进内层和
    have hstar_sum : ∀ j : ℕ,
        star (Finset.sum (Finset.range M) (fun v : ℕ =>
          f v * Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
        = Finset.sum (Finset.range M) (fun v : ℕ =>
          star (Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)) * star (f v)) := by
      intro j
      have hs : star (Finset.sum (Finset.range M) (fun v : ℕ =>
          f v * Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
          = Finset.sum (Finset.range M) (fun v : ℕ =>
            star (f v * Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))) := by
        have hmap := map_sum (starRingEnd ℂ)
          (fun v : ℕ => f v * Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))
          (Finset.range M)
        simpa using hmap
      rw [hs]
      apply Finset.sum_congr rfl
      intro v _
      rw [star_mul]
    have hstep1 : Finset.sum (Finset.range M) (fun j : ℕ =>
        (Finset.sum (Finset.range M) (fun u : ℕ =>
          f u * Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
          * star (Finset.sum (Finset.range M) (fun v : ℕ =>
            f v * Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))))
        = Finset.sum (Finset.range M) (fun j : ℕ =>
          (Finset.sum (Finset.range M) (fun u : ℕ =>
            f u * Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
            * (Finset.sum (Finset.range M) (fun v : ℕ =>
              star (Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)) * star (f v)))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hstar_sum j]
    rw [hstep1]
    -- 展开成三重和
    have hexp : Finset.sum (Finset.range M) (fun j : ℕ =>
        (Finset.sum (Finset.range M) (fun u : ℕ =>
          f u * Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
          * (Finset.sum (Finset.range M) (fun v : ℕ =>
            star (Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)) * star (f v))))
        = Finset.sum (Finset.range M) (fun u : ℕ =>
          Finset.sum (Finset.range M) (fun v : ℕ =>
            f u * star (f v) * Finset.sum (Finset.range M) (fun j : ℕ =>
              Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)
                * star (Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))))) := by
      have h1 : ∀ j : ℕ,
          (Finset.sum (Finset.range M) (fun u : ℕ =>
            f u * Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
            * (Finset.sum (Finset.range M) (fun v : ℕ =>
              star (Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)) * star (f v)))
          = Finset.sum (Finset.range M) (fun u : ℕ =>
            Finset.sum (Finset.range M) (fun v : ℕ =>
              f u * star (f v) *
                (Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)
                  * star (Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))))) := by
        intro j
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      rw [Finset.sum_congr rfl (fun j _ => h1 j)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
    rw [hexp]
    -- 内层正交和 = if u = v then M else 0
    have hinner : ∀ u ∈ Finset.range M, ∀ v ∈ Finset.range M,
        Finset.sum (Finset.range M) (fun j : ℕ =>
          Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)
            * star (Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
        = if u = v then (M:ℂ) else 0 := by
      intro u hu v hv
      exact pair_orth M u v hM (Finset.mem_range.mp hu) (Finset.mem_range.mp hv)
    rw [Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun v hv => by
      rw [hinner u hu v hv]))]
    -- 对角化
    have hdiag : Finset.sum (Finset.range M) (fun u : ℕ =>
        Finset.sum (Finset.range M) (fun v : ℕ =>
          f u * star (f v) * (if u = v then (M:ℂ) else 0)))
        = Finset.sum (Finset.range M) (fun u : ℕ => f u * star (f u) * (M:ℂ)) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_eq_single u]
      · rw [if_pos rfl]
      · intro v _ hvu
        rw [if_neg (Ne.symm hvu), mul_zero]
      · intro hnot
        exact absurd hu hnot
    rw [hdiag]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  -- 把两侧都写成实数的提升
  have hleft : Finset.sum (Finset.range M) (fun j : ℕ =>
      (Finset.sum (Finset.range M) (fun u : ℕ =>
        f u * Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I)))
        * star (Finset.sum (Finset.range M) (fun v : ℕ =>
          f v * Complex.exp (((2*Real.pi*((j:ℝ)*(v:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))))
      = ((Finset.sum (Finset.range M) (fun j : ℕ =>
          ‖Finset.sum (Finset.range M) (fun u : ℕ =>
            f u * Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))‖^2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← starRingEnd_apply]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hright : (M:ℂ) * Finset.sum (Finset.range M) (fun k : ℕ => f k * star (f k))
      = (((M:ℝ) * Finset.sum (Finset.range M) (fun k : ℕ => ‖f k‖^2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [← starRingEnd_apply]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcast : ((Finset.sum (Finset.range M) (fun j : ℕ =>
      ‖Finset.sum (Finset.range M) (fun u : ℕ =>
        f u * Complex.exp (((2*Real.pi*((j:ℝ)*(u:ℝ)/(M:ℝ)):ℝ):ℂ)*Complex.I))‖^2) : ℝ) : ℂ)
      = (((M:ℝ) * Finset.sum (Finset.range M) (fun k : ℕ => ‖f k‖^2) : ℝ) : ℂ) := by
    rw [← hleft, ← hright]
    exact hcompl
  exact Complex.ofReal_inj.mp hcast

theorem PEqualNP.Outside.L_goldbach_progression_unit_fourier_variance :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let Λ := ArithmeticFunction.vonMangoldt; ∀ (q n : ℕ), 0 < q → let D := fun r : ℕ => if Nat.Coprime r q then (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = r), Λ k) - (n:ℝ)/Nat.totient q else 0; (∑ a ∈ Finset.range q, ‖∑ r ∈ Finset.range q, (D r:ℂ)*E ((a:ℝ)*r/q)‖^2) = (q:ℝ)*(∑ r ∈ Finset.range q, (D r)^2) := by
  intro E Λ q n _hq D
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
    (discrete_parseval q (fun r => (D r : ℂ)))
