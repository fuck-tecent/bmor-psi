import Mathlib

-- child 1 zh: 任意整数频率与任意元数组的偶数阶傅里叶矩，等于两组频率和相等的有序元组对数。
-- child 1 en: Identify every even Fourier moment of any finite integer frequency family with the exact ordered collision count.
-- child 2 zh: 用整系数多项式纤维的次数上界控制任意子集上的指数和二次矩。
-- child 2 en: Bound the second moment of a nonconstant integer polynomial phase by the polynomial degree times the support size.
-- child 3 zh: 控制六次矩超过支撑大小平方乘二次矩的正部，聚焦大谱值。
-- child 3 en: Bound the positive excess of the sixth-power integrand above the support size squared times the second-power integrand.

set_option maxHeartbeats 600000 in
theorem Conjectures.Cuts.Cutd5bb5c97f936994868304587
   (h₁ : by
  classical
  let S := fun (f : ℕ → ℤ) (A : Finset ℕ) (t : ℝ) => ∑ j : (↥A), Complex.exp (2*(Real.pi:ℂ)*Complex.I*(f j:ℂ)*(t:ℂ))
  exact ∀ (f : ℕ → ℤ) (A : Finset ℕ) (r : ℕ),
    let w := fun u : Fin r → (↥A) => ∑ j : Fin r, f (u j)
    let U : Finset (Fin r → (↥A)) := Finset.univ
    (∫ t in (0:ℝ)..1, ‖S f A t‖^(2*r)) = (((U.product U).filter (fun z => w z.1 = w z.2)).card : ℝ))
   (h₂ : by
  classical
  let S := fun (P : Polynomial ℤ) (A : Finset ℕ) (t : ℝ) => ∑ j : (↥A), Complex.exp (2*(Real.pi:ℂ)*Complex.I*((P.eval (j.val:ℤ):ℤ):ℂ)*(t:ℂ))
  exact ∀ (P : Polynomial ℤ), 1 ≤ P.natDegree → ∀ A : Finset ℕ,
   (∫ t in (0:ℝ)..1, ‖S P A t‖^2) ≤ (P.natDegree:ℝ) * A.card)
   (h₃ : by
  classical
  let S := fun (P : Polynomial ℤ) (A : Finset ℕ) (t : ℝ) => ∑ j : (↥A), Complex.exp (2*(Real.pi:ℂ)*Complex.I*((P.eval (j.val:ℤ):ℤ):ℂ)*(t:ℂ))
  exact ∀ P : Polynomial ℤ, 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
    (∫ t in (0:ℝ)..1, max 0 (‖S P A t‖^6 - (A.card:ℝ)^2 * ‖S P A t‖^2)) ≤ C*(M:ℝ)^ε*(A.card:ℝ)^3)
   : (by
  classical
  exact ∀ P : Polynomial ℤ, 3 ≤ P.natDegree → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
    let weight := fun x : Fin 3 → (↥A) => ∑ j : Fin 3, P.eval ((x j : ℕ) : ℤ)
    (((Finset.univ : Finset ((Fin 3 → (↥A)) × (Fin 3 → (↥A)))).filter (fun z => weight z.1 = weight z.2)).card : ℝ) ≤ C*(M : ℝ)^ε*(A.card : ℝ)^3) := by
  classical
  intro P d ε hε
  obtain ⟨C,hC,hT⟩ := h₃ P d ε hε
  refine ⟨C+P.natDegree, by positivity, fun M hM A hA => ?_⟩
  let k : ℝ := A.card
  let s := fun (t:ℝ) => ∑ j : (↥A), Complex.exp (2*(Real.pi:ℂ)*Complex.I*((P.eval (j.val:ℤ):ℤ):ℂ)*(t:ℂ))
  let T := fun t => max 0 (‖s t‖^6 - k^2*‖s t‖^2)
  have hs : Continuous s := by dsimp [s]; fun_prop
  have ht : Continuous T := by dsimp only [T]; fun_prop
  have hL : Continuous (fun t => ‖s t‖^2) := by fun_prop
  have hS : Continuous (fun t => ‖s t‖^6) := by fun_prop
  have hL' : Continuous (fun t => k^2*‖s t‖^2) := by fun_prop
  have hI : (∫ t in (0:ℝ)..1, ‖s t‖^6) ≤ (∫ t in (0:ℝ)..1, T t) + k^2*(∫ t in (0:ℝ)..1, ‖s t‖^2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (ht.intervalIntegrable ..) (hL'.intervalIntegrable ..)]
    apply intervalIntegral.integral_mono (by norm_num) (hS.intervalIntegrable ..) ((ht.add hL').intervalIntegrable ..)
    intro t
    have := le_max_right (0:ℝ) (‖s t‖^6-k^2*‖s t‖^2)
    dsimp [T]; linarith
  have horth := h₁ (fun n => P.eval (n:ℤ)) A 3
  change (∫ t in (0:ℝ)..1, ‖s t‖^6) = _ at horth
  have hall : (Finset.univ : Finset (Fin 3 → (↥A))).product Finset.univ = (Finset.univ : Finset ((Fin 3 → (↥A)) × (Fin 3 → (↥A)))) := by ext z; simp
  rw [hall] at horth
  change _ ≤ (C+P.natDegree)*(M:ℝ)^ε*k^3
  rw [← horth]
  have hsmall : (∫ t in (0:ℝ)..1, ‖s t‖^2) ≤ (P.natDegree:ℝ)*k := h₂ P (by omega) A
  have hlarge : (∫ t in (0:ℝ)..1, T t) ≤ C*(M:ℝ)^ε*k^3 := hT M hM A hA
  have hge : 1 ≤ (M:ℝ)^ε := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ M by omega)) hε.le
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hgain : (P.natDegree:ℝ)*k^3 ≤ (P.natDegree:ℝ) * k^3 * (M:ℝ)^ε := le_mul_of_one_le_right (by positivity) hge
  calc
    _ ≤ _ := hI
    _ ≤ C*(M:ℝ)^ε*k^3 + k^2*((P.natDegree:ℝ)*k) := add_le_add hlarge (mul_le_mul_of_nonneg_left hsmall (sq_nonneg _))
    _ ≤ _ := by nlinarith only [hgain]
