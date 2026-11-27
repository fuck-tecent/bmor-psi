import Mathlib

/- The dependent-sum reindexing strategy also appears in DNZJSJ's
   GoldbachVaughan.truncated_dirichlet_sum_reindex, upstream PR 2430,
   commit c7833de75a61c29e2521e6f7f89fbaccf14e3801 (Apache-2.0).
   Here the source indices are filtered divisors, the inverse uses division,
   and both factor intervals have strict lower bounds. -/
private theorem factorBand (n U L R : ℕ) (F : ℕ → ℕ → ℕ → ℂ) :
    (∑ m ∈ Finset.range (n+1), ∑ a ∈ m.divisors.filter
      (fun a => L < a ∧ a ≤ R ∧ U < m/a), F m a (m/a)) =
    ∑ a ∈ Finset.Ioc L (min R n), ∑ b ∈ Finset.Ioc U (n/a), F (a*b) a b := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨x.2, x.1 / x.2⟩)
    (fun y _ => ⟨y.1 * y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m,a⟩ hx
    obtain ⟨hm,ha⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hd,hL,hR,hU⟩ := Finset.mem_filter.mp ha
    obtain ⟨hdvd,hm0⟩ := Nat.mem_divisors.mp hd
    have hmn : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Ioc.mpr ⟨hL, le_min hR
      ((Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd).trans hmn)⟩,
      Finset.mem_Ioc.mpr ⟨hU, Nat.div_le_div_right hmn⟩⟩
  · rintro ⟨a,b⟩ hy
    obtain ⟨ha,hb⟩ := Finset.mem_sigma.mp hy
    obtain ⟨hL,hR⟩ := Finset.mem_Ioc.mp ha
    obtain ⟨hU,hB⟩ := Finset.mem_Ioc.mp hb
    have ha0 : 0 < a := Nat.zero_lt_of_lt hL
    have hb0 : 0 < b := Nat.zero_lt_of_lt hU
    have hab : a*b ≤ n := by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha0).mp hB
    exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hab),
      Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_mul_right a b, (Nat.mul_pos ha0 hb0).ne'⟩,
      hL, hR.trans (min_le_left _ _), by simpa [Nat.mul_div_cancel_left b ha0] using hU⟩⟩
  · rintro ⟨m,a⟩ hx
    have hd := (Nat.mem_divisors.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).1).1
    change (⟨a*(m/a),a⟩ : Σ _ : ℕ, ℕ) = ⟨m,a⟩
    rw [Nat.mul_div_cancel_left' hd]
  · rintro ⟨a,b⟩ hx
    have ha := (Finset.mem_Ioc.mp (Finset.mem_sigma.mp hx).1).1
    change (⟨a,a*b/a⟩ : Σ _ : ℕ, ℕ) = ⟨a,b⟩
    rw [Nat.mul_div_cancel_left b (Nat.zero_lt_of_lt ha)]
  · rintro ⟨m,a⟩ hx
    have hd := (Nat.mem_divisors.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).1).1
    change F m a (m/a) = F (a*(m/a)) a (m/a)
    rw [Nat.mul_div_cancel_left' hd]

theorem PEqualNP.Outside.L_goldbach_factor_band_unfold :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let Λ := ArithmeticFunction.vonMangoldt; ∀ (n U L R : ℕ) (t : ℝ), let M := fun a : ℕ => ∑ d ∈ (Nat.divisors a).filter (fun d => U < d), μ d; let T := fun m : ℕ => ∑ a ∈ (Nat.divisors m).filter (fun a => L < a ∧ a ≤ R ∧ U < m/a), M a * Λ (m/a); (∑ m ∈ Finset.range (n+1), (T m : ℂ) * E ((m:ℝ)*t)) = ∑ a ∈ Finset.Ioc L (min R n), ∑ b ∈ Finset.Ioc U (n/a), ((M a * Λ b : ℝ):ℂ) * E ((a*b:ℕ)*t) := by
  dsimp only
  intro n U L R t
  let M := fun a : ℕ => ∑ d ∈ a.divisors.filter (fun d => U < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)
  let E := fun m : ℕ => Complex.exp (((2*Real.pi*((m:ℝ)*t):ℝ):ℂ)*Complex.I)
  let F := fun m a b : ℕ => ((M a * ArithmeticFunction.vonMangoldt b : ℝ):ℂ)*E m
  change (∑ m ∈ Finset.range (n+1), ((∑ a ∈ m.divisors.filter
    (fun a => L < a ∧ a ≤ R ∧ U < m/a), M a * ArithmeticFunction.vonMangoldt (m/a) : ℝ):ℂ) * E m) = _
  calc
    _ = ∑ m ∈ Finset.range (n+1), ∑ a ∈ m.divisors.filter
        (fun a => L < a ∧ a ≤ R ∧ U < m/a), F m a (m/a) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [Complex.ofReal_sum, Finset.sum_mul]
    _ = _ := factorBand n U L R F
