import Mathlib
open scoped BigOperators

/-!
# PREPUB goldbach: `L-goldbach-farey-sieve-cutoff-ratio`

`V n z ≤ 2 (M z / M y)^2 V n y`（`z ≤ y`，`n` 偶）：cut-off 变化的乘积比损失 ≤ 2
（常数 2 来自 `∏_{p ≥ 3}(1 + 1/(p(p-2))) ≤ 2`，后者由伸缩积
`∏_{m=2}^{M}(1 - 1/m^2) = (M+1)/(2M) ≥ 1/2` 控制）。Self-contained, Mathlib only.
-/

namespace PEqualNP.Outside

/-! ### `ℝ` 乘积比较工具（`MulLeftMono ℝ` 不存在，需自带非负前提） -/

lemma prod_le_prod_real {ι : Type*} {s : Finset ι} {f g : ι → ℝ}
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
      ih (fun i hi => hf0 i (by simp [hi])) (fun i hi => hfg i (by simp [hi]))
    have h2 : (0:ℝ) ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => hf0 i (by simp [hi]))
    have h3 : f a ≤ g a := hfg a (by simp)
    have h4 : (0:ℝ) ≤ f a := hf0 a (by simp)
    have h5 : (0:ℝ) ≤ g a := le_trans h4 h3
    exact mul_le_mul h3 h1 h2 h5

lemma prod_le_one_real {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hprod : ∏ i ∈ s, f i ≤ 1 :=
      ih (fun i hi => h0 i (by simp [hi])) (fun i hi => h1 i (by simp [hi]))
    have hnonneg : (0:ℝ) ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => h0 i (by simp [hi]))
    have ha1 : f a ≤ 1 := h1 a (by simp)
    calc f a * (∏ i ∈ s, f i) ≤ 1 * 1 := mul_le_mul ha1 hprod hnonneg (by norm_num)
      _ = 1 := by norm_num

lemma prod_le_of_subset_of_le_one_real {ι : Type*} {s t : Finset ι} {f : ι → ℝ}
    (hst : s ⊆ t) (h0 : ∀ i ∈ t, 0 ≤ f i) (h1 : ∀ i ∈ t, f i ≤ 1) :
    ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := by
  classical
  have hsplit : ∏ i ∈ t, f i = (∏ i ∈ t \ s, f i) * (∏ i ∈ s, f i) := by
    rw [← Finset.prod_sdiff hst, mul_comm]
  rw [hsplit]
  have hle : ∏ i ∈ t \ s, f i ≤ 1 :=
    prod_le_one_real (fun i hi => h0 i (Finset.mem_sdiff.mp hi).1)
      (fun i hi => h1 i (Finset.mem_sdiff.mp hi).1)
  have hs0 : (0:ℝ) ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => h0 i (hst hi))
  calc (∏ i ∈ t \ s, f i) * (∏ i ∈ s, f i) ≤ 1 * (∏ i ∈ s, f i) :=
        mul_le_mul_of_nonneg_right hle hs0
    _ = ∏ i ∈ s, f i := one_mul _

/-! ### 伸缩积 -/

/-- 伸缩积：`∏_{n=2}^{M} (1 - 1/n²) = (M+1)/(2M)`（`M ≥ 1`）。 -/
lemma prod_Icc_one_sub_inv_sq (M : ℕ) (hM : 1 ≤ M) :
    ∏ n ∈ Finset.Icc 2 M, (1 - 1/(n:ℝ)^2) = ((M:ℝ)+1)/(2*(M:ℝ)) := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    have h2M : 2 ≤ M + 1 := by omega
    rw [Finset.prod_Icc_succ_top h2M, ih]
    have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
    have hcast : (((M + 1 : ℕ)) : ℝ) = (M:ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hstep : (1 - 1/(((M:ℝ)+1))^2) = ((M:ℝ)*((M:ℝ)+2))/(((M:ℝ)+1)^2) := by
      field_simp
      ring
    rw [hstep]
    field_simp
    ring

/-- 偶数的部分积不小于全部积（因子都在 `(0,1]`）。 -/
lemma prod_Icc_le_even (M : ℕ) :
    ∏ n ∈ Finset.Icc 2 M, (1 - 1/(n:ℝ)^2)
      ≤ ∏ m ∈ (Finset.Icc 2 M).filter Even, (1 - 1/(m:ℝ)^2) := by
  have h0 : ∀ i ∈ Finset.Icc 2 M, 0 ≤ (1 - 1/(i:ℝ)^2) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hiR : (2:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi.1
    rw [sub_nonneg, div_le_one (by positivity : (0:ℝ) < (i:ℝ)^2)]
    nlinarith
  have h1 : ∀ i ∈ Finset.Icc 2 M, (1 - 1/(i:ℝ)^2) ≤ 1 := by
    intro i _
    have : (0:ℝ) ≤ 1/(i:ℝ)^2 := by positivity
    linarith
  exact prod_le_of_subset_of_le_one_real (Finset.filter_subset _ _) h0 h1

/-- 素数 `p ≥ 3` 的逐点恒等式。 -/
lemma one_add_inv_prime_eq (p : ℕ) (_hp : p.Prime) (h3 : 3 ≤ p) :
    (1:ℝ) + 1/((p:ℝ)*((p:ℝ)-2)) = (1 - 1/(((p:ℝ)-1)^2))⁻¹ := by
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast h3
  have hp0 : (p:ℝ) ≠ 0 := by positivity
  have hp1 : (p:ℝ) - 1 ≠ 0 := by linarith
  have hp2 : (p:ℝ) - 2 ≠ 0 := by linarith
  have hden : ((p:ℝ)-1)^2 ≠ 0 := pow_ne_zero 2 hp1
  have hden2 : (p:ℝ)*((p:ℝ)-2) ≠ 0 := mul_ne_zero hp0 hp2
  have hmul : (1 - 1/(((p:ℝ)-1)^2)) * (1 + 1/((p:ℝ)*((p:ℝ)-2))) = 1 := by
    field_simp
    ring
  exact (inv_eq_of_mul_eq_one_right hmul).symm

/-- 真实瓶颈：任意素数 `p ≥ 3` 时 `(1 - 1/p)^2 = (1 - 2/p) * (1 + 1/(p(p-2)))`。 -/
lemma one_sub_inv_sq_eq (p : ℕ) (_hp : p.Prime) (h3 : 3 ≤ p) :
    (1 - (p:ℝ)⁻¹)^2
      = (1 - 2/(p:ℝ)) * (1 + 1/((p:ℝ)*((p:ℝ)-2))) := by
  have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast h3
  have hp0 : (p:ℝ) ≠ 0 := by positivity
  have hp2 : (p:ℝ) - 2 ≠ 0 := by linarith
  field_simp
  ring

/-- 「伸缩积」核心：任意素数集 `Q`（素数 ≥ 3）上 `∏ (1 + 1/(p(p-2))) ≤ 2`。 -/
lemma prod_one_add_inv_le_two (Q : Finset ℕ) (y : ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ 3 ≤ p ∧ p ≤ y) :
    ∏ p ∈ Q, (1 + 1/((p:ℝ)*((p:ℝ)-2))) ≤ 2 := by
  classical
  rcases Nat.lt_or_ge y 3 with hy | hy
  · have hQe : Q = ∅ := by
      rcases Finset.eq_empty_or_nonempty Q with h | ⟨p, hp⟩
      · exact h
      · have h3 := (hQ p hp).2.1
        have hpy := (hQ p hp).2.2
        omega
    rw [hQe, Finset.prod_empty]
    norm_num
  · have hy1 : 1 ≤ y - 1 := by omega
    have hfac : ∀ p ∈ Q, (1 + 1/((p:ℝ)*((p:ℝ)-2)))
        = (1 - 1/(((p:ℝ)-1)^2))⁻¹ := by
      intro p hp
      exact one_add_inv_prime_eq p (hQ p hp).1 (hQ p hp).2.1
    rw [Finset.prod_congr rfl hfac, Finset.prod_inv_distrib]
    set S : Finset ℕ := Q.image (fun p => p - 1) with hS
    have hinj : Set.InjOn (fun p => p - 1) ↑Q := by
      intro a ha b hb hab
      have ha3 := (hQ a ha).2.1
      have hb3 := (hQ b hb).2.1
      simp only at hab
      omega
    have hprod_shift : (∏ p ∈ Q, (1 - 1/(((p:ℝ)-1)^2)))
        = ∏ m ∈ S, (1 - 1/(m:ℝ)^2) := by
      rw [hS, Finset.prod_image hinj]
      refine Finset.prod_congr rfl ?_
      intro p hp
      have hp1 : 1 ≤ p := le_trans (by norm_num) (hQ p hp).2.1
      rw [Nat.cast_sub hp1]
      norm_num
    have hS_sub : S ⊆ (Finset.Icc 2 (y-1)).filter Even := by
      intro m hm
      rw [hS, Finset.mem_image] at hm
      obtain ⟨p, hp, rfl⟩ := hm
      have h3 : 3 ≤ p := (hQ p hp).2.1
      have hpy : p ≤ y := (hQ p hp).2.2
      have hpodd_mod : p % 2 = 1 :=
        ((hQ p hp).1.eq_two_or_odd).resolve_left (by omega : p ≠ 2)
      have hpodd : Odd p := Nat.odd_iff.mpr hpodd_mod
      obtain ⟨k, hk⟩ := hpodd
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [even_iff_two_dvd]
      exact ⟨k, by omega⟩
    have h0 : ∀ i ∈ Finset.Icc 2 (y-1), 0 ≤ (1 - 1/(i:ℝ)^2) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      have hiR : (2:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi.1
      rw [sub_nonneg, div_le_one (by positivity : (0:ℝ) < (i:ℝ)^2)]
      nlinarith
    have h1 : ∀ i ∈ Finset.Icc 2 (y-1), (1 - 1/(i:ℝ)^2) ≤ 1 := by
      intro i _
      have : (0:ℝ) ≤ 1/(i:ℝ)^2 := by positivity
      linarith
    have hstep1 : (∏ n ∈ Finset.Icc 2 (y-1), (1 - 1/(n:ℝ)^2))
        ≤ ∏ m ∈ (Finset.Icc 2 (y-1)).filter Even, (1 - 1/(m:ℝ)^2) :=
      prod_Icc_le_even (y-1)
    have h0' : ∀ i ∈ (Finset.Icc 2 (y-1)).filter Even, 0 ≤ (1 - 1/(i:ℝ)^2) :=
      fun i hi => h0 i (Finset.filter_subset _ _ hi)
    have h1' : ∀ i ∈ (Finset.Icc 2 (y-1)).filter Even, (1 - 1/(i:ℝ)^2) ≤ 1 :=
      fun i hi => h1 i (Finset.filter_subset _ _ hi)
    have hstep2 : (∏ m ∈ (Finset.Icc 2 (y-1)).filter Even, (1 - 1/(m:ℝ)^2))
        ≤ ∏ m ∈ S, (1 - 1/(m:ℝ)^2) :=
      prod_le_of_subset_of_le_one_real hS_sub h0' h1'
    have hval := prod_Icc_one_sub_inv_sq (y-1) hy1
    have hy1pos : (0:ℝ) < (((y-1 : ℕ)):ℝ) := by exact_mod_cast (by omega : 0 < y-1)
    have hge : (1/2:ℝ) ≤ ∏ m ∈ S, (1 - 1/(m:ℝ)^2) := by
      have hchain : ((((y-1 : ℕ)) : ℝ) + 1)/(2*(((y-1 : ℕ)) : ℝ))
          ≤ ∏ m ∈ S, (1 - 1/(m:ℝ)^2) := by
        rw [← hval]
        exact le_trans hstep1 hstep2
      have hhalf : (1/2:ℝ) ≤ ((((y-1 : ℕ)) : ℝ) + 1)/(2*(((y-1 : ℕ)) : ℝ)) := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*(((y-1 : ℕ)) : ℝ))]
        nlinarith
      linarith
    have hS0 : ∀ m ∈ S, 0 ≤ (1 - 1/(m:ℝ)^2) := by
      intro m hm
      have hm2 : 2 ≤ m := by
        have := hS_sub hm
        rw [Finset.mem_filter, Finset.mem_Icc] at this
        exact this.1.1
      have hmR : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2
      rw [sub_nonneg, div_le_one (by positivity : (0:ℝ) < (m:ℝ)^2)]
      nlinarith
    have hPpos : 0 < ∏ m ∈ S, (1 - 1/(m:ℝ)^2) := by
      refine Finset.prod_pos ?_
      intro m hm
      have hm2 : 2 ≤ m := by
        have := hS_sub hm
        rw [Finset.mem_filter, Finset.mem_Icc] at this
        exact this.1.1
      have hmR : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2
      rw [sub_pos, div_lt_one (by positivity : (0:ℝ) < (m:ℝ)^2)]
      nlinarith
    rw [hprod_shift]
    rw [inv_le_iff_one_le_mul₀ hPpos]
    nlinarith

/-! ### 两个主乘积界 -/

/-- 每个素数 `p` 时 `0 < 1 - 1/p ≤ 1`。 -/
lemma one_sub_inv_bounds (p : ℕ) (hp : p.Prime) :
    0 < 1 - (p:ℝ)⁻¹ ∧ 1 - (p:ℝ)⁻¹ ≤ 1 := by
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  constructor
  · have hpR : (0:ℝ) < (p:ℝ) := by linarith
    rw [sub_pos]
    have hdiv : (1:ℝ)/(p:ℝ) < 1 := (div_lt_one hpR).mpr (by linarith)
    rwa [one_div] at hdiv
  · have h : (0:ℝ) ≤ (p:ℝ)⁻¹ := by positivity
    linarith

/-- 每个素数 `p` 时 `0 ≤ 1 - 2/p ≤ 1`（`p = 2` 时为 `0`）。 -/
lemma one_sub_two_inv_bounds (p : ℕ) (hp : p.Prime) :
    0 ≤ 1 - 2/(p:ℝ) ∧ 1 - 2/(p:ℝ) ≤ 1 := by
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  constructor
  · rw [sub_nonneg, div_le_one (by linarith : (0:ℝ) < (p:ℝ))]
    linarith
  · have h : (0:ℝ) ≤ 2/(p:ℝ) := by positivity
    linarith


/-! ### 主定理：cut-off 比损失 ≤ 2 -/

theorem L_goldbach_farey_sieve_cutoff_ratio :
    let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3); let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime; let M := fun z : ℕ => ∏ p ∈ P z, (1-(p:ℝ)⁻¹); let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ)); ∀ n z y : ℕ, 12 ≤ n → Even n → 2 ≤ z → z ≤ y → V n z ≤ 2*(M z/M y)^2 * V n y := by
  dsimp only
  intro n z y hn hEven hz hzy
  set Pz : Finset ℕ := (Finset.Icc 2 z).filter Nat.Prime with hPz
  set Py : Finset ℕ := (Finset.Icc 2 y).filter Nat.Prime with hPy
  set Qz : Finset ℕ := Pz.filter (fun p => ¬ p ∣ n) with hQz
  set Qy : Finset ℕ := Py.filter (fun p => ¬ p ∣ n) with hQy
  set C : ℝ := (((Finset.Icc ((n+2)/3) ((2*n)/3)).card:ℝ) * (n.totient:ℝ)) / (n:ℝ) with hC
  set Fz : ℝ := ∏ p ∈ Qz, (1 - 2/(p:ℝ)) with hFz
  set Fy : ℝ := ∏ p ∈ Qy, (1 - 2/(p:ℝ)) with hFy
  set Bz : ℝ := ∏ p ∈ Pz, (1-(p:ℝ)⁻¹) with hBz
  set By : ℝ := ∏ p ∈ Py, (1-(p:ℝ)⁻¹) with hBy
  change C * Fz ≤ 2 * (Bz / By)^2 * (C * Fy)
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h2dvd : 2 ∣ n := even_iff_two_dvd.mp hEven
  -- 常数因子非负
  have hCnonneg : 0 ≤ C := by
    rw [hC]
    apply div_nonneg
    · apply mul_nonneg <;> positivity
    · exact hnpos.le
  -- F 因子正性
  have hFzpos : 0 < Fz := by
    rw [hFz]
    refine Finset.prod_pos ?_
    intro p hp
    obtain ⟨hpP, hpn⟩ := Finset.mem_filter.mp hp
    have hprime : p.Prime := (Finset.mem_filter.mp hpP).2
    have hne2 : p ≠ 2 := by
      intro h
      subst h
      exact hpn h2dvd
    have hge3R : (2:ℝ) < (p:ℝ) := by
      exact_mod_cast (by have := hprime.two_le; omega : 2 < p)
    have hpR : (0:ℝ) < (p:ℝ) := by positivity
    rw [sub_pos]
    have hlt : 2/(p:ℝ) < 1 := (div_lt_one hpR).mpr hge3R
    linarith
  have hFypos : 0 < Fy := by
    rw [hFy]
    refine Finset.prod_pos ?_
    intro p hp
    obtain ⟨hpP, hpn⟩ := Finset.mem_filter.mp hp
    have hprime : p.Prime := (Finset.mem_filter.mp hpP).2
    have hne2 : p ≠ 2 := by
      intro h
      subst h
      exact hpn h2dvd
    have hge3R : (2:ℝ) < (p:ℝ) := by
      exact_mod_cast (by have := hprime.two_le; omega : 2 < p)
    have hpR : (0:ℝ) < (p:ℝ) := by positivity
    rw [sub_pos]
    have hlt : 2/(p:ℝ) < 1 := (div_lt_one hpR).mpr hge3R
    linarith
  -- B 因子正性
  have hBzpos : 0 < Bz := by
    rw [hBz]
    refine Finset.prod_pos ?_
    intro p hp
    exact (one_sub_inv_bounds p (Finset.mem_filter.mp hp).2).1
  have hBypos : 0 < By := by
    rw [hBy]
    refine Finset.prod_pos ?_
    intro p hp
    exact (one_sub_inv_bounds p (Finset.mem_filter.mp hp).2).1
  -- 子集关系
  have hPsub : Pz ⊆ Py := by
    intro p hp
    simp only [hPz, hPy, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, le_trans hp.1.2 hzy⟩, hp.2⟩
  have hQsub : Qz ⊆ Qy := by
    intro p hp
    simp only [hQz, hQy, Finset.mem_filter] at hp ⊢
    exact ⟨hPsub hp.1, hp.2⟩
  -- 引入比式量
  set Q1 : ℝ := ∏ p ∈ Py \ Pz, (1-(p:ℝ)⁻¹) with hQ1
  set Q2 : ℝ := ∏ p ∈ Qy \ Qz, (1-2/(p:ℝ)) with hQ2
  -- 乘积分解
  have hBsplit : By = Bz * Q1 := by
    rw [hBy, hBz, hQ1, ← Finset.prod_sdiff hPsub]
    ring
  have hFsplit : Fy = Fz * Q2 := by
    rw [hFy, hFz, hQ2, ← Finset.prod_sdiff hQsub]
    ring
  have hQ1pos : 0 < Q1 := by
    rw [hQ1]
    refine Finset.prod_pos ?_
    intro p hp
    have hpPy : p ∈ Py := (Finset.mem_sdiff.mp hp).1
    exact (one_sub_inv_bounds p (Finset.mem_filter.mp hpPy).2).1
  have hQ1ne : Q1 ≠ 0 := hQ1pos.ne'
  have hQ2nonneg : 0 ≤ Q2 := by
    rw [hQ2]
    refine Finset.prod_nonneg ?_
    intro p hp
    have hpQy : p ∈ Qy := (Finset.mem_sdiff.mp hp).1
    have hpPy : p ∈ Py := (Finset.mem_filter.mp hpQy).1
    exact (one_sub_two_inv_bounds p (Finset.mem_filter.mp hpPy).2).1
  -- 比值
  have hBratio : Bz / By = Q1⁻¹ := by
    rw [hBsplit]
    field_simp [hQ1ne, hBzpos.ne']
  -- 核心：Q1² ≤ 2 Q2
  have hKey : Q1^2 ≤ 2 * Q2 := by
    set A : Finset ℕ := (Py \ Pz).filter (fun p => ¬ p ∣ n) with hA
    have hAeq : Qy \ Qz = A := by
      rw [hA]
      ext p
      simp only [hQy, hQz, Finset.mem_sdiff, Finset.mem_filter]
      tauto
    have hQ1sq : Q1^2 = ∏ p ∈ Py \ Pz, (1-(p:ℝ)⁻¹)^2 := by
      rw [hQ1, sq, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl ?_
      intro p _
      ring
    have hsplit : (∏ p ∈ Py \ Pz, (1-(p:ℝ)⁻¹)^2)
        = (∏ p ∈ A, (1-(p:ℝ)⁻¹)^2)
          * (∏ p ∈ (Py \ Pz).filter (fun p => p ∣ n), (1-(p:ℝ)⁻¹)^2) := by
      have h := Finset.prod_filter_mul_prod_filter_not (Py \ Pz) (fun p => ¬ p ∣ n)
        (fun p => (1-(p:ℝ)⁻¹)^2)
      simp only [not_not] at h
      rw [hA]
      exact h.symm
    -- A 上的逐点恒等式与界
    have hAprod : (∏ p ∈ A, (1-(p:ℝ)⁻¹)^2) = Q2
        * (∏ p ∈ A, (1 + 1/((p:ℝ)*((p:ℝ)-2)))) := by
      have hQ2A : Q2 = ∏ p ∈ A, (1-2/(p:ℝ)) := by
        rw [hQ2, hAeq]
      rw [hQ2A, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl ?_
      intro p hp
      have hpK : p ∈ Py \ Pz := (Finset.mem_filter.mp hp).1
      have hpPy : p ∈ Py := (Finset.mem_sdiff.mp hpK).1
      have hpz : p ∉ Pz := (Finset.mem_sdiff.mp hpK).2
      have hprime : p.Prime := (Finset.mem_filter.mp hpPy).2
      have hge3 : 3 ≤ p := by
        by_contra hlt
        push_neg at hlt
        have hpPz : p ∈ Pz := by
          rw [hPz, Finset.mem_filter]
          exact ⟨by rw [Finset.mem_Icc]; exact ⟨hprime.two_le, by omega⟩, hprime⟩
        exact hpz hpPz
      exact one_sub_inv_sq_eq p hprime hge3
    have hAbound : (∏ p ∈ A, (1 + 1/((p:ℝ)*((p:ℝ)-2)))) ≤ 2 := by
      refine prod_one_add_inv_le_two A y ?_
      intro p hp
      have hpK : p ∈ Py \ Pz := (Finset.mem_filter.mp hp).1
      have hpPy : p ∈ Py := (Finset.mem_sdiff.mp hpK).1
      have hpz : p ∉ Pz := (Finset.mem_sdiff.mp hpK).2
      obtain ⟨hpIcc, hprime⟩ := Finset.mem_filter.mp hpPy
      refine ⟨hprime, ?_, (Finset.mem_Icc.mp hpIcc).2⟩
      by_contra hlt
      push_neg at hlt
      have hpPz : p ∈ Pz := by
        rw [hPz, Finset.mem_filter]
        exact ⟨by rw [Finset.mem_Icc]; exact ⟨hprime.two_le, by omega⟩, hprime⟩
      exact hpz hpPz
    have hApos : 0 ≤ ∏ p ∈ A, (1 + 1/((p:ℝ)*((p:ℝ)-2))) := by
      refine Finset.prod_nonneg ?_
      intro p hp
      have hpK : p ∈ Py \ Pz := (Finset.mem_filter.mp hp).1
      have hpPy : p ∈ Py := (Finset.mem_sdiff.mp hpK).1
      have hpz : p ∉ Pz := (Finset.mem_sdiff.mp hpK).2
      have hprime : p.Prime := (Finset.mem_filter.mp hpPy).2
      have hge3 : 3 ≤ p := by
        by_contra hlt
        push_neg at hlt
        have hpPz : p ∈ Pz := by
          rw [hPz, Finset.mem_filter]
          exact ⟨by rw [Finset.mem_Icc]; exact ⟨hprime.two_le, by omega⟩, hprime⟩
        exact hpz hpPz
      have hge3R : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hge3
      have hden : (0:ℝ) < (p:ℝ)*((p:ℝ)-2) := by nlinarith
      have hpos : (0:ℝ) < 1/((p:ℝ)*((p:ℝ)-2)) := by positivity
      linarith
    have hBbound : (∏ p ∈ (Py \ Pz).filter (fun p => p ∣ n), (1-(p:ℝ)⁻¹)^2) ≤ 1 := by
      refine prod_le_one_real ?_ ?_
      · intro p hp
        have hpPy : p ∈ Py := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).1
        have hb := one_sub_inv_bounds p (Finset.mem_filter.mp hpPy).2
        positivity
      · intro p hp
        have hpPy : p ∈ Py := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).1
        have hb := one_sub_inv_bounds p (Finset.mem_filter.mp hpPy).2
        nlinarith [hb.1, hb.2]
    have hBnonneg : 0 ≤ ∏ p ∈ (Py \ Pz).filter (fun p => p ∣ n), (1-(p:ℝ)⁻¹)^2 := by
      refine Finset.prod_nonneg ?_
      intro p hp
      have hpPy : p ∈ Py := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).1
      have hb := one_sub_inv_bounds p (Finset.mem_filter.mp hpPy).2
      positivity
    rw [hQ1sq, hsplit, hAprod]
    have hprod_le : Q2 * (∏ p ∈ A, (1 + 1/((p:ℝ)*((p:ℝ)-2))))
        * (∏ p ∈ (Py \ Pz).filter (fun p => p ∣ n), (1-(p:ℝ)⁻¹)^2) ≤ Q2 * 2 * 1 := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left hAbound hQ2nonneg
      · exact hBbound
      · exact hBnonneg
      · positivity
    linarith
  -- F 核
  have hcore : Fz ≤ 2 * (Bz / By)^2 * Fy := by
    have hQ1sqpos : (0:ℝ) < Q1^2 := by positivity
    have hmain : Fz ≤ 2 * (Q1⁻¹)^2 * (Fz * Q2) := by
      have hstep : 2 * (Q1⁻¹)^2 * (Fz * Q2) = 2 * Fz * Q2 / Q1^2 := by
        rw [inv_pow]
        field_simp
      rw [hstep, le_div_iff₀ hQ1sqpos]
      have hmul := mul_le_mul_of_nonneg_left hKey hFzpos.le
      linarith [hmul]
    rw [hBratio, hFsplit]
    exact hmain
  calc C * Fz ≤ C * (2 * (Bz / By)^2 * Fy) :=
        mul_le_mul_of_nonneg_left hcore hCnonneg
    _ = 2 * (Bz / By)^2 * (C * Fy) := by ring

end PEqualNP.Outside

/-! Canonical module-named statement (platform checker requires a declaration
named exactly after the gap module). -/
theorem Conjectures.Goldbach.FareySieveCutoffRatio :
    let I := fun n : ℕ => Finset.Icc ((n+2)/3) ((2*n)/3); let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime; let M := fun z : ℕ => ∏ p ∈ P z, (1-(p:ℝ)⁻¹); let V := fun n z : ℕ => ((I n).card:ℝ)*(n.totient:ℝ)/n * ∏ p ∈ (P z).filter (fun p => ¬ p ∣ n), (1-2/(p:ℝ)); ∀ n z y : ℕ, 12 ≤ n → Even n → 2 ≤ z → z ≤ y → V n z ≤ 2*(M z/M y)^2 * V n y
  := PEqualNP.Outside.L_goldbach_farey_sieve_cutoff_ratio
