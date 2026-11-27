import Mathlib

private theorem helperbudget :
    ∀ (Y : ℕ), (∑ d ∈ Finset.Icc 1 Y, ∑ e ∈ Finset.Icc 1 Y, (1:ℝ)/(Nat.lcm d e:ℝ)) ≤ (1+Real.log (max 1 Y))^3 := by
  intro Y
  classical
  let I := Finset.Icc 1 Y
  let T : ℕ × ℕ → ℕ × ℕ × ℕ := fun (d,e) => (d.gcd e, d/(d.gcd e), e/(d.gcd e))
  have hd (d e : ℕ) : (T (d,e)).2.1*(T (d,e)).1 = d :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have he (d e : ℕ) : (T (d,e)).2.2*(T (d,e)).1 = e :=
    Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  have rep (d e : ℕ) (h : 0<d) : (T (d,e)).1*(T (d,e)).2.1*(T (d,e)).2.2 = Nat.lcm d e := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.gcd_pos_of_pos_left e h)
    calc
      d.gcd e * ((T (d,e)).1*(T (d,e)).2.1*(T (d,e)).2.2) =
        ((T (d,e)).2.1*(T (d,e)).1)*((T (d,e)).2.2*(T (d,e)).1) := by change (d.gcd e)*((d.gcd e)*(d/(d.gcd e))*(e/(d.gcd e)))=(d/(d.gcd e)*(d.gcd e))*(e/(d.gcd e)*(d.gcd e)); ring
      _ = d*e := by rw [hd,he]
      _ = _ := (Nat.gcd_mul_lcm ..).symm
  let W : ℕ × ℕ × ℕ → ℝ := fun z => (1/(z.1:ℝ))*(1/(z.2.1:ℝ))*(1/(z.2.2:ℝ))
  have inj : Function.Injective T := by
    rintro ⟨d,e⟩ ⟨a,b⟩ h
    exact Prod.ext (by simpa only [hd] using congrArg (fun z : ℕ × ℕ × ℕ => z.2.1*z.1) h)
      (by simpa only [he] using congrArg (fun z : ℕ × ℕ × ℕ => z.2.2*z.1) h)
  have subset : (I ×ˢ I).image T ⊆ I ×ˢ (I ×ˢ I) := by
    intro z hz
    obtain ⟨⟨d,e⟩, hde, rfl⟩ := Finset.mem_image.mp hz
    rcases Finset.mem_product.mp hde with ⟨hd',he'⟩
    have ⟨hd1,hdY⟩ := Finset.mem_Icc.mp hd'
    have ⟨he1,heY⟩ := Finset.mem_Icc.mp he'
    have hg := Nat.gcd_pos_of_pos_left e hd1
    have hgd := Nat.le_of_dvd hd1 (Nat.gcd_dvd_left d e)
    have hge := Nat.le_of_dvd he1 (Nat.gcd_dvd_right d e)
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hg,hgd.trans hdY⟩, Finset.mem_product.mpr ⟨?_,?_⟩⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.div_pos hgd hg,(Nat.div_le_self ..).trans hdY⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.div_pos hge hg,(Nat.div_le_self ..).trans heY⟩
  have bound := Finset.sum_le_sum_of_injOn (f:=fun z : ℕ × ℕ => (1:ℝ)/(Nat.lcm z.1 z.2:ℝ)) (g:=W)
    T inj.injOn subset (by
      rintro ⟨d,e⟩ hz
      have h := rep d e (Finset.mem_Icc.mp (Finset.mem_product.mp hz).1).1
      change 1/(Nat.lcm d e:ℝ) ≤ 1/((T (d,e)).1:ℝ)*(1/((T (d,e)).2.1:ℝ))*(1/((T (d,e)).2.2:ℝ))
      rw [← h]
      simp [Nat.cast_mul,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]) (by
      intro z _ _
      dsimp [W]
      positivity)
  have HB : (∑ d ∈ I, 1/(d:ℝ)) ≤ 1+Real.log (max 1 Y) := by
    by_cases hY : Y=0
    · simp [I,hY]
    · rw [max_eq_right (by exact_mod_cast (show 1≤Y by omega) : (1:ℝ)≤Y)]
      simpa [I,harmonic_eq_sum_Icc,one_div] using harmonic_le_one_add_log Y
  calc
    _ = ∑ z ∈ I ×ˢ I, (1:ℝ)/(Nat.lcm z.1 z.2:ℝ) := (Finset.sum_product ..).symm
    _ ≤ ∑ z ∈ I ×ˢ (I ×ˢ I), W z := bound
    _ = (∑ d ∈ I, 1/(d:ℝ))^3 := by
      simp only [W,Finset.sum_product,Finset.sum_mul,Finset.mul_sum,pow_succ,pow_zero,one_mul]
      ac_rfl
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) HB _

private theorem helperintersection :
    ∀ (d e Y : ℕ), 0 < d → 0 < e → ((Finset.Icc 1 Y).filter (fun r => d ∣ r ∧ e ∣ r)).card = Y / (Nat.lcm d e) := by
  intro d e Y _ _
  rw [← Nat.card_multiples' Y (Nat.lcm d e)]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, Nat.lcm_dvd_iff]
  omega

private theorem helpermajorant :
    ∀ U R : ℕ, |∑ d ∈ R.divisors.filter (fun d => U < d), (ArithmeticFunction.moebius d:ℝ)| ≤ (R.divisors.card:ℝ) := by
  intro U R
  calc
    _ ≤ ∑ d ∈ R.divisors.filter (fun d => U < d), |(ArithmeticFunction.moebius d:ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ R.divisors.filter (fun d => U < d), (1:ℝ) := Finset.sum_le_sum fun d _ => by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=d))
    _ ≤ _ := by simpa using (show (((R.divisors.filter (fun d => U < d)).card:ℝ) ≤ (R.divisors.card:ℝ)) by exact_mod_cast Finset.card_filter_le _ _)

theorem PEqualNP.Outside.L_goldbach_minor_type_two_tail_second_moment :
    ∀ (U Y : ℕ), (∑ r ∈ Finset.Icc 1 Y, (∑ d ∈ r.divisors.filter (fun d => U < d), (ArithmeticFunction.moebius d:ℝ))^2) ≤ (Y:ℝ)*(1+Real.log (max 1 Y))^3 := by
  intro U Y
  classical
  let I := Finset.Icc 1 Y
  let P := I ×ˢ I
  let c := fun (r : ℕ) (z : ℕ × ℕ) => if z.1 ∣ r ∧ z.2 ∣ r then (1:ℝ) else 0
  have bound (r : ℕ) (hr : r∈I) : (∑ d ∈ r.divisors.filter (fun d => U<d), (ArithmeticFunction.moebius d:ℝ))^2 ≤ ∑ z ∈ P,c r z := by
    have hr0 := (Finset.mem_Icc.mp hr).1
    have hrY := (Finset.mem_Icc.mp hr).2
    have hs : P.filter (fun z => z.1 ∣ r ∧ z.2 ∣ r) = r.divisors ×ˢ r.divisors := by
      ext z
      obtain ⟨a,b⟩ := z
      simp only [P,I,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc,Nat.mem_divisors]
      constructor
      · rintro ⟨_,ha,hb⟩; exact ⟨⟨ha,by omega⟩,⟨hb,by omega⟩⟩
      · rintro ⟨⟨ha,_⟩,hb,_⟩
        exact ⟨⟨⟨Nat.pos_of_dvd_of_pos ha hr0,(Nat.le_of_dvd hr0 ha).trans hrY⟩,⟨Nat.pos_of_dvd_of_pos hb hr0,(Nat.le_of_dvd hr0 hb).trans hrY⟩⟩,ha,hb⟩
    have h := pow_le_pow_left₀ (abs_nonneg _) (helpermajorant U r) 2
    rw [sq_abs] at h
    convert h using 1
    simp [c,← Finset.sum_filter,hs,Finset.card_product,pow_two]
  have count (z : ℕ × ℕ) (hz : z∈P) : (∑ r ∈ I,c r z) ≤ (Y:ℝ)*(1/(Nat.lcm z.1 z.2:ℝ)) := by
    have h := Finset.mem_product.mp hz
    have hd := (Finset.mem_Icc.mp h.1).1
    have he := (Finset.mem_Icc.mp h.2).1
    have hnum : (∑ r ∈ I,c r z)=((Y/(Nat.lcm z.1 z.2):ℕ):ℝ) := by
      simp [c,← Finset.sum_filter,I,helperintersection z.1 z.2 Y hd he]
    rw [hnum,mul_one_div]
    apply (le_div_iff₀ ?_).mpr
    · exact_mod_cast Nat.div_mul_le_self Y (z.1.lcm z.2)
    · exact_mod_cast Nat.lcm_pos hd he
  calc
    _ ≤ ∑ r ∈ I,∑ z ∈ P,c r z := Finset.sum_le_sum bound
    _ = ∑ z ∈ P,∑ r ∈ I,c r z := Finset.sum_comm
    _ ≤ ∑ z ∈ P,(Y:ℝ)*(1/(Nat.lcm z.1 z.2:ℝ)) := Finset.sum_le_sum count
    _ = (Y:ℝ)*(∑ d ∈ I,∑ e ∈ I,1/(Nat.lcm d e:ℝ)) := by rw [← Finset.mul_sum,Finset.sum_product]
    _ ≤ _ := mul_le_mul_of_nonneg_left (helperbudget Y) (by positivity)
