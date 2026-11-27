import Mathlib

private theorem count_fibers {q : ℕ} {H : ℝ} (hH : 0 ≤ H) (F : ℕ → ℝ) (J : ℕ → ℤ)
    (inj : Set.InjOn J (Finset.range q : Set ℕ))
    (size : ∀ r ∈ Finset.range q, (J r).natAbs ≤ q)
    (cap : ∀ r, F r ≤ H)
    (far : ∀ r ∈ Finset.range q, 3 ≤ (J r).natAbs → F r ≤ q / ((J r).natAbs:ℝ)) :
    ∑ r ∈ Finset.range q, F r ≤ 5*H + 2*(q:ℝ)*(1+Real.log q) := by
  classical
  let R := Finset.range q
  let A := R.filter (fun r => (J r).natAbs < 3)
  let B := R.filter (fun r => ¬(J r).natAbs < 3)
  have hnear : ∑ r ∈ A, F r ≤ 5*H := by
    have hc : A.card ≤ 5 := by
      calc A.card = (A.image J).card := (Finset.card_image_of_injOn (inj.mono (Finset.filter_subset ..))).symm
           _ ≤ (Finset.Icc (-2:ℤ) 2).card := Finset.card_le_card (by
             intro z hz; obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hz
             have h := (Finset.mem_filter.mp hr).2
             exact Finset.mem_Icc.mpr (by omega))
           _ = 5 := by decide
    calc _ ≤ ∑ _r ∈ A, H := Finset.sum_le_sum (fun r _ => cap r)
         _ = (A.card:ℝ)*H := by simp
         _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hH
  have side {S : Finset ℕ} (hS : S ⊆ B) (hsg : (∀ r ∈ S, 0 ≤ J r) ∨ (∀ r ∈ S, J r < 0)) :
      ∑ r ∈ S, F r ≤ (q:ℝ)*(1+Real.log q) := by
    let g := fun r => (J r).natAbs
    have mem (r : ℕ) (hr : r ∈ S) := Finset.mem_filter.mp (hS hr)
    have hgi : Set.InjOn g (S : Set ℕ) := by
      intro r hr t ht he
      apply inj (mem r hr).1 (mem t ht).1
      change (J r).natAbs = (J t).natAbs at he
      rcases hsg with h | h <;> have hr' := h r hr <;> have ht' := h t ht <;> omega
    have sub : S.image g ⊆ Finset.Icc 1 q := by
      intro z hz; obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_Icc.mpr ⟨by dsimp [g]; have := (mem r hr).2; omega, size r (mem r hr).1⟩
    calc _ ≤ ∑ r ∈ S, (q:ℝ)*(g r:ℝ)⁻¹ := Finset.sum_le_sum (fun r hr => by
               simpa [g,div_eq_mul_inv] using far r (mem r hr).1 (by have := (mem r hr).2; omega))
         _ = ∑ z ∈ S.image g, (q:ℝ)*(z:ℝ)⁻¹ := by rw [Finset.sum_image hgi]
         _ ≤ ∑ z ∈ Finset.Icc 1 q, (q:ℝ)*(z:ℝ)⁻¹ := Finset.sum_le_sum_of_subset_of_nonneg sub (by intros; positivity)
         _ ≤ _ := by
           rw [← Finset.mul_sum]
           apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
           simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log q
  have hb : (∑ r ∈ B, F r) ≤ 2*((q:ℝ)*(1+Real.log q)) := by
    rw [← Finset.sum_filter_add_sum_filter_not B (fun r => 0 ≤ J r)]
    have hl := side (S:=B.filter (fun r => 0 ≤ J r)) (Finset.filter_subset ..)
      (Or.inl (fun _ hr => (Finset.mem_filter.mp hr).2))
    have hr := side (S:=B.filter (fun r => ¬0 ≤ J r)) (Finset.filter_subset ..)
      (Or.inr (fun _ hr => lt_of_not_ge (Finset.mem_filter.mp hr).2))
    linarith only [hl,hr]
  have eq := Finset.sum_filter_add_sum_filter_not R (fun r => (J r).natAbs < 3) F
  change (∑ r ∈ A, F r) + (∑ r ∈ B, F r) = _ at eq
  linarith only [hnear,hb,eq]

theorem Conjectures.Goldbach.ReciprocalChordSum :
    let E (y : ℝ) := Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I);
    let cap (H y : ℝ) := if E y = 1 then H else min H (2 / ‖1 - E y‖);
    ∀ (a q : ℕ) (t x H : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ H → |t - (a : ℝ) / q| ≤ 1 / (q : ℝ)^2 → (∑ r ∈ Finset.range q, cap H (x + (r : ℝ)*t)) ≤ 6 * (H + (q : ℝ) * Real.log (2 * q)) := by
  intro E cap a q t x H hq hcop hH happ
  let y (r : ℕ) := x+r*t
  let J (r : ℕ) : ℤ := round ((q:ℝ)*x)+(a:ℤ)*r-(q:ℤ)*round (y r)
  have hQ : (0:ℝ)<q := by exact_mod_cast hq
  have capH (r : ℕ) : cap H (y r) ≤ H := by dsimp only [cap]; split <;> simp
  have hlog : 1/2 ≤ Real.log (2*(q:ℝ)) := by
    have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
    exact (by linarith [Real.log_two_gt_d9] : 1/2 ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) (by linarith))
  by_cases hsmall : q ≤ 3
  · have h := Finset.sum_le_sum (s:=Finset.range q) (fun r _ => capH r)
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at h
    have h1 := mul_le_mul_of_nonneg_right (show (q:ℝ) ≤ 3 by exact_mod_cast hsmall) hH
    have h2 := mul_nonneg hQ.le (show 0 ≤ Real.log (2*(q:ℝ)) by linarith)
    exact h.trans (by linarith)
  have inj : Set.InjOn J (Finset.range q : Set ℕ) := by
    intro r hr s hs heq
    change _ + (a:ℤ)*r - (q:ℤ)*round (y r) = _ + (a:ℤ)*s - (q:ℤ)*round (y s) at heq
    have hm : a*r ≡ a*s [MOD q] := by
      apply Int.natCast_modEq_iff.mp
      apply Int.modEq_iff_dvd.mpr
      refine ⟨round (y s)-round (y r),?_⟩
      push_cast; linarith only [heq]
    have h := Nat.ModEq.cancel_left_of_coprime hcop.symm hm
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt (Finset.mem_range.mp hr),Nat.mod_eq_of_lt (Finset.mem_range.mp hs)] using h
  have approx (r : ℕ) (hr : r ∈ Finset.range q) :
      |(J r:ℝ)| ≤ (q:ℝ)*|y r-round (y r)|+3/2 := by
    have h1 := abs_sub_round ((q:ℝ)*x)
    have hrq : (r:ℝ) ≤ q := by exact_mod_cast (Finset.mem_range.mp hr).le
    have hb := mul_le_mul_of_nonneg_left happ (mul_nonneg hQ.le (Nat.cast_nonneg r))
    have hscale : (q:ℝ)*r*(1/(q:ℝ)^2) ≤ 1 := by
      field_simp [hQ.ne']; nlinarith [mul_le_mul_of_nonneg_left hrq hQ.le]
    have h2 : |(q:ℝ)*r*(t-(a:ℝ)/q)| ≤ 1 := by
      rw [abs_mul,abs_of_nonneg (mul_nonneg hQ.le (Nat.cast_nonneg r))]; exact hb.trans hscale
    have hid : (J r:ℝ) = (q:ℝ)*(y r-round (y r)) +
        ((round ((q:ℝ)*x):ℝ)-(q:ℝ)*x) - (q:ℝ)*r*(t-(a:ℝ)/q) := by
      dsimp [J,y]; push_cast; field_simp [hQ.ne']; ring
    rw [hid]
    have ht := abs_sub ((q:ℝ)*(y r-round (y r)) + ((round ((q:ℝ)*x):ℝ)-(q:ℝ)*x)) ((q:ℝ)*r*(t-(a:ℝ)/q))
    have hs := abs_add_le ((q:ℝ)*(y r-round (y r))) ((round ((q:ℝ)*x):ℝ)-(q:ℝ)*x)
    rw [abs_mul,abs_of_pos hQ,abs_sub_comm (round ((q:ℝ)*x):ℝ)] at hs
    linarith only [ht,hs,h1,h2]
  have hsize (r : ℕ) (hr : r ∈ Finset.range q) : (J r).natAbs ≤ q := by
    have h := approx r hr
    have h' := mul_le_mul_of_nonneg_left (abs_sub_round (y r)) hQ.le
    have h4 : (4:ℝ) ≤ q := by exact_mod_cast (show 4 ≤ q by omega)
    have hz : |(J r:ℝ)| ≤ q := by linarith
    have hreal : ((J r).natAbs:ℝ) ≤ q := by simpa using hz
    exact_mod_cast hreal
  have far (r : ℕ) (hr : r ∈ Finset.range q) (hj : 3 ≤ (J r).natAbs) :
      cap H (y r) ≤ q/((J r).natAbs:ℝ) := by
    let z := y r - round (y r)
    have h3' : (3:ℝ) ≤ ((J r).natAbs:ℝ) := by exact_mod_cast hj
    have h3 : (3:ℝ) ≤ |(J r:ℝ)| := by simpa using h3'
    have hz : |(J r:ℝ)| ≤ 2*(q:ℝ)*|z| := by
      have h := approx r hr
      change _ ≤ (q:ℝ)*|z|+3/2 at h
      linarith
    have hE : E (y r) = E z := by
      have he (u v : ℝ) : E (u+v) = E u*E v := by
        dsimp only [E]; rw [← Complex.exp_add]; congr 1; push_cast; ring
      have hi : E ((round (y r):ℤ):ℝ) = 1 := by
        dsimp only [E]
        rw [show ((2*Real.pi*((round (y r):ℤ):ℝ):ℝ):ℂ)*Complex.I =
            ((round (y r):ℤ):ℂ)*(2*(Real.pi:ℂ)*Complex.I) by push_cast; ring]
        exact Complex.exp_int_mul_two_pi_mul_I _
      rw [show y r = z+((round (y r):ℤ):ℝ) by dsimp [z]; ring,he,hi,mul_one]
    have hc : 4*|z| ≤ ‖1-E (y r)‖ := by
      rw [hE,norm_sub_rev]
      dsimp only [E]
      rw [mul_comm _ Complex.I,Complex.norm_exp_I_mul_ofReal_sub_one]
      have hπ := Real.pi_pos
      have hs := Real.mul_abs_le_abs_sin (x:=Real.pi*z) (by
        rw [abs_mul,abs_of_pos hπ]; linarith [mul_le_mul_of_nonneg_left (abs_sub_round (y r)) hπ.le])
      rw [abs_mul,abs_of_pos hπ] at hs
      rw [show 2*Real.pi*z/2 = Real.pi*z by ring,Real.norm_eq_abs,abs_mul]
      norm_num
      have e : 2/Real.pi*(Real.pi*|z|) = 2*|z| := by field_simp
      linarith
    have hab : 0 < |z| := by by_contra! hn; nlinarith only [hz,h3,mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2*(q:ℝ)) hn]
    have hne : E (y r) ≠ 1 := by intro he; rw [he,sub_self,norm_zero] at hc; linarith
    change (if E (y r) = 1 then H else min H _) ≤ _
    rw [ite_eq_right hne]
    apply (min_le_right ..).trans
    apply (div_le_div_iff₀ (by linarith : 0 < ‖1-E (y r)‖) (by exact_mod_cast (show 0 < (J r).natAbs by omega))).mpr
    have he : ((J r).natAbs:ℝ) = |(J r:ℝ)| := by simp
    rw [he]
    nlinarith only [hz,mul_le_mul_of_nonneg_left hc hQ.le]
  have h := count_fibers hH (fun r => cap H (y r)) J inj hsize capH far
  apply h.trans
  have hlog' := Real.log_nonneg (show (1:ℝ) ≤ q by exact_mod_cast hq)
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hQ.ne']
  nlinarith only [hH,mul_nonneg hQ.le hlog',mul_le_mul_of_nonneg_left (show 1/2 ≤ Real.log 2 by linarith [Real.log_two_gt_d9]) hQ.le]
