import Mathlib

private theorem units_to_residues {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (f : ZMod q -> Complex) :
    ∑ u : (ZMod q)ˣ, chi (u : ZMod q) * f u =
      ∑ x : ZMod q, chi x * f x := by
  classical
  let s : Finset (ZMod q) := Finset.univ.filter IsUnit
  have hunits : (∑ u : (ZMod q)ˣ, chi (u : ZMod q) * f u) =
      ∑ x ∈ s, chi x * f x := by
    apply Finset.sum_bij (s := (Finset.univ : Finset (ZMod q)ˣ))
      (t := s) (fun u hu => (u : ZMod q))
    · intro u hu
      simp [s, u.isUnit]
    · intro u hu v hv huv
      exact Units.ext huv
    · intro x hx
      have hxunit : IsUnit x := by simpa [s] using hx
      exact ⟨hxunit.unit, Finset.mem_univ _, hxunit.unit_spec⟩
    · intro u hu
      rfl
  rw [hunits]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x hxuniv hxnot
  have hxnonunit : ¬IsUnit x := by simpa [s] using hxnot
  rw [MulChar.map_nonunit chi hxnonunit, zero_mul]

open Finset

private theorem row_parseval (N : ℕ) [NeZero N] (F : (ZMod N)ˣ → ℂ) :
    let T := fun (W : (ZMod N)ˣ → ℂ) (χ : DirichletCharacter ℂ N) => ∑ a, W a * χ (a : ZMod N)
    ∑ χ, ‖T F χ‖^2 = (N.totient:ℝ)*∑ a, ‖F a‖^2 := by
  classical
  intro T
  have orth (a b : (ZMod N)ˣ) :
      (∑ χ : DirichletCharacter ℂ N, star (χ (a:ZMod N))*χ (b:ZMod N)) =
      if a=b then (N.totient:ℂ) else 0 := by
    have hca (χ : DirichletCharacter ℂ N) : star (χ (a:ZMod N)) = χ ((a:ZMod N)⁻¹) := by
      rw [MulChar.star_apply',MulChar.inv_apply,Ring.inverse_unit,ZMod.inv_coe_unit]
    simp_rw [hca]
    simpa only [Units.val_inj] using DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit (b:ZMod N)
  have parseval (W : (ZMod N)ˣ → ℂ) :
      ∑ χ : DirichletCharacter ℂ N, star (T F χ) * T W χ =
        (N.totient:ℂ)*∑ a, star (F a)*W a := by
    let k (χ : DirichletCharacter ℂ N) (a b : (ZMod N)ˣ) :=
      (star (F a)*W b) * (star (χ (a:ZMod N))*χ (b:ZMod N))
    have hex (χ : DirichletCharacter ℂ N) : star (T F χ)*T W χ = ∑ a,∑ b,k χ a b := by
      dsimp only [T,k]; rw [star_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum, star_mul]
      apply Finset.sum_congr rfl; intro b _; ring
    simp_rw [hex]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_comm]; dsimp only [k]
    simp_rw [← Finset.mul_sum,orth]
    simp [Finset.sum_ite_eq, mul_comm]
  have hs := parseval F
  have hnorm (z : ℂ) : star z * z = ((‖z‖^2:ℝ):ℂ) := by
    rw [Complex.star_def, Complex.conj_mul',Complex.ofReal_pow]
  simp_rw [hnorm] at hs
  exact_mod_cast hs

theorem Conjectures.Cuts.Task20f2602ec4088c9db5dcb4ab : (∀ (x1 x2 x3 : ℕ) [x4 : NeZero (x1 ^ x2)],   Nat.Prime x1 →     (0 : ℕ) < x2 →       Even x3 →         x1 ∣ x3 →           ∀ (x9 : DirichletCharacter ℂ (x1 ^ x2)) (x10 : Finset (DirichletCharacter ℂ (x1 ^ x2))),             have x11 : DirichletCharacter ℂ (x1 ^ x2) → DirichletCharacter ℂ (x1 ^ x2) → ℂ := fun (x11 x12 : DirichletCharacter ℂ (x1 ^ x2)) => ∑ x13 : ZMod (x1 ^ x2), x11 x13 * x12 (↑x3 - x13);             ∑ x12 ∈ x10, ‖x11 x9 x12 / x11 (1 : DirichletCharacter ℂ (x1 ^ x2)) (1 : DirichletCharacter ℂ (x1 ^ x2))‖ ^ (3 : ℕ) ≤ (1 : ℝ)) := by
  classical
  intro p k m _ hp hk he hm α F J
  let q := p^k
  have nil : IsNilpotent (m : ZMod q) := by
    refine ⟨k, ?_⟩
    rw [←Nat.cast_pow,ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow_of_dvd hm k
  have unit (u : (ZMod q)ˣ) : IsUnit ((m : ZMod q) - u) := by
    rw [sub_eq_add_neg, add_comm]
    exact nil.isUnit_add_left_of_commute u.isUnit.neg (Commute.all _ _)
  have repr (a b : DirichletCharacter ℂ q) :
      J a b = ∑ u : (ZMod q)ˣ, a ((m:ZMod q)-u) * b (u:ZMod q) := by
    let e := Equiv.subLeft (m:ZMod q)
    have h := e.sum_comp (fun x => b x * a ((m:ZMod q)-x))
    calc
      _ = ∑ x : ZMod q, b x * a ((m:ZMod q)-x) := by
        convert h using 1
        apply sum_congr rfl
        intro x _
        simp [e, mul_comm]
      _ = _ := by rw [←units_to_residues]; apply sum_congr rfl; intro u _; ring
  have den : J 1 1 = (q.totient:ℂ) := by
    rw [repr]
    simp only [MulChar.one_apply (unit _),MulChar.one_apply_coe,one_mul,sum_const,card_univ,
      nsmul_eq_mul,mul_one,ZMod.card_units_eq_totient]
  have sqtotal : ∑ b : DirichletCharacter ℂ q, ‖J α b‖^2 = (q.totient:ℝ)^2 := by
    simp_rw [repr]
    rw [row_parseval q (fun u => α ((m:ZMod q)-u))]
    have hn (u : (ZMod q)ˣ) : ‖α ((m:ZMod q)-u)‖ = 1 := α.unit_norm_eq_one (unit u).unit
    simp [hn,ZMod.card_units_eq_totient,pow_two]
  have hpos : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (pow_pos hp.pos k)
  have normal : ∑ b : DirichletCharacter ℂ q, ‖J α b / J 1 1‖^2 = 1 := by
    simp only [den,norm_div,Complex.norm_natCast, div_pow,←sum_div,sqtotal]
    exact div_self (by positivity)
  have single (b : DirichletCharacter ℂ q) : ‖J α b / J 1 1‖ ≤ 1 := by
    have h := single_le_sum (f:=fun b => ‖J α b / J 1 1‖^2) (fun _ _ => sq_nonneg _) (mem_univ b)
    rw [normal] at h
    nlinarith [norm_nonneg (J α b / J 1 1)]
  calc
    _ ≤ ∑ b ∈ F, ‖J α b / J 1 1‖^2 := by
      apply sum_le_sum
      intro b _
      rw [pow_succ]
      exact mul_le_of_le_one_right (sq_nonneg _) (single b)
    _ ≤ _ := (sum_le_sum_of_subset_of_nonneg (subset_univ F) (fun _ _ _ => sq_nonneg _)).trans normal.le
