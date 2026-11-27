import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_hensel_root_unique :
    ∀ p k r : ℕ, Nat.Prime p → p≠2 → 0<k → p^k ∣ r^2+1 → ∃! t : Fin p, p^(k+1) ∣ (r+t.val*p^k)^2+1 := by
  intro p k r hp hp2 hk hd
  haveI : Fact p.Prime := ⟨hp⟩
  have hpk_pos : 0 < p^k := pow_pos hp.pos k
  have hzpk : p ∣ p^k := by
    have h := pow_dvd_pow p (show 1 ≤ k by omega)
    simpa using h
  set c := (r^2+1)/p^k with hcdef
  have hc : p^k * c = r^2+1 := by
    rw [hcdef, Nat.mul_comm]
    exact Nat.div_mul_cancel hd
  have hX : ∀ s : ℕ, (r + s*p^k)^2+1 = p^k * (c + 2*s*r + s^2*p^k) := by
    intro s
    have expand : p^k * (c + 2*s*r + s^2*p^k) = p^k*c + 2*(s*r)*p^k + (s*p^k)^2 := by ring
    rw [expand, hc]
    ring
  have hiff : ∀ s : ℕ, p^(k+1) ∣ (r+s*p^k)^2+1 ↔
      ((c:ZMod p) + 2*(s:ZMod p)*(r:ZMod p) = 0) := by
    intro s
    rw [pow_succ, hX s, Nat.mul_dvd_mul_iff_left hpk_pos]
    rw [← Nat.dvd_add_iff_left (show p ∣ s^2 * p^k from dvd_mul_of_dvd_right hzpk (s^2))]
    rw [← CharP.cast_eq_zero_iff (ZMod p) p (c + 2*s*r)]
    push_cast
    ring_nf
  have hpr : p ∣ r^2+1 := dvd_trans hzpk hd
  have hr2z : (r:ZMod p)^2 + 1 = 0 := by
    have h : ((r^2+1 : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p (r^2+1)).mpr hpr
    push_cast at h
    simpa using h
  have hr_ne : (r:ZMod p) ≠ 0 := by
    intro h0
    rw [h0] at hr2z
    have h1 : (1:ZMod p) = 0 := by simpa using hr2z
    exact one_ne_zero h1
  have h2_ne : (2:ZMod p) ≠ 0 := by
    intro h0
    have hp2d : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h0
    rcases Nat.prime_two.eq_one_or_self_of_dvd p hp2d with h1 | h1
    · exact hp.ne_one h1
    · exact hp2 h1
  have h2r_ne : (2:ZMod p)*(r:ZMod p) ≠ 0 := mul_ne_zero h2_ne hr_ne
  set w : ZMod p := (2:ZMod p)*(r:ZMod p) with hwdef
  have hw_ne : w ≠ 0 := by rw [hwdef]; exact h2r_ne
  set u : ZMod p := -(c:ZMod p) * w⁻¹ with hudef
  have hwu : w * u = -(c:ZMod p) := by
    rw [hudef]
    have hstep : w * (-(c:ZMod p) * w⁻¹) = -((c:ZMod p) * (w * w⁻¹)) := by ring
    rw [hstep, mul_inv_cancel₀ hw_ne, mul_one]
  have hu_eq : (c:ZMod p) + 2*(u)*(r:ZMod p) = 0 := by
    have h2uw : (2:ZMod p)*u*(r:ZMod p) = w*u := by rw [hwdef]; ring
    rw [h2uw, hwu]; ring
  refine ⟨⟨u.val, ZMod.val_lt u⟩, ?_, ?_⟩
  · change p^(k+1) ∣ (r + u.val*p^k)^2+1
    rw [hiff u.val, ZMod.natCast_zmod_val u]
    exact hu_eq
  · intro t ht
    have ht' : (c:ZMod p) + 2*(t.val:ZMod p)*(r:ZMod p) = 0 := by
      rw [hiff t.val] at ht
      exact ht
    have hdiff : (2:ZMod p)*(r:ZMod p)*((t.val:ZMod p) - u) = 0 := by
      linear_combination ht' - hu_eq
    have hz : (t.val:ZMod p) - u = 0 := by
      rcases mul_eq_zero.mp hdiff with h | h
      · exact absurd h h2r_ne
      · exact h
    have hval : (t.val:ZMod p) = u := sub_eq_zero.mp hz
    have hval' : t.val = u.val := by
      have h := congrArg ZMod.val hval
      rw [ZMod.val_natCast] at h
      rw [Nat.mod_eq_of_lt t.isLt] at h
      exact h
    exact Fin.ext hval'
