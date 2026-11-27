import Mathlib

namespace SplitRec

abbrev Pt := ℤ × ℤ

def N (x : Pt) : ℤ := x.1 ^ 2 + x.1 * x.2 + x.2 ^ 2

def emul (x y : Pt) : Pt :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1 + x.2 * y.2)

def econ (x : Pt) : Pt := (x.1 + x.2, -x.2)

/-- rotation by 60 degrees: multiplication by the unit 1 + w -/
def ezeta (x : Pt) : Pt := (x.1 + x.2, -x.1)

def eneg (x : Pt) : Pt := (-x.1, -x.2)

def esec (x : Pt) : Prop := 0 < x.1 ∧ x.2 < x.1 ∧ 0 < x.1 + 2 * x.2

lemma N_four (x : Pt) : 4 * N x = (2 * x.1 + x.2) ^ 2 + 3 * x.2 ^ 2 := by
  simp only [N]; ring

lemma N_emul (x y : Pt) : N (emul x y) = N x * N y := by
  obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
  simp only [emul, N]; ring

lemma emul_assoc (x y z : Pt) : emul (emul x y) z = emul x (emul y z) := by
  obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y; obtain ⟨e, f⟩ := z
  simp only [emul, Prod.mk.injEq]; constructor <;> ring

lemma emul_comm (x y : Pt) : emul x y = emul y x := by
  obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
  simp only [emul, Prod.mk.injEq]; constructor <;> ring

lemma emul_con (x : Pt) : emul x (econ x) = (N x, 0) := by
  obtain ⟨a, c⟩ := x; simp only [emul, econ, N, Prod.mk.injEq]
  exact ⟨by ring, by ring⟩

lemma econ_emul (x y : Pt) : econ (emul x y) = emul (econ x) (econ y) := by
  obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
  simp only [emul, econ, Prod.mk.injEq]; constructor <;> ring

lemma econ_econ (x : Pt) : econ (econ x) = x := by
  obtain ⟨a, c⟩ := x; simp [econ]

lemma emul_smul (k : ℤ) (x : Pt) : emul (k, 0) x = (k * x.1, k * x.2) := by
  obtain ⟨a, c⟩ := x; simp [emul]

lemma N_nonneg (x : Pt) : 0 ≤ N x := by
  have h := N_four x
  nlinarith [sq_nonneg (2 * x.1 + x.2), sq_nonneg x.2]

lemma N_eq_zero (x : Pt) : N x = 0 → x = 0 := by
  intro h
  have h4 := N_four x
  rw [h] at h4
  have hx2 : x.2 = 0 := by nlinarith [sq_nonneg (2 * x.1 + x.2), sq_nonneg x.2]
  have hx1 : x.1 = 0 := by
    simp only [N] at h; rw [hx2] at h; nlinarith
  exact Prod.ext hx1 hx2

lemma N_pos {x : Pt} : 0 < N x ↔ x ≠ 0 := by
  constructor
  · intro h h0; rw [h0] at h; simp [N] at h
  · intro h
    rcases lt_trichotomy (N x) 0 with h' | h' | h'
    · exact absurd h' (not_lt.mpr (N_nonneg x))
    · exact absurd (N_eq_zero x h') h
    · exact h'

lemma emul_eq_zero {x y : Pt} (h : emul x y = 0) : x = 0 ∨ y = 0 := by
  have hN : N (emul x y) = 0 := by rw [h]; simp [N]
  rw [N_emul] at hN
  rcases mul_eq_zero.mp hN with h' | h'
  · exact Or.inl (N_eq_zero x h')
  · exact Or.inr (N_eq_zero y h')

lemma emul_cancel_right {x y z : Pt} (h : emul x z = emul y z) (hz : z ≠ 0) : x = y := by
  have hNz : N z ≠ 0 := fun h0 => hz (N_eq_zero z h0)
  have h1 : x.1 * z.1 - x.2 * z.2 = y.1 * z.1 - y.2 * z.2 := by
    simpa [emul] using congrArg Prod.fst h
  have h2 : x.1 * z.2 + x.2 * z.1 + x.2 * z.2 = y.1 * z.2 + y.2 * z.1 + y.2 * z.2 := by
    simpa [emul] using congrArg Prod.snd h
  have key1 : (x.1 - y.1) * N z = 0 := by
    simp only [N]; linear_combination (z.1 + z.2) * h1 + z.2 * h2
  have key2 : (x.2 - y.2) * N z = 0 := by
    simp only [N]; linear_combination z.1 * h2 - z.2 * h1
  have e1 : x.1 = y.1 := by
    rcases mul_eq_zero.mp key1 with h' | h'
    · omega
    · exact absurd h' hNz
  have e2 : x.2 = y.2 := by
    rcases mul_eq_zero.mp key2 with h' | h'
    · omega
    · exact absurd h' hNz
  exact Prod.ext e1 e2

lemma N_ezeta (x : Pt) : N (ezeta x) = N x := by
  obtain ⟨a, c⟩ := x; simp only [ezeta, N]; ring

lemma ezeta_six (x : Pt) : ezeta^[6] x = x := by
  obtain ⟨a, c⟩ := x
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, ezeta,
    Prod.mk.injEq]
  constructor <;> ring

lemma ezeta_inj : Function.Injective ezeta := by
  intro x y h
  have key : ∀ z : Pt, ezeta^[5] (ezeta z) = z := by
    intro z
    have h6 := ezeta_six z
    rw [show (6:ℕ) = 5 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one] at h6
    exact h6
  calc x = ezeta^[5] (ezeta x) := (key x).symm
    _ = ezeta^[5] (ezeta y) := by rw [h]
    _ = y := key y

end SplitRec

namespace SplitRec

lemma ne_of_sq (x : Pt) (h : ∀ t : ℤ, N x ≠ t ^ 2) :
    x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ x.1 + x.2 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0; exact h x.2 (by simp only [N]; rw [h0]; ring)
  · intro h0; exact h x.1 (by simp only [N]; rw [h0]; ring)
  · intro h0; exact h x.1 (by simp only [N]; rw [show x.2 = -x.1 by linarith]; ring)

lemma ne_of_three (x : Pt) (h : ¬ (3:ℤ) ∣ N x) :
    x.1 ≠ x.2 ∧ x.1 + 2 * x.2 ≠ 0 ∧ 2 * x.1 + x.2 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0; exact h ⟨x.1 ^ 2, by simp only [N]; rw [h0]; ring⟩
  · intro h0; exact h ⟨x.2 ^ 2, by simp only [N]; rw [show x.1 = -2 * x.2 by linarith]; ring⟩
  · intro h0; exact h ⟨x.1 ^ 2, by simp only [N]; rw [show x.2 = -2 * x.1 by linarith]; ring⟩

/-- one of the six rotations lies in the open sector -/
lemma esec_orb_ex (x : Pt) (h3 : ¬ (3:ℤ) ∣ N x) (hsq : ∀ t : ℤ, N x ≠ t ^ 2) :
    esec x ∨ esec (ezeta x) ∨ esec (ezeta (ezeta x)) ∨ esec (ezeta^[3] x) ∨
      esec (ezeta^[4] x) ∨ esec (ezeta^[5] x) := by
  obtain ⟨h1, h2, h3'⟩ := ne_of_sq x hsq
  obtain ⟨h4, h5, h6⟩ := ne_of_three x h3
  simp only [esec, ezeta, Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
  omega

/-- no nonzero rotation by 1..5 of a sector point is again in the sector -/
lemma esec_orb_not (y : Pt) (hy : esec y) :
    ¬ esec (ezeta y) ∧ ¬ esec (ezeta (ezeta y)) ∧ ¬ esec (ezeta^[3] y) ∧
      ¬ esec (ezeta^[4] y) ∧ ¬ esec (ezeta^[5] y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [esec, ezeta, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
        id_eq] at hy ⊢
      omega

lemma esec_orb_not_d (y : Pt) (hy : esec y) {d : ℕ} (h1 : 1 ≤ d) (h5 : d ≤ 5) :
    ¬ esec (ezeta^[d] y) := by
  have hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
  have hrot := esec_orb_not y hy
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · simpa using hrot.1
  · simpa using hrot.2.1
  · simpa using hrot.2.2.1
  · simpa using hrot.2.2.2.1
  · simpa using hrot.2.2.2.2

lemma ezeta_fix {b : Pt} (hb : b ≠ 0) {d : ℕ} (hd : d < 6) (h : ezeta^[d] b = b) : d = 0 := by
  obtain ⟨a, c⟩ := b
  have ha : a ≠ 0 ∨ c ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hb (by rw [hh.1, hh.2]; rfl)
  have hd' : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
  rcases hd' with h0 | h0 | h0 | h0 | h0 | h0
  · exact h0
  all_goals
    exfalso
    rw [h0] at h
    simp only [esec, ezeta, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
      id_eq, Prod.mk.injEq] at h
    omega

end SplitRec

namespace SplitRec

lemma two_dvd_N {a b : ℤ} (h : (2:ℤ) ∣ N (a, b)) : (2:ℤ) ∣ a ∧ (2:ℤ) ∣ b := by
  have key : ∀ u v : ZMod 2, u ^ 2 + u * v + v ^ 2 = 0 → u = 0 ∧ v = 0 := by decide
  have h2 : ((N (a, b) : ℤ) : ZMod 2) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h
  simp only [N] at h2
  push_cast at h2
  have hk := key (a : ZMod 2) (b : ZMod 2) h2
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mp hk.1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd b 2).mp hk.2⟩

lemma four_dvd_N {a b : ℤ} (ha : (2:ℤ) ∣ a) (hb : (2:ℤ) ∣ b) : (4:ℤ) ∣ N (a, b) := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  exact ⟨a' ^ 2 + a' * b' + b' ^ 2, by simp only [N]; ring⟩

/-- existence of a cube root of unity in ZMod p for p = 1 mod 3 -/
lemma exists_root (p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 1) :
    ∃ t : ZMod p, t ^ 2 + t + 1 = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rwa [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ← Nat.prime_iff_card_units]
  have hp1 : 0 < p - 1 := by have := hp.one_lt; omega
  have h3dvd : 3 ∣ p - 1 := by omega
  set a : ZMod p := ((g : (ZMod p)ˣ) : ZMod p) with ha_def
  have hordA : orderOf a = p - 1 := by
    rw [ha_def]
    simpa [hord] using orderOf_injective (Units.coeHom (ZMod p)) Units.val_injective g
  refine ⟨a ^ ((p - 1) / 3), ?_⟩
  have hu3 : (a ^ ((p - 1) / 3)) ^ 3 = 1 := by
    have hmul : ((p - 1) / 3) * 3 = p - 1 := by
      have h := Nat.mul_div_cancel' h3dvd
      omega
    rw [← pow_mul, hmul, ← hordA]
    exact pow_orderOf_eq_one a
  have hu1 : a ^ ((p - 1) / 3) ≠ 1 := by
    intro h
    have hd : orderOf a ∣ (p - 1) / 3 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hordA] at hd
    have hpos : 0 < (p - 1) / 3 := Nat.div_pos (by omega) (by norm_num)
    have := Nat.le_of_dvd hpos hd
    omega
  have hfac : (a ^ ((p - 1) / 3) - 1) * ((a ^ ((p - 1) / 3)) ^ 2 + a ^ ((p - 1) / 3) + 1) = 0 := by
    have h3 : (a ^ ((p - 1) / 3)) ^ 3 = 1 := hu3
    linear_combination h3
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linear_combination h) hu1
  · linear_combination h

end SplitRec

namespace SplitRec

/-- every prime `p = 1 mod 3` is a norm: `p = a^2 + a b + b^2` (Thue pigeonhole) -/
lemma prime_rep (p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 1) :
    ∃ a b : ℤ, N (a, b) = (p : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := exists_root p hp hp3
  set A : ℕ := Nat.sqrt p with hA
  have hAle : (A : ℤ) * (A : ℤ) ≤ (p : ℤ) := by
    have h := Nat.sqrt_le' p
    rw [hA] at ⊢
    have h' : (Nat.sqrt p : ℤ) ^ 2 ≤ (p : ℤ) := by exact_mod_cast h
    simpa [pow_two] using h'
  have hAlt : (p : ℤ) < ((A : ℤ) + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt' p
    rw [hA] at ⊢
    push_cast
    exact_mod_cast h
  have hcard : Fintype.card (ZMod p) < Fintype.card (Fin (A + 1) × Fin (A + 1)) := by
    have hz : Fintype.card (ZMod p) = p := by rw [← Nat.card_eq_fintype_card, Nat.card_zmod]
    rw [hz, Fintype.card_prod, Fintype.card_fin]
    push_cast
    nlinarith
  obtain ⟨u, v, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun q : Fin (A + 1) × Fin (A + 1) =>
      ((q.1 : ℕ) : ZMod p) - ((q.2 : ℕ) : ZMod p) * t) hcard
  set a : ℤ := (u.1 : ℤ) - (v.1 : ℤ) with ha
  set b : ℤ := (u.2 : ℤ) - (v.2 : ℤ) with hb
  have hne0 : (a, b) ≠ 0 := by
    intro h0
    apply hne
    have h1 : (u.1 : ℤ) = (v.1 : ℤ) := by
      have hh : a = 0 := by simpa using congrArg Prod.fst h0
      rw [ha] at hh; omega
    have h2 : (u.2 : ℤ) = (v.2 : ℤ) := by
      have hh : b = 0 := by simpa using congrArg Prod.snd h0
      rw [hb] at hh; omega
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  have hphi : (((a : ℤ)) : ZMod p) - (((b : ℤ)) : ZMod p) * t = 0 := by
    have h1 : (((u.1 : ℕ) : ZMod p) - ((u.2 : ℕ) : ZMod p) * t)
        = (((v.1 : ℕ) : ZMod p) - ((v.2 : ℕ) : ZMod p) * t) := heq
    have h2 : (((u.1 : ℕ) : ZMod p) - ((u.2 : ℕ) : ZMod p) * t)
        - (((v.1 : ℕ) : ZMod p) - ((v.2 : ℕ) : ZMod p) * t)
        = (((a : ℤ)) : ZMod p) - (((b : ℤ)) : ZMod p) * t := by
      simp only [ha, hb]; push_cast; ring
    rw [h1, sub_self] at h2
    exact h2.symm
  have hpdvd : (p : ℤ) ∣ N (a, b) := by
    have hN0 : ((N (a, b) : ℤ) : ZMod p) = 0 := by
      have ha' : (((a : ℤ)) : ZMod p) = (((b : ℤ)) : ZMod p) * t := by linear_combination hphi
      simp only [N]
      push_cast
      rw [ha']
      linear_combination ((((b : ℤ)) : ZMod p)) ^ 2 * ht
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (N (a, b)) p).mp hN0
  have hu1 : (u.1 : ℤ) < (A : ℤ) + 1 := by
    have h := u.1.isLt; exact_mod_cast h
  have hv1 : (v.1 : ℤ) < (A : ℤ) + 1 := by
    have h := v.1.isLt; exact_mod_cast h
  have hu2 : (u.2 : ℤ) < (A : ℤ) + 1 := by
    have h := u.2.isLt; exact_mod_cast h
  have hv2 : (v.2 : ℤ) < (A : ℤ) + 1 := by
    have h := v.2.isLt; exact_mod_cast h
  have hlo1 : (0:ℤ) ≤ (u.1 : ℤ) := Int.natCast_nonneg _
  have hlo2 : (0:ℤ) ≤ (v.1 : ℤ) := Int.natCast_nonneg _
  have hlo3 : (0:ℤ) ≤ (u.2 : ℤ) := Int.natCast_nonneg _
  have hlo4 : (0:ℤ) ≤ (v.2 : ℤ) := Int.natCast_nonneg _
  have hb1 : -((A:ℤ)) ≤ a := by rw [ha]; omega
  have hb2 : a ≤ ((A:ℤ)) := by rw [ha]; omega
  have hb3 : -((A:ℤ)) ≤ b := by rw [hb]; omega
  have hb4 : b ≤ ((A:ℤ)) := by rw [hb]; omega
  have e1 : 0 ≤ ((A:ℤ) - a) * ((A:ℤ) + a) := mul_nonneg (by linarith) (by linarith)
  have e2 : 0 ≤ ((A:ℤ) - b) * ((A:ℤ) + b) := mul_nonneg (by linarith) (by linarith)
  have e3 : 0 ≤ ((A:ℤ) - a) * ((A:ℤ) + b) := mul_nonneg (by linarith) (by linarith)
  have e4 : 0 ≤ ((A:ℤ) + a) * ((A:ℤ) - b) := mul_nonneg (by linarith) (by linarith)
  have hle3 : N (a, b) ≤ 3 * (A:ℤ)^2 := by simp only [N]; nlinarith
  have hA2 : 3 * (A:ℤ)^2 ≤ 3 * (p:ℤ) := by nlinarith
  have hsq_ne : (A:ℤ) * (A:ℤ) ≠ (p:ℤ) := by
    intro h
    have h1 : A * A = p := by exact_mod_cast h
    have hdvd : A ∣ p := ⟨A, h1.symm⟩
    have hsplit : A = 1 ∨ A = p := (Nat.dvd_prime hp).mp hdvd
    have hp2le : 2 ≤ p := hp.two_le
    rcases hsplit with h2 | h2
    · rw [h2] at h1
      have hp1 : p = 1 := by rw [← h1]
      omega
    · rw [h2] at h1; nlinarith
  have hA3 : 3 * (A:ℤ)^2 < 3 * (p:ℤ) := by
    rcases lt_or_eq_of_le hA2 with h | h
    · exact h
    · exfalso; apply hsq_ne; linarith
  have hlt : N (a, b) < 3 * (p:ℤ) := by linarith
  have hpos : 0 < N (a, b) := by rw [N_pos]; exact hne0
  have hp0 : (0:ℤ) < (p:ℤ) := by exact_mod_cast hp.pos
  obtain ⟨k, hk⟩ := hpdvd
  have hkpos : 0 < k := by
    apply pos_of_mul_pos_right _ (le_of_lt hp0)
    rw [← hk]; exact hpos
  have hklt : k < 3 := by
    apply lt_of_mul_lt_mul_left _ (le_of_lt hp0)
    rw [← hk]; linarith [hlt]
  have hk12 : k = 1 ∨ k = 2 := by omega
  rcases hk12 with h | h
  · exact ⟨a, b, by rw [hk, h]; ring⟩
  · exfalso
    have hN2 : N (a, b) = 2 * (p:ℤ) := by rw [hk, h]; ring
    have h2dvd : (2:ℤ) ∣ N (a, b) := by rw [hN2]; exact ⟨(p:ℤ), rfl⟩
    obtain ⟨ha2, hb2'⟩ := two_dvd_N h2dvd
    have h4d : (4:ℤ) ∣ N (a, b) := four_dvd_N ha2 hb2'
    rw [hN2] at h4d
    have hp2 : (2:ℤ) ∣ (p:ℤ) := by
      obtain ⟨m, hm⟩ := h4d
      exact ⟨m, by omega⟩
    have hpne2 : p ≠ 2 := by omega
    have hodd : Odd p := hp.odd_of_ne_two hpne2
    obtain ⟨d, hd⟩ := hodd
    obtain ⟨c, hc⟩ := hp2
    have hd' : (p:ℤ) = 2 * (d:ℤ) + 1 := by exact_mod_cast hd
    omega

end SplitRec

namespace SplitRec

def phi (p : ℕ) (t : ZMod p) (x : Pt) : ZMod p := (x.1 : ZMod p) - (x.2 : ZMod p) * t

lemma phi_emul (p : ℕ) (t : ZMod p) (ht : t ^ 2 + t + 1 = 0) (x y : Pt) :
    phi p t (emul x y) = phi p t x * phi p t y := by
  simp only [phi, emul]
  push_cast
  linear_combination (-(x.2 : ZMod p) * (y.2 : ZMod p)) * ht

lemma phi_norm (p : ℕ) (t : ZMod p) (ht : t ^ 2 + t + 1 = 0) (x : Pt) :
    phi p t x * phi p t (econ x) = ((N x : ℤ) : ZMod p) := by
  rw [← phi_emul p t ht, emul_con]
  simp [phi]

lemma phi_linear (p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 1) {t : ZMod p}
    (ht : t ^ 2 + t + 1 = 0) {x : Pt} (h1 : phi p t x = 0) (h2 : phi p t (econ x) = 0) :
    (x.1 : ZMod p) = 0 ∧ (x.2 : ZMod p) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h3ne : (3 : ZMod p) ≠ 0 := by
    intro hc
    have hc' : ((3 : ℤ) : ZMod p) = 0 := by simpa using hc
    have hdvdz : (p : ℤ) ∣ (3 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (3 : ℤ) p).mp hc'
    have hdvd : p ∣ 3 := by exact_mod_cast hdvdz
    have hp2 : 2 ≤ p := hp.two_le
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · omega
    · omega
  have hne : (1 + 2 * t : ZMod p) ≠ 0 := by
    intro h0
    have hsq : (1 + 2 * t) ^ 2 = (-3 : ZMod p) := by linear_combination 4 * ht
    rw [h0] at hsq
    have h3 : (3 : ZMod p) = 0 := by linear_combination hsq
    exact h3ne h3
  have hx2 : (x.2 : ZMod p) = 0 := by
    have hkey : (1 + 2 * t) * (x.2 : ZMod p) = 0 := by
      simp only [phi, econ] at h1 h2
      push_cast at h1 h2
      linear_combination h2 - h1
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h hne
    · exact h
  have hx1 : (x.1 : ZMod p) = 0 := by
    simp only [phi] at h1
    rw [hx2] at h1
    simpa using h1
  exact ⟨hx1, hx2⟩

/-- both evaluations vanishing forces divisibility by p -/
lemma p_dvd_of_phi (p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 1) {t : ZMod p}
    (ht : t ^ 2 + t + 1 = 0) {x : Pt} (h1 : phi p t x = 0) (h2 : phi p t (econ x) = 0) :
    (p : ℤ) ∣ x.1 ∧ (p : ℤ) ∣ x.2 := by
  obtain ⟨e1, e2⟩ := phi_linear p hp hp3 ht h1 h2
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd x.1 p).mp e1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd x.2 p).mp e2⟩

end SplitRec

namespace SplitRec

lemma N_econ (x : Pt) : N (econ x) = N x := by
  obtain ⟨a, c⟩ := x; simp only [econ, N]; ring

lemma N_eneg (x : Pt) : N (eneg x) = N x := by
  obtain ⟨a, c⟩ := x; simp only [eneg, N]; ring

lemma ezeta_three (x : Pt) : ezeta^[3] x = eneg x := by
  obtain ⟨a, c⟩ := x
  simp only [ezeta, eneg, Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
    Prod.mk.injEq]
  constructor <;> ring

lemma eneg_ezeta (x : Pt) : eneg (ezeta x) = ezeta (eneg x) := by
  obtain ⟨a, c⟩ := x
  simp only [ezeta, eneg]
  exact Prod.ext (by ring) (by ring)

lemma eneg_ezeta_iter (d : ℕ) (x : Pt) : ezeta^[d] (eneg x) = eneg (ezeta^[d] x) := by
  induction d with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, eneg_ezeta]

lemma N_ezeta_iter (d : ℕ) (x : Pt) : N (ezeta^[d] x) = N x := by
  induction d with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', N_ezeta, ih]

lemma ezeta_iterate_six_mul (n m : ℕ) (x : Pt) : ezeta^[m + 6 * n] x = ezeta^[m] x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, Function.iterate_add_apply, ezeta_six, ih]

lemma ezeta_iterate_mod (m : ℕ) (x : Pt) : ezeta^[m] x = ezeta^[m % 6] x := by
  rw [show ezeta^[m] x = ezeta^[m % 6 + 6 * (m / 6)] x from by rw [Nat.mod_add_div]]
  exact ezeta_iterate_six_mul (m / 6) (m % 6) x

lemma abs_bounds (S : ℤ) (hS : 1 ≤ S) (x : Pt) (h : N x = S) :
    |x.1| ≤ 2 * S ∧ |x.2| ≤ 2 * S ∧ |x.1 + x.2| ≤ 2 * S := by
  have hx := h
  simp only [N] at hx
  have h1 : x.1 ^ 2 + x.2 ^ 2 ≤ 2 * S := by nlinarith [sq_nonneg (x.1 + x.2)]
  have h2 : (x.1 + x.2) ^ 2 ≤ 2 * S := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have hxx : x.1 ^ 2 ≤ 2 * S := by nlinarith [h1, sq_nonneg x.2]
  have hyy : x.2 ^ 2 ≤ 2 * S := by nlinarith [h1, sq_nonneg x.1]
  have hS0 : (0:ℤ) ≤ S := by omega
  have hbig : (2:ℤ) * S ≤ (2*S) * (2*S) := by nlinarith
  have key : ∀ a : ℤ, a ^ 2 ≤ 2 * S → |a| ≤ 2 * S := by
    intro a ha
    have h2a : a ^ 2 ≤ (2*S) ^ 2 := by nlinarith
    have hsq := (sq_le_sq).mp h2a
    rwa [abs_of_nonneg (by omega : (0:ℤ) ≤ 2*S)] at hsq
  exact ⟨key x.1 hxx, key x.2 hyy, key (x.1 + x.2) h2⟩

end SplitRec

namespace SplitRec

/-- the closed sector used by the statement -/
def psec (x : Pt) : Prop := x.1 ≤ x.2 ∧ x.1 + 2 * x.2 ≤ 0 ∧ x.1 + x.2 ≤ 0

instance psecDecidable : DecidablePred psec := fun x => by unfold psec; infer_instance

lemma psec_iff_esec (x : Pt) (h3 : ¬ (3:ℤ) ∣ N x) (hsq : ∀ t : ℤ, N x ≠ t ^ 2) :
    psec x ↔ esec (eneg x) := by
  obtain ⟨h1, h2, h3'⟩ := ne_of_sq x hsq
  obtain ⟨h4, h5, h6⟩ := ne_of_three x h3
  simp only [psec, esec, eneg]
  omega

lemma psec_of_esec_iter {x : Pt} (k : ℕ) (h3 : ¬ (3:ℤ) ∣ N x) (hsq : ∀ t : ℤ, N x ≠ t ^ 2)
    (h : esec (ezeta^[k] (eneg x))) : psec (ezeta^[k] x) := by
  refine (psec_iff_esec (ezeta^[k] x) ?_ ?_).mpr ?_
  · rwa [N_ezeta_iter]
  · rw [N_ezeta_iter]; exact hsq
  · rwa [← eneg_ezeta_iter]

lemma psec_orb_exists (x : Pt) (h3 : ¬ (3:ℤ) ∣ N x) (hsq : ∀ t : ℤ, N x ≠ t ^ 2) :
    ∃ k : ℕ, k < 6 ∧ psec (ezeta^[k] x) := by
  have h3' : ¬ (3:ℤ) ∣ N (eneg x) := by rwa [N_eneg]
  have hsq' : ∀ t : ℤ, N (eneg x) ≠ t ^ 2 := by rw [N_eneg]; exact hsq
  have h := esec_orb_ex (eneg x) h3' hsq'
  rcases h with h | h | h | h | h | h
  · exact ⟨0, by norm_num, by simpa using psec_of_esec_iter 0 h3 hsq h⟩
  · exact ⟨1, by norm_num, by simpa [Function.iterate_one] using psec_of_esec_iter 1 h3 hsq h⟩
  · exact ⟨2, by norm_num, by simpa using psec_of_esec_iter 2 h3 hsq h⟩
  · exact ⟨3, by norm_num, by simpa using psec_of_esec_iter 3 h3 hsq h⟩
  · exact ⟨4, by norm_num, by simpa using psec_of_esec_iter 4 h3 hsq h⟩
  · exact ⟨5, by norm_num, by simpa using psec_of_esec_iter 5 h3 hsq h⟩

lemma psec_orb_not_d (y : Pt) (hy : psec y) (h3 : ¬ (3:ℤ) ∣ N y) (hsq : ∀ t : ℤ, N y ≠ t ^ 2)
    {d : ℕ} (h1 : 1 ≤ d) (h5 : d ≤ 5) : ¬ psec (ezeta^[d] y) := by
  intro hcon
  have e1 : esec (eneg y) := (psec_iff_esec y h3 hsq).mp hy
  have e2 : esec (eneg (ezeta^[d] y)) :=
    (psec_iff_esec (ezeta^[d] y) (by rwa [N_ezeta_iter])
      (by rw [N_ezeta_iter]; exact hsq)).mp hcon
  rw [← eneg_ezeta_iter] at e2
  exact esec_orb_not_d (eneg y) e1 h1 h5 e2

lemma psec_ezeta_six (y : Pt) (hy : psec y) (h3 : ¬ (3:ℤ) ∣ N y) (hsq : ∀ t : ℤ, N y ≠ t ^ 2)
    {d : ℕ} (hd : d < 6) : psec (ezeta^[d] y) → d = 0 := by
  intro h
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · exact h0
  · exact absurd h (psec_orb_not_d y hy h3 hsq h0 (by omega))

end SplitRec

namespace SplitRec

def box (S : ℤ) : Finset Pt := (Finset.Icc (-(2*S)) (2*S)) ×ˢ (Finset.Icc (-(2*S)) (2*S))

def reps (S : ℤ) : Finset Pt := (box S).filter (fun x => N x = S)

def sreps (S : ℤ) : Finset Pt := (reps S).filter (fun x => psec x)

lemma mem_box {S : ℤ} {x : Pt} :
    x ∈ box S ↔ (-(2*S) ≤ x.1 ∧ x.1 ≤ 2*S) ∧ (-(2*S) ≤ x.2 ∧ x.2 ≤ 2*S) := by
  simp only [box, Finset.mem_product, Finset.mem_Icc]

lemma mem_reps {S : ℤ} (hS : 1 ≤ S) {x : Pt} : x ∈ reps S ↔ N x = S := by
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    obtain ⟨e1, e2, _⟩ := abs_bounds S hS x h
    rw [mem_box]
    exact ⟨abs_le.mp e1, abs_le.mp e2⟩

lemma mem_sreps {S : ℤ} (hS : 1 ≤ S) {x : Pt} : x ∈ sreps S ↔ N x = S ∧ psec x := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
    exact ⟨(mem_reps hS).mp h1, h2⟩
  · intro ⟨h1, h2⟩
    exact Finset.mem_filter.mpr ⟨(mem_reps hS).mpr h1, h2⟩

end SplitRec

namespace SplitRec

lemma prime_rep_phi (p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 1) (t : ZMod p)
    (ht : t ^ 2 + t + 1 = 0) : ∃ π : Pt, N π = (p:ℤ) ∧ phi p t π = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hN⟩ := prime_rep p hp hp3
  have hpdvd : phi p t (a, b) * phi p t (econ (a, b)) = 0 := by
    rw [phi_norm p t ht, hN]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (p:ℤ) p).mpr (dvd_refl (p:ℤ))
  rcases mul_eq_zero.mp hpdvd with h | h
  · exact ⟨(a, b), hN, h⟩
  · exact ⟨econ (a, b), by rw [N_econ]; exact hN, h⟩

lemma phi_econ_ne_zero (p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 1) {t : ZMod p}
    (ht : t ^ 2 + t + 1 = 0) {π : Pt} (hNπ : N π = (p:ℤ)) (hφπ : phi p t π = 0) :
    phi p t (econ π) ≠ 0 := by
  intro h0
  obtain ⟨d1, d2⟩ := p_dvd_of_phi p hp hp3 ht hφπ h0
  obtain ⟨u, hu⟩ := d1
  obtain ⟨v, hv⟩ := d2
  have hp0 : (0:ℤ) < (p:ℤ) := by exact_mod_cast hp.pos
  have hp2 : (2:ℤ) ≤ (p:ℤ) := by exact_mod_cast hp.two_le
  have hN : N π = ((p:ℤ))^2 * N (u, v) := by
    simp only [N]
    rw [hu, hv]
    ring
  have hsq : ((p:ℤ))^2 ∣ (p:ℤ) := ⟨N (u, v), hNπ.symm.trans hN⟩
  have hle : ((p:ℤ))^2 ≤ (p:ℤ) := Int.le_of_dvd hp0 hsq
  nlinarith

lemma descent (p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 1) (t : ZMod p)
    (ht : t ^ 2 + t + 1 = 0) (π : Pt) (hNπ : N π = (p:ℤ)) (hφπ : phi p t π = 0)
    (T : ℤ) (α : Pt) (hNα : N α = (p:ℤ) * T) :
    ∃ β : Pt, N β = T ∧ (α = emul π β ∨ α = emul (econ π) β) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : (0:ℤ) < (p:ℤ) := by exact_mod_cast hp.pos
  have hpne : ((p:ℤ)) ≠ 0 := ne_of_gt hp0
  have hcπne : econ π ≠ 0 := by
    intro h
    have hz : N (econ π) = 0 := by rw [h]; simp [N]
    rw [N_econ, hNπ] at hz
    omega
  have main : ∀ α : Pt, N α = (p:ℤ) * T → phi p t α = 0 →
      ∃ β : Pt, N β = T ∧ α = emul π β := by
    intro α hNα hφα
    have h1 : phi p t (emul α (econ π)) = 0 := by
      rw [phi_emul p t ht, hφα]; ring
    have h2 : phi p t (econ (emul α (econ π))) = 0 := by
      rw [econ_emul, phi_emul p t ht, econ_econ, hφπ]; ring
    obtain ⟨d1, d2⟩ := p_dvd_of_phi p hp hp3 ht h1 h2
    obtain ⟨b1, hb1⟩ := d1
    obtain ⟨b2, hb2⟩ := d2
    have hγ : emul α (econ π) = emul ((p:ℤ), 0) (b1, b2) := by
      rw [emul_smul]; exact Prod.ext hb1 hb2
    have hNg : N (emul α (econ π)) = ((p:ℤ))^2 * N (b1, b2) := by
      rw [hγ, N_emul]; simp [N]
    have hNg2 : N (emul α (econ π)) = ((p:ℤ))^2 * T := by
      rw [N_emul, hNα, N_econ, hNπ]; ring
    have hNT : N (b1, b2) = T := by
      have he : ((p:ℤ))^2 * N (b1, b2) = ((p:ℤ))^2 * T := by rw [← hNg, hNg2]
      exact mul_left_cancel₀ (by positivity) he
    refine ⟨(b1, b2), hNT, ?_⟩
    have hpp : emul π (econ π) = ((p:ℤ), 0) := by rw [emul_con, hNπ]
    have hstep : emul (emul π (b1, b2)) (econ π) = emul ((p:ℤ), 0) (b1, b2) := by
      rw [emul_comm π (b1, b2), emul_assoc, hpp]
      exact emul_comm _ _
    have hstep2 : emul (emul π (b1, b2)) (econ π) = emul α (econ π) := by
      rw [hstep, ← hγ]
    exact (emul_cancel_right hstep2 hcπne).symm
  have hzero : phi p t α * phi p t (econ α) = 0 := by
    rw [phi_norm p t ht, hNα]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((p:ℤ) * T) p).mpr ⟨T, rfl⟩
  rcases mul_eq_zero.mp hzero with h | h
  · obtain ⟨β, hNβ, hβ⟩ := main α hNα h
    exact ⟨β, hNβ, Or.inl hβ⟩
  · obtain ⟨γ, hNγ, hγ⟩ := main (econ α) (by rwa [N_econ]) h
    exact ⟨econ γ, by rwa [N_econ], Or.inr (by rw [← econ_econ α, hγ, econ_emul])⟩

lemma branch_disjoint (p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 1) (t : ZMod p)
    (ht : t ^ 2 + t + 1 = 0) (π : Pt) (hNπ : N π = (p:ℤ)) (hφπ : phi p t π = 0)
    (T : ℤ) (hTn : ¬ ((p:ℤ) ∣ T)) (β β' : Pt) (hβ : N β = T) (hβ' : N β' = T) :
    emul π β ≠ emul (econ π) β' := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcon := phi_econ_ne_zero p hp hp3 ht hNπ hφπ
  intro heq
  have heq' : phi p t (emul π β) = phi p t (emul (econ π) β') := by rw [heq]
  rw [phi_emul p t ht, hφπ, zero_mul] at heq'
  rw [phi_emul p t ht] at heq'
  have hφβ' : phi p t β' = 0 := by
    rcases mul_eq_zero.mp heq'.symm with h | h
    · exact absurd h hcon
    · exact h
  have hdiv : ((p:ℤ)) ∣ N β' := by
    have hz : ((N β' : ℤ) : ZMod p) = 0 := by
      rw [← phi_norm p t ht β', hφβ']; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (N β') p).mp hz
  rw [hβ'] at hdiv
  exact hTn hdiv

end SplitRec

namespace SplitRec

lemma reps_mul (p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 1) (T : ℤ) (hT : 1 ≤ T)
    (hTn : ¬ ((p:ℤ) ∣ T)) :
    (reps ((p:ℤ) * T)).card = 2 * (reps T).card := by
  obtain ⟨t, ht⟩ := exists_root p hp hp3
  obtain ⟨π, hNπ, hφπ⟩ := prime_rep_phi p hp hp3 t ht
  have hp0 : (0:ℤ) < (p:ℤ) := by exact_mod_cast hp.pos
  have hp2 : (2:ℤ) ≤ (p:ℤ) := by exact_mod_cast hp.two_le
  have hS1 : 1 ≤ (p:ℤ) * T := by nlinarith
  have hπne : π ≠ 0 := by
    intro h
    rw [h] at hNπ
    simp [N] at hNπ
    omega
  have hcπne : econ π ≠ 0 := by
    intro h
    have hz : N (econ π) = 0 := by rw [h]; simp [N]
    rw [N_econ, hNπ] at hz
    omega
  have hset : reps ((p:ℤ) * T)
      = (reps T).image (fun β => emul π β) ∪ (reps T).image (fun β => emul (econ π) β) := by
    ext α
    simp only [Finset.mem_union, Finset.mem_image]
    constructor
    · intro hα
      have hNα : N α = (p:ℤ) * T := (mem_reps hS1).mp hα
      obtain ⟨β, hNβ, hor⟩ := descent p hp hp3 t ht π hNπ hφπ T α hNα
      have hβ : β ∈ reps T := (mem_reps hT).mpr hNβ
      rcases hor with h | h
      · exact Or.inl ⟨β, hβ, h.symm⟩
      · exact Or.inr ⟨β, hβ, h.symm⟩
    · rintro (⟨β, hβ, rfl⟩ | ⟨β, hβ, rfl⟩)
      · exact (mem_reps hS1).mpr (by rw [N_emul, hNπ, (mem_reps hT).mp hβ])
      · exact (mem_reps hS1).mpr (by rw [N_emul, N_econ, hNπ, (mem_reps hT).mp hβ])
  have hdisj : Disjoint ((reps T).image (fun β => emul π β))
      ((reps T).image (fun β => emul (econ π) β)) := by
    rw [Finset.disjoint_left]
    intro α h1 h2
    obtain ⟨β1, hβ1, h1'⟩ := Finset.mem_image.mp h1
    obtain ⟨β2, hβ2, h2'⟩ := Finset.mem_image.mp h2
    exact branch_disjoint p hp hp3 t ht π hNπ hφπ T hTn β1 β2 ((mem_reps hT).mp hβ1)
      ((mem_reps hT).mp hβ2) (h1'.trans h2'.symm)
  have hinj1 : ((reps T).image (fun β => emul π β)).card = (reps T).card := by
    refine Finset.card_image_of_injOn ?_
    intro β1 _ β2 _ heq
    have heq2 : emul β1 π = emul β2 π := by
      rw [emul_comm β1 π, emul_comm β2 π]; exact heq
    exact emul_cancel_right heq2 hπne
  have hinj2 : ((reps T).image (fun β => emul (econ π) β)).card = (reps T).card := by
    refine Finset.card_image_of_injOn ?_
    intro β1 _ β2 _ heq
    have heq2 : emul β1 (econ π) = emul β2 (econ π) := by
      rw [emul_comm β1 (econ π), emul_comm β2 (econ π)]; exact heq
    exact emul_cancel_right heq2 hcπne
  rw [hset, Finset.card_union_of_disjoint hdisj, hinj1, hinj2, two_mul]

end SplitRec

namespace SplitRec

lemma reps_one : reps (1:ℤ) = ({(1,0), (-1,0), (0,1), (0,-1), (-1,1), (1,-1)} : Finset Pt) := by
  ext x
  rw [mem_reps (le_refl (1:ℤ))]
  constructor
  · intro hx
    obtain ⟨a, c⟩ := x
    obtain ⟨e1, e2, _⟩ := abs_bounds 1 le_rfl (a, c) hx
    have h1 : -2 ≤ a := by simpa using (abs_le.mp e1).1
    have h2 : a ≤ 2 := by simpa using (abs_le.mp e1).2
    have h3 : -2 ≤ c := by simpa using (abs_le.mp e2).1
    have h4 : c ≤ 2 := by simpa using (abs_le.mp e2).2
    simp only [N] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases a <;> interval_cases c <;> simp_all
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hx
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals simp [N]

lemma card_reps_one : (reps (1:ℤ)).card = 6 * 2 ^ (1:ℕ).primeFactors.card := by
  rw [reps_one, Nat.primeFactors_one]
  simp only [Finset.card_empty, pow_zero, mul_one]
  decide

end SplitRec

namespace SplitRec

lemma card_reps (S : ℕ) (hS : 1 ≤ S) (hsq : Squarefree S)
    (hp3 : ∀ p ∈ S.primeFactors, p % 3 = 1) :
    (reps (S : ℤ)).card = 6 * 2 ^ S.primeFactors.card := by
  revert hS hsq hp3
  induction S using Nat.strong_induction_on with
  | _ S ih =>
    intro hS hsq hp3
    rcases Nat.lt_or_ge S 2 with hlt | hge
    · have hS1 : S = 1 := by omega
      subst hS1
      exact card_reps_one
    · obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : S ≠ 1)
      have hSne : S ≠ 0 := by omega
      have hSpos : 0 < S := by omega
      have hp3p : p % 3 = 1 := hp3 p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, hSne⟩)
      have hTmul : p * (S / p) = S := Nat.mul_div_cancel' hpdvd
      have hTne : S / p ≠ 0 := by
        intro h0
        rw [h0, Nat.mul_zero] at hTmul
        omega
      have hT1 : 1 ≤ S / p := Nat.div_pos (Nat.le_of_dvd hSpos hpdvd) hpp.pos
      have hTlt : S / p < S := Nat.div_lt_self hSpos hpp.one_lt
      have hdvdT : S / p ∣ S := ⟨p, by rw [Nat.mul_comm]; exact hTmul.symm⟩
      have hsqT : Squarefree (S / p) := Squarefree.squarefree_of_dvd hdvdT hsq
      have hp3T : ∀ q ∈ (S / p).primeFactors, q % 3 = 1 := by
        intro q hq
        have hq' := Nat.mem_primeFactors.mp hq
        exact hp3 q (Nat.mem_primeFactors.mpr ⟨hq'.1, hq'.2.1.trans hdvdT, hSne⟩)
      have hpnmem : p ∉ (S / p).primeFactors := by
        intro hmem
        have hpdvdT : p ∣ S / p := (Nat.mem_primeFactors.mp hmem).2.1
        have hppdvd : p * p ∣ S := by
          rw [← hTmul]
          exact mul_dvd_mul_left p hpdvdT
        exact (Nat.squarefree_iff_prime_squarefree.mp hsq) p hpp hppdvd
      have hpf : S.primeFactors = insert p (S / p).primeFactors := by
        have h1 : (p * (S / p)).primeFactors = insert p (S / p).primeFactors := by
          rw [Nat.primeFactors_mul (by omega : p ≠ 0) hTne, hpp.primeFactors,
            Finset.singleton_union]
        rwa [hTmul] at h1
      have hcardS : S.primeFactors.card = (S / p).primeFactors.card + 1 := by
        rw [hpf, Finset.card_insert_of_notMem hpnmem]
      have hndvd : ¬ ((p:ℤ) ∣ (((S / p : ℕ)) : ℤ)) := by
        intro hd
        have hdn : p ∣ S / p := by exact_mod_cast hd
        have hppdvd : p * p ∣ S := by
          rw [← hTmul]
          exact mul_dvd_mul_left p hdn
        exact (Nat.squarefree_iff_prime_squarefree.mp hsq) p hpp hppdvd
      have hSc : ((S:ℤ)) = (p:ℤ) * (((S / p : ℕ)) : ℤ) := by
        have h' : ((p * (S / p) : ℕ) : ℤ) = (S : ℤ) := by rw [hTmul]
        push_cast at h'
        exact h'.symm
      have hmul := reps_mul p hpp hp3p (((S / p : ℕ)) : ℤ) (by exact_mod_cast hT1) hndvd
      have hIH := ih (S / p) hTlt hT1 hsqT hp3T
      calc (reps ((S:ℤ))).card = (reps ((p:ℤ) * (((S / p : ℕ)) : ℤ))).card := by rw [hSc]
        _ = 2 * (reps (((S / p : ℕ)) : ℤ)).card := hmul
        _ = 2 * (6 * 2 ^ (S / p).primeFactors.card) := by rw [hIH]
        _ = 6 * 2 ^ S.primeFactors.card := by rw [hcardS, pow_succ]; ring

end SplitRec

namespace SplitRec

lemma card_reps_six_mul (S : ℤ) (hS : 1 ≤ S) (h3 : ¬ (3:ℤ) ∣ S) (hsq : ∀ t : ℤ, S ≠ t ^ 2) :
    (reps S).card = 6 * (sreps S).card := by
  have hcard : ((sreps S) ×ˢ (Finset.univ : Finset (Fin 6))).card = 6 * (sreps S).card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    ring
  have hmap : Set.MapsTo (fun a : Pt × Fin 6 => ezeta^[(a.2 : ℕ)] a.1)
      ↑((sreps S) ×ˢ (Finset.univ : Finset (Fin 6))) ↑(reps S) := by
    rintro ⟨x, k⟩ hx
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true] at hx
    obtain ⟨hNx, _⟩ := (mem_sreps hS).mp hx
    exact (mem_reps hS).mpr (by rw [N_ezeta_iter, hNx])
  have hinj : (↑((sreps S) ×ˢ (Finset.univ : Finset (Fin 6))) : Set (Pt × Fin 6)).InjOn
      (fun a : Pt × Fin 6 => ezeta^[(a.2 : ℕ)] a.1) := by
    rintro ⟨x1, k1⟩ h1 ⟨x2, k2⟩ h2 heq
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true] at h1 h2
    obtain ⟨hN1, hp1⟩ := (mem_sreps hS).mp h1
    obtain ⟨hN2, hp2⟩ := (mem_sreps hS).mp h2
    have hk1 : (k1 : ℕ) < 6 := k1.isLt
    have hk2 : (k2 : ℕ) < 6 := k2.isLt
    have heq' : ezeta^[(k1 : ℕ)] x1 = ezeta^[(k2 : ℕ)] x2 := heq
    have key : ∀ (a b : Pt) (d : ℕ), N a = S → N b = S → psec a → psec b → d < 6 →
        a = ezeta^[d] b → a = b ∧ d = 0 := by
      intro a b d hNa hNb hpa hpb hd hab
      have h3b : ¬ (3:ℤ) ∣ N b := by rw [hNb]; exact h3
      have hsqb : ∀ t : ℤ, N b ≠ t ^ 2 := by rw [hNb]; exact hsq
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · rw [h0] at hab
        simp at hab
        exact ⟨hab, h0⟩
      · exfalso
        exact (psec_orb_not_d b hpb h3b hsqb h0 (by omega)) (by rw [← hab]; exact hpa)
    rcases le_total (k1 : ℕ) (k2 : ℕ) with hle | hle
    · have hd6 : (k2 : ℕ) - (k1 : ℕ) < 6 := lt_of_le_of_lt (Nat.sub_le _ _) hk2
      have hxd : x1 = ezeta^[(k2 : ℕ) - (k1 : ℕ)] x2 := by
        have e : ezeta^[(k1 : ℕ)] (ezeta^[(k2 : ℕ) - (k1 : ℕ)] x2) = ezeta^[(k2 : ℕ)] x2 := by
          rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hle]
        exact (Function.Injective.iterate ezeta_inj (k1 : ℕ)) (heq'.trans e.symm)
      obtain ⟨hx, hd⟩ := key x1 x2 ((k2 : ℕ) - (k1 : ℕ)) hN1 hN2 hp1 hp2 hd6 hxd
      have hk : (k1 : ℕ) = (k2 : ℕ) := Nat.le_antisymm hle (Nat.le_of_sub_eq_zero hd)
      rw [hx]
      exact Prod.ext rfl (Fin.ext hk)
    · have hd6 : (k1 : ℕ) - (k2 : ℕ) < 6 := lt_of_le_of_lt (Nat.sub_le _ _) hk1
      have hxd : x2 = ezeta^[(k1 : ℕ) - (k2 : ℕ)] x1 := by
        have e : ezeta^[(k2 : ℕ)] (ezeta^[(k1 : ℕ) - (k2 : ℕ)] x1) = ezeta^[(k1 : ℕ)] x1 := by
          rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hle]
        exact (Function.Injective.iterate ezeta_inj (k2 : ℕ)) (heq'.symm.trans e.symm)
      obtain ⟨hx, hd⟩ := key x2 x1 ((k1 : ℕ) - (k2 : ℕ)) hN2 hN1 hp2 hp1 hd6 hxd
      have hk : (k1 : ℕ) = (k2 : ℕ) := Nat.le_antisymm (Nat.le_of_sub_eq_zero hd) hle
      rw [hx]
      exact Prod.ext rfl (Fin.ext hk)
  have hsurj : (↑((sreps S) ×ˢ (Finset.univ : Finset (Fin 6))) : Set (Pt × Fin 6)).SurjOn
      (fun a : Pt × Fin 6 => ezeta^[(a.2 : ℕ)] a.1) ↑(reps S) := by
    intro y hy
    have hNy : N y = S := (mem_reps hS).mp hy
    have h3' : ¬ (3:ℤ) ∣ N y := by rw [hNy]; exact h3
    have hsq' : ∀ t : ℤ, N y ≠ t ^ 2 := by rw [hNy]; exact hsq
    obtain ⟨k0, hk0, hpk⟩ := psec_orb_exists y h3' hsq'
    have hNy' : N (ezeta^[k0] y) = S := by rw [N_ezeta_iter, hNy]
    have hmem : ezeta^[k0] y ∈ sreps S := (mem_sreps hS).mpr ⟨hNy', hpk⟩
    rcases Nat.eq_zero_or_pos k0 with h0 | h0
    · refine ⟨(y, 0), ?_, ?_⟩
      · rw [Finset.mem_coe, Finset.mem_product]
        exact ⟨by rwa [show ezeta^[k0] y = y by rw [h0]; simp] at hmem, Finset.mem_univ _⟩
      · simp
    · refine ⟨(ezeta^[k0] y, ⟨6 - k0, by omega⟩), ?_, ?_⟩
      · rw [Finset.mem_coe, Finset.mem_product]
        exact ⟨hmem, Finset.mem_univ _⟩
      · change ezeta^[6 - k0] (ezeta^[k0] y) = y
        rw [← Function.iterate_add_apply, show (6 - k0) + k0 = 6 by omega]
        exact ezeta_six y
  rw [← hcard]
  exact (Finset.card_nbij (fun a : Pt × Fin 6 => ezeta^[(a.2 : ℕ)] a.1) hmap hinj hsurj).symm

end SplitRec

namespace SplitRec

def zset (S : ℕ) : Finset ℤ :=
  (Finset.Icc (0:ℤ) (2*(S:ℤ))).filter (fun z =>
      0 < ((Finset.Icc (-(2*(S:ℤ))) (2*(S:ℤ))).filter (fun x =>
              x≤ -x-z ∧ -x-z≤z ∧ x^2+x*(-x-z)+(-x-z)^2=(S:ℤ))).card)

lemma zset_eq_image (S : ℕ) (hS : 1 ≤ (S:ℤ)) :
    zset S = (sreps (S:ℤ)).image (fun p : Pt => -(p.1 + p.2)) := by
  ext z
  simp only [zset, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hz0, hz2⟩, hpos⟩
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    obtain ⟨hxr, hx1, hx2, hx3⟩ := Finset.mem_filter.mp hx
    rw [Finset.mem_Icc] at hxr
    have hNs : N (x, -x - z) = (S:ℤ) := by
      simp only [N]
      rw [hx3]
    have hp : psec (x, -x - z) := by
      simp only [psec]
      exact ⟨hx1, by linarith, by linarith⟩
    exact ⟨(x, -x - z), (mem_sreps hS).mpr ⟨hNs, hp⟩, by dsimp only; ring⟩
  · rintro ⟨⟨x, y⟩, hmem, hzeq⟩
    obtain ⟨hNs, hp⟩ := (mem_sreps hS).mp hmem
    obtain ⟨e1, e2, e3⟩ := abs_bounds (S:ℤ) hS (x, y) hNs
    simp only [psec] at hp
    obtain ⟨hp1, hp2, hp3⟩ := hp
    have h1 : -(2*(S:ℤ)) ≤ x ∧ x ≤ 2*(S:ℤ) := abs_le.mp e1
    have h3 : -(2*(S:ℤ)) ≤ x + y ∧ x + y ≤ 2*(S:ℤ) := abs_le.mp e3
    have hz0 : 0 ≤ z := by rw [← hzeq]; linarith
    have hz2 : z ≤ 2*(S:ℤ) := by rw [← hzeq]; linarith
    refine ⟨⟨hz0, hz2⟩, Finset.card_pos.mpr ⟨x, ?_⟩⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]; exact h1
    have hval : -x - z = y := by rw [← hzeq]; ring
    rw [hval]
    exact ⟨hp1, by linarith, hNs⟩

lemma sreps_sum_inj (S : ℤ) (hS : 1 ≤ S) {x y : Pt} (hx : x ∈ sreps S) (hy : y ∈ sreps S)
    (h : x.1 + x.2 = y.1 + y.2) : x = y := by
  obtain ⟨hNx, hpx⟩ := (mem_sreps hS).mp hx
  obtain ⟨hNy, hpy⟩ := (mem_sreps hS).mp hy
  simp only [psec] at hpx hpy
  obtain ⟨hx1, -, -⟩ := hpx
  obtain ⟨hy1, -, -⟩ := hpy
  simp only [N] at hNx hNy
  obtain ⟨a, c⟩ := x
  obtain ⟨b, d⟩ := y
  simp only at h hx1 hy1 hNx hNy
  have hs : (a + c)^2 = (b + d)^2 := by rw [h]
  have hac : a * c = b * d := by linear_combination hs - hNx + hNy
  have hb : b + d = a + c := h.symm
  have hkey : (a - b) * (a - d) = 0 := by linear_combination -hac + (-a) * hb
  rcases mul_eq_zero.mp hkey with hk | hk
  · have hab : a = b := by omega
    have hcd : c = d := by omega
    rw [hab, hcd]
  · have hab : a = b := by omega
    have hcd : c = d := by omega
    rw [hab, hcd]

end SplitRec

theorem PEqualNP.Outside.L_hash_collision_lab_split_records :
    ∀ S : ℕ, 1<S → Squarefree S → (∀ p ∈ S.primeFactors, p % 3 = 1) →
  ((Finset.Icc (0:ℤ) (2*(S:ℤ))).filter (fun z =>
      0 < ((Finset.Icc (-(2*(S:ℤ))) (2*(S:ℤ))).filter (fun x =>
              x≤ -x-z ∧ -x-z≤z ∧ x^2+x*(-x-z)+(-x-z)^2=(S:ℤ))).card)).card
  = 2^S.primeFactors.card := by
  intro S hS hsq hp3
  change (SplitRec.zset S).card = 2 ^ S.primeFactors.card
  have hS1 : 1 ≤ S := by omega
  have hSz : (1:ℤ) ≤ (S:ℤ) := by exact_mod_cast hS1
  have h3 : ¬ (3:ℤ) ∣ (S:ℤ) := by
    intro hd
    have hd3 : 3 ∣ S := by exact_mod_cast hd
    have hmem : 3 ∈ S.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, hd3, by omega⟩
    have h3p := hp3 3 hmem
    norm_num at h3p
  have hnsq : ∀ t : ℤ, (S:ℤ) ≠ t ^ 2 := by
    intro t ht
    have htz : (S:ℤ) = t ^ 2 := ht
    obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : S ≠ 1)
    have hpz : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hpp
    have hpdvd2 : (p:ℤ) ∣ t ^ 2 := by
      rw [← htz]
      exact_mod_cast hpdvd
    have hpt : (p:ℤ) ∣ t := hpz.dvd_of_dvd_pow hpdvd2
    have hppdvd : ((p:ℤ)) * (p:ℤ) ∣ (S:ℤ) := by
      rw [htz, pow_two]
      exact mul_dvd_mul hpt hpt
    have hppdvd' : p * p ∣ S := by exact_mod_cast hppdvd
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq) p hpp hppdvd'
  have h1 : (SplitRec.reps (S:ℤ)).card = 6 * 2 ^ S.primeFactors.card :=
    SplitRec.card_reps S hS1 hsq hp3
  have h2 : (SplitRec.reps (S:ℤ)).card = 6 * (SplitRec.sreps (S:ℤ)).card :=
    SplitRec.card_reps_six_mul (S:ℤ) hSz h3 hnsq
  have h6 : (SplitRec.sreps (S:ℤ)).card = 2 ^ S.primeFactors.card := by
    rw [h2] at h1
    omega
  have hz : (SplitRec.zset S).card = (SplitRec.sreps (S:ℤ)).card := by
    rw [SplitRec.zset_eq_image S hSz]
    refine Finset.card_image_of_injOn ?_
    intro x hx y hy hxy
    exact SplitRec.sreps_sum_inj (S:ℤ) hSz hx hy (by linarith)
  rw [hz, h6]
