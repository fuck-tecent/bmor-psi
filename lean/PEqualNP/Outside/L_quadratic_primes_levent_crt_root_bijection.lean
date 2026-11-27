import Mathlib

namespace PEqualNP.Outside

/-- The standard representatives modulo `q` of the roots of `X ^ 2 + a`. -/
def rootsStd (a q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun r => q ∣ r^2 + a)

lemma mem_rootsStd (q r : ℕ) : r ∈ rootsStd 1 q ↔ r < q ∧ q ∣ r^2 + 1 := by
  simp [rootsStd, Finset.mem_filter, Finset.mem_range]

/-- The `ZMod` avatar of membership in `rootsStd 1 q`. -/
lemma zmod_root_iff (q r : ℕ) : ((r : ZMod q)^2 + 1 = 0) ↔ q ∣ r^2 + 1 := by
  have h : ((r : ZMod q)^2 + 1 : ZMod q) = (r^2 + 1 : ℕ) := by
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  rw [h, ZMod.natCast_eq_zero_iff]

lemma coe_mod_cast (n m : ℕ) : ((n % m : ℕ) : ZMod m) = (n : ZMod m) := by
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq n m

lemma eq_of_cast_eq {n : ℕ} [NeZero n] {x y : ℕ} (hx : x < n) (hy : y < n)
    (h : (x : ZMod n) = (y : ZMod n)) : x = y := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

/-- The Chinese remainder equivalence sends a natural number to the pair of its two residues. -/
lemma crt_natCast {a b : ℕ} (h : Nat.Coprime a b) (n : ℕ) :
    ZMod.chineseRemainder h (n : ZMod (a * b)) = ((n : ZMod a), (n : ZMod b)) :=
  map_natCast (ZMod.chineseRemainder h) n

lemma crt_fst {a b : ℕ} (h : Nat.Coprime a b) (n : ℕ) :
    (ZMod.chineseRemainder h (n : ZMod (a * b))).1 = (n : ZMod a) :=
  congrArg Prod.fst (crt_natCast h n)

lemma crt_snd {a b : ℕ} (h : Nat.Coprime a b) (n : ℕ) :
    (ZMod.chineseRemainder h (n : ZMod (a * b))).2 = (n : ZMod b) :=
  congrArg Prod.snd (crt_natCast h n)

/-- Reducing a root modulo a divisor of the modulus again gives a root. -/
lemma mod_rootsStd {m n : ℕ} (hm : 0 < m) (hmn : m ∣ n) (r : ℕ) (hr : r ∈ rootsStd 1 n) :
    r % m ∈ rootsStd 1 m := by
  have hd : n ∣ r^2 + 1 := (mem_rootsStd n r).mp hr |>.2
  have hz : ((r : ZMod m)^2 + 1 = 0) := (zmod_root_iff m r).mpr (dvd_trans hmn hd)
  rw [← coe_mod_cast r m] at hz
  exact (mem_rootsStd m (r % m)).mpr ⟨Nat.mod_lt r hm, (zmod_root_iff m (r % m)).mp hz⟩

lemma crtRootsFrom_mem {a b : ℕ} [NeZero a] [NeZero b] (h : Nat.Coprime a b)
    (p : { u : ℕ // u ∈ rootsStd 1 a } × { v : ℕ // v ∈ rootsStd 1 b }) :
    ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) ∈ rootsStd 1 (a * b) := by
  haveI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have hc : ZMod.chineseRemainder h ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) =
      (↑p.1.1, ↑p.2.1) := RingEquiv.apply_symm_apply _ _
  have hu : ((p.1.1 : ℕ) : ZMod a)^2 + 1 = 0 :=
    (zmod_root_iff a p.1.1).mpr ((mem_rootsStd a p.1.1).mp p.1.2).2
  have hv : ((p.2.1 : ℕ) : ZMod b)^2 + 1 = 0 :=
    (zmod_root_iff b p.2.1).mpr ((mem_rootsStd b p.2.1).mp p.2.2).2
  have hprod : (((p.1.1 : ZMod a), (p.2.1 : ZMod b)) : ZMod a × ZMod b)^2 + 1 = 0 := by
    show ((↑p.1.1 ^ 2 + 1, ↑p.2.1 ^ 2 + 1) : ZMod a × ZMod b) = (0, 0)
    simp [hu, hv]
  have h0 : ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1))^2 + 1 = 0 := by
    apply (ZMod.chineseRemainder h).map_eq_zero_iff.mp
    rw [map_add, map_pow, map_one, hc]
    exact hprod
  refine (mem_rootsStd (a * b) _).mpr ⟨ZMod.val_lt _, ?_⟩
  have hz : (((ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) : ℕ) :
      ZMod (a * b)))^2 + 1 = 0 := by
    rw [ZMod.natCast_zmod_val]
    exact h0
  exact (zmod_root_iff (a * b) _).mp hz

def crtRootsTo {a b : ℕ} [NeZero a] [NeZero b] (_h : Nat.Coprime a b)
    (r : { r : ℕ // r ∈ rootsStd 1 (a * b) }) :
    { u : ℕ // u ∈ rootsStd 1 a } × { v : ℕ // v ∈ rootsStd 1 b } :=
  ⟨⟨r.1 % a, mod_rootsStd (Nat.pos_of_ne_zero (NeZero.ne a)) (dvd_mul_right a b) r.1 r.2⟩,
    ⟨r.1 % b, mod_rootsStd (Nat.pos_of_ne_zero (NeZero.ne b))
      (dvd_mul_of_dvd_right (dvd_refl b) a) r.1 r.2⟩⟩

def crtRootsFrom {a b : ℕ} [NeZero a] [NeZero b] (h : Nat.Coprime a b)
    (p : { u : ℕ // u ∈ rootsStd 1 a } × { v : ℕ // v ∈ rootsStd 1 b }) :
    { r : ℕ // r ∈ rootsStd 1 (a * b) } :=
  ⟨ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)), crtRootsFrom_mem h p⟩

lemma crtRootsFrom_crtRootsTo {a b : ℕ} [NeZero a] [NeZero b] (h : Nat.Coprime a b)
    (r : { r : ℕ // r ∈ rootsStd 1 (a * b) }) :
    crtRootsFrom h (crtRootsTo h r) = r := by
  haveI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have key : ((ZMod.chineseRemainder h).symm (↑(r.1 % a), ↑(r.1 % b)) : ZMod (a * b)) =
      (r.1 : ZMod (a * b)) := by
    rw [coe_mod_cast (r.1) a, coe_mod_cast (r.1) b, ← crt_natCast h r.1,
      RingEquiv.symm_apply_apply]
  have hval : ZMod.val ((ZMod.chineseRemainder h).symm (↑(r.1 % a), ↑(r.1 % b))) = r.1 :=
    eq_of_cast_eq (ZMod.val_lt _) ((mem_rootsStd (a * b) r.1).mp r.2).1
      ((ZMod.natCast_zmod_val _).trans key)
  exact Subtype.ext hval

lemma crtRootsTo_crtRootsFrom {a b : ℕ} [NeZero a] [NeZero b] (h : Nat.Coprime a b)
    (p : { u : ℕ // u ∈ rootsStd 1 a } × { v : ℕ // v ∈ rootsStd 1 b }) :
    crtRootsTo h (crtRootsFrom h p) = p := by
  haveI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have hc : ZMod.chineseRemainder h ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) =
      (↑p.1.1, ↑p.2.1) := RingEquiv.apply_symm_apply _ _
  have hxa : (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) : ZMod a) =
      (p.1.1 : ZMod a) := by
    rw [← crt_fst h (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1))),
      ZMod.natCast_zmod_val, hc]
  have hxb : (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) : ZMod b) =
      (p.2.1 : ZMod b) := by
    rw [← crt_snd h (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1))),
      ZMod.natCast_zmod_val, hc]
  have h1 : ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) % a = p.1.1 :=
    eq_of_cast_eq (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne a)))
      ((mem_rootsStd a p.1.1).mp p.1.2).1
        ((coe_mod_cast (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1))) a).trans hxa)
  have h2 : ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) % b = p.2.1 :=
    eq_of_cast_eq (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne b)))
      ((mem_rootsStd b p.2.1).mp p.2.2).1
        ((coe_mod_cast (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1))) b).trans hxb)
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · exact h1
  · exact h2

theorem crt_root_bij (a b : ℕ) [NeZero a] [NeZero b] (h : Nat.Coprime a b) :
    ∃ e : { r : ℕ // r ∈ rootsStd 1 (a * b) } ≃
        ({ u : ℕ // u ∈ rootsStd 1 a } × { v : ℕ // v ∈ rootsStd 1 b }),
      ∀ r, ((e r).1.val, (e r).2.val) = (r.val % a, r.val % b) := by
  refine ⟨⟨crtRootsTo h, crtRootsFrom h, crtRootsFrom_crtRootsTo h, crtRootsTo_crtRootsFrom h⟩,
    ?_⟩
  intro r
  rfl

end PEqualNP.Outside

theorem PEqualNP.Outside.L_quadratic_primes_levent_crt_root_bijection :
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a);
    ∀ (a b : ℕ) [NeZero a] [NeZero b], Nat.Coprime a b →
      ∃ e : {r : ℕ // r ∈ roots 1 (a*b)} ≃
        ({u : ℕ // u ∈ roots 1 a} × {v : ℕ // v ∈ roots 1 b}),
        ∀ r, ((e r).1.val, (e r).2.val) = (r.val % a, r.val % b) :=
  PEqualNP.Outside.crt_root_bij
