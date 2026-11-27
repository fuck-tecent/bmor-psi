import Mathlib

namespace PEqualNP.Outside

/-- The standard representatives modulo `q` of the roots of `X ^ 2 + a`. -/
def rootsQ (a q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun r => q ∣ r^2 + a)

lemma mem_rootsQ (a q r : ℕ) : r ∈ rootsQ a q ↔ r < q ∧ q ∣ r^2 + a := by
  simp [rootsQ, Finset.mem_filter, Finset.mem_range]

/-- The `ZMod` avatar of membership in `rootsQ a q`. -/
lemma zmod_rootQ (a q r : ℕ) : ((r : ZMod q)^2 + a = 0) ↔ q ∣ r^2 + a := by
  have h : ((r : ZMod q)^2 + a : ZMod q) = (r^2 + a : ℕ) := by
    simp only [Nat.cast_add, Nat.cast_pow]
  rw [h, ZMod.natCast_eq_zero_iff]

lemma coe_modQ (n m : ℕ) : ((n % m : ℕ) : ZMod m) = (n : ZMod m) := by
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq n m

lemma eq_of_cast_eqQ {n : ℕ} [NeZero n] {x y : ℕ} (hx : x < n) (hy : y < n)
    (h : (x : ZMod n) = (y : ZMod n)) : x = y := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

/-- The Chinese remainder equivalence sends a natural number to the pair of its two residues. -/
lemma crt_natCastQ {a b : ℕ} (h : Nat.Coprime a b) (n : ℕ) :
    ZMod.chineseRemainder h (n : ZMod (a * b)) = ((n : ZMod a), (n : ZMod b)) :=
  map_natCast (ZMod.chineseRemainder h) n

lemma crt_fstQ {a b : ℕ} (h : Nat.Coprime a b) (n : ℕ) :
    (ZMod.chineseRemainder h (n : ZMod (a * b))).1 = (n : ZMod a) :=
  congrArg Prod.fst (crt_natCastQ h n)

lemma crt_sndQ {a b : ℕ} (h : Nat.Coprime a b) (n : ℕ) :
    (ZMod.chineseRemainder h (n : ZMod (a * b))).2 = (n : ZMod b) :=
  congrArg Prod.snd (crt_natCastQ h n)

/-- Reducing a root modulo a divisor of the modulus again gives a root. -/
lemma mod_rootsQ {a m n : ℕ} (hm : 0 < m) (hmn : m ∣ n) (r : ℕ) (hr : r ∈ rootsQ a n) :
    r % m ∈ rootsQ a m := by
  have hd : n ∣ r^2 + a := (mem_rootsQ a n r).mp hr |>.2
  have hz : ((r : ZMod m)^2 + a = 0) := (zmod_rootQ a m r).mpr (dvd_trans hmn hd)
  rw [← coe_modQ r m] at hz
  exact (mem_rootsQ a m (r % m)).mpr ⟨Nat.mod_lt r hm, (zmod_rootQ a m (r % m)).mp hz⟩

lemma crtRootsFrom_memQ {a b c : ℕ} [NeZero a] [NeZero b] (h : Nat.Coprime a b)
    (p : { u : ℕ // u ∈ rootsQ c a } × { v : ℕ // v ∈ rootsQ c b }) :
    ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) ∈ rootsQ c (a * b) := by
  haveI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have hc : ZMod.chineseRemainder h ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) =
      (↑p.1.1, ↑p.2.1) := RingEquiv.apply_symm_apply _ _
  have hu : ((p.1.1 : ℕ) : ZMod a)^2 + c = 0 :=
    (zmod_rootQ c a p.1.1).mpr ((mem_rootsQ c a p.1.1).mp p.1.2).2
  have hv : ((p.2.1 : ℕ) : ZMod b)^2 + c = 0 :=
    (zmod_rootQ c b p.2.1).mpr ((mem_rootsQ c b p.2.1).mp p.2.2).2
  have hprod : (((p.1.1 : ZMod a), (p.2.1 : ZMod b)) : ZMod a × ZMod b)^2 + c = 0 := by
    show ((↑p.1.1 ^ 2 + c, ↑p.2.1 ^ 2 + c) : ZMod a × ZMod b) = (0, 0)
    simp [hu, hv]
  have h0 : ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1))^2 + c = 0 := by
    apply (ZMod.chineseRemainder h).map_eq_zero_iff.mp
    rw [map_add, map_pow, map_natCast, hc]
    exact hprod
  refine (mem_rootsQ c (a * b) _).mpr ⟨ZMod.val_lt _, ?_⟩
  have hz : (((ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) : ℕ) :
      ZMod (a * b)))^2 + c = 0 := by
    rw [ZMod.natCast_zmod_val]
    exact h0
  exact (zmod_rootQ c (a * b) _).mp hz

def crtRootsToQ {a b c : ℕ} [NeZero a] [NeZero b] (_h : Nat.Coprime a b)
    (r : { r : ℕ // r ∈ rootsQ c (a * b) }) :
    { u : ℕ // u ∈ rootsQ c a } × { v : ℕ // v ∈ rootsQ c b } :=
  ⟨⟨r.1 % a, mod_rootsQ (Nat.pos_of_ne_zero (NeZero.ne a)) (dvd_mul_right a b) r.1 r.2⟩,
    ⟨r.1 % b, mod_rootsQ (Nat.pos_of_ne_zero (NeZero.ne b)) (dvd_mul_left b a) r.1 r.2⟩⟩

def crtRootsFromQ {a b c : ℕ} [NeZero a] [NeZero b] (h : Nat.Coprime a b)
    (p : { u : ℕ // u ∈ rootsQ c a } × { v : ℕ // v ∈ rootsQ c b }) :
    { r : ℕ // r ∈ rootsQ c (a * b) } :=
  ⟨ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)), crtRootsFrom_memQ h p⟩

lemma crtRootsFrom_crtRootsToQ {a b c : ℕ} [NeZero a] [NeZero b] (h : Nat.Coprime a b)
    (r : { r : ℕ // r ∈ rootsQ c (a * b) }) :
    crtRootsFromQ h (crtRootsToQ h r) = r := by
  haveI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have key : ((ZMod.chineseRemainder h).symm (↑(r.1 % a), ↑(r.1 % b)) : ZMod (a * b)) =
      (r.1 : ZMod (a * b)) := by
    rw [coe_modQ (r.1) a, coe_modQ (r.1) b, ← crt_natCastQ h r.1,
      RingEquiv.symm_apply_apply]
  have hval : ZMod.val ((ZMod.chineseRemainder h).symm (↑(r.1 % a), ↑(r.1 % b))) = r.1 :=
    eq_of_cast_eqQ (ZMod.val_lt _) ((mem_rootsQ c (a * b) r.1).mp r.2).1
      ((ZMod.natCast_zmod_val _).trans key)
  exact Subtype.ext hval

lemma crtRootsTo_crtRootsFromQ {a b c : ℕ} [NeZero a] [NeZero b] (h : Nat.Coprime a b)
    (p : { u : ℕ // u ∈ rootsQ c a } × { v : ℕ // v ∈ rootsQ c b }) :
    crtRootsToQ h (crtRootsFromQ h p) = p := by
  haveI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have hc : ZMod.chineseRemainder h ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) =
      (↑p.1.1, ↑p.2.1) := RingEquiv.apply_symm_apply _ _
  have hxa : (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) : ZMod a) =
      (p.1.1 : ZMod a) := by
    rw [← crt_fstQ h (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1))),
      ZMod.natCast_zmod_val, hc]
  have hxb : (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) : ZMod b) =
      (p.2.1 : ZMod b) := by
    rw [← crt_sndQ h (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1))),
      ZMod.natCast_zmod_val, hc]
  have h1 : ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) % a = p.1.1 :=
    eq_of_cast_eqQ (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne a)))
      ((mem_rootsQ c a p.1.1).mp p.1.2).1
        ((coe_modQ (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1))) a).trans hxa)
  have h2 : ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1)) % b = p.2.1 :=
    eq_of_cast_eqQ (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne b)))
      ((mem_rootsQ c b p.2.1).mp p.2.2).1
        ((coe_modQ (ZMod.val ((ZMod.chineseRemainder h).symm (↑p.1.1, ↑p.2.1))) b).trans hxb)
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · exact h1
  · exact h2

/-- Coprimality splits the roots of `X ^ 2 + a` modulo a product into pairs of roots: the count is
multiplicative. -/
theorem L_quadratic_primes_levent_fixed_a_crt_density :
    let roots := fun a q : ℕ => (Finset.range q).filter (fun r => q ∣ r^2+a);
    ∀ a q m : ℕ, 0<q → 0 < m → Nat.Coprime q m →
      (roots a (q*m)).card = (roots a q).card * (roots a m).card := by
  intro roots c q m hq hm hcq
  haveI : NeZero q := ⟨ne_of_gt hq⟩
  haveI : NeZero m := ⟨ne_of_gt hm⟩
  haveI : NeZero (q * m) := ⟨mul_ne_zero (ne_of_gt hq) (ne_of_gt hm)⟩
  have hcard : (rootsQ c (q * m)).card = ((rootsQ c q) ×ˢ (rootsQ c m)).card := by
    refine Finset.card_bij (fun r _ => (r % q, r % m)) ?_ ?_ ?_
    · intro r hr
      refine Finset.mem_product.mpr
        ⟨mod_rootsQ hq (dvd_mul_right q m) r hr, mod_rootsQ hm (dvd_mul_left m q) r hr⟩
    · intro r₁ hr₁ r₂ hr₂ h
      have h1 : r₁ % q = r₂ % q := congrArg Prod.fst h
      have h2 : r₁ % m = r₂ % m := congrArg Prod.snd h
      have h3 : (r₁ : ZMod (q * m)) = (r₂ : ZMod (q * m)) := by
        apply (ZMod.chineseRemainder hcq).injective
        rw [crt_natCastQ hcq r₁, crt_natCastQ hcq r₂, ← coe_modQ r₁ q, ← coe_modQ r₂ q,
          ← coe_modQ r₁ m, ← coe_modQ r₂ m, h1, h2]
      exact eq_of_cast_eqQ ((mem_rootsQ c (q * m) r₁).mp hr₁).1
        ((mem_rootsQ c (q * m) r₂).mp hr₂).1 h3
    · intro p hp
      obtain ⟨hpq, hpm⟩ := Finset.mem_product.mp hp
      set x : { r : ℕ // r ∈ rootsQ c (q * m) } :=
        crtRootsFromQ hcq ⟨⟨p.1, hpq⟩, ⟨p.2, hpm⟩⟩
      refine ⟨x.1, x.2, ?_⟩
      exact congrArg
        (fun z : { u : ℕ // u ∈ rootsQ c q } × { v : ℕ // v ∈ rootsQ c m } => (z.1.1, z.2.1))
        (crtRootsTo_crtRootsFromQ hcq ⟨⟨p.1, hpq⟩, ⟨p.2, hpm⟩⟩)
  exact hcard.trans (Finset.card_product _ _)

end PEqualNP.Outside
