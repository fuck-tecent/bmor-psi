import Mathlib

private lemma sct_term (p q s t r d e : ℝ) (hr : 0 ≤ r) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hp : |p| ≤ 1) (hq : |q| ≤ e) (hs : |s| ≤ r) (ht : |t| ≤ d) :
    |q * s + p * t| ≤ e * r + d := by
  have h1 : |q * s| ≤ e * r := by
    rw [abs_mul]; exact mul_le_mul hq hs (abs_nonneg _) he
  have h2 : |p * t| ≤ d := by
    rw [abs_mul]
    calc |p| * |t| ≤ 1 * d := mul_le_mul hp ht (abs_nonneg _) zero_le_one
      _ = d := one_mul d
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem Conjectures.SquarePacking.SeventeenChargeCellTransfer :
    ∀ (a b a' b' u v u' v' r d e : ℝ), 0 ≤ r → 0 ≤ d → 0 ≤ e → |a| ≤ 1 → |b| ≤ 1 → |a'-a| ≤ e → |b'-b| ≤ e → |u'| ≤ r → |v'| ≤ r → |u'-u| ≤ d → |v'-v| ≤ d → |a*u+b*v| + 2*(d+e*r) < 1/2 → |(-b)*u+a*v| + 2*(d+e*r) < 1/2 → |a'*u'+b'*v'| < 1/2 ∧ |(-b')*u'+a'*v'| < 1/2 := by
  intro a b a' b' u v u' v' r d e hr hd he ha hb hae hbe hu hv hud hvd h1 h2
  have k1 := sct_term a (a'-a) u' (u'-u) r d e hr hd he ha hae hu hud
  have k2 := sct_term b (b'-b) v' (v'-v) r d e hr hd he hb hbe hv hvd
  have k3 := sct_term b (-(b'-b)) u' (u'-u) r d e hr hd he hb (by rwa [abs_neg]) hu hud
  have k4 := sct_term a (a'-a) v' (v'-v) r d e hr hd he ha hae hv hvd
  have t1 := abs_add_le (a*u+b*v + ((a'-a)*u' + a*(u'-u))) ((b'-b)*v' + b*(v'-v))
  have t2 := abs_add_le (a*u+b*v) ((a'-a)*u' + a*(u'-u))
  have k3' : |-(b'-b)*u' + b*(u'-u)*(-1)| ≤ e*r+d := by
    have : -(b'-b)*u' + b*(u'-u)*(-1) = -((b'-b)*u' + b*(u'-u)) := by ring
    rw [this, abs_neg]
    exact sct_term b (b'-b) u' (u'-u) r d e hr hd he hb hbe hu hud
  have t3 := abs_add_le ((-b)*u+a*v + (-(b'-b)*u' + b*(u'-u)*(-1))) ((a'-a)*v' + a*(v'-v))
  have t4 := abs_add_le ((-b)*u+a*v) (-(b'-b)*u' + b*(u'-u)*(-1))
  constructor
  · have : a'*u'+b'*v' = (a*u+b*v) + ((a'-a)*u' + a*(u'-u)) + ((b'-b)*v' + b*(v'-v)) := by ring
    rw [this]
    linarith
  · have : (-b')*u'+a'*v' = ((-b)*u+a*v) + (-(b'-b)*u' + b*(u'-u)*(-1)) + ((a'-a)*v' + a*(v'-v)) := by ring
    rw [this]
    linarith
