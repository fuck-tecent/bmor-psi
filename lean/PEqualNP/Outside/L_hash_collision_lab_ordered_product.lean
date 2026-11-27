import Mathlib

namespace PEqualNP.Outside

theorem L_hash_collision_lab_ordered_product :
    ∀ a b c x y z : ℤ, a ≤ b → b ≤ c → x ≤ y → y ≤ z →
      a + b + c = 0 → x + y + z = 0 →
      a ^ 2 + a * b + b ^ 2 = x ^ 2 + x * y + y ^ 2 →
      c < z → a * b * c < x * y * z := by
  intro a b c x y z hab hbc hxy hyz habc hxyz hnorm hcz
  let S : ℤ := a ^ 2 + a * b + b ^ 2
  have hc_nonneg : 0 ≤ c := by nlinarith
  have hfactor : 3 * c ^ 2 - S = (c - a) * (c - b) := by
    dsimp [S]
    nlinarith [habc]
  have hc_bound : S ≤ 3 * c ^ 2 := by
    have hca : 0 ≤ c - a := by omega
    have hcb : 0 ≤ c - b := by omega
    have hmul : 0 ≤ (c - a) * (c - b) := mul_nonneg hca hcb
    nlinarith [hfactor]
  have hcz_pos : 0 < z - c := sub_pos.mpr hcz
  have hzplus : 0 < z + c := by nlinarith
  have hzsq : c ^ 2 < z ^ 2 := by
    have hm : 0 < (z - c) * (z + c) := mul_pos hcz_pos hzplus
    nlinarith
  have hzc : c ^ 2 ≤ z * c := by
    simpa [pow_two] using mul_le_mul_of_nonneg_right (le_of_lt hcz) hc_nonneg
  have hsum : 3 * c ^ 2 < z ^ 2 + z * c + c ^ 2 := by nlinarith
  have hdiff : 0 < z ^ 2 + z * c + c ^ 2 - S := by nlinarith
  have hprod1 : a * b * c = c ^ 3 - S * c := by
    have hc : c = -a - b := by omega
    subst c
    dsimp [S]
    ring
  have hprod2 : x * y * z = z ^ 3 - S * z := by
    have hz' : z = -x - y := by omega
    subst z
    dsimp [S]
    rw [hnorm]
    ring
  have hgap : 0 < (z ^ 3 - S * z) - (c ^ 3 - S * c) := by
    have hfac : (z ^ 3 - S * z) - (c ^ 3 - S * c) =
        (z - c) * (z ^ 2 + z * c + c ^ 2 - S) := by ring
    rw [hfac]
    exact mul_pos hcz_pos hdiff
  nlinarith

end PEqualNP.Outside
