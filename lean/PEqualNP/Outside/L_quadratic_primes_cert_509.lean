import Mathlib

namespace PEqualNP.Outside

private theorem quadratic_prime_roots {p r s : ℕ} (hp : Nat.Prime p)
    (hr : r < p) (hs : s < p) (hrs : r + s = p) (hroot : p ∣ r ^ 2 + 1) :
    ∀ n : ℕ, p ∣ n ^ 2 + 1 ↔ n % p = r ∨ n % p = s := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  have hneg : (s : ZMod p) = -(r : ZMod p) := by
    rw [← add_eq_zero_iff_eq_neg, ← Nat.cast_add, add_comm s r, hrs, ZMod.natCast_self]
  have hroot' : (r : ZMod p) ^ 2 + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_zero_iff (r ^ 2 + 1) p).2 hroot
  intro n
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    ← hroot', add_left_inj, sq_eq_sq_iff_eq_or_eq_neg, ← hneg,
    ZMod.natCast_eq_natCast_iff' n r p, ZMod.natCast_eq_natCast_iff' n s p,
    Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs]

theorem L_quadratic_primes_cert_509 : ∀ n:ℕ, 509∣n^2+1 ↔ n % 509=208 ∨ n % 509=301 := by
  apply quadratic_prime_roots <;> norm_num

end PEqualNP.Outside
