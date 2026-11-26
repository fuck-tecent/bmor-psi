# Local Bombieri–Vinogradov interface

This is a local, non-catalogue draft on branch `research/bv-local`.

`statement.lean` defines `BVLevel θ`, the usual prime-progression error average
for moduli `q ≤ floor (X ^ θ)`, and records that the catalogue target is exactly
`BVLevel (3/5)`.

Important distinction:

- `BVLevel (1/2)` is the classical Bombieri–Vinogradov theorem, known
  unconditionally.
- `BVLevel (3/5)` is strictly stronger and is an open frontier conjecture in the
  catalogue. It is not a consequence of the classical level-1/2 theorem.

A formal proof of either level still needs quantitative PNT in arithmetic
progressions and zero-density/zero-free-region input, which are not in the pinned
Mathlib. This file only fixes the exact formal interface; it does not claim a proof.
