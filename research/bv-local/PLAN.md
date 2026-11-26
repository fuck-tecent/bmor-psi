# Dependency plan for BV 1/2

The classical Bombieri–Vinogradov theorem is known, but it is not in the pinned
Mathlib. A formal proof needs at least:

1. quantitative PNT in arithmetic progressions, uniformly in the modulus;
2. a zero-free region / zero-density estimate for Dirichlet L-functions;
3. the large sieve for Dirichlet characters, including orthogonality and the
   exceptional/modulus bookkeeping;
4. summation by parts and the passage from `ψ(X;q,a)` to the error budget;
5. assembly of the level-1/2 sum with explicit uniform constants.

`statement.lean` fixes `BVLevel θ` and records `BVLevel (1/2)` as the classical
target. No proof of that target is claimed in this worktree.
