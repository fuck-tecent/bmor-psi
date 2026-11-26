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

## GRH route to BV 1/2

Assuming the standard GRH consequence

```text
|ψ(X;q,a) - X/φ(q)| ≤ C * sqrt(X) * (log X)^2
```

uniformly in `q` and coprime `a`, summing over

```text
q ≤ sqrt(X) / (log X)^(A+2)
```

gives the classical BV level-1/2 budget

```text
C * X / (log X)^A.
```

`budget.lean` proves the real-variable identity for this summation. The remaining
analytic input is the derivation of the displayed GRH progression error from GRH
itself; `grh-compact` proves GRH but does not provide that AP error theorem.
