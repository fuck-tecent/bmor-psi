# Optimality of `3(p-1)` for the HJSW two-period fold family

**Status.** The upper-bound theorem below is proved (elementary, all odd primes) and
machine-checked in Lean 4.36.0 / Mathlib `fc4f59e5` (self-contained file, `import Mathlib`,
no `sorry`, no extra axioms). The equality side ("the maximum equals `3(p-1)`") is verified
computationally for `p <= 31`; for general `p` it reduces to the known validity of the HJSW
1975 construction, which this note does **not** formalize.

This note accompanies the proposed claimable intermediate goal
`L-no-three-in-line-hjsw-fold-upper-bound` in `research/problems.json`.

## Setting

Let `p` be an odd prime, `F = ZMod p`, and let `t in F` be a shift. The *shifted hyperbola cap*
is the graph `x |-> (u_x, v_x) = (x + t, x^{-1})`, indexed by `x in F^*`.
Lift each cap point to a `2 x 2` block of integer grid points:

```
P_x(i,j) = ( (u_x).val + i*p , (v_x).val + j*p ),    (i,j) in {0,1}^2 ,
```

where `ZMod.val` is the representative in `[0,p)`. A configuration is a mask
`R : F -> P({0,1}^2)` with `R(0) = empty`; the associated point set is the union of the
`R(x)` over `x != 0`. Call the configuration *valid* if no three of its points are collinear
(equivalently: every integer `3 x 3` determinant of two difference vectors is nonzero).

## Theorem (upper bound, all odd primes)

If a configuration is valid, then

```
sum_{x in F^*} |R(x)| <= 3*(p-1) .
```

In particular the HJSW value `3(p-1)` (density `3/2` with a `-1.5` lower-order term) cannot be
improved within this family: **there is no net gain inside the shifted-hyperbola two-period
fold family**, not even by one point.

## Proof structure

Write `det3(P,Q,R) = (Q1-P1)(R2-P2) - (Q2-P2)(R1-P1)`, and for two distinct fibres
`x != x'` set `du = u_{x'} - u_x`, `dv = v_{x'} - v_x` (integer differences of representatives).

1. **Det expansion.** For two points of one fibre with direction `(a,b) = (i2-i1, j2-j1)` and a
   point `Q = P_{x'}(i3,j3)` of another fibre,
   `det3 = p*(a*dv - b*du) + p^2*B` with `B = a*(j3-j1) - b*(i3-i1)`.
   Hence a collinear triple forces `b*du - a*dv = p*B`.

2. **Fibre-pair constraint characterisation.** Let `x != x'`, both nonzero. A `2+1` collinear
   triple with two points in the `x`-fibre exists **iff** `x*x' = 1` or `x*x' = -1` in `F`.
   Indeed the congruence `b*(x'-x) - a*((x')^{-1} - x^{-1}) = 0` is, after multiplying by
   `x*x'`, equivalent to `(x'-x)*(b*(x*x') + a) = 0`; since `x != x'` and `(a,b) != (0,0)`
   with `a,b in {-1,0,1}`, this holds iff `a,b in {+-1}` and `x*x' = -a/b = +-1`.

3. **Constants on edge pairs.** If `x*x' = +-1`, take a constraint direction, e.g. `(a,b) = (1,-1)`
   for `x*x'=1` or `(a,b) = (1,1)` for `x*x'=-1`, and put `D = b*du - a*dv`,
   `c = D/p`. Then `p | D` by Step 2, and the representatives give
   `|D| <= |du| + |dv| <= 2p-3 < 2p`; hence `c in {-1,0,1}`.
   (A sharper identity holds: on edge pairs `D = +-p*(w_x - w_{x'})` where
   `w_y = [ (y+t).val + (y+t) >= p ]` is the carry; this also explains the observed
   histogram `D in {-p,0,p}`.)

4. **Edge pairs have `S = 6`.** For the direction and the concrete pair
   `P1 = P_x(0,1)`, `P2 = P_x(1,0)` (case `x*x'=1`) or `P1 = P_x(0,0)`, `P2 = P_x(1,1)`
   (case `x*x'=-1`), one checks `B = i3+j3-1`, respectively `B = j3-i3`; both attain all of
   `{-1,0,1}` as `(i3,j3)` varies. Hence for each `c` there is a `Q in P_{x'}` with a
   collinear triple: two full buckets (`4+4`) are incompatible. A closer analysis of the
   forbidden sets shows that if one side is full (`|R(x)| = 4`) then `|R(x')| <= 2`:
   - `c = 0` forbids two cells of the other bucket, so `|R(x')| <= 2`;
   - `c = +-1` forbids one cell; assuming `|R(x')| = 3` the mask contains the constraint pair
     of that edge type (anti-diagonal `{(0,1),(1,0)}` for `x*x'=1`, main diagonal
     `{(0,0),(1,1)}` for `x*x'=-1`), and the **reverse arc** (two points in the `x'`-fibre
     plus one in the `x`-fibre) has forbidden set `F' = F(-c)` — a different single cell —
     which a full `x`-bucket must meet, a contradiction.
   Summarising: on every edge pair of the constraint graph, `|R(x)| + |R(x')| <= 6`.

5. **Constraint graph.** Define `G6` on `F^*` by `{x,x'}` edge iff `x*x' = +-1`, `x != x'`.
   Equivalently `x' = T1(x) = x^{-1}` or `x' = T2(x) = -x^{-1}`. Both `T1,T2` are involutions,
   `T1(x) != T2(x)` for odd `p`, and the orbits are `{x, x^{-1}, -x, -x^{-1}}`; hence every
   component of `G6` is a cycle `C2` or `C4` (the `C2`s being `{1,-1}` and, when `p = 1 mod 4`,
   `{r,-r}` with `r^2 = -1`).

6. **Counting.** Let `H = { x : |R(x)| = 4 }`. By Step 4, `H` is independent in `G6`; every
   neighbour of `H` has `|R| <= 2`, and all remaining fibres have `|R| <= 3`. Since independent
   sets in a disjoint union of `C2`/`C4` satisfy `|N(H)| >= |H|`,
   ```
   sum |R(x)| <= 4|H| + 2|N(H)| + 3((p-1) - |H| - |N(H)|)
              = 3(p-1) + |H| - |N(H)| <= 3(p-1) .
   ```
   (A formalised variant replaces this by an explicit fixed-point-free involution pairing
   `1 <-> -1` and `x <-> x^{-1}`; the conclusion is the same.)

## Computational evidence

* Exhaustive checks for all primes `p <= 101`, all shifts `t`: the structural facts
  (constraint graph components, `S = 6` on edges, forbidden-set tables) hold with no
  exception; 8.4 million individual Lemma-3 checks for `p <= 200` give zero violations.
* Exhaustive `16^4` search of all masks for `p = 5` gives maximum `12 = 3(p-1)`.
* The HJSW construction attains `3(p-1)` for every tested prime `p <= 293`.  The deletion rule
  used in these checks is: with `hh = (p-1)/2` and `t = hh`, remove from the `x`-fibre the corner
  `(dI, dJ)` where `dI = 0` if `x <= hh` and `1` otherwise, and `dJ = 0` if `x^{-1} > hh` and `1`
  otherwise.  (An earlier draft in our notes had the `dJ` half of this rule inverted; with the
  inverted version the configuration has a collinear triple for every odd `p >= 7`, e.g.
  `x = 2`, `x' = hh`, corners `(0,0),(1,1)` and `(0,0)`.  The corrected rule above has been
  re-checked by brute force for all shifts/triples for every prime `p <= 293` (61 primes) with no violation.
  This concerns only the equality side; the upper bound proved here is independent of it.)

## Lean formalisation

* `Final.lean` (1022 lines, `import Mathlib` only): definitions of the lift, the point set,
  the no-three-collinear predicate, and the unconditional main theorem
  `hjsw_fold_optimal`.
* A second, independently assembled proof (838 lines) reproduces the same theorem.
* The public statement is the closed proposition (all definitions inlined with `let`) posted as
  `L-no-three-in-line-hjsw-fold-upper-bound`; the wrapper theorem in the submission file is
  byte-compatible (whitespace-insensitive) with that statement.
* Local gates: `leancheck rc=0`, `guardcheck rc=0`, `finalcheck rc=0`, no `sorry`/`admit`/`axiom`.

## Reference

D. R. Hall, S. C. Jackson, A. Sudbery, K. Wild, *Some advances in the no-three-in-line
problem*, J. Combin. Theory Ser. A **18** (1975) 336-341.
<https://doi.org/10.1016/0097-3165(75)90043-6>
