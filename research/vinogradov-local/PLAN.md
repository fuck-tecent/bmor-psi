# Vinogradov local plan

## Completed components

- `vaughan.lean`: Vaughan identity, exponential-sum decomposition, arithmetic
  Type-I support bounds, and the reindexings
  - `expSum_low_mu_mul_log_eq` (second Type-I term),
  - `expSum_mul_zeta_eq` (general `f * ζ * g` triple sum),
  - `expSum_low_mu_lowLambda_zeta_eq` (third Type-I term),
  - `expSum_high_mu_zeta_highLambda_eq` (Type-II term).
- `rational.lean`: geometric/Abel bounds, log-weighted bounds, rational and
  major-arc sine lower bounds, and the `Icc` geometric bounds.
- `type1_bound.lean`:
  - second Type-I term on major arcs: `2 U q log n`;
  - third Type-I term on major arcs (`q > U^2`): `2 U^2 q log n`;
  - combined Type-I major-arc bound: `6 U^2 q log n`
    (`norm_expSum_vaughan_typeI_le_majorArc`);
  - Type-II Cauchy–Schwarz reduction
    (`norm_expSum_high_mu_zeta_highLambda_sq_le`).
- `finite_large_sieve.lean`: the accepted finite `ZMod` large sieve
  `∑_r ‖∑_n a_n e(rn/Q)‖^2 ≤ (N+Q) ∑_n |a_n|^2` vendored locally.

## Type-II target

For `t = a/q + β` on a major arc, with `gcd(a,q) = 1`, the Type-II term is

```lean
expSum n (high U μ * ζ * high U Λ) t
  = ∑ d ∈ Icc (U+1) n, μ d *
      ∑ e ∈ Icc (U+1) (n/d), Λ e *
        ∑ m ∈ Icc 1 (n/(d*e)), E (d*e*m*t).
```

The goal is a bound `o(n / (log n)^A)`, eventually for `U ≈ n^{2/5}` and
`q ≤ Q ≈ n^{1/5}`.

## Large-sieve route

1. ~~Collapse the `(e, m)` sum into a single divisor sum.~~ Done:
   `inner_high_sum_collapse` proves
   `∑_e Λ e ∑_m E(d e m t) = ∑_{l ≤ n/d} c_U(l) E(l * d * t)`
   with `c_U(l) = ∑_{e | l, e > U} Λ(e)`, and
   `norm_expSum_high_mu_zeta_highLambda_sq_le'` states the squared-energy
   bound in this collapsed form.
2. Dyadically split `d ∈ [D, 2D)` so that the length `n/d` is comparable to
   `n/D` inside each block.
3. Apply Cauchy–Schwarz over `d` (done) and the finite large sieve to the
   Fourier transforms at `l * d * a/q`.  The fixed-length form is done:
   `largeSieve_frequency_energy` proves
   `∑_{d ≤ D} ‖∑_{l ≤ L} c_l e(l d a/q)‖²
      ≤ (D/q + 1)(L + q)∑|c_l|²`
   for `gcd(a,q) = 1`.  What remains is the varying length `n/d` and `β`.
4. Handle the `β` perturbation.  The sharp separated additive large sieve is
   now vendored (`separated_large_sieve.lean`), and
   `separated_frequency_energy` gives the fixed-length energy bound for any
   `δ`-separated frequency family.  Remaining: prove `CircleSeparated` for
   `x d = d (a/q + β)` on blocks of length `< q`, using `gcd(a,q) = 1` and
   `|β| ≤ 1/(2 q D)`.  Done: `circleSeparated_majorArc_shift` proves the
   separation, and `majorArc_block_energy` gives
   `∑_{d ≤ D} ‖∑_{n ≤ L} c_n e(n(d0+d)(a/q+β))‖²
      ≤ (L + 1 + 2q)∑|c_n|²`.

The technical bottleneck is step 2: the finite large sieve needs a fixed
coefficient length, so a smooth cutoff (or a dyadic block decomposition with
an error term) is required before the vendored theorem applies.

## Minor arcs

After the major arcs, the remaining `t` satisfy
`|sin (π d t)|` lower bounds for all small `d`; the plan is to use the
Weierstrass/Weyl or Vinogradov minor-arc machinery on the same Type-I/II
decomposition.  Nothing in this direction is formalized yet.
