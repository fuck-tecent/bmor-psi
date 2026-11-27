# Frontier Type-II b1-b1 (local research)

Target: `L-goldbach-frontier-type2-b1-b1`
(`lean/PEqualNP/Outside/L_goldbach_frontier_type2_b1_b1.lean`).

Both variables lie in the balanced frontier band `(n^(1/16), n^(1/4)]`; the
deep-minor integral of `τ₁ × τ₁` is `o(n)`.

Earlier path: `research/vinogradov-local` (Type-II dispersion).

## Milestone 1: dispersion form

`dispersion.lean` proves, for any coefficient sequence `u` and any measurable
`wideArcs`,

```lean
∫_{wideArcsᶜ} S n u x * S n u x * E (-(n:ℝ)*x)
  = ∑ m1, ∑ m2, u m1 u m2 *
      ∫_{wideArcsᶜ} E (((m1:ℝ)+(m2:ℝ)-(n:ℝ)) * x)
```

i.e. the deep-minor integral reduces to `∑_{m1,m2} c(m1)c(m2) K_n(m1+m2-n)`,
where `K_n(h) = ∫_{wideArcsᶜ} E(h x) dx` is the Fourier transform of the
deep-minor indicator.  The frequency is `h = m1 + m2 - n` (not `m1 - m2`).

Compiled against the catalogue project:

```
cd ~/github.com/fuck-tencent/goldback-work/lean && lake env lean <file>
```

## Next

1. Kernel structure: `K_n(h) = [h=0] - ∑_{q≤Q₁} ∑_{a≤q, (a,q)=1} ∫_{|β|≤H/(qn)} E(h(a/q+β))`.
   Nonresonant h (`q ∤ h` for all arcs) gets the geometric/Ramanujan bound;
   resonant h keeps `q | h` — the same `typeIIResonantOffDiag` shape as in
   `vinogradov-local`.
2. Collapse `m1 = a r`, `m2 = b s` via the proved bilinear expansion to reach
   the `τ₁` coefficient form.

## Milestone 2: kernel decomposition

`kernel.lean`: the deep-minor kernel is the full-circle integral minus the
wide-arc integral,

```lean
∫_{wideArcsᶜ} E(h t) dt = ∫_0^1 E(h t) dt − ∫_{wideArcs} E(h t) dt,
```

proved from the pointwise decomposition `f = s.indicator f + sᶜ.indicator f`
(explicit interval-integrability hypotheses).

Next: evaluate `∫_0^1 E(h t) dt` (it is `1` for `h = 0`, `0` otherwise) and
expand the wide-arc integral into the arc sum over `q ≤ Q₁`, `a ≤ q`.

## Milestone 3: the full-circle Fourier integral

`circle.lean`:

```lean
integral_E_circle (h : ℤ) :
  ∫ t in (0:ℝ)..1, E ((h:ℝ)*t) = if h = 0 then 1 else 0
```

Proof via Mathlib's `integral_exp_mul_complex`
(`∫ x in a..b, exp (c * x) = (exp (c*b) - exp (c*a))/c`) with `c = 2πi h`,
plus `Complex.exp_int_mul_two_pi_mul_I`.

Hence `K_n(h) = [h = 0] − ∫_{wideArcs} E(h t) dt`.

## Milestone 4: interval Fourier bounds

`osc.lean`:

```lean
norm_integral_E_le_length (h : ℤ) (hAB : A ≤ B) :
  ‖∫_{A}^{B} E(h t) dt‖ ≤ B - A

norm_integral_E_le_osc (h : ℤ) (hh : h ≠ 0) :
  ‖∫_{A}^{B} E(h t) dt‖ ≤ 1 / (π |h|)
```

So every arc integral is `≤ min(length, 1/(π|h|))`, exactly the input for the
non-resonant bound (`integral_exp_mul_complex` + `‖exp (i·)‖ = 1`).

## Milestone 5: arc parametrisation

`arc.lean`:

```lean
integral_E_arc (h : ℤ) (c ρ : ℝ) :
  ∫ t in (c - ρ)..(c + ρ), E(h t) = E(h c) * ∫ β in (-ρ)..ρ, E(h β)
```

So each wide-arc integral factors into the central phase `E(h a/q)` times the
translated kernel.  Combined with `norm_integral_E_le_osc`, every arc
contributes `≤ min(2ρ, 1/(π|h|))` in absolute value; the `E(h a/q)` phases are
what the Ramanujan cancellation acts on when summing over `a`.

## Milestone 6: packaged definitions

`defs.lean` names every object of the catalogue target:

`E`, `S`, `Qs`, `Qcut`, `Hwide`, `wideArcs`, `Ucut`, `Bcut`, `ccoef`,
`tau1`, `Jdeep`, and the packaged goal `Target`.

The direct `Iff.rfl` check that `Target` is definitionally the catalogue
`let`-chain did not unify (a syntactic mismatch somewhere in the local
`let` binders), so the packaged statement is kept as the working interface and
will be matched to the catalogue statement when the proof file is assembled.

## Milestone 7: wide-arc membership interface

`cover.lean`: `mem_wideArcs_iff` rewrites membership in `wideArcs n` into the
arc-family form

```lean
t ∈ wideArcs n ↔ ∃ q ∈ Icc 1 (Qcut n), ∃ a ∈ (range (q+1)).filter (Coprime · q),
  |t - a/q| ≤ Hwide n / (q n).
```

This is the interface for the arc-sum expansion of `∫_{wideArcs} E(h t) dt`.
The arcs are not disjoint at this width, so the expansion will need a bounded
overlap (Farey-spacing) argument or a disjoint sub-family.

## Milestone 8: Farey spacing

`farey.lean`:

```lean
farey_spacing (hq : 0 < q) (hq' : 0 < q')
  (hne : a/q ≠ a'/q') :
  1/(q q') ≤ |a/q - a'/q'|
```

This is the input for the bounded-overlap argument: although the wide arcs at
width `H/(q n)` are not disjoint, the reduced centres are `1/(q q')`-separated,
so a point can lie in only `C` of them once `H Q₁ / n < 1/C`.

## Milestone 9: overlap denominator bound

`overlap.lean`:

```lean
overlap_denominator_bound (hn : 0 < n) (hH : 0 ≤ H)
  (h1 : |t - a/q| ≤ H/(q n)) (h2 : |t - a'/q'| ≤ H/(q' n))
  (hne : a/q ≠ a'/q') :
  n ≤ 2 H q q'
```

So two distinct wide arcs meeting at `t` must satisfy `q q' ≥ n/(2H)`.  Since
`H = 256 Q₁ Q`, this says overlapping denominators are large; combined with
`farey_spacing` it gives the bounded-overlap count.  (This file contains its
own copy of `farey_spacing` to stay self-contained.)

## Milestone 10: one numerator per denominator

`unique.lean`:

```lean
arc_unique_per_denominator (hH : 0 ≤ H) (hn : 2H < n) (hq : 0 < q)
  (h1 : |t - a/q| ≤ H/(q n)) (h2 : |t - a'/q| ≤ H/(q n))
  (hne : a ≠ a') : False
```

So for `n > 2H` each denominator `q` contributes at most one arc through `t`.
Together with `overlap_denominator_bound`, the multiplicity of `wideArcs` at a
point is controlled by: at most one small-`q` arc (`q q' ≥ n/(2H)`) and at most
`1 + Q₁/√(n/(2H)) = O(1 + log² n)` large-`q` ones.
