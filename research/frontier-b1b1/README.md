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
