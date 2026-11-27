# b1-b1 port workspace

Target: `L-goldbach-frontier-type2-b1-b1`

```lean
Jdeep n = ∫ t in 0..1, (wideArcs n)ᶜ.indicator (fun x => S n τ₁ x * S n τ₁ x * E (-n x)) t
goal:    ∀ e > 0, ∃ N, ∀ n ≥ N, Even n → ‖Jdeep n‖ ≤ e * n
```

Files here are compiled inside the main project:

```sh
cd ~/github.com/fuck-tencent/goldback-work/lean
lake env lean ../../goldback-vinogradov/research/b1b1-port/atoms.lean
```

They import the verified module `PEqualNP.Outside.L_goldbach_frontier_type2_b1_b4`
(Mathlib-only, 8135 lines, its own olean) and reuse its machinery:

* `DyadicMixedB4Geometric.wave`, `phase`
* `DyadicMixedB4ArcGeometry.wide`, `radius`, `window`, `cell`
* `DyadicMixedB4ArcCenters.centered_deep_wave_integral`, `ramanujan`
* `DyadicMixedB4ArcDecomposition.split_shifted_wave`, `plainPolynomial`
* `DyadicMixedB4YoungIntegral.norm_indicator_product_le`
* `DyadicMixedB4OffWaveMoment.offWave_mass_le_weighted`
* `DyadicMixedB4LowBand.lowBandCoefficient`  (this **is** the task's `τ₁`)
* `DyadicMixedB4Scale.cutoffU / cutoffB / cutoffR / cutoffH`

## Milestone 1 (`atoms.lean`)

```lean
atomWave a U R t = ∑ r ∈ Icc (U+1) R, (Λ r : ℂ) * phase ((a*r : ℕ) * t)

plainPolynomial_tau1 (n) (t) :
  plainPolynomial n (fun m => (lowBandCoefficient (cutoffU n) (lowCut n) m : ℂ)) t
    = ∑ a ∈ Icc (cutoffU n + 1) (lowCut n),
        (lowMoebiusWeight (cutoffU n) a : ℂ) * atomWave a (cutoffU n) (n / a) t
```

Proved by instantiating the verified
`Conjectures.Goldbach.FrontierType2B1B1BilinearExpansion`.
So `S n τ₁` is a sum of atoms indexed by the small divisor `a ∈ (U, B₁]`,
with weight `c(a) = lowMoebiusWeight U a` and progression sum `atomWave a U (n/a)`.

## Parameter arithmetic for the b1-b4 split

`B = cutoffB n = ⌊n^(1/3)⌋`, `H = cutoffH n = 256·B·log²`, `R = cutoffR n = ⌊n^(1/9)⌋`,
`radius M = 1/(8M²)`.  `split_shifted_wave` asks for

| hypothesis | equivalent |
|---|---|
| `B ≤ M` | `M ≥ n^(1/3)` |
| `4·H·M ≤ n` | `M ≤ n^(2/3)/(1024 log²n)` |
| `R·n·radius M ≤ H` | `M ≥ n^(7/18)/(45 log n)` |
| atom step `g ≤ M` | `g ≤ M` |

The window `[n^(7/18), n^(2/3-o(1))]` is non-empty, so **take `M = ⌊n^(7/18)⌋`**.
The far part then costs

```text
‖F‖₂ · ‖G‖₂  ≲  √(n log³n) · W · M · log²n  =  n^(8/9+o(1))  =  o(n)
```

with `W = sup_u ∑_{step = u} |weight| ≤ τ(u) ≤ n^o(1)`.  This is *better* than the
`n^(31/32)` b1-b4 budget, so the far side has room to spare.

## The obstruction

For `τ₁` the `Λ`-weight sits on the **large** cofactor `r = m/a ≤ n/a`, not on a
bounded factor:

```text
τ₁(m) = ∑_{a | m, U < a ≤ B₁} c(a) · Λ(m/a).
```

`split_shifted_wave` expands `∫ (wideᶜ) F · wave g l r` in the Fourier modes of `F`
and needs the progression factor to be the **unweighted** geometric sum
`wave g l r t = ∑_{h ∈ (l,r]} e(g h t)`.  With `Λ` inside, the progression is

```text
atomWave a U N t = ∑_{r ≤ N} Λ(r) e(a r t),
```

a weighted geometric sum.  The near-window analysis (`progressionAverage`,
`windowKernel`) has no `Λ` weights, so it does not apply.  Moreover the atom step
would have to be `g = a·e` once `Λ = μ * log` is expanded, which is unbounded.

Note that in b1-b4 (and b4-b4) this problem does not arise precisely because
`τ₄` has `a > n^(2/3)`, hence cofactor `< n^(1/3)`: the `Λ` lands on a *bounded*
factor and can be absorbed into the atom weight.

## What is and is not weight-polymorphic

`centered_deep_wave_integral` and `split_shifted_wave` are **weight-polymorphic**:
their only arithmetic input is `wave_at_cell_center`, i.e. `q ∣ g ⟹ e(g h a/q) = 1`.
A weighted progression `∑_h c_h e(g h t)` satisfies the same identity, so the exact
decomposition

```text
Jdeep  =  far part (offWave)  +  near part (annuli, Ramanujan sums)
```

goes through verbatim for `atomWave`.  The two *bounds* differ:

* far part: needs a weighted analogue of `offWave_mass_le_weighted`, where the
  unweighted identity `∫ |wave g l r|² = r - l` is replaced by
  `∫ |∑_h Λ(h) e(g h t)|² = ∑_h Λ(h)²`.  Tractable; the far budget is `n^(8/9)`.
* near part: the Ramanujan/primitive-character evaluation
  `∑_h e(g h a/q) = c_q(...)` needs **unit** coefficients.  This is where the
  weight really bites, and where `Λ = μ * log` (or Vaughan) has to move the weight
  off the progression index.

## Plan to get unweighted waves

Use `Λ = μ * log`, i.e. `Λ(r) = ∑_{e | r} μ(e) log (r/e)`, so that

```text
atomWave a U N t = ∑_e μ(e) ∑_{k : U < e k ≤ N} log k · e(a e k t).
```

Now the progression index is `k` (unweighted except for the **smooth** factor
`log k`), and the atom is `e` with weight `μ(e)`.  Two routes to remove `log k`:

1. partial summation: `∑_k log k · e(g k t) = ∫ (1/u) ∑_{u < k ≤ K} e(g k t) du`,
   which is an integral of unweighted geometric sums;
2. dyadic decomposition `k ∈ (2^j, 2^{j+1}]` with `log k = (j+1) log 2 + O(1)`,
   the `O(1)` error being absorbed by the same `offWave_mass_le_weighted` bound.

Both reduce b1-b1 to the b1-b4 far/near split for atoms `(a, e)` with step `ae`
and unweighted waves, which is exactly the shape the imported machinery handles.

## Status

* `atoms.lean` — compiles, no `sorry`.
* next: the `Λ = μ * log` re-expansion of `atomWave` into unweighted waves.
