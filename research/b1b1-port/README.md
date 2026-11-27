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

## Milestone 2 (`b1b1_port.lean`): the exact b1-b1 far/near decomposition

The file now contains (all verified, no `sorry`):

```lean
wwave c u l r t      -- weighted progression ∑_{h ∈ (l,r]} c h · e(u h t)
woffWave c b u l r   -- the grid-neighbourhood complement of wwave
continuous_wwave
wwave_at_cell_center -- q ∣ g ⟹ wwave c g l r (t + a/q) = wwave c g l r t
integral_cell_wwave
centered_deep_wwave_integral  -- weighted centred annulus integral = Ramanujan sum
split_shifted_wwave           -- weighted far/near split
```

i.e. the two structural lemmas of the verified `b1-b4` module are re-proved for
arbitrary progression weights.  Their only arithmetic input is
`q ∣ g → e(g h a/q) = 1`, which is weight-independent.

Then:

```lean
plainPolynomial_tau1   -- S_{τ₁} = ∑_{a ∈ (U,B₁]} c(a) · wwave Λ a U (n/a)
deepIntegral_eq_task   -- the port's Jdeep equals the task integrand
deepIntegral_split     -- Jdeep = ∑_{a ∈ (U,B₁]} c(a) · (farPart n a + nearPart n a)
```

with

```text
farPart n a  = ∫_{wideArcsᶜ} S_{τ₁} · offWave(Λ, a, U, n/a)
nearPart n a = ∑_{q | a, q > R} ∑_{m ≤ n} τ₁(m) · c_q(m - n) ·
                 ∫_{window q} e((m-n)t) · wwave Λ a U (n/a)
```

**No new parameter arithmetic is needed**: `M := maximumStep n = cutoffU n * cutoffB n`
satisfies every hypothesis of `split_shifted_wwave`, because
`cutoffB n ≤ maximumStep n`, `cutoffR n ≤ cutoffB n` and
`cutoffR n · n · radius (maximumStep n) ≤ cutoffH n` are exactly
`cutoffs_ordered` and `cutoffR_covered` from the verified module, and the atom
steps are `a ≤ lowCut n ≤ cutoffB n ≤ maximumStep n`.

### Remaining two estimates

* **far**: needs the weighted analogue of `offWave_mass_le_weighted`, replacing
  `∫ |wave|² = r - l` by `∫ |wwave Λ|² = ∑_{h} Λ(h)²`.  Scale:
  `√n · maximumStep · W ≈ n^(43/48+o(1)) = o(n)`.
* **near**: must be bounded below `n^(43/48)`.  The crude bound
  (absolute values, `|c_q| ≤ q`, `|window| ≤ 2·radius M`) gives only
  `≈ n^(5/4+o(1))`, so the `progressionAverage` / `windowKernel` smoothing must
  be redone in weighted form.  This is the remaining substantial piece.

## Milestone 3: decoding the far-side machinery, and the exact gap

I read the far-side chain of the verified module:

```text
smoothKernel a c t = 1/(a + |t - c|)
nearestCenter  : ∃ i ≤ u, |u t - i| ≤ 1/2
waveBound      : ‖wave u l r t‖ ≤ (2/u) * smoothKernel (1/(n+1)) (i/u) t
pairEnv / awayPoint / awayBound
offWave_mass_le_pairwise / offWave_mass_le_weighted
```

`waveBound` is built from exactly two inputs:

```text
(1) length      ‖wave u l r t‖ ≤ n/u                       (from r - l ≤ n/u)
(2) oscillation ‖wave u l r t‖ * |t - i/u| ≤ 1/u           (from wave_sin)
```

and these give `‖wave‖ * (1/(n+1) + |t - i/u|) ≤ 2/u`, i.e.
`‖wave u l r t‖ ≤ (2/u) * smoothKernel (1/(n+1)) (i/u) t`.

For b1-b1 the progression is `Λ`-weighted, so the weighted `waveBound` needs

```text
(1) ‖wwave Λ u l r t‖ ≤ ∑_{h ∈ (l,r]} Λ h            -- proved below (wwave_mangoldt_cap)
(2) ‖wwave Λ u l r t‖ · |t - i/u| ≤ (log-factor) / u  -- MISSING
```

and (2) is precisely a **weighted exponential-sum estimate**:
with `θ = u t` and `‖θ‖ ≥ H/(u n)` (valid on `wideArcsᶜ`),

```text
‖∑_{h ∈ (l,r]} Λ(h) e(θ h)‖ * ‖θ‖/u  ≲  log^C n .
```

The standard route is `Λ = μ * log` followed by partial summation over the
*monotone* weight `log k`:

```text
∑_h Λ(h) e(θ h) = ∑_d μ(d) ∑_k log k · e(θ d k),
|∑_{k ≤ K} log k · e(θ d k)| ≤ 2 log K · sup_K' |∑_{k ≤ K'} e(θ d k)|
                             ≤ 2 log K / ‖d θ‖ .
```

This is the one genuinely missing analytic ingredient for the far side.

### What the far side can and cannot afford

* Target (as in b1-b4): `‖far‖ ≲ √n · maximumStep n · W = n^(43/48+o(1))`.
* The *trivial* far bound is `‖S_{τ₁}‖₂ · ‖G‖₂` with
  `‖S_{τ₁}‖₂² = ∑_m |τ₁(m)|² ≈ n log⁴ n` and `‖G‖₂² ≤ ‖S_{τ₁}‖₂²`, giving only
  `n log⁴ n` — a `log⁴` miss.  So the far side, too, cannot be closed by `L²`
  alone: it needs the weighted oscillation bound (2) to get `‖G‖_{L²(gridᶜ)}`
  down to `n^(19/48+o(1))`.

### Revised status

`deepIntegral_split` is exact and verified.  Both remaining estimates (far and
near) now reduce to the *same* missing analytic input: a weighted
(equivalently, `Λ = μ * log` + Abel) exponential-sum bound for
`∑_{h} Λ(h) e(θ h)` off the wide arcs.  Everything else (arc geometry,
Ramanujan sums, the split, the `L²` identities) is in place.

## Milestone 4: the verified Vinogradov minor-arc saving is usable

The catalogue module `Conjectures.Goldbach.VinogradovPolylogMinorSaving`
(verified, 9065 lines, imports only Mathlib) provides

```text
∀ A > 0, ∀ᶠ n, ∀ t ∈ [0,1],
  t ∉ arcsPoly (2⌈A⌉₊+16) n →
    ‖∑_{k ≤ n} Λ k · e(k t)‖ ≤ n · (log n)^(-A)
```

with `arcsPoly B n` the union of `[a/q ± (log₂(n+2))^B/(q n)]` over `q ≤ (log₂(n+2))^B`.

Two consequences for b1-b1:

1. **The arcs are inside the wide arcs.**  `arcsPoly_subset_wideSet` (proved in
   `b1b1_port.lean`) shows

   ```lean
   (log₂(n+2))^B ≤ cutoffB n → (log₂(n+2))^B ≤ cutoffH n → arcsPoly B n ⊆ wideSet n
   ```

   so `t ∉ wideArcs n` gives `t ∉ arcsPoly B n`.

2. **Passing to `θ = u t`.**  If `{u t}` lies in a polylog arc of denominator
   `q` and radius `P/(q n)`, then `t` lies within `P/(u q n)` of `p/(u q)`, and
   `u q ≤ B₁ · (log n)^B = n^(1/4+o(1)) ≤ n^(1/3) = cutoffB n`; also
   `P/(q n) ≤ H/(q n)` because `H = 256 n^(1/3) log² n ≫ P`.  Hence the
   Vinogradov arcs *pulled back along `u`* are still inside the wide arcs, and
   for `t ∉ wideArcs n`

   ```text
   ‖∑_{h ≤ n/u} Λ(h) · e(u h t)‖ ≤ (n/u) · (log n)^(-A) .
   ```

So the pointwise minor-arc input is *available* for the weighted progressions,
and it is stronger than the `‖wwave‖·|t - i/u| ≤ 1/u` ingredient of `awayBound`.

### Why this does not by itself close b1-b1

The target is the *signed* integral `∫_{Aᶜ} S_{τ₁}² e(-n t) dt`.  A pointwise
bound `|S_{τ₁}| ≤ n (log n)^(2-A)` only gives

```text
|Jdeep| ≤ ∫_{Aᶜ} |S|² ≤ sup|S| · ∫|S| ≤ n(log n)^(2-A) · n^(1/2) log² n ,
```

which still exceeds `n` by `n^(1/2)`.  The reason is structural: the `L²` mass
`∑_m |τ₁(m)|² ≈ n log⁴ n` sits mostly *on* `Aᶜ` (the wide arcs have measure
`O(log²n / n^(1/3))`), so no bound on `∫_{Aᶜ}|S|²` or on `sup_{Aᶜ}|S|` can prove
`o(n)`.  The saving has to come from the oscillation `e(-n t)`, i.e. from the
far/near dispersion and the coefficient structure — exactly as in the verified
b1-b4 proof.  The decomposition is done (`deepIntegral_split`); what is left is
the *weighted* `awayBound` / `offWave_mass_le_weighted`.

The Vinogradov module is nevertheless valuable: it removes the need for the
`wave_sin` oscillation ingredient in the weighted `waveBound`, since on `Aᶜ`
the whole weighted progression is already `≤ (n/u)(log n)^(-A)`.
