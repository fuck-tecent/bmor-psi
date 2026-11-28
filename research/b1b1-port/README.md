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

## Milestone 5: route (b) "D = o(n)" is numerically FALSE

Route (b) was: show the main term `D = ∑_{m₁+m₂=n} τ₁(m₁)τ₁(m₂)` is `o(n)` by Möbius
cancellation, i.e. via `∑_{a ∈ (U,B₁]} c(a)/a = o(1)`.

`theta_numerics.py` computes `τ₁` exactly from the task definition (sieve over `a`
and `r`), for `n = 10^4 … 10^7`:

| n | U | B₁ | θ = ∑ c(a)/a | D/n | ∑\|τ₁\|²/n |
|---|---|---|---|---|---|
| 10^4 | 1 | 10 | −1.929 | 3.688 | 12.98 |
| 10^5 | 2 | 17 | −1.081 | 2.360 | 9.34 |
| 10^6 | 2 | 31 | −1.368 | 3.550 | 14.63 |
| 10^7 | 2 | 56 | −1.648 | 5.321 | 20.97 |

So `θ` is of order one and slowly growing, and `D = Θ(n θ²)`: **`D` is not `o(n)`.**

Structural reason (now proved in `b1b1_port.lean`):

```lean
sum_moebius_divisors_real (n) : ∑_{d | n} μ d = if n = 1 then 1 else 0
lowMoebiusWeight_eq_neg_small (U a) (1 < a) :
  lowMoebiusWeight U a = - ∑_{d | a, d ≤ U} μ d
```

so `c(a) = ∑_{U<d|a} μ d` is the Möbius sum over the **small** divisors.  For `U = 2`
this makes `c(a) = -1` exactly on odd prime powers and `0` elsewhere, whence

```text
θ ≈ - ∑_{p ≤ B₁} H_{B₁/p} / p ≈ - log B₁ · (log log B₁ + O(1)) ,
```

which is what the numbers show.  (Note `θ² ≈ 3.72, 1.17, 1.87, 2.72` against
`D/n ≈ 3.69, 2.36, 3.55, 5.32` — same order, ratio `≈ 2`.)

### Consequence for the strategy

The target `|D - W| = o(n)` with `D = Θ(n log log² n)` is a **main-term matching**
statement, not a smallness statement.  This is exactly what the verified `b1-b4`
proof does, and notably it does so **without ever computing a singular series**: it
proves `far` and `near` are each `n^(31/32+o(1))`, and the main term is cancelled
implicitly by the split.

Therefore the remaining gap for b1-b1 is unchanged and precise:

```text
∫_{gridᶜ} |S_{τ₁}|²  ≪  n^(1-δ)        (weighted L²-off-grid / weighted awayBound)
```

together with the near-side bound.  The numerics do *not* contradict this: the
`L²` mass `∑|τ₁|² ≈ n log log n` is small enough that a power saving off the grid
is plausible, exactly as in b1-b4.

## Milestone 6: Fourier orthogonality (foundation of the weighted Parseval identity)

Verified this round:

```lean
integral_phase_int (k : ℤ) :
  ∫_{0}^{1} phase (k t) dt = if k = 0 then 1 else 0

integral_phase_sub (a b : ℕ) :
  ∫_{0}^{1} phase (a t) * conj (phase (b t)) dt = if a = b then 1 else 0
```

The first is the orthogonality of the Fourier modes, proved exactly like the
verified `integral_E_circle`.  The second follows from the first via
`conj (phase x) = phase (-x)` and `phase_add`.

### Why this matters: the weighted Parseval identity

The far side of the b1-b4 proof consumes the unweighted identity
`∫ |wave u l r|² = r - l`.  For a `Λ`-weighted progression the correct value is

```text
∫ |wwave c u l r|² = ∑_{h ∈ (l,r]} ‖c h‖² .
```

With `integral_phase_sub`, the proof is a two-line computation once the double
sum is written out:

```text
‖wwave t‖² = ∑_{h,h'} c h · conj (c h') · phase ((h - h') u t)
∫ ‖wwave‖² = ∑_{h,h'} c h · conj (c h') · [h = h'] = ∑_h ‖c h‖² .
```

(The bookkeeping that remains is the `normSq` ⇄ `‖·‖²` ⇄ `z * conj z` rewrite and
the collapse `[(h - h') u = 0] = [h = h']` for `u > 0`.)

### Where the `∫_{gridᶜ}|S_{τ₁}|²` programme stands

| ingredient | status |
|---|---|
| atom expansion `S_{τ₁} = ∑_a c(a) wwave Λ a U (n/a)` | ✅ |
| exact far/near split `deepIntegral_split` | ✅ |
| orthogonal modes `integral_phase_int/sub` | ✅ |
| weighted Parseval `∫‖wwave‖² = ∑‖c h‖²` | next (computation outlined above) |
| weighted `L²` off-grid (`awayBound` analogue) | open — needs a large-sieve/second-moment input |
| near field: `wwave ≈ ∑ Λ h` on the window (error `π/(4M)`) | sketched, not formalised |

## Milestone 7: weighted Parseval (the `L²` workhorse)

```lean
integral_wwave_norm_sq (c) (hu : 0 < u) (l r) :
  ∫_{0}^{1} ‖wwave c u l r t‖² dt = ∑_{h ∈ (l,r]} ‖c h‖²

integral_wwave_mangoldt_norm_sq (u l r) (hu : 0 < u) :
  ∫_{0}^{1} ‖wwave Λ u l r t‖² dt = ∑_{h ∈ (l,r]} Λ(h)²

integral_tauCoeff_norm_sq (n) :
  ∫_{0}^{1} ‖plainPolynomial n (tauCoeff n) t‖² dt = ∑_{m ≤ n} ‖tauCoeff n m‖²
```

Proof of the first: reindex the progression over the fibre map `h ↦ h·u`
(`Finset.sum_fiberwise_of_maps_to`), apply the module's Fourier Parseval
`DyadicMixedB4Fourier.parseval_real`, and collapse
`∑_m ‖∑_{h·u = m} c h‖² = ∑_h ‖c h‖²` using injectivity of `h ↦ h·u` for
`u > 0` (so each fibre has at most one element).  The second and third are
immediate corollaries.

This is the exact replacement for the module's unweighted `∫|wave u l r|² = r − l`.
In particular

```text
∫_{gridᶜ} |S_{τ₁}|²  ≤  ∑_m |τ₁(m)|²  =  ∫_{0}^{1} |S_{τ₁}|² .
```

### Programme status

| ingredient | status |
|---|---|
| atom expansion `S_{τ₁} = ∑_a c(a)·wwave Λ a U (n/a)` | ✅ |
| exact far/near split `deepIntegral_split` | ✅ |
| Fourier-mode orthogonality `integral_phase_int/sub` | ✅ |
| weighted Parseval `∫‖wwave‖² = ∑‖c h‖²` | ✅ |
| near field: `wwave ≈ ∑ Λ h` on the window, error `π/(4M)` | next |
| weighted `L²` off-grid (`awayBound` analogue) | open — needs a second-moment/large-sieve input |

## Milestone 8: the near field is NOT "constant on the window" (correction)

I previously claimed that on the window `|x| ≤ radius M` the weighted progression
is essentially its total mass, with relative error `π/(4M)`.  **That was wrong** —
it dropped the `h` factor.  The verified honest statement is

```lean
wwave_mangoldt_sub_total_norm_le (u l r) (t) :
  ‖wwave Λ u l r t - ∑_{h ∈ (l,r]} Λ h‖
    ≤ 2π|t| · ∑_{h ∈ (l,r]} (u h) · Λ h
```

and `∑_{h ≤ N} h Λ h ≈ N²/2` against `∑_{h ≤ N} Λ h ≈ N`, so the relative error is

```text
≈ (π/2) · u · N · |t| = (π/2) n |t|      (since u N = n).
```

On the full window `|t| ≤ radius M = 1/(8M²)` with `M = maximumStep ≈ n^(19/48)`
this is `≈ n^(5/24)`, i.e. **huge**.  So the constant approximation is only valid on
the archimedean core

```text
|t| ≲ 1/n ,
```

and the rest of the annulus (`1/n ≤ |t| ≤ radius M`) genuinely needs the
oscillation / window-kernel analysis — which is precisely the `sineKernel` /
`scalarKernel` / `windowKernel` / `DyadicMixedB4Abel` stack that the verified
`b3-b4` module adds on top of `b1-b4` (the extra ~2200 lines).

So the near field splits as

```text
core   |x| ≤ 1/n        : wwave ≈ ∑ Λ h            (proved here)
annulus 1/n ≤ |x| ≤ ρ_q : ∫ e(k t) wwave  — window kernel, Ramanujan weights
```

which is the classical major-arc structure, and the verified `windowKernel`
machinery is exactly what handles the annulus.

### Programme status

| ingredient | status |
|---|---|
| atom expansion `S_{τ₁} = ∑_a c(a)·wwave Λ a U (n/a)` | ✅ |
| exact far/near split `deepIntegral_split` | ✅ |
| Fourier-mode orthogonality `integral_phase_int/sub` | ✅ |
| weighted Parseval `∫‖wwave‖² = ∑‖c h‖²` | ✅ |
| near core: `wwave = ∑ Λ h + O(2π|t|∑ h Λ h)` | ✅ |
| near annulus: window-kernel analysis | open (machinery exists in `b3-b4`, needs weighted port) |
| weighted `L²` off-grid (`awayBound` analogue) | open (needs second-moment/large-sieve input) |

## Milestone 9: archimedean decay of the window transform

Verified this round:

```lean
norm_integral_phase_osc (k : ℤ) (hk : k ≠ 0) {A B : ℝ} :
  ‖∫_{A}^{B} phase (k t) dt‖ ≤ 1 / (π |k|)

integral_ball_eq {ρ} (hρ : 0 ≤ ρ) (f) :
  ∫_{|x| ≤ ρ} f x dx = ∫_{-ρ}^{ρ} f x dx

norm_integral_ball_phase_le (k) (hk) (hρ : 0 ≤ ρ) :
  ‖∫_{|x| ≤ ρ} phase (k t) dt‖ ≤ 1 / (π |k|)

norm_integral_annulus_phase_le (k) (hk) (0 ≤ inner ≤ ρ) :
  ‖∫_{inner ≤ |x| ≤ ρ} phase (k t) dt‖ ≤ 2 / (π |k|)
```

The last one is the shape of the `window` (`= ball (radius M) \ ball inner`),
and it is the basic archimedean input of the near side.

### Consequence for the near side

Summing over the weighted progression gives the honest window bound

```text
|∫_{window q} phase (k t) · wwave Λ a U N t dt|
  ≤ ∑_{h ∈ (U, N]} Λ h · 2/(π |k + a h|) .
```

So a single window costs at least `≈ 1/|k|`, and summing over `h` gives
`≈ log²/a`.  Hence the near side cannot be closed by the window transform alone:
it must exploit the cancellation in the `m`-sum

```text
∑_m τ₁(m) · c_q(m - n)
```

which is exactly the Ramanujan / primitive-character large sieve step of the
verified `b1-b4` / `b3-b4` proofs.

### Programme status

| ingredient | status |
|---|---|
| atom expansion, exact far/near split | ✅ |
| Fourier orthogonality, weighted Parseval | ✅ |
| near core `wwave = ∑ Λ h + O(2π\|t\|∑ h Λ h)` | ✅ |
| archimedean window decay (ball/annulus) | ✅ |
| near annulus: weighted character large sieve | open (machinery exists in `b3-b4`) |
| weighted `L²` off-grid (`awayBound` analogue) | open (second-moment input) |

## Milestone 10: the exact reduction `Jdeep = D - W`

Verified this round:

```lean
def diagonalSum (n) := ∑_{m, m' ≤ n} if m + m' = n then τ₁(m) τ₁(m') else 0

plainPolynomial_sq_expand (n) (t) :
  S(t)² e(-n t) = ∑_{m, m' ≤ n} τ₁ m τ₁ m' · e(((m + m') - n) t)

integral_sq_phase_eq_diagonal (n) :
  ∫_{0}^{1} S(t)² e(-n t) dt = diagonalSum n

deepIntegral_eq_diagonal_sub_wide (n) :
  Jdeep n = diagonalSum n
              - ∫_{0}^{1} (wideSet n).indicator (S(t)² e(-n t)) dt
```

So the target `Jdeep = o(n)` is *exactly* the statement

```text
D  -  W  =  o(n) ,      D = ∑_{m + m' = n} τ₁(m) τ₁(m') ,   W = ∫_{wideArcs} S² e(-n·) .
```

Numerically `D/n ≈ 3.7, 2.4, 3.6, 5.3` for `n = 10^4 … 10^7` (and `D ≈ 2 n θ²` with
`θ = ∑ c(a)/a ≈ -log B₁ log log B₁`), so `Jdeep = o(n)` is a **main-term matching**
statement: `W` must reproduce `D` to relative accuracy `o(1)`.

## Warning on the far-side programme

My earlier proposal — "show `∫_{gridᶜ} |S_{τ₁}|² ≪ n^{1-δ}`" — now looks
**doubtful**, and I did not build on it.  Order-of-magnitude reasoning for a single
atom `a`:

* total mass `∫ |wwave Λ a U (n/a)|² = ∑_{h ≤ n/a} Λ(h)² ≈ (n/a) log(n/a)`;
* grid mass `∫_{grid_a} |wwave|²`: on the grid `‖a t‖ ≤ a·radius M ≈ n^{-13/24}`, so
  the progression is coherent only up to `h ≲ n^{13/24}`, giving
  `|wwave| ≈ n^{13/24}` on a set of measure `≈ a·n^{-19/24}`, i.e. mass
  `≈ n^{13/24}·a·n^{-19/24} = a·n^{-1/4}` — negligible against `(n/a)log(n/a)`.

If that is right, the grid removes almost none of the mass, and the far part is
`≈ ‖S_{τ₁}‖₂ ‖G‖₂ ≈ n·log^{Θ(1)}` — **not** `o(n)`.  In `b1-b4` the mechanism works
only because `τ₄`'s waves are short (`cofactor < n^{1/3}`), so their mass *is*
concentrated on the grid.  `τ₁` has no short cofactor, so the far/near split alone
cannot close b1-b1: the saving has to come from the `D`-`W` main-term cancellation
itself.

This should be checked (it is a paper computation), and it changes what the next
investment should be: either the main-term computation of `W` on the wide arcs, or
a genuinely new dispersion argument.  I am flagging it rather than porting thousands
of lines into a bound that may be false.

## Milestone 11: the far/near split provably cannot close b1-b1

I checked the warning of the previous milestone, analytically and numerically.

### Analytic

For one atom `a` with `N = n/a`, put `V(θ) = ∑_{h ∈ (U,N]} Λ(h) e(θ h)`.  On the
grid intervals `t = j/a + x`,

```text
wwave Λ a U N (t) = V(a x) ,
```

so

```text
∫_{grid_a} |wwave|²  =  ∫_{|θ| ≤ a·radius M} |V(θ)|² dθ ,
∫_{0}^{1}  |wwave|²  =  ∑_{h ≤ N} Λ(h)²  ≈  N log N .
```

The crude bound `|V| ≤ ψ(N) ≈ N` on the grid gives

```text
∫_{grid_a} |wwave|² ≤ 2·a·radius M · N² = n²/(4 a M²) ,
```

hence `‖G‖₂² ≤ n²/(4M²)·∑_a τ(a)²/a ≈ n^(29/24) log³` and
`far ≤ ‖S‖₂‖G‖₂ ≈ n^(53/48) log^(5/2)` — **larger than `n`**.  Using instead the
oscillation bound `|V(θ)| ≲ 1/‖θ‖` gives `∫_{grid_a} ≲ N`, so
`‖G‖₂² ≲ n∑_a τ(a)²/a ≈ n log³`, and `far ≲ n log^(5/2)`.  Either way the far part
is `n·log^{Θ(1)}`, **not** `o(n)`.

### Numerical (`vmass_numerics.py`)

`R(δ) := ∫_{|θ| ≤ δ}|V(θ)|²dθ / ∫₀¹|V|²` for `N = 2·10^4`:

| δ | δ·N | R(δ) |
|---|---|---|
| 0.001 | 20 | 0.2247 |
| 0.003 | 60 | 0.2278 |
| 0.010 | 200 | 0.2400 |
| 0.030 | 600 | 0.5128 |

(The `0.3`/`0.1` rows are unreliable: the spikes have width `1/N = 5·10^-5`, far
below the sampling step.)  In the b1-b1 regime `a·radius M·N = n/(8M²) = n^(5/24)/8`,
which for `n ≳ 10^16` is `≈ 10^3`, so `R ≈ 0.25`: **the grid captures only about a
quarter of the `L²` mass**, and `∫_{gridᶜ}|S_{τ₁}|² = Θ(n log^{1+o(1)})`.

### Conclusion

The verified `b1-b4` far/near mechanism **cannot** prove b1-b1: for `τ₄` the grid
captures essentially all the mass (short waves), for `τ₁` it captures only `1/log`
of it.  Since the off-grid mass is a positive fraction of `n log`, no absolute-value
bound on the far part can be `o(n)`; the saving has to come from the **signed**
cancellation `D - W = o(n)`, i.e. the main-term route (b) proper.

`b1-b1` therefore reduces to:

```text
W  =  D + o(n) ,      W = ∫_{wideArcs} S² e(-n·) ,   D = ∑_{m+m'=n} τ₁(m) τ₁(m') .
```

i.e. the classical major-arc main-term computation (singular series × archimedean
factor) with enough precision to cancel `D ≈ 2 n θ²`, `θ = ∑ c(a)/a`.

## Milestone 12: the `L²` size of `S_{τ₁}`

Verified this round:

```lean
sum_vonMangoldt_div_divisors (m) :
  ∑_{a | m} Λ(m/a) = log m

tauCoeff_abs_le (n m) {T} (0 ≤ T)
    (hc : ∀ a, U < a → a ≤ B₁ → |c(a)| ≤ T) :
  ‖τ₁(m)‖ ≤ T · log m

integral_tauCoeff_norm_sq_le (n) (0 < n) (0 ≤ T)
    (hc : ∀ a, U < a → a ≤ B₁ → |c(a)| ≤ T) :
  ∫_{0}^{1} ‖S_{τ₁}(t)‖² dt ≤ T² (n+1) (log n)²
```

The middle one is the pointwise bound `|τ₁(m)| ≤ T ∑_{a|m}Λ(m/a) = T log m`
(using `∑_{d|m} Λ(d) = log m`), and the last is its `L²` consequence via the
verified weighted Parseval `∫‖S‖² = ∑|τ₁|²`.

These are the two `F`-side inputs of any far estimate: a pointwise bound
`aBound : ∀ m, ‖τ₁(m)‖ ≤ A` and `‖S_{τ₁}‖₂² ≤ A² n`.

### Running status of the b1-b1 dossier

| layer | content | status |
|---|---|---|
| task definitions | `τ₁ = lowBandCoefficient`, `wideArcs = wide cutoffB cutoffH` | ✅ |
| atom expansion | `S_{τ₁} = ∑_a c(a) wwave Λ a U (n/a)` | ✅ |
| weighted far/near split | `deepIntegral_split` (exact) | ✅ |
| Fourier toolkit | orthogonality, weighted Parseval, archimedean ball/annulus decay | ✅ |
| exact reduction | `Jdeep = D − W` | ✅ |
| coefficient sizes | `|τ₁(m)| ≤ T log m`, `∫‖S‖² ≤ T² n log²` | ✅ |
| decisive negative | far/near cannot give `o(n)` (off-grid carries ~3/4 of `n log`) | ✅ |
| **what remains** | **`W = D + o(n)`**: major-arc main-term computation for `τ₁` | open |

The remaining step needs the major-arc approximation
`S(a/q + β) ≈ (1/q)(∑_{r mod q} e(ar/q)) v(β)` with `v(β) = ∑_m τ₁(m) e(mβ)`,
i.e. equidistribution of `τ₁` in residue classes modulo `q ≤ n^(1/3)` — a
Siegel–Walfisz-type input for the Möbius/divisor coefficient.  That is the
genuine research content of the cell, and the reason it is marked `challenge_only`.

## Milestone 13: the bridge to the prime-indicator major-arc model

Verified this round:

```lean
def primeWave (a U N) (t) :=
  ∑_{k ∈ (U,N]} (if k prime then log k else 0) · e(a k t)

def primePowerCorrection (a U N) (t) :=
  ∑_{k ∈ (U,N]} (Λ k - (if k prime then log k else 0)) · e(a k t)

atomWave_eq_primeWave_add_correction :
  atomWave a U N t = primeWave a U N t + primePowerCorrection a U N t

primePowerCorrection_norm_le :
  ‖primePowerCorrection a U N t‖ ≤ ∑_{k ∈ (U,N]} if k prime then 0 else Λ k

plainPolynomial_tauCoeff_prime_split :
  S_{τ₁}(t) = ∑_a c(a) · primeWave a U (n/a) t
                + ∑_a c(a) · primePowerCorrection a U (n/a) t
```

So `S_{τ₁}` is a finite combination of **dilated prime sums** plus a
prime-power correction.  This is the bridge to the verified major-arc model
`L_goldbach_frontier_medcore_bv_band` (and `spatial_lowmod_model_match`),
which are stated for `S n w` with `w = ` prime indicator.

### What remains, precisely

1. **Dilation**: `primeWave a U N (t) = S N w (a t)` up to the `k ≤ U` truncation
   (`∑_{k ≤ U} w k ≈ n^(1/16)`) and the `N = n/a` truncation.
   On the arc `t = a₀/q + β`, `a t` sits on the arc around `a a₀/q` with reduced
   denominator `q / gcd(a,q)`, so the model must be summed over the fibre.
2. **Apply the model** to each dilated prime sum, expand the square, and use
   the verified `bandRamanujan` / `K n` machinery.
3. **Bound `D`** by the same computation (it is the `q = 0` / full-circle term)
   and show the difference is `o(n)`.

### Dossier summary (13 verified milestones, 1091 lines, no `sorry`)

| layer | content |
|---|---|
| definitions | `τ₁ = lowBandCoefficient`, `wideArcs`, `tauCoeff`, `diagonalSum` |
| atom/prime structure | `plainPolynomial_tau1`, `primeWave`, `primePowerCorrection`, `…_prime_split` |
| weighted analysis | `wwave`, `woffWave`, `centered_deep_wwave_integral`, `split_shifted_wwave` |
| Fourier toolkit | `integral_phase_int/sub`, `integral_wwave_norm_sq`, ball/annulus decay |
| exact reduction | `deepIntegral_split`, `deepIntegral_eq_diagonal_sub_wide` |
| size bounds | `|τ₁(m)| ≤ T log m`, `∫‖S‖² ≤ T² n log²` |
| numerical evidence | `theta_numerics.py`, `vmass_numerics.py` |
| decisive negative | far/near cannot reach `o(n)` |

The remaining step is the major-arc model application — a substantial but
*standard* computation, with the prime-indicator version already verified in the
catalogue.

## Milestone 14: the dilation bridge is complete

```lean
def primeSum (N : ℕ) (θ : ℝ) : ℂ :=
  ∑_{k ≤ N} (if k prime then log k else 0) · e(k θ)

primeWave_eq_dilated (a U N) (hU : U ≤ N) :
  primeWave a U N t = primeSum N (a·t) - primeSum U (a·t)

plainPolynomial_tauCoeff_dilated (n) (hUa : ∀ a, U < a ≤ B₁ → U ≤ n/a) :
  S_{τ₁}(t)
    = ∑_{a ∈ (U,B₁]} c(a) · primeSum (n/a) (a·t)
    - ∑_{a ∈ (U,B₁]} c(a) · primeSum U (a·t)
    + ∑_{a ∈ (U,B₁]} c(a) · primePowerCorrection a U (n/a) t
```

`primeSum N` is *exactly* the object of the verified major-arc model
(`L_goldbach_frontier_medcore_bv_band` writes `S n w t = ∑_{k ≤ n} w(k) e(k t)`
with `w(k) = if k prime then log k else 0`).  So `S_{τ₁}` is now expressed as

```text
S_{τ₁}(t)  =  ∑_a c(a) S_{n/a} w (a t)   -   (short truncation)   +   (prime powers)
```

and the model can be applied term by term.

### Concrete remaining steps

1. **Model on each dilated arc.** On `t = a₀/q + β` with `q ∈ (n^(1/10), n^(1/3)]`,
   `a t` sits near `a a₀ / q`, whose reduced denominator is `q / gcd(a,q)`.
   Since `a ≤ B₁ = n^(1/4)` and `q > n^(1/10)`, the product `q·a` can exceed `Q₁`,
   so the fibre split over `gcd(a,q)` is needed.
2. **Expand the square** and use the verified `bandRamanujan` / `K n` formulas.
3. **Match against `D`** (the full-circle term) to get `o(n)`.

Steps 1-3 are a large but standard major-arc computation.  The verified pieces are:
`L_goldbach_frontier_medcore_bv_band` (band model for `S n w`),
`L_goldbach_frontier_spatial_lowmod_model_match` (small moduli),
`L_goldbach_frontier_spatial_macro_sinc_tail` (archimedean tail),
`bandRamanujan`, `K n` formulas.

## Milestone 15: interface lemma, and the full architecture located in the catalogue

```lean
primeSum_eq_module (N) (θ) :
  primeSum N θ = ∑_{k ≤ N} ↑(if k prime then log k else 0) · phase (k θ)
```

i.e. `primeSum` is literally the module's `S n w`.

### The catalogue already contains the whole minor-arc architecture (for `w`)

| module | lines | statement |
|---|---|---|
| `frontier_spatial_exact_split` | 697 | **exact** identity `minor = diag − offLowNear − offLowFar − offHighMod`, `minor = ∫_{(arcs)ᶜ}(S n w)²e(-n·)`, `arcs` = polylog (radius `Q²/(qn)`, `q ≤ Q²`) |
| `frontier_spatial_lowmod_model_match` | 7432 | `offLowNear = seriesLow + O(εn)`, `seriesLow = n ∑_{q ≤ log₂(n+2)} (μ(q)²/φ(q)²) ∑_a cos(2πna/q)` — **the singular series** |
| `frontier_spatial_macro_sinc_tail` | 6094 | `offLowFar = O(εn)` |
| `frontier_medcore_bv_band` | 1710 | medium-band model for `S n w` (Bombieri–Vinogradov) |

So the entire binary/ternary Goldbach minor-arc computation is formalised for the
**prime indicator** `w`: exact decomposition, singular series, and both tail
estimates.

### Consequence for b1-b1

The b1-b1 task is exactly the same architecture with `w` replaced by
`τ₁ = c * Λ` (equivalently `c * w` modulo prime powers, which the verified
`primePowerCorrection` controls).  Concretely:

1. port `spatial_exact_split` (an *exact* identity: expand `(S_{τ₁})²e(-n·)` over
   frequencies `m₁ + m₂ - n`, integrate over `arcsᶜ`, collect `sincKernel`);
2. port `lowmod_model_match` for the new coefficient — the local densities become
   `∑_a c(a)`-weighted sums instead of `1`;
3. port `macro_sinc_tail`.

This is a large but *known* port with a verified template, and the hard analytic
inputs (singular series, tail) are already solved in the `w` case.

### Dossier

15 verified milestones, 1132 lines, no `sorry`, branch `research/b1b1-arcsplit`.

## Milestone 16: the weighted phase-quadruple expansion (in the `exact_split` form)

```lean
wwave_pair_expand (c c') (a a') (U U' N N') (n) (t) :
  wwave c a U N t * wwave c' a' U' N' t * phase (-(n t))
    = ∑_{j ∈ (U,N]} ∑_{k ∈ (U',N']} c j c' k · phase ((a j + a' k - n) t)

plainPolynomial_sq_dilated_expand (n) (t) :
  S_{τ₁}(t)² e(-n t)
    = ∑_{a, a' ∈ (U,B₁]} c(a) c(a') ·
        ∑_{j ∈ (U, n/a]} ∑_{k ∈ (U, n/a']} Λ(j) Λ(k) ·
          e((a j + a' k - n) t)
```

(The second is the catalogue's verified `L-goldbach-frontier-type2-b1-b1-phase-quadruple-expansion`
re-derived in the `wwave`-factorised form that the integral stage consumes.)

This is the input of the `spatial_exact_split` port: integrating over the arc
complement now collects, for each quadruple `(a, a', j, k)`, the sinc kernel

```text
∫_{arcsᶜ} e((a j + a' k - n) t) dt
  = [a j + a' k = n] - ∑_{q} (Ramanujan cosine sum) · sinc(...)
```

with the frequency `m = a j + a' k - n` replacing `j + k - n` of the `w` case.

### Remaining port (honest scale)

The `w`-version is ~15k verified lines (`exact_split` 697, `lowmod_model_match`
7432, `macro_sinc_tail` 6094, `medcore_bv_band` 1710).  The `τ₁`-version is the
same architecture with `m = a j + a' k - n` in place of `m = j + k - n`, so:

1. `exact_split` port — exact identity, mechanical but long;
2. local densities: `1/φ(q)²` becomes `(∑_a c(a) ρ_a)²`-shaped sums;
3. archimedean tail: same form, extra `a`-sums.

This is a multi-session engineering project with a verified template, not an
open problem.

## Milestone 17: the archimedean sinc factor

```lean
integral_phase_symmetric_exp (m) (hm : m ≠ 0) (ρ) :
  ∫_{-ρ}^{ρ} e(m β) dβ = (e(2πi m ρ) - e(-2πi m ρ)) / (2πi m)

integral_phase_symmetric (m) (hm : m ≠ 0) (ρ) :
  ∫_{-ρ}^{ρ} e(m β) dβ = sin (2π m ρ) / (π m)

integral_ball_phase_eq_sinc (m) (hm) (hρ : 0 ≤ ρ) :
  ∫_{|x| ≤ ρ} e(m x) dx = sin (2π m ρ) / (π m)
```

The last is exactly the archimedean factor of the verified `sincKernel`
(`sin(2π m Q/(q n))/(π m)`), so the `exact_split` port can now collect it directly.

## Milestone 18: the arc split and the per-arc sinc factor

Ported from `arcsplit.lean` into the port file (now with `wideSet = wide cutoffB cutoffH`
and `logSq n = (log₂(n+2))²`):

```lean
arcSet n q a          -- the arc centred at a/q with radius cutoffH n/(q n)
arcSet_measurable
mem_wideSet_iff       -- membership in the arc-family form
fraction_inj          -- reduced fractions are injective
radius_sum_lt         -- Farey spacing vs. the radius sum
arcs_disjoint         -- the wide arcs are pairwise disjoint
arcSet_unique         -- a point lies in at most one arc
wideSet_indicator_eq_sum / integral_wideSet_eq_sum
                      -- ∫_{wideSet} f = ∑_{q,a} ∫_{arcSet q a} f
```

New:

```lean
arcSet_eq_Icc (n q a) :
  arcSet n q a = Icc (a/q - H/(qn)) (a/q + H/(qn))

integral_arcSet_phase (n q a) (m) (hm : m ≠ 0) :
  ∫_{arcSet n q a} e(m t) dt
    = e(m · a/q) · sin (2π m · H/(q n)) / (π m)
```

The last is exactly one term of the verified `sincKernel`
(`cos(2π m a/q) · sin(2π m Q/(q n))/(π m)` up to the `e` vs `cos` convention).

### Remaining to finish the `sincKernel` collection

The `wideSet` includes the arcs at `0/1` and `1/1`, which stick out of `[0,1]`;
so the clipped integral `∫₀¹ 1_{arc} e(m t)` equals the full `∫_{arcSet}` except
for the two boundary arcs, whose excess is an explicit finite term.  After
accounting for that (and using `arcs_disjoint`),

```text
∫_{(wideSet)ᶜ} e(m t) dt  =  [m = 0]  -  ∑_{q ≤ cutoffB n} ∑_{a, (a,q)=1}
                                e(m a/q) · sin(2π m H/(q n)) / (π m)   +  boundary term
```

which is the `τ₁`-version of `spatial_exact_split`'s sinc collection.

## Milestone 19: clipping lemma and the sinc sum

```lean
integral_arcSet_indicator_phase_of_inside (n q a) (m)
    (hleft : 0 < a/q - H/(qn)) (hright : a/q + H/(qn) < 1) :
  ∫_{0}^{1} 1_{arcSet n q a} e(m t) dt = ∫_{arcSet n q a} e(m t) dt

sum_arcSet_phase (n) (m) (hm : m ≠ 0) :
  ∑_{q ≤ cutoffB n} ∑_{a, (a,q)=1} ∫_{arcSet n q a} e(m t)
    = ∑_{q} ∑_{a} e(m a/q) · sin (2π m H/(q n)) / (π m)
```

The first says a strictly interior arc is not clipped by `[0,1]`; the second is the
`sincKernel` sum in closed form.

### Remaining for the complete sinc collection

Only the two boundary arcs `(q,a) = (1,0)` and `(1,1)` remain.  By `1`-periodicity
of `e(m·)`, their clipped contributions combine to exactly
`∫_{-ρ_1}^{ρ_1} e(m t) dt = sin(2π m H/n)/(π m)`, i.e. the *same* sinc term.  So
after that one lemma,

```text
∫_{0}^{1} 1_{wideSet n} e(m t) dt
  = ∑_{q ≤ cutoffB n} ∑_{a, (a,q)=1} e(m a/q) · sin(2π m H/(q n))/(π m)
```

and hence (using `∫_{0}^{1} e(m t) dt = [m=0]` for `m ≠ 0`)

```text
∫_{(wideSet n)ᶜ} e(m t) dt = - ∑_{q,a} e(m a/q) sin(2π m H/(q n))/(π m) .
```

That is the `τ₁`-analogue of `spatial_exact_split`'s sinc collection.

## Milestone 20: the boundary arcs combine by periodicity

```lean
phase_int (k : ℤ) : phase (k : ℝ) = 1

integral_boundary_arcs (m : ℤ) (ρ : ℝ) :
  ∫_{0}^{ρ} e(m t) dt + ∫_{1-ρ}^{1} e(m t) dt = ∫_{-ρ}^{ρ} e(m t) dt
```

The second is the `1`-periodicity statement behind the two boundary arcs
`(q,a) = (1,0)` and `(1,1)`: their clipped pieces together give exactly the full
ball at `0`, hence the same `sinc` term
`sin(2π m ρ₁)/(π m)`.

With `integral_arcSet_indicator_phase_of_inside` (interior arcs are not clipped)
and `sum_arcSet_phase`, the sinc collection is now complete up to the bookkeeping
of separating the `q = 1` case from `q ≥ 2`:

```text
∫_{0}^{1} 1_{wideSet n} e(m t) dt
  = ∑_{q ≤ cutoffB n} ∑_{a, (a,q)=1} e(m a/q) · sin(2π m H/(q n))/(π m) ,
```

hence

```text
∫_{(wideSet n)ᶜ} e(m t) dt = - ∑_{q,a} e(m a/q) sin(2π m H/(q n))/(π m)     (m ≠ 0).
```

## Milestone 21: the complement split

```lean
integral_compl_indicator_phase (n) (m) :
  ∫_{0}^{1} 1_{Aᶜ} e(m t) dt = ∫_{0}^{1} e(m t) dt - ∫_{0}^{1} 1_A e(m t) dt

integral_compl_indicator_phase_eq (n) (m) (hm : m ≠ 0) :
  ∫_{0}^{1} 1_{Aᶜ} e(m t) dt = - ∫_{0}^{1} 1_A e(m t) dt
```

Together with `integral_wideSet_eq_sum`, `integral_arcSet_phase`,
`integral_arcSet_indicator_phase_of_inside` and `integral_boundary_arcs`, every
ingredient of the sinc collection is now in place; only the case split
`q = 1` vs `q ≥ 2` remains to be written out.

## Full dossier at this point (21 verified milestones)

| # | content |
|---|---|
| 1 | deep-minor definitions, `Target` |
| 2-4 | weighted far/near split (`wwave`, `centered_deep_wwave_integral`, `split_shifted_wwave`) |
| 5 | `deepIntegral_split` (exact, atom by atom) |
| 6-7 | Fourier orthogonality, weighted Parseval |
| 8-9 | archimedean decay (ball/annulus), near-core error term |
| 10 | `Jdeep = D - W` |
| 11 | numerics: `D = Θ(n loglog²)`, off-grid carries ~3/4 of the `L²` mass |
| 12 | coefficient sizes `|τ₁(m)| ≤ T log m`, `∫‖S‖² ≤ T² n log²` |
| 13-14 | prime/major-arc split, dilation bridge `S_{τ₁} = ∑_a c(a) S_w(a·)` |
| 15 | `primeSum = S n w` interface |
| 16 | weighted phase-quadruple expansion |
| 17 | archimedean sinc factor `∫_{|x|≤ρ} e(m x) = sin(2πmρ)/(πm)` |
| 18 | wide-arc disjointness / integral split, per-arc sinc |
| 19 | clipping lemma, sinc sum over the arc family |
| 20 | boundary arcs combine by periodicity |
| 21 | complement split `∫_{Aᶜ} = [m=0] - ∫_A` |

Remaining (all porting, with verified templates):
* finish the `q = 1` case split of the sinc collection;
* multiply into `plainPolynomial_sq_dilated_expand` (the `τ₁` `exact_split`);
* port `lowmod_model_match` (local densities `1/φ(q)² → (∑_a c(a)…)²`);
* port `macro_sinc_tail`.

## Milestone 22: the `q = 1` boundary case

```lean
integral_arcSet_one_zero (n) (m) (0 ≤ ρ) (ρ < 1) :
  ∫_{0}^{1} 1_{arcSet n 1 0} e(m t) dt = ∫_{0}^{ρ} e(m t) dt          -- ρ = H/n

integral_arcSet_one_one (n) (m) (0 ≤ ρ) (ρ < 1) :
  ∫_{0}^{1} 1_{arcSet n 1 1} e(m t) dt = ∫_{1-ρ}^{1} e(m t) dt

sum_arcSet_one (n) (m) (hm : m ≠ 0) (0 ≤ ρ) (ρ < 1) :
  ∑_{a ∈ {0,1}} ∫_{0}^{1} 1_{arcSet n 1 a} e(m t) dt
    = sin (2π m ρ) / (π m)
```

The last is the `q = 1` contribution in closed form, using
`integral_boundary_arcs` and `integral_phase_symmetric`.

### What remains for the complete sinc collection

Only `q ≥ 2`: for those `a` is coprime and `a ≤ q` forces `1 ≤ a ≤ q-1`,
`ρ_q = H/(qn) < 1/q`, so the arc lies strictly inside `(0,1)` and
`integral_arcSet_indicator_phase_of_inside` + `integral_arcSet_phase` apply
(hypotheses: `H < n`).  Splitting `Icc 1 Q₁ = {1} ∪ Icc 2 Q₁` then gives

```text
∫_{0}^{1} 1_{wideSet n} e(m t) dt
  = ∑_{q ≤ cutoffB n} ∑_{a ∈ [1,q), (a,q)=1} e(m a/q) · sin(2π m H/(q n))/(π m)
```

and hence, by `integral_compl_indicator_phase_eq`,

```text
∫_{(wideSet n)ᶜ} e(m t) dt = - ∑_{q,a} e(m a/q) sin(2π m H/(q n))/(π m)   (m ≠ 0).
```

## Milestone 23: interior arcs and the interior sinc sum

```lean
integral_arcSet_clipped_eq_sinc (n q a) (m) (hm : m ≠ 0)
    (hleft : 0 < a/q - H/(qn)) (hright : a/q + H/(qn) < 1) :
  ∫_{0}^{1} 1_{arcSet n q a} e(m t) dt
    = e(m a/q) · sin(2π m H/(q n))/(π m)

sum_arcSet_phase_interior (n) (m) (hm) (hint : ∀ q ∈ Icc 2 Q₁, ∀ a, interior) :
  ∑_{q ∈ Icc 2 Q₁} ∑_{a} ∫_{0}^{1} 1_{arcSet n q a} e(m t)
    = ∑_{q ∈ Icc 2 Q₁} ∑_{a} e(m a/q) sin(2π m H/(q n))/(π m)
```

Together with `sum_arcSet_one` (the `q = 1` contribution), every per-index piece
of the sinc collection is now verified.  The only thing left is the pure
bookkeeping:

* split `Icc 1 (cutoffB n) = {1} ∪ Icc 2 (cutoffB n)`;
* note `(range (q+1)).filter (Coprime · q) = (range q).filter (Coprime · q)` for
  `q ≥ 2` (since `¬ Coprime q q`);
* discharge the interior hypotheses from `1 ≤ a ≤ q-1` and `H < n`.

### Assessment at this point

The dossier (23 verified milestones, 1726 lines, no `sorry`) contains every
structural ingredient of the `τ₁` circle-method computation:

| layer | verified content |
|---|---|
| definitions | `τ₁`, `wideArcs`, `tauCoeff`, `diagonalSum`, `primeSum`, `primeWave`, `primePowerCorrection` |
| atom/prime structure | `plainPolynomial_tau1`, `prime/major-arc split`, dilation bridge, weighted quadruple expansion |
| weighted analysis | `wwave`, `woffWave`, split lemmas, weighted Parseval |
| Fourier/archimedean | orthogonal modes, ball/annulus decay, sinc factor |
| arcs | disjointness, integral split, per-arc sinc, clipping, boundary, interior |
| global reductions | `deepIntegral_split`, `Jdeep = D - W`, complement split |
| sizes | `|τ₁(m)| ≤ T log m`, `∫‖S‖² ≤ T² n log²` |
| numerics | `D = Θ(n loglog²)`, off-grid carries ~3/4 of `L²` |
| negative | far/near cannot reach `o(n)` |

Remaining: the assembly of the sinc collection, then the `τ₁` `exact_split`, then
the ports of `lowmod_model_match` and `macro_sinc_tail`.

## Milestone 24: repository update — a new verified large sieve, and a heartbeat fix

### `maxHeartbeats` (important)

The port file is compiled with `lake env lean <path>`, which does **not** apply the
project's `leanOptions` (`maxHeartbeats = 4000000` from `leanfile.toml`). Several
earlier failures ("deterministic timeout at whnf", and possibly some of the
`simp`-shape mismatches) were caused by the default 200000 limit.  The file now
starts with

```lean
set_option maxHeartbeats 4000000
```

### A newly verified tool: the finite large sieve

`L-goldbach-finite-large-sieve` is **accepted** on the board (`proved: true`) and
proves (source at `~/github.com/fuck-tencent/goldback-artifacts/finite-large-sieve/`)

```lean
theorem L_goldbach_finite_large_sieve (N Q : ℕ) [NeZero Q] (a : ℕ → ℂ) :
  ∑_{r : ZMod Q} ‖∑_{n ≤ N} a n * ZMod.stdAddChar (r * n)‖²
    ≤ (N + Q) * ∑_{n ≤ N} ‖a n‖²
```

together with the `ZMod` Parseval identity.  This is exactly the single-modulus
large sieve needed for the near-side Ramanujan estimates (and for
`∑_q |∑_m a_m c_q(m-n)|²`-type bounds).  It is not yet on local `main`
(`1133bda2`), so it must be imported after merging upstream (now at `513184b2`)
or copied from the artifacts repository.

### Other repository news

* upstream `main` advanced `1133bda2 → 513184b2` (new tasks
  `L-goldbach-adaptive-minor-negative-tail`,
  `L-goldbach-dyn-short-restricted-power-saving`,
  `L-goldbach-short-window-power-exceptions`, …; new proved files
  `L_twin_primes_unconditional_short`, `DynThinWindowExceptions`, …).
* board: 1003 published, 940 accepted, 63 open.
* other sessions' branches in the research repo:
  `proof/finite-large-sieve`, `rebase/finite-large-sieve`,
  `rebase/type2-b1-b1-split` (the latter only adds the four prerequisite task
  JSONs, no Lean).

### New definition this round

```lean
def arcKernel (n : ℕ) (m : ℤ) : ℂ :=
  ∫_{0}^{1} 1_{wideSet n}ᶜ · e(m t) dt
```

so that the quadruple expansion reads
`Jdeep = ∑_{a,a'} c(a)c(a') ∑_{j,k} Λ(j)Λ(k) · arcKernel n (a j + a' k - n)`.
The formal term-by-term integration of `plainPolynomial_sq_dilated_expand` over
`wideSetᶜ` is what remains: the pointwise rewrite goes through, but the final
matching of the two nested-sum shapes (coefficient association) was not closed
this round.

## Milestone 25: the pointwise quadruple expansion with distributed indicator

```lean
deepIntegrand_eq_quadruple_sum (n) (t) :
  1_{wideSet n}ᶜ (S² e(-n·)) t
    = ∑_{a, a' ∈ (U,B₁]} (c a · c a') ·
        ∑_{j ∈ (U, n/a]} ∑_{k ∈ (U, n/a']} (Λ j · Λ k) ·
          1_{wideSet n}ᶜ (e((a j + a' k - n) ·)) t
```

This is the exact pointwise form the `exact_split` integration consumes: after
integrating over `[0,1]` and interchanging the finite sums with the integral
(using `intervalIntegral.integral_finsetSum` and
`indicator_intervalIntegrable`), each quadruple contributes
`arcKernel n (a j + a' k - n)`.

The remaining formal step is the nested `integral_finsetSum` interchange.  The
integrability side conditions need the `convert … using 1; ext x;
simp only [Finset.sum_apply]` pattern for `IntervalIntegrable.sum` (its conclusion
is stated for `∑ i ∈ s, f i` as a function, which is only definitionally the goal's
`fun x => ∑ i ∈ s, f i x`).

## Milestone 26: `Jdeep` as the integral of the expanded quadruple sum

```lean
deepIntegral_eq_integral_quadruple (n) :
  Jdeep n
    = ∫_{0}^{1} ∑_{a, a'} (c a · c a') ∑_{j ∈ (U,n/a]} ∑_{k ∈ (U,n/a']}
        (Λ j · Λ k) · 1_{wideSet n}ᶜ (e((a j + a' k - n)·)) t dt
```

This composes `deepIntegral_eq_task` (the `shiftedPolynomial` form) with the
pointwise quadruple expansion.  The only formal step left before the
`arcKernel` form is the four-level finite-sum interchange

```text
∫ ∑_{a} ∑_{a'} ∑_{j} ∑_{k} F a a' j k t dt
  = ∑_{a} ∑_{a'} ∑_{j} ∑_{k} ∫ F a a' j k t dt ,
```

with integrability of each `(a,a',j,k)` term supplied by
`indicator_intervalIntegrable` + `const_mul`, and the `IntervalIntegrable.sum`
defeq gap closed by `convert … using 1; ext x; simp only [Finset.sum_apply]`.

## Milestone 27: `Jdeep` in quadruple-sum form (`exact_split`, first half done)

```lean
intervalIntegrable_finset_sum' (s) (h) :
  (∀ i ∈ s, IntervalIntegrable (f i)) →
    IntervalIntegrable (fun t => ∑ i ∈ s, f i t)

deepIntegral_eq_quadruple_sum (n) :
  Jdeep n
    = ∑_{a, a' ∈ (U,B₁]} (c a · c a') ·
        ∑_{j ∈ (U, n/a]} ∑_{k ∈ (U, n/a']} (Λ j · Λ k) ·
          arcKernel n ((a j) + (a' k) - n)
```

This is the `τ₁`-analogue of the first half of the verified `spatial_exact_split`:
the deep-minor integral is now an explicit quadruple sum over the atom indices,
each term weighted by the coefficient and by the arc kernel at the frequency
`a j + a' k - n`.

The remaining half is the explicit kernel formula

```text
arcKernel n m = [m = 0] - ∑_{q ≤ cutoffB n} ∑_{a, (a,q)=1}
                  e(m a/q) · sin(2π m H/(q n))/(π m)      (m ≠ 0),
```

whose ingredients are all verified (`integral_phase_symmetric`,
`integral_arcSet_phase`, `integral_arcSet_indicator_phase_of_inside`,
`integral_boundary_arcs`, `sum_arcSet_one`, `integral_compl_indicator_phase_eq`);
only the `q = 1` vs `q ≥ 2` case split remains (with `Nat.coprime_self q` for the
index-set equality).

### Dossier

27 verified milestones, 1811 lines, no `sorry`, branch `research/b1b1-arcsplit`.

## Handover: the next four fixes (all mechanical)

The three theorems attempted last round — `sum_range_one_rhs`,
`integral_wideSet_phase_eq_sinc_range`, `arcKernel_eq_sinc` — failed only on
tactic plumbing.  The exact fixes:

### 1. `hsplit` needs `1 ≤ cutoffB n` and a linear `omega`

```lean
-- add to the theorem's hypotheses:
(hQ : 1 ≤ cutoffB n)

-- and prove:
have hsplit : Finset.Icc 1 (cutoffB n) = insert 1 (Finset.Icc 2 (cutoffB n)) := by
  clear hn hρ0 hρ1          -- (cutoffB n)^2 in hn is non-linear: omega gives up
  ext q
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega
```

`hsplit` is *false* without `hQ` (when `cutoffB n = 0`, the left side is empty and
the right side is `{1}`).

### 2. Same `clear` in `hfilter`

```lean
have hfilter : ∀ q : ℕ, 2 ≤ q →
    (Finset.range (q+1)).filter (fun a => Nat.Coprime a q)
      = (Finset.range q).filter (fun a => Nat.Coprime a q) := by
  intro q hq
  clear hn hρ0 hρ1
  have hins : Finset.range (q+1) = insert q (Finset.range q) := by
    ext a; simp only [Finset.mem_range, Finset.mem_insert]; omega
  rw [hins, Finset.filter_insert, if_neg]
  intro hcop
  have := (Nat.coprime_self q).mp hcop      -- needs the explicit `q`
  omega
```

### 3. Split `Icc 1 Q₁` only once

```lean
rw [integral_wideSet_eq_sum n hn _ hcont, hsplit, Finset.sum_insert hnot1]
```

(`rw [hsplit]` already rewrites *both* occurrences; the second `sum_insert` fails
with "pattern not found".)

### 4. Drop the trailing `ring` in `arcKernel_eq_sinc`

```lean
unfold arcKernel
rw [integral_compl_indicator_phase_eq n m hm]
rw [integral_wideSet_phase_eq_sinc_range n m hm hn hQ hρ0 hρ1 hint]
-- no `ring` needed
```

### What this yields

```lean
arcKernel_eq_sinc (n) (m) (hm : m ≠ 0) (hn) (hQ) (hρ0) (hρ1) (hint) :
  arcKernel n m
    = - ∑ q ∈ Icc 1 (cutoffB n), ∑ a ∈ (range q).filter (Coprime · q),
          e(m a/q) · sin (2π m H/(q n))/(π m)
```

and substituting into `deepIntegral_eq_quadruple_sum` completes the `τ₁` version of
`spatial_exact_split`:

```text
Jdeep n = - ∑_{a,a',j,k} c(a)c(a')Λ(j)Λ(k) ·
             ∑_{q,a₀} e(m a₀/q) sin(2π m H/(q n))/(π m) ,     m = a j + a' k - n
```

After that:

5. aggregate the `q`-sum with the now-available verified large sieve
   `L_goldbach_finite_large_sieve` (merge upstream `513184b2` first, or copy from
   `~/github.com/fuck-tencent/goldback-artifacts/finite-large-sieve/`),
   giving the local densities `1/φ(q)² → (∑_a c(a) …)²`;
6. port the archimedean tail (`spatial_macro_sinc_tail`).

### Environment notes

* compile with `cd ~/github.com/fuck-tencent/goldback-work/lean && lake env lean
  ../../goldback-vinogradov/research/b1b1-port/b1b1_port.lean`
* the file sets `set_option maxHeartbeats 4000000` because `lake env lean <path>`
  does **not** apply the project's `leanOptions`;
* `IntervalIntegrable.sum`'s conclusion is `∑ i ∈ s, f i` (a function), which is
  only definitionally the goal's `fun t => ∑ i ∈ s, f i t`; use
  `intervalIntegrable_finset_sum'` (already in the file) or
  `convert … using 1; ext x; simp only [Finset.sum_apply]`;
* `Indicators` vs `setIntegral`: `integral_arcSet_indicator_phase_of_inside` and
  `integral_arcSet_one_zero/one` show the working pattern
  (`intervalIntegral.integral_of_le` → `setIntegral_indicator` → set identity).

## Milestone 28: the arc kernel in closed form (`exact_split` second half done)

```lean
sum_range_one_rhs (n) (m) :
  ∑_{a ∈ (range 1).filter (Coprime · 1)} e(m a/1) · sin(2π m H/(1·n))/(π m)
    = sin(2π m H/n)/(π m)

integral_wideSet_phase_eq_sinc_range (n) (m) (hm : m ≠ 0) (hn) (hQ : 1 ≤ cutoffB n)
    (hρ0) (hρ1) (hint) :
  ∫_{0}^{1} 1_{wideSet n} e(m t) dt
    = ∑_{q ≤ cutoffB n} ∑_{a ∈ (range q).filter (Coprime · q)}
        e(m a/q) · sin(2π m H/(q n))/(π m)

arcKernel_eq_sinc (n) (m) (hm : m ≠ 0) (hn) (hQ) (hρ0) (hρ1) (hint) :
  arcKernel n m
    = - ∑_{q ≤ cutoffB n} ∑_{a ∈ (range q).filter (Coprime · q)}
        e(m a/q) · sin(2π m H/(q n))/(π m)
```

The four fixes from the handover worked: `hQ : 1 ≤ cutoffB n`, `clear hn hρ0 hρ1`
before the `omega`s, a single `hsplit` rewrite (plus one extra `sum_insert` for the
copied right-hand sum), and the `(1 : ℝ)` casts in `sum_range_one_rhs` written as
`((1 : ℕ) : ℝ)` to match the goal.

### Combining with Milestone 27

```text
Jdeep n = ∑_{a,a',j,k} c(a)c(a')Λ(j)Λ(k) · arcKernel n (a j + a' k - n)
```

with the kernel now explicit.  The `m = 0` term is the last piece needed for the
full substitution (`arcKernel n 0 = 1 - |wideArcs ∩ (0,1]|`), after which

```text
Jdeep n = D - W ,   D = ∑_{a j + a' k = n} c(a)c(a')Λ(j)Λ(k) ,
                    W = ∑_{q ≤ Q₁} ∑_{a,a',j,k} c(a)c(a')Λ(j)Λ(k) c_q(m) sinc(mρ_q)
```

(both halves of the `τ₁` `spatial_exact_split`).

### Dossier

28 verified milestones, 1929 lines, no `sorry`, branch `research/b1b1-arcsplit`.

## Milestone 29: the kernel at zero frequency

```lean
arcKernel_zero (n) :
  arcKernel n 0 = ↑(volume.real ((wideSet n)ᶜ ∩ Set.Ioc 0 1))
```

(the complement measure, via `setIntegral_indicator` + `setIntegral_const`).

### The last interface for the full substitution

`deepIntegral_eq_quadruple_sum` + `arcKernel_eq_sinc` (`m ≠ 0`) + `arcKernel_zero`
(`m = 0`) now give, by `Finset.sum_congr` with a `by_cases h : m = 0` split,

```text
Jdeep n = ∑_{a,a'} (c a · c a') ∑_{j,k} (Λ j · Λ k) ·
   if a j + a' k = n
   then arcKernel n 0
   else - ∑_{q ≤ Q₁} ∑_{a₀ ∈ (range q), (a₀,q)=1} e(m a₀/q) sin(2π m H/(q n))/(π m)
```

i.e. `Jdeep = D·(1 - |A|) - W` with

```text
D = ∑_{a j + a' k = n} c(a)c(a')Λ(j)Λ(k)
W = ∑_{quad} c(a)c(a')Λ(j)Λ(k) ∑_q c_q(m) sin(2π m H/(q n))/(π m)
```

This is the complete `τ₁`-version of `spatial_exact_split`.  The remaining work is
the local-density aggregation (Milestone "second layer" in the handover).

### Dossier

29 verified milestones, 1966 lines, no `sorry`, branch `research/b1b1-arcsplit`.

## Milestone 30: the complete `τ₁` exact_split

```lean
def sineFactor (n) (m : ℤ) (q a : ℕ) : ℂ :=
  e(m a/q) · sin(2π m H/(q n))/(π m)

def sincSum (n) (m : ℤ) : ℂ :=
  ∑_{q ≤ cutoffB n} ∑_{a ∈ (range q), (a,q)=1} sineFactor n m q a

arcKernel_eq_neg_sincSum (n) (m) (hm : m ≠ 0) (…) :
  arcKernel n m = - sincSum n m

deepIntegral_eq_diagonal_sub_sinc (n) (hn) (hQ) (hρ0) (hρ1) (hint) :
  Jdeep n
    = ∑_{a,a'} (c a · c a') ∑_{j,k} (Λ j · Λ k) ·
        if a j + a' k = n then arcKernel n 0 else - sincSum n (a j + a' k - n)
```

This is the **complete `τ₁`-analogue of `spatial_exact_split`**:

```text
Jdeep = D · (1 - |A|) - W
D = ∑_{a j + a' k = n} c(a)c(a')Λ(j)Λ(k)          (the "q = ∞" local count)
W = ∑_{quad} c(a)c(a')Λ(j)Λ(k) ∑_q c_q(m) sin(2π m H/(q n))/(π m)
```

### What is left for b1-b1

Only the **local-density aggregation**:

1. compute `D` (a weighted count of `a j + a' k = n` with `Λ` weights) to `o(n)`
   precision — this needs an upper bound, not an asymptotic;
2. aggregate the `q`-sum in `W` using `L_goldbach_finite_large_sieve` (accepted;
   merge upstream `513184b2` to import it), replacing `1/φ(q)²` by the
   `∑_a c(a)`-weighted local density;
3. show `|D - W| = o(n)`.

### Dossier

30 verified milestones, 2035 lines, no `sorry`, branch `research/b1b1-arcsplit`.

## Correction before the "second layer": `D` cannot be bounded by `o(n)`

I had planned to "bound `D`" as the first step of the local-density layer.  That is
**wrong** and would waste effort:

```text
D = ∑_{a j + a' k = n} c(a)c(a')Λ(j)Λ(k) = ∑_{m + m' = n} τ₁(m)τ₁(m')
```

is the same diagonal that `theta_numerics.py` measures: `D/n = 3.688, 2.360, 3.550,
5.321` for `n = 10^4 … 10^7`, and `D ≈ 2 n θ²` with `θ = ∑ c(a)/a ≈ -log B₁ log log B₁`.
So `D = Θ(n log log² n)` — **not** `o(n)`, and no upper bound on `D` alone can help.

### What the second layer actually is

`Jdeep = D·(1-|A|) - W'` where `W'` is the `m ≠ 0` part of the wide-arc integral.
Since `D = Θ(n log log² n)`, the statement `Jdeep = o(n)` is precisely the
**main-term matching** `W' = D + o(n)` — the classical singular-series computation.
Nothing smaller suffices.

Two useful exact reformulations, both immediate from
`plainPolynomial_sq_dilated_expand` evaluated at `t = a₀/q`:

```text
∑_{a,a',j,k} c(a)c(a')Λ(j)Λ(k) · e((a j + a' k) a₀/q)
  = S_{τ₁}(a₀/q)² ,                                   (pointwise expansion)

∑_{quad} coeff · c_q(a j + a' k - n)
  = ∑_{a₀ ∈ (range q), (a₀,q)=1} e(-n a₀/q) · S_{τ₁}(a₀/q)² ,
```

so

```text
W = ∫_{A} S² e(-n·) = ∑_{q ≤ Q₁} ∑_{a₀, (a₀,q)=1}
      e(-n a₀/q) S_{τ₁}(a₀/q)² · sin(2π·(…))/(π·(…))
```

i.e. `W` is the arc integral, and matching it against `D` requires the
**major-arc approximation of `S_{τ₁}(a₀/q)`** —
`S_{τ₁}(a₀/q) ≈ (1/q) ∑_{r mod q} e(r a₀/q) · v(0)`-type, with `v` the archimedean
transform.  That needs the distribution of `τ₁ = c * Λ` in residue classes, i.e. the
`c`-weighted version of Bombieri–Vinogradov (the verified `w`-version is
`frontier_medcore_bv_band` + `frontier_spatial_lowmod_model_match`).

### Consequence for the plan

* Do **not** try to bound `D`.  The only viable route is:
  1. major-arc model for `S_{τ₁}(a₀/q)` (needs the `c`-weighted BV / Siegel–Walfisz);
  2. sum the model over `q ≤ Q₁` to get `W_model`;
  3. show `W_model = D + o(n)` (the singular series identity).

* Everything up to the model is now verified (30 milestones): the exact split, the
  kernel, the sinc sum, and the reformulation above.

* The cheapest next concrete lemma is the second displayed identity
  (`∑_{quad} coeff · c_q(m) = ∑_{a₀} e(-n a₀/q) S_{τ₁}(a₀/q)²`), which is a finite
  sum interchange using `plainPolynomial_sq_dilated_expand` at `t = a₀/q`.

## Milestone 31: the expansion summed over sample points

```lean
sum_plainPolynomial_sq_phase_eq_quad (n) (T : Finset ℝ) :
  ∑_{x ∈ T} S_{τ₁}(x)² e(-n x)
    = ∑_{x ∈ T} ∑_{a,a'} (c a · c a') ∑_{j,k} (Λ j · Λ k) · e((a j + a' k - n)·x)
```

Immediate from `plainPolynomial_sq_dilated_expand` (`Finset.sum_congr`).

### The remaining reordering (and the robust recipe)

The form needed for `W` has the `x`-sum **innermost** (it comes from `sincSum`),
while the formula above has it outermost.  The reordering

```text
∑_a ∑_a' ∑_j ∑_k ( coeff · ∑_x e(m x) )  =  ∑_x ∑_a ∑_a' ∑_j ∑_k ( coeff · e(m x) )
```

is a four-fold `Finset.sum_comm`.  `rw [Finset.sum_comm]` always rewrites the
*outermost* pair, so it cannot be used naively.  Two robust ways:

1. **`conv` descent**:
   ```lean
   conv_lhs => enter [2, a, 2, a', 2, j, 2, k]; rw [Finset.sum_comm]
   ```
   (repeat, descending to the innermost pair each time), or
2. **state the target with the `x`-sum outermost from the start** — i.e. prove the
   `W`-aggregation using `sum_plainPolynomial_sq_phase_eq_quad` and only later pull
   `∑_x` back inside with `Finset.mul_sum` at the innermost level (which is a
   local algebraic identity, `c * ∑ = ∑ c *`).

Route 2 is likely the cleanest: the `S_{τ₁}(a₀/q)²` form is exactly what the
major-arc model wants to approximate, so keeping the `a₀`-sum outermost is natural.

### Dossier

31 verified milestones, 2040 lines, no `sorry`, branch `research/b1b1-arcsplit`.

## Milestones 32-33: sinc as an arc integral; local coordinates

### The correction to the route-2 plan

Route 2 asked for

```text
W = ∑_q ∑_{a₀} e(-n a₀/q) · S(a₀/q)² · sinc(...)
```

That is **not** a valid identity: the sinc amplitude `sin(2πmρ)/(πm)` depends on the
frequency `m`, so it cannot be pulled out of the quadruple sum as a constant.  The
correct statement is that the sinc *is* an arc integral:

```lean
sineFactor_eq_arcIntegral (n q a m) (hm : m ≠ 0) :
  sineFactor n m q a = ∫ t in arcSet n q a, phase (m·t)          -- M32

sincSum_eq_sum_arcIntegral (n m) (hm : m ≠ 0) :
  sincSum n m = ∑_{q ≤ Q₁} ∑_{a<q,(a,q)=1} ∫_{arcSet n q a} phase (m·t)
```

so the frequency dependence stays inside.  Everything below uses that.

### Milestone 32: `Jdeep` as `D` minus arc integrals

```lean
deepIntegral_eq_diagonal_sub_arc_sum (n) :
  Jdeep n = diagonalSum n
    − ∑_{q ≤ Q₁} ∑_{a ∈ (range(q+1)),(a,q)=1}
        ∫₀¹ 1_{arcSet n q a} · S² · e(−n·)
```

(clipped arcs, the `integral_wideSet_eq_sum` normal form).

Then the **unclipping**: the `q = 1` arcs `0/1`, `1/1` stick out of `(0,1]`, but for a
`1`-periodic integrand the two clipped pieces recombine into the single full ball
`arcSet n 1 0`, and for `q ≥ 2` the numerator `a = q` is never coprime.  Hence

```lean
sum_arcSet_clipped_eq_sum_arcSet (n) (hQ : 1 ≤ cutoffB n) {f} (hf : Continuous f)
    (hper : ∀ u, f (u+1) = f u) (hint) (hρ0) (hρ1) :
  ∑_{q ∈ Icc 1 Q₁} ∑_{a ∈ (range(q+1)),(a,q)=1} ∫₀¹ 1_{arcSet n q a} f
    = ∑_{q ∈ Icc 1 Q₁} ∑_{a ∈ (range q),(a,q)=1} ∫_{arcSet n q a} f
```

with the `(range q)` family — exactly the `sincSum` index family.  Supporting lemmas:

```lean
plainPolynomial_add_one      -- S is 1-periodic
periodic_deepIntegrand       -- S²·e(−n·) is 1-periodic
integral_boundary_arcs_periodic  -- boundary pieces = full ball, any periodic f
arcSet_one_zero_eq_Icc
integral_arcSet_one_zero_gen / integral_arcSet_one_one_gen
sum_arcSet_one_gen           -- the q = 1 pair = ∫_{−ρ₁}^{ρ₁}
integral_arcSet_indicator_of_inside_gen
filter_range_succ_coprime    -- (range(q+1)) ∩ coprime = (range q) ∩ coprime for q ≥ 2
```

Result:

```lean
deepIntegral_eq_diagonal_sub_periodic_arc_sum (n) (hn) (hQ) (hρ0) (hρ1) (hint) :
  Jdeep n = D n − ∑_{q ≤ Q₁} ∑_{a<q,(a,q)=1} ∫_{arcSet n q a} S² e(−n·)
```

### Milestone 33: local coordinates on one arc

```lean
integral_arcSet_shift (n q a) :
  ∫_{arcSet n q a} S² e(−n·)
    = e(−n·a/q) · ∫_{−ρ_q}^{ρ_q} S(a/q+β)² e(−nβ) dβ        (ρ_q = H/(qn))
```

and therefore

```lean
deepIntegral_eq_diagonal_sub_shifted_arc_sum (n) (hn) (hQ) (hρ0) (hρ1) (hint) :
  Jdeep n = D n − ∑_{q ≤ Q₁} ∑_{a<q,(a,q)=1} e(−n·a/q) ·
      ∫_{−ρ_q}^{ρ_q} S(a/q+β)² e(−nβ) dβ
```

This is the **correct** form of the requested `W` identity, and the interface for the
major-arc approximation: `S(a/q+β)` is now a one-variable object on a short
archimedean interval.

### Dossier

33 verified milestones, 2336 lines, no `sorry`, branch `research/b1b1-arcsplit`.

---

## Cross-cell note: which matrix cells the `b1-b4` template can reach

*Strategy note (no Lean content). Live-board check, catalogue revision `970850fd`:
999 published / 939 accepted / 60 open.*

The whole `b1-b4` / `b4-b4` engine pivots on one number, `maximumStep`
(`L_goldbach_frontier_type2_b1_b4.lean`):

```lean
def wave (u l r : ℕ) (t : ℝ) : ℂ := ∑ h ∈ Ioc l r, phase ((u*h:ℕ)*t)   -- unweighted
def highAtoms (n) := Icc 1 (cutoffU n) ×ˢ Ioc (cutoffU n) (cutoffB n)   -- (d, cofactor)
def atomStep (atom) := atom.1 * atom.2                                  -- d · (m/a)
def atomWeight (atom) := (-(μ atom.1 : ℂ)) * (Λ atom.2 : ℂ)             -- Λ on the cofactor
def maximumStep (n) := cutoffU n * cutoffB n                            -- n^(19/48)
```

`wave` is **unweighted**, so the `Λ`-weighted factor must sit in the atom.
`upperBandWeight` attaches `Λ` to the *cofactor* `r = m/a`, hence the atom step is
`d·(m/a)` and the far-field (`offWave`/Young) budget is

```text
‖F‖₂ ‖G‖₂  ≲  √n · maximumStep · W ,      W = sup_u ∑_{step = u} |weight| ≤ n^o(1) ,
```

i.e. `√n` times the largest atom step. The template therefore works exactly when
the **cofactor** is at most `n^(1/3)`:

```text
√n · n^(1/16) · n^(1/3)  =  n^(43/48)  =  o(n) .
```

`τ₄` is the only band with a bounded cofactor (`a > n^(2/3) ⟹ m/a < n^(1/3)`).
Cell by cell, with `U = n^(1/16)`, `C` = cofactor cap of the expanded side and
`M = U·C`:

| cell | expanded side | `C` | `M` | far budget `√n·M` | board |
|---|---|---|---|---|---|
| b1-b4 | τ₄ | `n^(1/3)` | `n^(19/48)` | `n^(43/48)` | ACCEPTED |
| b2-b4 | τ₄ | `n^(1/3)` | `n^(19/48)` | `n^(43/48)` | ACCEPTED |
| b3-b4 | τ₄ | `n^(1/3)` | `n^(19/48)` | `n^(43/48)` | ACCEPTED |
| b4-b4 | τ₄ | `n^(1/3)` | `n^(19/48)` | `n^(43/48)` | ACCEPTED |
| b1-b1 | τ₁ | `n^(15/16)` | `n` | `n^(3/2)` | **open (this task)** |
| b1-b2 | τ₁ / τ₂ | `n^(15/16)` / `n^(3/4)` | `n` / `n^(13/16)` | `n^(3/2)` / `n^(21/16)` | open, claimed |
| b1-b3 | τ₁ / τ₃ | `n^(15/16)` / `n^(2/3)` | `n` / `n^(35/48)` | `n^(3/2)` / `n^(59/48)` | open, claimed |
| b2-b2 | τ₂ | `n^(3/4)` | `n^(13/16)` | `n^(21/16)` | **open** |
| b2-b3 | τ₂ / τ₃ | `n^(3/4)` / `n^(2/3)` | `n^(13/16)` / `n^(35/48)` | `n^(21/16)` / `n^(59/48)` | **open** |
| b3-b3-parity | τ₃ | `n^(2/3)` | `n^(35/48)` | `n^(59/48)` | **open** |

**The four accepted cells are exactly the four with cofactor `≤ n^(1/3)`.** Every
open cell misses the far budget by a positive power of `n`, on *both* sides, so
moving from b1-b1 to b2-b2 / b2-b3 buys nothing: the long-cofactor mechanism is
what is missing, not the choice of band. This is the parameter-arithmetic form of
the Milestone 11 finding (`τ₁`'s waves are not concentrated on the grid).

Also worth recording for the claim bookkeeping: on revision `970850fd` the
remaining open cells of this track are b1-b1, b1-b2, b1-b3, b2-b2, b2-b3,
b3-b3-parity; `desk.assignments` shows b1-b2 and b1-b3 as `working` under other
handles, so they are not claimable.

### What a port would still need: `low_band_progressions`

`upperBandWeight` has a strict `lower < a` but **no upper bound on `a`**, while the
catalogue's `τ_k` also requires `a ≤ B_k`. The low-band atom expansion is therefore
a separate identity (a `bandWeight` with the extra `a ≤ B`):

```lean
/-- Low-band atom expansion: `Λ` on the cofactor, `μ` on the short divisor.
The `k` range is the point: `a = d·k ≤ B`. -/
theorem low_band_progressions (limit cutoff lower B : ℕ) (hB : B ≤ limit) :
  ∑ m ∈ range (limit+1),
      (∑ a ∈ m.divisors.filter (fun a => lower < a ∧ a ≤ B ∧ cutoff < m / a),
          (∑ d ∈ a.divisors.filter (fun d => cutoff < d), w d) * c (m / a)) * phase m
    = ∑ b ∈ Ioc cutoff (limit / lower), ∑ d ∈ Icc 1 cutoff,
        (-w d) * c b *
          ∑ k ∈ Ioc (lower / d) (min (limit / (d * b)) (B / d)), phase (d * b * k)
```

The Möbius cancellation `∑_{d|a} w d = 0` for `a > 1` trades the large divisors
`d > cutoff` for the small ones `d ≤ cutoff` at the cost of a sign. Instantiations:
`(lower, B, cutoff) = (U, B₁, U)` for τ₁, `(B₁, B₂, U)` for τ₂, `(B₂, B₃, U)` for τ₃.

This lemma is *necessary* for any port, but it does **not** remove the obstruction
above: it constrains `a = d·k`, not the cofactor `m/a`.

### Independent check: the frequency-side budget is also too large

The alternative `K(h)` route (`Jdeep = ∑_h d(h) K(h)`, dispersion in the frequency
variable) cannot close by Cauchy–Schwarz either. With
`d(h) = ∑_{m+m'=n+h} τ₁(m) τ₁(m')`:

```text
∑_h |d(h)|²  =  ∫₀¹ |S_{τ₁}|⁴  ≥  (∫₀¹ |S_{τ₁}|²)²  =  (∑_m |τ₁(m)|²)² .
```

The `a = a'` diagonal contributes
`∑_a |c(a)|² ∑_{p ≤ n/a} Λ(p)² ≈ n log n · ∑_{a ∈ (U,B₁]} |c(a)|²/a`. For prime
`a ∈ (U,B₁]` one has `c(a) = −1`, and `∑_{U<p≤B₁} 1/p ≈ log 4` is a positive
constant, so `∑_m |τ₁(m)|² ≈ n log n · Θ(1)` and

```text
‖d‖₂ ‖K‖₂  ≥  (∑_m |τ₁(m)|²) · |K(0)|  ≈  n log n  >  n ,
```

because `K(0) = 1 − |wideArcs| ≥ 1/2`. So the method's own error budget exceeds
`εn` no matter how sharp the Ramanujan or kernel bounds are made; the signed
cancellation `D − W` has to be used in the space domain (Milestones 10–11), not in
the frequency domain.

## Milestone 34: upstream merge (`1fe24b28`) and why the "local density" triangle inequality cannot close b1-b1

### Merge

`goldback-work` was fast-forwarded `1133b2d2 → 1fe24b28` (32 commits).  The dossier
re-checks clean against the merged tree (2336 lines, no `sorry`, 1m40s).

The merge brings a **new, fully proved route**, `selberg-large-sieve-and-power-saving`.
All six of its modules are sorry-free and axiom-free on `main`:

| module | lines | content |
|---|---|---|
| `Conjectures.Goldbach.SelbergSharpLargeSieve` | 1382 | sharp large sieve: `∑_{i<M}‖∑_{k≤N} a k e(k x_i)‖² ≤ (N + max 1 (2/δ)) ∑‖a k‖²` for points `δ`-separated mod 1 |
| `Conjectures.Goldbach.UnconditionalMinorFiveSixths` | 3517 | `‖S_n(w,t)‖ ≤ n^(5/6+ε)` outside `wideArcs` |
| `Conjectures.Goldbach.DeepThreeQuartersFromFareyError` | 679 | Friedlander–Goldston error ⇒ 3/4 bound |
| `Conjectures.Goldbach.ThreeQuartersExceptionalDirichletWindows` | 632 | exceptional Dirichlet windows |
| `Conjectures.Goldbach.ThreeQuartersModelSqrtExceptions` | 2095 | conditional circle model ⇒ `X^(1/2+ε)` Goldbach exceptions |
| `Conjectures.Goldbach.DeepThreeQuartersExceptionalZeroCriterion` | 6599 | equivalence with the correction-only form |

Consequences for this port:

* `L_goldbach_finite_large_sieve` (the weak single-modulus `ZMod Q` version in
  `goldback-artifacts`) is **obsolete** — the sharp Selberg form with separation is
  on `main` and strictly stronger.  Do not add the old file.
* The only remaining open target of that route is
  `L-goldbach-frontier-deep-three-quarters-saving` itself.

### The quantitative obstruction to "local density absolute convergence"

Proposed route: bound `|Jdeep| ≤ ∑_q |A_q| · |weight − limit density|`.  Two problems.

**(1) There is no limit density in `q`.**  From `arcKernel_eq_neg_sincSum`,

```text
W = ∑_{q ≤ Q₁} ∑_{quads} coeff · c_q(m) · sin(2π m ρ_q)/(π m),    ρ_q = H/(q n) .
```

For fixed `m ≠ 0`, `sin(2π m ρ_q)/(π m) → 0` as `n → ∞` because `ρ_q → 0`.  So every
`q`-term tends to `0`; the sum over `q ≤ n^(1/3)` takes its value entirely from the
range `|m − n| ≲ 1/ρ_q = q n / H`, not from convergence of local densities in `q`.

**(2) The triangle inequality is off by `n^(1/3)`.**  By Milestone 33,

```text
Jdeep = D − ∑_{q ≤ Q₁} ∑_{a₀,(a₀,q)=1} e(−n a₀/q) ∫_{−ρ_q}^{ρ_q} S(a₀/q+β)² e(−nβ) dβ ,
```

and `∫_{arc}|S|² ≈ n/φ(q)` (the `|β| ≤ ρ_q` window integrates the `n` frequencies),
so for one modulus

```text
∑_{a₀} |A_q|  ≈  φ(q) · n/φ(q)  =  n ,
hence   ∑_{q ≤ Q₁} |A_q|  ≈  n · Q₁  =  n^(4/3) .
```

But the target is `|∑_q A_q| ≤ ε n`, and `∑_q A_q = D + O(εn) = Θ(n)`.  So the
`q`-sum has to cancel from `n^(4/3)` down to `n`: a factor `n^(1/3)`.  Any bound of the
form `|Jdeep| ≤ ∑_q |·| · |·|` is therefore *structurally* too lossy, no matter how
sharp the per-`q` estimate.  This is the quantitative form of Milestone 11.

**(3) A sup-norm route is also too lossy.**  `|Jdeep| ≤ ∫_{Aᶜ}|S|²`, and
`‖S‖₂² = ∑|τ₁|² ≈ n log⁴ n`, so `∫_{Aᶜ}|S|² ≤ ‖S‖_∞(Aᶜ) · n^(1/2) log² n`.  To get
`o(n)` one needs `‖S‖_∞(Aᶜ) ≲ n^(1/2−δ)`.  The newly merged 5/6 bound gives
`n^(4/3)`; even the open 3/4 bound gives `n^(5/4)`.  **Neither suffices**, and the
`1/2` threshold is exactly "major arcs up to `√n`".

### Where that leaves the port

`b1-b1` is a **signed main-term identity** (`W = D + o(n)`), not a smallness statement.
Every verified tool — `sincSum`, arc geometry, large sieve, 5/6 bound — is an
absolute-value or mean-square instrument, and each one provably loses at least
`n^(1/3)` (or `n^(1/4)` in the sup route) more than the budget `εn` allows.  The
dossier therefore stands as the exact reduction plus a proof that the available
method classes cannot finish it.

## Milestone 35: the exact position of b1-b1 in the upstream reduction chain

This is the last substantive finding of the port.  It supersedes the framing of
Milestone 34 (which said "no Type-II instrument exists"): the sharper statement is
that the upstream chain is **already assembled** and b1-b1 is literally one of six
missing cells in it.

### 35.1 Type-I is done, twice

**(a) Upstream, verified.**
`lean/PEqualNP/Outside/L_goldbach_frontier_vaughan_type1_elimination.lean`
(1569 lines, no `sorry`, on `main`):

```lean
theorem PEqualNP.Outside.L_goldbach_frontier_vaughan_type1_elimination :
  … ‖Jdeep n Λ Λ − Jdeep n (typeII n) (typeII n)‖ ≤ 60 * Z ,
        Z = (n:ℝ)^(23/24) * (Real.log n)^2  =  o(n)
```

So the whole `Λ × Λ` deep-minor problem reduces to the **Type-II coefficient**
with a sublinear error `n^(23/24) log² n`.

**(b) Local machinery.**
`goldback-vinogradov/research/vinogradov-local/` (`type1.lean`, `type1_bound.lean`
≈ 230 KB, `assembly.lean`, `separated_large_sieve.lean`, …).  Its own README records
the conclusion verbatim:

> For `U = n^(1/16)`, `C = O(log n)`, this is `o(n)` without any prime-distribution
> input.  **The remaining hard part is therefore the Type-II range, not the low
> Type-I terms.**

Support bound `‖∑_{k≤N} low U f k · E(k t)‖ ≤ (U+1)·C`; residue refinement
`‖S₂(a/q+β)‖ ≤ 4 q log n (1 + log q)` for `q ≥ 2U`; third-term fibre reindexing
`∑_{d,e≤U} … ≤ log(U²)·2q·2(1+log q)`.

Note: that directory is being actively edited by another session (mtime same day);
this port does not touch it.

### 35.2 `τ₁` **is** Vaughan's Type-II coefficient, band-truncated

```lean
-- upstream  typeII_coefficient (U m)
∑ a ∈ m.divisors.filter (U < a ∧ U < m/a),
    (∑ d ∈ a.divisors.filter (U < d), μ d) * Λ (m/a)

-- catalogue τ₁
∑ a ∈ m.divisors.filter (U < a ∧ a ≤ B₁ ∧ U < m/a),
    (∑ d ∈ a.divisors.filter (U < d), μ d) * Λ (m/a)
```

The two are **identical except for the extra `a ≤ B₁`**.  Hence `τ₁, τ₂, τ₃, τ₄` are
the band-splits of Vaughan's Type-II coefficient:

```text
τ₁ : a ∈ (U,  B₁] = (n^(1/16), n^(1/4)]
τ₂ : a ∈ (B₁, B₂] = (n^(1/4),  n^(1/3)]
τ₃ : a ∈ (B₂, B₃] = (n^(1/3),  n^(2/3)]
τ₄ : a ∈ (B₃, n/U] = (n^(2/3), n/U]
typeII = τ₁ + τ₂ + τ₃ + τ₄ .
```

### 35.3 The assembly theorem: ten cells

`lean/PEqualNP/Outside/L_goldbach_frontier_type2_matrix_bridge.lean` (58 lines,
no `sorry`) proves, from the following hypotheses,

```lean
intro hswap htype ⟨N₀,hsplit⟩ h11 h12 h14 h44 h22 h24 h13 h23 h34 h33 e he
```

that `‖deepMinor n‖ ≤ e * n`.  Reading the hypothesis list:

```text
Jdeep(Λ,Λ) = o(n)
  ← hswap + htype            swap + Type-I elimination      PROVED
  ← hsplit : typeII = τ₁+τ₂+τ₃+τ₄                          PROVED
  ← all ten cells (i,j)                                    ← the gap
```

The symmetric 4×4 matrix has exactly ten independent cells, and the hypothesis list
contains exactly those ten: `h11 h12 h13 h14 h22 h23 h24 h33 h34 h44`.  The budget is
split as `e/18` per hypothesis.

Board status (catalogue revision `970850fd`):

| cell | task | status |
|---|---|---|
| h11 | `…-type2-b1-b1` | **open**, `challenge_only`, 914 |
| h12 | `…-type2-b1-b2` | open, claimed by another handle |
| h13 | `…-type2-b1-b3` | open, claimed by another handle |
| h22 | `…-type2-b2-b2` | open, `challenge_only`, 914 |
| h23 | `…-type2-b2-b3` | open, `challenge_only`, 914 |
| h33 | `…-type2-b3-b3-parity` | open, `challenge_only`, 914 |
| h14 | `…-type2-b1-b4` | **proved** |
| h24 | `…-type2-b2-b4` | **proved** |
| h34 | `…-type2-b3-b4` | **proved** |
| h44 | `…-type2-b4-b4` | **proved** |

**Four of ten are proved, and they are exactly the `τ₄` column** — the short-cofactor
column (`a > n^(2/3) ⇒ m/a < n^(1/3)`), which is the only regime the far/near engine
reaches.  The six open cells all have long cofactors.

### 35.4 Why a naive port of the Type-I budget fails

Type-I elimination gives `n^(23/24)`.  For `τ₁` one would have to sum the same
estimate over the short divisors `a ∈ (U, B₁]`, with
`∑_{a≤B₁} |c(a)| ≤ ∑_{a≤B₁} τ(a) ≍ n^(1/4) log n`.  That gives

```text
n^(23/24) · n^(1/4)  =  n^(29/24) ,
```

i.e. **`n^(5/24)` over budget**.  (Estimate, not a verified statement.)  The `a`-sum
must therefore be treated *jointly* with Vaughan's `d, e` — which is precisely the
missing Type-II instrument.

### 35.5 Verdict

* b1-b1 is **not** an isolated problem.  It is cell `h11` of the ten-cell
  decomposition of `Jdeep(Λ,Λ) = o(n)`, and that conclusion is exactly the
  binary-Goldbach-type asymptotic for the log-weighted prime sum.
* All glue is verified: swap, Type-I elimination, `typeII = Στᵢ`, matrix assembly.
* The only open content is the six long-cofactor cells.  Every method available to
  this port fails on them by a quantified margin (Milestones 11, 34, and 35.4).
* Therefore: **no clear path to b1-b1 with the current toolset**; no PR can be
  opened; this dossier (exact reduction + quantified impossibilities + the position
  of the cell in the upstream chain) is the deliverable.

## Milestone 36: correction — the `d,e` joint treatment *does* exist, and it draws the gap at `n^(2/5)`

M34 claimed "there is no Type-II / Bombieri–Vinogradov instrument for the `τ` family
anywhere in the tree".  **That is wrong.**  There is a complete, verified Vaughan
Type-II bilinear engine.  Retracting it.

### 36.1 What exists

`lean/PEqualNP/Outside/L_goldbach_bulk_density_one.lean`
(10 406 lines, no `sorry`, on `main`; main theorem
`PEqualNP.Outside.L_goldbach_bulk_density_one`).  The Type-II machinery sits in
`OAI.Problem337.Vaughan`:

| theorem | content |
|---|---|
| `typeII_eq_hyperbola` | joint `d,e` parametrisation: `∑_{k≤N} (typeIICoefficient U * longPart V Λ) k · w k = ∑_{d·e≤N, d>U, e>V} typeIICoefficient U d · Λ e · w (d·e)` |
| `typeII_eq_sum_dyadic_blocks` | splits the hyperbolic region into dyadic blocks |
| `norm_typeII_le_dyadic_log_budget` | assembles per-block bounds with a `log` budget |
| `norm_bilinear_sq_le`, `norm_bilinear_sq_le_energy` | bilinear Cauchy–Schwarz on the `d,e` pair |
| `near_rational_hyperbolic_bilinear_sq_le` | the joint square bound at a near-rational phase: `‖∑_{m∈[L,U]} c m ∑_{n∈t} b n · column θ X n m‖² ≤ (∑‖c m‖²)·((2N/q+1)(2(U+1−L)+4q(1+log 2q)))·(∑‖b n‖²)` |
| `typeIIBlock_sq_le_raw / _normalized / _uniform` | per-block, uniform in the block |
| `optimized_typeIIBlock_bound` | per-block optimised |
| **`optimized_typeII_bound`** | `‖∑‖ ≤ 54·(1+log 2N)^4 · (N/√q + N^(4/5) + √(Nq))` for `|θ−a/q| ≤ 1/q²`, `q ≤ N`, `N^(2/5) ≥ 2` |

with

```lean
def optimizedCutoff (X : ℝ) : ℕ := ⌊X ^ (2/5 : ℝ)⌋₊
def approximationEnvelope (X q : ℝ) : ℝ := X/Real.sqrt q + X^(4/5:ℝ) + Real.sqrt (X*q)
```

So the engine covers the Type-II range **`d, e > N^(2/5)`**, and the envelope is the
classical `N/√q + N^(4/5) + √(Nq)`.

### 36.2 The precise coverage, and hence the gap

Vaughan's verified coverage in this tree is

```text
Type-I   : one factor ≤ U = n^(1/16)        -- type1_elimination, n^(23/24) error
Type-II  : both factors > n^(2/5)           -- optimized_typeII_bound
gap      : U < factor ≤ n^(2/5)             -- nothing
```

`U = ⌊n^(1/16)⌋` is literally the `U` in the task statements
(`vaughan_type1_elimination`, line 1500; `type1_cut_parameters` line 1150).

Cell by cell:

| band | range | vs Vaughan |
|---|---|---|
| τ₁ | `(n^(1/16), n^(1/4)]` | **entirely in the gap** |
| τ₂ | `(n^(1/4), n^(1/3)]` | **entirely in the gap** |
| τ₃ | `(n^(1/3), n^(2/3)]` | straddles `n^(2/5)`; `(n^(2/5), n^(2/3)]` covered |
| τ₄ | `(n^(2/3), n/U]` | fully in the Type-II range |

**This is the sharp reason why the four `-b4` cells are proved and the six others are
open**: the `τ₄` column is the only one whose divisor band lies entirely in a
Vaughan-covered range.  b1-b1 (`τ₁ × τ₁`) is entirely inside the classical
**Vaughan gap** `(n^(1/16), n^(2/5))`.

### 36.3 What this changes and what it does not

* **Changes:** the sentence in M34 "no Type-II instrument exists" is retracted.
  The correct statement is "the Type-II instrument exists but stops at `n^(2/5)`,
  and b1-b1's band `(n^(1/16), n^(1/4)]` is below it".
* **Does not change:** the verdict.  b1-b1 still has no available path.  Pushing
  `optimized_typeII_bound` from `N^(2/5)` down to `N^(1/4)` is a Type-II estimate at
  level `n^(1/4)` with one factor unbounded — i.e. exactly the Bombieri–Vinogradov
  strength input that is not formalized anywhere, and the `n^(5/24)` shortfall of
  §35.4 is the same obstruction seen from the Type-I side.
* The `a`-sum over `(n^(1/16), n^(1/4)]` in §35.4 is now interpretable precisely: it
  is *trying to push Vaughan's Type-II estimate down into the gap*, which is why the
  triangle inequality over `a` overruns by `n^(5/24)`.

### 36.4 Revised one-line summary

```text
最先进的已验证 Vaughan 覆盖 = {某因子 ≤ n^(1/16)} ∪ {两因子均 > n^(2/5)}
b1-b1 的除数带 (n^(1/16), n^(1/4)] 整段落在缺口里。
```

That, not "no instrument", is the reason b1-b1 is open for this port.

### 36.5 Correction to §36.2: τ₃ is *not* "half covered"

The §36.2 row for τ₃ ("straddles `n^(2/5)`; `(n^(2/5), n^(2/3)]` covered") is
**imprecise** and should not be used as a plan.  Two reasons.

**(i) Vaughan's Type-II condition is on *both* factors, not on the divisor alone.**
`optimized_typeII_bound` applies to `typeIICoefficient U' * longPart U' Λ` with
`U' = optimizedCutoff N = ⌊N^(2/5)⌋`, i.e. it needs

```text
a > N^(2/5)   AND   m/a > N^(2/5)      (hence m > N^(4/5)).
```

For τ₃ the divisor is `a ∈ (n^(1/3), n^(2/3)]` but the cofactor is only
`m/a ∈ (n^(1/16), n^(2/3)]`.  So the genuinely covered sub-region is

```text
{ a > n^(2/5)  ∧  m/a > n^(2/5) }  ⊆  { m > n^(4/5) } ,
```

which is much smaller than "the right half of the divisor band".  In particular the
whole piece with `m/a ≤ n^(2/5)` is outside Vaughan.

**(ii) τ₃ is a bounded band, not a `typeIICoefficient`.**  The verified coefficient has
only a *lower* bound `a > U'`; τ₃ also requires `a ≤ B₃ = n^(2/3)`.  Since
`a > n^(2/3)` and `m/a > n^(1/16)` is compatible with `m ≤ n`
(`n^(2/3+1/16) = n^(35/48) < n`), the truncation is not empty and has to be removed
separately, e.g. by writing τ₃ as a combination of `typeIICoefficient` at different
cutoffs plus the two boundary regions `{a > B₃}` and `{U < m/a ≤ B₂}`.  That bookkeeping
is routine; it does not change the budget.

> **⊘ RETRACTED — see M41.1.**  The support value in this paragraph is arithmetically
> wrong: `B₃·n^(2/5) = n^(2/3+2/5) = n^(16/15) > n`, so the support bound is **vacuous** and
> the small-cofactor piece is **full-range**.  The sentence "Piece (ii) is supported on
> `m ≤ n^(13/15)`" and the mass estimate after it must not be used.  The correct table is in
> M41.2.

**Consequence.**  b3-b3-parity is *not* tryable in the sense "we can close it".  What it
does support is a **partial reduction**: the sub-region
`a > n^(2/5) ∧ m/a > n^(2/5)` can be discharged by `optimized_typeII_bound`, leaving
(i) the gap band `a ∈ (n^(1/3), n^(2/5))` and (ii) the small-cofactor region
`m/a ≤ n^(2/5)`.  Piece (ii) is supported on `m ≤ B₃·n^(2/5) = n^(13/15)`, whose total
coefficient mass is `≈ n^(13/15) log² n` (estimate:
`∑_{a∈(B₂,B₃]} τ(a)/a ≈ (1/6) log² n`), so it is *small* as a mass but still needs a
bilinear `L²` handle because `Jdeep` is a product of two such sums.

So: no new path; the correct statement is "τ₃ has a Vaughan-covered sub-region, and two
named residual regions, neither of which is covered".

## Milestone 37: the local-count identity is verified

```lean
def ramanujanPhase (q : ℕ) (m : ℝ) : ℂ :=
  ∑ a₀ ∈ (Finset.range q).filter (fun a₀ => Nat.Coprime a₀ q), phase (m * (a₀/q))

theorem sum_comm_outer5 {α} [AddCommMonoid α] … :
  ∑_{x∈s} ∑_{y∈t} ∑_{y'∈t'} ∑_{z∈u y} ∑_{w∈v y'} f x y y' z w
    = ∑_{y∈t} ∑_{y'∈t'} ∑_{z∈u y} ∑_{w∈v y'} ∑_{x∈s} f x y y' z w

theorem quad_sum_ramanujan (n q : ℕ) :
  ∑_{a ∈ I₁} ∑_{a' ∈ I₁} (c a · c a') · ∑_{j ∈ I₂ a} ∑_{k ∈ I₂ a'} (Λ j · Λ k) ·
      ramanujanPhase q (a j + a' k − n)
    = ∑_{a₀ ∈ (range q), (a₀,q)=1} S_{τ₁}(a₀/q)² · e(−n a₀/q)
```

Two implementation notes worth keeping:

* `ramanujanPhase` is stated with a **real** frequency `m : ℝ`, deliberately.  The
  frequency produced by `plainPolynomial_sq_dilated_expand` is
  `(((a*j:ℕ):ℝ) + ((a'*k:ℕ):ℝ) - (n:ℝ))`; using `ℤ` here forces a cast rewrite in every
  single term.  With `ℝ` the two sides match syntactically and the proof is
  `simp only [ramanujanPhase, Finset.mul_sum]` followed by one `symm`.
* `sum_comm_outer5` is proved by four `Finset.sum_comm` rewrites interleaved with three
  `Finset.sum_congr` descents — `rw [Finset.sum_comm]` always rewrites the *outermost*
  pair, so the descent is mandatory.  It replaces the failed `conv_rhs` attempt of
  Milestone 31.

Content: `D` is the `q = ∞` local count, and the `q`-th term of the `sincSum` layer is
the finite-modulus local count.  This closes the bookkeeping of the "local density"
picture; the estimate that would use it is the one shown impossible in M34/M36.

Dossier: 2336 → 2409 lines, no `sorry`, 36 verified milestones.

## Milestone 38: the τ₃ "Vaughan-covered sub-region" is not reachable by instantiation

§36.5 proposed discharging the sub-region `a > n^(2/5) ∧ m/a > n^(2/5)` of `τ₃` with
`optimized_typeII_bound`.  Reading the interface shows this is **not** an instantiation.

### 38.1 Good news: the two cutoffs are separate

```lean
theorem norm_typeII_le_dyadic_log_budget (N U V : ℕ) (w : ℕ → ℂ) (B : ℝ)
    (hB0 : 0 ≤ B)
    (hB : ∀ j < Nat.log 2 N + 1, ‖typeIIBlock N U V j w‖ ≤ B) :
    ‖weightedSum (Ioc 0 N) w (typeIICoefficient U * longPart V Λ)‖
      ≤ (1 + Real.log N / Real.log 2) * B
```

So the Möbius cutoff `U` and the cofactor cutoff `V` are independent, and
`typeII_eq_hyperbola (N U V w)` / `typeII_eq_sum_dyadic_blocks` are stated for general
`U, V`.  For `τ₃` the natural pair would be `U = ⌊n^(1/16)⌋` (its Möbius truncation) and
`V = ⌊n^(2/5)⌋` (the cofactor floor).

### 38.2 Bad news: the block estimate is only proved at `U = V = N^(2/5)`

The single hypothesis `hB` is what carries all the analysis, and the only proved
supplier is

```lean
theorem optimized_typeIIBlock_bound (θ a q …) (N j …) :
    ‖typeIIBlock N (optimizedCutoff N) (optimizedCutoff N) j (phase …)‖ ≤ …
```

i.e. `U = V = ⌊N^(2/5)⌋`, with no `U, V` parameters at all.  Moreover
`typeIIBlock N U V j` is indexed by `VaughanDyadic.shell U N j`, so a *smaller* `U`
makes the block strictly larger and the bound strictly weaker.  Running the engine at
`U = ⌊n^(1/3)⌋` (τ₃'s divisor floor) or at `U = ⌊n^(1/16)⌋` requires **re-proving the
block-level Type-II estimate below `N^(2/5)`** — which is exactly "push Vaughan into the
gap", the same missing analysis as §35.4 / §36.3.

So the τ₃ sub-band reduction is not a bounded piece of formalisation; it is blocked at
the same place as b1-b1 itself.  The only part that *is* small is the purely
combinatorial band-split (`Finset.sum_filter` / `filter_filter`), i.e. definition
unfolding, which the platform's task rules explicitly refuse to count as a task.

### 38.3 Consequence

Nothing in the open cells of the Type-II matrix is reachable from the verified toolset.
The dossier is closed here:

```text
b1b1_port.lean  2409 lines, 36 verified milestones, no sorry
README.md       M1-M38
```

The durable value is: (i) the exact reduction chain `Jdeep = D − W` down to local
coordinates, in four independent normal forms (M29-M33); (ii) the local-count identity
(M37); (iii) quantified impossibilities for every method class available (M11, M34,
M36, M38); (iv) the position of b1-b1 as cell `h11` of the ten-cell `matrix_bridge`
(M35).

## Milestone 39: the two *mechanical* gaps of §38 are closed

§38 said "the block-level Type-II estimate must be reproved below `N^(2/5)`".  **That was
wrong.**  The block estimate is already stated for arbitrary cutoffs.  What is actually
needed is (i) a budget conversion that does not assume `U ≥ N^(2/5)`, and (ii) a divisor
*window* parameter.  Both are now verified.

### 39.1 The block estimate was already general

```lean
-- OAI.Problem337.Vaughan
theorem typeIIBlock_sq_le_uniform (θ a q) (hq) (hcop) (happrox) (N U V j) (hqN) (hU) (hV) :
  ‖typeIIBlock N U V j (fun k => phase (θ*k))‖^2
    ≤ 32 * N * (typeIILogScale N)^6 * (N/q + N/U + N/V + q)
```

`U` and `V` are free parameters; nothing forces `U = N^(2/5)`.  The `2/5` enters only
one step later.

### 39.2 The budget, with free cutoffs

```lean
theorem cutoff_squared_budget_general (X q C U V R : ℝ)
    (hX : 1 ≤ X) (hq : 0 < q) (hC : 0 ≤ C) (hU : 0 < U) (hV : 0 < V)
    (hbound : R^2 ≤ C * X * (1 + log (2X))^6 * (X/q + X/U + X/V + q)) :
  R ≤ √C * (1 + log (2X))^3 * (X/√q + X/√U + X/√V + √(X q))
```

`optimizedCutoff_squared_budget` is the special case `U = V = ⌊X^(2/5)⌋`, where
`X/√U = X^(4/5)`.  The identity that pins `2/5` is

```text
X · (X/U)  ≤  (X^(4/5))²  =  X^(8/5)      ⟺      U ≥ X^(2/5) .
```

For `U = X^(1/16)` the `U`-term is `X^(31/16)` against `X^(8/5)`: the loss is exactly
`X^(27/80)`.  The block scale becomes `X^(31/32) log³` and the summed scale
`X^(31/32) log⁴ = o(X)` — **the budget still closes**, so nothing analytic is lost here.

Instantiation (imports `PEqualNP.Outside.L_goldbach_bulk_density_one`):

```lean
theorem typeIIBlock_norm_le_general (θ a q) (hq) (hcop) (happrox) (N U V j)
    (hqN) (hU : 0 < U) (hV : 0 < V) (hN : 1 ≤ N) :
  ‖typeIIBlock N U V j (fun k => phase (θ*k))‖
    ≤ √32 * (1 + log (2N))^3 * (N/√q + N/√U + N/√V + √(N q))
```

### 39.3 The divisor window

The verified coefficient has *no upper bound* on the divisor `a`, and its Möbius cutoff
is tied to the same number:

```text
typeIICoefficient U m  = ∑_{a|m, m/a>U} (∑_{d|a, d>U} μ d) · Λ(m/a)
```

while `τ₃` needs `a ∈ (B₂, B₃]`.  The window is split off as a difference of half-lines:

```lean
/-- Möbius cutoff `U`, cofactor cutoff `V`, divisor only constrained by `a > L`. -/
def halfLineTypeII (U V L : ℕ) : ℕ → ℝ
/-- additionally `a ≤ H`. -/
def windowTypeII (U V L H : ℕ) : ℕ → ℝ
def cutoffB3 (n : ℕ) : ℕ := ⌊n^(2/3)⌋            -- B₃ (B₂ is the module's cutoffB)

theorem windowTypeII_eq_sub (U V L H m) (hLH : L ≤ H) :
  windowTypeII U V L H m = halfLineTypeII U V L m - halfLineTypeII U V H m

def tauThree (n : ℕ) : ℕ → ℝ := windowTypeII (U n) (U n) (B₂ n) (B₃ n)
theorem tauThree_apply (n m) :            -- exactly the catalogue's τ₃ display
  tauThree n m
    = ∑ a ∈ (Nat.divisors m).filter (B₂ < a ∧ a ≤ B₃ ∧ U < m/a), c_U(a) · Λ(m/a)
theorem tauThree_eq_sub (n m) (h : B₂ ≤ B₃) :
  tauThree n m = halfLineTypeII (U) (U) B₂ m - halfLineTypeII (U) (U) B₃ m
```

and the support statement behind §36.5(ii):

```lean
theorem le_mul_of_cofactor_le (m a H V₀) (ha : a ∣ m) (haH : a ≤ H) (hcof : m/a ≤ V₀) :
  m ≤ H * V₀
```

> **⊘ RETRACTED — see M41.1.**  `H · V₀ = n^(2/3+2/5) = n^(16/15) > n`, so this
> instantiation puts *no* restriction on `m`; the small-cofactor part of `τ₃` is full-range.
> The lemma `le_mul_of_cofactor_le` is correct — only this instantiation (`H = B₃`,
> `V₀ = n^(2/5)`) is not.  Correct table: M41.2.  (The trick *does* work for `τ₁` and `τ₂`.)

Two implementation notes:

* `windowTypeII_eq_sub` originally used `Finset.sum_sdiff`; in this Mathlib the
  statement does not have the `∑_{s₁\s₂} = ∑_{s₁} - ∑_{s₂}` orientation.  The working
  proof goes through `Finset.sum_filter` and `Finset.sum_sub_distrib`, reducing the
  identity to a pointwise `if`-case split on `L < a`, `V < m/a`, `a ≤ H`.
* `cutoff_squared_budget_general` needs `1 ≤ X`, not `0 < X`: `log (2X) ≥ 0` is used.

### 39.4 Correction to §38

**§38 is superseded.**  The correct statement of the remaining gap is now only §3 of the
three-way split:

| # | gap | status |
|---|---|---|
| 1 | budget with free cutoffs | **closed** (`cutoff_squared_budget_general`, `typeIIBlock_norm_le_general`) |
| 2 | divisor window parameter | **closed** (`windowTypeII`, `tauThree_eq_sub`) |
| 3 | the cofactor pieces falling out of the window difference, and the gap band `a ∈ (n^(1/3), n^(2/5))` | **open** |

So the τ₃ reduction now needs only: (a) a *sum* version of §39.2–39.3 (interchange of
the window difference with `weightedSum`), and (b) an estimate for the residual
cofactor range — item 3, which is the analytic input.

Dossier: 2578 lines (imports `L_goldbach_bulk_density_one`), 121 verified declarations (90 theorems, 22 defs, 9 lemmas),
no `sorry`.

## Milestone 40: Cauchy–Schwarz for the deep-minor pair integral

Both residual estimates of the `τ₃` reduction reduce to one inequality: the deep-minor
bilinear integral is bounded by the product of the two `L²` masses.  Verified:

```lean
theorem norm_phase (x : ℝ) : ‖phase x‖ = 1

/-- Cauchy–Schwarz for a product integral on a set inside `(0,1]`. -/
theorem norm_setIntegral_mul_le_sqrt {E : Set ℝ} (hE : MeasurableSet E)
    (hEsub : E ⊆ Set.Ioc (0:ℝ) 1) {f g : ℝ → ℂ} (Cf Cg : ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfb : ∀ t, ‖f t‖ ≤ Cf) (hgb : ∀ t, ‖g t‖ ≤ Cg) :
  ‖∫ t in E, f t * g t‖
    ≤ √(∫ t in E, ‖f t‖²) * √(∫ t in E, ‖g t‖²)

/-- **Cross term**: `|Jdeep(u,v)| ≤ ‖S_u‖₂ ‖S_v‖₂`. -/
theorem norm_deepCross_le_sqrt {E} (hE) (hEsub) (n) (u v) (Cu Cv) (hu) (hv) :
  ‖∫ t in E, S_u t * S_v t * phase (-(n:ℝ)*t)‖
    ≤ √(∫ t in E, ‖S_u t‖²) * √(∫ t in E, ‖S_v t‖²)

/-- **Self term**: `|Jdeep(u,u)| ≤ ‖S_u‖₂²`. -/
theorem norm_deepSelf_le {E} (hE) (hEsub) (n) (u) (Cu) (hu) :
  ‖∫ t in E, S_u t * S_u t * phase (-(n:ℝ)*t)‖ ≤ ∫ t in E, ‖S_u t‖²
```

> **⊘ RETRACTED — see M41.1.**  Everything in this block up to the end of M40 is invalid:
> `B₃·n^(2/5) = n^(16/15) > n`, so the `τ₃` residual is **full-range**, its `L²` mass is
> `≈ ∑|τ₃|² ≈ n log²n`, and none of the four conclusions below (`‖S_res‖₂² = o(n)`,
> `|Jdeep(res,res)| = o(n)`, `|Jdeep(main,res)| = o(n)`,
> `Jdeep(τ₃,τ₃) = Jdeep(main,main) + o(n)`) follows.  The two Cauchy–Schwarz lemmas
> themselves are correct and general; only this application is not.  Do not build on the
> "outcome B" reduction.

Combined with the support lemma of M39 (`le_mul_of_cofactor_le`), the `τ₃` residual is
handled as follows: the residual (`a ≤ n^(2/5)` or `m/a ≤ n^(2/5)`) is supported on
`m ≤ B₃·n^(2/5) = n^(13/15)` **[INVALID: 16/15]**, so

```text
‖S_res‖₂² = ∑_{m ≤ n^(13/15)} |τ_res(m)|² = n^(13/15+o(1)) = o(n)
‖S_res‖₂  = n^(13/30+o(1))
```

and then

```text
|Jdeep(res,res)| ≤ ‖S_res‖₂²                    = o(n)
|Jdeep(main,res)| ≤ ‖S_τ₃‖₂ ‖S_res‖₂ = n^(14/15+o(1)) = o(n)
```

so `Jdeep(τ₃,τ₃) = Jdeep(main,main) + o(n)`.  **This is the reduction of outcome B** in the
outcome table; it is a reduction, not the task.

Landmines recorded:

* In this file `μ` is the Möbius arithmetic function (via
  `open scoped ArithmeticFunction.Moebius`), so `(μ := …)` cannot be used as a named
  argument — `integral_mul_norm_le_Lp_mul_Lq μ` parses `μ` as the Möbius function.
  Workaround: state the `MemLp` hypotheses with `ENNReal.ofReal 2` so the measure is
  inferred, and pass no `μ`.
* `Real.rpow_natCast`/`Real.rpow_two`: `integral_mul_norm_le_Lp_mul_Lq` produces
  `x ^ (2 : ℝ)` (real power), while the natural statement uses `x ^ 2`.  `Real.rpow_two`
  is the rewrite; `simp only [Real.rpow_natCast]` makes no progress on the literal.
* `(μ := …)` aside, `∫ t in E, ‖g t‖ ^ 2` prints beta-reduced but `rw` inside
  `Filter.Eventually.of_forall (fun t => ·)` sees `(fun t => …) t`; use
  `simp only [hnorm t]` rather than `rw`.
* `Jdeep`'s integrand is `(S_u * S_v) * phase`, while the general lemma yields
  `S_u * (S_v * phase)`; the bridge is one `integral_congr_ae` with `simp only [mul_assoc]`.

Dossier: 2578 -> 2680 lines, 126 verified declarations (95 theorems, 22 defs, 9 lemmas), no `sorry`.

## Milestone 41 (branch `research/b1b1-exponent-fix`): exponent correction + the `τ₁` peeling

This branch exists because M36.5 and M40 contain an arithmetic error that invalidates
their conclusions.  It does **not** rewrite those sections; it corrects them here.

### 41.1 The error

Both sections assert

```text
B₃ · n^(2/5) = n^(13/15)
```

Exact arithmetic: `2/3 + 2/5 = 10/15 + 6/15 = **16/15**`.  Since `16/15 > 1`, the bound
`m ≤ B₃ · n^(2/5)` is **weaker than `m ≤ n`**, i.e. vacuous.

The Lean lemmas are fine — `le_mul_of_cofactor_le` (M39) really does prove `m ≤ H · V₀`,
and M40's Cauchy–Schwarz lemmas are correct and general.  What is wrong is the
*instantiation* `H = B₃ = n^(2/3)`, `V₀ = n^(2/5)`.

**Consequently the following are NOT established** (they appear in M36.5 and M40):

```text
‖S_res‖₂² = n^(13/15+o(1)) = o(n)                    ✗
|Jdeep(res,res)| = o(n)                              ✗
|Jdeep(main,res)| ≤ n^(14/15+o(1)) = o(n)            ✗
Jdeep(τ₃,τ₃) = Jdeep(main,main) + o(n)               ✗
```

The `τ₃` residual is full-range, so its `L²` mass is `≈ ∑|τ₃|² ≈ n log²n`, not `o(n)`.

### 41.2 The correct table

Support of the low-cofactor part (`m/a ≤ V`) is `m ≤ H_i · V`.  With `V = n^(2/5)`:

| cell | divisor upper bound `H_i` | `H_i · V` | short support? |
|---|---|---|---|
| **τ₁** | `B₁ = n^(1/4)` | **`n^(13/20)`** | **yes** |
| **τ₂** | `B₂ = n^(1/3)` | **`n^(11/15)`** | **yes** |
| τ₃ | `B₃ = n^(2/3)` | `n^(16/15)` | no (vacuous) |
| τ₄ | `n/U = n^(15/16)` | `n^(107/80)` | no (vacuous) |

**The trick works for `τ₁` and `τ₂` and fails for `τ₃`** — the opposite of what M40 says.
The reason is structural: the support bound needs `H_i · V < n`, and `τ₃`'s divisor band
reaches `n^(2/3)`, which is already too high.

For `τ₃` the only short piece is `m/a ≤ n^(1/3−δ)` (giving `m ≤ n^(1−δ)`); the rest of the
cofactor interval, and the whole gap band `a ∈ (n^(1/3), n^(2/5))`, are full-range:
`n^(2/5) · n^(2/3) = n^(16/15)`.

### 41.3 What is verified here: the `τ₁` peeling

```lean
def lowBandCoefficientBot (n V : ℕ) : ℕ → ℝ   -- τ₁ with m/a ≤ V
def lowBandCoefficientTop (n V : ℕ) : ℕ → ℝ   -- τ₁ with V < m/a

theorem lowBandCoefficient_eq_bot_add_top (n V m) :
  lowBandCoefficient (U n) (B₁ n) m = Bot n V m + Top n V m

theorem lowBandCoefficientBot_eq_zero (n V m) (hm : B₁ n * V < m) : Bot n V m = 0

theorem lowBandCoefficientBot_abs_le (n V m) {T} (hT) (hc) :
  ‖(Bot n V m : ℂ)‖ ≤ T * Real.log m

theorem integral_plainPolynomial_norm_sq (n) (a : ℕ → ℂ) :
  ∫₀¹ ‖plainPolynomial n a t‖² = ∑_{m ≤ n} ‖a m‖²

theorem sum_bot_norm_sq_localize (n V) (hV : B₁ n * V ≤ n) :
  ∑_{m ≤ n} ‖Bot n V m‖² = ∑_{m ≤ B₁ n * V} ‖Bot n V m‖²

/-- **The peeling bound.** -/
theorem integral_bot_norm_sq_le (n V) (hV : B₁ n * V ≤ n) {T} (hT) (hc) :
  ∫₀¹ ‖S_{Bot n V}‖² ≤ T² * (B₁ n * V + 1) * (Real.log n)²
```

So the low-cofactor part's `L²` mass is bounded by an **explicit** quantity, and by M40's
`norm_deepSelf_le` / `norm_deepCross_le_sqrt` its self term and its cross term with `τ₁`
are controlled by it.

### 41.4 The two regimes for `V`

The bound is `T² · (B₁ V + 1) · log²n`, parametric in the coefficient bound `T`:

| choice of `T` | condition for `o(n)` | admissible `V` |
|---|---|---|
| crude `T ≤ B₁ = n^(1/4)` (from `abs_lowMoebiusWeight_le` + `a.divisors.card ≤ a`) | `B₁³ V = o(n)` | `V = n^(1/4 − δ)` |
| divisor bound `T = n^o(1)` | `B₁ V = o(n)` | **`V = n^(3/4 − δ)`** |

The second regime is the interesting one: it peels off everything with cofactor
`≤ n^(3/4−δ)`, leaving

```text
a ∈ (n^(1/16), n^(1/4)] ,   m/a > n^(3/4−δ) .
```

Since `Λ` is supported on prime powers, `m/a > n^(3/4−δ)` forces `m/a` to be essentially a
**prime**.  So `b1-b1` reduces to a "small divisor × large prime" Type-I object.

**Not yet formalized:** the instantiation `T ≤ B₁` (needs `a.divisors.card ≤ a`), and the
divisor bound `T = n^o(1)`.  The verified lemma is parametric in `T`, so both are one
instantiation away.

### 41.5 Status of the two questions

* **Is `h33` reachable?**  No.  Its residual is full-range (§41.2), the sup route is
  uniformly dead (`|Jdeep| ≲ N²/U` needs `U = ω(N)`), and one-sidedness only gives
  `Re Jdeep ≥ −∫_{Aᶜ}(Im T)²` with `T = S·e(−nt/2)`, still against a total `≈ n log²n`.
* **Can the `τ₃` cofactor interval + gap band be resolved?**  Not by support/Cauchy–Schwarz.
  Only `m/a ≤ n^(1/3−δ)` is short.  The rest needs a new minor-arc estimate.

Dossier on this branch: 2840 lines, no `sorry`.

## Milestone 42: both instantiations of the peeling bound

M41.4 listed two unformalised steps.  One is done; the other is replaced by a **free**
stronger regime, and the original "divisor bound" target is shown to be the only one that
needs new mathematics.

### 42.1 `T ≤ B₁` — done

```lean
theorem lowMoebiusWeight_abs_le_lowCut (n a : ℕ) (ha : a ≤ lowCut n) :
  |lowMoebiusWeight (cutoffU n) a| ≤ (lowCut n : ℝ)      -- card_divisors_le_self

theorem integral_bot_norm_sq_le_lowCut (n V : ℕ) (hV : lowCut n * V ≤ n) :
  ∫₀¹ ‖S_{Bot n V}‖²
    ≤ (B₁ n)² * (B₁ n · V + 1) * (log n)²
```

Scale: `B₁²·B₁·V = n^(1/2)·n^(1/4)·V = n^(3/4)V`, so `V = o(n^(1/4))` suffices.

### 42.2 The "divisor bound" step: `T` bounds the **coefficient**, not `d(m)`

M41.4 asked for `T = n^o(1)` from a divisor bound on `m ≤ B₁V`.  That is not what the
lemma needs.  Reading `lowBandCoefficientBot_abs_le`:

```lean
(hc : ∀ a, cutoffU n < a → a ≤ lowCut n → |lowMoebiusWeight (cutoffU n) a| ≤ T)
```

`T` bounds `c_U(a) = ∑_{U<d|a} μ(d)`, and by `lowMoebiusWeight_eq_neg_small`
(`c_U(a) = −∑_{d|a, d≤U} μ(d)` for `a > 1` — Möbius cancellation) we get **for free**

```lean
theorem lowMoebiusWeight_abs_le_cutoffU (U a : ℕ) (ha : 1 < a) :
  |lowMoebiusWeight U a| ≤ (U : ℝ)          -- ≤ #{d | a : d ≤ U} ≤ U

theorem integral_bot_norm_sq_le_cutoffU (n V : ℕ) (hV) (hU : 1 ≤ cutoffU n) :
  ∫₀¹ ‖S_{Bot n V}‖² ≤ (U n)² * (B₁ n · V + 1) * (log n)²
```

Scale: `U²·B₁·V = n^(1/8)·n^(1/4)·V = n^(3/8)V`, so **`V = o(n^(5/8))` suffices** —
strictly better than 42.1, and unconditional.

### 42.3 The three regimes

| `T` bound on `c_U(a)` | source | total scale | admissible `V` |
|---|---|---|---|
| `B₁ = n^(1/4)` | `card_divisors_le_self` | `n^(3/4)V` | `V = n^(1/4−δ)` |
| **`U = n^(1/16)`** | **Möbius cancellation (free)** | **`n^(3/8)V`** | **`V = n^(5/8−δ)`** |
| `n^ε` | divisor bound `d(n) = n^o(1)` | `n^(1/4+2ε)V` | `V = n^(3/4−2ε)` |

The free bound is `min(U, 2√a) = U` for `a ≤ B₁ = n^(1/4)` (paired divisors give
`#{d | a : d ≤ U} ≤ 2√a = n^(1/8) > n^(1/16)`), so `U` is the best **elementary** value.

### 42.4 What remains for the third regime

`V = n^(3/4−δ)` needs `max_{a ≤ n^(1/4)} d(a) = n^o(1)`, i.e.

```lean
∀ ε > 0, ∃ N, ∀ m ≥ N, (m.divisors.card : ℝ) ≤ (m : ℝ) ^ ε
```

**This is not in Mathlib.**  Grepping `Mathlib` for `divisors.card` gives only
`card_divisors_le_self : #n.divisors ≤ n` and `card_divisors` (the factorization product);
there is no `n^o(1)` bound, and no `2^{ω(n)}`-versus-`n` asymptotics.  Building it needs:
`Nat.card_divisors` (exists) + `∏_{p|n} p ∣ n` (exists, `prod_primeFactors_dvd`) +
`∏ p^{e_p} = n` + the `e+1 ≤ C_δ p^{δe}` estimate + absorbing `C_δ^{ω(n)}`.  That is a
standalone 200+ line formalisation and is **not** attempted here.

So the peeling is now verified in the two elementary regimes; the third is a clean,
well-scoped open formalisation target rather than an unknown.

Dossier: 2840 -> 2907 lines, no `sorry`.

## Milestone 43: towards `d(n) = n^o(1)` — step 1 of 3

Target (the third peeling regime, `V = n^(3/4−δ)`):

```lean
∀ ε > 0, ∃ N, ∀ m ≥ N, (m.divisors.card : ℝ) ≤ (m : ℝ) ^ ε
```

Not in Mathlib.  Plan, in three steps:

1. **exponent-vs-prime-power** (this milestone, done);
2. product assembly: `d(n) ≤ C_δ^(ω n) · n^δ`;
3. the `ω`-saving: `ω(n) ≤ ε' log n` eventually, from `(ω n)! ≤ n`.

### 43.1 Step 1 — verified

```lean
theorem add_one_le_rpow_mul (δ : ℝ) (hδ : 0 < δ) (p : ℕ) (hp : 2 ≤ p)
    (e : ℕ) (he : 1 ≤ e) :
  (e : ℝ) + 1 ≤ (2 / (δ * Real.log 2)) * (p : ℝ) ^ (δ * (e : ℝ))
```

Proof chain (all in Lean):

```text
2^δ = exp(δ log 2) ≥ 1 + δ log 2                    -- Real.rpow_def_of_pos, Real.add_one_le_exp
p^δ ≥ 2^δ                                          -- Real.rpow_le_rpow
(1 + δ log2)^e ≤ (p^δ)^e                            -- Bernoulli: one_add_mul_le_pow
(2/(δ log2))·(1 + e δ log2) = 2/(δ log2) + 2e ≥ e+1
p^(δ e) = (p^δ)^e                                   -- Real.rpow_mul, rpow_natCast
```

So `C_δ := 2/(δ log 2)` is an explicit, usable constant.

### 43.2 What steps 2 and 3 still need

* Step 2: `Nat.card_divisors` (exists: `#n.divisors = ∏_{p ∈ n.primeFactors}(n.factorization p + 1)`),
  then `∏ (e+1) ≤ ∏ C_δ p^(δ e) = C_δ^(ω n) · (∏ p^e)^δ = C_δ^(ω n) · n^δ`, using
  `Nat.prod_factorization_pow_eq_self` (exists) and `∏ x_i^δ = (∏ x_i)^δ` for `x_i ≥ 0`
  (elementary induction with `Real.mul_rpow`).  Estimated ~80 lines.
* Step 3: `ω! ≤ n` (the product of `ω` distinct primes is at least `ω!`), then
  `ω log ω ≲ log n`, giving `ω ≤ 2 log n / log log n`, hence `C_δ^ω ≤ n^(ε−δ)` eventually.
  Needs `Nat.factorial` growth estimates and `Real.log`/`log log` manipulation;
  estimated ~150–250 lines.

Neither step needs new mathematics; both are length.  Step 1 is the only part with a
genuine choice of constant.

Dossier: 2907 -> 2970 lines, no `sorry`.

## Milestone 44: `d(n) = n^o(1)` — step 2 of 3 done

Per the PR constraint (one Lean file, ≤ 2 MiB; the file is 152 KiB) everything goes into
`b1b1_port.lean` rather than a second module that would have to be inlined later.

### 44.1 Verified

```lean
/-- `∏ (x i)^δ = (∏ x i)^δ` for nonnegative factors. -/
theorem prod_rpow_eq_rpow_prod …

/-- Product monotonicity for nonnegative real factors.
    (`MulLeftMono ℝ` does *not* hold, so `Finset.prod_le_prod` is unusable here.) -/
theorem prod_le_prod_nonneg …

/-- **`d(n) ≤ C_δ^(ω n) · n^δ`** with `C_δ = 2/(δ log 2)`. -/
theorem card_divisors_le_pow_mul_rpow (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hn : 0 < n) :
  (n.divisors.card : ℝ) ≤ (2 / (δ * Real.log 2)) ^ n.primeFactors.card * (n : ℝ) ^ δ
```

Assembly: `Nat.card_divisors` ⟹ `d(n) = ∏_{p ∈ primeFactors}(e_p+1)`; step 1 applies
factorwise; `∏ p^(δ e_p) = (∏ p^e_p)^δ = n^δ` via `prod_rpow_eq_rpow_prod`,
`Nat.prod_factorization_pow_eq_self`, `Real.rpow_mul`, `Real.rpow_natCast`.

### 44.2 Landmines recorded

* `Finset.prod_le_prod` needs `[MulLeftMono N]`, which **fails for `ℝ`** (negatives).
  There is no `prod_le_prod_of_nonneg` in this Mathlib; `prod_le_prod_nonneg` above is
  the replacement (induction + `mul_le_mul`).
* `Nat.prod_factorization_pow_eq_self (hn : n ≠ 0) : n.factorization.prod (· ^ ·) = n`;
  to use it on `∏ p ∈ n.primeFactors, …` rewrite with
  `← Nat.prod_factorization_eq_prod_primeFactors` first.
* `rw [← hnat]` where `hnat : ∏ … = n` will also rewrite occurrences of `n` *inside*
  `n.primeFactors`.  Cast the ℕ identity to `ℝ` instead and `push_cast` it.
* `↑(e + 1)` (ℕ addition, then cast) versus `↑e + 1` (real addition) needs `push_cast`
  before applying step 1.

### 44.3 Step 3 remains — and why it is not short

Step 2 leaves `d(n) ≤ C_δ^ω · n^δ`.  For `d(n) ≤ n^ε` one needs
`C_δ^ω ≤ n^(ε−δ)`, i.e. `ω(n) log C_δ ≤ (ε−δ) log n`.

* `ω(n) ≤ log₂ n` (trivial) gives `ω log C_δ ≤ (log C_δ/log 2) log n`, and
  `log C_δ/log 2 ≤ ε/2` forces `δ ≥ 4/(ε log 2)·2^{−ε/2} → ∞` as `ε → 0`.  **Insufficient.**
* A `√(log n)` bound on `ω` would suffice, but is **false** in general; the truth is
  `ω(n) ≤ (1+o(1)) log n / log log n`, and the elementary route is
  `n ≥ ∏_{p|n} p ≥ ∏_{i≤ω}(i+1) = (ω+1)!`, whence `ω log ω ≲ log n`.

So step 3 needs `Nat.factorial` growth bounds plus `Real.log`/`Real.log ∘ Real.log`
manipulation: ~150–250 lines, no new mathematics.  The three ingredients are:

```text
(A)  ∏_{i<ω}(i+1) = ω! ≤ ∏_{p ∈ primeFactors} p ≤ n
(B)  ω! ≥ (ω/2)^(ω/2)          -- discard the small half of the factors
(C)  ω ≤ ε' log n when ω ≥ K(ε') and ε' log 2 · log(K/2) ≥ 2
```

Dossier: 2956 -> 3034 lines, no `sorry`.  (127 theorems, 24 defs, 9 lemmas.)

## Milestone 45: `d(n) = n^o(1)` — **complete**, and without any `log log`

M43 listed three steps and estimated 150–250 lines for step 3 (`ω(n)` saving via `ω! ≤ n`).
**Step 3 turned out to be unnecessary.**  There is a split that avoids `ω` entirely.

### 45.1 The idea

For a prime `p ≥ 2^(1/δ)`,

```text
e + 1 ≤ 2^e ≤ p^(δ e)          -- no constant at all, because 2 ≤ p^δ.
```

So only the primes **below** `2^(1/δ)` — at most `⌈2^(1/δ)⌉` of them, since they lie in
`Finset.range ⌈2^(1/δ)⌉` — carry the constant `C_δ = 2/(δ log 2)`.  Splitting
`n.primeFactors` into `small` (`p < ⌈2^(1/δ)⌉`) and `large`:

```text
∏_{small}(e+1) ≤ C_δ^(#small) · ∏_{small} p^(δ e) ≤ C_δ^(⌈2^(1/δ)⌉) · n^δ
∏_{large}(e+1) ≤ ∏_{large} p^(δ e)                ≤ n^δ
```

hence `d(n) ≤ C_δ^(⌈2^(1/δ)⌉) · n^(2δ)`.  **No `ω(n)`, no `log log`, no `ω!`.**

### 45.2 Verified

```lean
theorem add_one_le_two_pow (e : ℕ) : e + 1 ≤ 2 ^ e
theorem one_le_prod_of_one_le' …            -- 1 ≤ ∏ f for real f ≥ 1
theorem add_one_le_rpow_of_large (δ) (hδ) (p) (hp : 2^(1/δ) ≤ p) (e) :
  (e:ℝ) + 1 ≤ p^(δ e)
theorem card_divisors_le_const_mul_rpow (n) (δ) (hδ) (hn : 0 < n) :
  (n.divisors.card : ℝ) ≤
    (max (2/(δ log 2)) 1) ^ (Nat.ceil (2^(1/δ))) * n^(2δ)
/-- **`d(n) = n^o(1)`** -/
theorem card_divisors_le_rpow_eventually (ε : ℝ) (hε : 0 < ε) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n.divisors.card : ℝ) ≤ (n : ℝ) ^ ε
```

The constant is explicit: `B_δ = (max (2/(δ log 2)) 1)^(⌈2^(1/δ)⌉)`, and the threshold is
`N = ⌈B_(ε/4)^(2/ε)⌉ + 1` (using `δ = ε/4` so that `2δ = ε/2` leaves room for `B ≤ n^(ε/2)`).

### 45.3 Consequences for the peeling

`integral_bot_norm_sq_le` is now instantiable at `T = n^ε`:

```text
∫₀¹ ‖S_{Bot n V}‖²  ≤  T² · (B₁ V + 1) · log²n  =  n^(1/4 + 2ε) V · log²n
```

so `V = n^(3/4 − 2ε − δ')` gives `o(n)` — **the third regime of the M42 table**, and the
strongest the peeling can be.  The remaining formal step is to plug
`card_divisors_le_rpow_eventually` into `lowMoebiusWeight_abs_le`'s hypothesis `hc`
(`|c_U(a)| ≤ d(a) ≤ a^(4ε)` for `a ≤ B₁ = n^(1/4)`), which is now a one-liner in principle.

### 45.4 Landmines (all cost a compile round)

* `Finset.one_le_prod` **also** needs `MulLeftMono ℝ` — replaced by `one_le_prod_of_one_le'`.
* `Nat.lt_two_pow_self` has an implicit argument: `(n := e)`.
* `Real.rpow_le_rpow` unification: the first (nonnegativity) argument fixes `x`, so it must be
  `0 ≤ B^(2/ε)`, not `0 ≤ B`.
* Do not `s.find("  calc (n.divisors.card : ℝ)")` to patch — it matches the *earlier*
  occurrence in M44 and silently deletes the rest of the file.

Dossier: 3034 -> 3258 lines, no `sorry`.  (113 theorems, 24 defs, 12 lemmas.)

## Milestone 46: the third peeling regime is complete

`integral_bot_norm_sq_le`'s coefficient hypothesis is now discharged by the divisor bound.

```lean
theorem integral_bot_norm_sq_le_divisor (n V : ℕ) (hV : lowCut n * V ≤ n)
    {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (hdiv : ∀ m : ℕ, N ≤ m → (m.divisors.card : ℝ) ≤ (m : ℝ) ^ ε) :
  ∫₀¹ ‖S_{Bot n V}‖²
    ≤ (max (N:ℝ) ((lowCut n : ℝ) ^ ε)) ^ 2 * (B₁·V + 1) * (log n) ^ 2

/-- **Third regime**, no extra hypothesis. -/
theorem integral_bot_norm_sq_le_divisor_bound (n V : ℕ) (hV : lowCut n * V ≤ n)
    {ε : ℝ} (hε : 0 < ε) :
  ∃ N : ℕ, ∫₀¹ ‖S_{Bot n V}‖²
    ≤ (max (N:ℝ) ((lowCut n : ℝ) ^ ε)) ^ 2 * (B₁·V + 1) * (log n) ^ 2
```

Discharge of `hc`: for `a ≥ N`,
`|c_U(a)| ≤ a.divisors.card ≤ a^ε ≤ (B₁ n)^ε`; for `a < N`,
`|c_U(a)| ≤ a.divisors.card ≤ a < N`.  So `T = max N (B₁ n)^ε`.

`max N (B₁ n)^ε` avoids needing `lowCut n ≤ n`, which is why the threshold is `B₁ n` and not `n`.

### The corrected three-regime table (final)

| `T` bound on `c_U(a)` | source | total scale | admissible `V` |
|---|---|---|---|
| `B₁ = n^(1/4)` | `card_divisors_le_self` | `n^(3/4) V` | `n^(1/4−δ)` |
| `U = n^(1/16)` | Möbius cancellation (free) | `n^(3/8) V` | `n^(5/8−δ)` |
| **`n^(ε/4)`** | **divisor bound `d(n)=n^o(1)` (M45)** | **`n^(1/4+ε/2) V`** | **`n^(3/4−ε/2−δ)`** |

So `V = n^(3/4−δ')` for any `δ' > ε/2`: the peeling removes **all cofactors below
`n^(3/4−δ)`**, leaving

```text
a ∈ (n^(1/16), n^(1/4)] ,   m/a > n^(3/4−δ) ,
```

and since `m ≤ n` forces `m/a ≤ n^(15/16)`, the surviving cofactor window is only
`(n^(3/4−δ), n^(15/16)]`.

### What this does and does not give

* **Does**: the `τ₁` low-cofactor part is `L²`-small with an explicit bound, unconditionally.
  Combined with M40 (`norm_deepSelf_le`, `norm_deepCross_le_sqrt`), the self and cross terms
  involving `S_{Bot}` are `o(n)`.
* **Does not**: close b1-b1.  The remaining piece is `Jdeep(τ₁^Top, τ₁^Top)`, whose cofactor
  is `> n^(3/4−δ)` — a full-range signed object, not a short one.  The sign problem is
  untouched.

Dossier: 3258 -> 3297 lines, 115 theorems / 24 defs / 9 lemmas, no `sorry`.

## Milestone 47: the exponent sharpens from `n^(2δ)` to `n^δ`; the peeling ceiling

### 47.1 (a) is right — the product is exact

M45 bounded the two half-products *separately* by `n^δ`, losing a factor `n^δ`.  But

```text
∏_{small} p^(δ e) · ∏_{large} p^(δ e) = ∏_{all} p^(δ e) = n^δ      (exact identity)
```

so keeping the products until the very end gives the sharper bound.  Verified:

```lean
theorem card_divisors_le_const_mul_rpow_pow (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hn : 0 < n) :
  (n.divisors.card : ℝ) ≤
    (max (2/(δ log 2)) 1) ^ (Nat.ceil (2^(1/δ))) * (n : ℝ) ^ δ        -- was ^(2δ)

theorem card_divisors_le_rpow_eventually_pow (ε : ℝ) (hε : 0 < ε) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n.divisors.card : ℝ) ≤ (n : ℝ) ^ ε      -- δ = ε/2, not ε/4
```

`δ = ε/2` now suffices (the threshold is `⌈B_(ε/2)^(2/ε)⌉ + 1` instead of
`⌈B_(ε/4)^(2/ε)⌉ + 1`).  Both earlier versions are kept; the `_pow` ones are the sharp ones.

### 47.2 (b) is right — the peeling has hit its ceiling

`integral_bot_norm_sq_le` carries `hV : lowCut n * V ≤ n`, i.e. `V ≤ n / B₁`.  With
`B₁ = n^(1/4)` this is `V < n^(3/4)`, so `V = n^(3/4−δ)` is **the optimum of this
mechanism**, and M46 already attains it.

Cost/benefit of M43–M46 (≈ 300 lines): `V` moved from `n^(5/8)` to `n^(3/4)`, i.e. `n^(1/8)`.
The divisor bound is a reusable Mathlib-grade lemma, but for b1-b1 the marginal return of
this line is exhausted.  Recorded and closed.

### 47.3 What the next idea is *not*

The proposed prime-power sparsity

```text
#{p^k ≤ n^(15/16) : k ≥ 2} = O(n^(15/32) log n)
```

is **not** `d(n) = n^o(1)`.  It is a *counting* statement over an interval, proved
elementarily (for each `k`, `#{p : p^k ≤ X} ≤ X^(1/k)`, summed over `k ≤ log₂ X`), and it
does not use the divisor bound at all.  Conversely the divisor bound says nothing about how
many perfect powers lie below `X`.

Where `d(n) = n^o(1)` *does* enter that argument is the value bound
`|τ^Top(m)| ≤ d(m)·log m = n^o(1)`, which turns the *count* of surviving integers
(`≤ B₁ · n^(15/32) = n^(23/32)`) into an `L²` bound `n^(23/32+o(1)) = o(n)`.

Mathlib has **no** prime-power counting lemma (only `IsPrimePow` + field-cardinality facts),
so it would be built from scratch — the 50–80 line estimate is right.

Dossier: 3297 -> 3441 lines, 119 theorems / 24 defs / 9 lemmas, no `sorry`.

## Milestone 48: prime-power sparsity

Independent of the divisor bound (see M47.3): a counting statement.

```lean
/-- Every higher power lies in the `biUnion` of the `k`-th power images. -/
theorem higherPower_mem_biUnion (X m : ℕ) (hmX : m ≤ X)
    (hm : ∃ p k : ℕ, Nat.Prime p ∧ 2 ≤ k ∧ m = p ^ k) :
  m ∈ (Finset.Icc 2 (Nat.log 2 X)).biUnion
        (fun k => (Finset.range (Nat.sqrt X + 1)).image (fun p => p ^ k))

/-- **Prime-power sparsity**: at most `(log₂ X + 1)·(√X + 1)` higher powers below `X`. -/
theorem card_biUnion_powers_le (X : ℕ) :
  ((Finset.Icc 2 (Nat.log 2 X)).biUnion
      (fun k => (Finset.range (Nat.sqrt X + 1)).image (fun p => p ^ k))).card
    ≤ (Nat.log 2 X + 1) * (Nat.sqrt X + 1)
```

So `#{p^k ≤ X : p prime, k ≥ 2} = O(√X log X)` — with `X = n^(15/16)` this is
`O(n^(15/32) log n)`, and the surviving `m = a·p^k` with `a ≤ B₁ = n^(1/4)` number at most
`n^(23/32+o(1))`.

### Landmine: unbounded existentials are not decidable

The natural statement `(range (X+1)).filter (fun m => ∃ p k, …)` **does not elaborate**:
`∃ p ∈ s, P p` is `Exists (fun p => p ∈ s ∧ P p)`, an unbounded quantifier over `ℕ`, so
`DecidablePred` fails.  Splitting into (i) a membership lemma for a `biUnion` and (ii) a
cardinality bound on that `biUnion` keeps every quantified statement finite and therefore
decidable.  (A `Set.ncard` restatement of the `filter` form would also work; not needed.)

Also: `Finset.card_Icc` is not the name in this Mathlib — use
`Finset.card_le_card` with `Icc 2 K ⊆ range (K+1)`.

Dossier: 3441 -> 3500 lines, 119 theorems / 24 defs / 9 lemmas, no `sorry`.

## Milestone 49: support size of the higher-prime-power part

M48 counted the higher powers `p^k ≤ X`.  The `τ₁` cut needs `m = a·p^k` with `a ≤ B₁`, so
the relevant count is over products.  Verified:

```lean
/-- Membership: `a·p^k` lies in the finite `biUnion` of `k`-th power images. -/
theorem higherPower_product_mem (B X m a p k : ℕ) (ha : a ≤ B) (hpp : Nat.Prime p)
    (hk2 : 2 ≤ k) (hpk : p ^ k ≤ X) (hm : m = a * p ^ k) :
  m ∈ (Finset.Icc 2 (Nat.log 2 X)).biUnion (fun k' =>
        (Finset.range (B + 1)).biUnion (fun a' =>
          (Finset.range (Nat.sqrt X + 1)).image (fun p' => a' * p' ^ k')))

/-- **Support size**: `≤ (log₂X + 1)(B + 1)(√X + 1)`. -/
theorem card_higherPower_products_le (B X : ℕ) :
  ((Finset.Icc 2 (Nat.log 2 X)).biUnion (fun k =>
      (Finset.range (B + 1)).biUnion (fun a =>
        (Finset.range (Nat.sqrt X + 1)).image (fun p => a * p ^ k)))).card
    ≤ (Nat.log 2 X + 1) * (B + 1) * (Nat.sqrt X + 1)
```

### The arithmetic on the `τ₁` cut

`τ₁^Top`'s higher-prime-power part has `a ∈ (n^(1/16), n^(1/4)]` and cofactor
`m/a = p^k`, `k ≥ 2`, with `n^(3/4−δ) < p^k ≤ n/U = n^(15/16)`.  So `X = n^(15/16)`,
`B = B₁ = n^(1/4)`, and

```text
#support  ≤ (log n) · n^(1/4) · n^(1/2 · 15/16)
          = n^(1/4 + 15/32) · log n
          = n^(23/32) · log n .                                     ← matches the estimate
```

With `|τ₁(m)| ≤ d(m)·log m = n^o(1)` (M45 is exactly where the divisor bound enters), the
`L²` mass of that part is

```text
∑ |τ^hp(m)|²  ≤  #support · sup|τ|²  =  n^(23/32+o(1))  =  o(n) .
```

### What is verified here and what is not

* **Verified**: the counting (both lemmas above).  This is the new content; it needed the
  `biUnion`-instead-of-`filter` trick (M48's decidability landmine) applied twice.
* **Not done**: an actual `τ₁^Top`-higher-power coefficient definition plus the `L²`
  assembly.  That needs a `Finset.filter` over `∃ p k, …`, which is again undecidable, so it
  must be phrased as "supported in the M49 set" — i.e. a support hypothesis, not a
  definition.  It is glue (~30 lines), not mathematics.

### Where this leaves the object

After M42–M49 the surviving part of `τ₁^Top` is

```text
a ∈ (n^(1/16), n^(1/4)] ,   m/a > n^(3/4−δ) ,   m/a a PRIME (not a higher power)
```

— literally "small divisor × large prime".  That is a Type-I object.  The repo's Type-I
machinery (`vinogradov-local/type1_bound.lean`) currently reaches `U = n^(1/16)`; `n^(1/4)`
needs a new residue argument.  So the structural reduction is complete, the analytic input
is not.

Dossier: 3500 -> 3573 lines, 121 theorems / 24 defs / 9 lemmas, no `sorry`.

## Milestone 50 (branch `research/b1b1-h33`): the `h33` / `b3-b3-parity` reduction

The parity cell asks for `Re Jdeep ≥ −εn`.  The reduction turns it into an `L²` statement
about the **imaginary part** of a half-shifted polynomial, with no trigonometry:

```text
S = ∑ τ₃(m) e(mt),   T = S · e(−(n/2)t),   hence T² = S² e(−nt)  (the deep integrand)

Re(T²) = (Re T)² − (Im T)²  ≥  −(Im T)² ,
(Im T)² = (‖T‖² − Re T²)/2                    (pointwise algebra)
∫₀¹‖T‖² = ∫₀¹‖S‖² = ∑ τ₃(m)²                  (Parseval)
Re ∫₀¹T² = D₃                                 (diagonal identity)
```

### Verified

```lean
def tauThreeC (n) : ℕ → ℂ
theorem plainPolynomial_sq_phase_expand_gen (n) (c) (t)     -- general frequency expansion
def diagonalSumOf (n) (c) : ℂ
theorem integral_sq_phase_eq_diagonalOf (n) (c)             -- ∫₀¹ S²e(−n·) = D, any c
def halfShift (n) (t) : ℂ
theorem halfShift_sq / T_sq                                 -- T² = S²e(−n·)
theorem norm_halfShift / im_sq_eq                           -- ‖T‖ = ‖S‖; (Im z)² = (‖z‖²−Re z²)/2
theorem intervalIntegrable_indicator_real
theorem integral_imT_sq_eq (n) (c) :
  ∫₀¹ (Im T)² = (∑‖c m‖² − ∫₀¹ Re(S²e(−n·))) / 2

def deepIntegralThree (n) : ℂ
theorem re_deepIntegral3_ge_neg_im_sq (n) :
  −(∫_{Aᶜ} (Im T)²) ≤ ∫_{Aᶜ} Re(S² e(−n·))
```

So **the `h33` floor is equivalent to an `L²` bound on `Im T`** — a `1`-parameter object
instead of the quadruple sum.  This is the cut worth having if `goldbach` decomposes the
task later.

### Now also verified (the three pieces that were missing)

```lean
theorem im_phase (θ) : (phase θ).im = Real.sin (2 * Real.pi * θ)
theorem imT_eq_sin_sum (n) (c) (hc : ∀ m, (c m).im = 0) (t) :
  (Im T) = ∑_{m ≤ n} c(m).re * Real.sin (2 * Real.pi * ((m:ℝ) − n/2) * t)
theorem intervalIntegral_re_eq (f) (hf : Continuous f) :
  ∫₀¹ (f t).re = (∫₀¹ f t).re
/-- **`∫₀¹(Im T)² = ½(∑τ₃² − D₃)`** -/
theorem integral_imT_sq_eq_diagonal (n) (c) (hc : ∀ m, (c m).im = 0) :
  ∫₀¹ (Im T)² = ((∑_{m ≤ n} (c m).re ^ 2) − (diagonalSumOf n c).re) / 2
```

Note: `integral_re` is **unqualified** (root namespace) in this Mathlib —
`MeasureTheory.integral_re` and `RCLike.integral_re` are both unknown.  `(f x).re` versus
`RCLike.re (f x)` also needs a `rfl`-bridge before the rewrite.

### The antisymmetric-difference form — verified

Using `Finset.sum_range_reflect` (reflection `m ↦ n − m`) and
`sin(2π(n/2 − m)t) = −sin(2π(m − n/2)t)`:

```lean
theorem imT_two_mul_eq (n) (c) (hc : ∀ m, (c m).im = 0) (t) :
  2 * (Im T)
    = ∑ m ∈ Finset.range (n+1),
        ((c m).re - (c (n - m)).re) * Real.sin (2 * Real.pi * ((m:ℝ) - n/2) * t)
```

This is the antisymmetric difference made explicit: the summand
`((c m).re − (c(n−m)).re)·sin(2π(m − n/2)t)` is **symmetric about `m = n/2`**, so for even
`n` the whole thing is twice the `k = 1..n/2` sum of
`((c(n/2+k)).re − (c(n/2−k)).re)·sin(2πkt)`.

Sign check (this cost one compile): reflection gives
`∑ c(m).re·sin(m−n/2) = −∑ c(n−m).re·sin(m−n/2)`, i.e. `hstep` carries a **minus**; the
doubling step is `2Σf = Σf − Σg`, not `Σf + Σg`.

### The last cosmetic step (not done)

The `Icc 1 (n/2)` form needs the symmetric-range split
`∑_{m ≤ 2a} g m = 2∑_{k=1}^{a} g(a+k) + g(a)` (with `g(n−m) = g(m)` and `g(a) = 0`),
i.e. `range (2a+1) = {a} ⊔ {a+k} ⊔ {a−k}`.  Pure `Finset` bookkeeping; the mathematical
content is entirely in `imT_two_mul_eq` above.

### Landmines

* `Complex.sq_abs` does not exist; use `← Complex.normSq_eq_norm_sq` + `Complex.normSq_apply`.
* `indicator_intervalIntegrable` is `ℂ`-valued, so it coerces real-valued functions; wrote
  `intervalIntegrable_indicator_real`.
* `set`-defined functions print as `(fun x => …) x` and `simp only`/`dsimp only` do not always
  beta-reduce; writing the raw lambdas avoids it entirely.
* `Finset.card_Icc` is absent in this Mathlib.

Dossier: 3573 → 3889 lines, no `sorry`.

## Milestone 51: the actual prime-cofactor reduction of `τ₁^Top`

M49 counted products `a·p^k` but left the coefficient-level split and its `L²` estimate
undone.  These are now supplied using only the decidable test `Nat.Prime (m/a)`:

```lean
def lowBandCoefficientTopPrime (n V : ℕ) : ℕ → ℝ
def lowBandCoefficientTopProper (n V : ℕ) : ℕ → ℝ

theorem lowBandCoefficientTop_eq_prime_add_proper (n V m) :
  Top n V m = TopPrime n V m + TopProper n V m

theorem lowBandCoefficientTopProper_abs_le :
  ‖(TopProper n V m : ℂ)‖ ≤ T * Real.log m

theorem lowBandCoefficientTopProper_mem_cover (hmn : m ≤ n)
    (hm : TopProper n V m ≠ 0) :
  m ∈ {a · p^k | a ≤ B₁, p prime, 2 ≤ k, p^k ≤ n}

theorem sum_topProper_norm_sq_le :
  ∑_{m ≤ n} ‖TopProper n V m‖²
    ≤ T² · (log n)² · #(M49 product cover with X = n)

theorem integral_topProper_norm_sq_le_divisor_explicit (ε > 0) :
  ∃ N, ∫₀¹ ‖S_{TopProper}‖²
    ≤ (max N (B₁ n)^ε)² · (log n)²
        · (log₂ n + 1)(B₁ n + 1)(√n + 1)
```

Using `X = n` instead of the sharper `X = n/U` is deliberate: it avoids all cutoff
positivity and natural-division side conditions, and is already sufficient.  The support
count is `O(B₁ √n log n) = O(n^(3/4) log n)`.  Once `N ≤ (B₁ n)^ε`, the displayed `L²`
bound has scale

```text
n^(3/4 + ε/2) · (log n)³ = o(n)       for ε < 1/2 .
```

The M40 Cauchy–Schwarz bounds therefore discard both the proper-power self term and its
cross term with the prime part.  Together with M46's low-cofactor peeling, the only
surviving coefficient is

```text
a ∈ (n^(1/16), n^(1/4)] ,   m/a > V ,   m/a prime ,
```

up to two unconditional `L²`-small errors.  This is the actual "small divisor × large
prime" reduction anticipated in M49, rather than only a support-counting statement.  The
signed deep-minor estimate for that prime-cofactor part remains open; no pointwise,
Parseval, or absolute-value estimate in this dossier closes it.

Dossier: 3889 → 4090 lines, no `sorry`.  The complete file passes `lake env lean` with
Lean 4.36.0 and the locked Mathlib cache at the original 4,000,000-heartbeat limit.
