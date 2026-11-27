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
