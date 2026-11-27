# HJSW two-periodic fold optimality: equality side

The no-three-in-line desk now carries `L-no-three-in-line-fold-optimality-attained`.
For every odd prime `p`, the HJSW two-periodic fold family on the `2p x 2p` grid with
translation `t = (p-1)/2` and the deleted-corner rule attains exactly `3 (p - 1)` lift
points without three collinear points.  Together with the upper-bound task this pins the
optimal value of the fold family to `3 (p - 1)`.

The claimable lemma is self-contained: its statement is the closed `let`-chain `Prop`
below (translation, inversion cap, four lift points per fibre, two-periodic mask,
non-collinearity, and the exact count), so a proof file needs only `import Mathlib`.

Reference: Hall, Jackson, Sudbery, Wild, *Some advances in the no-three-in-line problem*,
Discrete Mathematics 18 (1977) 133-140 (HJSW construction).
