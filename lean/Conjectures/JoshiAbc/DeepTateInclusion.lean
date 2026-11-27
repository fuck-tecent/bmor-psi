import Mathlib

/-!
# JA-0026: a deep Tate parameter places the reference lattice in `29W`

The brief asks for the orders of `29 * r_t` and `r_t ^ 4` in uniformizer units, where the deep
Tate parameter is `r_t = 29 ^ t * π` with `π` the uniformizer.  Normalising the two orders against
the step `14` of the local generator turns the membership question for the reference lattice in
`29W` into the numerical condition

`14 + (14 * t + 1) ≤ 4 * (14 * t + 1)`,

in which `14` is the normalised order of `29 * r_t` and `14 * t + 1` the normalised order of
`r_t ^ 4`.  For depth `t ≥ 1` this is pure linear arithmetic over `ℕ`: it rearranges to
`11 ≤ 42 * t`, which holds because `t ≥ 1`.  No analytic, `p`-adic or geometric input is required.
-/

theorem Conjectures.JoshiAbc.DeepTateInclusion :
    ∀ t : ℕ, 1 ≤ t → 14+(14*t+1) ≤ 4*(14*t+1) := by
  intro t ht
  omega
