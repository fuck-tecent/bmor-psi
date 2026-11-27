# Weighted point piercing at side 4.661

The frozen statement asks for finitely many rational sites with natural weights and a threshold \(q>0\). Their total weight must be below \(17q\), while the sites inside every admissible open unit square must have weight at least \(q\).

At side \(4661/1000\), the accompanying certificate builds 560 admissible open squares with positive integer weights in 70 dihedral orbits. Every point has depth at most \(8{,}015{,}919\), including points on box edges. Their total weight is \(136{,}270{,}632=17\cdot 8{,}015{,}919+9\). Double-counting incidence forces any point certificate to have weight strictly above \(17q\).

## Comparison with the documented packing

At the rational outward ceiling \(4.6755300936045509516342148538535054\) for Bidwell's construction, the 17 pairwise interior-disjoint unit squares force total point weight at least \(17q\). The [certified endpoint record](https://squaremath.org/cases/17.html#certified-endpoint-upper-bound) documents that comparison. The new obstruction holds from \(4.661\) onward. A larger container contains the same 560 admissible squares, with the same point-depth bound on the whole plane. This extends the point-certificate obstruction to the interval from \(4.661\) up to the published packing scale.

## Consequence for the lower-bound route

The task excludes the single weighted-point mechanism proposed in `L-square-packing-seventeen-weighted-sites-4661`. The geometric exclusion sought by `L-square-packing-seventeen-lower-4661` still needs another certificate. Guzhou0806's independently replayed R071 bound, \(4.66044275\), uses a family of compound charges. [Seventeen-square result record](https://squaremath.org/cases/17.html)

## Replay

The [certificate source](SeventeenWeightedSites4661RefuteCertificate.lean) proves the exact negation in the project's pinned toolchain. From the repository's `lean` directory, run:

```sh
lake env lean --threads=7 ../research/problems/square-packing/routes/seventeen-square-frontier/SeventeenWeightedSites4661RefuteCertificate.lean
```

The proof checks all 49 boxes in the kernel and reports only `propext`, `Classical.choice`, and `Quot.sound` for the final theorem.

## 中文摘要

在边长 \(4661/1000\) 的容器内取 560 个合法开单位正方形。分盒证明任意点的荷载至多为 \(8{,}015{,}919\)。方块总权为 \(136{,}270{,}632\)，比上界的 17 倍多 9。对加权点和方块双重计数后，总点权无论如何都超过 \(17q\)，从而否定原来的单点加权证书命题。这把由 Bidwell 已核验构型推得的障碍推进到更小边长。排除边长 \(4.661\) 的实际装填还需独立的几何证明。
