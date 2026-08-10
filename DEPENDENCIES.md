# Published dependency ledger

Published inputs are kept separate from the new candidate deductions.

## Core Landesman--Litt inputs

### Canonical representations of surface groups

Aaron Landesman and Daniel Litt, *Annals of Mathematics* 199 (2024),
823--897. [Published version](https://annals.math.princeton.edu/2024/199-2/p06)
and [arXiv:2205.15352v4](https://arxiv.org/abs/2205.15352v4).

| Source item | Use in the manuscript |
|---|---|
| Theorem 1.2.1 | Published finite-image range $r<\sqrt{g+1}$ |
| Lemma 2.2.3 and the proof of Lemma 2.2.2 | Finite-cover projective globalization and uniqueness of its projective intertwiners |
| Lemmas 2.1.4--2.1.5 and Lemma 2.4.1 | Finite-index base image, normality of the fibre group, and total-space unitarity |
| Proposition 2.3.4 and Corollary 2.3.5 | Linear globalization after dominant etale base change |
| Proposition 4.2.2 and Lemma 6.1.1 | Rank-one fixed-part construction and Hodge-type case split |
| Theorem 4.1.1 and Theorem 5.1.6 | Logarithmic de Rham description of the Hodge filtration and multiplication map |
| Proposition 8.2.1; Lemmas 8.3.3--8.3.4; Proposition 8.4.1; Lemmas 8.5.1--8.5.2 | Rigidity, integrality, unitary finite image, and formal constancy |
| Lemma 8.6.1 and Section 8.7 | Characteristic extensions and socle induction |

### Geometric local systems on very general curves and isomonodromy

Aaron Landesman and Daniel Litt, *Journal of the American Mathematical
Society* 37 (2024), 683--729.
[Published version](https://doi.org/10.1090/jams/1038) and
[arXiv:2202.00039v3](https://arxiv.org/abs/2202.00039v3).

| Source item | Use in the manuscript |
|---|---|
| Lemma 6.2.3 | Clifford/HN inequality and equality chain |
| Proposition 6.3.6 | High-HN quotient and section-deficit bound |
| Theorem 1.2.13 | Unitarity for the stated isomonodromic PVHS range |

## Other published inputs

| Source | Use in the manuscript |
|---|---|
| Brambila-Paz, Grzegorczyk, and Newstead, *Geography of Brill--Noether loci for small slopes*, J. Algebraic Geom. 6 (1997), 645--669; [arXiv](https://arxiv.org/abs/alg-geom/9511003) | Small-slope Brill--Noether bounds |
| Earle and Kra, *On sections of some holomorphic families of closed Riemann surfaces*, Acta Math. 137 (1976), 49--79 | Classification of sections of universal-curve families |
| Chen and Salter, *The Birman exact sequence does not virtually split*, Math. Res. Lett. 28 (2021), 383--413; [arXiv](https://arxiv.org/abs/1804.11235) | Exclusion of a degree-one section on a finite cover of the unpointed universal curve; a pointed application first needs separate descent of its fixed part and Hodge line to a closed family |

## New interfaces

| Interface | Status in this repository |
|---|---|
| Stable endpoint $d\ge g-s+1$, $d\ge2$ | `PROVED CONDITIONAL ON` the cited HN/equality chain |
| Normalizer boundary-cocycle obstruction | `PROVED` as a Cech and $\mathfrak{sl}_3$ normalizer calculation; its applications additionally use $H^0(C,E)=0$ to make the full extension boundary injective |
| Zero-weight genus-five $q=9$ elimination after closed descent | `CANDIDATE`; the direct boundary-cocycle route is displayed in full |
| Zero-weight genus-five $q=9$, $h=2$ Pfaffian and spectral reduction | `CANDIDATE`; included as a separate reconstruction and no longer load-bearing |
| Periodic-chain determinant theorem | `PROVED` as a local algebra statement |
| Fixed-part line on every connected finite cover | `PROVED CONDITIONAL ON` Landesman--Litt Proposition 4.2.2, Lemma 6.1.1, and Theorems 4.1.1 and 5.1.6 |
| Global canonical-Deligne determinant use | `PROVED` by the periodic-chain calculation together with the intrinsic generic determinant character, whose DVR extensions have zeros but no poles and therefore glue; retained as an independent reconstruction rather than a main-proof dependency |
| Pointed boundary descent for an effective degree-one Hodge line | `PROVED` only under the manuscript's $S=0$, Zariski-dense adjoint hypotheses; Chen--Salter is used after that descent, and no general pointed-section exclusion is claimed |
| Rank-three formal propagation | `PROVED CONDITIONAL ON` the specialized fixed-part and Artin substitutions in the cited pipeline |

No published source listed here states the new $g\ge5$ conclusion.

The exact role of the published strict-rank hypothesis in Sections 8.2--8.7 is
tracked in [PIPELINE_AUDIT.md](PIPELINE_AUDIT.md).
The load-bearing interfaces and the independent determinant reconstruction
are recorded in [LOAD_BEARING_AUDIT.md](LOAD_BEARING_AUDIT.md).
