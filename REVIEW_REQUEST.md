# Focused review request

## Status

This repository contains a `CANDIDATE` manuscript proposing a new proof. It is
not an established theorem. No claim is made in genus three or four.

## Claim under review

For $g\geq5$ and $n\geq0$, the manuscript argues that a representation

```math
\rho:\pi_1(\Sigma_{g,n})\longrightarrow\mathrm{GL}_3(\mathbb C)
```

with finite mapping-class-group orbit up to conjugacy has finite image.
Landesman--Litt prove the corresponding statement when
$r<\sqrt{g+1}$, which covers rank three directly for $g\geq9$.

## Highest-value checks

A focused review of the following interfaces would be especially useful:

1. **Normalizer boundary-cocycle obstruction:** Section 6. Does the Cech
   identity for global quotient-normalizer sections force
   $[x,y]=\lambda(x)y-\lambda(y)x$ when the full extension boundary is
   injective? Does the displayed $\mathfrak{sl}_3$ normalizer calculation
   then exclude every generically rank-three space of global sections? In
   both genus-five applications, does $H^0(C,E)=0$ give exactly the required
   injectivity of $H^0(C,E/M)\to H^1(C,M)$?
2. **Fixed part, boundary descent, and full finite cover:** Section 4 and the
   fixed-part Hodge-section subsection of Section 10. Does the rank-one fixed
   part give a global rank-zero Hodge line on
   every connected finite-etale cover? In the dense $S=0$ branch, does the
   point-pushing calculation kill the boundary summands and descend that line
   to a finite cover of the unpointed moduli space before Chen--Salter is used?
   Does generic degree-one effectivity then produce a section without
   shrinking the base? Does the general-fibre remark justify every later
   nonhyperelliptic, non-Weierstrass, and pointed nonspecial-divisor test?
3. **Formal propagation:** Section 14. Does finite-cover adjoint vanishing
   pass correctly to the dominant-etale Artin base for irreducible, reducible
   nonscalar, and scalar residual systems, and do the cited downstream
   Landesman--Litt arguments use no additional strict-rank hypothesis?
4. **Optional separate reconstructions:** In the non-load-bearing $q=9$ and
   canonical-Deligne sections, do the Pfaffian/spectral-projector and
   periodic-chain no-pole arguments separately recover their former
   endpoint contradictions?

The finite branch review should also use the explicit parabolic-stability
bookkeeping in Section 2 when checking the genus-six and genus-five HN tables.

The source-level internal reconstruction is recorded in
[LOAD_BEARING_AUDIT.md](LOAD_BEARING_AUDIT.md), and the downstream source map
is in [PIPELINE_AUDIT.md](PIPELINE_AUDIT.md). These are navigation aids, not
independent referee reports.

## Finite checks

Run:

```sh
make verify-math
```

This replays the displayed genus-six and genus-five HN arithmetic,
reconstructs the $q=10$ local jet matrices, and checks the $q=9$ fibrewise
linear algebra. Passing scripts do not certify Hodge theory, parabolic
geometry, saturation, moduli descent, or mapping-class-group propagation.

## Most useful response

Corrections, missing hypotheses, or pointers to relevant literature would be
very helpful.
