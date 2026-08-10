# Finite mathematics verifiers

Run both deterministic checks with:

```sh
make verify-math
```

- `verify_hn_branches.py` enumerates the finite genus-five HN offset list,
  no-high numerical branches, and the section-count upper bounds displayed in
  the manuscript.
- `verify_q9.py` uses exact rational arithmetic to check the $q=9$ orbit
  dimensions, Kirillov ranks, minimal-centralizer brackets, spectral
  polynomial and projector identities, lift independence, and divisor-degree
  cases. It also checks the semisimple and minimal quotient-normalizer tables
  used by the boundary-cocycle obstruction; it does not certify the global
  Cech identity or boundary-map injectivity.

These scripts certify only finite arithmetic and fibrewise linear algebra.
They do not prove the Hodge, parabolic, saturation, moduli, or propagation
arguments.
