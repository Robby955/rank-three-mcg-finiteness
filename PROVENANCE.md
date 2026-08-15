# Provenance and artifact identity

This repository is the public review package for the candidate manuscript.

## Artifact history

The initial TeX source and PDF were copied byte-for-byte from the canonical
source checkpoint. On 9 August 2026, the public review copy received one
presentation correction in the universal-extension proof: a display that
incorrectly printed `H^1(O_C)=0` was rewritten to say that the composite into
`H^1(O_C)` is zero. The following sentence already proves that this map is an
isomorphism. No theorem statement or mathematical hypothesis changed.

The `0.1.2-candidate` review release records a subsequent line-by-line review
of the zero-weight `q = 9` branch. It replaces the invalid bare use of a section on
a pointed universal curve with an explicit residue and point-pushing descent
to a finite cover of the unpointed moduli space. It also makes the Pfaffian
square, semisimple sheaf equality, minimal-centralizer saturation, canonical
global determinant character, completed-kernel lattice, and scalar Artin
twist explicit. The headline theorem and `CANDIDATE` status are unchanged.

The same review snapshot now also records a shorter main elimination. A
normalizer boundary-cocycle identity directly excludes the zero-weight
`q = 9` branch and the final high-HN branch once their universal-extension
kernels have generic rank at least three. The Pfaffian/spectral-projector and
canonical-Deligne determinant arguments remain in the manuscript as separate
reconstructions, but are no longer load-bearing for those
two eliminations. This simplification was checked internally against the
generic orbit algebra and both bundle-theoretic applications. The theorem
statement and `CANDIDATE` status are unchanged.

The `0.1.3-candidate` expanded review release retains the
`0.1.2-candidate` release unchanged and expands the finite genus-six and genus-five
high-HN eliminations, prints the local jet matrices used in the
`(S, q) = (2, 10)` branch, and adds a source-by-source propagation map and an
expanded review record. The finite checker now reconstructs the
displayed `q = 10` matrices from the parahoric bracket. No theorem statement or
mathematical hypothesis changes.

The `0.1.4-candidate` review release retains `0.1.3-candidate` unchanged and
adds a compact load-bearing dependency roadmap, an explicit general-fibre
testing remark with local cross-references, and the parabolic-stability degree
and weight calculations at the formerly compressed uses. It also makes the
README notation robust in the GitHub mobile application. No theorem statement
or mathematical hypothesis changes.

The `0.1.5-candidate` review release retains the theorem, hypotheses, and proof
of `0.1.4-candidate` unchanged and streamlines the public review package. The
earlier versioned PDF remains fixed in its release. No mathematical claim or
dependency changes.

## Canonical artifacts

| Artifact | Pages | SHA-256 |
|---|---:|---|
| `manuscript/rank3_genus5_reader.tex` | -- | `26e3d2d8162e36c8e45fb5aac8c6e7ee8fd6f3e35d3bd828f1022a6768bdffb7` |
| `output/pdf/rank3_genus5_reader-v0.1.4-candidate.pdf` | 35 | `9466b90ea13d51f7e3cb1203603c25170b4639ec2d41fc1b25224b7959191a25` |
| `output/pdf/rank3_genus5_reader-v0.1.5-candidate.pdf` | 35 | `0e26d8ba2af9f03d28fb1a63aba2cc7d2e80eeb777b379abfbff13687f1ec30b` |

The current source and `0.1.5-candidate` PDF values are recorded in
`CHECKSUMS.sha256` and enforced by `verification/verify_release.py`. The
`0.1.4-candidate` value identifies the fixed historical release artifact.

## Scope

This package is designed to let a reader audit the rank-three argument without
navigating exploratory notes, alternate approaches, or general-rank work.
