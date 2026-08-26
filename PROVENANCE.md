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
two eliminations. This simplification was checked directly against the
generic orbit algebra and both bundle-theoretic applications. The theorem
statement and `CANDIDATE` status are unchanged.

The `0.1.3-candidate` expanded review release retains the
`0.1.2-candidate` release unchanged and expands the finite genus-six and genus-five
high-HN eliminations, prints the local jet matrices then used in the
`(S, q) = (2, 10)` branch, and adds a source-by-source propagation map and an
expanded review record. The finite checker reconstructs those historical
`q = 10` matrices from the parahoric bracket. No theorem statement or
mathematical hypothesis changed in that release.

The `0.1.4-candidate` review release retains `0.1.3-candidate` unchanged and
adds a compact load-bearing dependency roadmap, an explicit general-fibre
testing remark with local cross-references, and the parabolic-stability degree
and weight calculations at the formerly compressed uses. It also makes the
README notation robust in the GitHub mobile application. No theorem statement
or mathematical hypothesis changes.

The repaired `0.1.5-candidate` review version corrects the
`(S, q) = (2, 10)` proof. The earlier text incorrectly inferred that the
unique effective divisor of a degree-two line bundle had to equal the double
marked point. The replacement writes the bracket as a literal morphism of
extensions, uses the degree-two divisor sequence to bound its self-block by
rank one, and produces four independent quotient-normalizer sections. The
normalizer boundary-cocycle proposition then eliminates the branch. The local
jet matrices are no longer load-bearing, though their finite checker is
retained as a diagnostic. The theorem statement and `CANDIDATE` status remain
unchanged; earlier tagged PDFs remain fixed historical review copies.

The `0.1.6-candidate` review version sharpens attribution and presentation
without changing the theorem statement or its `CANDIDATE` status.  The
abstract and opening architecture now identify the organizing rank-three
refinement precisely: retain the Landesman--Litt rigidity, integrality, and
deformation framework, then treat the only adjoint constituents not already
covered by their strict-range theorem, of ranks eight, six, and five.  The
assistance disclosure now identifies the affected proof-search areas and the
author's responsibility without publishing prompts or private process logs.

The standalone `0.1.0-candidate` square-endpoint note extracts the
general-rank equality argument already recorded in the manuscript and expands
its terminal duality and finite-image splitting steps. It is a separate
unrefereed candidate artifact and does not alter the rank-three theorem.

The standalone `0.1.1-candidate` genus-four manuscript records a separate
rank-three extension for all puncture counts. Its proposed proof is conditional
on the five imported interfaces B1--B5 stated in the manuscript and has not
been independently refereed. It is therefore published here as a `CANDIDATE`,
not as an established theorem. It does not make a genus-three claim.

## Canonical artifacts

| Artifact | Pages | SHA-256 |
|---|---:|---|
| `manuscript/rank3_genus5_reader.tex` | -- | `2cc61289a02074c4bd42cdbe337ca5dca922bc83299ccf56ca485d6b65f2d6c3` |
| `output/pdf/rank3_genus5_reader-v0.1.4-candidate.pdf` | 35 | `9466b90ea13d51f7e3cb1203603c25170b4639ec2d41fc1b25224b7959191a25` |
| `output/pdf/rank3_genus5_reader-v0.1.5-candidate.pdf` | 35 | `a51aa0ca10c138f186f24d72c8df1c62b507f7dce30558114c7ca71baf492faf` |
| `output/pdf/rank3_genus5_reader-v0.1.6-candidate.pdf` | 35 | `2141f8c9c5a40577a39c338a29b964a67470efd82726e11e29a5f8179021c090` |
| `manuscript/rank3_genus4_extension.tex` | -- | `e6719763c5fa10f0912d87f19f11ea9f440d03d60822112a4682e0084eee9736` |
| `output/pdf/rank3_genus4_extension.pdf` | 30 | `c9280e8f7e26c7c859101b3568199c5c1d0c872358d21153fa1520faa99788bc` |
| `manuscript/general_rank_square_endpoint.tex` | -- | `868391dd70d39b7d3a78194cf46df4ef3c522bfb7102ca6cb7ffcaa428c84f04` |
| `output/pdf/general_rank_square_endpoint.pdf` | 6 | `3ad2764bbc091e462b7d895fdc6be2942bc2258ac63f970f383e51eaed3b2b20` |

The current sources and PDFs are recorded in `CHECKSUMS.sha256` and enforced
by the three artifact verifiers. The `0.1.4-candidate` value identifies the fixed
historical release artifact.

## Scope

This package is designed to let a reader audit the rank-three genus-at-least-five
argument, the separate conditional genus-four extension, and the standalone
general-rank square endpoint without navigating genus-three working ledgers or
alternate approaches.
