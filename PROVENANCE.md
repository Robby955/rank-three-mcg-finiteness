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

The prepared `0.1.5-candidate` review version retains the theorem, hypotheses,
and proof of `0.1.4-candidate` unchanged and streamlines the public review
package. The earlier versioned PDF remains fixed in its release. No
mathematical claim or dependency changes.

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
| `manuscript/rank3_genus5_reader.tex` | -- | `73c86d7a158fb5d89cefd0adf0463fa4dd05bc34f77ad2670baa1e4ec1df8ace` |
| `output/pdf/rank3_genus5_reader-v0.1.4-candidate.pdf` | 35 | `9466b90ea13d51f7e3cb1203603c25170b4639ec2d41fc1b25224b7959191a25` |
| `output/pdf/rank3_genus5_reader-v0.1.5-candidate.pdf` | 35 | `ae30533bae960e1bdb6ec934f73006b86d117360c2c02a320a3d09badd6336b0` |
| `manuscript/rank3_genus4_extension.tex` | -- | `2c0ddb951b07a97db92a87145077f5e2846a18debd4f897fa786942e59117388` |
| `output/pdf/rank3_genus4_extension.pdf` | 30 | `c1362e6d4130b8c3e264a138f7787aebc9735441d0747bae20f2c69637a92a01` |
| `manuscript/general_rank_square_endpoint.tex` | -- | `9be5e83a5c69dd0882f8c684e3e549cb5b235d48702d7fc06d5fbb3719622a2f` |
| `output/pdf/general_rank_square_endpoint.pdf` | 6 | `e5ec46ed9de38335aae8189f76a38e882a6a422627e82d059d1edf0aa40a6abf` |

The current sources and PDFs are recorded in `CHECKSUMS.sha256` and enforced
by the three artifact verifiers. The `0.1.4-candidate` value identifies the fixed
historical release artifact.

## Scope

This package is designed to let a reader audit the rank-three genus-at-least-five
argument, the separate conditional genus-four extension, and the standalone
general-rank square endpoint without navigating genus-three working ledgers or
alternate approaches.
