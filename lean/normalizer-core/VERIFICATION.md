# Verification record

This cumulative update was prepared against public main
`307a99b7ace7a51380c1377fba50504352af0999` on 11 September 2026.
Its proof sources match the verified local mathematical checkpoint
`0a7c55c234d16f1f1bca69b5b5bc1bd2acde547f`; all 183 proof/pin hashes
were checked before transfer. Compared with the public baseline, it adds
53 proof modules, 284 named theorems, 394 audited declarations and 30
examples. No dependency pin or manuscript changed. The final public payload
was also built and audited locally.

| Check | Result |
|---|---|
| `python3 scripts/verify.py` | PASS: full build, 875 named theorems, 1230 audited declarations, 84 compiled examples. |
| Complete `#print axioms` audit | Only `propext`, `Classical.choice`, and `Quot.sound`. |
| Proof placeholders or custom axioms | None in the proved core. |
| `python3 scripts/check_correspondence.py` | PASS: 1230 accurate declaration links and package documentation links. |
| Distribution manifest | 194 source/documentation/pin files, excluding itself, receipts, dependencies and build outputs. |

The full library, examples and regenerated audit passed 4157 build jobs.
The worktree shares pinned dependencies and has its own copy of the prior
verified project cache. This is an incremental full-target build, not an
independent clean dependency rebuild. Complete actual #print axioms output
is generated in receipts/axioms.log. Exact statements are in the source
and all audited declaration links are checked in CORRESPONDENCE.md.

There are 22,485 core Lean source lines including comments, blanks and
examples, excluding the generated audit and dependencies. The machine
receipt verification.json records 183 proof/pin hashes and exact versions.

## Checked mathematical scope

CurveMapExistence constructs a finite map X -> P1_k from the hypotheses:
k a field, X integral, p:X -> Spec k proper, dimension at most one, and
integrally closed actual stalks. A nontrivial affine neighborhood has a
section with a nonempty proper invertibility locus; its [1:s] map is
nonconstant. A proved extension retains its restriction on the whole open,
so the global map is nonconstant. The existing finiteness criterion then
applies. No rational function or nonconstancy certificate is a premise.
The zero-dimensional case is also proved without reducedness or integrality.
Every positive-degree abelian-sheaf cohomology group vanishes in that case.

The proper smooth integral curve result derives actual stalk normality
from smooth regularity and the dimension bound. Both normal and smooth
branches give actual H1(X,O_X) finiteness with the original field action.
Neither assumes H1 finiteness, an abstract quotient, or a supplied finite map.

CurveMapSingular uses the extension theorem only outside a specified affine
open; its points may be singular. It constructs the required open when
there is at most one nonnormal point, giving an actual finite map and H1
finiteness. The general statement with a supplied affine open states that
input explicitly and does not construct it for arbitrary singular curves.

The accumulated examples include the doubled point over Q (retaining its nilpotent),
the smooth-curve H1 conclusion with the actual field action, and the
one-exceptional-point finite-map conclusion without normality at that point.
Existing exact matrix and geometric examples remain included in the build.

## Remaining geometry

For a proper integral curve with at least two points, construct a nontrivial
affine open containing all nonnormal points. The new extension and finite-map
theorems then close H1 finiteness without requiring global normality.
This affine-neighborhood result and the alternative general normalization,
finite-support defect and cohomology transfer remain unformalized.
The original general target has not been narrowed. Dimension zero is closed.

Higher curve vanishing, Euler/degree comparison, determinant nowhere
vanishing, the complete h0(E/M)<=4 bound and representation-theorem
obligations remain. The specified normal, smooth and one-exceptional-point
branches are FORMALIZED. The unrestricted request and campaign are PARTIAL.

## Reproduction and public status

```sh
python3 scripts/verify.py
python3 scripts/check_correspondence.py
shasum -a 256 -c SHA256SUMS
```

Lean remains pinned to leanprover/lean4:v4.34.0-rc2, commit
6a10ac8c22beadecabdbb0919c2b50214762f91d; mathlib remains pinned to
7974e751bece493b6ff508039423ca9fa2452fa8. Generated verification receipts record the exact source hashes, toolchain
version and complete axiom output.
Hosted verification of this update is pending. The existing workflow checks
hashes before building, regenerates the full declaration audit, checks
correspondence and immutable pins, and uploads the generated evidence.
The workflow must pass for the submitted commit before claiming hosted
verification. No pre-existing receipt is required to run the checks.
