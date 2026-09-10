import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! Zero-dimensional finite-type schemes over a field are finite over that field.
Affineness and finite residue extensions are consequences of the proof route,
not hypotheses. Nilpotents in the source are allowed. -/

noncomputable section

namespace Normalizer
open CategoryTheory AlgebraicGeometry

universe u
variable {Y : Scheme.{u}}

/-- A quasi-compact locally Noetherian scheme of dimension at most zero
is an actual Artinian scheme. The empty scheme is included. -/
theorem scheme_isArtinian_of_dim_le_zero [IsLocallyNoetherian Y] [CompactSpace Y]
    (hdim : topologicalKrullDim Y ≤ 0) : IsArtinianScheme Y :=
  { toIsLocallyArtinian := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim }

/-- The underlying point set of such a scheme is finite; the conclusion
does not discard its possibly nonreduced scheme structure. -/
theorem scheme_finite_points_of_dim_le_zero [IsLocallyNoetherian Y] [CompactSpace Y]
    (hdim : topologicalKrullDim Y ≤ 0) : Finite Y := by
  have := scheme_isArtinian_of_dim_le_zero hdim
  infer_instance

variable {k : Type u} [Field k] (p : Y ⟶ Spec (.of k))

/-- A quasi-compact finite-type morphism to a field with zero-dimensional
source is finite as an actual scheme morphism. Properness is unnecessary. -/
theorem scheme_isFinite_of_dim_le_zero [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim Y ≤ 0) : IsFinite p := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : Finite Y := scheme_finite_points_of_dim_le_zero hdim
  have : LocallyQuasiFinite p :=
    LocallyQuasiFinite.of_finite_preimage_singleton p (fun _ ↦ Set.toFinite _)
  exact IsFinite.of_locallyQuasiFinite p

/-- Compactness of the source suffices in place of an explicit
quasi-compactness hypothesis on its finite-type structure morphism. -/
theorem scheme_isFinite_of_compact_dim_le_zero [LocallyOfFiniteType p] [CompactSpace Y]
    (hdim : topologicalKrullDim Y ≤ 0) : IsFinite p :=
  scheme_isFinite_of_dim_le_zero p hdim

/-- A proper scheme over a field whose dimension is at most zero is
finite over that field, including its full nilpotent structure. -/
theorem scheme_isFinite_of_proper_dim_le_zero [IsProper p]
    (hdim : topologicalKrullDim Y ≤ 0) : IsFinite p :=
  scheme_isFinite_of_dim_le_zero p hdim

end Normalizer
