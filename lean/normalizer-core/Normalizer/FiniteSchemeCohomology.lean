import Normalizer.DiscreteSheafCohomology
import Normalizer.SectionZeroFinite

/-! Intrinsic higher cohomology of abelian sheaves on actual finite schemes.
This does not identify cohomology with that of a pushforward on an ambient scheme. -/

noncomputable section

namespace Normalizer
open CategoryTheory AlgebraicGeometry

universe u v
variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-- Actual finiteness over a field implies discreteness of the scheme's
underlying space, without removing its nilpotents. -/
theorem finiteScheme_discreteTopology (p : Y ⟶ Spec (.of k)) [IsFinite p] :
    DiscreteTopology Y := by
  have : IsLocallyArtinian Y := IsLocallyArtinian.of_locallyQuasiFinite p
  infer_instance

/-- Every actual abelian sheaf on a finite scheme over a field has vanishing
intrinsic positive-degree cohomology. -/
theorem finiteScheme_positiveCohomology_subsingleton
    (p : Y ⟶ Spec (.of k)) [IsFinite p]
    (F : TopCat.Sheaf AddCommGrpCat.{u} Y.toTopCat) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  have : DiscreteTopology Y.toTopCat := finiteScheme_discreteTopology p
  exact discreteSheaf_positiveCohomology_subsingleton F n

variable {X : Scheme.{u}} [IsIntegral X]
  (L : X.Modules) (s : Γ(L, ⊤))
  (hs : L.presheaf.germ ⊤ (genericPoint X) (by trivial) s ≠ 0)
  {ι : Type v} [Finite ι] (U : ι → X.Opens)
  [∀ i, QuasiCompact (U i).ι] (hU : iSup U = ⊤)
  (e : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅ L.over (U i))

include hs in
/-- Intrinsic positive-degree cohomology vanishes for every abelian sheaf on
the actual zero scheme of the specified section on a finite-type integral curve. -/
theorem schemeSectionZeroScheme_positiveCohomology_subsingleton
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim X ≤ 1)
    (F : TopCat.Sheaf AddCommGrpCat.{u}
      (schemeSectionZeroScheme (schemeSectionDualEvaluation L s)
        U (fun i ↦ schemeDualLineFrameIso L (e i)) hU).toTopCat) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  have := schemeSectionZeroScheme_isFinite L s hs U hU e p hdim
  exact finiteScheme_positiveCohomology_subsingleton
    (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
      U (fun i ↦ schemeDualLineFrameIso L (e i)) hU ≫ p) F n

include hs in
/-- In particular, intrinsic positive-degree cohomology vanishes on the actual
specified zero scheme on a proper integral curve. -/
theorem properCurve_sectionZeroScheme_positiveCohomology_subsingleton
    (p : X ⟶ Spec (.of k)) [IsProper p] (hdim : topologicalKrullDim X ≤ 1)
    (F : TopCat.Sheaf AddCommGrpCat.{u}
      (schemeSectionZeroScheme (schemeSectionDualEvaluation L s)
        U (fun i ↦ schemeDualLineFrameIso L (e i)) hU).toTopCat) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) :=
  schemeSectionZeroScheme_positiveCohomology_subsingleton L s hs U hU e p hdim F n

end Normalizer
