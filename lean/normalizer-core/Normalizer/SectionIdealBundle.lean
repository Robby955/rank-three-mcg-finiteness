import Normalizer.LineBidual
import Normalizer.DualTransport
import Normalizer.SectionImageSheaf
import Normalizer.SectionEvaluationMono
import Normalizer.SectionZeroScheme
import Normalizer.FiniteBundlePresentation

/-! The inverse of the actual image ideal module of a specified section.
This construction recovers the original line module by canonical biduality. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite Limits TopologicalSpace
universe u

variable {X : Scheme.{u}} (L : X.Modules) (s : Γ(L, ⊤))

/-- The inverse ideal module is the actual dual of the categorical image
of evaluation at the specified section. -/
def schemeSectionInverseIdealBundle : X.Modules :=
  schemeDualSheaf (schemeSectionImageSheaf (schemeSectionDualEvaluation L s))

/-- The canonical section of the inverse ideal module is its actual ideal
inclusion, viewed as a local functional on that ideal. -/
def schemeSectionInverseIdealSection : Γ(schemeSectionInverseIdealBundle L s, ⊤) :=
  schemeDualSectionOfHom (schemeSectionImageSheafι (schemeSectionDualEvaluation L s))

/-- Genuine line charts and monic evaluation construct actual line charts
of the inverse ideal module. -/
def schemeSectionInverseIdealFrame [Mono (schemeSectionDualEvaluation L s)]
    {U : X.Opens} (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U) :
    (SheafOfModules.unit X.ringCatSheaf).over U ≅
      (schemeSectionInverseIdealBundle L s).over U :=
  schemeDualLineFrameIso _ (schemeSectionImageSheafFrame
    (schemeSectionDualEvaluation L s) (schemeDualLineFrameIso L e))

private theorem sectionLineChartsAt {ι : Type u} (U : ι → X.Opens)
    (hU : iSup U = ⊤)
    (e : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅ L.over (U i)) :
    ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over V ≅ L.over V) := by
  intro x
  have hx : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨U i, hi, ⟨e i⟩⟩

variable [IsIntegral X]
  (hs : L.presheaf.germ ⊤ (genericPoint X) (by trivial) s ≠ 0)
  {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
  (e : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅ L.over (U i))

/-- The inverse of the actual section image ideal is canonically the
original line module. Monicity is proved from generic nonzeroness. -/
def schemeSectionInverseIdealIso : schemeSectionInverseIdealBundle L s ≅ L := by
  have := schemeSectionDualEvaluation_mono L s hs (sectionLineChartsAt L U hU e)
  exact schemeDualIso (schemeSectionImageSheafIso (schemeSectionDualEvaluation L s)) ≪≫
    (schemeLineBidualIso L U hU e).symm

/-- The actual canonical inclusion section of the inverse image ideal
maps to the specified original section, not just to some nonzero section. -/
theorem schemeSectionInverseIdealIso_section :
    (schemeSectionInverseIdealIso L s hs U hU e).hom.val.app (op ⊤)
      (schemeSectionInverseIdealSection L s) = s := by
  have := schemeSectionDualEvaluation_mono L s hs (sectionLineChartsAt L U hU e)
  let a := schemeDualIso (schemeSectionImageSheafIso (schemeSectionDualEvaluation L s))
  let b := schemeLineBidualIso L U hU e
  have he : a.hom.val.app (op ⊤) (schemeSectionInverseIdealSection L s) =
      b.hom.val.app (op ⊤) s := by
    change (schemeDualMap (schemeSectionImageSheafIso (schemeSectionDualEvaluation L s)).hom).val.app
      (op ⊤) (schemeDualSectionOfHom (schemeSectionImageSheafι
        (schemeSectionDualEvaluation L s))) = (schemeBidualMap L).val.app (op ⊤) s
    rw [schemeDualMap_sectionOfHom, schemeSectionImageSheafIso_hom_ι,
      schemeBidualMap_globalSection]
  change b.inv.val.app (op ⊤)
    (a.hom.val.app (op ⊤) (schemeSectionInverseIdealSection L s)) = s
  rw [he]
  exact ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso b).toLinearEquiv.symm_apply_apply s

/-- The actual image ideal module has the actual global zero ideal as its
chart ideal data. This exposes the sheaf/subscheme linkage explicitly. -/
theorem schemeSectionImageSheaf_zeroIdeal_comap
    [Finite ι] [∀ i, QuasiCompact (U i).ι] (i : ι) :
    let _ := schemeSectionDualEvaluation_mono L s hs (sectionLineChartsAt L U hU e)
    (schemeSectionZeroIdeal (schemeSectionDualEvaluation L s) U
      (fun j ↦ schemeDualLineFrameIso L (e j)) hU).comap (U i).ι =
        schemeSectionImageIdealOn (schemeSectionImageSheafι (schemeSectionDualEvaluation L s))
          (schemeSectionImageSheafFrame (schemeSectionDualEvaluation L s)
            (schemeDualLineFrameIso L (e i))) := by
  dsimp only
  rw [schemeSectionZeroIdeal_comap, schemeSectionImageSheaf_idealOn]

private def inverseIdealFreeChart (i : ι) :
    (schemeSectionInverseIdealBundle L s).over (U i) ≅
      SheafOfModules.free (R := X.ringCatSheaf.over (U i)) PUnit.{u + 1} := by
  have := schemeSectionDualEvaluation_mono L s hs (sectionLineChartsAt L U hU e)
  exact (schemeSectionInverseIdealFrame L s (e i)).symm ≪≫
    (coproductUniqueIso
      (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit (X.ringCatSheaf.over (U i)))).symm

include hs hU e in
/-- The constructed inverse ideal module is locally free in mathlib's
actual sheaf sense, as witnessed by the constructed rank-one charts. -/
theorem schemeSectionInverseIdealBundle_isLocallyFree :
    (schemeSectionInverseIdealBundle L s).IsLocallyFree := by
  let J : ι → Type u := fun _ ↦ PUnit.{u + 1}
  let q := freeCoverLocalGeneratorsData (schemeSectionInverseIdealBundle L s)
    U hU J (inverseIdealFreeChart L s hs U hU e)
  let : q.IsLocallyFreeData := freeCoverLocalGeneratorsData_isLocallyFree
    (schemeSectionInverseIdealBundle L s) U hU J (inverseIdealFreeChart L s hs U hU e)
  exact q.isLocallyFree

include hs hU e in
/-- The same constructed rank-one charts prove finite presentation of
the actual inverse ideal module. -/
theorem schemeSectionInverseIdealBundle_isFinitePresentation :
    (schemeSectionInverseIdealBundle L s).IsFinitePresentation :=
  sheaf_isFinitePresentation_of_finiteFree_cover (schemeSectionInverseIdealBundle L s)
    U hU (fun _ ↦ PUnit.{u + 1}) (inverseIdealFreeChart L s hs U hU e)

end Normalizer
