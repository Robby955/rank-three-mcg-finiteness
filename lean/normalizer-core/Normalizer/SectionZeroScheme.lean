import Normalizer.SectionZeroIdeal
import Normalizer.IdealSheafGluing

/-! The actual zero subscheme of a map from a line sheaf to the structure
sheaf, constructed from a finite genuine line-chart cover. Overlap identities
are derived from the original map, not included as extra inputs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite Limits
universe u v
variable {X : Scheme.{u}} {L : X.Modules}

/-- Restrict an actual local line chart to a smaller open. -/
def schemeLineChartRestrict {U V : X.Opens} (h : V ≤ U)
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U) :
    (SheafOfModules.unit X.ringCatSheaf).over V ≅ L.over V :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app
    (SheafOfModules.unit X.ringCatSheaf)).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf (homOfLE h)).mapIso e ≪≫
    (SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app L

variable (φ : L ⟶ SheafOfModules.unit X.ringCatSheaf)

/-- The actual local image ideals of the same sheaf map agree on an overlap. -/
theorem schemeSectionImageIdealOn_overlap {U V : X.Opens}
    (eU : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (eV : (SheafOfModules.unit X.ringCatSheaf).over V ≅ L.over V) :
    (schemeSectionImageIdealOn φ eU).comap (pullback.fst U.ι V.ι) =
      (schemeSectionImageIdealOn φ eV).comap (pullback.snd U.ι V.ι) := by
  apply idealSheaf_overlap_of_inf
  let eW := schemeLineChartRestrict (inf_le_left : U ⊓ V ≤ U) eU
  rw [schemeSectionImageIdealOn_comap φ eW eU inf_le_left,
    schemeSectionImageIdealOn_comap φ eW eV inf_le_right]

variable {ι : Type v} (U : ι → X.Opens)
  (e : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅ L.over (U i))

/-- The global ideal from a genuine line-chart cover. The actual cover is
explicit; finiteness and quasi-compactness prove its exact chart restrictions. -/
def schemeSectionZeroIdeal [Finite ι] [∀ i, QuasiCompact (U i).ι] (_hU : ⨆ i, U i = ⊤) : X.IdealSheafData :=
  finiteIdealSheafGlue (fun i => (U i).toScheme) (fun i => (U i).ι)
    (fun i => schemeSectionImageIdealOn φ (e i))

/-- The constructed global ideal restricts to the actual section image ideal
on every chart; its overlap compatibility follows from the given map. -/
theorem schemeSectionZeroIdeal_comap [Finite ι] [∀ i, QuasiCompact (U i).ι]
    (hU : ⨆ i, U i = ⊤) (i : ι) :
    (schemeSectionZeroIdeal φ U e hU).comap (U i).ι =
      schemeSectionImageIdealOn φ (e i) :=
  finiteIdealSheafGlue_comap (fun i => (U i).toScheme) (fun i => (U i).ι)
    (fun i => schemeSectionImageIdealOn φ (e i))
    (fun i j => schemeSectionImageIdealOn_overlap φ (e i) (e j)) i

/-- The actual zero subscheme determined by the prescribed sheaf map and
its genuine line-chart cover. -/
def schemeSectionZeroScheme [Finite ι] [∀ i, QuasiCompact (U i).ι] (hU : ⨆ i, U i = ⊤) : Scheme :=
  (schemeSectionZeroIdeal φ U e hU).subscheme

/-- The inclusion of the actual global zero subscheme. -/
def schemeSectionZeroSchemeι [Finite ι] [∀ i, QuasiCompact (U i).ι] (hU : ⨆ i, U i = ⊤) :
    schemeSectionZeroScheme φ U e hU ⟶ X :=
  (schemeSectionZeroIdeal φ U e hU).subschemeι

/-- The global zero subscheme is a closed subscheme, with its full ideal
structure rather than only a reduced zero set. -/
theorem schemeSectionZeroScheme_isClosedImmersion [Finite ι] [∀ i, QuasiCompact (U i).ι]
    (hU : ⨆ i, U i = ⊤) :
    IsClosedImmersion (schemeSectionZeroSchemeι φ U e hU) := by
  dsimp [schemeSectionZeroSchemeι]
  infer_instance

/-- Base change of the global zero subscheme to a chart is the local zero
subscheme constructed directly from the original map. -/
def schemeSectionZeroSchemeChartIso [Finite ι] [∀ i, QuasiCompact (U i).ι]
    (hU : ⨆ i, U i = ⊤) (i : ι) :
    schemeSectionZeroSubschemeOn φ (e i) ≅
      pullback (U i).ι (schemeSectionZeroSchemeι φ U e hU) :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme
    (schemeSectionZeroIdeal_comap φ U e hU i).symm) ≪≫
      (schemeSectionZeroIdeal φ U e hU).comapIso (U i).ι

end Normalizer
