import Normalizer.DeterminantGenericNonzero
import Normalizer.SectionZeroDivisor
import Normalizer.SectionEvaluationMono
import Normalizer.SectionZeroScheme
import Normalizer.SectionIdealBundle

/-! The actual zero ideal of the specified determinant section, with
injectivity and regular local equations derived from generic independence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u v
variable {X : Scheme.{u}} (H : X.Modules) (n : ℕ) (s : Fin n → Γ(H, ⊤))
  {I : Type u} [Fintype I] (j : I ≃ Fin n)

include j in
/-- Actual rank-n charts and independence of the specified generic germs
make evaluation against their actual determinant section monic. -/
theorem schemeDeterminantDualEvaluation_mono [IsIntegral X]
    (hs : LinearIndependent X.functionField
      (fun i ↦ H.presheaf.germ ⊤ (genericPoint X) (by trivial) (s i)))
    (hcharts : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((schemeTrivialBundle X I).over U ≅ H.over U)) :
    Mono (schemeSectionDualEvaluation (schemeExteriorSheaf H n)
      (schemeExteriorGlobalSection H n s)) := by
  apply schemeSectionDualEvaluation_mono _ _
    (schemeExteriorGlobalSection_generic_ne_zero H n s hs)
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hcharts x
  exact ⟨U, hx, ⟨bundleTopExteriorSheafIsoOver j e⟩⟩

/-- The equation of the specified determinant in the chart induced by an
actual rank-n frame is regular in every actual local ring on that chart. -/
theorem schemeDeterminantLocalEquation_germ_isRegular [IsIntegral X]
    (hs : LinearIndependent X.functionField
      (fun i ↦ H.presheaf.germ ⊤ (genericPoint X) (by trivial) (s i)))
    {U : X.Opens} (e : (schemeTrivialBundle X I).over U ≅ H.over U)
    (V : X.Opens) (h : V ≤ U) (x : X) (hx : x ∈ V) :
    IsRegular (X.presheaf.germ V x hx
      (sectionLocalEquation (schemeExteriorSheaf H n) (schemeExteriorGlobalSection H n s)
        (bundleTopExteriorSheafIsoOver j e) V h)) :=
  sectionLocalEquation_germ_isRegular _ _ _
    (schemeExteriorGlobalSection_generic_ne_zero H n s hs) V h x hx

/-- The inverse ideal module of the actual specified determinant is the
actual exterior line, using only genuine rank-n charts and generic independence. -/
def schemeDeterminantInverseIdealIso [IsIntegral X]
    (hs : LinearIndependent X.functionField
      (fun i ↦ H.presheaf.germ ⊤ (genericPoint X) (by trivial) (s i)))
    {A : Type u} (U : A → X.Opens) (hU : iSup U = ⊤)
    (e : ∀ a, (schemeTrivialBundle X I).over (U a) ≅ H.over (U a)) :
    schemeSectionInverseIdealBundle (schemeExteriorSheaf H n)
      (schemeExteriorGlobalSection H n s) ≅ schemeExteriorSheaf H n :=
  schemeSectionInverseIdealIso _ _ (schemeExteriorGlobalSection_generic_ne_zero H n s hs)
    U hU (fun a ↦ bundleTopExteriorSheafIsoOver j (e a))

/-- This isomorphism carries the canonical inclusion section to the
specified determinant section built from the original section family. -/
theorem schemeDeterminantInverseIdealIso_section [IsIntegral X]
    (hs : LinearIndependent X.functionField
      (fun i ↦ H.presheaf.germ ⊤ (genericPoint X) (by trivial) (s i)))
    {A : Type u} (U : A → X.Opens) (hU : iSup U = ⊤)
    (e : ∀ a, (schemeTrivialBundle X I).over (U a) ≅ H.over (U a)) :
    (schemeDeterminantInverseIdealIso H n s j hs U hU e).hom.val.app (op ⊤)
      (schemeSectionInverseIdealSection (schemeExteriorSheaf H n)
        (schemeExteriorGlobalSection H n s)) = schemeExteriorGlobalSection H n s :=
  schemeSectionInverseIdealIso_section _ _
    (schemeExteriorGlobalSection_generic_ne_zero H n s hs)
    U hU (fun a ↦ bundleTopExteriorSheafIsoOver j (e a))

variable {ι : Type v} [Finite ι] (U : ι → X.Opens)
  [∀ i, QuasiCompact (U i).ι]
  (e : ∀ i, (schemeTrivialBundle X I).over (U i) ≅ H.over (U i))
  (hU : ⨆ i, U i = ⊤)

/-- The actual global zero ideal of the specified exterior section, built
from the genuine rank-n cover and its induced dual determinant charts. -/
def schemeDeterminantZeroIdeal : X.IdealSheafData :=
  schemeSectionZeroIdeal
    (schemeSectionDualEvaluation (schemeExteriorSheaf H n) (schemeExteriorGlobalSection H n s))
    U (fun i ↦ schemeDualLineFrameIso (schemeExteriorSheaf H n)
      (bundleTopExteriorSheafIsoOver j (e i))) hU

/-- The global determinant zero ideal restricts exactly to the actual
local image ideal; compatibility is derived from the same evaluation map. -/
theorem schemeDeterminantZeroIdeal_comap (i : ι) :
    (schemeDeterminantZeroIdeal H n s j U e hU).comap (U i).ι =
      schemeSectionImageIdealOn
        (schemeSectionDualEvaluation (schemeExteriorSheaf H n) (schemeExteriorGlobalSection H n s))
        (schemeDualLineFrameIso (schemeExteriorSheaf H n)
          (bundleTopExteriorSheafIsoOver j (e i))) :=
  schemeSectionZeroIdeal_comap _ _ _ _ i

/-- Each affine open of a chart has the actual specified determinant
equation as generator of the restriction of the global zero ideal. -/
theorem schemeDeterminantZeroIdeal_chart_ideal (i : ι) (V : (U i).toScheme.affineOpens) :
    ((schemeDeterminantZeroIdeal H n s j U e hU).comap (U i).ι).ideal V =
      Ideal.span {sectionLocalEquation (schemeExteriorSheaf H n)
        (schemeExteriorGlobalSection H n s)
        (bundleTopExteriorSheafIsoOver j (e i))
        ((U i).ι ''ᵁ V.1) ((U i).ι_image_le V.1)} := by
  rw [schemeDeterminantZeroIdeal_comap, schemeSectionImageIdealOn_ideal,
    schemeSectionDualEvaluation_imageIdeal]

/-- Generic independence gives a regular generator for the actual local
ring image of the global determinant zero ideal on every affine chart. -/
theorem schemeDeterminantZeroIdeal_chart_germ_regular [IsIntegral X]
    (hs : LinearIndependent X.functionField
      (fun i ↦ H.presheaf.germ ⊤ (genericPoint X) (by trivial) (s i)))
    (i : ι) (V : (U i).toScheme.affineOpens) (x : X) (hx : x ∈ (U i).ι ''ᵁ V.1) :
    ∃ r : X.presheaf.stalk x, IsRegular r ∧
      (((schemeDeterminantZeroIdeal H n s j U e hU).comap (U i).ι).ideal V).map
        (X.presheaf.germ ((U i).ι ''ᵁ V.1) x hx).hom = Ideal.span {r} := by
  rw [schemeDeterminantZeroIdeal_comap, schemeSectionImageIdealOn_ideal]
  exact schemeSectionDualEvaluation_germ_imageIdeal_regular _ _
    (bundleTopExteriorSheafIsoOver j (e i))
    (schemeExteriorGlobalSection_generic_ne_zero H n s hs) _ ((U i).ι_image_le V.1) x hx

end Normalizer
