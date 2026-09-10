import Normalizer.SectionZeroIdeal
import Mathlib.CategoryTheory.Limits.Shapes.Images

/-! A monic line-sheaf map identifies its source with its actual categorical
image. Its image inclusion gives the same section ideals and local frames. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite Limits
universe u
variable {X : Scheme.{u}} {L : X.Modules}
  (φ : L ⟶ SheafOfModules.unit X.ringCatSheaf)

/-- The actual categorical image module sheaf. -/
def schemeSectionImageSheaf : X.Modules := image φ

/-- The actual image inclusion into the structure sheaf. -/
def schemeSectionImageSheafι :
    schemeSectionImageSheaf φ ⟶ SheafOfModules.unit X.ringCatSheaf := image.ι φ

/-- A regular map identifies its line sheaf with its categorical image. -/
def schemeSectionImageSheafIso [Mono φ] : L ≅ schemeSectionImageSheaf φ :=
  (imageMonoIsoSource φ).symm

/-- The comparison is the canonical factorization map through the image. -/
theorem schemeSectionImageSheafIso_hom [Mono φ] :
    (schemeSectionImageSheafIso φ).hom = factorThruImage φ := by
  apply (cancel_mono (image.ι φ)).mp
  simp [schemeSectionImageSheafIso]

/-- Composing the canonical comparison with the image inclusion recovers
exactly the original map. -/
theorem schemeSectionImageSheafIso_hom_ι [Mono φ] :
    (schemeSectionImageSheafIso φ).hom ≫ schemeSectionImageSheafι φ = φ :=
  imageMonoIsoSource_inv_ι φ

/-- The inclusion composed with the inverse comparison gives the same map. -/
theorem schemeSectionImageSheafIso_inv_comp [Mono φ] :
    (schemeSectionImageSheafIso φ).inv ≫ φ = schemeSectionImageSheafι φ :=
  imageMonoIsoSource_hom_self φ

/-- The image sheaf inclusion has exactly the original sectionwise image
ideal. Surjectivity here follows from the actual isomorphism on sections. -/
theorem schemeSectionImageSheaf_imageIdeal [Mono φ] (V : X.Opens) :
    schemeSectionImageIdeal (schemeSectionImageSheafι φ) V =
      schemeSectionImageIdeal φ V := by
  ext r
  rw [mem_schemeSectionImageIdeal, mem_schemeSectionImageIdeal]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨(schemeSectionImageSheafIso φ).inv.val.app (op V) s, ?_⟩
    have he := congrArg (fun f : schemeSectionImageSheaf φ ⟶
      SheafOfModules.unit X.ringCatSheaf => f.val.app (op V) s)
      (schemeSectionImageSheafIso_inv_comp φ)
    exact he.trans hs
  · rintro ⟨s, hs⟩
    refine ⟨(schemeSectionImageSheafIso φ).hom.val.app (op V) s, ?_⟩
    have he := congrArg (fun f : L ⟶ SheafOfModules.unit X.ringCatSheaf =>
      f.val.app (op V) s) (schemeSectionImageSheafIso_hom_ι φ)
    exact he.trans hs

/-- Every genuine local line frame transports to the actual image sheaf. -/
def schemeSectionImageSheafFrame [Mono φ] {U : X.Opens}
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U) :
    (SheafOfModules.unit X.ringCatSheaf).over U ≅
      (schemeSectionImageSheaf φ).over U :=
  e ≪≫ (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso
    (schemeSectionImageSheafIso φ)

/-- The transported image frame has exactly the same local equation. -/
theorem schemeSectionImageSheafFrame_equation [Mono φ] {U : X.Opens}
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (V : X.Opens) (h : V ≤ U) :
    schemeSectionImageEquation (schemeSectionImageSheafι φ)
      (schemeSectionImageSheafFrame φ e) V h = schemeSectionImageEquation φ e V h := by
  exact congrArg (fun f : L ⟶ SheafOfModules.unit X.ringCatSheaf =>
    f.val.app (op V) (moduleLineFrameAt L e V h 1))
      (schemeSectionImageSheafIso_hom_ι φ)

/-- The actual ideal-sheaf data are unchanged when formed from the image
inclusion and its transported line frame. -/
theorem schemeSectionImageSheaf_idealOn [Mono φ] {U : X.Opens}
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U) :
    schemeSectionImageIdealOn (schemeSectionImageSheafι φ)
      (schemeSectionImageSheafFrame φ e) = schemeSectionImageIdealOn φ e := by
  apply Scheme.IdealSheafData.ext
  funext V
  exact schemeSectionImageSheaf_imageIdeal φ _

end Normalizer
