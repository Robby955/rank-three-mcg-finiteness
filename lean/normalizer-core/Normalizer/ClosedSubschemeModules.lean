import Normalizer.SheafStalkMap
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! The actual structure-module quotient map for a closed subscheme,
including affine surjectivity and surjectivity on every ambient stalk. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The structure sheaf of the actual closed subscheme, pushed forward
as a module sheaf on the ambient scheme. -/
def closedSubschemeStructureSheaf : X.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj
    (SheafOfModules.unit I.subscheme.ringCatSheaf)

/-- The actual quotient map from the ambient structure module to the
pushforward of the closed subscheme's structure module. -/
def closedSubschemeStructureMap :
    SheafOfModules.unit X.ringCatSheaf ⟶ closedSubschemeStructureSheaf I :=
  SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom

/-- On sections, the module quotient map is the actual closed-immersion
map on regular functions. -/
theorem closedSubschemeStructureMap_app (V : X.Opens) (r : Γ(X, V)) :
    (closedSubschemeStructureMap I).val.app (op V) r = I.subschemeι.app V r := rfl

/-- On an actual affine open, the structure-module quotient is surjective. -/
theorem closedSubschemeStructureMap_affine_surjective (V : X.affineOpens) :
    Function.Surjective ((closedSubschemeStructureMap I).val.app (op V.1)) :=
  I.subschemeι_app_surjective V

/-- On an actual affine open, vanishing under the structure-module quotient
is exactly membership in the defining ideal. -/
theorem closedSubschemeStructureMap_affine_eq_zero_iff
    (V : X.affineOpens) (r : Γ(X, V.1)) :
    (closedSubschemeStructureMap I).val.app (op V.1) r = 0 ↔ r ∈ I.ideal V := by
  change (I.subschemeι.app V.1).hom r = 0 ↔ _
  rw [← RingHom.mem_ker, I.ker_subschemeι_app V]

/-- The actual closed-subscheme quotient is surjective on every ambient
module stalk, including at points outside the closed subscheme. -/
theorem closedSubschemeStructureMap_stalk_surjective (x : X) :
    Function.Surjective (schemeModuleStalkMap (closedSubschemeStructureMap I) x) := by
  intro m
  obtain ⟨W, hxW, a, rfl⟩ := (closedSubschemeStructureSheaf I).presheaf.exists_germ_eq m
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hxW
  obtain ⟨r, hr⟩ := closedSubschemeStructureMap_affine_surjective I ⟨V, hV⟩
    ((closedSubschemeStructureSheaf I).presheaf.map (homOfLE hVW).op a)
  refine ⟨(Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).germ V x hxV r, ?_⟩
  rw [schemeModuleStalkMap_germ]
  change (closedSubschemeStructureSheaf I).presheaf.germ V x hxV
    ((closedSubschemeStructureMap I).val.app (op V) r) = _
  rw [hr]
  exact (closedSubschemeStructureSheaf I).presheaf.germ_res_apply
    (homOfLE hVW) x hxV a

end Normalizer
