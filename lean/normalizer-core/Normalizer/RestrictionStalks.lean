import Normalizer.IntegralSheafTorsion
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! Restriction to open subschemes preserves actual free module stalks. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
attribute [local instance] RingHomInvPair.of_ringEquiv
open CategoryTheory AlgebraicGeometry Opposite

universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
  (E : X.Modules) (y : Y)

/-- The actual local rings before and after open restriction are isomorphic. -/
def restrictionLocalRingEquiv : Y.presheaf.stalk y ≃+* X.presheaf.stalk (f y) :=
  (asIso (f.stalkMap y)).symm.commRingCatIsoToRingEquiv

/-- The inverse local-ring identification takes a germ on the open subscheme
to the germ obtained by the actual section-ring isomorphism. -/
theorem restrictionLocalRingEquiv_germ (V : Y.Opens) (hy : y ∈ V) (a : Γ(Y, V)) :
    restrictionLocalRingEquiv f y (Y.presheaf.germ V y hy a) =
      X.presheaf.germ (f ''ᵁ V) (f y) (by exact ⟨y, hy, rfl⟩) ((f.appIso V).inv a) := by
  apply (ConcreteCategory.bijective_of_isIso (f.stalkMap y)).injective
  change (asIso (f.stalkMap y)).hom ((asIso (f.stalkMap y)).inv _) = _
  rw [Iso.inv_hom_id_apply]
  rw [Scheme.Hom.germ_stalkMap_apply]
  have h := congrArg (Y.presheaf.germ V y hy)
    (show (f.appIso V).hom ((f.appIso V).inv a) = a from
      ConcreteCategory.congr_hom (f.appIso V).inv_hom_id a)
  rw [Scheme.Hom.appIso_hom] at h
  simpa only [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply] using h.symm


/-- The additive identification of actual module stalks under open restriction. -/
def restrictionStalkAddIso :
    (E.restrict f).presheaf.stalk y ≅ E.presheaf.stalk (f y) :=
  (Scheme.Modules.restrictStalkNatIso f y).app E

/-- The actual restriction-stalk identification has the prescribed germ formula. -/
theorem restrictionStalkAddIso_germ (V : Y.Opens) (hy : y ∈ V)
    (b : Γ(E.restrict f, V)) :
    (restrictionStalkAddIso f E y).hom ((E.restrict f).presheaf.germ V y hy b) =
      E.presheaf.germ (f ''ᵁ V) (f y) (by exact ⟨y, hy, rfl⟩)
        ((E.restrictAppIso f V).hom b) := by
  exact ConcreteCategory.congr_hom
    (Scheme.Modules.germ_restrictStalkNatIso_hom_app f y E hy) b

/-- Restriction identifies the actual stalk modules semilinearly over the
actual isomorphism of local rings. -/
def restrictionStalkEquiv :
    (E.restrict f).presheaf.stalk y ≃ₛₗ[RingHomClass.toRingHom (restrictionLocalRingEquiv f y)]
      E.presheaf.stalk (f y) where
  __ := (restrictionStalkAddIso f E y).addCommGroupIsoToAddEquiv
  map_smul' r s := by
    obtain ⟨U, hyU, a, rfl⟩ := Y.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hyV, b, rfl⟩ := (E.restrict f).presheaf.exists_le_germ_eq s hyU
    let i : V ⟶ U := homOfLE hVU
    change (restrictionStalkAddIso f E y).hom
      ((Y.presheaf.germ U y hyU a) • ((E.restrict f).presheaf.germ V y hyV b)) =
        restrictionLocalRingEquiv f y (Y.presheaf.germ U y hyU a) •
          (restrictionStalkAddIso f E y).hom ((E.restrict f).presheaf.germ V y hyV b)
    rw [← Y.presheaf.germ_res_apply i y hyV a, ← schemeModule_germ_smul]
    rw [restrictionStalkAddIso_germ, restrictionLocalRingEquiv_germ,
      restrictionStalkAddIso_germ, ← schemeModule_germ_smul]
    congr 1

/-- A free actual stalk remains free after restricting the sheaf to an open
subscheme; the local rings are related by their proved isomorphism. -/
theorem restrictionStalk_free
    [Module.Free (X.presheaf.stalk (f y)) (E.presheaf.stalk (f y))] :
    Module.Free (Y.presheaf.stalk y) ((E.restrict f).presheaf.stalk y) :=
  Module.Free.of_equiv (restrictionStalkEquiv f E y).symm

end Normalizer
