import Normalizer.SectionLineExact
import Mathlib.Topology.Sheaves.Functors

/-! Forgetting module structure commutes with actual scheme pushforward.
The comparison preserves the underlying additive sections and morphisms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite
universe u v

/-- The existing module-sheaf forgetful functor, specialized to a scheme. -/
def schemeModulesToAbelianSheaves (X : Scheme.{u}) :
    X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  SheafOfModules.toSheaf X.ringCatSheaf

/-- Its underlying presheaf is the actual scheme-module additive presheaf. -/
theorem schemeModulesToAbelianSheaves_obj_presheaf {X : Scheme.{u}} (F : X.Modules) :
    ((schemeModulesToAbelianSheaves X).obj F).obj = F.presheaf := rfl

/-- On morphisms it is the actual scheme-module additive presheaf map. -/
theorem schemeModulesToAbelianSheaves_map {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) :
    ((schemeModulesToAbelianSheaves X).map f).hom = f.mapPresheaf := rfl

variable {X Y : Scheme.{u}} (i : Y ⟶ X)

/-- Actual scheme-module pushforward commutes with forgetting to abelian
sheaves. Scalar restriction does not alter the underlying additive sheaf. -/
def schemeModuleAbelianPushforwardIso :
    Scheme.Modules.pushforward i ⋙ schemeModulesToAbelianSheaves X ≅
      schemeModulesToAbelianSheaves Y ⋙ TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base :=
  Iso.refl _

/-- The canonical comparison is identity on actual sections on every open. -/
theorem schemeModuleAbelianPushforwardIso_app (F : Y.Modules) (U : X.Opens)
    (a : Γ(F, i ⁻¹ᵁ U)) :
    ((schemeModuleAbelianPushforwardIso i).app F).hom.hom.app (op U) a = a := rfl

/-- The comparison commutes with every actual module-sheaf morphism. -/
theorem schemeModuleAbelianPushforwardIso_naturality {F G : Y.Modules} (f : F ⟶ G) :
    (schemeModulesToAbelianSheaves X).map ((Scheme.Modules.pushforward i).map f) ≫
        ((schemeModuleAbelianPushforwardIso i).app G).hom =
      ((schemeModuleAbelianPushforwardIso i).app F).hom ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map
          ((schemeModulesToAbelianSheaves Y).map f) :=
  (schemeModuleAbelianPushforwardIso i).hom.naturality f

/-- Pushforward of a module morphism acts on underlying abelian sections
by that same morphism on the actual inverse-image open. -/
theorem schemeModuleAbelianPushforward_map_app {F G : Y.Modules} (f : F ⟶ G)
    (U : X.Opens) (a : Γ(F, i ⁻¹ᵁ U)) :
    ((schemeModulesToAbelianSheaves X).map
      ((Scheme.Modules.pushforward i).map f)).hom.app (op U) a = f.app (i ⁻¹ᵁ U) a := rfl

variable (L : X.Modules) (s : Γ(L, ⊤))
  {ι : Type v} [Finite ι] (U : ι → X.Opens) [∀ a, QuasiCompact (U a).ι]
  (e : ∀ a, (SheafOfModules.unit X.ringCatSheaf).over (U a) ≅ L.over (U a))
  (hU : iSup U = ⊤)

/-- The actual line-restriction cokernel, viewed as an abelian sheaf, is
the ordinary abelian-sheaf pushforward of the actual pulled-back line bundle. -/
def schemeSectionLineRestrictionAbelianIso :
    (schemeModulesToAbelianSheaves X).obj (schemeSectionLineRestrictionSheaf L s U e hU) ≅
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s) U
          (fun a => schemeDualLineFrameIso L (e a)) hU).base).obj
        ((schemeModulesToAbelianSheaves
          (schemeSectionZeroScheme (schemeSectionDualEvaluation L s) U
            (fun a => schemeDualLineFrameIso L (e a)) hU)).obj
          ((Scheme.Modules.pullback
            (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s) U
              (fun a => schemeDualLineFrameIso L (e a)) hU)).obj L)) :=
  (schemeModuleAbelianPushforwardIso
    (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s) U
      (fun a => schemeDualLineFrameIso L (e a)) hU)).app _

/-- The underlying abelian sheaf of the actual section cokernel is the
ordinary pushforward of the actual restricted line bundle. -/
def schemeSectionLineCokernelAbelianIso :
    (schemeModulesToAbelianSheaves X).obj (Limits.cokernel (schemeSectionHom L s)) ≅
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s) U
          (fun a => schemeDualLineFrameIso L (e a)) hU).base).obj
        ((schemeModulesToAbelianSheaves
          (schemeSectionZeroScheme (schemeSectionDualEvaluation L s) U
            (fun a => schemeDualLineFrameIso L (e a)) hU)).obj
          ((Scheme.Modules.pullback
            (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s) U
              (fun a => schemeDualLineFrameIso L (e a)) hU)).obj L)) :=
  (schemeModulesToAbelianSheaves X).mapIso (schemeSectionLineCokernelIso L s U e hU) ≪≫
    schemeSectionLineRestrictionAbelianIso L s U e hU

/-- The abelian-sheaf cokernel identification preserves the actual
cokernel projection and the actual adjunction restriction map. -/
theorem schemeSectionLineCokernelAbelianIso_π_hom :
    (schemeModulesToAbelianSheaves X).map (Limits.cokernel.π (schemeSectionHom L s)) ≫
      (schemeSectionLineCokernelAbelianIso L s U e hU).hom =
    (schemeModulesToAbelianSheaves X).map (schemeSectionLineRestrictionMap L s U e hU) ≫
      (schemeSectionLineRestrictionAbelianIso L s U e hU).hom := by
  change _ ≫ ((schemeModulesToAbelianSheaves X).map
    (schemeSectionLineCokernelIso L s U e hU).hom ≫ _) = _
  rw [← Category.assoc, ← Functor.map_comp, schemeSectionLineCokernelIso_π_hom]

end Normalizer
