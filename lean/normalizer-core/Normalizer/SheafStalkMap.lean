import Normalizer.IntegralSheafTorsion
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! Maps of actual scheme-module stalks, linear over the actual local ring. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory AlgebraicGeometry

universe u
variable {X : Scheme.{u}} {E H : X.Modules}

/-- A sheaf morphism induces a linear map of actual stalks over the local ring. -/
def schemeModuleStalkMap (f : E ⟶ H) (x : X) :
    E.presheaf.stalk x →ₗ[X.presheaf.stalk x] H.presheaf.stalk x where
  __ := ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.mapPresheaf).hom
  map_smul' r s := by
    let : Module (X.presheaf.stalk x)
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj H.presheaf) :=
      schemeModuleStalkModule H x
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.mapPresheaf
      (r • s : E.presheaf.stalk x) : H.presheaf.stalk x) =
      r • ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.mapPresheaf s :
        H.presheaf.stalk x)
    obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, b, rfl⟩ := E.presheaf.exists_le_germ_eq s hxU
    let i : V ⟶ U := homOfLE hVU
    rw [← X.presheaf.germ_res_apply i x hxV a, ← schemeModule_germ_smul]
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    simp only [Scheme.Modules.mapPresheaf_app, Scheme.Modules.Hom.app_smul,
      schemeModule_germ_smul]

/-- The induced stalk map sends the germ of a section to the germ of its image. -/
theorem schemeModuleStalkMap_germ (f : E ⟶ H) (x : X) (U : X.Opens)
    (hx : x ∈ U) (s : Γ(E, U)) :
    schemeModuleStalkMap f x (E.presheaf.germ U x hx s) =
      H.presheaf.germ U x hx (f.app U s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx f.mapPresheaf s

/-- An actual sheaf isomorphism induces an isomorphism of stalk modules over
the same actual local ring. -/
def schemeModuleStalkIso (e : E ≅ H) (x : X) :
    E.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] H.presheaf.stalk x where
  __ := ((Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso e).addCommGroupIsoToAddEquiv
  map_smul' := (schemeModuleStalkMap e.hom x).map_smul

end Normalizer
