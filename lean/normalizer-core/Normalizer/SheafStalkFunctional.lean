import Normalizer.SheafStalkMap

/-! A functional on an actual scheme-module sheaf induces a functional on
each actual stalk, valued in the actual local ring. The construction uses
the colimit defining the stalk, and its germ formula is proved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u
variable {X : Scheme.{u}} {Q : X.Modules}
  (ψ : Q ⟶ SheafOfModules.unit X.ringCatSheaf) (x : X)

private def functionalCocone : Cocone ((OpenNhds.inclusion x).op ⋙ Q.presheaf) where
  pt := AddCommGrpCat.of (X.presheaf.stalk x)
  ι := {
    app := fun U => AddCommGrpCat.ofHom
      ((X.presheaf.germ U.unop.1 x U.unop.2).hom.toAddMonoidHom.comp
        (ψ.val.app (op U.unop.1)).hom.toAddMonoidHom)
    naturality := by
      intro U V f
      ext s
      change X.presheaf.germ V.unop.1 x V.unop.2
          (ψ.val.app (op V.unop.1) (Q.presheaf.map ((OpenNhds.inclusion x).op.map f) s)) =
        X.presheaf.germ U.unop.1 x U.unop.2 (ψ.val.app (op U.unop.1) s)
      have hn := PresheafOfModules.naturality_apply ψ.val
        ((OpenNhds.inclusion x).op.map f) s
      exact (congrArg (X.presheaf.germ V.unop.1 x V.unop.2) hn).trans
        (X.presheaf.germ_res_apply ((OpenNhds.inclusion x).map f.unop) x V.unop.2 _) }

private def stalkFunctionalAdd : Q.presheaf.stalk x →+ X.presheaf.stalk x :=
  (colimit.desc _ (functionalCocone ψ x)).hom

private theorem stalkFunctionalAdd_germ (U : X.Opens) (hx : x ∈ U) (s : Γ(Q, U)) :
    stalkFunctionalAdd ψ x (Q.presheaf.germ U x hx s) =
      X.presheaf.germ U x hx (ψ.val.app (op U) s) := by
  exact ConcreteCategory.congr_hom
    (colimit.ι_desc (functionalCocone ψ x) (op ⟨U, hx⟩)) s

/-- The actual local-ring-valued stalk functional induced by a sheaf
morphism into the unit sheaf. Its linearity follows from germ compatibility. -/
def schemeStalkFunctional : Q.presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x where
  __ := stalkFunctionalAdd ψ x
  map_smul' r s := by
    change stalkFunctionalAdd ψ x (r • s) = r * stalkFunctionalAdd ψ x s
    obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, b, rfl⟩ := Q.presheaf.exists_le_germ_eq s hxU
    let i : V ⟶ U := homOfLE hVU
    rw [← X.presheaf.germ_res_apply i x hxV a, ← schemeModule_germ_smul]
    rw [stalkFunctionalAdd_germ, stalkFunctionalAdd_germ]
    let l : Γ(Q, V) →ₗ[Γ(X, V)] Γ(X, V) := (ψ.val.app (op V)).hom
    change X.presheaf.germ V x hxV (l (X.presheaf.map i.op a • b)) =
      X.presheaf.germ V x hxV (X.presheaf.map i.op a) * X.presheaf.germ V x hxV (l b)
    rw [l.map_smul]
    exact map_mul _ _ _

/-- The stalk functional agrees with the original sheaf map on every germ. -/
theorem schemeStalkFunctional_germ (U : X.Opens) (hx : x ∈ U) (s : Γ(Q, U)) :
    schemeStalkFunctional ψ x (Q.presheaf.germ U x hx s) =
      X.presheaf.germ U x hx (ψ.val.app (op U) s) :=
  stalkFunctionalAdd_germ ψ x U hx s

end Normalizer
