import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! Actual line-chart transport through pullback and local pushforward. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u
variable {X D : Scheme.{u}} (i : D ⟶ X) (L : X.Modules) (U : X.Opens)

/-- Restricting an actual pullback to the inverse-image open is the
pullback of the actual restriction along the restricted scheme morphism. -/
def schemePullbackRestrictIso :
    ((Scheme.Modules.pullback i).obj L).restrict (i ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (i ∣_ U)).obj (L.restrict U.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback (i ⁻¹ᵁ U).ι).app _ ≪≫
    (Scheme.Modules.pullbackComp (i ⁻¹ᵁ U).ι i).app L ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι i U).symm).app L ≪≫
    (Scheme.Modules.pullbackComp (i ∣_ U) U.ι).symm.app L ≪≫
    (Scheme.Modules.pullback (i ∣_ U)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).symm

/-- Convert a genuine over-site line chart to the actual open-subscheme restriction. -/
def schemeLineChartOnRestriction
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U) :
    SheafOfModules.unit U.toScheme.ringCatSheaf ≅ L.restrict U.ι :=
  (Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
    ((Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf)).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
    (Scheme.Modules.overFunctorEquiv U).app L

/-- A genuine local line chart pulls back to a genuine chart on the
actual inverse-image open, for an arbitrary scheme morphism. -/
def schemePullbackLineChart
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U) :
    (SheafOfModules.unit D.ringCatSheaf).over (i ⁻¹ᵁ U) ≅
      ((Scheme.Modules.pullback i).obj L).over (i ⁻¹ᵁ U) := by
  let V := i ⁻¹ᵁ U
  let Q := Scheme.Modules.overEquiv V
  let a : SheafOfModules.unit V.toScheme.ringCatSheaf ≅
      ((Scheme.Modules.pullback i).obj L).restrict V.ι :=
    (asIso (SheafOfModules.pullbackObjUnitToUnit (i ∣_ U).toRingCatSheafHom)).symm ≪≫
      (Scheme.Modules.pullback (i ∣_ U)).mapIso (schemeLineChartOnRestriction L U e) ≪≫
      (schemePullbackRestrictIso i L U).symm
  exact (V.sheafOfModulesEquivOverInverseUnit D.ringCatSheaf).symm ≪≫
    Q.inverse.mapIso a ≪≫
    Q.inverse.mapIso ((Scheme.Modules.overFunctorEquiv V).app _).symm ≪≫
    (Q.unitIso.app _).symm

variable {M N : D.Modules}

/-- A morphism over the actual inverse-image open induces a morphism
between the pushforwards over the original open, by actual scalar restriction. -/
def schemePushforwardOverMap
    (f : M.over (i ⁻¹ᵁ U) ⟶ N.over (i ⁻¹ᵁ U)) :
    ((Scheme.Modules.pushforward i).obj M).over U ⟶
      ((Scheme.Modules.pushforward i).obj N).over U where
  val := {
    app := fun W ↦
      (ModuleCat.restrictScalars (i.app W.unop.left).hom).map
        (f.val.app (op (Over.mk (homOfLE
          (show i ⁻¹ᵁ W.unop.left ≤ i ⁻¹ᵁ U from fun _ hx ↦ (leOfHom W.unop.hom) hx)))))
    naturality := by
      intro V W g
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      let g' : Over.mk (homOfLE
          (show i ⁻¹ᵁ W.unop.left ≤ i ⁻¹ᵁ U from fun _ hx ↦ (leOfHom W.unop.hom) hx)) ⟶
          Over.mk (homOfLE
            (show i ⁻¹ᵁ V.unop.left ≤ i ⁻¹ᵁ U from fun _ hx ↦ (leOfHom V.unop.hom) hx)) :=
        Over.homMk (homOfLE (show i ⁻¹ᵁ W.unop.left ≤ i ⁻¹ᵁ V.unop.left from
          fun _ hx ↦ (leOfHom g.unop.left) hx))
      exact PresheafOfModules.naturality_apply f.val g'.op m }

/-- Genuine inverse-image charts induce actual isomorphisms between the
pushforwards over the original open. -/
def schemePushforwardOverIso
    (e : M.over (i ⁻¹ᵁ U) ≅ N.over (i ⁻¹ᵁ U)) :
    ((Scheme.Modules.pushforward i).obj M).over U ≅
      ((Scheme.Modules.pushforward i).obj N).over U where
  hom := schemePushforwardOverMap i U e.hom
  inv := schemePushforwardOverMap i U e.inv
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    exact (ModuleCat.restrictScalars (i.app W.unop.left).hom).map_comp _ _ |>.symm.trans
      (congrArg ((ModuleCat.restrictScalars (i.app W.unop.left).hom).map)
        (congrArg (fun f ↦ f.val.app (op (Over.mk (homOfLE
          (show i ⁻¹ᵁ W.unop.left ≤ i ⁻¹ᵁ U from fun _ hx ↦ (leOfHom W.unop.hom) hx)))) )
          e.hom_inv_id))
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    exact (ModuleCat.restrictScalars (i.app W.unop.left).hom).map_comp _ _ |>.symm.trans
      (congrArg ((ModuleCat.restrictScalars (i.app W.unop.left).hom).map)
        (congrArg (fun f ↦ f.val.app (op (Over.mk (homOfLE
          (show i ⁻¹ᵁ W.unop.left ≤ i ⁻¹ᵁ U from fun _ hx ↦ (leOfHom W.unop.hom) hx)))) )
          e.inv_hom_id))

/-- A genuine line chart identifies the actual pushforward of its pullback
with the actual pushed-forward structure sheaf on that same chart. -/
def schemeLineRestrictionComparison
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U) :
    ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L)).over U ≅
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit D.ringCatSheaf)).over U :=
  schemePushforwardOverIso i U (schemePullbackLineChart i L U e).symm

/-- The canonical identification of the pullback of the unit sheaf
preserves the actual structure-sheaf restriction map under adjunction. -/
theorem schemePullbackUnit_unit_compatibility :
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.pushforward i).map
        (SheafOfModules.pullbackObjUnitToUnit i.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom := by
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    i.toRingCatSheafHom

/-- The comparison between actual open restriction and categorical
pullback preserves their adjunction units. -/
theorem schemeOpenRestriction_unit_compatibility :
    (Scheme.Modules.restrictAdjunction U.ι).unit.app L ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app L) =
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app L :=
  Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction U.ι)
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι) L

end Normalizer
