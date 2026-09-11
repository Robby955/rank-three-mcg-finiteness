import Normalizer.PullbackRestrictionUnit

/-! Compatibility of genuine line charts with the actual pullback adjunction unit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite
universe u

variable {X D : Scheme.{u}} (i : D ⟶ X) (L : X.Modules) (U : X.Opens)

/-- The constructed inverse-image line chart agrees with its actual restricted-scheme
chart under the equivalence of sites. -/
theorem schemePullbackLineChart_overEquiv (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U) :
    (Scheme.Modules.overEquiv (i ⁻¹ᵁ U)).functor.map
        (schemePullbackLineChart i L U e).inv ≫
      ((i ⁻¹ᵁ U).sheafOfModulesEquivOverUnit D.ringCatSheaf).hom =
    ((Scheme.Modules.overFunctorEquiv (i ⁻¹ᵁ U)).app _).hom ≫
      (schemePullbackRestrictIso i L U).hom ≫
      (Scheme.Modules.pullback (i ∣_ U)).map (schemeLineChartOnRestriction L U e).inv ≫
      SheafOfModules.pullbackObjUnitToUnit (i ∣_ U).toRingCatSheafHom := by
  simp only [schemePullbackLineChart, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.symm_hom,
    TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit,
    Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  simp [Scheme.Modules.overEquiv, Equivalence.fun_inv_map,
    Iso.app_hom, Iso.app_inv, Category.assoc]

/-- The actual restricted line chart has the original chart coordinates. -/
theorem schemeLineChartOnRestriction_hom_app (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (W : U.toScheme.Opens) (a : Γ(X, U.ι ''ᵁ W)) :
    (schemeLineChartOnRestriction L U e).hom.val.app (op W) a =
      e.hom.val.app (op (Over.mk (homOfLE (U.ι_image_le W)))) a := by
  change e.hom.val.app (op (Over.mk (homOfLE (U.ι_image_le W)))) ((U.ι.appIso W).inv a) = _
  rw [Scheme.Opens.ι_appIso]
  rfl

/-- A genuine global line trivialization intertwines the actual adjunction unit
with the actual structure-sheaf map. -/
theorem schemeLineIso_unit_compatibility {X D : Scheme.{u}} (i : D ⟶ X) (L : X.Modules)
    (e : SheafOfModules.unit X.ringCatSheaf ≅ L) :
    e.hom ≫ (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L ≫
      (Scheme.Modules.pushforward i).map
        ((Scheme.Modules.pullback i).map e.inv ≫
          SheafOfModules.pullbackObjUnitToUnit i.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom := by
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality e.hom
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
  have hmap := (Scheme.Modules.pullback i).map_id (SheafOfModules.unit X.ringCatSheaf)
  have h := congrArg (fun f => (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (SheafOfModules.unit X.ringCatSheaf) ≫ (Scheme.Modules.pushforward i).map
        (f ≫ SheafOfModules.pullbackObjUnitToUnit i.toRingCatSheafHom)) hmap
  exact h.trans (by simpa only [Category.id_comp] using schemePullbackUnit_unit_compatibility i)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
/-- The genuine local line comparison carries the actual adjunction unit
to the actual structure-sheaf map, with the original line chart. -/
theorem schemeLineRestrictionComparison_unit_compatibility (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U) :
    e.hom ≫ (SheafOfModules.overFunctor X.ringCatSheaf U).map
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L) ≫
        (schemeLineRestrictionComparison i L U e).hom =
      (SheafOfModules.overFunctor X.ringCatSheaf U).map
        (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) := by
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (schemePullbackLineChart i L U e).inv.val.app
    (op (Over.mk (homOfLE (show i ⁻¹ᵁ (U.ι ''ᵁ W.unop) ≤ i ⁻¹ᵁ U from
      fun _ hx ↦ U.ι_image_le W.unop hx))))
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L).val.app
      (op (U.ι ''ᵁ W.unop))
      (e.hom.val.app (op (Over.mk (homOfLE (U.ι_image_le W.unop)))) a)) =
      i.app (U.ι ''ᵁ W.unop) a
  let V := i ⁻¹ᵁ U
  let j := i ∣_ U
  let P := (Scheme.Modules.pullback i).obj L
  let Z := i ⁻¹ᵁ (U.ι ''ᵁ W.unop)
  let T := j ⁻¹ᵁ W.unop
  have k : V.ι ''ᵁ T = Z := image_morphismRestrict_preimage i U W.unop
  have inj : Function.Injective (D.presheaf.map (eqToHom k).op) :=
    (ConcreteCategory.bijective_of_isIso (D.presheaf.map (eqToHom k).op)).injective
  apply inj
  let f : Over.mk (homOfLE (V.ι_image_le T)) ⟶
      Over.mk (homOfLE (show Z ≤ V from fun _ hx ↦ U.ι_image_le W.unop hx)) :=
    Over.homMk (eqToHom k)
  have hn := PresheafOfModules.naturality_apply
    (schemePullbackLineChart i L U e).inv.val f.op
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L).val.app
      (op (U.ι ''ᵁ W.unop))
      (e.hom.val.app (op (Over.mk (homOfLE (U.ι_image_le W.unop)))) a))
  change _ = D.presheaf.map (eqToHom k).op (i.app (U.ι ''ᵁ W.unop) a)
  refine hn.symm.trans ?_
  have hc := congrArg (fun q => q.val.app (op T)
    (P.presheaf.map (eqToHom k).op
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L).val.app
        (op (U.ι ''ᵁ W.unop))
        (e.hom.val.app (op (Over.mk (homOfLE (U.ι_image_le W.unop)))) a))))
    (schemePullbackLineChart_overEquiv i L U e)
  refine hc.trans ?_
  let e' := schemeLineChartOnRestriction L U e
  let c := SheafOfModules.pullbackObjUnitToUnit j.toRingCatSheafHom
  let b := e.hom.val.app (op (Over.mk (homOfLE (U.ι_image_le W.unop)))) a
  change c.val.app (op T) (((Scheme.Modules.pullback j).map e'.inv).val.app (op T)
    ((schemePullbackRestrictIso i L U).hom.val.app (op T)
      (P.presheaf.map (eqToHom k).op
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L).val.app
          (op (U.ι ''ᵁ W.unop)) b)))) = _
  have hr := congrArg (fun f => f b)
    (schemePullbackRestrictIso_unit_app i U L W.unop)
  refine (congrArg (fun z => c.val.app (op T)
    (((Scheme.Modules.pullback j).map e'.inv).val.app (op T) z)) hr).trans ?_
  have he := congrArg (fun f => f.val.app W a)
    (schemeLineIso_unit_compatibility j (L.restrict U.ι) e')
  change c.val.app (op T) (((Scheme.Modules.pullback j).map e'.inv).val.app (op T)
    (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app (L.restrict U.ι)).val.app W
      (e'.hom.val.app W a))) = j.app W.unop a at he
  have he' : e'.hom.val.app W a = b :=
    schemeLineChartOnRestriction_hom_app L U e W.unop a
  rw [he'] at he
  refine he.trans ?_
  exact congrArg (fun f => f a) (morphismRestrict_app i U W.unop)

end Normalizer
