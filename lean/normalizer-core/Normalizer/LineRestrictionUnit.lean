import Normalizer.LineRestrictionComparison

/-! Adjunction-unit coherence for genuine local line restriction comparisons. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite
universe u

/-- The canonical pullback-composition comparison has the unit compatibility
specified by its actual conjugate pushforward-composition map. -/
theorem schemePullbackComp_unit_compatibility {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)).unit.app M ≫
        (Scheme.Modules.pushforwardComp f g).hom.app
          ((Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).obj M) =
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
        (Scheme.Modules.pushforward (f ≫ g)).map
          ((Scheme.Modules.pullbackComp f g).inv.app M) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rwa [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h

/-- The inverse open-restriction comparison also preserves the actual unit. -/
theorem schemeOpenRestriction_inv_unit_compatibility {X : Scheme.{u}}
    (L : X.Modules) (U : X.Opens) :
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app L ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app L) =
      (Scheme.Modules.restrictAdjunction U.ι).unit.app L := by
  rw [← schemeOpenRestriction_unit_compatibility, Category.assoc, ← Functor.map_comp]
  simp

/-- Transport along equal scheme morphisms preserves the actual pullback
adjunction unit and its corresponding pushforward transport. -/
theorem schemePullbackCongr_unit_compatibility {X Y : Scheme.{u}}
    {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullbackCongr h).hom.app M) ≫
        (Scheme.Modules.pushforwardCongr h).hom.app ((Scheme.Modules.pullback g).obj M) =
      (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M := by
  subst g
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change ((Scheme.Modules.pullback f).obj M).presheaf.map (𝟙 (op (f ⁻¹ᵁ U.unop)))
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app U s) = _
  rw [((Scheme.Modules.pullback f).obj M).presheaf.map_id]
  rfl

end Normalizer
