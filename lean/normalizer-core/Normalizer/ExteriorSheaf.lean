import Normalizer.ExteriorSemilinear
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! The actual exterior-power module sheaf is the sheafification of
sectionwise exterior powers, with coefficient-changing restriction maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u
variable {X : Scheme.{u}} (H : X.Modules) (n : ℕ)

local instance (U : X.Opensᵒᵖ) : Module (X.presheaf.obj U) (H.presheaf.obj U) :=
  (H.val.obj U).isModule

private def exteriorRestriction {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    ModuleCat.of (X.presheaf.obj U) (⋀[X.presheaf.obj U]^n (H.presheaf.obj U)) ⟶
      (ModuleCat.restrictScalars (X.presheaf.map f).hom).obj
        (ModuleCat.of (X.presheaf.obj V) (⋀[X.presheaf.obj V]^n (H.presheaf.obj V))) := by
  letI := Module.compHom (⋀[X.presheaf.obj V]^n (H.presheaf.obj V)) (X.presheaf.map f).hom
  exact ModuleCat.ofHom {
    toFun := exteriorSemilinearMap n (X.presheaf.map f).hom (H.val.restrictₛₗ f)
    map_add' := (exteriorSemilinearMap n (X.presheaf.map f).hom (H.val.restrictₛₗ f)).map_add
    map_smul' := (exteriorSemilinearMap n (X.presheaf.map f).hom (H.val.restrictₛₗ f)).map_smulₛₗ }

/-- Actual sectionwise exterior powers, with restrictions induced by the
actual coefficient-changing restriction maps of the original sheaf. -/
def schemeExteriorPresheaf : X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.mk (R := X.presheaf)
    (fun U => ModuleCat.of (X.presheaf.obj U) (⋀[X.presheaf.obj U]^n (H.presheaf.obj U)))
    (fun f => exteriorRestriction H n f)
    (by
      intro U
      apply ModuleCat.hom_ext
      apply exteriorPower.linearMap_ext
      ext v
      change exteriorSemilinearMap n (X.presheaf.map (𝟙 U)).hom (H.val.restrictₛₗ (𝟙 U))
        (exteriorPower.ιMulti (X.presheaf.obj U) n v) = exteriorPower.ιMulti (X.presheaf.obj U) n v
      rw [exteriorSemilinearMap_ιMulti]
      congr 1
      funext i
      exact ConcreteCategory.congr_hom (H.presheaf.map_id U) (v i))
    (by
      intro U V W f g
      apply ModuleCat.hom_ext
      apply exteriorPower.linearMap_ext
      ext v
      change exteriorSemilinearMap n (X.presheaf.map (f ≫ g)).hom (H.val.restrictₛₗ (f ≫ g))
        (exteriorPower.ιMulti (X.presheaf.obj U) n v) =
        exteriorSemilinearMap n (X.presheaf.map g).hom (H.val.restrictₛₗ g)
          (exteriorSemilinearMap n (X.presheaf.map f).hom (H.val.restrictₛₗ f)
            (exteriorPower.ιMulti (X.presheaf.obj U) n v))
      simp only [exteriorSemilinearMap_ιMulti]
      congr 1
      funext i
      exact H.val.map_comp_apply f g (v i))

/-- Restriction of a pure exterior product is the exterior product of the
restricted sections, with its actual new coefficient ring. -/
theorem schemeExteriorPresheaf_restrict {U V : X.Opensᵒᵖ} (f : U ⟶ V)
    (v : Fin n → H.presheaf.obj U) :
    (schemeExteriorPresheaf H n).map f (exteriorPower.ιMulti _ n v) =
      exteriorPower.ιMulti _ n (fun i => H.presheaf.map f (v i)) :=
  exteriorSemilinearMap_ιMulti n (X.presheaf.map f).hom (H.val.restrictₛₗ f) v

/-- The actual exterior-power sheaf is the associated sheaf of the
sectionwise exterior-power module presheaf. -/
def schemeExteriorSheaf : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (schemeExteriorPresheaf H n)

/-- Canonical projection from the exterior-power presheaf to its associated sheaf. -/
def schemeExteriorProjection : schemeExteriorPresheaf H n ⟶ (schemeExteriorSheaf H n).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _

/-- The actual pure exterior product of local sections in the exterior-power sheaf. -/
def schemeExteriorPure (U : X.Opens) (v : Fin n → Γ(H, U)) : Γ(schemeExteriorSheaf H n, U) :=
  (schemeExteriorProjection H n).app (op U) (exteriorPower.ιMulti _ n v)

/-- Exterior products in the actual sheaf commute with restriction. -/
theorem schemeExteriorPure_restrict {U V : X.Opens} (f : V ⟶ U)
    (v : Fin n → Γ(H, U)) :
    (schemeExteriorSheaf H n).presheaf.map f.op (schemeExteriorPure H n U v) =
      schemeExteriorPure H n V (fun i => H.presheaf.map f.op (v i)) := by
  exact (PresheafOfModules.naturality_apply (schemeExteriorProjection H n) f.op
    (exteriorPower.ιMulti _ n v)).symm.trans
      (congrArg ((schemeExteriorProjection H n).app (op V))
        (schemeExteriorPresheaf_restrict H n f.op v))

/-- The exterior product of a specified family of actual global sections. -/
def schemeExteriorGlobalSection (s : Fin n → Γ(H, ⊤)) : Γ(schemeExteriorSheaf H n, ⊤) :=
  schemeExteriorPure H n ⊤ s

end Normalizer
