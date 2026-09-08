import Normalizer.NormalizerSheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! The tensor product of module sheaves is the sheafification of the
sectionwise tensor product of their underlying presheaves. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Opposite TopologicalSpace

universe u
variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  (A B : SheafOfModules.{u} R)
  (ring_comm : ∀ V (a b : R.obj.obj V), a * b = b * a)

/-- The section ring with its supplied commutativity proof. Its underlying ring is unchanged. -/
@[instance_reducible]
def moduleSectionCommRing (V : (Opens X)ᵒᵖ) : CommRing (R.obj.obj V) :=
  CommRing.mk (ring_comm V)

private def commRingPresheaf : (Opens X)ᵒᵖ ⥤ CommRingCat.{u} where
  obj V := @CommRingCat.of (R.obj.obj V) (moduleSectionCommRing ring_comm V)
  map {V W} f := @CommRingCat.ofHom _ _
    (moduleSectionCommRing ring_comm V) (moduleSectionCommRing ring_comm W)
    (R.obj.map f).hom
  map_id V := by ext x; exact ConcreteCategory.congr_hom (R.obj.map_id V) x
  map_comp f g := by ext x; exact ConcreteCategory.congr_hom (R.obj.map_comp f g) x

/-- The genuine sectionwise tensor product presheaf. -/
def moduleTensorPresheaf : PresheafOfModules.{u} R.obj :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj
    (R := commRingPresheaf ring_comm) A.val B.val

/-- The tensor sheaf is the sheafification of the tensor presheaf. -/
def moduleTensorSheaf : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    (moduleTensorPresheaf A B ring_comm)

/-- The canonical map from the tensor presheaf to its associated sheaf. -/
def moduleTensorProjection : moduleTensorPresheaf A B ring_comm ⟶
    (moduleTensorSheaf A B ring_comm).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app _

/-- The universal property of the tensor sheaf, for maps out of the actual
sectionwise tensor presheaf. -/
def moduleTensorHomEquiv (C : SheafOfModules.{u} R) :
    (moduleTensorSheaf A B ring_comm ⟶ C) ≃
      (moduleTensorPresheaf A B ring_comm ⟶ C.val) :=
  PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)

/-- Extend a morphism from the tensor presheaf uniquely to the tensor sheaf. -/
def moduleTensorLift (C : SheafOfModules.{u} R)
    (f : moduleTensorPresheaf A B ring_comm ⟶ C.val) :
    moduleTensorSheaf A B ring_comm ⟶ C :=
  (moduleTensorHomEquiv A B ring_comm C).symm f

/-- The universal equivalence restricts a sheaf morphism along the canonical projection. -/
theorem moduleTensorHomEquiv_apply (C : SheafOfModules.{u} R)
    (f : moduleTensorSheaf A B ring_comm ⟶ C) :
    moduleTensorHomEquiv A B ring_comm C f =
      moduleTensorProjection A B ring_comm ≫ f.val := rfl

/-- A lifted map has the prescribed values on the tensor presheaf. -/
theorem moduleTensorProjection_lift (C : SheafOfModules.{u} R)
    (f : moduleTensorPresheaf A B ring_comm ⟶ C.val) :
    moduleTensorProjection A B ring_comm ≫
      (moduleTensorLift A B ring_comm C f).val = f :=
  (moduleTensorHomEquiv A B ring_comm C).apply_symm_apply f

/-- Uniqueness in the tensor sheaf's universal property. -/
theorem moduleTensor_hom_ext (C : SheafOfModules.{u} R)
    (f g : moduleTensorSheaf A B ring_comm ⟶ C)
    (h : moduleTensorProjection A B ring_comm ≫ f.val =
      moduleTensorProjection A B ring_comm ≫ g.val) : f = g :=
  (moduleTensorHomEquiv A B ring_comm C).injective h

/-- A pure tensor in the sectionwise tensor presheaf. -/
def moduleTensorPresheafPure (V : (Opens X)ᵒᵖ)
    (a : A.val.obj V) (b : B.val.obj V) :
    (moduleTensorPresheaf A B ring_comm).obj V := by
  letI := moduleSectionCommRing ring_comm V
  exact a ⊗ₜ[R.obj.obj V] b

/-- The image of a pure tensor in the actual tensor sheaf. -/
def moduleTensorPure (V : (Opens X)ᵒᵖ)
    (a : A.val.obj V) (b : B.val.obj V) :
    (moduleTensorSheaf A B ring_comm).val.obj V :=
  (moduleTensorProjection A B ring_comm).app V
    (moduleTensorPresheafPure A B ring_comm V a b)

/-- Restriction preserves pure tensors in the tensor presheaf. -/
theorem moduleTensorPresheafPure_restrict {V W : (Opens X)ᵒᵖ} (h : V ⟶ W)
    (a : A.val.obj V) (b : B.val.obj V) :
    (moduleTensorPresheaf A B ring_comm).map h
      (moduleTensorPresheafPure A B ring_comm V a b) =
        moduleTensorPresheafPure A B ring_comm W (A.val.map h a) (B.val.map h b) := rfl

/-- The restriction map is the usual tensor product of the two restrictions. -/
theorem moduleTensorPresheaf_map_tmul {V W : (Opens X)ᵒᵖ} (h : V ⟶ W)
    (a : A.val.obj V) (b : B.val.obj V) :
    letI := moduleSectionCommRing ring_comm V
    letI := moduleSectionCommRing ring_comm W
    (moduleTensorPresheaf A B ring_comm).map h (a ⊗ₜ[R.obj.obj V] b) =
      A.val.map h a ⊗ₜ[R.obj.obj W] B.val.map h b := by
  rfl

/-- Restriction preserves pure tensors after sheafification. -/
theorem moduleTensorPure_restrict {V W : (Opens X)ᵒᵖ} (h : V ⟶ W)
    (a : A.val.obj V) (b : B.val.obj V) :
    (moduleTensorSheaf A B ring_comm).val.map h
      (moduleTensorPure A B ring_comm V a b) =
        moduleTensorPure A B ring_comm W (A.val.map h a) (B.val.map h b) :=
  (PresheafOfModules.naturality_apply (moduleTensorProjection A B ring_comm) h _).symm

/-- A lifted map sends a pure tensor to the value prescribed by its presheaf map. -/
theorem moduleTensorLift_pure (C : SheafOfModules.{u} R)
    (f : moduleTensorPresheaf A B ring_comm ⟶ C.val) (V : (Opens X)ᵒᵖ)
    (a : A.val.obj V) (b : B.val.obj V) :
    (moduleTensorLift A B ring_comm C f).val.app V
      (moduleTensorPure A B ring_comm V a b) =
        f.app V (moduleTensorPresheafPure A B ring_comm V a b) :=
  ConcreteCategory.congr_hom
    (congrArg (fun k => k.app V) (moduleTensorProjection_lift A B ring_comm C f)) _

end Normalizer
