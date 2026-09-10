import Normalizer.GlobalSectionFrame
import Normalizer.DeterminantFrame
import Normalizer.TrivializedSubsheafEvaluation

/-! Pointwise unit determinants of the actual global section germs
construct a global sheaf trivialization. The curve degree argument that
establishes these determinant conditions is a separate input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u
variable {X : Scheme.{u}} (H : X.Modules) (ι : Type u) [Fintype ι] [DecidableEq ι]
  (s : ι → Γ(H, ⊤))

/-- The actual coordinate matrix of the global section germs, in a basis
of the actual module stalk over its local ring. -/
def schemeSectionStalkMatrix (x : X)
    (b : Module.Basis ι (X.presheaf.stalk x) (H.presheaf.stalk x)) :
    Matrix ι ι (X.presheaf.stalk x) :=
  frameCoordinateMatrix b (fun i => H.presheaf.germ ⊤ x trivial (s i))

private theorem sectionFrameStalk_bijective_iff (x : X)
    (b : Module.Basis ι (X.presheaf.stalk x) (H.presheaf.stalk x)) :
    IsUnit (schemeSectionStalkMatrix H ι s x b).det ↔
      Function.Bijective (schemeModuleStalkMap (schemeSectionFrameMap H ι s) x) := by
  rw [schemeSectionStalkMatrix, frameCoordinateMatrix_isUnit_det_iff]
  have he : (Fintype.linearCombination (X.presheaf.stalk x)
      (fun i => H.presheaf.germ ⊤ x trivial (s i)) :
        (ι → X.presheaf.stalk x) → H.presheaf.stalk x) =
      (schemeModuleStalkMap (schemeSectionFrameMap H ι s) x) ∘
        (schemeTrivialStalkEquiv X ι x) := by
    funext a
    exact (schemeSectionFrameMap_stalk H ι s x a).symm
  rw [he, Function.Bijective.of_comp_iff _ (schemeTrivialStalkEquiv X ι x).bijective]

/-- The actual section-family evaluation is a global isomorphism precisely
when its coordinate determinant is a unit at every stalk. -/
theorem schemeSectionFrameMap_isIso_iff_unit_det
    (b : ∀ x : X, Module.Basis ι (X.presheaf.stalk x) (H.presheaf.stalk x)) :
    IsIso (schemeSectionFrameMap H ι s) ↔
      ∀ x : X, IsUnit (schemeSectionStalkMatrix H ι s x (b x)).det := by
  constructor
  · intro h x
    let := h
    exact (sectionFrameStalk_bijective_iff H ι s x (b x)).mpr
      (schemeModuleStalkIso (asIso (schemeSectionFrameMap H ι s)) x).bijective
  · intro h
    exact schemeModule_isIso_of_stalk_bijective (schemeSectionFrameMap H ι s)
      (fun x => (sectionFrameStalk_bijective_iff H ι s x (b x)).mp (h x))

/-- A global trivialization is constructed from the actual chosen sections
and the unit determinants of their stalk coordinate matrices. -/
def schemeSectionFrameIso
    (b : ∀ x : X, Module.Basis ι (X.presheaf.stalk x) (H.presheaf.stalk x))
    (h : ∀ x : X, IsUnit (schemeSectionStalkMatrix H ι s x (b x)).det) :
    schemeTrivialBundle X ι ≅ H := by
  letI := (schemeSectionFrameMap_isIso_iff_unit_det H ι s b).mpr h
  exact asIso (schemeSectionFrameMap H ι s)

/-- The constructed global trivialization sends each standard section to
the corresponding prescribed global section. -/
theorem schemeSectionFrameIso_standard
    (b : ∀ x : X, Module.Basis ι (X.presheaf.stalk x) (H.presheaf.stalk x))
    (h : ∀ x : X, IsUnit (schemeSectionStalkMatrix H ι s x (b x)).det) (i : ι) :
    (schemeSectionFrameIso H ι s b h).hom.app ⊤ (schemeTrivialSection X ι ⊤ i) = s i := by
  change (schemeSectionFrameMap H ι s).val.app (op ⊤) (schemeTrivialSection X ι ⊤ i) = s i
  rw [schemeSectionFrameMap_standard]
  exact ConcreteCategory.congr_hom (H.presheaf.map_id (op ⊤)) (s i)

/-- Equivalently, the actual section-family map is an isomorphism if its
determinant is nonzero in the residue field at every scheme point. -/
theorem schemeSectionFrameMap_isIso_iff_residue_det
    (b : ∀ x : X, Module.Basis ι (X.presheaf.stalk x) (H.presheaf.stalk x)) :
    IsIso (schemeSectionFrameMap H ι s) ↔
      ∀ x : X, ((schemeSectionStalkMatrix H ι s x (b x)).map
        (IsLocalRing.residue (X.presheaf.stalk x))).det ≠ 0 := by
  rw [schemeSectionFrameMap_isIso_iff_unit_det H ι s b]
  apply forall_congr'
  intro x
  change IsUnit (frameCoordinateMatrix (b x) _).det ↔ _
  rw [frameCoordinateMatrix_isUnit_det_iff]
  exact (frameCoordinateMatrix_residue_det_ne_zero_iff (b x) _).symm

end Normalizer

namespace Normalizer
open CategoryTheory AlgebraicGeometry

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k)) [UniversallyClosed f]
  (G : X.Modules) (I : G.Submodule) (ι : Type u) [Fintype ι] [DecidableEq ι]

/-- Pointwise unit determinants of actual subsheaf section germs imply
preservation of dimension under actual generic tensor evaluation. The
global trivialization and independent frame are both constructed. -/
theorem properSubsheaf_evaluation_finrank_of_unit_det
    (s : ι → Γ((I.toSheafOfModules : X.Modules), ⊤))
    (b : ∀ x : X, Module.Basis ι (X.presheaf.stalk x)
      ((Scheme.Modules.presheaf I.toSheafOfModules).stalk x))
    (h : ∀ x : X, IsUnit (schemeSectionStalkMatrix I.toSheafOfModules ι s x (b x)).det) :
    letI := schemeGlobalSectionsModuleOfMorphism f I.toSheafOfModules
    letI := schemeFunctionFieldAlgebra f
    letI := schemeGenericSectionsModule f G
    letI := schemeGenericSectionsScalarTower f G
    ∀ W : Submodule k Γ((I.toSheafOfModules : X.Modules), ⊤),
      Module.finrank X.functionField
        (((schemeSubsheafGenericEvaluation f G I).comp W.subtype).liftBaseChange X.functionField).range =
          Module.finrank k W :=
  properTrivializedSubsheaf_evaluation_finrank f G I ι
    (schemeSectionFrameIso I.toSheafOfModules ι s b h)

end Normalizer
