import Normalizer.TrivialBundleStalk
import Normalizer.EvaluationFrame
import Normalizer.NormalizerStalk

/-! Actual generic evaluation on finite trivial bundles and trivialized
subsheaves. The coordinate maps and independent generic frame are derived
from the sheaf trivialization and geometric constancy. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry Opposite

universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (.of k))

/-- The actual generic module action is compatible with the actual
constant-field algebra structure on the function field. -/
theorem schemeGenericSectionsScalarTower (Q : X.Modules) :
    letI := schemeFunctionFieldAlgebra f
    letI := schemeGenericSectionsModule f Q
    IsScalarTower k X.functionField (Q.presheaf.stalk (genericPoint X)) := by
  let := schemeFunctionFieldAlgebra f
  let := schemeGenericSectionsModule f Q
  exact IsScalarTower.of_compHom k X.functionField (Q.presheaf.stalk (genericPoint X))

/-- An actual sheaf map induces a base-field-linear map on actual global
sections, with scalar structures supplied by the scheme morphism. -/
def schemeGlobalSectionsMap {A B : X.Modules} (q : A ⟶ B) :
    letI := schemeGlobalSectionsModuleOfMorphism f A
    letI := schemeGlobalSectionsModuleOfMorphism f B
    Γ(A, ⊤) →ₗ[k] Γ(B, ⊤) := by
  letI := schemeGlobalSectionsModuleOfMorphism f A
  letI := schemeGlobalSectionsModuleOfMorphism f B
  exact {
    toFun := q.app ⊤
    map_add' := by intro a b; exact map_add (q.app ⊤).hom a b
    map_smul' := by
      intro a s
      exact Scheme.Modules.Hom.app_smul q (schemeConstantMap f a) s }

/-- An actual sheaf isomorphism induces an equivalence on global
sections over the actual base-field scalar structure. -/
def schemeGlobalSectionsIso {A B : X.Modules} (e : A ≅ B) :
    letI := schemeGlobalSectionsModuleOfMorphism f A
    letI := schemeGlobalSectionsModuleOfMorphism f B
    Γ(A, ⊤) ≃ₗ[k] Γ(B, ⊤) := by
  letI := schemeGlobalSectionsModuleOfMorphism f A
  letI := schemeGlobalSectionsModuleOfMorphism f B
  exact {
    __ := ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso e).toLinearEquiv.toAddEquiv
    map_smul' := (schemeGlobalSectionsMap f e.hom).map_smul }

variable [IsAlgClosed k] [UniversallyClosed f]
  (ι : Type u) [Fintype ι] [DecidableEq ι]

local notation "T" => schemeTrivialBundle X ι

/-- The scalar coordinates of actual global sections of the trivial
bundle, constructed by applying geometric constancy to each projection. -/
def properTrivialCoordinates :
    letI := schemeGlobalSectionsModuleOfMorphism f T
    Γ(T, ⊤) →ₗ[k] (ι → k) := by
  letI := schemeGlobalSectionsModuleOfMorphism f T
  exact LinearMap.pi (fun i => properGlobalCharacter f (schemeTrivialProjection X ι i))

omit [DecidableEq ι] in
/-- Scalar coordinates determine the actual global section. -/
theorem properTrivialCoordinates_injective : Function.Injective (properTrivialCoordinates f ι) := by
  intro s t hst
  apply (schemeTrivialCoordinates X ι ⊤).injective
  ext i
  have h := congrArg (fun a => schemeConstantMap f (a i)) hst
  change schemeConstantMap f (properGlobalCharacter f (schemeTrivialProjection X ι i) s) =
    schemeConstantMap f (properGlobalCharacter f (schemeTrivialProjection X ι i) t) at h
  rw [properGlobalCharacter_spec, properGlobalCharacter_spec] at h
  exact (schemeTrivialCoordinates_apply X ι ⊤ s i).trans
    (h.trans (schemeTrivialCoordinates_apply X ι ⊤ t i).symm)

omit [DecidableEq ι] in
/-- The actual generic coordinate tuple is the image of the constructed
global scalar tuple in the function field. -/
theorem properTrivialCoordinates_generic (s : Γ(T, ⊤)) :
    schemeTrivialStalkCoordinates X ι (genericPoint X) (schemeGenericEvaluation f T s) =
      fun i => schemeFunctionFieldConstantMap f (properTrivialCoordinates f ι s i) := by
  funext i
  exact properGenericCharacter_compat f (schemeTrivialProjection X ι i) s

/-- Actual generic evaluation has the constructed independent-frame
formula. No coordinate or compatibility map is supplied. -/
theorem properTrivialEvaluation_frame (s : Γ(T, ⊤)) :
    schemeGenericEvaluation f T s =
      schemeTrivialStalkFrame X ι (genericPoint X)
        (fun i => schemeFunctionFieldConstantMap f (properTrivialCoordinates f ι s i)) := by
  rw [← properTrivialCoordinates_generic]
  exact (schemeTrivialStalkFrame_coordinates X ι (genericPoint X) _).symm

/-- The canonical tensor extension of actual generic evaluation is
injective for the actual finite trivial bundle on this scheme. -/
theorem properTrivialEvaluation_tensor_injective :
    letI := schemeGlobalSectionsModuleOfMorphism f T
    letI := schemeFunctionFieldAlgebra f
    letI := schemeGenericSectionsModule f T
    letI := schemeGenericSectionsScalarTower f T
    Function.Injective ((schemeGenericEvaluation f T).liftBaseChange X.functionField) := by
  let := schemeGlobalSectionsModuleOfMorphism f T
  let := schemeFunctionFieldAlgebra f
  let := schemeGenericSectionsModule f T
  let := schemeGenericSectionsScalarTower f T
  exact evaluation_lift_injective_of_frame (schemeGenericEvaluation f T)
    (properTrivialCoordinates f ι) (schemeTrivialStalkFrame X ι (genericPoint X))
    (properTrivialCoordinates_injective f ι)
    (schemeTrivialStalkFrame_injective X ι (genericPoint X))
    (properTrivialEvaluation_frame f ι)

variable (H : X.Modules) (t : schemeTrivialBundle X ι ≅ H)

/-- An actual global trivialization supplies injective scalar coordinates. -/
def properTrivializedCoordinates :
    letI := schemeGlobalSectionsModuleOfMorphism f H
    Γ(H, ⊤) →ₗ[k] (ι → k) := by
  letI := schemeGlobalSectionsModuleOfMorphism f T
  letI := schemeGlobalSectionsModuleOfMorphism f H
  exact (properTrivialCoordinates f ι).comp (schemeGlobalSectionsIso f t).symm.toLinearMap

/-- The generic frame is constructed by applying the actual stalk
isomorphism to the canonical frame of the finite trivial sheaf. -/
def properTrivializedGenericFrame :
    (ι → X.functionField) →ₗ[X.functionField] H.presheaf.stalk (genericPoint X) :=
  (schemeModuleStalkIso t (genericPoint X)).toLinearMap.comp
    (schemeTrivialStalkFrame X ι (genericPoint X))

omit [DecidableEq ι] in
/-- Coordinates from a genuine global sheaf trivialization are injective. -/
theorem properTrivializedCoordinates_injective :
    Function.Injective (properTrivializedCoordinates f ι H t) :=
  (properTrivialCoordinates_injective f ι).comp (schemeGlobalSectionsIso f t).symm.injective

/-- The independent generic frame is a conclusion of the actual sheaf
trivialization. -/
theorem properTrivializedGenericFrame_injective :
    Function.Injective (properTrivializedGenericFrame ι H t) :=
  (schemeModuleStalkIso t (genericPoint X)).injective.comp
    (schemeTrivialStalkFrame_injective X ι (genericPoint X))

/-- Actual generic evaluation has the frame equation supplied by the
actual global trivialization; no compatibility equation is assumed. -/
theorem properTrivializedEvaluation_frame (s : Γ(H, ⊤)) :
    schemeGenericEvaluation f H s =
      properTrivializedGenericFrame ι H t
        (fun i => schemeFunctionFieldConstantMap f (properTrivializedCoordinates f ι H t s i)) := by
  let s₀ := (schemeGlobalSectionsIso f t).symm s
  have hs : t.hom.app ⊤ s₀ = s := (schemeGlobalSectionsIso f t).apply_symm_apply s
  have hn := schemeGenericEvaluation_natural f t.hom s₀
  rw [hs, properTrivialEvaluation_frame f ι s₀] at hn
  exact hn.symm

include t in
/-- Tensor extension of actual generic evaluation is injective for a
genuinely globally trivialized sheaf. The frame data are constructed. -/
theorem properTrivializedEvaluation_tensor_injective :
    letI := schemeGlobalSectionsModuleOfMorphism f H
    letI := schemeFunctionFieldAlgebra f
    letI := schemeGenericSectionsModule f H
    letI := schemeGenericSectionsScalarTower f H
    Function.Injective ((schemeGenericEvaluation f H).liftBaseChange X.functionField) := by
  let := schemeGlobalSectionsModuleOfMorphism f H
  let := schemeFunctionFieldAlgebra f
  let := schemeGenericSectionsModule f H
  let := schemeGenericSectionsScalarTower f H
  exact evaluation_lift_injective_of_frame (schemeGenericEvaluation f H)
    (properTrivializedCoordinates f ι H t) (properTrivializedGenericFrame ι H t)
    (properTrivializedCoordinates_injective f ι H t)
    (properTrivializedGenericFrame_injective ι H t)
    (properTrivializedEvaluation_frame f ι H t)

end Normalizer
