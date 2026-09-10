import Normalizer.ProperTrivialEvaluation

/-! Actual evaluation of global sections of a trivialized subsheaf into
the ambient generic fibre, with independence derived from sheaf data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) (G : X.Modules) (I : G.Submodule)

/-- Actual generic evaluation of subsheaf sections into the ambient
generic fibre, induced by the actual inclusion. -/
def schemeSubsheafGenericEvaluation :
    letI := schemeGlobalSectionsModuleOfMorphism f I.toSheafOfModules
    letI := schemeGenericSectionsModule f G
    Γ((I.toSheafOfModules : X.Modules), ⊤) →ₗ[k] G.presheaf.stalk (genericPoint X) := by
  letI := schemeGlobalSectionsModuleOfMorphism f I.toSheafOfModules
  letI := schemeFunctionFieldAlgebra f
  letI := schemeGenericSectionsModule f I.toSheafOfModules
  letI := schemeGenericSectionsModule f G
  letI := schemeGenericSectionsScalarTower f I.toSheafOfModules
  letI := schemeGenericSectionsScalarTower f G
  exact ((schemeModuleStalkMap I.ι (genericPoint X)).restrictScalars k).comp
    (schemeGenericEvaluation f I.toSheafOfModules)

/-- The constructed evaluation is exactly the ambient germ of the
underlying global section. -/
theorem schemeSubsheafGenericEvaluation_apply
    (s : Γ((I.toSheafOfModules : X.Modules), ⊤)) :
    schemeSubsheafGenericEvaluation f G I s =
      G.presheaf.germ ⊤ (genericPoint X) trivial s.val :=
  schemeModuleStalkMap_germ I.ι (genericPoint X) ⊤ trivial s

variable [IsAlgClosed k] [UniversallyClosed f]
  (ι : Type u) [Fintype ι] [DecidableEq ι]
  (t : schemeTrivialBundle X ι ≅ I.toSheafOfModules)

include t in
/-- A genuine global trivialization of the subsheaf makes its actual
tensor evaluation into the ambient generic fibre injective. Coordinates,
their compatibility, and the independent frame are all constructed. -/
theorem properTrivializedSubsheaf_tensor_injective :
    letI := schemeGlobalSectionsModuleOfMorphism f I.toSheafOfModules
    letI := schemeFunctionFieldAlgebra f
    letI := schemeGenericSectionsModule f G
    letI := schemeGenericSectionsScalarTower f G
    Function.Injective ((schemeSubsheafGenericEvaluation f G I).liftBaseChange X.functionField) := by
  let := schemeGlobalSectionsModuleOfMorphism f I.toSheafOfModules
  let := schemeFunctionFieldAlgebra f
  let := schemeGenericSectionsModule f G
  let := schemeGenericSectionsScalarTower f G
  let j := (schemeModuleStalkMap I.ι (genericPoint X)).comp
    (properTrivializedGenericFrame ι I.toSheafOfModules t)
  apply evaluation_lift_injective_of_frame (schemeSubsheafGenericEvaluation f G I)
    (properTrivializedCoordinates f ι I.toSheafOfModules t) j
    (properTrivializedCoordinates_injective f ι I.toSheafOfModules t)
  · exact (schemeSubmoduleStalk_injective G I (genericPoint X)).comp
      (properTrivializedGenericFrame_injective ι I.toSheafOfModules t)
  · intro s
    exact congrArg (schemeModuleStalkMap I.ι (genericPoint X))
      (properTrivializedEvaluation_frame f ι I.toSheafOfModules t s)

include t in
/-- Every subspace of actual global subsheaf sections preserves its
dimension under canonical tensor evaluation in the ambient generic fibre.
The global sheaf trivialization is the geometric input. -/
theorem properTrivializedSubsheaf_evaluation_finrank :
    letI := schemeGlobalSectionsModuleOfMorphism f I.toSheafOfModules
    letI := schemeFunctionFieldAlgebra f
    letI := schemeGenericSectionsModule f G
    letI := schemeGenericSectionsScalarTower f G
    ∀ W : Submodule k Γ((I.toSheafOfModules : X.Modules), ⊤),
      Module.finrank X.functionField
        (((schemeSubsheafGenericEvaluation f G I).comp W.subtype).liftBaseChange X.functionField).range =
          Module.finrank k W := by
  let := schemeGlobalSectionsModuleOfMorphism f I.toSheafOfModules
  let := schemeFunctionFieldAlgebra f
  let := schemeGenericSectionsModule f G
  let := schemeGenericSectionsScalarTower f G
  intro W
  let j := (schemeModuleStalkMap I.ι (genericPoint X)).comp
    (properTrivializedGenericFrame ι I.toSheafOfModules t)
  apply evaluation_range_finrank_of_frame
    ((schemeSubsheafGenericEvaluation f G I).comp W.subtype)
    ((properTrivializedCoordinates f ι I.toSheafOfModules t).comp W.subtype) j
  · exact (properTrivializedCoordinates_injective f ι I.toSheafOfModules t).comp W.subtype_injective
  · exact (schemeSubmoduleStalk_injective G I (genericPoint X)).comp
      (properTrivializedGenericFrame_injective ι I.toSheafOfModules t)
  · intro s
    exact congrArg (schemeModuleStalkMap I.ι (genericPoint X))
      (properTrivializedEvaluation_frame f ι I.toSheafOfModules t s.val)

end Normalizer
