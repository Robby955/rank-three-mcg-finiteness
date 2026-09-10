import Normalizer.ProperGlobalCharacter

/-! Actual generic evaluation and character compatibility on integral
schemes. Evaluation is the germ map at the scheme's generic point.
No injectivity or dimension assertion for global sections is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

/-- The inclusion of base-field constants in the actual function field. -/
def schemeFunctionFieldConstantMap (f : X ⟶ Spec (.of k)) : k →+* X.functionField :=
  (X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp (schemeConstantMap f)

/-- The base-field algebra structure on the actual function field. -/
@[instance_reducible]
def schemeFunctionFieldAlgebra (f : X ⟶ Spec (.of k)) : Algebra k X.functionField :=
  (schemeFunctionFieldConstantMap f).toAlgebra

/-- Restriction of scalars on the actual generic fibre. -/
@[instance_reducible]
def schemeGenericSectionsModule (f : X ⟶ Spec (.of k)) (Q : X.Modules) :
    Module k (Q.presheaf.stalk (genericPoint X)) :=
  Module.compHom (Q.presheaf.stalk (genericPoint X)) (schemeFunctionFieldConstantMap f)

/-- The actual generic evaluation of global sections, linear over the
base field via the scheme's structure morphism. -/
def schemeGenericEvaluation (f : X ⟶ Spec (.of k)) (Q : X.Modules) :
    letI := schemeGlobalSectionsModuleOfMorphism f Q
    letI := schemeGenericSectionsModule f Q
    Γ(Q, ⊤) →ₗ[k] Q.presheaf.stalk (genericPoint X) := by
  letI := schemeGlobalSectionsModuleOfMorphism f Q
  letI := schemeGenericSectionsModule f Q
  exact {
    toFun := Q.presheaf.germ ⊤ (genericPoint X) trivial
    map_add' := by intro s t; exact map_add _ _ _
    map_smul' := by
      intro a s
      change Q.presheaf.germ ⊤ (genericPoint X) trivial (schemeConstantMap f a • s) =
        schemeFunctionFieldConstantMap f a • Q.presheaf.germ ⊤ (genericPoint X) trivial s
      exact schemeModule_germ_smul Q (genericPoint X) ⊤ trivial (schemeConstantMap f a) s }

/-- Generic evaluation is natural for actual sheaf morphisms. -/
theorem schemeGenericEvaluation_natural (f : X ⟶ Spec (.of k))
    {Q H : X.Modules} (q : Q ⟶ H) (s : Γ(Q, ⊤)) :
    schemeModuleStalkMap q (genericPoint X) (schemeGenericEvaluation f Q s) =
      schemeGenericEvaluation f H (q.app ⊤ s) :=
  schemeModuleStalkMap_germ q (genericPoint X) ⊤ trivial s

/-- A global section killed by a sheaf map evaluates in the actual
kernel of its generic stalk map. This constructs the required membership. -/
theorem schemeGenericEvaluation_mem_kernel (f : X ⟶ Spec (.of k))
    {Q H : X.Modules} (q : Q ⟶ H) (s : Γ(Q, ⊤)) (hs : q.app ⊤ s = 0) :
    schemeGenericEvaluation f Q s ∈ (schemeModuleStalkMap q (genericPoint X)).ker := by
  change schemeModuleStalkMap q (genericPoint X) (schemeGenericEvaluation f Q s) = 0
  rw [schemeGenericEvaluation_natural, hs, map_zero]

/-- The actual function-field-valued generic character induced by the
sheaf character. -/
def schemeGenericCharacter {Q : X.Modules}
    (ψ : Q ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Q.presheaf.stalk (genericPoint X) →ₗ[X.functionField] X.functionField :=
  schemeStalkFunctional ψ (genericPoint X)

/-- Geometric constancy proves compatibility of the actual global scalar
character with the actual generic functional and actual evaluation map. -/
theorem properGenericCharacter_compat [IsAlgClosed k]
    (f : X ⟶ Spec (.of k)) [UniversallyClosed f] {Q : X.Modules}
    (ψ : Q ⟶ SheafOfModules.unit X.ringCatSheaf) (s : Γ(Q, ⊤)) :
    schemeGenericCharacter ψ (schemeGenericEvaluation f Q s) =
      schemeFunctionFieldConstantMap f (properGlobalCharacter f ψ s) :=
  properGlobalCharacter_germ f ψ s (genericPoint X)

end Normalizer
