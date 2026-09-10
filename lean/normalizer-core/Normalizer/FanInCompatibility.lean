import Normalizer.GenericBoundary
import Normalizer.SchemeGenericEvaluation

/-! Comparison of the independently constructed scalar and stalk characters.
The weaker universal-closedness interface is retained. Under properness,
both constructions give the same actual maps and values. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite
universe u

/-- The two constants interfaces use exactly the same structure morphism. -/
theorem schemeConstants_eq_constantMap (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (CommRingCat.of k)) :
    schemeConstants k s = schemeConstantMap s := rfl

/-- The two generic constants interfaces are the same ring map. -/
theorem schemeFunctionFieldConstants_eq_constantMap (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] (s : X ⟶ Spec (CommRingCat.of k)) :
    schemeFunctionFieldConstants k s = schemeFunctionFieldConstantMap s := rfl

/-- The independently constructed global scalar characters agree by
injectivity of the actual constants map. -/
theorem properScalarCharacter_eq_globalCharacter (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X] (s : X ⟶ Spec (CommRingCat.of k)) [IsProper s]
    (K : X.Modules) (χ : K ⟶ SheafOfModules.unit X.ringCatSheaf) (t : Γ(K, ⊤)) :
    properSchemeScalarCharacter k s K χ t = properGlobalCharacter s χ t := by
  apply (properScheme_constants_bijective k s).injective
  rw [properSchemeScalarCharacter_spec, schemeConstants_eq_constantMap,
    properGlobalCharacter_spec]
  rfl

/-- The character constructed through the unit-stalk equivalence equals
the character constructed directly by a stalk cocone, on every element. -/
theorem schemeModuleStalkCharacter_eq_stalkFunctional {X : Scheme.{u}}
    (K : X.Modules) (χ : K ⟶ SheafOfModules.unit X.ringCatSheaf) (x : X) :
    schemeModuleStalkCharacter K χ x = schemeStalkFunctional χ x := by
  ext t
  obtain ⟨U, hx, a, rfl⟩ := K.presheaf.exists_germ_eq t
  rw [schemeModuleStalkCharacter_germ, schemeStalkFunctional_germ]
  rfl

end Normalizer
