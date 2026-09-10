import Normalizer.SchemeGenericEvaluation
import Normalizer.TrivializedCharacter

/-! The global scalar character for the actual line-normalizer quotient
sheaf on a proper integral scheme. The sheaf character is constructed from
line trivializations and the action operators, not supplied as an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [UniversallyClosed f]
  (E : X.Modules) (I : E.Submodule)
  (action : ∀ V, E.val.obj V → E.val.obj V →ₗ[X.ringCatSheaf.obj.obj V] E.val.obj V)
  (action_res : ∀ {V W} (g : V ⟶ W) (m x : E.val.obj V),
    E.val.map g (action V m x) = action W (E.val.map g m) (E.val.map g x))
  (action_smul_right : ∀ V (a : X.ringCatSheaf.obj.obj V) (m x : E.val.obj V),
    action V (a • m) x = a • action V m x)
  {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
  (triv : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅
    I.toSheafOfModules.over (U i))
  (alternating : ∀ V (z : E.val.obj V), action V z z = 0)

/-- The actual line-normalizer quotient sheaf, viewed as a scheme module.
Abelianness of the line follows from alternation and genuine local frames. -/
abbrev schemeLineNormalizerQuotient : X.Modules :=
  normalizerQuotientSheaf E I action action_res
    (lineSubsheaf_abelian_of_trivializations E I action action_res action_smul_right
      U hcover triv alternating)

local notation "Qₙ" => schemeLineNormalizerQuotient E I action action_res action_smul_right
  U hcover triv alternating

/-- The actual sheaf action character from the local line frames. The
commutativity used in its construction comes from the scheme structure. -/
def schemeNormalizerCharacter : Qₙ ⟶ SheafOfModules.unit X.ringCatSheaf :=
  lineQuotientCharacter E I action action_res (fun V a b => @mul_comm (X.presheaf.obj V) _ a b)
    action_smul_right U hcover triv alternating

local notation "ψₙ" => schemeNormalizerCharacter E I action action_res action_smul_right
  U hcover triv alternating

/-- The scalar-valued global normalizer character, with constancy derived
from universal closedness over the algebraically closed base field. -/
def properNormalizerScalar :
    letI := schemeGlobalSectionsModuleOfMorphism f Qₙ
    Γ(Qₙ, ⊤) →ₗ[k] k :=
  properGlobalCharacter f ψₙ

/-- The constructed global normalizer scalar agrees with its induced
generic sheaf functional on actual generic evaluation of every section.
Identification with the matrix normalizer quotient is a separate step. -/
theorem properNormalizerScalar_generic (s : Γ(Qₙ, ⊤)) :
    schemeGenericCharacter ψₙ (schemeGenericEvaluation f Qₙ s) =
      schemeFunctionFieldConstantMap f
        (properNormalizerScalar f E I action action_res action_smul_right U hcover triv alternating s) :=
  properGenericCharacter_compat f ψₙ s

end Normalizer
