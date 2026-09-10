import Normalizer.NormalizerBilinear
import Normalizer.GenericBoundary

/-! The generic boundary-law subspace for the actual normalizer quotient.
The trivial-sheaf inclusion and the identity on its global generators are
explicit inputs. Its generic dimension, bracket, and character are derived. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Opposite AlgebraicGeometry
universe u
variable {X : Scheme.{u}} (E : X.Modules)
  (I : (E : SheafOfModules X.ringCatSheaf).Submodule)
  (action : ∀ V, E.val.obj V → E.val.obj V →ₗ[X.ringCatSheaf.obj.obj V] E.val.obj V)
  (action_res : ∀ {V W} (f : V ⟶ W) (m x : E.val.obj V),
    E.val.map f (action V m x) = action W (E.val.map f m) (E.val.map f x))
  (habelian : ∀ V (x m : E.val.obj V), x ∈ I.obj V → m ∈ I.obj V →
    action V m x = 0)
  (jacobi : ∀ V (x y m : E.val.obj V),
    action V m (action V y x) =
      action V (action V m y) x - action V (action V m x) y)
  (skew : ∀ V (x y : E.val.obj V), action V y x = -action V x y)

private theorem sectionRing_comm (V) (a b : X.ringCatSheaf.obj.obj V) : a * b = b * a := by
  change Γ(X, V.unop) at a b
  exact mul_comm a b

include skew in
private theorem action_smul (V) (r : X.ringCatSheaf.obj.obj V) (m x : E.val.obj V) :
    action V (r • m) x = r • action V m x := by
  rw [skew V x (r • m), map_smul, skew V m x]
  simp

private abbrev quotientModule : X.Modules :=
  normalizerQuotientSheaf E I action action_res habelian
local notation "K" => quotientModule E I action action_res habelian

variable {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
  (triv : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅
    I.toSheafOfModules.over (U i))

private abbrev quotientCharacter :=
  quotientCharacterOfTrivializations E I action action_res
    sectionRing_comm (action_smul E action skew) habelian U hcover triv
local notation "χ" => quotientCharacter E I action action_res habelian skew U hcover triv

variable [IsIntegral X]

/-- On the actual normalizer quotient, a monomorphism from a finite free
sheaf and the global boundary identity produce a subspace of the same
dimension in the actual generic stalk. The bracket and character are the
ones constructed from the normalizer and genuine line trivializations. -/
theorem normalizerQuotient_generic_boundaryLaw (J : Type u) [Fintype J]
    (f : (SheafOfModules.free (R := X.ringCatSheaf) J : X.Modules) ⟶ K) [Mono f]
    (hlaw : ∀ i j,
      normalizerQuotientBracket E I action action_res habelian jacobi skew ⊤
        (f.val.app (op ⊤) (freeSheafGenerator i)) (f.val.app (op ⊤) (freeSheafGenerator j)) =
      schemeGlobalCharacter K χ (f.val.app (op ⊤) (freeSheafGenerator i)) •
        f.val.app (op ⊤) (freeSheafGenerator j) -
      schemeGlobalCharacter K χ (f.val.app (op ⊤) (freeSheafGenerator j)) •
        f.val.app (op ⊤) (freeSheafGenerator i)) :
    ∃ W : Submodule X.functionField ((K).presheaf.stalk (genericPoint X)),
      Module.finrank X.functionField W = Fintype.card J ∧
      BoundaryLaw W
        (fun a b => normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew
          (genericPoint X) a b)
        (schemeModuleStalkCharacter K χ (genericPoint X)) :=
  freeSheaf_mono_generic_boundaryLaw K
    (normalizerQuotientSectionBilinear E I action action_res habelian jacobi skew)
    (normalizerQuotientSectionBilinear_restrict E I action action_res habelian jacobi skew)
    χ J f hlaw

/-- The constructed actual normalizer-quotient boundary-law subspace retains
its dimension after arbitrary field extension, including an algebraic closure.
The extended bracket and character are the genuine tensor base changes. -/
theorem normalizerQuotient_generic_boundaryLaw_baseChange
    (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
    (J : Type u) [Fintype J]
    (f : (SheafOfModules.free (R := X.ringCatSheaf) J : X.Modules) ⟶ K) [Mono f]
    (hlaw : ∀ i j,
      normalizerQuotientBracket E I action action_res habelian jacobi skew ⊤
        (f.val.app (op ⊤) (freeSheafGenerator i)) (f.val.app (op ⊤) (freeSheafGenerator j)) =
      schemeGlobalCharacter K χ (f.val.app (op ⊤) (freeSheafGenerator i)) •
        f.val.app (op ⊤) (freeSheafGenerator j) -
      schemeGlobalCharacter K χ (f.val.app (op ⊤) (freeSheafGenerator j)) •
        f.val.app (op ⊤) (freeSheafGenerator i)) :
    ∃ W : Submodule Ω (TensorProduct X.functionField Ω ((K).presheaf.stalk (genericPoint X))),
      Module.finrank Ω W = Fintype.card J ∧
      BoundaryLaw W
        (fun a b => LinearMap.BilinMap.baseChange Ω
          (normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew
            (genericPoint X)) a b)
        (boundaryCharacterBaseChange (schemeModuleStalkCharacter K χ (genericPoint X))) :=
  freeSheaf_mono_generic_boundaryLaw_baseChange K
    (normalizerQuotientSectionBilinear E I action action_res habelian jacobi skew)
    (normalizerQuotientSectionBilinear_restrict E I action action_res habelian jacobi skew)
    χ Ω J f hlaw

end Normalizer
