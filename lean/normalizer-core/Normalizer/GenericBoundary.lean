import Normalizer.ScalarCharacter
import Normalizer.StalkBracket
import Normalizer.GenericSections
import Normalizer.BoundaryBaseChange

/-! The boundary law and its dimension in the actual generic fibre. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite
universe u

/-- The base-field embedding into the actual function field induced by
the structure morphism and the actual generic germ. -/
def schemeFunctionFieldConstants (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] (s : X ⟶ Spec (CommRingCat.of k)) :
    k →+* X.functionField :=
  (X.presheaf.germ ⊤ (genericPoint X) (by trivial)).hom.comp (schemeConstants k s)

/-- The actual generic character of a global section is the image of
the proper-scheme scalar character under the canonical field embedding. -/
theorem generic_character_scalar (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of k)) [IsProper s]
    (K : X.Modules) (χ : K ⟶ SheafOfModules.unit X.ringCatSheaf) (x : Γ(K, ⊤)) :
    schemeModuleStalkCharacter K χ (genericPoint X)
      (K.presheaf.germ ⊤ (genericPoint X) (by trivial) x) =
        schemeFunctionFieldConstants k s (properSchemeScalarCharacter k s K χ x) := by
  rw [schemeModuleStalkCharacter_germ]
  change X.presheaf.germ ⊤ (genericPoint X) (by trivial) (χ.app ⊤ x) =
    X.presheaf.germ ⊤ (genericPoint X) (by trivial)
      (schemeConstants k s (properSchemeScalarCharacter k s K χ x))
  rw [properSchemeScalarCharacter_spec]

variable {X : Scheme.{u}} [IsIntegral X] (K : X.Modules)
  (B : ∀ U : X.Opens, Γ(K, U) →ₗ[Γ(X, U)] Γ(K, U) →ₗ[Γ(X, U)] Γ(K, U))
  (hB : ∀ (U V : X.Opens) (h : U ≤ V) (s t : Γ(K, V)),
    K.presheaf.map (homOfLE h).op (B V s t) =
      B U (K.presheaf.map (homOfLE h).op s) (K.presheaf.map (homOfLE h).op t))
  (χ : K ⟶ SheafOfModules.unit X.ringCatSheaf)

/-- A boundary identity on global generators holds on their full span in
the actual generic stalk. Both the bracket and character are constructed
from actual sheaf data; no function-field boundary map is assumed. -/
theorem generic_boundaryLaw_span {I : Type u} (t : I → Γ(K, ⊤))
    (hlaw : ∀ i j, B ⊤ (t i) (t j) =
      schemeGlobalCharacter K χ (t i) • t j - schemeGlobalCharacter K χ (t j) • t i) :
    BoundaryLaw (Submodule.span X.functionField (Set.range
      (fun i ↦ K.presheaf.germ ⊤ (genericPoint X) (by trivial) (t i))))
      (fun a b ↦ schemeModuleStalkBilinear K B hB (genericPoint X) a b)
      (schemeModuleStalkCharacter K χ (genericPoint X)) := by
  apply boundaryLaw_span
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  rw [schemeModuleStalkBilinear_germ, hlaw, map_sub,
    schemeModule_germ_smul, schemeModule_germ_smul,
    schemeModuleStalkCharacter_germ, schemeModuleStalkCharacter_germ]
  rfl

/-- A true trivial-sheaf inclusion supplies both the required generic
dimension and a boundary-law subspace, once its global generators obey
the global identity. The dimension is derived from the inclusion. -/
theorem freeSheaf_mono_generic_boundaryLaw (I : Type u) [Fintype I]
    (f : (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) ⟶ K) [Mono f]
    (hlaw : ∀ i j, B ⊤ (f.val.app (op ⊤) (freeSheafGenerator i)) (f.val.app (op ⊤) (freeSheafGenerator j)) =
      schemeGlobalCharacter K χ (f.val.app (op ⊤) (freeSheafGenerator i)) • f.val.app (op ⊤) (freeSheafGenerator j) -
      schemeGlobalCharacter K χ (f.val.app (op ⊤) (freeSheafGenerator j)) • f.val.app (op ⊤) (freeSheafGenerator i)) :
    ∃ W : Submodule X.functionField (K.presheaf.stalk (genericPoint X)),
      Module.finrank X.functionField W = Fintype.card I ∧
      BoundaryLaw W (fun a b ↦ schemeModuleStalkBilinear K B hB (genericPoint X) a b)
        (schemeModuleStalkCharacter K χ (genericPoint X)) := by
  refine ⟨_, freeSheaf_mono_generic_span_finrank I f, ?_⟩
  exact generic_boundaryLaw_span K B hB χ (fun i ↦ f.val.app (op ⊤) (freeSheafGenerator i)) hlaw

/-- The same actual generic generators keep their dimension and boundary law
after any field extension, in particular passage to an algebraic closure. -/
theorem freeSheaf_mono_generic_boundaryLaw_baseChange
    (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
    (I : Type u) [Fintype I]
    (f : (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) ⟶ K) [Mono f]
    (hlaw : ∀ i j, B ⊤ (f.val.app (op ⊤) (freeSheafGenerator i))
        (f.val.app (op ⊤) (freeSheafGenerator j)) =
      schemeGlobalCharacter K χ (f.val.app (op ⊤) (freeSheafGenerator i)) •
        f.val.app (op ⊤) (freeSheafGenerator j) -
      schemeGlobalCharacter K χ (f.val.app (op ⊤) (freeSheafGenerator j)) •
        f.val.app (op ⊤) (freeSheafGenerator i)) :
    ∃ W : Submodule Ω (TensorProduct X.functionField Ω
        (K.presheaf.stalk (genericPoint X))),
      Module.finrank Ω W = Fintype.card I ∧
      BoundaryLaw W
        (fun a b ↦ LinearMap.BilinMap.baseChange Ω
          (schemeModuleStalkBilinear K B hB (genericPoint X)) a b)
        (boundaryCharacterBaseChange (schemeModuleStalkCharacter K χ (genericPoint X))) := by
  let v := fun i ↦ K.presheaf.germ ⊤ (genericPoint X) (by trivial)
    (f.val.app (op ⊤) (freeSheafGenerator i))
  refine ⟨_, baseChange_span_finrank v (freeSheaf_mono_generic_linearIndependent I f), ?_⟩
  exact boundaryLaw_baseChange_span_range v _ _
    (generic_boundaryLaw_span K B hB χ
      (fun i ↦ f.val.app (op ⊤) (freeSheafGenerator i)) hlaw)

end Normalizer
