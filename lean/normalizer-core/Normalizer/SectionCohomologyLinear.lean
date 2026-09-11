import Normalizer.ModuleSheafCohomologyScalars
import Normalizer.SectionCohomologyExact

/-! Base-field linearity of the actual connecting map of the section sequence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry Abelian
universe u v
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of k))

/-- The extension class of an actual short exact module-sheaf sequence commutes
with the actual scalar endomorphisms on its underlying abelian sheaves. -/
theorem schemeModuleShortExact_extClass_scalar
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (a : k) :
    (schemeModulesToAbelianSheaves_shortExact S hS).extClass.comp
      (Ext.mk₀ (schemeModuleScalarEnd p S.X₁ a)) (add_zero 1) =
    (Ext.mk₀ (schemeModuleScalarEnd p S.X₃ a)).comp
      (schemeModulesToAbelianSheaves_shortExact S hS).extClass (zero_add 1) := by
  have := schemeModulesToAbelianSheaves_additive X
  let q : S.map (schemeModulesToAbelianSheaves X) ⟶
      S.map (schemeModulesToAbelianSheaves X) := {
    τ₁ := schemeModuleScalarEnd p S.X₁ a
    τ₂ := schemeModuleScalarEnd p S.X₂ a
    τ₃ := schemeModuleScalarEnd p S.X₃ a
    comm₁₂ := schemeModuleScalarEnd_naturality p S.f a
    comm₂₃ := schemeModuleScalarEnd_naturality p S.g a }
  exact ShortComplex.ShortExact.extClass_naturality
    (schemeModulesToAbelianSheaves_shortExact S hS)
    (schemeModulesToAbelianSheaves_shortExact S hS) q

variable (L : X.Modules) (s : Γ(L, ⊤))
  {ι : Type v} [Finite ι] (U : ι → X.Opens) [∀ a, QuasiCompact (U a).ι]
  (e : ∀ a, (SheafOfModules.unit X.ringCatSheaf).over (U a) ≅ L.over (U a))
  (hU : iSup U = ⊤)

/-- The actual connecting homomorphism of the specified-section sequence is
linear over the base field, by naturality of its actual extension class. -/
def schemeSectionLineCohomologyδLinear [IsIntegral X] (hs : s ≠ 0) :
    letI := schemeModuleCohomologyModule p (schemeSectionLineRestrictionSheaf L s U e hU) 0
    letI := schemeModuleCohomologyModule p (SheafOfModules.unit X.ringCatSheaf) 1
    Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (schemeSectionLineRestrictionSheaf L s U e hU)) 0 →ₗ[k]
      Sheaf.H ((schemeModulesToAbelianSheaves X).obj
        (SheafOfModules.unit X.ringCatSheaf)) 1 := by
  letI := schemeModuleCohomologyModule p (schemeSectionLineRestrictionSheaf L s U e hU) 0
  letI := schemeModuleCohomologyModule p (SheafOfModules.unit X.ringCatSheaf) 1
  exact {
    __ := schemeSectionLineCohomologyδ L s U e hU hs
    map_smul' := fun a x => by
      change (x.comp (Ext.mk₀ (schemeModuleScalarEnd p _ a)) (add_zero 0)).comp
        (schemeSectionLineAbelianComplex_shortExact L s U e hU hs).extClass
          (zero_add 1) =
        (x.comp (schemeSectionLineAbelianComplex_shortExact L s U e hU hs).extClass
          (zero_add 1)).comp (Ext.mk₀ (schemeModuleScalarEnd p _ a)) (add_zero 1)
      rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero]
      exact congrArg (fun z => x.comp z (zero_add 1))
        (schemeModuleShortExact_extClass_scalar p (schemeSectionLineComplex L s U e hU)
          (schemeSectionLineComplex_shortExact L s U e hU hs) a).symm }

end Normalizer
