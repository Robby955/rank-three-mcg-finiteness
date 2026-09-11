import Normalizer.AffineSheafLifting
import Normalizer.ModuleAbelianPushforward
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! Actual affine degree-one sheaf-cohomology vanishing. The cohomology is
mathlib's Ext-defined cohomology in the category of all abelian sheaves. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
variable {R : CommRingCat.{u}}

/-- A localizing R-module sheaf on Spec R has vanishing actual H¹. This
applies the proved local-to-global lifting theorem to its canonical embedding
in an injective abelian sheaf, then uses the actual Ext exact sequence. -/
theorem localizingSheaf_H1_subsingleton
    (F : TopCat.Sheaf (ModuleCat.{u} R) (PrimeSpectrum.Top R))
    (hF : IsLocalizing F) :
    Subsingleton (Sheaf.H (affineModuleAbelianSheaf F) 1) := by
  let A := affineModuleAbelianSheaf F
  let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι A))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  have hsurj := localizingSheaf_extension_globalSections_surjective F hF
    (Injective.ι A) (cokernel.π (Injective.ι A)) (cokernel.condition _) hS
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS x
    (Abelian.Ext.eq_zero_of_injective _) (rfl : 0 + 1 = 1)
  obtain ⟨t, ht⟩ := hsurj (Sheaf.H.equiv₀ S.X₃ isTerminalTop y)
  let z := (Sheaf.H.equiv₀ S.X₂ isTerminalTop).symm t
  have hz : Sheaf.H.map S.g 0 z = y := by
    apply (Sheaf.H.equiv₀ S.X₃ isTerminalTop).injective
    rw [← Sheaf.H.equiv₀_naturality]
    simpa only [z, AddEquiv.apply_symm_apply] using ht
  rw [← hy, ← hz, Sheaf.H.map_apply, Abelian.Ext.comp_assoc_of_second_deg_zero,
    hS.comp_extClass, Abelian.Ext.comp_zero]

/-- For any commutative ring R and any R-module M, the actual associated
sheaf has H¹(Spec R, M tilde) = 0. There are no noetherian, finite-presentation,
characteristic, or acyclicity hypotheses. -/
theorem tilde_H1_subsingleton (M : ModuleCat.{u} R) :
    Subsingleton (Sheaf.H ((schemeModulesToAbelianSheaves (Spec R)).obj (tilde M)) 1) := by
  change Subsingleton (Sheaf.H
    (affineModuleAbelianSheaf (modulesSpecToSheaf.obj (tilde M))) 1)
  exact localizingSheaf_H1_subsingleton _ (isLocalizing_tilde M)

/-- Every element of the actual first cohomology group of an associated
module sheaf on Spec R is zero. -/
theorem tilde_H1_eq_zero (M : ModuleCat.{u} R)
    (x : Sheaf.H ((schemeModulesToAbelianSheaves (Spec R)).obj (tilde M)) 1) : x = 0 := by
  have := tilde_H1_subsingleton M
  exact Subsingleton.elim _ _

/-- Every actual quasicoherent module sheaf on Spec R has vanishing H¹.
The localization property is supplied by mathlib's proved quasicoherence
criterion, rather than taken as a separate premise. -/
theorem quasicoherent_Spec_H1_subsingleton (F : (Spec R).Modules)
    [F.IsQuasicoherent] :
    Subsingleton (Sheaf.H ((schemeModulesToAbelianSheaves (Spec R)).obj F) 1) := by
  change Subsingleton (Sheaf.H (affineModuleAbelianSheaf (modulesSpecToSheaf.obj F)) 1)
  exact localizingSheaf_H1_subsingleton _
    ((isIso_fromTildeΓ_iff_isLocalizing F).mp inferInstance)

end Normalizer
