import Normalizer.FiniteChartGeometry
import Normalizer.ModulePushforwardSections

/-! Compatibility of the actual Proj coordinate constants with the original
structure morphism, and their pullback to actual chart sections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (k : Type u) [Field k]

/-- The structure morphism on a standard chart is induced by the actual constant-coefficient map. -/
theorem projectiveLineChart_structure (i : Fin 2) :
    (projectiveLineChart k i).ι ≫ projectiveLineToSpec k =
      (projectiveLineChartIsoSpec k i).hom ≫ Spec.map (CommRingCat.ofHom
        ((fromZeroRingHom _ _).comp (projectiveLineZeroConstants k))) := by
  apply (cancel_epi (projectiveLineChartIsoSpec k i).inv).mp
  rw [← Category.assoc, Iso.inv_hom_id_assoc]
  change Proj.awayι _ _ _ _ ≫ projectiveLineToSpec k = _
  rw [projectiveLineToSpec, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- Actual base-field constants on a chart are the constants of its homogeneous-localization ring. -/
theorem projectiveLineChart_constant (i : Fin 2) (a : k) :
    schemeConstantAt (projectiveLineToSpec k) (projectiveLineChart k i) a =
      (projectiveLineChartSectionsEquiv k i).symm
        (projectiveChartFromPolynomial k i (Polynomial.C a)) := by
  have h := congrArg (fun f : (projectiveLineChart k i).toScheme ⟶ Spec (.of k) =>
    (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) (projectiveLineChart_structure k i)
  simp only [Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality] at h
  have h' := congrArg (fun f => f a) h
  change (projectiveLineChart k i).topIso.inv
    (schemeConstantAt (projectiveLineToSpec k) (projectiveLineChart k i) a) = _ at h'
  change _ = ((projectiveLineChartIsoSpec k i).hom.appTop)
    ((Scheme.ΓSpecIso _).inv
      (((fromZeroRingHom _ _).comp (projectiveLineZeroConstants k)) a)) at h'
  change _ = (Proj.basicOpenToSpec _ _).app ⊤ _ at h'
  rw [Proj.basicOpenToSpec_app_top] at h'
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] at h'
  apply ((projectiveLineChart k i).topIso.symm.commRingCatIsoToRingEquiv.injective)
  simp only [projectiveChartFromPolynomial, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    RingHom.comp_apply]
  exact h'

/-- In actual polynomial chart coordinates, constants from the structure morphism are coefficient polynomials. -/
theorem projectiveLineChart_polynomial_constant (i : Fin 2) (a : k) :
    projectiveLineChartSectionsPolynomialEquiv k i
      (schemeConstantAt (projectiveLineToSpec k) (projectiveLineChart k i) a) = Polynomial.C a := by
  rw [projectiveLineChart_constant]
  change projectiveChartToPolynomial k i
    (projectiveLineChartSectionsEquiv k i ((projectiveLineChartSectionsEquiv k i).symm _)) = _
  rw [RingEquiv.apply_symm_apply, projectiveChartToPolynomial_from_C]

variable {k} {X Y : Scheme.{u}}

/-- Base constants on actual inverse-image opens agree with pullback of the original constants. -/
theorem schemeConstantAt_comp (f : X ⟶ Y) (p : Y ⟶ Spec (.of k))
    (U : Y.Opens) (a : k) :
    schemeConstantAt (f ≫ p) (f ⁻¹ᵁ U) a = f.app U (schemeConstantAt p U a) := by
  change (X.presheaf.map (homOfLE le_top).op) (f.appTop (schemeConstantMap p a)) = _
  exact (congrArg (fun g => g (schemeConstantMap p a))
    (f.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)).symm

end Normalizer
