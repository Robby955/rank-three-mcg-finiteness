import Normalizer.ProjectiveChartScalars
import Normalizer.LaurentChartModules

/-! The actual Laurent-module action on the overlap of a finite map to P1.
All ring maps are induced by the original scheme morphism and restrictions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open CategoryTheory AlgebraicGeometry LaurentPolynomial
open scoped LaurentPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (k : Type u) [Field k]

/-- The two projective coordinates have Laurent exponents 1 and -1. -/
def projectiveChartExponent (i : Fin 2) : ℤ := if i = 0 then 1 else -1

/-- Actual chart restriction expressed in the overlap's Laurent coordinates. -/
def projectiveChartLaurentHom (i : Fin 2) :
    Γ(projectiveLine k, projectiveLineChart k i) →+* k[T;T⁻¹] :=
  (projectiveLineOverlapSectionsLaurentEquiv k).toRingHom.comp
    ((projectiveLine k).presheaf.map (homOfLE (projectiveLineOverlap_le k i)).op).hom

/-- The actual Laurent-coordinate restriction is evaluation in the appropriate oriented variable. -/
theorem projectiveChartLaurentHom_eval (i : Fin 2)
    (r : Γ(projectiveLine k, projectiveLineChart k i)) :
    projectiveChartLaurentHom k i r =
      Polynomial.eval₂RingHom C (T (projectiveChartExponent i))
        (projectiveLineChartSectionsPolynomialEquiv k i r) := by
  have h₀ : (Polynomial.toLaurent : Polynomial k →+* k[T;T⁻¹]) =
      Polynomial.eval₂RingHom C (T 1) := by
    apply Polynomial.ringHom_ext <;> simp
  have h₁ : LaurentPolynomial.invert.toRingHom.comp
      (Polynomial.toLaurent : Polynomial k →+* k[T;T⁻¹]) =
        Polynomial.eval₂RingHom C (T (-1)) := by
    apply Polynomial.ringHom_ext <;> simp
  fin_cases i
  · exact (projectiveLineSections_restrict_zero k r).trans
      (congrArg (fun f : Polynomial k →+* k[T;T⁻¹] =>
        f (projectiveLineChartSectionsPolynomialEquiv k 0 r)) h₀)
  · exact (projectiveLineSections_restrict_one k r).trans
      (congrArg (fun f : Polynomial k →+* k[T;T⁻¹] =>
        f (projectiveLineChartSectionsPolynomialEquiv k 1 r)) h₁)

/-- The actual ratio restricts to its oriented Laurent monomial. -/
theorem projectiveChartLaurentHom_ratio (i : Fin 2) :
    projectiveChartLaurentHom k i (projectiveLineChartRatio k i) =
      T (projectiveChartExponent i) := by
  rw [projectiveChartLaurentHom_eval]
  have hr : projectiveLineChartSectionsPolynomialEquiv k i (projectiveLineChartRatio k i) =
      Polynomial.X := by
    change projectiveChartToPolynomial k i
      (projectiveLineChartSectionsEquiv k i ((projectiveLineChartSectionsEquiv k i).symm _)) = _
    rw [RingEquiv.apply_symm_apply, projectiveChartToPolynomial_coordinate]
  rw [hr]
  simp

/-- Constants of the actual overlap agree with coefficients in its Laurent coordinates. -/
theorem projectiveLineOverlap_laurent_constant (a : k) :
    projectiveLineOverlapSectionsLaurentEquiv k
      (schemeConstantAt (projectiveLineToSpec k) (projectiveLineOverlap k) a) = C a := by
  rw [← schemeConstantAt_restrict (projectiveLineToSpec k)
    (homOfLE (projectiveLineOverlap_le k 0)) a]
  rw [projectiveLineSections_restrict_zero, projectiveLineChart_polynomial_constant,
    Polynomial.toLaurent_C]

variable {k} {X : Scheme.{u}} (f : X ⟶ projectiveLine k)

/-- The Laurent ring acts on actual overlap sections by the original morphism's sheaf map. -/
def finiteMapLaurentHom : k[T;T⁻¹] →+* Γ(X, finiteMapOverlap f) :=
  (f.app (projectiveLineOverlap k)).hom.comp
    (projectiveLineOverlapSectionsLaurentEquiv k).symm.toRingHom

/-- The actual Laurent-ring algebra structure on overlap sections. -/
@[instance_reducible]
def finiteMapLaurentAlgebra : Algebra k[T;T⁻¹] Γ(X, finiteMapOverlap f) :=
  (finiteMapLaurentHom f).toAlgebra

/-- The actual coefficient-field algebra structure on overlap sections. -/
@[instance_reducible]
def finiteMapOverlapFieldAlgebra : Algebra k Γ(X, finiteMapOverlap f) :=
  (schemeConstantAt (f ≫ projectiveLineToSpec k) (finiteMapOverlap f)).toAlgebra

/-- Laurent constants pull back to precisely the constants of the original structure morphism. -/
theorem finiteMapLaurentHom_C (a : k) :
    finiteMapLaurentHom f (C a) =
      schemeConstantAt (f ≫ projectiveLineToSpec k) (finiteMapOverlap f) a := by
  change (f.app (projectiveLineOverlap k))
    ((projectiveLineOverlapSectionsLaurentEquiv k).symm (C a)) =
      schemeConstantAt (f ≫ projectiveLineToSpec k) (f ⁻¹ᵁ projectiveLineOverlap k) a
  rw [schemeConstantAt_comp]
  apply congrArg (fun x => (f.app (projectiveLineOverlap k)) x)
  exact (projectiveLineOverlapSectionsLaurentEquiv k).symm_apply_eq.mpr
    (projectiveLineOverlap_laurent_constant k a).symm

/-- The overlap's two actual scalar actions form a scalar tower. -/
theorem finiteMapOverlap_scalarTower :
    letI := finiteMapLaurentAlgebra f
    letI := finiteMapOverlapFieldAlgebra f
    IsScalarTower k k[T;T⁻¹] Γ(X, finiteMapOverlap f) := by
  let := finiteMapLaurentAlgebra f
  let := finiteMapOverlapFieldAlgebra f
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact (finiteMapLaurentHom_C f a).symm

/-- The actual chart-ring action on inverse-image chart sections. -/
@[instance_reducible]
def finiteMapChartAlgebra (i : Fin 2) :
    Algebra Γ(projectiveLine k, projectiveLineChart k i) Γ(X, f ⁻¹ᵁ projectiveLineChart k i) :=
  (f.app (projectiveLineChart k i)).hom.toAlgebra

/-- Actual restriction is semilinear for the actual chart-to-Laurent scalar map. -/
def finiteMapChartSemilinear (i : Fin 2) :
    letI := finiteMapChartAlgebra f i
    letI := finiteMapLaurentAlgebra f
    Γ(X, f ⁻¹ᵁ projectiveLineChart k i) →ₛₗ[projectiveChartLaurentHom k i]
      Γ(X, finiteMapOverlap f) := by
  letI := finiteMapChartAlgebra f i
  letI := finiteMapLaurentAlgebra f
  refine { (finiteMapChartRestriction f i).toAddMonoidHom with map_smul' := ?_ }
  intro r a
  change finiteMapChartRestriction f i (f.app _ r * a) =
    finiteMapLaurentHom f (projectiveChartLaurentHom k i r) * finiteMapChartRestriction f i a
  rw [map_mul]
  congr 1
  change ((X.presheaf.map (homOfLE (finiteMapOverlap_le f i)).op) (f.app _ r)) =
    (f.app (projectiveLineOverlap k))
      ((projectiveLineOverlapSectionsLaurentEquiv k).symm
        (projectiveLineOverlapSectionsLaurentEquiv k _))
  rw [RingEquiv.symm_apply_apply]
  exact (congrArg (fun g => g r)
    (f.naturality (homOfLE (projectiveLineOverlap_le k i)).op)).symm

/-- Actual localization clears denominators by a power of the corresponding Laurent monomial. -/
theorem finiteMapOverlap_clearDenominator [IsAffineHom f] (i : Fin 2) :
    letI := finiteMapChartAlgebra f i
    letI := finiteMapLaurentAlgebra f
    ∀ z : Γ(X, finiteMapOverlap f), ∃ n : ℤ,
      ∃ a : Γ(X, f ⁻¹ᵁ projectiveLineChart k i),
        (T n : k[T;T⁻¹]) • z = finiteMapChartSemilinear f i a := by
  let := finiteMapChartAlgebra f i
  let := finiteMapLaurentAlgebra f
  let := (finiteMapChartRestriction f i).toAlgebra
  have := finiteMapChartRestriction_isLocalization f i
  intro z
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj
    (f.app (projectiveLineChart k i) (projectiveLineChartRatio k i)) z
  refine ⟨(n : ℤ) * projectiveChartExponent i, a, ?_⟩
  have hr : finiteMapChartRestriction f i (f.app _ (projectiveLineChartRatio k i)) =
      finiteMapLaurentHom f (T (projectiveChartExponent i)) := by
    have h := (finiteMapChartSemilinear f i).map_smulₛₗ (projectiveLineChartRatio k i) 1
    change finiteMapChartRestriction f i (f.app _ (projectiveLineChartRatio k i) * 1) =
      finiteMapLaurentHom f (projectiveChartLaurentHom k i (projectiveLineChartRatio k i)) *
        finiteMapChartRestriction f i 1 at h
    simpa only [mul_one, map_one, projectiveChartLaurentHom_ratio] using h
  change finiteMapLaurentHom f (T _) * z = finiteMapChartRestriction f i a
  change z * (finiteMapChartRestriction f i _ ^ n) = finiteMapChartRestriction f i a at ha
  rw [hr, ← map_pow, T_pow, mul_comm] at ha
  exact ha

end Normalizer
