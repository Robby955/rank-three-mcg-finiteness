import Normalizer.FiniteMapLaurent
import Normalizer.ProjectiveLineCohomology

/-! Finiteness of actual structure-sheaf H1 for a scheme equipped with an
actual finite morphism to the projective line. No source normality,
integrality, smoothness or H1 finiteness is supplied. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open CategoryTheory AlgebraicGeometry LaurentPolynomial
open scoped LaurentPolynomial
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual section boundary on any open equal to the intersection of a two-open cover. -/
def schemeUnitBoundaryOnOverlap (p : X ⟶ Spec (.of k))
    (U V : X.Opens) (hUV : U ⊔ V = ⊤) (W : X.Opens) (hW : W = U ⊓ V) :
    letI := (schemeConstantAt p W).toAlgebra
    letI := schemeModuleCohomologyModule p (SheafOfModules.unit X.ringCatSheaf) 1
    Γ(X, W) →ₗ[k] Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (SheafOfModules.unit X.ringCatSheaf)) 1 := by
  subst W
  exact twoOpenSectionδ p U V hUV (SheafOfModules.unit X.ringCatSheaf)

/-- The actual boundary on the specified overlap is onto for an affine cover. -/
theorem schemeUnitBoundaryOnOverlap_surjective (p : X ⟶ Spec (.of k))
    (U V : X.Opens) (hUV : U ⊔ V = ⊤) (W : X.Opens) (hW : W = U ⊓ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Function.Surjective (schemeUnitBoundaryOnOverlap p U V hUV W hW) := by
  subst W
  have := schemeUnit_isLocallyFree X
  exact twoOpenSectionδ_surjective p U V hUV (SheafOfModules.unit X.ringCatSheaf) hU hV

/-- The original boundary kernel consists exactly of actual restriction differences. -/
theorem schemeUnitBoundaryOnOverlap_eq_zero_iff (p : X ⟶ Spec (.of k))
    (U V : X.Opens) (hUV : U ⊔ V = ⊤) (W : X.Opens) (hW : W = U ⊓ V)
    (z : Γ(X, W)) :
    schemeUnitBoundaryOnOverlap p U V hUV W hW z = 0 ↔
      ∃ s : Γ(X, U), ∃ t : Γ(X, V),
        X.presheaf.map (homOfLE (hW.trans_le inf_le_left)).op s -
          X.presheaf.map (homOfLE (hW.trans_le inf_le_right)).op t = z := by
  subst W
  exact twoOpenSectionδ_eq_zero_iff p U V hUV (SheafOfModules.unit X.ringCatSheaf) z

variable (f : X ⟶ projectiveLine k)

/-- The actual pulled-back overlap is the intersection used by the cohomology boundary. -/
theorem finiteMapOverlap_eq_inf :
    finiteMapOverlap f = projectiveLinePullbackChart f 0 ⊓ projectiveLinePullbackChart f 1 := by
  rw [finiteMapOverlap, projectiveLineOverlap_eq_inf, Scheme.Hom.preimage_inf]
  rfl

/-- Finite morphisms give finite actual chart modules, with the original sheaf-map action. -/
theorem finiteMapChart_module_finite [IsFinite f] (i : Fin 2) :
    letI := finiteMapChartAlgebra f i
    Module.Finite Γ(projectiveLine k, projectiveLineChart k i)
      Γ(X, f ⁻¹ᵁ projectiveLineChart k i) :=
  IsFinite.finite_app f _ (projectiveLineChart_isAffine k i)

/-- Images of actual chart generators generate the actual overlap over the Laurent ring. -/
theorem finiteMapChart_generators_span [IsAffineHom f] (i : Fin 2)
    {ι : Type*} (v : ι → Γ(X, f ⁻¹ᵁ projectiveLineChart k i)) :
    letI := finiteMapChartAlgebra f i
    letI := finiteMapLaurentAlgebra f
    Submodule.span Γ(projectiveLine k, projectiveLineChart k i) (Set.range v) = ⊤ →
      Submodule.span k[T;T⁻¹] (Set.range (finiteMapChartSemilinear f i ∘ v)) = ⊤ := by
  let := finiteMapChartAlgebra f i
  let := finiteMapLaurentAlgebra f
  intro hv
  exact laurentChart_span_eq_top k _ (finiteMapChartSemilinear f i) v hv
    (finiteMapOverlap_clearDenominator f i)

/-- Each actual chart restriction image equals the coefficient span of the corresponding
oriented Laurent powers of its restricted generators. -/
theorem finiteMapChart_restriction_image (i : Fin 2)
    {ι : Type*} (v : ι → Γ(X, f ⁻¹ᵁ projectiveLineChart k i)) :
    letI := finiteMapChartAlgebra f i
    letI := finiteMapLaurentAlgebra f
    letI := finiteMapOverlapFieldAlgebra f
    Submodule.span Γ(projectiveLine k, projectiveLineChart k i) (Set.range v) = ⊤ →
      Set.range (finiteMapChartRestriction f i) =
        (laurentSpan k (finiteMapChartSemilinear f i ∘ v)
          (Set.range (fun n : ℕ => (n : ℤ) * projectiveChartExponent i)) : Set Γ(X, finiteMapOverlap f)) := by
  let := finiteMapChartAlgebra f i
  let := finiteMapLaurentAlgebra f
  let := finiteMapOverlapFieldAlgebra f
  have := finiteMapOverlap_scalarTower f
  intro hv
  exact laurentChart_range_eq_span k _ (finiteMapChartSemilinear f i) v hv
    (projectiveLineChartSectionsPolynomialEquiv k i) (projectiveChartExponent i)
    (projectiveChartLaurentHom_eval k i)

/-- The first chart's oriented exponents are precisely the nonnegative integers. -/
theorem projectiveChartExponent_range_zero :
    Set.range (fun n : ℕ => (n : ℤ) * projectiveChartExponent 0) = Set.Ici 0 := by
  ext z
  simp only [show projectiveChartExponent 0 = 1 from rfl, mul_one, Set.mem_range, Set.mem_Ici]
  constructor
  · rintro ⟨n, rfl⟩; omega
  · intro hz; exact ⟨z.toNat, Int.toNat_of_nonneg hz⟩

/-- The second chart's oriented exponents are precisely the nonpositive integers. -/
theorem projectiveChartExponent_range_one :
    Set.range (fun n : ℕ => (n : ℤ) * projectiveChartExponent 1) = Set.Iic 0 := by
  ext z
  simp only [show projectiveChartExponent 1 = -1 from rfl, mul_neg_one, Set.mem_range, Set.mem_Iic]
  constructor
  · rintro ⟨n, rfl⟩; omega
  · intro hz
    refine ⟨(-z).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega), neg_neg]

/-- For any actual finite morphism to P1, actual structure-sheaf H1 is finite over the original field. -/
theorem finiteMap_projectiveLine_unit_H1_finite [IsFinite f] :
    letI := schemeModuleCohomologyModule (f ≫ projectiveLineToSpec k)
      (SheafOfModules.unit X.ringCatSheaf) 1
    Module.Finite k (Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (SheafOfModules.unit X.ringCatSheaf)) 1) := by
  let p := f ≫ projectiveLineToSpec k
  let F := SheafOfModules.unit X.ringCatSheaf
  let := schemeModuleCohomologyModule p F 1
  let := finiteMapChartAlgebra f 0
  let := finiteMapChartAlgebra f 1
  let := finiteMapLaurentAlgebra f
  let := finiteMapOverlapFieldAlgebra f
  have := finiteMapOverlap_scalarTower f
  have := finiteMapChart_module_finite f 0
  have := finiteMapChart_module_finite f 1
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin
    (R := Γ(projectiveLine k, projectiveLineChart k 0))
    (M := Γ(X, f ⁻¹ᵁ projectiveLineChart k 0))
  obtain ⟨m, w, hw⟩ := Module.Finite.exists_fin
    (R := Γ(projectiveLine k, projectiveLineChart k 1))
    (M := Γ(X, f ⁻¹ᵁ projectiveLineChart k 1))
  let U := projectiveLinePullbackChart f 0
  let V := projectiveLinePullbackChart f 1
  let δ := schemeUnitBoundaryOnOverlap p U V (projectiveLinePullbackChart_cover f)
    (finiteMapOverlap f) (finiteMapOverlap_eq_inf f)
  have hz (i : Fin 2) (a : Γ(X, f ⁻¹ᵁ projectiveLineChart k i)) :
      δ (finiteMapChartRestriction f i a) = 0 := by
    apply (schemeUnitBoundaryOnOverlap_eq_zero_iff p U V _ _ _ _).mpr
    fin_cases i
    · exact ⟨a, 0, by simp only [map_zero, sub_zero]; rfl⟩
    · exact ⟨0, -a, by simp only [map_zero, map_neg, zero_sub, neg_neg]; rfl⟩
  apply laurentChart_boundary_finite k
    (finiteMapChartSemilinear f 0 ∘ v) (finiteMapChartSemilinear f 1 ∘ w)
    (finiteMapChart_generators_span f 0 v hv) (finiteMapChart_generators_span f 1 w hw) δ
    (schemeUnitBoundaryOnOverlap_surjective p U V _ _ _
      (projectiveLinePullbackChart_isAffine f 0) (projectiveLinePullbackChart_isAffine f 1))
  · intro z hz'
    have he := finiteMapChart_restriction_image f 0 v hv
    rw [projectiveChartExponent_range_zero] at he
    obtain ⟨a, rfl⟩ := Set.ext_iff.mp he z |>.mpr hz'
    exact hz 0 a
  · intro z hz'
    have he := finiteMapChart_restriction_image f 1 w hw
    rw [projectiveChartExponent_range_one] at he
    obtain ⟨a, rfl⟩ := Set.ext_iff.mp he z |>.mpr hz'
    exact hz 1 a

/-- A nonconstant projective-line map on a proper integral curve suffices:
its finiteness and actual H1 finiteness are both derived. -/
theorem properCurve_unit_H1_finite_of_projectiveMap [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProper p]
    (hcomp : f ≫ projectiveLineToSpec k = p)
    (hdim : topologicalKrullDim X ≤ 1)
    (hnonconstant : ∃ x₁ x₂ : X, f x₁ ≠ f x₂) :
    letI := schemeModuleCohomologyModule p (SheafOfModules.unit X.ringCatSheaf) 1
    Module.Finite k (Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (SheafOfModules.unit X.ringCatSheaf)) 1) := by
  have := projectiveLineToSpec_isProper k
  have := properCurve_nonconstant_map_isFinite p (projectiveLineToSpec k) f hcomp hdim hnonconstant
  subst p
  exact finiteMap_projectiveLine_unit_H1_finite f

end Normalizer
