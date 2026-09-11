import Normalizer.CurveRationalExtension
import Normalizer.ProjectiveLine
import Normalizer.TwoAffineSections

/-! A morphism from a normal curve to the actual projective line,
constructed from a specified element of its generic stalk. Normality
is stated explicitly; this construction does not treat singular curves. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}

section Integral
variable [IsIntegral X]

/-- The actual generic-stalk map with homogeneous coordinates `[1:t]`. -/
def curveGenericProjectiveLineMap (p : X ⟶ Spec (.of k)) (t : X.functionField) :
    Spec (.of X.functionField) ⟶ projectiveLine k :=
  projectiveLineOfSection (X.fromSpecStalk (genericPoint X) ≫ p)
    ((Scheme.ΓSpecIso (.of X.functionField)).inv t)

/-- The specified generic map is over the original base field. -/
theorem curveGenericProjectiveLineMap_comp (p : X ⟶ Spec (.of k)) (t : X.functionField) :
    curveGenericProjectiveLineMap p t ≫ projectiveLineToSpec k =
      X.fromSpecStalk (genericPoint X) ≫ p :=
  projectiveLineOfSection_comp _ _

/-- A specified rational function on a normal curve gives a unique actual
projective-line morphism with those generic coordinates. -/
theorem normalCurve_projectiveLine_existsUnique
    [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (hdim : topologicalKrullDim X ≤ 1)
    (p : X ⟶ Spec (.of k)) (t : X.functionField) :
    ∃! f : X ⟶ projectiveLine k, f ≫ projectiveLineToSpec k = p ∧
      X.fromSpecStalk (genericPoint X) ≫ f = curveGenericProjectiveLineMap p t := by
  have := projectiveLineToSpec_isProper k
  exact normalCurve_genericMap_existsUnique hdim p (projectiveLineToSpec k)
    (curveGenericProjectiveLineMap p t) (curveGenericProjectiveLineMap_comp p t)

/-- The projective-line morphism constructed by extension of `[1:t]`. -/
def normalCurveProjectiveLineMap
    [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (hdim : topologicalKrullDim X ≤ 1)
    (p : X ⟶ Spec (.of k)) (t : X.functionField) : X ⟶ projectiveLine k :=
  (normalCurve_projectiveLine_existsUnique hdim p t).exists.choose

/-- The constructed morphism respects the original structure map. -/
theorem normalCurveProjectiveLineMap_comp
    [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (hdim : topologicalKrullDim X ≤ 1)
    (p : X ⟶ Spec (.of k)) (t : X.functionField) :
    normalCurveProjectiveLineMap hdim p t ≫ projectiveLineToSpec k = p :=
  (normalCurve_projectiveLine_existsUnique hdim p t).exists.choose_spec.1

/-- The generic restriction is the originally specified `[1:t]` map. -/
theorem normalCurveProjectiveLineMap_generic
    [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (hdim : topologicalKrullDim X ≤ 1)
    (p : X ⟶ Spec (.of k)) (t : X.functionField) :
    X.fromSpecStalk (genericPoint X) ≫ normalCurveProjectiveLineMap hdim p t =
      curveGenericProjectiveLineMap p t :=
  (normalCurve_projectiveLine_existsUnique hdim p t).exists.choose_spec.2

/-- Nonconstancy of the constructed morphism, when established, makes it finite.
The normality input is used only in constructing this particular morphism. -/
theorem normalCurveProjectiveLineMap_isFinite_of_nonconstant
    [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (hdim : topologicalKrullDim X ≤ 1)
    (p : X ⟶ Spec (.of k)) [IsProper p] (t : X.functionField)
    (hnonconstant : ∃ x₁ x₂ : X,
      normalCurveProjectiveLineMap hdim p t x₁ ≠ normalCurveProjectiveLineMap hdim p t x₂) :
    IsFinite (normalCurveProjectiveLineMap hdim p t) := by
  have := projectiveLineToSpec_isProper k
  exact properCurve_nonconstant_map_isFinite p (projectiveLineToSpec k) _
    (normalCurveProjectiveLineMap_comp hdim p t) hdim hnonconstant

end Integral

/-- The actual inverse image of a standard projective-line chart. -/
def projectiveLinePullbackChart (f : X ⟶ projectiveLine k) (i : Fin 2) : X.Opens :=
  f ⁻¹ᵁ projectiveLineChart k i

/-- The two pulled-back coordinate opens cover the source scheme. -/
theorem projectiveLinePullbackChart_cover (f : X ⟶ projectiveLine k) :
    projectiveLinePullbackChart f 0 ⊔ projectiveLinePullbackChart f 1 = ⊤ := by
  have hc : projectiveLineChart k 0 ⊔ projectiveLineChart k 1 = ⊤ := by
    apply top_unique
    rw [← projectiveLineChart_cover k]
    apply iSup_le
    intro i
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  simp only [projectiveLinePullbackChart, ← Scheme.Hom.preimage_sup, hc,
    Scheme.Hom.preimage_top]

/-- Under an affine morphism, in particular a finite one, the actual
inverse-image coordinate opens are affine. No normality is needed here. -/
theorem projectiveLinePullbackChart_isAffine (f : X ⟶ projectiveLine k)
    [IsAffineHom f] (i : Fin 2) : IsAffineOpen (projectiveLinePullbackChart f i) :=
  (projectiveLineChart_isAffine k i).preimage f

/-- The actual coordinate-ring action on the inverse-image chart sections,
induced by the original morphism's sheaf map. -/
@[instance_reducible]
def projectiveLinePullbackChartAlgebra (f : X ⟶ projectiveLine k) (i : Fin 2) :
    Algebra Γ(projectiveLine k, projectiveLineChart k i)
      Γ(X, projectiveLinePullbackChart f i) :=
  (f.app (projectiveLineChart k i)).hom.toAlgebra

/-- A finite map supplies finite actual chart modules over the corresponding
projective-line chart rings. Polynomial-coordinate identification is separate. -/
theorem projectiveLinePullbackChart_finite (f : X ⟶ projectiveLine k) [IsFinite f]
    (i : Fin 2) :
    letI := projectiveLinePullbackChartAlgebra f i
    Module.Finite Γ(projectiveLine k, projectiveLineChart k i)
      Γ(X, projectiveLinePullbackChart f i) :=
  IsFinite.finite_app f _ (projectiveLineChart_isAffine k i)

/-- The actual inverse-image chart section quotient computes actual H¹
for an affine morphism to the projective line. In particular this applies
to a finite morphism. No cohomology dimension is supplied or concluded. -/
def projectiveLineChartSectionH1QuotientEquiv
    (p : X ⟶ Spec (.of k)) (f : X ⟶ projectiveLine k) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent] :
    let U := projectiveLinePullbackChart f 0
    let V := projectiveLinePullbackChart f 1
    letI := schemeOpenSectionsModule p (U ⊓ V) F
    letI := schemeModuleCohomologyModule p F 1
    (Γ(F, U ⊓ V) ⧸ (twoOpenSectionδ p U V (projectiveLinePullbackChart_cover f) F).ker) ≃ₗ[k]
      Sheaf.H ((schemeModulesToAbelianSheaves X).obj F) 1 :=
  twoAffineSectionH1QuotientEquiv p _ _ (projectiveLinePullbackChart_cover f) F
    (projectiveLinePullbackChart_isAffine f 0) (projectiveLinePullbackChart_isAffine f 1)

end Normalizer
