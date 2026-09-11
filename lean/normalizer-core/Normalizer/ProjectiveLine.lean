import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! The actual projective line as Proj of the polynomial ring in two
variables with its usual grading, and its standard affine opens. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open CategoryTheory AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (k : Type u) [CommRing k]

/-- The projective line is the actual Proj scheme of the standard graded
polynomial ring in two variables. -/
def projectiveLine : Scheme.{u} := Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)

/-- Constants identify the coefficient ring with the degree-zero ring of
the standard homogeneous polynomial grading. -/
def projectiveLineZeroConstants :
    k →+* MvPolynomial.homogeneousSubmodule (Fin 2) k 0 where
  toFun a := ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C (Fin 2) a⟩
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_add' a b := Subtype.ext (map_add MvPolynomial.C a b)
  map_mul' a b := Subtype.ext (map_mul MvPolynomial.C a b)

/-- The actual constants map to degree zero is bijective. -/
theorem projectiveLineZeroConstants_bijective :
    Function.Bijective (projectiveLineZeroConstants k) := by
  constructor
  · intro a b h
    exact MvPolynomial.C_injective (Fin 2) k (congrArg Subtype.val h)
  · intro p
    refine ⟨MvPolynomial.constantCoeff p.val, Subtype.ext ?_⟩
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr p.property)).symm

/-- The canonical isomorphism from constants to the actual degree-zero ring. -/
def projectiveLineZeroEquiv : k ≃+* MvPolynomial.homogeneousSubmodule (Fin 2) k 0 :=
  RingEquiv.ofBijective (projectiveLineZeroConstants k) (projectiveLineZeroConstants_bijective k)

/-- The structure morphism of the actual Proj model over its coefficient ring. -/
def projectiveLineToSpec : projectiveLine k ⟶ Spec (.of k) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) k) ≫
    Spec.map (CommRingCat.ofHom (projectiveLineZeroEquiv k).toRingHom)

/-- The standard homogeneous-coordinate open D₊(X_i). -/
def projectiveLineChart (i : Fin 2) : (projectiveLine k).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i)

/-- Each standard coordinate open of the actual projective line is affine. -/
theorem projectiveLineChart_isAffine (i : Fin 2) : IsAffineOpen (projectiveLineChart k i) := by
  exact Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X k i) (by decide : 0 < 1)

/-- The two variables generate the graded polynomial algebra over its actual
 degree-zero ring. -/
theorem projectiveLine_adjoin_variables :
    Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin 2) k 0)
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)) = ⊤ := by
  apply eq_top_iff.mpr
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C a =>
    exact (Algebra.adjoin _ _).algebraMap_mem (projectiveLineZeroConstants k a)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

/-- Finite type over degree zero, with the two homogeneous variables as generators. -/
theorem projectiveLine_finiteType :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin 2) k 0)
      (MvPolynomial (Fin 2) k) := by
  classical
  refine ⟨⟨Finset.univ.image MvPolynomial.X, ?_⟩⟩
  simpa using projectiveLine_adjoin_variables k

/-- The structure map of the actual projective line is proper. -/
theorem projectiveLineToSpec_isProper : IsProper (projectiveLineToSpec k) := by
  let := projectiveLine_finiteType k
  have : IsIso (CommRingCat.ofHom (projectiveLineZeroEquiv k).toRingHom) :=
    inferInstanceAs (IsIso (projectiveLineZeroEquiv k).toCommRingCatIso.hom)
  unfold projectiveLineToSpec
  infer_instance

/-- The two standard affine opens cover the actual projective line. -/
theorem projectiveLineChart_cover : (⨆ i : Fin 2, projectiveLineChart k i) = ⊤ := by
  exact Proj.iSup_basicOpen_eq_top' _ _
    (fun i => ⟨1, MvPolynomial.isHomogeneous_X k i⟩) (projectiveLine_adjoin_variables k)

/-- The actual standard chart has the homogeneous-localization coordinate ring. -/
def projectiveLineChartIsoSpec (i : Fin 2) :
    (projectiveLineChart k i).toScheme ≅
      Spec (.of (HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i))) :=
  Proj.basicOpenIsoSpec _ _ (MvPolynomial.isHomogeneous_X k i) (by decide : 0 < 1)

variable {k} {X : Scheme.{u}}

/-- Homogeneous coordinates `[1:t]`, evaluated in the actual global sections
of a scheme over the coefficient ring. -/
def projectiveLineSectionEval (p : X ⟶ Spec (.of k)) (t : Γ(X, ⊤)) :
    MvPolynomial (Fin 2) k →+* Γ(X, ⊤) :=
  MvPolynomial.eval₂Hom ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom
    (fun i => if i = 0 then 1 else t)

/-- The coordinate `X₀` maps to one, so the evaluated irrelevant ideal is the unit ideal. -/
theorem projectiveLineSectionEval_irrelevant (p : X ⟶ Spec (.of k)) (t : Γ(X, ⊤)) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toIdeal.map
      (projectiveLineSectionEval p t) = ⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
  have h := Ideal.mem_map_of_mem (projectiveLineSectionEval p t)
    (HomogeneousIdeal.mem_irrelevant_of_mem
      (MvPolynomial.homogeneousSubmodule (Fin 2) k) (by decide : 0 < 1)
      (MvPolynomial.isHomogeneous_X k (0 : Fin 2)))
  simpa [projectiveLineSectionEval] using h

/-- The actual morphism to Proj defined by the coordinates `[1:t]`. -/
def projectiveLineOfSection (p : X ⟶ Spec (.of k)) (t : Γ(X, ⊤)) :
    X ⟶ projectiveLine k :=
  Proj.fromOfGlobalSections _ (projectiveLineSectionEval p t)
    (projectiveLineSectionEval_irrelevant p t)

/-- The section-defined projective-line morphism is over the original base. -/
theorem projectiveLineOfSection_comp (p : X ⟶ Spec (.of k)) (t : Γ(X, ⊤)) :
    projectiveLineOfSection p t ≫ projectiveLineToSpec k = p := by
  unfold projectiveLineOfSection projectiveLineToSpec
  rw [← Category.assoc, Proj.fromOfGlobalSections_toSpecZero, Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have he : ((projectiveLineSectionEval p t).comp
      (algebraMap (MvPolynomial.homogeneousSubmodule (Fin 2) k 0) _)).comp
      (projectiveLineZeroEquiv k).toRingHom =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom := by
    ext a
    simp [projectiveLineSectionEval, projectiveLineZeroEquiv, projectiveLineZeroConstants]
  rw [he]
  simp only [CommRingCat.hom_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom,
    Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

/-- The zero-coordinate chart contains the whole image of `[1:t]`. -/
theorem projectiveLineOfSection_preimage_zero (p : X ⟶ Spec (.of k)) (t : Γ(X, ⊤)) :
    projectiveLineOfSection p t ⁻¹ᵁ projectiveLineChart k 0 = ⊤ := by
  rw [projectiveLineOfSection, projectiveLineChart,
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ (by decide : 0 < 1)
      (MvPolynomial.isHomogeneous_X k 0)]
  simp [projectiveLineSectionEval]

/-- The other standard chart pulls back to the invertibility locus of the specified section. -/
theorem projectiveLineOfSection_preimage_one (p : X ⟶ Spec (.of k)) (t : Γ(X, ⊤)) :
    projectiveLineOfSection p t ⁻¹ᵁ projectiveLineChart k 1 = X.basicOpen t := by
  rw [projectiveLineOfSection, projectiveLineChart,
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ (by decide : 0 < 1)
      (MvPolynomial.isHomogeneous_X k 1)]
  simp [projectiveLineSectionEval]

end Normalizer
