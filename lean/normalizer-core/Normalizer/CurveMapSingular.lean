import Normalizer.CurveMapExistence

/-! Finite maps with singularities allowed on a specified affine open.
The one-exceptional-point case constructs that open. A general affine
neighborhood of the nonnormal locus is not constructed here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

/-- Every point of a nontrivial integral scheme lies in an actual affine
open with at least two points. For the generic point, choose a neighborhood
of another point, which necessarily also contains the generic point. -/
theorem integral_exists_nontrivial_affineOpen_at [Nontrivial X] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧ Nontrivial U := by
  classical
  by_cases hx : x = genericPoint X
  · obtain ⟨U, hU, hn⟩ := integral_exists_nontrivial_affineOpen (X := X)
    have := hn
    obtain ⟨y⟩ := (inferInstance : Nonempty U)
    exact ⟨U, hx ▸ (genericPoint_specializes y.val).mem_open U.isOpen y.property, hU, hn⟩
  · obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
      (show x ∈ (⊤ : X.Opens) from trivial)
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    have hne : (⟨x, hxU⟩ : U) ≠ genericPoint U.toScheme := by
      intro he
      apply hx
      exact (congrArg (fun y : U => (y : X)) he).trans
        (genericPoint_eq_of_isOpenImmersion U.ι)
    exact ⟨U, hxU, hU, ⟨⟨_, _, hne⟩⟩⟩

/-- A proper integral curve admits a finite projective-line map if an
actual nontrivial affine open contains all its nonnormal points. The map,
its extension across the complementary points, and nonconstancy are derived. -/
theorem properCurve_exists_finite_projectiveLine_of_normalOutsideAffine
    (p : X ⟶ Spec (.of k)) [IsProper p] (hdim : topologicalKrullDim X ≤ 1)
    (U : X.Opens) (hU : IsAffineOpen U) [Nontrivial U]
    (houtside : ∀ x : X, x ∉ U → IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ f : X ⟶ projectiveLine k, f ≫ projectiveLineToSpec k = p ∧ IsFinite f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsAffine U.toScheme := hU
  obtain ⟨g, hg, x₁, x₂, hne⟩ := affineIntegral_exists_nonconstant_projectiveLineMap (U.ι ≫ p)
  let a : X.PartialMap (projectiveLine k) := ⟨U, U.isOpen.dense ⟨x₁.val, x₁.property⟩, g⟩
  have := projectiveLineToSpec_isProper k
  have hv (x : X) (hx : x ∉ a.domain) : ValuationRing (X.presheaf.stalk x) := by
    have := houtside x hx
    exact normalCurve_stalk_valuationRing hdim x
  obtain ⟨f, hf, he⟩ := partialMap_extends_of_valuationOutside p (projectiveLineToSpec k) a hg hv
  have hn : ∃ x₁ x₂ : X, f x₁ ≠ f x₂ := by
    refine ⟨x₁.val, x₂.val, ?_⟩
    intro h
    apply hne
    change g = U.ι ≫ f at he
    rw [he]
    exact h
  exact ⟨f, hf, properCurve_nonconstant_map_isFinite p (projectiveLineToSpec k) f hf hdim hn⟩

/-- A proper integral curve normal away from one specified point has an
actual finite projective-line map. No normality at that point or affine
neighborhood containing it is assumed. -/
theorem properCurve_exists_finite_projectiveLine_of_normalAwayPoint
    (p : X ⟶ Spec (.of k)) [IsProper p] (hdim : topologicalKrullDim X ≤ 1) (x : X)
    (hnormal : ∀ y : X, y ≠ x → IsIntegrallyClosed (X.presheaf.stalk y)) :
    ∃ f : X ⟶ projectiveLine k, f ≫ projectiveLineToSpec k = p ∧ IsFinite f := by
  classical
  cases subsingleton_or_nontrivial X with
  | inl hs =>
    have := hs
    have := proper_finiteSpace_isFinite p
    have := projectiveLineToSpec_isProper k
    exact ⟨projectiveLineOfSection p 0, projectiveLineOfSection_comp p 0,
      finiteScheme_map_isFinite p (projectiveLineToSpec k) _ (projectiveLineOfSection_comp p 0)⟩
  | inr hn =>
    have := hn
    obtain ⟨U, hxU, hU, hnU⟩ := integral_exists_nontrivial_affineOpen_at x
    have := hnU
    apply properCurve_exists_finite_projectiveLine_of_normalOutsideAffine p hdim U hU
    intro y hy
    apply hnormal y
    rintro rfl
    exact hy hxU

/-- Actual structure-sheaf H1 finiteness when the proper integral curve is
normal away from one point. The exceptional point may be singular. -/
theorem properCurve_unit_H1_finite_of_normalAwayPoint
    (p : X ⟶ Spec (.of k)) [IsProper p] (hdim : topologicalKrullDim X ≤ 1) (x : X)
    (hnormal : ∀ y : X, y ≠ x → IsIntegrallyClosed (X.presheaf.stalk y)) :
    letI := schemeModuleCohomologyModule p (SheafOfModules.unit X.ringCatSheaf) 1
    Module.Finite k (Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (SheafOfModules.unit X.ringCatSheaf)) 1) := by
  obtain ⟨f, hf, hfinite⟩ := properCurve_exists_finite_projectiveLine_of_normalAwayPoint p hdim x hnormal
  have := hfinite
  subst p
  exact finiteMap_projectiveLine_unit_H1_finite f

end Normalizer
