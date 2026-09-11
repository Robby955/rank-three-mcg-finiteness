import Normalizer.CurveProjectiveLine
import Normalizer.FiniteMapH1
import Normalizer.FiniteSchemeCohomology
import Normalizer.SmoothSchemeStalks

/-! Construction of finite projective-line maps. Normal-curve results explicitly
state normality; the original singular integral target remains separate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- A proper zero-dimensional scheme over a field is finite, with no
integrality or reducedness requirement. -/
theorem proper_dimZero_isFinite (p : X ⟶ Spec (.of k)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 0) : IsFinite p := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  have : Finite X := noetherian_dimZero_finite hdim
  have : LocallyQuasiFinite p := LocallyQuasiFinite.of_finite_preimage_singleton p
    (fun _ => Set.toFinite _)
  exact (IsFinite.iff_isProper_and_locallyQuasiFinite p).mpr ⟨inferInstance, inferInstance⟩

/-- Every morphism over a field from a finite scheme to a separated scheme
is finite; the finiteness of its point fibres is derived. -/
theorem finiteScheme_map_isFinite (p : X ⟶ Spec (.of k)) [IsFinite p]
    (q : Y ⟶ Spec (.of k)) [IsSeparated q]
    (f : X ⟶ Y) (hcomp : f ≫ q = p) : IsFinite f := by
  have : Finite X := by
    have := p.finite_preimage_singleton (IsLocalRing.closedPoint k)
    have he : p ⁻¹' {IsLocalRing.closedPoint k} = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [he] at this
    exact Set.finite_univ_iff.mp this
  have : IsProper (f ≫ q) := hcomp ▸ inferInstance
  have : IsProper f := IsProper.of_comp f q
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f
    (fun _ => Set.toFinite _)
  exact (IsFinite.iff_isProper_and_locallyQuasiFinite f).mpr ⟨inferInstance, inferInstance⟩

/-- The zero-dimensional branch has an actual finite map to the projective
line, obtained from the constant homogeneous coordinates `[1:0]`. -/
theorem proper_dimZero_exists_finite_projectiveLine
    (p : X ⟶ Spec (.of k)) [IsProper p] (hdim : topologicalKrullDim X ≤ 0) :
    ∃ f : X ⟶ projectiveLine k, f ≫ projectiveLineToSpec k = p ∧ IsFinite f := by
  have := proper_dimZero_isFinite p hdim
  have := projectiveLineToSpec_isProper k
  exact ⟨projectiveLineOfSection p 0, projectiveLineOfSection_comp p 0,
    finiteScheme_map_isFinite p (projectiveLineToSpec k) _ (projectiveLineOfSection_comp p 0)⟩

/-- All positive-degree abelian-sheaf cohomology vanishes on a proper
zero-dimensional scheme over a field. -/
theorem proper_dimZero_positiveCohomology_subsingleton
    (p : X ⟶ Spec (.of k)) [IsProper p] (hdim : topologicalKrullDim X ≤ 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat) (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  have := proper_dimZero_isFinite p hdim
  exact finiteScheme_positiveCohomology_subsingleton p F n

/-- Generic agreement with a global map forces agreement on the entire
specified partial-map domain, for an integral source and separated target. -/
theorem partialMap_eq_restriction_of_generic [IsIntegral X] [Y.IsSeparated]
    (a : X.PartialMap Y) (f : X ⟶ Y)
    (h : a.fromFunctionField = X.fromSpecStalk (genericPoint X) ≫ f) :
    a.hom = a.domain.ι ≫ f := by
  apply (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
  apply Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq a f.toPartialMap
    ((genericPoint_specializes _).mem_open a.domain.2 a.dense_domain.nonempty.choose_spec) (by trivial)
  simpa using h

/-- A partial map extends into a proper target when every stalk outside
its actual domain is a valuation ring. Stalks inside that domain need not
be normal: the already-defined map is retained there. -/
theorem partialMap_extends_of_valuationOutside [IsIntegral X]
    (p : X ⟶ Spec (.of k)) (q : Y ⟶ Spec (.of k)) [IsProper q]
    (a : X.PartialMap Y) (ha : a.hom ≫ q = a.domain.ι ≫ p)
    (houtside : ∀ x : X, x ∉ a.domain → ValuationRing (X.presheaf.stalk x)) :
    ∃ f : X ⟶ Y, f ≫ q = p ∧ a.hom = a.domain.ι ≫ f := by
  have : Y.IsSeparated := by
    constructor
    have : IsSeparated (q ≫ terminal.from (Spec (.of k))) := inferInstance
    simpa using this
  have hg : a.fromFunctionField ≫ q = X.fromSpecStalk (genericPoint X) ≫ p := by
    dsimp only [Scheme.PartialMap.fromFunctionField, Scheme.PartialMap.fromSpecStalkOfMem]
    rw [Category.assoc, ha, ← Category.assoc]
    simp
  let r := Scheme.RationalMap.ofFunctionField p q a.fromFunctionField hg
  have hr : r = a.toRationalMap := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    exact Scheme.RationalMap.fromFunctionField_ofFunctionField p q a.fromFunctionField hg
  have hd : r.domain = ⊤ := by
    apply TopologicalSpace.Opens.ext
    apply Set.eq_univ_iff_forall.mpr
    intro x
    by_cases hx : x ∈ a.domain
    · rw [hr]
      exact a.le_domain_toRationalMap hx
    · have := houtside x hx
      exact genericMap_mem_domain_of_valuationStalk p q a.fromFunctionField hg x
  obtain ⟨f, hf⟩ := rationalMap_exists_hom_of_domain_eq_top r hd
  have hgen : X.fromSpecStalk (genericPoint X) ≫ f = a.fromFunctionField := by
    have h := congrArg Scheme.RationalMap.fromFunctionField hf
    simpa [r, Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.PartialMap.fromFunctionField,
      Scheme.RationalMap.fromFunctionField_ofFunctionField] using h
  refine ⟨f, ?_, partialMap_eq_restriction_of_generic a f hgen.symm⟩
  apply schemeHom_eq_of_genericRestriction
  simpa only [← Category.assoc, hgen] using hg

/-- A specified partial map on a normal integral curve extends to a global
map into a proper target over the original base. Its restriction is proved,
not supplied as a further geometric hypothesis. -/
theorem normalCurve_partialMap_extends [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (hdim : topologicalKrullDim X ≤ 1)
    (p : X ⟶ Spec (.of k)) (q : Y ⟶ Spec (.of k)) [IsProper q]
    (a : X.PartialMap Y) (ha : a.hom ≫ q = a.domain.ι ≫ p) :
    ∃ f : X ⟶ Y, f ≫ q = p ∧ a.hom = a.domain.ι ≫ f :=
  partialMap_extends_of_valuationOutside p q a ha
    (fun x _ => normalCurve_stalk_valuationRing hdim x)

/-- On an affine integral scheme with at least two points, an actual global
section defines a nonconstant projective-line map. The section is chosen
with a proper nonempty invertibility locus. -/
theorem affineIntegral_exists_nonconstant_projectiveLineMap
    [IsIntegral X] [IsAffine X] [Nontrivial X]
    (p : X ⟶ Spec (.of k)) :
    ∃ f : X ⟶ projectiveLine k, f ≫ projectiveLineToSpec k = p ∧
      ∃ x₁ x₂ : X, f x₁ ≠ f x₂ := by
  obtain ⟨x, hx⟩ := exists_ne (genericPoint X)
  let V : X.Opens := ⟨(closure ({x} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
  have hg : genericPoint X ∈ V := by
    intro h
    exact hx ((specializes_iff_mem_closure.mpr h).antisymm (genericPoint_specializes x)).eq
  obtain ⟨s, hsV, hgs⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨genericPoint X, hg⟩
    (by trivial)
  have hxs : x ∉ X.basicOpen s := by
    intro h
    exact hsV h (subset_closure (Set.mem_singleton x))
  refine ⟨projectiveLineOfSection p s, projectiveLineOfSection_comp p s,
    genericPoint X, x, ?_⟩
  intro he
  have hgen : projectiveLineOfSection p s (genericPoint X) ∈ projectiveLineChart k 1 := by
    change genericPoint X ∈ projectiveLineOfSection p s ⁻¹ᵁ projectiveLineChart k 1
    rwa [projectiveLineOfSection_preimage_one]
  rw [he] at hgen
  apply hxs
  change x ∈ projectiveLineOfSection p s ⁻¹ᵁ projectiveLineChart k 1 at hgen
  rwa [projectiveLineOfSection_preimage_one] at hgen

/-- An integral scheme with at least two points contains an actual affine
open with at least two points. -/
theorem integral_exists_nontrivial_affineOpen [IsIntegral X] [Nontrivial X] :
    ∃ U : X.Opens, IsAffineOpen U ∧ Nontrivial U := by
  obtain ⟨x, hx⟩ := exists_ne (genericPoint X)
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (show x ∈ (⊤ : X.Opens) from trivial)
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hne : (⟨x, hxU⟩ : U) ≠ genericPoint U.toScheme := by
    intro he
    apply hx
    exact (congrArg (fun y : U => (y : X)) he).trans
      (genericPoint_eq_of_isOpenImmersion U.ι)
  exact ⟨U, hU, ⟨⟨_, _, hne⟩⟩⟩

/-- A normal integral curve with at least two points has an actual
nonconstant projective-line map over its original field. No rational
function or nonconstancy certificate is supplied as an input. -/
theorem normalCurve_exists_nonconstant_projectiveLineMap
    [IsIntegral X] [IsLocallyNoetherian X] [Nontrivial X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (hdim : topologicalKrullDim X ≤ 1) (p : X ⟶ Spec (.of k)) :
    ∃ f : X ⟶ projectiveLine k, f ≫ projectiveLineToSpec k = p ∧
      ∃ x₁ x₂ : X, f x₁ ≠ f x₂ := by
  obtain ⟨U, hU, hnU⟩ := integral_exists_nontrivial_affineOpen (X := X)
  let : Nontrivial U := hnU
  let : IsAffine U.toScheme := hU
  obtain ⟨g, hg, x₁, x₂, hne⟩ := affineIntegral_exists_nonconstant_projectiveLineMap (U.ι ≫ p)
  let a : X.PartialMap (projectiveLine k) :=
    ⟨U, U.isOpen.dense ⟨x₁.val, x₁.property⟩, g⟩
  have := projectiveLineToSpec_isProper k
  obtain ⟨f, hf, he⟩ := normalCurve_partialMap_extends hdim p (projectiveLineToSpec k) a hg
  refine ⟨f, hf, x₁.val, x₂.val, ?_⟩
  intro h
  apply hne
  change g = U.ι ≫ f at he
  rw [he]
  exact h

/-- A proper morphism with a finite source space is finite. -/
theorem proper_finiteSpace_isFinite [Finite X]
    (p : X ⟶ Spec (.of k)) [IsProper p] : IsFinite p := by
  have : LocallyQuasiFinite p := LocallyQuasiFinite.of_finite_preimage_singleton p
    (fun _ => Set.toFinite _)
  exact (IsFinite.iff_isProper_and_locallyQuasiFinite p).mpr ⟨inferInstance, inferInstance⟩

/-- A proper normal integral curve of dimension at most one admits an actual
finite projective-line map over its original field. Normality is explicit;
this theorem includes the zero-dimensional case. -/
theorem properNormalCurve_exists_finite_projectiveLine
    [IsIntegral X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (p : X ⟶ Spec (.of k)) [IsProper p] (hdim : topologicalKrullDim X ≤ 1) :
    ∃ f : X ⟶ projectiveLine k, f ≫ projectiveLineToSpec k = p ∧ IsFinite f := by
  classical
  have := projectiveLineToSpec_isProper k
  cases subsingleton_or_nontrivial X with
  | inl hs =>
    let := hs
    have := proper_finiteSpace_isFinite p
    exact ⟨projectiveLineOfSection p 0, projectiveLineOfSection_comp p 0,
      finiteScheme_map_isFinite p (projectiveLineToSpec k) _ (projectiveLineOfSection_comp p 0)⟩
  | inr hn =>
    let := hn
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    obtain ⟨f, hf, hn⟩ := normalCurve_exists_nonconstant_projectiveLineMap hdim p
    exact ⟨f, hf, properCurve_nonconstant_map_isFinite p (projectiveLineToSpec k) f hf hdim hn⟩

/-- Actual structure-sheaf H1 is finite-dimensional on a proper normal
integral curve. The finite map and its scalar compatibility are constructed. -/
theorem properNormalCurve_unit_H1_finite
    [IsIntegral X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (p : X ⟶ Spec (.of k)) [IsProper p] (hdim : topologicalKrullDim X ≤ 1) :
    let := schemeModuleCohomologyModule p (SheafOfModules.unit X.ringCatSheaf) 1
    Module.Finite k (Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (SheafOfModules.unit X.ringCatSheaf)) 1) := by
  obtain ⟨f, hf, hfinite⟩ := properNormalCurve_exists_finite_projectiveLine p hdim
  let := hfinite
  subst p
  exact finiteMap_projectiveLine_unit_H1_finite f

/-- Smooth integral curves have integrally closed actual stalks. Smoothness
supplies regularity; dimension at most one supplies the principal ideal property. -/
theorem smoothCurve_stalk_isIntegrallyClosed [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [Smooth p] (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  have := smoothScheme_stalk_isRegularLocalRing k p x
  have hd : Order.krullDim X ≤ 1 := by
    rwa [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  have hs : ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
    rw [ringKrullDim_stalk_eq_coheight]
    exact (Order.coheight_le_krullDim x).trans hd
  have := principalIdealRing_of_regularLocal_dim_le_one (X.presheaf.stalk x) hs
  infer_instance

/-- A proper smooth integral curve admits an actual finite projective-line
map, with no supplied rational function, local normality or nonconstancy. -/
theorem properSmoothCurve_exists_finite_projectiveLine [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProper p] [Smooth p] (hdim : topologicalKrullDim X ≤ 1) :
    ∃ f : X ⟶ projectiveLine k, f ≫ projectiveLineToSpec k = p ∧ IsFinite f := by
  have := smoothCurve_stalk_isIntegrallyClosed p hdim
  exact properNormalCurve_exists_finite_projectiveLine p hdim

/-- Actual structure-sheaf H1 finiteness for a proper smooth integral curve.
Normality and the finite projective-line map are derived from these hypotheses. -/
theorem properSmoothCurve_unit_H1_finite [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProper p] [Smooth p] (hdim : topologicalKrullDim X ≤ 1) :
    letI := schemeModuleCohomologyModule p (SheafOfModules.unit X.ringCatSheaf) 1
    Module.Finite k (Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (SheafOfModules.unit X.ringCatSheaf)) 1) := by
  have := smoothCurve_stalk_isIntegrallyClosed p hdim
  exact properNormalCurve_unit_H1_finite p hdim

end Normalizer
