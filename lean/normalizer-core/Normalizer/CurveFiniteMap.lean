import Normalizer.CurveClosedSubscheme
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! Finiteness of a nonconstant proper morphism from an integral curve.
The proof constructs finite point fibres using dimension at most one,
then applies the proper and quasi-finite criterion. -/
noncomputable section
namespace Normalizer
open CategoryTheory AlgebraicGeometry TopologicalSpace Order Set

private theorem closed_singleton_of_minimal_closure
    {X : Type*} [TopologicalSpace X] [T0Space X] (x : X)
    (hmin : IsMin (⟨closure {x}, isIrreducible_singleton.closure,
      isClosed_closure⟩ : IrreducibleCloseds X)) : IsClosed ({x} : Set X) := by
  apply closure_eq_iff_isClosed.mp
  apply subset_antisymm _ subset_closure
  intro y hy
  let Cx : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure,
    isClosed_closure⟩
  let Cy : IrreducibleCloseds X := ⟨closure {y}, isIrreducible_singleton.closure,
    isClosed_closure⟩
  have hle : Cy ≤ Cx := closure_minimal (singleton_subset_iff.mpr hy) isClosed_closure
  have he : Cy = Cx := le_antisymm hle (hmin hle)
  exact (show IsGenericPoint y (closure {x}) from
    congrArg (fun C : IrreducibleCloseds X => (C : Set X)) he).eq isGenericPoint_closure

/-- In a sober irreducible space of dimension at most one, every point
other than the generic point is closed. -/
theorem curve_closedPoint_of_ne_generic
    {X : Type*} [TopologicalSpace X] [T0Space X] [QuasiSober X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (x : X) (hx : x ≠ genericPoint X) :
    IsClosed ({x} : Set X) := by
  let Cx : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure,
    isClosed_closure⟩
  rcases krullDim_le_one_iff.mp hdim Cx with hmin | hmax
  · exact closed_singleton_of_minimal_closure x hmin
  · let T : IrreducibleCloseds X :=
      ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
    have he : Cx = T := le_antisymm (subset_univ _) (hmax (subset_univ _))
    exact (hx ((show IsGenericPoint x univ from
      congrArg (fun C : IrreducibleCloseds X => (C : Set X)) he).eq
        (genericPoint_spec X))).elim

/-- A zero-dimensional Noetherian T₀ space has finitely many points.
Every point is the generic point of a maximal irreducible closed subset. -/
theorem noetherian_dimZero_finite
    {X : Type*} [TopologicalSpace X] [T0Space X] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 0) : Finite X := by
  have h : (genericPoints X).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  apply Set.finite_univ_iff.mp
  apply h.subset
  intro x _
  change closure ({x} : Set X) ∈ irreducibleComponents X
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨isClosed_closure, isIrreducible_singleton.closure⟩, ?_⟩
  intro s hs hxs
  let Cx : IrreducibleCloseds X :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hmax : IsMax Cx := krullDim_nonpos_iff_forall_isMax.mp hdim Cx
  exact hmax (show Cx ≤ (⟨s, hs.2, hs.1⟩ : IrreducibleCloseds X) from hxs)

/-- A proper closed subset of a Noetherian irreducible T₀ curve is finite. -/
theorem curve_properClosedSubset_finite
    {X : Type*} [TopologicalSpace X] [T0Space X] [NoetherianSpace X]
    [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 1)
    (s : Set X) (hs : IsClosed s) (hproper : s ≠ univ) : s.Finite := by
  have hdimS := topologicalKrullDim_nonpos_of_closedEmbedding
    hs.isClosedEmbedding_subtypeVal hdim (by
      intro hsurj
      apply hproper
      exact Set.eq_univ_iff_forall.mpr fun x => (hsurj x).choose_spec ▸ (hsurj x).choose.property)
  have := noetherian_dimZero_finite hdimS
  exact Set.toFinite s

/-- Every fibre of a nonconstant closed continuous map out of a
Noetherian sober irreducible curve is finite, including nonclosed fibres. -/
theorem curve_closedMap_fibres_finite
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T0Space X] [QuasiSober X] [NoetherianSpace X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (f : X → Y) (hf : Continuous f)
    (hclosed : IsClosedMap f) (hnonconstant : ∃ x₁ x₂, f x₁ ≠ f x₂) (y : Y) :
    (f ⁻¹' {y}).Finite := by
  classical
  by_cases hy : IsClosed ({y} : Set Y)
  · apply curve_properClosedSubset_finite hdim _ (hy.preimage hf)
    intro hall
    obtain ⟨x₁, x₂, hne⟩ := hnonconstant
    have hx (x : X) : f x = y := by
      have : x ∈ f ⁻¹' {y} := hall ▸ mem_univ x
      exact this
    exact hne ((hx x₁).trans (hx x₂).symm)
  · apply (Set.finite_singleton (genericPoint X)).subset
    intro x hx
    by_contra hgeneric
    have hpoint := curve_closedPoint_of_ne_generic hdim x hgeneric
    have hc := hclosed {x} hpoint
    rw [Set.image_singleton, show f x = y from hx] at hc
    exact hy hc

/-- A nonconstant proper morphism from an integral Noetherian scheme of
dimension at most one is finite. No finiteness of its fibres is assumed. -/
theorem curve_nonconstant_proper_isFinite
    {X Y : Scheme} [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Y) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (hnonconstant : ∃ x₁ x₂ : X, f x₁ ≠ f x₂) : IsFinite f := by
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f
    (curve_closedMap_fibres_finite hdim f f.continuous f.isClosedMap hnonconstant)
  exact (IsFinite.iff_isProper_and_locallyQuasiFinite f).mpr ⟨inferInstance, inferInstance⟩

/-- A nonconstant map from a proper integral curve over a field to a
separated scheme over that field is finite. Noetherianity and properness
of the actual map are derived from the structure morphism. -/
theorem properCurve_nonconstant_map_isFinite
    {k : Type*} [Field k] {X Y : Scheme} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProper p]
    (q : Y ⟶ Spec (.of k)) [IsSeparated q]
    (f : X ⟶ Y) (hcomp : f ≫ q = p)
    (hdim : topologicalKrullDim X ≤ 1)
    (hnonconstant : ∃ x₁ x₂ : X, f x₁ ≠ f x₂) : IsFinite f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  have : IsProper (f ≫ q) := hcomp ▸ inferInstance
  have : IsProper f := IsProper.of_comp f q
  exact curve_nonconstant_proper_isFinite f hdim hnonconstant

end Normalizer
