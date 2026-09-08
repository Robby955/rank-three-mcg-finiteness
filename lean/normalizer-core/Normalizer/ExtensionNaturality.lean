import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Normalizer.ExtensionDimension

/-! Connecting-map naturality for the actual mathlib homology sequence.
These statements assume short exact sequences of complexes and genuine maps
between them. No boundary map or naturality identity is postulated. The
application to sheaf extensions requires constructing the corresponding
complexes and maps; that geometric construction is not supplied here. -/

namespace Normalizer
open CategoryTheory CategoryTheory.Limits

variable {C I : Type*} [Category* C] [Abelian C] {c : ComplexShape I}

/-- A morphism of short exact sequences with zero left component kills the
target connecting map after the induced map on the right. -/
theorem connecting_zero_of_zero_left
    {S T : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (hleft : φ.τ₁ = 0) (i j : I) (hij : c.Rel i j) :
    HomologicalComplex.homologyMap φ.τ₃ i ≫ hT.δ i j hij = 0 := by
  rw [← HomologicalComplex.HomologySequence.δ_naturality φ hS hT i j hij,
    hleft, HomologicalComplex.homologyMap_zero, comp_zero]

/-- The manuscript's `s_* e A = 0`, in actual homology-sequence notation.
`φ` is the bracket morphism with zero left component. `ψ` is multiplication
by the section. The right component of `φ` factors through the block `A`. -/
theorem extension_block_annihilated
    {S₀ S T : ShortComplex (HomologicalComplex C c)}
    (hS₀ : S₀.ShortExact) (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S₀ ⟶ T) (ψ : S ⟶ T) (A : S₀.X₃ ⟶ S.X₃)
    (hleft : φ.τ₁ = 0) (hfactor : φ.τ₃ = A ≫ ψ.τ₃)
    (i j : I) (hij : c.Rel i j) :
    HomologicalComplex.homologyMap A i ≫ hS.δ i j hij ≫
      HomologicalComplex.homologyMap ψ.τ₁ j = 0 := by
  rw [HomologicalComplex.HomologySequence.δ_naturality ψ hS hT i j hij,
    ← Category.assoc, ← HomologicalComplex.homologyMap_comp, ← hfactor]
  exact connecting_zero_of_zero_left hS₀ hT φ hleft i j hij

/-- If both downstream maps are monomorphisms, the block vanishes. This is
the degree-one case after the geometric identifications are supplied. -/
theorem extension_block_zero
    {S₀ S T : ShortComplex (HomologicalComplex C c)}
    (hS₀ : S₀.ShortExact) (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S₀ ⟶ T) (ψ : S ⟶ T) (A : S₀.X₃ ⟶ S.X₃)
    (hleft : φ.τ₁ = 0) (hfactor : φ.τ₃ = A ≫ ψ.τ₃)
    (i j : I) (hij : c.Rel i j)
    [Mono (hS.δ i j hij)] [Mono (HomologicalComplex.homologyMap ψ.τ₁ j)] :
    HomologicalComplex.homologyMap A i = 0 := by
  apply (cancel_mono (hS.δ i j hij)).mp
  apply (cancel_mono (HomologicalComplex.homologyMap ψ.τ₁ j)).mp
  simpa only [Category.assoc, zero_comp] using
    extension_block_annihilated hS₀ hS hT φ ψ A hleft hfactor i j hij

end Normalizer

namespace Normalizer
open CategoryTheory CategoryTheory.Limits

/-- A dimension bound using the actual connecting map of a short exact
sequence of complexes of vector spaces. Naturality is proved above, rather
than supplied as a linear-map hypothesis. -/
theorem homology_extension_kernel_lower_bound
    {F I : Type*} [Field F] {c : ComplexShape I}
    {S₀ S T : ShortComplex (HomologicalComplex (ModuleCat F) c)}
    (hS₀ : S₀.ShortExact) (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S₀ ⟶ T) (ψ : S ⟶ T) (A : S₀.X₃ ⟶ S.X₃)
    (hleft : φ.τ₁ = 0) (hfactor : φ.τ₃ = A ≫ ψ.τ₃)
    (i j : I) (hij : c.Rel i j)
    [FiniteDimensional F (S₀.X₃.homology i)]
    [FiniteDimensional F (S.X₁.homology j)]
    (hvanish : IsZero (S.X₂.homology i))
    (g d h : ℕ) (hd : 1 ≤ d)
    (hsource : g + d - 1 ≤ Module.finrank F (S₀.X₃.homology i) + h)
    (hdivisor : Module.finrank F
      (HomologicalComplex.homologyMap ψ.τ₁ j).hom.ker ≤ d - 1) :
    g - h ≤ Module.finrank F (HomologicalComplex.homologyMap A i).hom.ker := by
  let := hS.mono_δ i j hij hvanish
  apply extension_kernel_lower_bound (HomologicalComplex.homologyMap A i).hom
    (hS.δ i j hij).hom (HomologicalComplex.homologyMap ψ.τ₁ j).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) _ g d h hd hsource hdivisor
  have hz := extension_block_annihilated hS₀ hS hT φ ψ A hleft hfactor i j hij
  exact congrArg ModuleCat.Hom.hom hz

end Normalizer
