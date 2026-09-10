import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties

/-! Proper closed subspaces of an irreducible space of dimension at most
one have dimension at most zero. This is a topological statement and its
application to actual closed subschemes. -/

noncomputable section
namespace Normalizer
open CategoryTheory AlgebraicGeometry TopologicalSpace Order Set

/-- A nonsurjective closed embedding into an irreducible space of
dimension at most one has zero-dimensional source, including the empty case. -/
theorem topologicalKrullDim_nonpos_of_closedEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [IrreducibleSpace X]
    {f : Y → X} (hf : Topology.IsClosedEmbedding f)
    (hdim : topologicalKrullDim X ≤ 1) (hproper : ¬ Function.Surjective f) :
    topologicalKrullDim Y ≤ 0 := by
  apply krullDim_nonpos_iff_forall_isMin.mpr
  intro Z
  let F := IrreducibleCloseds.map f hf.continuous
  have hF : StrictMono F := IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing
  have hclosed : IsClosed (f '' (Z : Set Y)) := hf.isClosedMap _ Z.isClosed
  have himage : (F Z : Set X) = f '' (Z : Set Y) := by
    simpa only [F, IrreducibleCloseds.coe_map] using hclosed.closure_eq
  rcases krullDim_le_one_iff.mp hdim (F Z) with hmin | hmax
  · intro W hW
    have he := le_antisymm (hF.monotone hW) (hmin (hF.monotone hW))
    exact le_of_eq ((IrreducibleCloseds.map_injective_of_isInducing hf.isInducing) he).symm
  · exfalso
    apply hproper
    intro x
    let T : IrreducibleCloseds X := ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
    have hz : T ≤ F Z := hmax (show F Z ≤ T from subset_univ _)
    have hx : x ∈ (F Z : Set X) := hz (show x ∈ T from trivial)
    rw [himage] at hx
    obtain ⟨y, _, hy⟩ := hx
    exact ⟨y, hy⟩

/-- An actual closed subscheme omitting the generic point of an integral
scheme of dimension at most one has topological dimension at most zero. -/
theorem closedSubscheme_dimension_nonpos
    {X Y : Scheme} [IsIntegral X] (i : Y ⟶ X) [IsClosedImmersion i]
    (hdim : topologicalKrullDim X ≤ 1)
    (hgeneric : genericPoint X ∉ Set.range i) : topologicalKrullDim Y ≤ 0 := by
  apply topologicalKrullDim_nonpos_of_closedEmbedding i.isClosedEmbedding hdim
  intro hsurj
  exact hgeneric (hsurj (genericPoint X))

end Normalizer
