import Normalizer.ProperConstants
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.LinearAlgebra.Dimension.Finite

/-! Global functions on an actual finite scheme over a field form a finite
vector space under the algebra structure induced by its structure morphism.
Their dimension is zero exactly when the scheme is empty. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {k : Type u} [Field k] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (CommRingCat.of k))

/-- The actual base-field algebra structure on global functions. -/
@[instance_reducible]
def schemeGlobalFunctionsAlgebra : Algebra k Γ(Y, ⊤) :=
  (schemeConstantMap p).toAlgebra

/-- The scalar structure is induced by the specified structure morphism. -/
theorem schemeGlobalFunctionsAlgebra_map :
    let := schemeGlobalFunctionsAlgebra p
    algebraMap k Γ(Y, ⊤) = schemeConstantMap p := rfl

/-- A finite scheme morphism induces a finite map on actual global functions. -/
theorem finiteScheme_constantMap_finite [IsFinite p] : (schemeConstantMap p).Finite := by
  apply RingHom.finite_respectsIso.2
    (e := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
  exact p.finite_appTop

/-- Global functions are a finite module for the actual structure-map action. -/
theorem finiteScheme_globalFunctions_finite [IsFinite p] :
    let := schemeGlobalFunctionsAlgebra p
    Module.Finite k Γ(Y, ⊤) := finiteScheme_constantMap_finite p

/-- Over a field, the actual global function module is finite-dimensional. -/
theorem finiteScheme_globalFunctions_finiteDimensional [IsFinite p] :
    let := schemeGlobalFunctionsAlgebra p
    FiniteDimensional k Γ(Y, ⊤) := finiteScheme_globalFunctions_finite p

/-- Nonempty schemes have nontrivial global function rings, as witnessed
by the germ map into a nontrivial local ring at an actual point. -/
theorem schemeGlobalFunctions_nontrivial [Nonempty Y] : Nontrivial Γ(Y, ⊤) := by
  let y : Y := Classical.choice inferInstance
  exact (Y.presheaf.germ ⊤ y trivial).hom.domain_nontrivial

/-- The global function space of a nonempty finite scheme has positive dimension. -/
theorem finiteScheme_globalFunctions_finrank_pos [IsFinite p] [Nonempty Y] :
    let := schemeGlobalFunctionsAlgebra p
    0 < Module.finrank k Γ(Y, ⊤) := by
  let := schemeGlobalFunctionsAlgebra p
  let := finiteScheme_globalFunctions_finite p
  let := schemeGlobalFunctions_nontrivial (Y := Y)
  exact Module.finrank_pos

/-- An empty scheme has only one global regular function. -/
theorem schemeGlobalFunctions_subsingleton_of_isEmpty [IsEmpty Y] :
    Subsingleton Γ(Y, ⊤) := by
  have h : (⊤ : Y.Opens) = ⊥ := by
    ext y
    exact isEmptyElim y
  rw [h]
  infer_instance

/-- For an actual finite scheme over the field, vanishing of the dimension
of its global function space is equivalent to emptiness of the scheme. -/
theorem finiteScheme_globalFunctions_finrank_eq_zero_iff [IsFinite p] :
    let := schemeGlobalFunctionsAlgebra p
    Module.finrank k Γ(Y, ⊤) = 0 ↔ IsEmpty Y := by
  let := schemeGlobalFunctionsAlgebra p
  let := finiteScheme_globalFunctions_finite p
  constructor
  · intro h
    refine ⟨fun y => ?_⟩
    let : Nonempty Y := ⟨y⟩
    exact (Nat.ne_of_gt (finiteScheme_globalFunctions_finrank_pos p)) h
  · intro h
    let := h
    let := schemeGlobalFunctions_subsingleton_of_isEmpty (Y := Y)
    exact Module.finrank_zero_of_subsingleton

end Normalizer
