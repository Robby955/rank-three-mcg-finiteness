import Normalizer.TopExteriorCoordinate
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Nonzero exterior products of specified independent vectors. -/

noncomputable section
namespace Normalizer
open Module

/-- The exterior product of a basis is nonzero over a nontrivial ring. -/
theorem basis_exteriorProduct_ne_zero {R M : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup M] [Module R M] {n : ℕ} (b : Basis (Fin n) R M) :
    exteriorPower.ιMulti R n b ≠ 0 := by
  intro h
  have he := congrArg (topExteriorCoordinate b) h
  exact one_ne_zero (by simpa only [topExteriorCoordinate_basis, map_zero] using he)

/-- Any specified independent finite family has nonzero exterior product.
The ambient vector space need not be finite-dimensional. -/
theorem exteriorProduct_ne_zero_of_linearIndependent {F M : Type*} [Field F]
    [AddCommGroup M] [Module F M] {n : ℕ} (v : Fin n → M)
    (hv : LinearIndependent F v) : exteriorPower.ιMulti F n v ≠ 0 := by
  let W := Submodule.span F (Set.range v)
  let b : Basis (Fin n) F W := Basis.span hv
  have hb := basis_exteriorProduct_ne_zero b
  have hi := exteriorPower.map_injective_field (n := n) (Submodule.subtype_injective W)
  have he : exteriorPower.map n W.subtype (exteriorPower.ιMulti F n b) =
      exteriorPower.ιMulti F n v := by
    rw [exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    exact congrArg Subtype.val (Basis.span_apply hv i)
  intro h
  apply hb
  apply hi
  rw [he, h, map_zero]

end Normalizer
