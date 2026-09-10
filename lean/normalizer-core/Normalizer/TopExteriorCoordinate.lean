import Normalizer.TopWedgeCoordinates

set_option autoImplicit false

namespace Normalizer

open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {n : ℕ}

/-- The determinant alternating form gives the coordinate of a top exterior vector. -/
noncomputable def topExteriorCoordinate (b : Basis (Fin n) R M) :
    (⋀[R]^n M) →ₗ[R] R :=
  exteriorPower.alternatingMapLinearEquiv b.det

@[simp]
theorem topExteriorCoordinate_ιMulti (b : Basis (Fin n) R M) (v : Fin n → M) :
    topExteriorCoordinate b (exteriorPower.ιMulti R n v) =
      (frameCoordinateMatrix b v).det :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det v

@[simp]
theorem topExteriorCoordinate_basis (b : Basis (Fin n) R M) :
    topExteriorCoordinate b (exteriorPower.ιMulti R n b) = 1 := by
  change exteriorPower.alternatingMapLinearEquiv b.det (exteriorPower.ιMulti R n b) = 1
  simp [Basis.det_self]

/-- Every top exterior vector is its determinant coordinate times the basis wedge. -/
theorem topExteriorCoordinate_expansion (b : Basis (Fin n) R M) (x : ⋀[R]^n M) :
    topExteriorCoordinate b x • exteriorPower.ιMulti R n b = x := by
  have h : (topExteriorCoordinate b).smulRight (exteriorPower.ιMulti R n b) =
      (LinearMap.id : (⋀[R]^n M) →ₗ[R] (⋀[R]^n M)) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change topExteriorCoordinate b (exteriorPower.ιMulti R n v) •
      exteriorPower.ιMulti R n b = exteriorPower.ιMulti R n v
    rw [topExteriorCoordinate_ιMulti]
    exact (topWedge_eq_det_smul b v).symm
  exact DFunLike.congr_fun h x

/-- A basis identifies the actual top exterior power with the coefficient ring. -/
noncomputable def topExteriorCoordinateEquiv (b : Basis (Fin n) R M) :
    (⋀[R]^n M) ≃ₗ[R] R :=
  { topExteriorCoordinate b with
    invFun := fun r => r • exteriorPower.ιMulti R n b
    left_inv := topExteriorCoordinate_expansion b
    right_inv := fun r => by
      change topExteriorCoordinate b (r • exteriorPower.ιMulti R n b) = r
      simp only [map_smul, topExteriorCoordinate_basis, smul_eq_mul, mul_one] }

@[simp]
theorem topExteriorCoordinateEquiv_apply (b : Basis (Fin n) R M) (x : ⋀[R]^n M) :
    topExteriorCoordinateEquiv b x = topExteriorCoordinate b x := rfl

@[simp]
theorem topExteriorCoordinateEquiv_symm_apply (b : Basis (Fin n) R M) (r : R) :
    (topExteriorCoordinateEquiv b).symm r = r • exteriorPower.ιMulti R n b := rfl

end Normalizer
