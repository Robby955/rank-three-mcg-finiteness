import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! A unit coordinate determinant constructs the actual coefficient-to-vector
equivalence over a commutative ring. -/

noncomputable section
namespace Normalizer
open Module

universe u v w
variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- The columns are the coordinates of the proposed frame vectors. -/
def frameCoordinateMatrix (b : Basis ι R M) (v : ι → M) : Matrix ι ι R :=
  fun i j => b.repr (v j) i

/-- The coordinate matrix represents the actual finite linear-combination map. -/
theorem frameCoordinateMatrix_toMatrix (b : Basis ι R M) (v : ι → M) :
    LinearMap.toMatrix (Pi.basisFun R ι) b (Fintype.linearCombination R v) =
      frameCoordinateMatrix b v := by
  ext i j
  simp [LinearMap.toMatrix_apply, Pi.basisFun_apply, frameCoordinateMatrix]

/-- An invertible coordinate determinant constructs an equivalence, including its inverse. -/
def determinantFrameEquiv (b : Basis ι R M) (v : ι → M)
    (h : IsUnit (frameCoordinateMatrix b v).det) : (ι → R) ≃ₗ[R] M :=
  LinearEquiv.ofIsUnitDet (v := Pi.basisFun R ι) (v' := b)
    (f := Fintype.linearCombination R v) (by rwa [frameCoordinateMatrix_toMatrix])

/-- The constructed equivalence sends coefficients to their actual linear combination. -/
theorem determinantFrameEquiv_apply (b : Basis ι R M) (v : ι → M)
    (h : IsUnit (frameCoordinateMatrix b v).det) (a : ι → R) :
    determinantFrameEquiv b v h a = ∑ i, a i • v i :=
  rfl

/-- Unit determinant is equivalent to bijectivity of the actual coefficient map. -/
theorem frameCoordinateMatrix_isUnit_det_iff (b : Basis ι R M) (v : ι → M) :
    IsUnit (frameCoordinateMatrix b v).det ↔
      Function.Bijective (Fintype.linearCombination R v) := by
  constructor
  · intro h
    exact (determinantFrameEquiv b v h).bijective
  · intro h
    have hd := (LinearEquiv.ofBijective (Fintype.linearCombination R v) h).isUnit_det
      (Pi.basisFun R ι) b
    change IsUnit (LinearMap.toMatrix (Pi.basisFun R ι) b
      (Fintype.linearCombination R v)).det at hd
    rwa [frameCoordinateMatrix_toMatrix] at hd

/-- Whether the determinant is a unit does not depend on the reference basis. -/
theorem frameCoordinateMatrix_isUnit_det_basis_iff
    (b c : Basis ι R M) (v : ι → M) :
    IsUnit (frameCoordinateMatrix b v).det ↔ IsUnit (frameCoordinateMatrix c v).det := by
  rw [frameCoordinateMatrix_isUnit_det_iff, frameCoordinateMatrix_isUnit_det_iff]

/-- At a local ring, the actual coefficient map is bijective precisely when the
coordinate determinant remains nonzero in the residue field. -/
theorem frameCoordinateMatrix_residue_det_ne_zero_iff [IsLocalRing R]
    (b : Basis ι R M) (v : ι → M) :
    ((frameCoordinateMatrix b v).map (IsLocalRing.residue R)).det ≠ 0 ↔
      Function.Bijective (Fintype.linearCombination R v) := by
  change ((IsLocalRing.residue R).mapMatrix (frameCoordinateMatrix b v)).det ≠ 0 ↔ _
  rw [← RingHom.map_det, IsLocalRing.residue_ne_zero_iff_isUnit,
    frameCoordinateMatrix_isUnit_det_iff]

end Normalizer
