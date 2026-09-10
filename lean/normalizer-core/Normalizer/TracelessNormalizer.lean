import Normalizer.CyclicNormalizer
import Normalizer.SemisimpleNormalizer
import Normalizer.MatrixTrichotomy

/-! Exhaustive obstruction for independent line-normalizer quotient lifts in
the traceless three-by-three matrices over an algebraically closed field. -/

namespace Normalizer

variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
variable {W : Type*} [AddCommGroup W] [Module F W]

/-- Every nonzero traceless three-by-three matrix satisfies the normalizer
boundary obstruction.  The proof derives the exhaustive alternatives and
the required model identifications; neither is an input. -/
theorem traceless_matrix_boundary_lift (m : Mat F) (hm : m ≠ 0)
    (ht : Matrix.trace m = 0) (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F)
    (h : MatrixBoundaryLift m J χ) : Module.finrank F W < 3 := by
  rcases traceless_matrix_trichotomy m ht with hc | hs | hn
  · exact cyclic_matrix_boundary_lift m hm ht hc J χ h
  · exact semisimple_matrix_boundary_lift m hm ht hs J χ h
  · exact square_zero_matrix_boundary_lift m hm hn J χ h

end Normalizer
