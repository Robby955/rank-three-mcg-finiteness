import Normalizer.DeterminantFrame
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-! The actual top exterior product has the determinant coefficient in
any reference basis. This supplies the local formula for determinant sections. -/

noncomputable section
namespace Normalizer
open Module
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {n : ℕ}

/-- The top exterior product of a family is its coordinate determinant
times the top exterior product of the reference basis. -/
theorem topWedge_eq_det_smul (b : Basis (Fin n) R M) (v : Fin n → M) :
    exteriorPower.ιMulti R n v =
      (frameCoordinateMatrix b v).det • exteriorPower.ιMulti R n b := by
  have h : exteriorPower.ιMulti R n =
      b.det.smulRight (exteriorPower.ιMulti R n b) := by
    apply b.ext_alternating
    intro i hi
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change exteriorPower.ιMulti R n (b ∘ σ) = b.det (b ∘ σ) • exteriorPower.ιMulti R n b
    simp [AlternatingMap.map_perm, Basis.det_self, smul_assoc]
  have hv := congrArg (fun f => f v) h
  change exteriorPower.ιMulti R n v = b.det v • exteriorPower.ιMulti R n b at hv
  exact hv

end Normalizer
