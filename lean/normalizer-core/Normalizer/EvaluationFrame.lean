import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.Basic

/-! The algebraic interface supplied by a trivial evaluation subbundle.
Its global coordinates lie in the constant field, and its generic frame
is independent. These concrete data imply injectivity of tensor evaluation.
No assertion about arbitrary global sections is made. -/

namespace Normalizer
open TensorProduct

variable {F K W Q : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup W] [Module F W]
  [AddCommGroup Q] [Module K Q] [Module F Q] [IsScalarTower F K Q]

/-- If evaluation has constant coordinates in an independent generic
frame, its canonical tensor lift is the base change of that coordinate map
followed by the frame inclusion. -/
theorem evaluation_lift_eq_of_frame {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ev : W →ₗ[F] Q) (c : W →ₗ[F] (ι → F)) (j : (ι → K) →ₗ[K] Q)
    (he : ∀ w, ev w = j (fun i => algebraMap F K (c w i))) :
    ev.liftBaseChange K = j.comp
      ((TensorProduct.piScalarRight F K K ι).toLinearMap.comp (c.baseChange K)) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a w
  simp only [LinearMap.liftBaseChange_tmul, LinearMap.comp_apply,
    LinearMap.baseChange_tmul, LinearEquiv.coe_coe]
  rw [he]
  rw [← j.map_smul]
  congr 1
  ext i
  simp [Algebra.smul_def, mul_comm]

/-- The generic tensor evaluation is injective when the supplied constant
coordinate map and generic frame are both injective. Flatness is applied to
the coordinate map, not to an arbitrary map into a function-field fibre. -/
theorem evaluation_lift_injective_of_frame {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ev : W →ₗ[F] Q) (c : W →ₗ[F] (ι → F)) (j : (ι → K) →ₗ[K] Q)
    (hc : Function.Injective c) (hj : Function.Injective j)
    (he : ∀ w, ev w = j (fun i => algebraMap F K (c w i))) :
    Function.Injective (ev.liftBaseChange K) := by
  rw [evaluation_lift_eq_of_frame ev c j he]
  exact hj.comp ((TensorProduct.piScalarRight F K K ι).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap c hc))

/-- Under those frame data, the dimension of the actual function-field
evaluation image equals the constant-field dimension of the section space. -/
theorem evaluation_range_finrank_of_frame {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ev : W →ₗ[F] Q) (c : W →ₗ[F] (ι → F)) (j : (ι → K) →ₗ[K] Q)
    (hc : Function.Injective c) (hj : Function.Injective j)
    (he : ∀ w, ev w = j (fun i => algebraMap F K (c w i))) :
    Module.finrank K (ev.liftBaseChange K).range = Module.finrank F W := by
  rw [LinearMap.finrank_range_of_inj (evaluation_lift_injective_of_frame ev c j hc hj he)]
  exact Module.finrank_baseChange

/-- A generic frame may live in an ambient fibre containing the normalizer
quotient. Injectivity of tensor evaluation follows from the frame equation
after any ambient linear map; the target need not itself carry that frame. -/
theorem evaluation_lift_injective_of_composite_frame
    {Z ι : Type*} [AddCommGroup Z] [Module K Z] [Module F Z]
    [IsScalarTower F K Z] [Fintype ι] [DecidableEq ι]
    (ev : W →ₗ[F] Q) (i : Q →ₗ[K] Z)
    (c : W →ₗ[F] (ι → F)) (j : (ι → K) →ₗ[K] Z)
    (hc : Function.Injective c) (hj : Function.Injective j)
    (he : ∀ w, i (ev w) = j (fun a => algebraMap F K (c w a))) :
    Function.Injective (ev.liftBaseChange K) := by
  have hinj := evaluation_lift_injective_of_frame
    ((i.restrictScalars F).comp ev) c j hc hj he
  rw [← LinearMap.liftBaseChange_comp] at hinj
  intro x y h
  apply hinj
  exact congrArg i h

end Normalizer
