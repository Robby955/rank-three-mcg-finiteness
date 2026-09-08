import Mathlib.LinearAlgebra.Contraction

/-! The canonical tensor-Hom comparison for a genuinely trivialized rank-one
module. The target module is arbitrary; no freeness or finiteness is assumed. -/

noncomputable section

namespace Normalizer

open TensorProduct

universe u v w

variable (R : Type u) (M : Type v) (G : Type w)
  [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup G] [Module R G]

/-- Canonical evaluation, with the target factor preceding the dual factor. -/
def tensorHomEval : G ⊗[R] (M →ₗ[R] R) →ₗ[R] (M →ₗ[R] G) :=
  dualTensorHom R M G ∘ₗ (TensorProduct.comm R G (M →ₗ[R] R)).toLinearMap

@[simp]
theorem tensorHomEval_tmul (g : G) (φ : M →ₗ[R] R) (m : M) :
    tensorHomEval R M G (g ⊗ₜ[R] φ) m = φ m • g := rfl

variable {R M G}

/-- Every vector has its actual coordinate in a chosen rank-one trivialization. -/
theorem line_coordinate (e : M ≃ₗ[R] R) (m : M) :
    e m • e.symm 1 = m := by
  apply e.injective
  simp

/-- Every linear functional is a scalar multiple of the chosen coordinate. -/
theorem line_dual_coordinate (e : M ≃ₗ[R] R) (φ : M →ₗ[R] R) :
    φ (e.symm 1) • e.toLinearMap = φ := by
  ext m
  have h := congrArg φ (line_coordinate e m)
  simpa only [map_smul, smul_eq_mul, LinearMap.smul_apply,
    LinearEquiv.coe_coe, mul_comm] using h

/-- Explicit inverse to canonical evaluation in a rank-one trivialization. -/
def lineTensorHomInv (e : M ≃ₗ[R] R) :
    (M →ₗ[R] G) →ₗ[R] G ⊗[R] (M →ₗ[R] R) where
  toFun f := f (e.symm 1) ⊗ₜ[R] e.toLinearMap
  map_add' f g := by simp [add_tmul]
  map_smul' r f := by simp [smul_tmul']

@[simp]
theorem lineTensorHomInv_apply (e : M ≃ₗ[R] R) (f : M →ₗ[R] G) :
    lineTensorHomInv e f = f (e.symm 1) ⊗ₜ[R] e.toLinearMap := rfl

theorem tensorHomEval_lineTensorHomInv (e : M ≃ₗ[R] R) (f : M →ₗ[R] G) :
    tensorHomEval R M G (lineTensorHomInv e f) = f := by
  ext m
  change e m • f (e.symm 1) = f m
  rw [← f.map_smul, line_coordinate]

theorem lineTensorHomInv_tensorHomEval (e : M ≃ₗ[R] R)
    (t : G ⊗[R] (M →ₗ[R] R)) :
    lineTensorHomInv e (tensorHomEval R M G t) = t := by
  induction t with
  | zero => simp
  | tmul g φ =>
    change (φ (e.symm 1) • g) ⊗ₜ[R] e.toLinearMap = g ⊗ₜ[R] φ
    rw [smul_tmul, line_dual_coordinate]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The canonical tensor-Hom map is an equivalence for a rank-one module.
Only the inverse construction uses the chosen trivialization. -/
def lineTensorHomEquiv (e : M ≃ₗ[R] R) :
    G ⊗[R] (M →ₗ[R] R) ≃ₗ[R] (M →ₗ[R] G) :=
  { tensorHomEval R M G with
    invFun := lineTensorHomInv e
    left_inv := lineTensorHomInv_tensorHomEval e
    right_inv := tensorHomEval_lineTensorHomInv e }

@[simp]
theorem lineTensorHomEquiv_toLinearMap (e : M ≃ₗ[R] R) :
    (lineTensorHomEquiv (G := G) e).toLinearMap = tensorHomEval R M G := rfl

@[simp]
theorem lineTensorHomEquiv_symm_apply (e : M ≃ₗ[R] R) (f : M →ₗ[R] G) :
    (lineTensorHomEquiv e).symm f = f (e.symm 1) ⊗ₜ[R] e.toLinearMap := rfl

/-- The isomorphism is independent of the chosen rank-one trivialization. -/
theorem lineTensorHomEquiv_eq (e e' : M ≃ₗ[R] R) :
    lineTensorHomEquiv (G := G) e = lineTensorHomEquiv e' := by
  apply LinearEquiv.toLinearMap_injective
  rfl

theorem tensorHomEval_injective (e : M ≃ₗ[R] R) :
    Function.Injective (tensorHomEval R M G) :=
  (lineTensorHomEquiv e).injective

theorem tensorHomEval_surjective (e : M ≃ₗ[R] R) :
    Function.Surjective (tensorHomEval R M G) :=
  (lineTensorHomEquiv e).surjective

variable {G' : Type*} [AddCommGroup G'] [Module R G']

/-- Evaluation commutes with an arbitrary linear map on its target. -/
theorem tensorHomEval_natural_target (f : G →ₗ[R] G')
    (t : G ⊗[R] (M →ₗ[R] R)) :
    tensorHomEval R M G' (TensorProduct.map f LinearMap.id t) =
      f.comp (tensorHomEval R M G t) := by
  induction t with
  | zero => ext m; simp
  | tmul g φ => ext m; simp
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.comp_add]

variable {M' : Type*} [AddCommGroup M'] [Module R M']

/-- Evaluation commutes with pullback of the linear functional. -/
theorem tensorHomEval_natural_source (f : M' →ₗ[R] M)
    (t : G ⊗[R] (M →ₗ[R] R)) :
    tensorHomEval R M' G (TensorProduct.map LinearMap.id f.dualMap t) =
      (tensorHomEval R M G t).comp f := by
  induction t with
  | zero => ext m; simp
  | tmul g φ => ext m; simp
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.add_comp]

end Normalizer
