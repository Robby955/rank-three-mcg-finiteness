import Normalizer.BoundarySpan
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Extension of the boundary law and its dimension obstruction to a larger field. -/

noncomputable section

namespace Normalizer
open TensorProduct

variable {F Ω V : Type*} [Field F] [Field Ω] [Algebra F Ω]
  [AddCommGroup V] [Module F V]

/-- Extend a scalar-valued character by tensoring and using the tensor right-unit
isomorphism. The resulting map is linear over the larger field. -/
def boundaryCharacterBaseChange (chi : V →ₗ[F] F) : Ω ⊗[F] V →ₗ[Ω] Ω :=
  (AlgebraTensorModule.rid F Ω Ω).toLinearMap.comp (chi.baseChange Ω)

/-- Evaluation of the extended character on pure tensors. -/
theorem boundaryCharacterBaseChange_tmul (chi : V →ₗ[F] F) (a : Ω) (v : V) :
    boundaryCharacterBaseChange (Ω := Ω) chi (a ⊗ₜ[F] v) =
      a * algebraMap F Ω (chi v) := by
  simp [boundaryCharacterBaseChange, Algebra.smul_def, mul_comm]

/-- Evaluation of the extended bracket on pure tensors. -/
theorem boundaryBracketBaseChange_tmul (B : V →ₗ[F] V →ₗ[F] V)
    (a b : Ω) (v w : V) :
    LinearMap.BilinMap.baseChange Ω B (a ⊗ₜ[F] v) (b ⊗ₜ[F] w) = (a * b) ⊗ₜ[F] B v w :=
  LinearMap.BilinMap.baseChange_tmul B a v b w

/-- The boundary law on a subspace persists on the larger-field span of its
actual tensor images. Bracket and character compatibility are proved by the
pure-tensor formulas rather than supplied as assumptions. -/
theorem boundaryLaw_baseChange_span (B : V →ₗ[F] V →ₗ[F] V) (chi : V →ₗ[F] F)
    (U : Submodule F V) (hlaw : BoundaryLaw U (fun v w ↦ B v w) chi) :
    BoundaryLaw (Submodule.span Ω ((fun v : V ↦ (1 : Ω) ⊗ₜ[F] v) '' (U : Set V)))
      (fun v w ↦ LinearMap.BilinMap.baseChange Ω B v w) (boundaryCharacterBaseChange chi) := by
  apply boundaryLaw_span
  rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
  have hvw : B v w = chi v • w - chi w • v := hlaw v hv w hw
  dsimp only
  rw [boundaryBracketBaseChange_tmul, one_mul, hvw,
    TensorProduct.tmul_sub, boundaryCharacterBaseChange_tmul,
    boundaryCharacterBaseChange_tmul, one_mul, one_mul]
  simp only [TensorProduct.tmul_smul, Algebra.smul_def, mul_one,
    TensorProduct.smul_tmul', Algebra.algebraMap_self_apply]

/-- For a family of generators, the extended boundary law holds on precisely
the span whose dimension is preserved by `baseChange_span_finrank`. -/
theorem boundaryLaw_baseChange_span_range {I : Type*} (v : I → V)
    (B : V →ₗ[F] V →ₗ[F] V) (chi : V →ₗ[F] F)
    (hlaw : BoundaryLaw (Submodule.span F (Set.range v)) (fun x y ↦ B x y) chi) :
    BoundaryLaw (Submodule.span Ω (Set.range (fun i ↦ (1 : Ω) ⊗ₜ[F] v i)))
      (fun x y ↦ LinearMap.BilinMap.baseChange Ω B x y) (boundaryCharacterBaseChange chi) := by
  have hsub : Submodule.span Ω (Set.range (fun i ↦ (1 : Ω) ⊗ₜ[F] v i)) ≤
      Submodule.span Ω ((fun w : V ↦ (1 : Ω) ⊗ₜ[F] w) ''
        (Submodule.span F (Set.range v) : Set V)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨v i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  intro x hx y hy
  exact boundaryLaw_baseChange_span B chi _ hlaw x (hsub hx) y (hsub hy)

/-- Independence survives extension to an arbitrary field, by flatness of the
field extension and the genuine tensor map. -/
theorem baseChange_one_tmul_linearIndependent {I : Type*} (v : I → V)
    (hv : LinearIndependent F v) :
    LinearIndependent Ω (fun i ↦ (1 : Ω) ⊗ₜ[F] v i) :=
  Module.Flat.linearIndependent_one_tmul hv

/-- The span of a finite independent family keeps its dimension after extending
the coefficient field, including extension to an algebraic closure. -/
theorem baseChange_span_finrank {I : Type*} [Fintype I] (v : I → V)
    (hv : LinearIndependent F v) :
    Module.finrank Ω (Submodule.span Ω
      (Set.range (fun i ↦ (1 : Ω) ⊗ₜ[F] v i))) = Fintype.card I :=
  finrank_span_eq_card (baseChange_one_tmul_linearIndependent v hv)

end Normalizer
