import Normalizer.MatrixTransport
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.Basic

/-! Canonical scalar extension of matrices, linear lifts, and scalar-valued
characters. The extension space is the actual tensor product. -/

namespace Normalizer
open TensorProduct

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/-- The canonical identification of the scalar extension of three-by-three
matrices with matrices over the extension field. -/
noncomputable def matrixScalarExtension : K ⊗[F] Mat F ≃ₗ[K] Mat K :=
  (LinearEquiv.baseChange F K (Mat F) (Fin 3 → Fin 3 → F)
    (Matrix.ofLinearEquiv F).symm).trans
    ((TensorProduct.piRight F K K (fun _ : Fin 3 => Fin 3 → F)).trans
      ((LinearEquiv.piCongrRight fun _ => TensorProduct.piScalarRight F K K (Fin 3)).trans
        (Matrix.ofLinearEquiv K)))

variable {F K}

theorem matrixScalarExtension_tmul (a : K) (X : Mat F) :
    matrixScalarExtension F K (a ⊗ₜ[F] X) = a • X.map (algebraMap F K) := by
  ext i j
  simp [matrixScalarExtension, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply,
    Algebra.smul_def, mul_comm]

theorem matrix_map_trace (X : Mat F) :
    Matrix.trace (X.map (algebraMap F K)) = algebraMap F K (Matrix.trace X) := by
  exact (AddMonoidHom.map_trace (algebraMap F K) X).symm

theorem matrix_map_comm (X Y : Mat F) :
    (comm X Y).map (algebraMap F K) =
      comm (X.map (algebraMap F K)) (Y.map (algebraMap F K)) := by
  exact map_sub ((algebraMap F K).mapMatrix) (X * Y) (Y * X) |>.trans (by
    simp only [map_mul, comm, RingHom.mapMatrix_apply])

theorem matrix_map_smul (a : F) (X : Mat F) :
    (a • X).map (algebraMap F K) = algebraMap F K a • X.map (algebraMap F K) := by
  ext i j
  simp

theorem matrix_map_ne_zero (m : Mat F) (hm : m ≠ 0) :
    m.map (algebraMap F K) ≠ 0 := by
  intro h
  apply hm
  ext i j
  exact (algebraMap F K).injective (by simpa using congrFun (congrFun h i) j)

variable {W : Type*} [AddCommGroup W] [Module F W]

/-- The scalar extension of a matrix-valued linear lift. -/
noncomputable def matrixBaseChange (K : Type*) [Field K] [Algebra F K]
    (J : W →ₗ[F] Mat F) : K ⊗[F] W →ₗ[K] Mat K :=
  (matrixScalarExtension F K).toLinearMap.comp (J.baseChange K)

/-- The scalar extension of the actual scalar-valued character. -/
noncomputable def characterBaseChange (K : Type*) [Field K] [Algebra F K]
    (χ : W →ₗ[F] F) : K ⊗[F] W →ₗ[K] K :=
  (TensorProduct.AlgebraTensorModule.rid F K K).toLinearMap.comp (χ.baseChange K)

theorem matrixBaseChange_tmul (J : W →ₗ[F] Mat F) (a : K) (x : W) :
    matrixBaseChange K J (a ⊗ₜ[F] x) = a • (J x).map (algebraMap F K) := by
  simp [matrixBaseChange, matrixScalarExtension_tmul]

theorem characterBaseChange_tmul (χ : W →ₗ[F] F) (a : K) (x : W) :
    characterBaseChange K χ (a ⊗ₜ[F] x) = a * algebraMap F K (χ x) := by
  simp [characterBaseChange, Algebra.smul_def, mul_comm]

/-- Extension of the ground field preserves the dimension of the source
of quotient lifts. -/
theorem boundaryLift_baseChange_finrank :
    Module.finrank K (K ⊗[F] W) = Module.finrank F W :=
  Module.finrank_baseChange

/-- Independence modulo the distinguished line is preserved by the actual
tensor extension. This follows from flatness applied to the quotient map. -/
theorem matrixBaseChange_independent_mod_line (m : Mat F)
    (J : W →ₗ[F] Mat F)
    (hinj : ∀ x, (∃ z : F, J x = z • m) → x = 0)
    (x : K ⊗[F] W)
    (hx : ∃ z : K, matrixBaseChange K J x = z • m.map (algebraMap F K)) : x = 0 := by
  let q := (Submodule.span F {m}).mkQ
  have hi : Function.Injective (q.comp J) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    apply hinj w
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero _).mp hw)
    exact ⟨z, hz.symm⟩
  have hbi : Function.Injective ((q.comp J).baseChange K) :=
    Module.Flat.lTensor_preserves_injective_linearMap (q.comp J) hi
  obtain ⟨z, hz⟩ := hx
  have hJ : J.baseChange K x = z ⊗ₜ[F] m := by
    apply (matrixScalarExtension F K).injective
    simpa [matrixBaseChange, matrixScalarExtension_tmul] using hz
  apply hbi
  rw [map_zero, LinearMap.baseChange_comp, LinearMap.comp_apply, hJ,
    LinearMap.baseChange_tmul]
  have hqm : q m = 0 := (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.mem_span_singleton_self m)
  simp [hqm]

end Normalizer
