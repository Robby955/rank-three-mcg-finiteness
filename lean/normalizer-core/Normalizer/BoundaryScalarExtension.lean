import Normalizer.MatrixScalarExtension
import Normalizer.TracelessNormalizer
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.Module

/-! Extension of the normalizer action and boundary law to an actual tensor
product, followed by the obstruction over any characteristic-zero field. -/

namespace Normalizer
open TensorProduct
variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable {W : Type*} [AddCommGroup W] [Module F W]

private theorem comm_add_left (X Y Z : Mat K) :
    comm (X + Y) Z = comm X Z + comm Y Z := by
  simp only [comm, add_mul, mul_add]
  abel

private theorem comm_add_right (X Y Z : Mat K) :
    comm X (Y + Z) = comm X Y + comm X Z := by
  simp only [comm, add_mul, mul_add]
  abel

private theorem comm_smul_left (a : K) (X Y : Mat K) :
    comm (a • X) Y = a • comm X Y := by simp [comm, smul_sub]

private theorem comm_smul_right (a : K) (X Y : Mat K) :
    comm X (a • Y) = a • comm X Y := by simp [comm, smul_sub]

/-- Trace-zero lifts remain trace zero on the entire scalar extension. -/
theorem matrixBaseChange_trace (J : W →ₗ[F] Mat F)
    (ht : ∀ x, Matrix.trace (J x) = 0) (x : K ⊗[F] W) :
    Matrix.trace (matrixBaseChange K J x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [matrixBaseChange_tmul, matrix_map_trace, ht]
  | add x y hx hy => simp [hx, hy]

/-- The extended character is the actual scalar action on the extended line. -/
theorem matrixBaseChange_action (m : Mat F) (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F)
    (ha : ∀ x, comm (J x) m = χ x • m) (x : K ⊗[F] W) :
    comm (matrixBaseChange K J x) (m.map (algebraMap F K)) =
      characterBaseChange K χ x • m.map (algebraMap F K) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [comm]
  | tmul a x =>
    rw [matrixBaseChange_tmul, characterBaseChange_tmul, comm_smul_left,
      ← matrix_map_comm, ha x, matrix_map_smul, smul_smul]
  | add x y hx hy => simp only [map_add, comm_add_left, hx, hy, add_smul]

/-- Bilinearity extends the boundary identity from the original vectors to
all tensors; the coefficient on pure tensors becomes a*b times the image
of the original coefficient. -/
theorem matrixBaseChange_boundary (m : Mat F) (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F)
    (hl : ∀ x y, ∃ z : F,
      comm (J x) (J y) = χ x • J y - χ y • J x + z • m) :
    ∀ x y : K ⊗[F] W, ∃ z : K,
      comm (matrixBaseChange K J x) (matrixBaseChange K J y) =
        characterBaseChange K χ x • matrixBaseChange K J y -
        characterBaseChange K χ y • matrixBaseChange K J x +
        z • m.map (algebraMap F K) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => intro y; exact ⟨0, by simp [comm]⟩
  | tmul a x =>
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [comm]⟩
    | tmul b y =>
      obtain ⟨z, hz⟩ := hl x y
      have he : comm ((J x).map (algebraMap F K)) ((J y).map (algebraMap F K)) =
          algebraMap F K (χ x) • (J y).map (algebraMap F K) -
          algebraMap F K (χ y) • (J x).map (algebraMap F K) +
          algebraMap F K z • m.map (algebraMap F K) := by
        rw [← matrix_map_comm, hz]
        change (algebraMap F K).mapMatrix (_ - _ + _) = _
        rw [map_add, map_sub]
        simp only [RingHom.mapMatrix_apply, matrix_map_smul]
      refine ⟨a * b * algebraMap F K z, ?_⟩
      rw [matrixBaseChange_tmul, matrixBaseChange_tmul,
        characterBaseChange_tmul, characterBaseChange_tmul,
        comm_smul_left, comm_smul_right, he]
      module
    | add y z hy hz =>
      obtain ⟨c, hc⟩ := hy
      obtain ⟨d, hd⟩ := hz
      refine ⟨c + d, ?_⟩
      simp only [map_add, comm_add_right, hc, hd]
      module
  | add x y hx hy =>
    intro z
    obtain ⟨c, hc⟩ := hx z
    obtain ⟨d, hd⟩ := hy z
    refine ⟨c + d, ?_⟩
    simp only [map_add, comm_add_left, hc, hd]
    module

/-- Every hypothesis in the quotient-lift interface survives arbitrary
extension of fields, including its independence modulo the line. -/
theorem matrixBoundaryLift_baseChange (m : Mat F)
    (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F) (h : MatrixBoundaryLift m J χ) :
    MatrixBoundaryLift (m.map (algebraMap F K))
      (matrixBaseChange K J) (characterBaseChange K χ) := by
  exact ⟨matrixBaseChange_trace J h.1,
    matrixBaseChange_action m J χ h.2.1,
    matrixBaseChange_boundary m J χ h.2.2.1,
    matrixBaseChange_independent_mod_line m J h.2.2.2⟩

/-- The exhaustive obstruction over any characteristic-zero field. The
proof constructs the scalar extension to an algebraic closure and preserves
the original dimension, rather than assuming algebraic closedness. -/
theorem traceless_matrix_boundary_lift_any_field [CharZero F]
    (m : Mat F) (hm : m ≠ 0) (ht : Matrix.trace m = 0)
    (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F) (h : MatrixBoundaryLift m J χ) :
    Module.finrank F W < 3 := by
  let K := AlgebraicClosure F
  have h' := matrixBoundaryLift_baseChange (K := K) m J χ h
  have hm' := matrix_map_ne_zero (K := K) m hm
  have ht' : Matrix.trace (m.map (algebraMap F K)) = 0 := by
    rw [matrix_map_trace, ht, map_zero]
  have hd := traceless_matrix_boundary_lift _ hm' ht' _ _ h'
  rwa [boundaryLift_baseChange_finrank] at hd

end Normalizer
