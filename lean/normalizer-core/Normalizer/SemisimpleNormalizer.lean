import Normalizer.DiagonalNormalizer
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Trace

namespace Normalizer
open Module
variable {F : Type*} [Field F]

/-- A spanning family of eigenspaces yields an eigenvector basis with exactly
three elements in dimension three. -/
theorem eigenbasis_three (f : Module.End F (Fin 3 → F))
    (hf : ⨆ a : F, f.eigenspace a = ⊤) :
    ∃ (b : Basis (Fin 3) F (Fin 3 → F)) (d : Fin 3 → F),
      ∀ i, f (b i) = d i • b i := by
  classical
  let s : Set (Fin 3 → F) := {v | ∃ a : F, f v = a • v}
  have hs : ⊤ ≤ Submodule.span F s := by
    rw [← hf]
    apply iSup_le
    intro a v hv
    apply Submodule.subset_span
    exact ⟨a, Module.End.mem_eigenspace_iff.mp hv⟩
  let ι : Type _ := ↥((linearIndepOn_empty F (id : (Fin 3 → F) → (Fin 3 → F))).extend (Set.empty_subset s))
  let b : Basis ι F (Fin 3 → F) := Basis.ofSpan hs
  let := Module.Finite.finite_basis b
  let := Fintype.ofFinite ι
  have hc : Fintype.card ι = 3 := by
    simpa using (Module.finrank_eq_card_basis b).symm
  let e : ι ≃ Fin 3 := Fintype.equivFinOfCardEq hc
  let b' := b.reindex e
  have hb (i : Fin 3) : ∃ a : F, f (b' i) = a • b' i := by
    exact Basis.ofSpan_subset hs ⟨e.symm i, (b.reindex_apply e i).symm⟩
  choose d hd using hb
  exact ⟨b', d, hd⟩

/-- Expressing a matrix in a chosen basis preserves its algebra operations. -/
noncomputable def matrixInBasis (b : Basis (Fin 3) F (Fin 3 → F)) : Mat F ≃ₐ[F] Mat F :=
  Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv b)

theorem matrixInBasis_trace (b : Basis (Fin 3) F (Fin 3 → F)) (X : Mat F) :
    Matrix.trace (matrixInBasis b X) = Matrix.trace X := by
  change Matrix.trace (LinearMap.toMatrix b b (Matrix.toLin' X)) = _
  rw [← LinearMap.trace_eq_matrix_trace F b, Matrix.trace_toLin'_eq]

theorem matrixInBasis_comm (b : Basis (Fin 3) F (Fin 3 → F)) (X Y : Mat F) :
    matrixInBasis b (comm X Y) = comm (matrixInBasis b X) (matrixInBasis b Y) := by
  simp only [comm, map_sub, map_mul]

/-- Eigenvector basis data identifies the transformed matrix with the actual
diagonal matrix of the listed eigenvalues. -/
theorem matrixInBasis_diagonal (b : Basis (Fin 3) F (Fin 3 → F))
    (m : Mat F) (d : Fin 3 → F)
    (hb : ∀ i, Matrix.toLin' m (b i) = d i • b i) :
    matrixInBasis b m = Matrix.diagonal d := by
  ext i j
  change LinearMap.toMatrixAlgEquiv b (Matrix.toLin' m) i j = _
  rw [LinearMap.toMatrixAlgEquiv_apply, hb j, map_smul]
  by_cases hij : i = j
  · subst j; simp
  · simp [Matrix.diagonal, hij]

variable [CharZero F]
variable {W : Type*} [AddCommGroup W] [Module F W]

/-- The obstruction for every matrix whose eigenspaces span the ambient space. -/
theorem diagonalizable_matrix_boundary_lift (m : Mat F) (hm : m ≠ 0)
    (ht : Matrix.trace m = 0) (hf : ⨆ a : F, Module.End.eigenspace (Matrix.toLin' m) a = ⊤)
    (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F)
    (h : MatrixBoundaryLift m J χ) : Module.finrank F W < 3 := by
  obtain ⟨b, d, hb⟩ := eigenbasis_three (Matrix.toLin' m) hf
  have he := matrixInBasis_diagonal b m d hb
  have hdt : Matrix.trace (Matrix.diagonal d) = 0 := by
    rw [← he, matrixInBasis_trace, ht]
  have hdn : Matrix.diagonal d ≠ 0 := by
    rw [← he]
    exact (map_ne_zero_iff (matrixInBasis b) (matrixInBasis b).injective).mpr hm
  apply diagonal_matrix_boundary_lift d hdt hdn _ χ
  exact matrix_boundary_lift_transport m _ (matrixInBasis b).toLinearEquiv
    (matrixInBasis_trace b) (matrixInBasis_comm b) 1 one_ne_zero (by simpa using he) J χ h

/-- Over an algebraically closed field, every semisimple nonzero traceless
matrix satisfies the same quotient obstruction. -/
theorem semisimple_matrix_boundary_lift [IsAlgClosed F]
    (m : Mat F) (hm : m ≠ 0) (ht : Matrix.trace m = 0)
    (hs : Module.End.IsSemisimple (Matrix.toLin' m))
    (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F)
    (h : MatrixBoundaryLift m J χ) : Module.finrank F W < 3 := by
  exact diagonalizable_matrix_boundary_lift m hm ht hs.iSup_eigenspace_eq_top J χ h

end Normalizer
