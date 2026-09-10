import Normalizer.Flagship
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Matrix representatives of a subspace in an actual line-normalizer quotient.
The independence condition is independence modulo the distinguished line,
not just independence of the chosen matrix representatives. -/

namespace Normalizer
variable {F : Type*} [Field F] [CharZero F]
variable {W : Type*} [AddCommGroup W] [Module F W]

/-- A linear lift of a quotient subspace, its actual scalar action, the
boundary identity modulo the line, and injectivity in the quotient. -/
def MatrixBoundaryLift (m : Mat F) (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F) : Prop :=
  (∀ x, Matrix.trace (J x) = 0) ∧
  (∀ x, comm (J x) m = χ x • m) ∧
  (∀ x y, ∃ z : F,
    comm (J x) (J y) = χ x • J y - χ y • J x + z • m) ∧
  (∀ x, (∃ z : F, J x = z • m) → x = 0)

/-- The semisimple obstruction applied to genuine independent quotient lifts. -/
theorem sem_matrix_boundary_lift (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F)
    (h : MatrixBoundaryLift semM J χ) : Module.finrank F W < 3 := by
  obtain ⟨htr, hact, hlaw, hinj⟩ := h
  let f := semCoordinates.comp J
  have hchar (x : W) : χ x = 0 := by
    obtain ⟨_, _, _, ht⟩ := (sem_normalizer (J x) (χ x)).mp ⟨htr x, hact x⟩
    exact ht
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply hinj x
    let X : lineNormalizer (semM : Mat F) :=
      ⟨J x, (mem_lineNormalizer _ _).mpr ⟨htr x, χ x, hact x⟩⟩
    exact (sem_projection_kernel X).mp hx
  have hboundary : BoundaryLaw f.range semBracket (fun _ => 0) := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    let X : lineNormalizer (semM : Mat F) :=
      ⟨J x, (mem_lineNormalizer _ _).mpr ⟨htr x, χ x, hact x⟩⟩
    let Y : lineNormalizer (semM : Mat F) :=
      ⟨J y, (mem_lineNormalizer _ _).mpr ⟨htr y, χ y, hact y⟩⟩
    obtain ⟨z, hz⟩ := hlaw x y
    have hb := sem_projection_bracket X Y
    have he := congrArg semCoordinates hz
    rw [hchar x, hchar y, zero_smul, zero_smul, sub_self, zero_add] at he
    have hm : semCoordinates (semM : Mat F) = 0 := by
      ext i; fin_cases i <;> simp [semCoordinates, semM]
    rw [map_smul, hm, smul_zero] at he
    simpa [f, X, Y, semProjection, LinearMap.comp_apply] using hb.symm.trans he
  have hd := sem_no_three f.range hboundary
  rwa [LinearMap.finrank_range_of_inj hf] at hd

/-- The minimal-nilpotent obstruction applied to genuine independent quotient lifts. -/
theorem nil_matrix_boundary_lift (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F)
    (h : MatrixBoundaryLift nilM J χ) : Module.finrank F W < 3 := by
  obtain ⟨htr, hact, hlaw, hinj⟩ := h
  let f := nilCoordinates.comp J
  have hchar (x : W) : χ x = f x 0 := by
    let X : lineNormalizer (nilM : Mat F) :=
      ⟨J x, (mem_lineNormalizer _ _).mpr ⟨htr x, χ x, hact x⟩⟩
    exact nil_projection_character X (χ x) (hact x)
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply hinj x
    let X : lineNormalizer (nilM : Mat F) :=
      ⟨J x, (mem_lineNormalizer _ _).mpr ⟨htr x, χ x, hact x⟩⟩
    exact (nil_projection_kernel X).mp hx
  have hboundary : BoundaryLaw f.range nilBracket (fun v => v 0) := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    let X : lineNormalizer (nilM : Mat F) :=
      ⟨J x, (mem_lineNormalizer _ _).mpr ⟨htr x, χ x, hact x⟩⟩
    let Y : lineNormalizer (nilM : Mat F) :=
      ⟨J y, (mem_lineNormalizer _ _).mpr ⟨htr y, χ y, hact y⟩⟩
    obtain ⟨z, hz⟩ := hlaw x y
    have hb := nil_projection_bracket X Y
    have he := congrArg nilCoordinates hz
    have hm : nilCoordinates (nilM : Mat F) = 0 := by
      ext i; fin_cases i <;> simp [nilCoordinates, nilM]
    simp only [map_add, map_sub, map_smul, hm, smul_zero, add_zero] at he
    simpa [f, X, Y, nilProjection, LinearMap.comp_apply, hchar] using hb.symm.trans he
  have hd := nil_no_three f.range hboundary
  rwa [LinearMap.finrank_range_of_inj hf] at hd

/-- Conjugation by an invertible matrix, with the inverse as part of the data. -/
def matrixConjugation (P : (Mat F)ˣ) : Mat F ≃ₗ[F] Mat F where
  toFun X := (P : Mat F) * X * (↑P⁻¹ : Mat F)
  invFun X := (↑P⁻¹ : Mat F) * X * (P : Mat F)
  left_inv X := by simp [mul_assoc]
  right_inv X := by simp [mul_assoc]
  map_add' X Y := by simp [mul_add, add_mul]
  map_smul' a X := by simp

omit [CharZero F] in
theorem matrixConjugation_trace (P : (Mat F)ˣ) (X : Mat F) :
    Matrix.trace (matrixConjugation P X) = Matrix.trace X :=
  Matrix.trace_units_conj P X

omit [CharZero F] in
theorem matrixConjugation_comm (P : (Mat F)ˣ) (X Y : Mat F) :
    matrixConjugation P (comm X Y) =
      comm (matrixConjugation P X) (matrixConjugation P Y) := by
  simp [matrixConjugation, comm, mul_sub, sub_mul, mul_assoc]

omit [CharZero F] in
/-- A change of basis and a nonzero rescaling of the generator preserve all
four quotient-lift hypotheses, including the same scalar-valued character. -/
theorem matrix_boundary_lift_transport
    (m n : Mat F) (e : Mat F ≃ₗ[F] Mat F)
    (hetr : ∀ X, Matrix.trace (e X) = Matrix.trace X)
    (hebr : ∀ X Y, e (comm X Y) = comm (e X) (e Y))
    (a : F) (ha : a ≠ 0) (hem : e m = a • n)
    (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F)
    (h : MatrixBoundaryLift m J χ) :
    MatrixBoundaryLift n (e.toLinearMap.comp J) χ := by
  obtain ⟨htr, hact, hlaw, hinj⟩ := h
  refine ⟨fun x => (hetr (J x)).trans (htr x), ?_, ?_, ?_⟩
  · intro x
    have h := congrArg e (hact x)
    rw [hebr, map_smul, hem] at h
    have hs (X : Mat F) : comm X (a • n) = a • comm X n := by
      simp [comm, smul_sub]
    rw [hs, smul_comm (χ x) a n] at h
    exact (smul_right_injective _ ha) h
  · intro x y
    obtain ⟨z, hz⟩ := hlaw x y
    refine ⟨z * a, ?_⟩
    have h := congrArg e hz
    rw [hebr, map_add, map_sub, map_smul, map_smul, map_smul, hem, smul_smul] at h
    exact h
  · intro x hx
    obtain ⟨z, hz⟩ := hx
    apply hinj x
    refine ⟨z / a, e.injective ?_⟩
    rw [map_smul, hem, smul_smul, div_mul_cancel₀ z ha]
    exact hz

theorem conjugate_sem_matrix_boundary_lift
    (m : Mat F) (P : (Mat F)ˣ) (a : F) (ha : a ≠ 0)
    (hm : matrixConjugation P m = a • semM)
    (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F)
    (h : MatrixBoundaryLift m J χ) : Module.finrank F W < 3 := by
  exact sem_matrix_boundary_lift _ χ
    (matrix_boundary_lift_transport m semM (matrixConjugation P)
      (matrixConjugation_trace P) (matrixConjugation_comm P) a ha hm J χ h)

theorem conjugate_nil_matrix_boundary_lift
    (m : Mat F) (P : (Mat F)ˣ) (a : F) (ha : a ≠ 0)
    (hm : matrixConjugation P m = a • nilM)
    (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F)
    (h : MatrixBoundaryLift m J χ) : Module.finrank F W < 3 := by
  exact nil_matrix_boundary_lift _ χ
    (matrix_boundary_lift_transport m nilM (matrixConjugation P)
      (matrixConjugation_trace P) (matrixConjugation_comm P) a ha hm J χ h)

omit [CharZero F] in
theorem matrix_reindex_trace (e : Fin 3 ≃ Fin 3) (X : Mat F) :
    Matrix.trace (Matrix.reindexAlgEquiv F F e X) = Matrix.trace X := by
  exact Equiv.sum_comp e.symm (fun i => X i i)

omit [CharZero F] in
theorem matrix_reindex_comm (e : Fin 3 ≃ Fin 3) (X Y : Mat F) :
    Matrix.reindexAlgEquiv F F e (comm X Y) =
      comm (Matrix.reindexAlgEquiv F F e X) (Matrix.reindexAlgEquiv F F e Y) := by
  simp only [comm, map_sub, map_mul]

end Normalizer
