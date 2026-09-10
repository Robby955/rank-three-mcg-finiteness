import Normalizer.MatrixTransport
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Basis

/-! Explicit normal form for a nonzero square-zero three-by-three matrix. -/

namespace Normalizer

open Module

variable {F : Type*} [Field F]

/-- A nonzero square-zero endomorphism of a three-dimensional space has a
basis consisting of one length-two chain and one additional kernel vector. -/
theorem square_zero_three_basis (f : Module.End F (Fin 3 → F)) (hf : f ≠ 0)
    (hf2 : f ^ 2 = 0) :
    ∃ b : Basis (Fin 3) F (Fin 3 → F),
      f (b 0) = 0 ∧ f (b 1) = b 0 ∧ f (b 2) = 0 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra! h
    exact hf (LinearMap.ext h)
  have hff (x : Fin 3 → F) : f (f x) = 0 := by
    have h := LinearMap.congr_fun hf2 x
    simpa [pow_two, Module.End.mul_apply] using h
  have hle : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨x, rfl⟩
    exact hff x
  have hdim := f.finrank_range_add_finrank_ker
  have hdimle := Submodule.finrank_mono hle
  have hker : 2 ≤ Module.finrank F (LinearMap.ker f) := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
    omega
  obtain ⟨w, hw, hwu⟩ : ∃ w, w ∈ LinearMap.ker f ∧ w ∉ Submodule.span F {f v} := by
    by_contra! h
    have hle' : LinearMap.ker f ≤ Submodule.span F {f v} := h
    have hd := Submodule.finrank_mono hle'
    rw [finrank_span_singleton hv] at hd
    omega
  have hfw : f w = 0 := hw
  have huw : LinearIndependent F ![f v, w] := by
    apply (LinearIndependent.pair_iff' hv).mpr
    intro a ha
    apply hwu
    rw [← ha]
    exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self (f v))
  have hli : LinearIndependent F ![f v, v, w] := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have hc' : c 0 • f v + c 1 • v + c 2 • w = 0 := by
      simpa [Fin.sum_univ_succ, add_assoc] using hc
    have hc1 : c 1 = 0 := by
      have hcf := congrArg f hc'
      have hsmul : c 1 • f v = 0 := by simpa [hff, hfw] using hcf
      exact (smul_eq_zero.mp hsmul).resolve_right hv
    have hcuw : ∑ j : Fin 2, (![c 0, c 2] : Fin 2 → F) j • (![f v, w] : Fin 2 → (Fin 3 → F)) j = 0 := by
      simpa [Fin.sum_univ_succ, hc1] using hc'
    have hc0 : c 0 = 0 := by
      simpa using Fintype.linearIndependent_iff.mp huw ![c 0, c 2] hcuw 0
    have hc2 : c 2 = 0 := by
      simpa using Fintype.linearIndependent_iff.mp huw ![c 0, c 2] hcuw 1
    fin_cases i <;> assumption
  let b : Basis (Fin 3) F (Fin 3 → F) := basisOfPiSpaceOfLinearIndependent hli
  refine ⟨b, ?_, ?_, ?_⟩
  · simpa [b] using hff v
  · simp [b]
  · simpa [b] using hfw

/-- Every nonzero square-zero three-by-three matrix is conjugate to the
checked minimal-nilpotent model. -/
theorem square_zero_conjugate_nil (m : Mat F) (hm : m ≠ 0) (hm2 : m ^ 2 = 0) :
    ∃ P : (Mat F)ˣ, matrixConjugation P m = nilM := by
  classical
  let f : Module.End F (Fin 3 → F) := Matrix.toLin' m
  have hf : f ≠ 0 := by simpa [f] using hm
  have hf2 : f ^ 2 = 0 := by
    have he : Matrix.toLinAlgEquiv' m = Matrix.toLin' m := by ext v i; rfl
    simpa [f, he] using congrArg
      (Matrix.toLinAlgEquiv' : Mat F ≃ₐ[F] Module.End F (Fin 3 → F)) hm2
  obtain ⟨b, hb0, hb1, hb2⟩ := square_zero_three_basis f hf hf2
  have hbmat : LinearMap.toMatrix b b f = nilM := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, hb0, hb1, hb2, nilM]
  let s : Basis (Fin 3) F (Fin 3 → F) := Pi.basisFun F (Fin 3)
  let P : (Mat F)ˣ :=
    ⟨b.toMatrix s, s.toMatrix b, b.toMatrix_mul_toMatrix_flip s, s.toMatrix_mul_toMatrix_flip b⟩
  refine ⟨P, ?_⟩
  change b.toMatrix s * m * s.toMatrix b = nilM
  have hm' : m = LinearMap.toMatrix s s f := by simp [s, f]
  rw [hm', basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  exact hbmat

/-- A square-zero three-by-three matrix has zero trace, also in positive
characteristic. -/
theorem square_zero_trace (m : Mat F) (hm2 : m ^ 2 = 0) : Matrix.trace m = 0 := by
  by_cases hm : m = 0
  · simp [hm]
  obtain ⟨P, hP⟩ := square_zero_conjugate_nil m hm hm2
  have ht := congrArg Matrix.trace hP
  rw [matrixConjugation_trace] at ht
  simpa [nilM, Matrix.trace, Fin.sum_univ_succ] using ht

/-- A traceless matrix whose scalar shift is square-zero has zero shift in
characteristic zero. -/
theorem traceless_shift_square_zero [CharZero F] (m : Mat F) (a : F)
    (htr : Matrix.trace m = 0) (hshift : (m - a • 1) ^ 2 = 0) : a = 0 := by
  have ht := square_zero_trace (m - a • 1) hshift
  have h3 : (3 : F) ≠ 0 := by norm_num
  simpa [htr, h3] using ht

/-- The checked minimal-nilpotent obstruction applies to every nonzero
square-zero three-by-three matrix. -/
theorem square_zero_matrix_boundary_lift [CharZero F]
    {W : Type*} [AddCommGroup W] [Module F W]
    (m : Mat F) (hm : m ≠ 0) (hm2 : m ^ 2 = 0)
    (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F)
    (h : MatrixBoundaryLift m J χ) : Module.finrank F W < 3 := by
  obtain ⟨P, hP⟩ := square_zero_conjugate_nil m hm hm2
  exact conjugate_nil_matrix_boundary_lift m P 1 one_ne_zero (by simpa using hP) J χ h

end Normalizer
