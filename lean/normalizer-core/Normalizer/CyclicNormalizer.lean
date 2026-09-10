import Normalizer.CyclicVector
import Normalizer.MatrixTransport
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-! The regular, full-minimal-polynomial-degree branch of the line-normalizer
obstruction.  This handles all cyclic traceless `3 × 3` matrices at once. -/

namespace Normalizer

variable {F : Type*} [Field F] [CharZero F]
variable {W : Type*} [AddCommGroup W] [Module F W]

/-- Cyclic nonzero traceless three-by-three matrices have no independent
three-dimensional family of line-normalizer quotient lifts. -/
theorem cyclic_matrix_boundary_lift (m : Mat F) (hm : m ≠ 0)
    (htr : Matrix.trace m = 0) (hd : (minpoly F m).natDegree = 3)
    (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F)
    (h : MatrixBoundaryLift m J χ) : Module.finrank F W < 3 := by
  obtain ⟨hJtr, hact, _, hinj⟩ := h
  have hJinj : Function.Injective J := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    exact hinj x ⟨0, by simpa using hx⟩
  let : FiniteDimensional F W := FiniteDimensional.of_injective J hJinj
  let e : Mat F ≃ₐ[F] Module.End F (Fin 3 → F) := Matrix.toLinAlgEquiv'
  let τ : Module.End F (Fin 3 → F) →ₗ[F] F :=
    (Matrix.traceLinearMap (Fin 3) F F).comp e.symm.toLinearMap
  have he0 : e m ≠ 0 := by simpa using hm
  have hed : (minpoly F (e m)).natDegree = Module.finrank F (Fin 3 → F) := by
    change (minpoly F (Matrix.toLin' m)).natDegree = _
    simpa using hd
  have hτ1 : τ 1 ≠ 0 := by
    simp [τ]
  have hτm : τ (e m) = 0 := by simpa [τ] using htr
  have hτJ : ∀ x, τ ((e.toLinearMap.comp J) x) = 0 := by
    intro x
    simpa [τ] using hJtr x
  have heact : ∀ x, (e.toLinearMap.comp J) x * e m - e m * (e.toLinearMap.comp J) x =
      χ x • e m := by
    intro x
    simpa [comm] using congrArg e (hact x)
  have heinj : ∀ x, (∃ z : F, (e.toLinearMap.comp J) x = z • e m) → x = 0 := by
    rintro x ⟨z, hz⟩
    apply hinj x
    refine ⟨z, e.injective ?_⟩
    simpa using hz
  have hdim := cyclic_normalizer_lift_finrank (e m) he0 hed τ hτ1 hτm
    (e.toLinearMap.comp J) χ hτJ heact heinj
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
  omega

end Normalizer
