import Normalizer.Flagship
import Mathlib.Algebra.Lie.Classical

namespace Normalizer
variable {F : Type*} [Field F] [CharZero F]

/-- The semisimple coordinate model is the usual mathlib `sl₂`. -/
def slTwoEquiv : (Fin 3 → F) ≃ₗ[F] LieAlgebra.SpecialLinear.sl (Fin 2) F where
  toFun v := ⟨!![v 0 / 2, v 1; v 2, -(v 0 / 2)], by
    change Matrix.trace (!![v 0 / 2, v 1; v 2, -(v 0 / 2)] : Matrix (Fin 2) (Fin 2) F) = 0
    simp [Matrix.trace, Fin.sum_univ_succ]⟩
  invFun X := ![(X : Matrix (Fin 2) (Fin 2) F) 0 0 - X.val 1 1, X.val 0 1, X.val 1 0]
  left_inv v := by
    ext i; fin_cases i <;> simp
  right_inv X := by
    have h : Matrix.trace (X : Matrix (Fin 2) (Fin 2) F) = 0 := X.property
    simp [Matrix.trace, Fin.sum_univ_succ] at h
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;>
      linear_combination -h / 2
  map_add' v w := by
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' a v := by
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

theorem slTwo_bracket (v w : Fin 3 → F) :
    slTwoEquiv (semBracket v w) = ⁅slTwoEquiv v, slTwoEquiv w⁆ := by
  apply Subtype.ext
  change _ = _ * _ - _ * _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slTwoEquiv, semBracket] <;> ring

noncomputable def semQuotientSlTwoEquiv :
    SemQuotient F ≃ₗ[F] LieAlgebra.SpecialLinear.sl (Fin 2) F :=
  (semQuotientEquiv (F := F)).trans slTwoEquiv

theorem sem_quotient_slTwo_bracket (x y : SemQuotient F) :
    semQuotientSlTwoEquiv (semQuotientBracket x y) =
      ⁅semQuotientSlTwoEquiv x, semQuotientSlTwoEquiv y⁆ := by
  simp only [semQuotientSlTwoEquiv, LinearEquiv.trans_apply, semQuotientBracket,
    LinearEquiv.apply_symm_apply]
  exact slTwo_bracket _ _

end Normalizer
