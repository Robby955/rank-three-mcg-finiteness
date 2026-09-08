import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace Normalizer
variable {F : Type*} [Field F] [CharZero F]

abbrev Mat (F : Type*) := Matrix (Fin 3) (Fin 3) F

def comm (X Y : Mat F) : Mat F := X * Y - Y * X
def semM : Mat F := !![1, 0, 0; 0, 1, 0; 0, 0, -2]
def nilM : Mat F := !![0, 1, 0; 0, 0, 0; 0, 0, 0]

/-- Coordinates on the semisimple quotient in the basis `D,E12,E21`. -/
def semLift (v : Fin 3 → F) : Mat F :=
  !![v 0 / 2, v 1, 0; v 2, -(v 0 / 2), 0; 0, 0, 0]

/-- Coordinates on the minimal quotient in the basis `D,H,P,Q`. -/
def nilLift (v : Fin 4 → F) : Mat F :=
  !![(v 0 + v 1) / 2, 0, v 2;
     0, (-v 0 + v 1) / 2, 0; 0, v 3, -(v 1)]

def semBracket (v w : Fin 3 → F) : Fin 3 → F :=
  ![2 * (v 1 * w 2 - w 1 * v 2),
    v 0 * w 1 - w 0 * v 1, -(v 0 * w 2 - w 0 * v 2)]

def nilBracket (v w : Fin 4 → F) : Fin 4 → F :=
  ![0, 0,
    ((v 0 + 3 * v 1) * w 2 - (w 0 + 3 * w 1) * v 2) / 2,
    ((v 0 - 3 * v 1) * w 3 - (w 0 - 3 * w 1) * v 3) / 2]

macro "matrix_calc" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [comm, semM, nilM, semLift, nilLift, semBracket, nilBracket,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.smul_apply] <;> ring))

omit [CharZero F] in
theorem semLift_trace (v : Fin 3 → F) : Matrix.trace (semLift v) = 0 := by
  simp [Matrix.trace, semLift, Fin.sum_univ_succ]

theorem nilLift_trace (v : Fin 4 → F) : Matrix.trace (nilLift v) = 0 := by
  simp [Matrix.trace, nilLift, Fin.sum_univ_succ]
  ring

omit [CharZero F] in
theorem sem_action (v : Fin 3 → F) (z : F) :
    comm (semLift v + z • semM) semM = 0 := by matrix_calc

theorem nil_action (v : Fin 4 → F) (z : F) :
    comm (nilLift v + z • nilM) nilM = v 0 • nilM := by matrix_calc

theorem sem_bracket_lift (v w : Fin 3 → F) (a b : F) :
    comm (semLift v + a • semM) (semLift w + b • semM) =
      semLift (semBracket v w) := by matrix_calc

/-- The discarded coefficient is explicitly a multiple of `E12`.
This also proves that the coordinate bracket is independent of lifts. -/
theorem nil_bracket_lift (v w : Fin 4 → F) (a b : F) :
    comm (nilLift v + a • nilM) (nilLift w + b • nilM) =
      nilLift (nilBracket v w) +
        (v 2 * w 3 - w 2 * v 3 + v 0 * b - w 0 * a) • nilM := by
  matrix_calc

/-- Exact semisimple line normalizer, including its character. -/
theorem sem_normalizer (X : Mat F) (t : F) :
    Matrix.trace X = 0 ∧ comm X semM = t • semM ↔
      ∃ v : Fin 3 → F, ∃ z : F, X = semLift v + z • semM ∧ t = 0 := by
  constructor
  · rintro ⟨htr, hc⟩
    have h00 := congrFun (congrFun hc 0) 0
    have h02 := congrFun (congrFun hc 0) 2
    have h12 := congrFun (congrFun hc 1) 2
    have h20 := congrFun (congrFun hc 2) 0
    have h21 := congrFun (congrFun hc 2) 1
    simp [comm, semM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      Matrix.smul_apply] at h00 h02 h12 h20 h21
    simp [Matrix.trace, Fin.sum_univ_succ] at htr
    refine ⟨![X 0 0 - X 1 1, X 0 1, X 1 0], -(X 2 2) / 2, ?_, by simpa using h00.symm⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [semLift, semM] <;>
      first
      | linear_combination htr / 2
      | linear_combination -h02 / 3
      | linear_combination -h12 / 3
      | linear_combination h20 / 3
      | linear_combination h21 / 3
  · rintro ⟨v, z, rfl, rfl⟩
    constructor
    · simp [Matrix.trace, semLift, semM, Fin.sum_univ_succ]
      ring
    · simpa using sem_action v z

/-- Exact minimal-nilpotent line normalizer, including its character. -/
theorem nil_normalizer (X : Mat F) (t : F) :
    Matrix.trace X = 0 ∧ comm X nilM = t • nilM ↔
      ∃ v : Fin 4 → F, ∃ z : F, X = nilLift v + z • nilM ∧ t = v 0 := by
  constructor
  · rintro ⟨htr, hc⟩
    have h00 := congrFun (congrFun hc 0) 0
    have h01 := congrFun (congrFun hc 0) 1
    have h02 := congrFun (congrFun hc 0) 2
    have h21 := congrFun (congrFun hc 2) 1
    simp [comm, nilM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      Matrix.smul_apply] at h00 h01 h02 h21
    simp [Matrix.trace, Fin.sum_univ_succ] at htr
    refine ⟨![X 0 0 - X 1 1, -(X 2 2), X 0 2, X 2 1], X 0 1, ?_, h01.symm⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nilLift, nilM] <;>
      first
      | linear_combination htr / 2
      | linear_combination h00
      | linear_combination h02
      | linear_combination h21
  · rintro ⟨v, z, rfl, rfl⟩
    constructor
    · simp [Matrix.trace, nilLift, nilM, Fin.sum_univ_succ]
      ring
    · exact nil_action v z

end Normalizer
