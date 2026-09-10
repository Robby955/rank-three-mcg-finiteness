import Normalizer.SquareZero
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Semisimple

/-! An exhaustive replacement for a full Jordan-normal-form theorem in the
three-by-three line-normalizer argument. -/

namespace Normalizer

open Polynomial

variable {F : Type*} [Field F] [IsAlgClosed F]

/-- A monic polynomial of degree at most two which is not squarefree is the
square of a monic linear polynomial. -/
theorem monic_degree_le_two_not_squarefree (p : F[X]) (hp : p.Monic)
    (hd : p.natDegree ≤ 2) (hsq : ¬ Squarefree p) :
    ∃ a : F, p = (X - C a) ^ 2 := by
  obtain ⟨q, hq, hqdvd⟩ : ∃ q : F[X], ∃ _ : Irreducible q, q * q ∣ p := by
    simpa only [squarefree_iff_no_irreducibles hp.ne_zero, not_forall, not_imp,
      not_not] using hsq
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root q
    (by rw [IsAlgClosed.degree_eq_one_of_irreducible F hq]; decide)
  have hlinear : X - C a ∣ q := dvd_iff_isRoot.mpr ha
  have hdiv : (X - C a) ^ 2 ∣ p :=
    by simpa [pow_two] using (mul_dvd_mul hlinear hlinear).trans hqdvd
  exact ⟨a, eq_of_monic_of_dvd_of_natDegree_le ((monic_X_sub_C a).pow 2) hp hdiv
    (by simpa using hd)⟩

/-- Every traceless three-by-three matrix over an algebraically closed field
of characteristic zero has full minimal-polynomial degree, is semisimple,
or is square-zero.  No Jordan reduction is assumed. -/
theorem traceless_matrix_trichotomy [CharZero F] (m : Mat F) (htr : Matrix.trace m = 0) :
    (minpoly F m).natDegree = 3 ∨ Module.End.IsSemisimple (Matrix.toLin' m) ∨ m ^ 2 = 0 := by
  by_cases hdeg : (minpoly F m).natDegree = 3
  · exact Or.inl hdeg
  right
  have hle3 : (minpoly F m).natDegree ≤ 3 := by
    simpa using Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly m)
      (Matrix.charpoly_monic m).ne_zero
  have hle2 : (minpoly F m).natDegree ≤ 2 := by omega
  by_cases hsq : Squarefree (minpoly F m)
  · left
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := minpoly F (Matrix.toLin' m))
    · simpa using hsq
    · exact minpoly.aeval F (Matrix.toLin' m)
  · right
    obtain ⟨a, ha⟩ := monic_degree_le_two_not_squarefree (minpoly F m)
      (minpoly.monic (Matrix.isIntegral m)) hle2 hsq
    have hshift : (m - a • 1) ^ 2 = 0 := by
      have he := minpoly.aeval F m
      rw [ha] at he
      simpa [Algebra.algebraMap_eq_smul_one] using he
    have ha0 := traceless_shift_square_zero m a htr hshift
    simpa [ha0] using hshift

end Normalizer
