import Normalizer.MatrixTransport

namespace Normalizer
variable {F : Type*} [Field F] [CharZero F]
variable {W : Type*} [AddCommGroup W] [Module F W]

omit [CharZero F] in
/-- Distinct diagonal entries force every line-normalizing matrix to be diagonal;
its first two diagonal entries then detect a trace-zero matrix. -/
theorem distinct_diagonal_matrix_boundary_lift (d : Fin 3 → F)
    (hd : Function.Injective d) (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F)
    (h : MatrixBoundaryLift (Matrix.diagonal d) J χ) : Module.finrank F W < 3 := by
  let f : W →ₗ[F] (Fin 2 → F) :=
    { toFun := fun x => ![J x 0 0, J x 1 1]
      map_add' := by intros; ext i; fin_cases i <;> simp
      map_smul' := by intros; ext i; fin_cases i <;> simp }
  have hoff (x : W) (i j : Fin 3) (hij : i ≠ j) : J x i j = 0 := by
    have he := congrFun (congrFun (h.2.1 x) i) j
    simp only [comm, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.smul_apply, Matrix.diagonal_apply_ne _ hij, smul_zero] at he
    have : (d j - d i) * J x i j = 0 := by linear_combination he
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (fun he => hij (hd he).symm))
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have h0 : J x 0 0 = 0 := congrFun hx 0
    have h1 : J x 1 1 = 0 := congrFun hx 1
    have h2 : J x 2 2 = 0 := by
      have ht := h.1 x
      simpa [Matrix.trace, Fin.sum_univ_succ, h0, h1] using ht
    apply h.2.2.2 x
    refine ⟨0, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst j
      fin_cases i <;> simp [h0, h1, h2]
    · simp [hoff x i j hij]
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  have : Module.finrank F (Fin 2 → F) = 2 := by simp
  omega

omit [CharZero F] in
/-- A nonzero trace-zero diagonal matrix with a repeated entry is a rescaled
permutation of the checked semisimple representative. -/
theorem repeated_diagonal_sem_model (d : Fin 3 → F)
    (ht : Matrix.trace (Matrix.diagonal d) = 0)
    (hn : Matrix.diagonal d ≠ 0) (hd : ¬ Function.Injective d) :
    ∃ (e : Fin 3 ≃ Fin 3) (a : F), a ≠ 0 ∧
      Matrix.reindexAlgEquiv F F e (Matrix.diagonal d) = a • semM := by
  classical
  have ht' : d 0 + d 1 + d 2 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_succ, add_assoc] using ht
  have hp (h01 : d 0 = d 1) :
      ∃ (e : Fin 3 ≃ Fin 3) (a : F), a ≠ 0 ∧
        Matrix.reindexAlgEquiv F F e (Matrix.diagonal d) = a • semM := by
    have h2 : d 2 = -2 * d 0 := by linear_combination ht' + h01
    have h0 : d 0 ≠ 0 := by
      intro hz
      apply hn
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ← h01, h2, hz]
    refine ⟨Equiv.refl _, d 0, h0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.reindexAlgEquiv, semM, Matrix.diagonal, ← h01, h2]
    all_goals ring
  by_cases h01 : d 0 = d 1
  · exact hp h01
  have hex : d 0 = d 2 ∨ d 1 = d 2 := by
    by_contra he
    push Not at he
    apply hd
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  rcases hex with h02 | h12
  · have h1 : d 1 = -2 * d 0 := by linear_combination ht' + h02
    have h0 : d 0 ≠ 0 := by
      intro hz
      exact h01 (by simp [h1, hz])
    refine ⟨Equiv.swap 1 2, d 0, h0, ?_⟩
    have hs (i : Fin 3) : Equiv.swap (1 : Fin 3) 2 i = (![0, 2, 1] : Fin 3 → Fin 3) i := by
      fin_cases i <;> decide
    ext i j
    change Matrix.diagonal d ((Equiv.swap 1 2).symm i) ((Equiv.swap 1 2).symm j) = _
    rw [Equiv.symm_swap, hs i, hs j]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, semM, ← h02, h1]
    all_goals ring
  · have h0 : d 0 = -2 * d 1 := by linear_combination ht' + h12
    have h1 : d 1 ≠ 0 := by
      intro hz
      exact h01 (by simp [h0, hz])
    refine ⟨Equiv.swap 0 2, d 1, h1, ?_⟩
    have hs (i : Fin 3) : Equiv.swap (0 : Fin 3) 2 i = (![2, 1, 0] : Fin 3 → Fin 3) i := by
      fin_cases i <;> decide
    ext i j
    change Matrix.diagonal d ((Equiv.swap 0 2).symm i) ((Equiv.swap 0 2).symm j) = _
    rw [Equiv.symm_swap, hs i, hs j]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, semM, ← h12, h0]
    all_goals ring

/-- Every nonzero trace-zero diagonal matrix satisfies the quotient obstruction. -/
theorem diagonal_matrix_boundary_lift (d : Fin 3 → F)
    (ht : Matrix.trace (Matrix.diagonal d) = 0) (hn : Matrix.diagonal d ≠ 0)
    (J : W →ₗ[F] Mat F) (χ : W →ₗ[F] F)
    (h : MatrixBoundaryLift (Matrix.diagonal d) J χ) : Module.finrank F W < 3 := by
  by_cases hd : Function.Injective d
  · exact distinct_diagonal_matrix_boundary_lift d hd J χ h
  · obtain ⟨e, a, ha, he⟩ := repeated_diagonal_sem_model d ht hn hd
    exact sem_matrix_boundary_lift _ χ
      (matrix_boundary_lift_transport _ semM (Matrix.reindexAlgEquiv F F e).toLinearEquiv
        (matrix_reindex_trace e) (matrix_reindex_comm e) a ha he J χ h)

end Normalizer
