import Normalizer.Matrices
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace Normalizer
variable {F : Type*} [Field F] [CharZero F]

/-- The required law is imposed on every pair of vectors of the subspace. -/
def BoundaryLaw {V : Type*} [AddCommGroup V] [Module F V] (U : Submodule F V)
    (bracket : V → V → V) (character : V → F) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, bracket x y = character x • y - character y • x

private def coordinatePair {n : ℕ} (i j : Fin n) : (Fin n → F) →ₗ[F] (Fin 2 → F) where
  toFun v := ![v i, v j]
  map_add' _ _ := by ext k; fin_cases k <;> rfl
  map_smul' _ _ := by ext k; fin_cases k <;> rfl

omit [CharZero F] in
private theorem bound_by_pair {n : ℕ} (U : Submodule F (Fin n → F)) (i j : Fin n)
    (h : ∀ x ∈ U, x i = 0 → x j = 0 → x = 0) : Module.finrank F U ≤ 2 := by
  let f := (coordinatePair (F := F) i j).comp U.subtype
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply Subtype.ext
    exact h x x.property (congrFun hx 0) (congrFun hx 1)
  simpa using LinearMap.finrank_le_finrank_of_injective hf

/-- The semisimple quotient has no three-space satisfying the boundary law. -/
theorem sem_no_three (U : Submodule F (Fin 3 → F))
    (hlaw : BoundaryLaw U semBracket (fun _ => 0)) : Module.finrank F U < 3 := by
  by_contra hn
  have heq : U = ⊤ := Submodule.eq_top_of_finrank_eq (by
    have hle := U.finrank_le
    simp only [Module.finrank_pi, Fintype.card_fin] at hle ⊢
    omega)
  have h := hlaw ![0, 1, 0] (by simp [heq]) ![0, 0, 1] (by simp [heq])
  have h0 := congrFun h 0
  change (2 : F) * (1 * 1 - 0 * 0) = 0 * 0 - 0 * 0 at h0
  norm_num at h0

private theorem nil_law_coordinates (U : Submodule F (Fin 4 → F))
    (hlaw : BoundaryLaw U nilBracket (fun v => v 0))
    (x y : Fin 4 → F) (hx : x ∈ U) (hy : y ∈ U) :
    (x 0 * y 1 - y 0 * x 1 = 0) ∧
    ((x 0 - 3 * x 1) * y 2 - (y 0 - 3 * y 1) * x 2 = 0) ∧
    ((x 0 + 3 * x 1) * y 3 - (y 0 + 3 * y 1) * x 3 = 0) := by
  have h1 := congrFun (hlaw x hx y hy) 1
  have h2 := congrFun (hlaw x hx y hy) 2
  have h3 := congrFun (hlaw x hx y hy) 3
  simp [nilBracket] at h1 h2 h3
  exact ⟨h1.symm, by linear_combination -2 * h2, by linear_combination -2 * h3⟩

/-- Every subspace in the minimal quotient obeying the law has dimension at
most two. Proof by injective coordinate projections, over any char-zero field. -/
theorem nil_dimension_le_two (U : Submodule F (Fin 4 → F))
    (hlaw : BoundaryLaw U nilBracket (fun v => v 0)) : Module.finrank F U ≤ 2 := by
  classical
  by_cases hd : ∃ x ∈ U, x 0 ≠ 0
  · obtain ⟨x, hx, hd⟩ := hd
    by_cases hp : x 0 - 3 * x 1 ≠ 0
    · apply bound_by_pair U 0 3
      intro y hy hy0 hy3
      obtain ⟨h1, h2, _⟩ := nil_law_coordinates U hlaw x y hx hy
      have hy1 : y 1 = 0 := by
        apply (mul_eq_zero.mp (by simpa [hy0] using h1)).resolve_left hd
      have hy2 : y 2 = 0 := by
        apply (mul_eq_zero.mp (by simpa [hy0, hy1] using h2)).resolve_left hp
      ext i; fin_cases i <;> assumption
    · have hq : x 0 + 3 * x 1 ≠ 0 := by
        intro hq
        apply hd
        have hp' : x 0 - 3 * x 1 = 0 := not_ne_iff.mp hp
        linear_combination (hp' + hq) / 2
      apply bound_by_pair U 0 2
      intro y hy hy0 hy2
      obtain ⟨h1, _, h3⟩ := nil_law_coordinates U hlaw x y hx hy
      have hy1 : y 1 = 0 := by
        apply (mul_eq_zero.mp (by simpa [hy0] using h1)).resolve_left hd
      have hy3 : y 3 = 0 := by
        apply (mul_eq_zero.mp (by simpa [hy0, hy1] using h3)).resolve_left hq
      ext i; fin_cases i <;> assumption
  · have hd0 : ∀ x ∈ U, x 0 = 0 := by simpa using hd
    by_cases hh : ∃ x ∈ U, x 1 ≠ 0
    · obtain ⟨x, hx, hh⟩ := hh
      apply bound_by_pair U 1 3
      intro y hy hy1 hy3
      have hy0 := hd0 y hy
      obtain ⟨_, h2, _⟩ := nil_law_coordinates U hlaw x y hx hy
      have hp : x 0 - 3 * x 1 ≠ 0 := by
        simpa [hd0 x hx] using mul_ne_zero (by norm_num : (3 : F) ≠ 0) hh
      have hy2 : y 2 = 0 := by
        exact (mul_eq_zero.mp (by simpa [hy0, hy1] using h2)).resolve_left hp
      ext i; fin_cases i <;> assumption
    · have hh0 : ∀ x ∈ U, x 1 = 0 := by simpa using hh
      apply bound_by_pair U 2 3
      intro y hy hy2 hy3
      have hy0 := hd0 y hy
      have hy1 := hh0 y hy
      ext i; fin_cases i <;> assumption

theorem nil_no_three (U : Submodule F (Fin 4 → F))
    (hlaw : BoundaryLaw U nilBracket (fun v => v 0)) : Module.finrank F U < 3 := by
  have := nil_dimension_le_two U hlaw
  omega

end Normalizer
