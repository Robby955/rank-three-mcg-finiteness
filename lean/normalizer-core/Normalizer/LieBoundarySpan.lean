import Normalizer.ActualNormalizerQuotient
import Mathlib.RingTheory.TensorProduct.Basic

/-! A boundary identity on evaluated sections extends to their span over
the function field. This does not assume that generic evaluation is injective.
The actual scalar-action character is retained throughout. -/

namespace Normalizer

variable {K Q : Type*} [Field K] [LieRing Q] [LieAlgebra K Q]

/-- Bilinearity extends the boundary law from a generating set to its
entire linear span, using the same ambient linear character. -/
theorem lie_boundaryLaw_span (s : Set Q) (χ : Q →ₗ[K] K)
    (hl : ∀ x ∈ s, ∀ y ∈ s, ⁅x, y⁆ = χ x • y - χ y • x) :
    BoundaryLaw (Submodule.span K s) (fun x y => ⁅x, y⁆) χ := by
  intro x hx y hy
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy => exact hl x hx y hy
  | zero_left y hy => simp
  | zero_right x hx => simp
  | add_left x y z _ _ _ hx hy =>
    simp only [add_lie, map_add, hx, hy, add_smul, smul_add]
    abel
  | add_right x y z _ _ _ hx hy =>
    simp only [lie_add, map_add, hx, hy, add_smul, smul_add]
    abel
  | smul_left a x y _ _ h =>
    simp only [smul_lie, map_smul, h, smul_sub, smul_smul, smul_eq_mul]
    rw [mul_comm (χ y) a]
  | smul_right a x y _ _ h =>
    simp only [lie_smul, map_smul, h, smul_sub, smul_smul, smul_eq_mul]
    rw [mul_comm (χ x) a]

variable {F W : Type*} [Field F] [Algebra F K]
  [AddCommGroup W] [Module F W] [Module F Q] [IsScalarTower F K Q]

/-- A scalar-valued global character and its evaluation compatibility
extend the law to the image of the canonical tensor evaluation map. -/
theorem evaluated_boundaryLaw (ev : W →ₗ[F] Q) (χ : W →ₗ[F] F)
    (χK : Q →ₗ[K] K)
    (hχ : ∀ x, χK (ev x) = algebraMap F K (χ x))
    (hl : ∀ x y, ⁅ev x, ev y⁆ = χ x • ev y - χ y • ev x) :
    BoundaryLaw (ev.liftBaseChange K).range (fun x y => ⁅x, y⁆) χK := by
  rw [LinearMap.range_liftBaseChange]
  apply lie_boundaryLaw_span
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [hχ, hχ, hl]
  simp only [algebraMap_smul]

/-- The actual function-field span of evaluated sections has dimension
at most two whenever the evaluated boundary law and character agree. -/
theorem slThree_evaluated_span_finrank [CharZero K]
    (m : SlThree K) (hm : m ≠ 0)
    [Module F (SlThreeLineQuotient m)] [IsScalarTower F K (SlThreeLineQuotient m)]
    (ev : W →ₗ[F] SlThreeLineQuotient m) (χ : W →ₗ[F] F)
    (hχ : ∀ x, slThreeLineCharacter m hm (ev x) = algebraMap F K (χ x))
    (hl : ∀ x y, ⁅ev x, ev y⁆ = χ x • ev y - χ y • ev x) :
    Module.finrank K (ev.liftBaseChange K).range < 3 :=
  slThree_quotient_boundary_finrank m hm _
    (evaluated_boundaryLaw ev χ (slThreeLineCharacter m hm) hχ hl)

end Normalizer
