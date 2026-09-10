import Normalizer.LieBoundarySpan
import Normalizer.EvaluationFrame

/-! Final linear assembly for the section argument. Geometry must supply
the constant-coordinate frame, the map to the rank-two quotient's sections,
and evaluation of its kernel in the actual normalizer quotient with compatible
character and boundary law. The dimension loss and contradiction are proved. -/

namespace Normalizer

variable {F K W T Z : Type*} [Field F] [Field K] [Algebra F K] [CharZero K]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]
  [AddCommGroup T] [Module F T] [FiniteDimensional F T]
  [AddCommGroup Z] [Module K Z] [Module F Z] [IsScalarTower F K Z]

/-- A frame for W in the ambient generic fibre and the boundary law on
the kernel of φ give dim W ≤ dim T + 2. The frame need not lie in the
normalizer quotient; only the evaluated kernel does. -/
theorem slThree_section_dimension_le_of_frame
    (m : SlThree K) (hm : m ≠ 0)
    [Module F (SlThreeLineQuotient m)] [IsScalarTower F K (SlThreeLineQuotient m)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : W →ₗ[F] T) (ev : φ.ker →ₗ[F] SlThreeLineQuotient m)
    (i : SlThreeLineQuotient m →ₗ[K] Z)
    (c : W →ₗ[F] (ι → F)) (j : (ι → K) →ₗ[K] Z)
    (hc : Function.Injective c) (hj : Function.Injective j)
    (he : ∀ w : φ.ker, i (ev w) = j (fun a => algebraMap F K (c w a)))
    (χ : φ.ker →ₗ[F] F)
    (hχ : ∀ w, slThreeLineCharacter m hm (ev w) = algebraMap F K (χ w))
    (hl : ∀ x y, ⁅ev x, ev y⁆ = χ x • ev y - χ y • ev x) :
    Module.finrank F W ≤ Module.finrank F T + 2 := by
  have hinj : Function.Injective (ev.liftBaseChange K) :=
    evaluation_lift_injective_of_composite_frame ev i (c.comp φ.ker.subtype) j
      (hc.comp Subtype.val_injective) hj he
  have hdim : Module.finrank K (ev.liftBaseChange K).range =
      Module.finrank F φ.ker := by
    rw [LinearMap.finrank_range_of_inj hinj]
    exact Module.finrank_baseChange
  have hker := slThree_evaluated_span_finrank m hm ev χ hχ hl
  rw [hdim] at hker
  have hrange := φ.range.finrank_le
  have hnull := φ.finrank_range_add_finrank_ker
  omega

/-- The algebraic four-section bound, conditional on the explicit frame,
kernel evaluation, character compatibility, boundary law, and dim T ≤ 2.
This is not an instantiation with sections of a curve bundle. -/
theorem slThree_four_sections_of_frame
    (m : SlThree K) (hm : m ≠ 0)
    [Module F (SlThreeLineQuotient m)] [IsScalarTower F K (SlThreeLineQuotient m)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : W →ₗ[F] T) (ev : φ.ker →ₗ[F] SlThreeLineQuotient m)
    (i : SlThreeLineQuotient m →ₗ[K] Z)
    (c : W →ₗ[F] (ι → F)) (j : (ι → K) →ₗ[K] Z)
    (hc : Function.Injective c) (hj : Function.Injective j)
    (he : ∀ w : φ.ker, i (ev w) = j (fun a => algebraMap F K (c w a)))
    (χ : φ.ker →ₗ[F] F)
    (hχ : ∀ w, slThreeLineCharacter m hm (ev w) = algebraMap F K (χ w))
    (hl : ∀ x y, ⁅ev x, ev y⁆ = χ x • ev y - χ y • ev x)
    (hT : Module.finrank F T ≤ 2) : Module.finrank F W ≤ 4 := by
  have := slThree_section_dimension_le_of_frame m hm φ ev i c j hc hj he χ hχ hl
  omega

end Normalizer
