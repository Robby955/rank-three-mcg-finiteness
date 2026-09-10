import Normalizer.BoundaryScalarExtension
import Normalizer.FrameCharacter
import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Module.Projective

/-! The dimension obstruction for a subspace of the actual normalizer
quotient in sl3. Linear representatives are constructed inside the proof. -/

namespace Normalizer
attribute [local instance] LieRing.ofAssociativeRing
variable {F : Type*} [Field F]

/-- The actual Lie algebra of traceless three-by-three matrices. -/
abbrev SlThree (F : Type*) [Field F] := LieAlgebra.SpecialLinear.sl (Fin 3) F

/-- The actual Lie normalizer of a line, quotiented by that line ideal. -/
abbrev SlThreeLineQuotient (m : SlThree F) :=
  (frameLine (R := F) m).normalizer ⧸ frameIdeal (R := F) m

/-- The scalar-action character on the actual normalizer quotient. -/
noncomputable def slThreeLineCharacter (m : SlThree F) (hm : m ≠ 0) :
    SlThreeLineQuotient m →ₗ[F] F :=
  quotientFrameCharacter m (smul_left_injective F hm)

set_option maxHeartbeats 800000 in
/-- A subspace of the actual Lie quotient satisfying its boundary law has
linear matrix representatives with all four quotient-lift properties. -/
theorem slThree_quotient_boundary_lift_exists (m : SlThree F) (hm : m ≠ 0)
    (U : Submodule F (SlThreeLineQuotient m))
    (hl : BoundaryLaw U (fun x y => ⁅x, y⁆) (slThreeLineCharacter m hm)) :
    ∃ J : U →ₗ[F] Mat F,
      MatrixBoundaryLift (m : Mat F) J ((slThreeLineCharacter m hm).comp U.subtype) := by
  let N := (frameLine (R := F) m).normalizer
  let q : N →ₗ[F] SlThreeLineQuotient m := (frameIdeal (R := F) m).toSubmodule.mkQ
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (frameIdeal (R := F) m).toSubmodule.mkQ_surjective)
  have hqs (x : SlThreeLineQuotient m) : q (s x) = x := LinearMap.congr_fun hs x
  let S : U →ₗ[F] N := s.comp U.subtype
  let J : U →ₗ[F] Mat F := (SlThree F).incl.toLinearMap.comp (N.incl.toLinearMap.comp S)
  let χ := (slThreeLineCharacter m hm).comp U.subtype
  have hqS (x : U) : q (S x) = (x : SlThreeLineQuotient m) := hqs x
  have hχ (x : U) : frameCharacter m (smul_left_injective F hm) (S x) = χ x := by
    have he := quotientFrameCharacter_mk m (smul_left_injective F hm) (S x)
    change slThreeLineCharacter m hm (q (S x)) = _ at he
    rw [hqS] at he
    exact he.symm
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (S x).val.property
  · intro x
    have he := frameCharacter_action m (smul_left_injective F hm) (S x)
    rw [hχ] at he
    exact congrArg (fun A : SlThree F => (A : Mat F)) he
  · intro x y
    let D : N := ⁅S x, S y⁆ - χ x • S y + χ y • S x
    have hD : q D = 0 := by
      simp only [D, map_add, map_sub, map_smul]
      change ⁅q (S x), q (S y)⁆ - χ x • q (S y) + χ y • q (S x) = 0
      rw [hqS, hqS]
      have hb : ⁅(x : SlThreeLineQuotient m), (y : SlThreeLineQuotient m)⁆ =
          χ x • (y : SlThreeLineQuotient m) - χ y • (x : SlThreeLineQuotient m) :=
        hl x x.property y y.property
      erw [hb]
      change χ x • (y : SlThreeLineQuotient m) - χ y • (x : SlThreeLineQuotient m) -
        χ x • (y : SlThreeLineQuotient m) + χ y • (x : SlThreeLineQuotient m) = 0
      abel
    have hDI : D ∈ (frameIdeal (R := F) m).toSubmodule := (Submodule.Quotient.mk_eq_zero _).mp hD
    change (D : SlThree F) ∈ Submodule.span F {m} at hDI
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hDI
    have he := congrArg (fun A : SlThree F => (A : Mat F)) hz.symm
    change comm (J x) (J y) - χ x • J y + χ y • J x = z • (m : Mat F) at he
    refine ⟨z, ?_⟩
    change comm (J x) (J y) = χ x • J y - χ y • J x + z • (m : Mat F)
    calc
      comm (J x) (J y) =
          (comm (J x) (J y) - χ x • J y + χ y • J x) + χ x • J y - χ y • J x := by abel
      _ = χ x • J y - χ y • J x + z • (m : Mat F) := by rw [he]; abel
  · intro x hx
    obtain ⟨z, hz⟩ := hx
    have hS : (S x : SlThree F) = z • m := Subtype.ext hz
    have hmem : S x ∈ (frameIdeal (R := F) m).toSubmodule := by
      change (S x : SlThree F) ∈ Submodule.span F {m}
      rw [hS]
      exact Submodule.smul_mem _ z (Submodule.mem_span_singleton_self m)
    have hzero : q (S x) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hmem
    rw [hqS] at hzero
    exact Subtype.ext hzero

/-- Every subspace of the actual sl3 line-normalizer quotient satisfying
the boundary law for its actual character has dimension at most two. -/
theorem slThree_quotient_boundary_finrank [CharZero F] (m : SlThree F) (hm : m ≠ 0)
    (U : Submodule F (SlThreeLineQuotient m))
    (hl : BoundaryLaw U (fun x y => ⁅x, y⁆) (slThreeLineCharacter m hm)) :
    Module.finrank F U < 3 := by
  obtain ⟨J, hJ⟩ := slThree_quotient_boundary_lift_exists m hm U hl
  exact traceless_matrix_boundary_lift_any_field (m : Mat F)
    (fun h => hm (Subtype.ext h)) m.property J _ hJ

end Normalizer
