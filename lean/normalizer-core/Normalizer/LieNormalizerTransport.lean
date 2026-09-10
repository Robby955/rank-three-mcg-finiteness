import Normalizer.ActualNormalizerQuotient

/-! Lie equivalences transport actual line normalizers, their Lie quotients,
and their scalar-action characters. The supplied ambient equivalence need
not come from a matrix conjugation. -/

noncomputable section
namespace Normalizer

variable {R L K : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing K] [LieAlgebra R K]

/-- An ambient Lie equivalence preserves and reflects membership in the
actual normalizer of the frame line. -/
theorem mem_frameNormalizer_lieEquiv (e : L ≃ₗ⁅R⁆ K) (m x : L) :
    e x ∈ (frameLine (R := R) (e m)).normalizer ↔
      x ∈ (frameLine (R := R) m).normalizer := by
  rw [mem_frameNormalizer, mem_frameNormalizer]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, e.injective ?_⟩
    change e ⁅x, m⁆ = e (a • m)
    rw [e.map_lie, map_smul]
    exact ha
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← e.map_lie, ha, map_smul]

/-- The restriction of the ambient equivalence is an actual Lie
equivalence of line normalizers. -/
def frameNormalizerLieEquiv (e : L ≃ₗ⁅R⁆ K) (m : L) :
    (frameLine (R := R) m).normalizer ≃ₗ⁅R⁆
      (frameLine (R := R) (e m)).normalizer where
  __ := frameNormalizerMap m e.toLieHom.toLinearMap e.map_lie
  map_lie' := by intro x y; apply Subtype.ext; exact e.map_lie x y
  invFun x := ⟨e.symm x, by
    apply (mem_frameNormalizer_lieEquiv e m (e.symm x)).mp
    simpa only [e.apply_symm_apply] using x.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x
  right_inv x := by apply Subtype.ext; exact e.apply_symm_apply x

/-- The constructed normalizer equivalence is the ambient map on values. -/
theorem frameNormalizerLieEquiv_apply (e : L ≃ₗ⁅R⁆ K) (m : L)
    (x : (frameLine (R := R) m).normalizer) :
    (frameNormalizerLieEquiv e m x : K) = e (x : L) := rfl

/-- The quotient map induced by an ambient Lie equivalence preserves the
actual quotient brackets. -/
def frameQuotientLieHom (e : L ≃ₗ⁅R⁆ K) (m : L) :
    ((frameLine (R := R) m).normalizer ⧸ frameIdeal m) →ₗ⁅R⁆
      ((frameLine (R := R) (e m)).normalizer ⧸ frameIdeal (e m)) where
  __ := frameQuotientMap m e.toLieHom.toLinearMap e.map_lie
  map_lie' := by
    intro x y
    refine Quotient.inductionOn₂' x y ?_
    intro a b
    exact congrArg (frameIdeal (R := R) (e m)).toSubmodule.mkQ
      ((frameNormalizerLieEquiv e m).map_lie a b)

private theorem frameQuotientLieHom_bijective (e : L ≃ₗ⁅R⁆ K) (m : L) :
    Function.Bijective (frameQuotientLieHom e m) := by
  constructor
  · have hz : ∀ x, frameQuotientLieHom e m x = 0 → x = 0 := by
      intro x
      refine Quotient.inductionOn' x ?_
      intro a ha
      have hmem := (Submodule.Quotient.mk_eq_zero _).mp ha
      change e (a : L) ∈ Submodule.span R {e m} at hmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change (a : L) ∈ Submodule.span R {m}
      apply Submodule.mem_span_singleton.mpr
      refine ⟨c, e.injective ?_⟩
      change e (c • m) = e (a : L)
      rw [map_smul]
      exact hc
    intro x y h
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, h, sub_self]
  · intro x
    refine Quotient.inductionOn' x ?_
    intro a
    refine ⟨(frameIdeal (R := R) m).toSubmodule.mkQ
      ((frameNormalizerLieEquiv e m).symm a), ?_⟩
    exact congrArg (frameIdeal (R := R) (e m)).toSubmodule.mkQ
      ((frameNormalizerLieEquiv e m).apply_symm_apply a)

/-- The quotient equivalence is constructed from the induced map; its
bijectivity follows by reflecting the line ideal and lifting representatives. -/
def frameQuotientLieEquiv (e : L ≃ₗ⁅R⁆ K) (m : L) :
    ((frameLine (R := R) m).normalizer ⧸ frameIdeal m) ≃ₗ⁅R⁆
      ((frameLine (R := R) (e m)).normalizer ⧸ frameIdeal (e m)) :=
  LieEquiv.ofBijective (frameQuotientLieHom e m) (frameQuotientLieHom_bijective e m)

/-- The quotient equivalence sends the class of a representative to the
class of its actual transported normalizer element. -/
theorem frameQuotientLieEquiv_mk (e : L ≃ₗ⁅R⁆ K) (m : L)
    (x : (frameLine (R := R) m).normalizer) :
    frameQuotientLieEquiv e m ((frameIdeal m).toSubmodule.mkQ x) =
      (frameIdeal (e m)).toSubmodule.mkQ (frameNormalizerLieEquiv e m x) := rfl

/-- Transport by the constructed quotient equivalence preserves the
actual scalar action on the line. -/
theorem quotientFrameCharacter_lieEquiv (e : L ≃ₗ⁅R⁆ K) (m : L)
    (hm : Function.Injective (fun r : R => r • m))
    (hk : Function.Injective (fun r : R => r • e m))
    (x : (frameLine (R := R) m).normalizer ⧸ frameIdeal m) :
    quotientFrameCharacter (e m) hk (frameQuotientLieEquiv e m x) =
      quotientFrameCharacter m hm x :=
  quotientFrameCharacter_restrict m e.toLieHom.toLinearMap e.map_lie hm hk x

/-- The boundary law transports to the image subspace under the actual
quotient equivalence, with its actual target scalar-action character. -/
theorem boundaryLaw_frameQuotientLieEquiv {F A B : Type*} [Field F]
    [LieRing A] [LieAlgebra F A] [LieRing B] [LieAlgebra F B]
    (e : A ≃ₗ⁅F⁆ B) (m : A)
    (hm : Function.Injective (fun r : F => r • m))
    (hk : Function.Injective (fun r : F => r • e m))
    (U : Submodule F ((frameLine (R := F) m).normalizer ⧸ frameIdeal m))
    (hl : BoundaryLaw U (fun x y => ⁅x, y⁆) (quotientFrameCharacter m hm)) :
    BoundaryLaw (U.map (frameQuotientLieEquiv e m).toLinearEquiv.toLinearMap)
      (fun x y => ⁅x, y⁆) (quotientFrameCharacter (e m) hk) := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have he := congrArg (frameQuotientLieEquiv e m) (hl a ha b hb)
  rw [(frameQuotientLieEquiv e m).map_lie, map_sub, map_smul, map_smul] at he
  rw [← quotientFrameCharacter_lieEquiv e m hm hk a,
    ← quotientFrameCharacter_lieEquiv e m hm hk b] at he
  exact he

section Field
variable {F A : Type*} [Field F] [CharZero F] [LieRing A] [LieAlgebra F A]

/-- Any Lie algebra supplied with an isomorphism to sl3 satisfies the
actual line-normalizer quotient obstruction. The normalizer and quotient
equivalences, character transport, and image dimension are constructed. -/
theorem lieEquiv_slThree_quotient_boundary_finrank (e : A ≃ₗ⁅F⁆ SlThree F)
    (m : A) (hm : m ≠ 0)
    (U : Submodule F ((frameLine (R := F) m).normalizer ⧸ frameIdeal m))
    (hl : BoundaryLaw U (fun x y => ⁅x, y⁆)
      (quotientFrameCharacter m (smul_left_injective F hm))) :
    Module.finrank F U < 3 := by
  have hem : e m ≠ 0 := by
    intro h
    apply hm
    apply e.injective
    change e m = e 0
    rw [map_zero]
    exact h
  let q := frameQuotientLieEquiv e m
  let V := U.map q.toLinearEquiv.toLinearMap
  have hlV : BoundaryLaw V (fun x y => ⁅x, y⁆)
      (slThreeLineCharacter (e m) hem) :=
    boundaryLaw_frameQuotientLieEquiv e m (smul_left_injective F hm)
      (smul_left_injective F hem) U hl
  have hV := slThree_quotient_boundary_finrank (e m) hem V hlV
  have hdim : Module.finrank F U = Module.finrank F V :=
    (Submodule.equivMapOfInjective q.toLinearEquiv.toLinearMap q.injective U).finrank_eq
  rw [hdim]
  exact hV

end Field

end Normalizer
