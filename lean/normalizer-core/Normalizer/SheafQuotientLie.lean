import Normalizer.SheafQuotientBracket
import Normalizer.TrivializedCharacter
import Mathlib.Algebra.Lie.OfAssociative

/-! Lie identities for the bracket on the actual quotient sheaf.
Identities are checked on a constructed cover of local representatives.
The ambient alternating bracket and its Jacobi identity are explicit inputs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Normalizer
open CategoryTheory Limits Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  (E : SheafOfModules.{u} R) (I : E.Submodule)
  (action : ∀ V, E.val.obj V → E.val.obj V →ₗ[R.obj.obj V] E.val.obj V)
  (action_res : ∀ {V W} (f : V ⟶ W) (m x : E.val.obj V),
    E.val.map f (action V m x) = action W (E.val.map f m) (E.val.map f x))
  (habelian : ∀ V (x m : E.val.obj V), x ∈ I.obj V → m ∈ I.obj V →
    action V m x = 0)
  (jacobi : ∀ V (x y m : E.val.obj V),
    action V m (action V y x) =
      action V (action V m y) x - action V (action V m x) y)
  (skew : ∀ V (x y : E.val.obj V), action V y x = -action V x y)

private abbrev normalizerModule := (normalizerSubsheaf E I action action_res).toSheafOfModules
local notation "N" => normalizerModule E I action action_res
local notation "K" => normalizerQuotientSheaf E I action action_res habelian
local notation "π" => cokernel.π (normalizerLineInclusion E I action action_res habelian)
local notation "nb" => normalizerSectionBracket E I action action_res jacobi
local notation "br" => normalizerQuotientBracket E I action action_res habelian jacobi skew

include skew in
private theorem sectionBracket_skew (V) (x y : (N).val.obj V) : nb V x y = -nb V y x := by
  apply Subtype.ext
  exact skew V x.val y.val

private theorem sectionBracket_add_left (V) (x y z : (N).val.obj V) :
    nb V (x + y) z = nb V x z + nb V y z := by
  apply Subtype.ext
  exact (action V z.val).map_add x.val y.val

private theorem sectionBracket_smul_left (V) (r : R.obj.obj V) (x y : (N).val.obj V) :
    nb V (r • x) y = r • nb V x y := by
  apply Subtype.ext
  exact (action V y.val).map_smul r x.val

/-- Skew symmetry holds on arbitrary sections of the actual quotient. -/
theorem normalizerQuotientBracket_skew (V : Opens X) (x y : (K).val.obj (op V)) :
    br V x y = -br V y x := by
  apply sheaf_eq_of_local_lifts π (sheaf_cokernel_locallySurjective _) K V x y y
  intro W h a b c ha hb hc
  change (π).val.app (op W) a = (K).val.map (homOfLE h).op x at ha
  change (π).val.app (op W) b = (K).val.map (homOfLE h).op y at hb
  change (K).val.map (homOfLE h).op (br V x y) = (K).val.map (homOfLE h).op (-br V y x)
  rw [map_neg, normalizerQuotientBracket_restrict, normalizerQuotientBracket_restrict,
    ← ha, ← hb, normalizerQuotientBracket_projection, normalizerQuotientBracket_projection]
  exact (congrArg ((π).val.app (op W))
    (sectionBracket_skew E I action action_res jacobi skew _ a b)).trans
      (map_neg ((π).val.app (op W)).hom _)

/-- Additivity in the first argument descends through the sheaf quotient. -/
theorem normalizerQuotientBracket_add_left (V : Opens X) (x y z : (K).val.obj (op V)) :
    br V (x + y) z = br V x z + br V y z := by
  apply sheaf_eq_of_local_lifts π (sheaf_cokernel_locallySurjective _) K V x y z
  intro W h a b c ha hb hc
  change (π).val.app (op W) a = (K).val.map (homOfLE h).op x at ha
  change (π).val.app (op W) b = (K).val.map (homOfLE h).op y at hb
  change (π).val.app (op W) c = (K).val.map (homOfLE h).op z at hc
  change (K).val.map (homOfLE h).op (br V (x + y) z) =
    (K).val.map (homOfLE h).op (br V x z + br V y z)
  rw [map_add, normalizerQuotientBracket_restrict, normalizerQuotientBracket_restrict,
    normalizerQuotientBracket_restrict, map_add, ← ha, ← hb, ← hc,
    ← map_add ((π).val.app (op W)).hom a b,
    normalizerQuotientBracket_projection, normalizerQuotientBracket_projection,
    normalizerQuotientBracket_projection]
  exact (congrArg ((π).val.app (op W))
    (sectionBracket_add_left E I action action_res jacobi _ a b c)).trans
      (map_add ((π).val.app (op W)).hom _ _)

/-- Additivity in the second argument follows from the proved skew law. -/
theorem normalizerQuotientBracket_add_right (V : Opens X) (x y z : (K).val.obj (op V)) :
    br V x (y + z) = br V x y + br V x z := by
  rw [normalizerQuotientBracket_skew E I action action_res habelian jacobi skew V x (y + z),
    normalizerQuotientBracket_add_left,
    normalizerQuotientBracket_skew E I action action_res habelian jacobi skew V y x,
    normalizerQuotientBracket_skew E I action action_res habelian jacobi skew V z x]
  simp [add_comm]

/-- Scalar linearity in the first argument on each quotient-section module. -/
theorem normalizerQuotientBracket_smul_left (V : Opens X) (r : R.obj.obj (op V))
    (x y : (K).val.obj (op V)) : br V (r • x) y = r • br V x y := by
  apply sheaf_eq_of_local_lifts π (sheaf_cokernel_locallySurjective _) K V x y y
  intro W h a b c ha hb hc
  change (π).val.app (op W) a = (K).val.map (homOfLE h).op x at ha
  change (π).val.app (op W) b = (K).val.map (homOfLE h).op y at hb
  change (K).val.map (homOfLE h).op (br V (r • x) y) =
    (K).val.map (homOfLE h).op (r • br V x y)
  rw [(K).val.map_smul, normalizerQuotientBracket_restrict,
    normalizerQuotientBracket_restrict, (K).val.map_smul, ← ha, ← hb,
    ← map_smul ((π).val.app (op W)).hom (R.obj.map (homOfLE h).op r) a,
    normalizerQuotientBracket_projection, normalizerQuotientBracket_projection]
  exact (congrArg ((π).val.app (op W))
    (sectionBracket_smul_left E I action action_res jacobi _ _ a b)).trans
      (map_smul ((π).val.app (op W)).hom _ _)

/-- Scalar linearity in the second argument follows from skew symmetry. -/
theorem normalizerQuotientBracket_smul_right (V : Opens X) (r : R.obj.obj (op V))
    (x y : (K).val.obj (op V)) : br V x (r • y) = r • br V x y := by
  rw [normalizerQuotientBracket_skew E I action action_res habelian jacobi skew V x (r • y),
    normalizerQuotientBracket_smul_left,
    normalizerQuotientBracket_skew E I action action_res habelian jacobi skew V y x]
  simp

variable (alternating : ∀ V (x : E.val.obj V), action V x x = 0)

include alternating in
/-- Ambient alternation descends without any assumption on characteristic. -/
theorem normalizerQuotientBracket_alternating (V : Opens X) (x : (K).val.obj (op V)) :
    br V x x = 0 := by
  apply sheaf_eq_of_local_lifts π (sheaf_cokernel_locallySurjective _) K V x x x
  intro W h a b c ha hb hc
  change (π).val.app (op W) a = (K).val.map (homOfLE h).op x at ha
  change (K).val.map (homOfLE h).op (br V x x) = (K).val.map (homOfLE h).op 0
  rw [map_zero, normalizerQuotientBracket_restrict, ← ha, normalizerQuotientBracket_projection]
  have hz : nb (op W) a a = 0 := Subtype.ext (alternating (op W) a.val)
  rw [hz, map_zero]

/-- Jacobi descends on a common cover of three local normalizer lifts. -/
theorem normalizerQuotientBracket_jacobi (V : Opens X) (x y z : (K).val.obj (op V)) :
    br V (br V x y) z = br V x (br V y z) - br V y (br V x z) := by
  apply sheaf_eq_of_local_lifts π (sheaf_cokernel_locallySurjective _) K V x y z
  intro W h a b c ha hb hc
  change (π).val.app (op W) a = (K).val.map (homOfLE h).op x at ha
  change (π).val.app (op W) b = (K).val.map (homOfLE h).op y at hb
  change (π).val.app (op W) c = (K).val.map (homOfLE h).op z at hc
  change (K).val.map (homOfLE h).op (br V (br V x y) z) =
    (K).val.map (homOfLE h).op (br V x (br V y z) - br V y (br V x z))
  rw [map_sub]
  simp only [normalizerQuotientBracket_restrict, ← ha, ← hb, ← hc,
    normalizerQuotientBracket_projection]
  have hn : nb (op W) (nb (op W) a b) c =
      nb (op W) a (nb (op W) b c) - nb (op W) b (nb (op W) a c) :=
    Subtype.ext (jacobi (op W) a.val b.val c.val)
  exact (congrArg ((π).val.app (op W)) hn).trans (map_sub ((π).val.app (op W)).hom _ _)

/-- The actual quotient-section module equipped with its constructed Lie
ring structure. The underlying additive group is unchanged. -/
@[instance_reducible]
def normalizerQuotientLieRing (V : Opens X) : LieRing ((K).val.obj (op V)) where
  bracket := br V
  add_lie := normalizerQuotientBracket_add_left E I action action_res habelian jacobi skew V
  lie_add := normalizerQuotientBracket_add_right E I action action_res habelian jacobi skew V
  lie_self := normalizerQuotientBracket_alternating E I action action_res habelian
    jacobi skew alternating V
  leibniz_lie x y z := by
    exact (eq_sub_iff_add_eq.mp
      (normalizerQuotientBracket_jacobi E I action action_res habelian jacobi skew V x y z)).symm

@[instance_reducible]
private def commutativeSectionRing
    (ring_comm : ∀ V (a b : R.obj.obj V), a * b = b * a) (V) : CommRing (R.obj.obj V) :=
  { (inferInstance : Ring (R.obj.obj V)) with mul_comm := ring_comm V }

/-- The quotient is a Lie algebra over its commutative ring of sections,
using the existing module action and the constructed Lie bracket. -/
@[instance_reducible]
def normalizerQuotientLieAlgebra
    (ring_comm : ∀ V (a b : R.obj.obj V), a * b = b * a) (V : Opens X) :
    letI := commutativeSectionRing ring_comm (op V)
    letI := normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating V
    LieAlgebra (R.obj.obj (op V)) ((K).val.obj (op V)) := by
  letI := commutativeSectionRing ring_comm (op V)
  letI := normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating V
  exact { (inferInstance : Module (R.obj.obj (op V)) ((K).val.obj (op V))) with
    lie_smul := normalizerQuotientBracket_smul_right E I action action_res habelian jacobi skew V }

/-- Actual sheaf restrictions bundled as Lie homomorphisms over the
integers. Their stronger semilinearity over the restriction of section
rings is already part of the underlying sheaf-of-modules restriction. -/
def normalizerQuotientLieRestriction (V W : Opens X) (h : W ≤ V) :
    letI := normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating V
    letI := normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating W
    (K).val.obj (op V) →ₗ⁅ℤ⁆ (K).val.obj (op W) := by
  letI := normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating V
  letI := normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating W
  exact { ((K).val.restrictₛₗ (homOfLE h).op).toAddMonoidHom.toIntLinearMap with
    map_lie' := normalizerQuotientBracket_restrict E I action action_res habelian
      jacobi skew V W h _ _ }

/-- Bundling the restriction as a Lie homomorphism leaves its action on
sections equal to the actual sheaf restriction. -/
theorem normalizerQuotientLieRestriction_apply (V W : Opens X) (h : W ≤ V)
    (x : (K).val.obj (op V)) :
    normalizerQuotientLieRestriction E I action action_res habelian jacobi skew alternating
      V W h x = (K).val.map (homOfLE h).op x := rfl

/-- The bundled Lie restrictions preserve the identity restriction. -/
theorem normalizerQuotientLieRestriction_id (V : Opens X) :
    let := normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating V
    normalizerQuotientLieRestriction E I action action_res habelian jacobi skew alternating
      V V le_rfl = LieHom.id (R := ℤ) := by
  let := normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating V
  ext x
  change (K).val.map (𝟙 (op V)) x = x
  simp

/-- Composition of the bundled Lie restrictions is the actual composite
sheaf restriction. -/
theorem normalizerQuotientLieRestriction_comp (V W T : Opens X) (h : W ≤ V) (k : T ≤ W) :
    let := normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating V
    let := normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating W
    let := normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating T
    (normalizerQuotientLieRestriction E I action action_res habelian jacobi skew alternating
      W T k).comp (normalizerQuotientLieRestriction E I action action_res habelian
        jacobi skew alternating V W h) =
      normalizerQuotientLieRestriction E I action action_res habelian jacobi skew alternating
        V T (k.trans h) := by
  let := normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating V
  let := normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating W
  let := normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating T
  ext x
  exact ((K).val.map_comp_apply (homOfLE h).op (homOfLE k).op x).symm

variable
  (ring_comm : ∀ V (a b : R.obj.obj V), a * b = b * a)
  (action_smul_right : ∀ V (r : R.obj.obj V) (m x : E.val.obj V),
    action V (r • m) x = r • action V m x)

include ring_comm action_smul_right in
/-- The character in a genuine frame kills brackets: Jacobi reduces its
action on the frame to the commutator of two scalar multiplications. -/
theorem sectionFrameCharacter_bracket (V)
    (t : R.obj.obj V ≃ₗ[R.obj.obj V] I.obj V) (x y : (N).val.obj V) :
    sectionFrameCharacter E I action action_res V t (nb V x y) = 0 := by
  apply sectionFrameCharacter_unique E I action action_res V t
  change action V (t 1) (action V y.val x.val) = 0 • (t 1 : E.val.obj V)
  rw [jacobi, sectionFrameCharacter_action E I action action_res V t y,
    sectionFrameCharacter_action E I action action_res V t x,
    action_smul_right, action_smul_right,
    sectionFrameCharacter_action E I action action_res V t x,
    sectionFrameCharacter_action E I action action_res V t y,
    smul_smul, smul_smul, ring_comm, sub_self, zero_smul]

variable {ι : Type u} (U : ι → Opens X) (hcover : iSup U = ⊤)
  (triv : ∀ i, (SheafOfModules.unit R).over (U i) ≅ I.toSheafOfModules.over (U i))

local notation "χ" => quotientCharacterOfTrivializations E I action action_res ring_comm
  action_smul_right habelian U hcover triv

/-- The actual quotient character kills the image of every normalizer
bracket, proved on the cover of genuine line-sheaf trivializations. -/
theorem quotientCharacterOfTrivializations_projected_bracket (V : Opens X)
    (x y : (N).val.obj (op V)) :
    (χ).val.app (op V) ((π).val.app (op V) (nb (op V) x y)) = 0 := by
  let RS : TopCat.Sheaf AddCommGrpCat.{u} X :=
    ⟨(SheafOfModules.unit R).val.presheaf, (SheafOfModules.unit R).isSheaf⟩
  apply RS.eq_of_locally_eq' (fun i => V ⊓ U i) V (fun _ => homOfLE inf_le_left)
    (by rw [← inf_iSup_eq, hcover, inf_top_eq])
  intro i
  let W := V ⊓ U i
  let f : op V ⟶ op W := (homOfLE inf_le_left).op
  change (SheafOfModules.unit R).val.map f
    ((χ).val.app (op V) ((π).val.app (op V) (nb (op V) x y))) =
      (SheafOfModules.unit R).val.map f 0
  rw [map_zero]
  have hn : (K).val.map f ((π).val.app (op V) (nb (op V) x y)) =
      (π).val.app (op W) (nb (op W) ((N).val.map f x) ((N).val.map f y)) :=
    (PresheafOfModules.naturality_apply (π).val f _).symm.trans
      (congrArg ((π).val.app (op W))
        (normalizerSectionBracket_restrict E I action action_res jacobi f x y))
  exact (PresheafOfModules.naturality_apply (χ).val f _).symm.trans
    ((congrArg ((χ).val.app (op W)) hn).trans
      ((quotientCharacterOfTrivializations_local E I action action_res ring_comm
        action_smul_right habelian U hcover triv i W inf_le_right _).trans
        (sectionFrameCharacter_bracket E I action action_res jacobi ring_comm
          action_smul_right (op W) (lineTrivializationAt E I (triv i) W inf_le_right) _ _)))

/-- The character on the actual quotient sheaf kills brackets of arbitrary
quotient sections, including sections with no lift on their original open. -/
theorem quotientCharacterOfTrivializations_bracket (V : Opens X)
    (x y : (K).val.obj (op V)) : (χ).val.app (op V) (br V x y) = 0 := by
  apply sheaf_eq_of_local_lifts (π) (sheaf_cokernel_locallySurjective _)
    (SheafOfModules.unit R) V x y y
  intro W h a b c ha hb hc
  change (π).val.app (op W) a = (K).val.map (homOfLE h).op x at ha
  change (π).val.app (op W) b = (K).val.map (homOfLE h).op y at hb
  change (SheafOfModules.unit R).val.map (homOfLE h).op ((χ).val.app (op V) (br V x y)) =
    (SheafOfModules.unit R).val.map (homOfLE h).op 0
  rw [map_zero]
  have hn : (K).val.map (homOfLE h).op (br V x y) =
      (π).val.app (op W) (nb (op W) a b) := by
    rw [normalizerQuotientBracket_restrict, ← ha, ← hb, normalizerQuotientBracket_projection]
  exact (PresheafOfModules.naturality_apply (χ).val (homOfLE h).op _).symm.trans
    ((congrArg ((χ).val.app (op W)) hn).trans
      (quotientCharacterOfTrivializations_projected_bracket E I action action_res habelian
        jacobi ring_comm action_smul_right U hcover triv W a b))

/-- The constructed sheaf character, bundled on each open as a Lie-algebra
homomorphism to the commutative section ring with its zero commutator. -/
def quotientCharacterLieHom (V : Opens X) :
    letI := commutativeSectionRing ring_comm (op V)
    letI := normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating V
    letI := normalizerQuotientLieAlgebra E I action action_res habelian jacobi skew alternating
      ring_comm V
    letI := LieRing.ofAssociativeRing (A := R.obj.obj (op V))
    (K).val.obj (op V) →ₗ⁅R.obj.obj (op V)⁆ R.obj.obj (op V) := by
  letI := commutativeSectionRing ring_comm (op V)
  letI := normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating V
  letI := normalizerQuotientLieAlgebra E I action action_res habelian jacobi skew alternating
    ring_comm V
  letI := LieRing.ofAssociativeRing (A := R.obj.obj (op V))
  refine { ((χ).val.app (op V)).hom with map_lie' := ?_ }
  intro x y
  let fx : R.obj.obj (op V) := (χ).val.app (op V) x
  let fy : R.obj.obj (op V) := (χ).val.app (op V) y
  change (χ).val.app (op V) (br V x y) = fx * fy - fy * fx
  rw [quotientCharacterOfTrivializations_bracket, ring_comm, sub_self]

/-- Bundling the character as a Lie homomorphism preserves the original
sheaf character on every quotient section. -/
theorem quotientCharacterLieHom_apply (V : Opens X) (x : (K).val.obj (op V)) :
    quotientCharacterLieHom E I action action_res habelian jacobi skew alternating
      ring_comm action_smul_right U hcover triv V x = (χ).val.app (op V) x := rfl

end Normalizer
