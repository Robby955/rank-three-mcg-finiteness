import Normalizer.NormalizerSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! The normalizer character from genuine local sheaf trivializations.
A trivialization is an isomorphism from the restricted unit module sheaf to
the restricted line subsheaf. Local character maps and their compatibility
are derived, not supplied. The curve-specific existence of these
trivializations and constancy of global regular functions remain separate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Opposite TopologicalSpace

universe u
variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  (E : SheafOfModules.{u} R) (I : E.Submodule)
  (action : ∀ V, E.val.obj V → E.val.obj V →ₗ[R.obj.obj V] E.val.obj V)
  (action_res : ∀ {V W} (f : V ⟶ W) (m x : E.val.obj V),
    E.val.map f (action V m x) = action W (E.val.map f m) (E.val.map f x))

/-- Evaluation of a genuine local sheaf trivialization gives a basis
isomorphism on each smaller open. -/
def lineTrivializationAt {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ I.toSheafOfModules.over U)
    (V : Opens X) (h : V ≤ U) :
    R.obj.obj (op V) ≃ₗ[R.obj.obj (op V)] I.obj (op V) :=
  ((SheafOfModules.evaluation (R.over U) (op (Over.mk (homOfLE h)))).mapIso e).toLinearEquiv

/-- The basis isomorphisms commute with restriction because they come
from a morphism of actual sheaves of modules. -/
theorem lineTrivializationAt_restrict {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ I.toSheafOfModules.over U)
    (V W : Opens X) (h : V ≤ W) (k : W ≤ U) (r : R.obj.obj (op W)) :
    I.toSheafOfModules.val.map (homOfLE h).op (lineTrivializationAt E I e W k r) =
      lineTrivializationAt E I e V (h.trans k) (R.obj.map (homOfLE h).op r) := by
  let f : Over.mk (homOfLE (h.trans k)) ⟶ Over.mk (homOfLE k) :=
    Over.homMk (homOfLE h)
  exact (PresheafOfModules.naturality_apply e.hom.val f.op r).symm

private def sectionAction (V)
    (t : R.obj.obj V ≃ₗ[R.obj.obj V] I.obj V) :
    (normalizerSubsheaf E I action action_res).obj V →ₗ[R.obj.obj V] I.obj V :=
  ((action V (t 1 : E.val.obj V)).comp
    ((normalizerSubsheaf E I action action_res).obj V).subtype).codRestrict (I.obj V) (by
      intro x
      exact normalizerSubsheaf_action E I action action_res V x (t 1) x.property (t 1).property)

/-- The scalar action coefficient, obtained from a genuine basis
isomorphism rather than postulated as a character. -/
def sectionFrameCharacter (V)
    (t : R.obj.obj V ≃ₗ[R.obj.obj V] I.obj V) :
    (normalizerSubsheaf E I action action_res).obj V →ₗ[R.obj.obj V] R.obj.obj V :=
  t.symm.toLinearMap.comp (sectionAction E I action action_res V t)

private theorem frame_scalar (V)
    (t : R.obj.obj V ≃ₗ[R.obj.obj V] I.obj V) (r : R.obj.obj V) :
    (t r : E.val.obj V) = r • (t 1 : E.val.obj V) := by
  simpa using congrArg Subtype.val (t.map_smul r (1 : R.obj.obj V))

/-- The constructed coefficient satisfies its defining action equation. -/
theorem sectionFrameCharacter_action (V)
    (t : R.obj.obj V ≃ₗ[R.obj.obj V] I.obj V)
    (x : (normalizerSubsheaf E I action action_res).obj V) :
    action V (t 1) x = sectionFrameCharacter E I action action_res V t x •
      (t 1 : E.val.obj V) := by
  rw [← frame_scalar E I V t]
  exact (congrArg Subtype.val (t.apply_symm_apply
    (sectionAction E I action action_res V t x))).symm

/-- Injectivity of the actual basis isomorphism makes the coefficient unique. -/
theorem sectionFrameCharacter_unique (V)
    (t : R.obj.obj V ≃ₗ[R.obj.obj V] I.obj V)
    (x : (normalizerSubsheaf E I action action_res).obj V) (a : R.obj.obj V)
    (ha : action V (t 1) x = a • (t 1 : E.val.obj V)) :
    sectionFrameCharacter E I action action_res V t x = a := by
  apply t.injective
  apply Subtype.ext
  rw [frame_scalar E I V t (sectionFrameCharacter E I action action_res V t x),
    frame_scalar E I V t a, ← sectionFrameCharacter_action, ha]

variable
  (ring_comm : ∀ V (a b : R.obj.obj V), a * b = b * a)
  (action_smul_right : ∀ V (a : R.obj.obj V) (m x : E.val.obj V),
    action V (a • m) x = a • action V m x)

include ring_comm action_smul_right in
/-- Over the commutative section ring, the coefficient acts by scalar
multiplication on every section of the line, not just the selected basis. -/
theorem sectionFrameCharacter_action_all (V)
    (t : R.obj.obj V ≃ₗ[R.obj.obj V] I.obj V)
    (x : (normalizerSubsheaf E I action action_res).obj V) (m : I.obj V) :
    action V m x = sectionFrameCharacter E I action action_res V t x •
      (m : E.val.obj V) := by
  have hm : (m : E.val.obj V) = t.symm m • (t 1 : E.val.obj V) := by
    simpa using frame_scalar E I V t (t.symm m)
  rw [hm, action_smul_right, sectionFrameCharacter_action, smul_smul, smul_smul,
    ring_comm]

include ring_comm action_smul_right in
/-- The scalar coefficient is independent of the basis isomorphism.
No transition coefficient or overlap agreement is an input. -/
theorem sectionFrameCharacter_independent (V)
    (t q : R.obj.obj V ≃ₗ[R.obj.obj V] I.obj V)
    (x : (normalizerSubsheaf E I action action_res).obj V) :
    sectionFrameCharacter E I action action_res V t x =
      sectionFrameCharacter E I action action_res V q x := by
  symm
  apply sectionFrameCharacter_unique E I action action_res V q x
  exact sectionFrameCharacter_action_all E I action action_res ring_comm
    action_smul_right V t x (q 1)

/-- The local character on a trivializing open and every subopen is
computed from the actual sheaf isomorphism. -/
def trivializationCharacter {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ I.toSheafOfModules.over U)
    (V : Opens X) (h : V ≤ U) :
    (normalizerSubsheaf E I action action_res).toSheafOfModules.val.obj (op V)
      →ₗ[R.obj.obj (op V)] R.obj.obj (op V) :=
  sectionFrameCharacter E I action action_res (op V) (lineTrivializationAt E I e V h)

/-- Local characters commute with restriction, derived from the
trivialization's naturality and the bracket's restriction law. -/
theorem trivializationCharacter_restrict {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ I.toSheafOfModules.over U)
    (V W : Opens X) (h : V ≤ W) (k : W ≤ U)
    (x : (normalizerSubsheaf E I action action_res).toSheafOfModules.val.obj (op W)) :
    R.obj.map (homOfLE h).op (trivializationCharacter E I action action_res e W k x) =
      trivializationCharacter E I action action_res e V (h.trans k)
        ((normalizerSubsheaf E I action action_res).toSheafOfModules.val.restrictₛₗ
          (homOfLE h).op x) := by
  symm
  apply sectionFrameCharacter_unique E I action action_res (op V)
    (lineTrivializationAt E I e V (h.trans k))
  have hf : E.val.map (homOfLE h).op
      (lineTrivializationAt E I e W k 1 : E.val.obj (op W)) =
      (lineTrivializationAt E I e V (h.trans k) 1 : E.val.obj (op V)) := by
    have ht := congrArg (fun z : I.obj (op V) => (z : E.val.obj (op V)))
      (lineTrivializationAt_restrict E I e V W h k 1)
    change E.val.map (homOfLE h).op (lineTrivializationAt E I e W k 1 : E.val.obj (op W)) =
      (lineTrivializationAt E I e V (h.trans k) (R.obj.map (homOfLE h).op 1) : E.val.obj (op V)) at ht
    simpa using ht
  have ha := congrArg (fun z => E.val.map (homOfLE h).op z)
    (sectionFrameCharacter_action E I action action_res (op W)
      (lineTrivializationAt E I e W k) x)
  rw [action_res, E.val.map_smul, hf] at ha
  exact ha

include ring_comm action_smul_right in
/-- Characters from two genuine trivializations agree on every common
subopen. Agreement is proved from the action, not imposed on the cover. -/
theorem trivializationCharacter_agree {U W : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ I.toSheafOfModules.over U)
    (f : (SheafOfModules.unit R).over W ≅ I.toSheafOfModules.over W)
    (V : Opens X) (h : V ≤ U) (k : V ≤ W)
    (x : (normalizerSubsheaf E I action action_res).toSheafOfModules.val.obj (op V)) :
    trivializationCharacter E I action action_res e V h x =
      trivializationCharacter E I action action_res f V k x :=
  sectionFrameCharacter_independent E I action action_res ring_comm action_smul_right
    (op V) (lineTrivializationAt E I e V h) (lineTrivializationAt E I f V k) x

variable (habelian : ∀ V (x m : E.val.obj V), x ∈ I.obj V → m ∈ I.obj V →
  action V m x = 0)

/-- The local character kills the line, derived from its abelian bracket
and the action equation in a genuine frame. -/
theorem trivializationCharacter_kills_line {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ I.toSheafOfModules.over U)
    (V : Opens X) (h : V ≤ U) (s : I.toSheafOfModules.val.obj (op V)) :
    trivializationCharacter E I action action_res e V h
      ((normalizerLineInclusion E I action action_res habelian).val.app (op V) s) = 0 := by
  apply sectionFrameCharacter_unique E I action action_res (op V)
    (lineTrivializationAt E I e V h)
  rw [zero_smul]
  exact habelian (op V) s.val _ s.property
    (lineTrivializationAt E I e V h 1).property

variable {ι : Type u} (U : ι → Opens X) (hcover : iSup U = ⊤)
  (triv : ∀ i, (SheafOfModules.unit R).over (U i) ≅ I.toSheafOfModules.over (U i))

/-- The normalizer character from a cover of genuine line-sheaf
trivializations. No local character or compatibility law is an input. -/
def normalizerCharacterOfTrivializations :
    (normalizerSubsheaf E I action action_res).toSheafOfModules ⟶ SheafOfModules.unit R :=
  gluedNormalizerCharacter E I action action_res U hcover
    (fun i V h => trivializationCharacter E I action action_res (triv i) V h)
    (fun i V W h k x => trivializationCharacter_restrict E I action action_res (triv i) V W h k x)
    (fun i j V h k x => trivializationCharacter_agree E I action action_res ring_comm
      action_smul_right (triv i) (triv j) V h k x)

/-- The action on an abelian line sheaf gives a character on the actual
sheaf quotient, using genuine local trivializations and proved descent. -/
def quotientCharacterOfTrivializations :
    normalizerQuotientSheaf E I action action_res habelian ⟶ SheafOfModules.unit R :=
  gluedNormalizerQuotientCharacter E I action action_res habelian U hcover
    (fun i V h => trivializationCharacter E I action action_res (triv i) V h)
    (fun i V W h k x => trivializationCharacter_restrict E I action action_res (triv i) V W h k x)
    (fun i j V h k x => trivializationCharacter_agree E I action action_res ring_comm
      action_smul_right (triv i) (triv j) V h k x)
    (fun i V h s => trivializationCharacter_kills_line E I action action_res habelian
      (triv i) V h s)

/-- Evaluation on a local quotient lift gives its computed scalar action. -/
theorem quotientCharacterOfTrivializations_local (i : ι) (V : Opens X) (h : V ≤ U i)
    (x : (normalizerSubsheaf E I action action_res).toSheafOfModules.val.obj (op V)) :
    (quotientCharacterOfTrivializations E I action action_res ring_comm action_smul_right
      habelian U hcover triv).val.app (op V)
        ((Limits.cokernel.π (normalizerLineInclusion E I action action_res habelian)).val.app
          (op V) x) = trivializationCharacter E I action action_res (triv i) V h x :=
  gluedNormalizerQuotientCharacter_local E I action action_res habelian U hcover _ _ _ _ i V h x

/-- The constructed quotient character satisfies the manuscript's action
equation on every line section of a trivializing open. -/
theorem quotientCharacterOfTrivializations_action (i : ι) (V : Opens X) (h : V ≤ U i)
    (x : (normalizerSubsheaf E I action action_res).toSheafOfModules.val.obj (op V))
    (m : I.obj (op V)) :
    action (op V) m x.val =
      (quotientCharacterOfTrivializations E I action action_res ring_comm action_smul_right
        habelian U hcover triv).val.app (op V)
          ((Limits.cokernel.π (normalizerLineInclusion E I action action_res habelian)).val.app
            (op V) x) • (m : E.val.obj (op V)) := by
  rw [quotientCharacterOfTrivializations_local E I action action_res ring_comm
    action_smul_right habelian U hcover triv i V h x]
  exact sectionFrameCharacter_action_all E I action action_res ring_comm action_smul_right
    (op V) (lineTrivializationAt E I (triv i) V h) x m

include action_smul_right in
private theorem rank_one_action_zero (V)
    (t : R.obj.obj V ≃ₗ[R.obj.obj V] I.obj V)
    (alternating : ∀ z : E.val.obj V, action V z z = 0)
    (x m : I.obj V) : action V m x = 0 := by
  have hx : (x : E.val.obj V) = t.symm x • (t 1 : E.val.obj V) := by
    simpa using frame_scalar E I V t (t.symm x)
  have hm : (m : E.val.obj V) = t.symm m • (t 1 : E.val.obj V) := by
    simpa using frame_scalar E I V t (t.symm m)
  rw [hx, hm, action_smul_right, map_smul, alternating, smul_zero, smul_zero]

include action_res action_smul_right hcover triv in
/-- A rank-one subsheaf with genuine local trivializations is abelian for
an alternating bilinear bracket. The conclusion is derived by local
coordinates and sheaf separatedness, not required as a geometric input. -/
theorem lineSubsheaf_abelian_of_trivializations
    (alternating : ∀ V (z : E.val.obj V), action V z z = 0)
    (V) (x m : E.val.obj V) (hx : x ∈ I.obj V) (hm : m ∈ I.obj V) :
    action V m x = 0 := by
  let ES : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨E.val.presheaf, E.isSheaf⟩
  apply ES.eq_of_locally_eq' (fun i => V.unop ⊓ U i) V.unop
    (fun _ => homOfLE inf_le_left) (by rw [← inf_iSup_eq, hcover, inf_top_eq])
  intro i
  change E.val.map (homOfLE inf_le_left).op (action V m x) =
    E.val.map (homOfLE inf_le_left).op 0
  rw [action_res, map_zero]
  exact rank_one_action_zero E I action action_smul_right (op (V.unop ⊓ U i))
    (lineTrivializationAt E I (triv i) (V.unop ⊓ U i) inf_le_right) (alternating _)
    ⟨E.val.map (homOfLE inf_le_left).op x, I.map_mem _ hx⟩
    ⟨E.val.map (homOfLE inf_le_left).op m, I.map_mem _ hm⟩

/-- The quotient character for a locally trivial rank-one subsheaf with
alternating bilinear bracket. Local maps, compatibility, and abelianness
are all derived from the actual trivializations and operator identities. -/
def lineQuotientCharacter
    (alternating : ∀ V (z : E.val.obj V), action V z z = 0) :
    normalizerQuotientSheaf E I action action_res
      (lineSubsheaf_abelian_of_trivializations E I action action_res action_smul_right
        U hcover triv alternating) ⟶ SheafOfModules.unit R :=
  quotientCharacterOfTrivializations E I action action_res ring_comm action_smul_right
    (lineSubsheaf_abelian_of_trivializations E I action action_res action_smul_right
      U hcover triv alternating) U hcover triv

end Normalizer
