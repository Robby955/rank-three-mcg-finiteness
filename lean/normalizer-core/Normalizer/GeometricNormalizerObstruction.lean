import Normalizer.NormalizerStalkIntegration
import Normalizer.ActualNormalizerQuotient

/-! The matrix obstruction applied to the actual intrinsic generic stalk
of a sheaf normalizer quotient. The ambient generic Lie identification
and the boundary law remain explicit; their compatibility is derived. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite
attribute [local instance] LieRing.ofAssociativeRing
universe u
variable {X : Scheme.{u}} [IsIntegral X] [CharZero X.functionField]
  (E : X.Modules) (I : E.Submodule)
  (action : ∀ V, E.val.obj V → E.val.obj V →ₗ[X.ringCatSheaf.obj.obj V] E.val.obj V)
  (action_res : ∀ {V W} (f : V ⟶ W) (m s : E.val.obj V),
    E.val.map f (action V m s) = action W (E.val.map f m) (E.val.map f s))
  (action_smul_right : ∀ V (a : X.ringCatSheaf.obj.obj V) (m s : E.val.obj V),
    action V (a • m) s = a • action V m s)
  (habelian : ∀ V (s m : E.val.obj V), s ∈ I.obj V → m ∈ I.obj V →
    action V m s = 0)
  (jacobi : ∀ V (a b m : E.val.obj V),
    action V m (action V b a) =
      action V (action V m b) a - action V (action V m a) b)
  (skew : ∀ V (a b : E.val.obj V), action V b a = -action V a b)
  {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
  (triv : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅
    I.toSheafOfModules.over (U i))
  (e : E.presheaf.stalk (genericPoint X) ≃ₗ[X.functionField] SlThree X.functionField)
  (he : ∀ (V : X.Opens) (hxV : genericPoint X ∈ V) (m s : Γ(E, V)),
    e (E.presheaf.germ V (genericPoint X) hxV (action (op V) m s)) =
      ⁅e (E.presheaf.germ V (genericPoint X) hxV s),
        e (E.presheaf.germ V (genericPoint X) hxV m)⁆)

private abbrev quotientModule : X.Modules :=
  normalizerQuotientSheaf E I action action_res habelian
local notation "Q" => quotientModule E I action action_res habelian
local notation "χ" => quotientCharacterOfTrivializations E I action action_res
  (fun V a b => @mul_comm (X.presheaf.obj V) _ a b)
  action_smul_right habelian U hcover triv

include e he in
/-- A boundary-law subspace of the actual intrinsic generic normalizer
quotient has dimension at most two, once its ambient generic Lie algebra
is genuinely identified with sl3. The line generator is proved nonzero,
and the quotient bracket and character comparisons are constructed. -/
theorem actualNormalizer_generic_boundary_finrank
    (W : Submodule X.functionField ((Q).presheaf.stalk (genericPoint X)))
    (hlaw : BoundaryLaw W
      (fun a b => normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew
        (genericPoint X) a b)
      (schemeModuleStalkCharacter Q χ (genericPoint X))) :
    Module.finrank X.functionField W < 3 := by
  have hη : genericPoint X ∈ iSup U := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hη
  let m := e (schemeLineFrameGerm E I (genericPoint X) (U i) hi (triv i))
  have hfaith : Function.Injective (fun a : X.functionField => a • m) :=
    schemeLineFrameGerm_map_smul_injective E I (genericPoint X) e (U i) hi (triv i)
  have hm : m ≠ 0 := by
    intro hz
    exact one_ne_zero (hfaith (show (1 : X.functionField) • m = 0 • m by simp [hz]))
  let θ := schemeNormalizerQuotientStalkEquiv E I action action_res action_smul_right
    habelian (genericPoint X) e he (U i) hi (triv i)
  have hmap : BoundaryLaw (W.map θ.toLinearMap) (fun a b => ⁅a, b⁆)
      (slThreeLineCharacter m hm) :=
    normalizerQuotientStalkEquiv_boundary_identity E I action action_res action_smul_right
      habelian jacobi skew (genericPoint X) e he U hcover triv i hi W hlaw
  have hdim := slThree_quotient_boundary_finrank m hm (W.map θ.toLinearMap) hmap
  rwa [LinearEquiv.finrank_map_eq] at hdim

end Normalizer
