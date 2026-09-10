import Normalizer.NormalizerQuotientStalk
import Normalizer.SheafStalkFunctional

/-! The character of the actual normalizer quotient sheaf agrees with the
scalar-action character under the constructed quotient-stalk comparison. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry Opposite

universe u
variable {X : Scheme.{u}} (E : X.Modules) (I : E.Submodule)

/-- The actual frame germ remains faithful after an ambient linear
identification; its coefficient injectivity is derived from the sheaf frame. -/
theorem schemeLineFrameGerm_map_smul_injective
    (x : X) {L : Type u} [AddCommGroup L] [Module (X.presheaf.stalk x) L]
    (e : E.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] L)
    (U : X.Opens) (hxU : x ∈ U)
    (t : (SheafOfModules.unit X.ringCatSheaf).over U ≅ I.toSheafOfModules.over U) :
    Function.Injective (fun a : X.presheaf.stalk x =>
      a • e (schemeLineFrameGerm E I x U hxU t)) := by
  intro a b hab
  apply schemeLineFrameGerm_smul_injective E I x U hxU t
  apply e.injective
  change e (a • schemeLineFrameGerm E I x U hxU t) =
    e (b • schemeLineFrameGerm E I x U hxU t)
  rw [map_smul, map_smul]
  exact hab

variable
  (action : ∀ V, E.val.obj V → E.val.obj V →ₗ[X.ringCatSheaf.obj.obj V] E.val.obj V)
  (action_res : ∀ {V W} (f : V ⟶ W) (m s : E.val.obj V),
    E.val.map f (action V m s) = action W (E.val.map f m) (E.val.map f s))
  (action_smul_right : ∀ V (a : X.ringCatSheaf.obj.obj V) (m s : E.val.obj V),
    action V (a • m) s = a • action V m s)
  (habelian : ∀ V (s m : E.val.obj V), s ∈ I.obj V → m ∈ I.obj V →
    action V m s = 0)
  {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
  (triv : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅
    I.toSheafOfModules.over (U i))
  (x : X) (i : ι) (hxi : x ∈ U i)
  {L : Type u} [LieRing L] [LieAlgebra (X.presheaf.stalk x) L]
  (e : E.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] L)
  (he : ∀ (V : X.Opens) (hxV : x ∈ V) (m s : Γ(E, V)),
    e (E.presheaf.germ V x hxV (action (op V) m s)) =
      ⁅e (E.presheaf.germ V x hxV s), e (E.presheaf.germ V x hxV m)⁆)

local notation "Nₛ" => normalizerSubsheaf E I action action_res
local notation "iₛ" => normalizerLineInclusion E I action action_res habelian
local notation "Qₛ" => normalizerQuotientSheaf E I action action_res habelian
local notation "mₓ" => schemeLineFrameGerm E I x (U i) hxi (triv i)
local notation "ψₛ" => quotientCharacterOfTrivializations E I action action_res
  (fun V a b => @mul_comm (X.presheaf.obj V) _ a b)
  action_smul_right habelian U hcover triv

/-- The actual constructed sheaf character is identified with the
algebraic scalar-action character on every quotient stalk element.
Character compatibility and faithfulness of the frame are proved. -/
theorem schemeNormalizerQuotientStalkCharacter
    (z : (Scheme.Modules.presheaf Qₛ).stalk x) :
    schemeStalkFunctional ψₛ x z =
      quotientFrameCharacter (e mₓ)
        (schemeLineFrameGerm_map_smul_injective E I x e (U i) hxi (triv i))
        (schemeNormalizerQuotientStalkEquiv E I action action_res action_smul_right
          habelian x e he (U i) hxi (triv i) z) := by
  obtain ⟨a, rfl⟩ := schemeCokernelStalk_surjective iₛ x z
  obtain ⟨V, hVU, hxV, s, rfl⟩ :=
    (Scheme.Modules.presheaf (Nₛ).toSheafOfModules).exists_le_germ_eq a hxi
  rw [schemeNormalizerQuotientStalkEquiv_projection, quotientFrameCharacter_mk]
  symm
  apply frameCharacter_eq
  let mV := lineTrivializationAt E I (triv i) V hVU 1
  have hmV : E.presheaf.germ V x hxV (mV : E.val.obj (op V)) = mₓ := by
    have hr := congrArg Subtype.val
      (lineTrivializationAt_restrict E I (triv i) V (U i) hVU le_rfl 1)
    simp only [map_one] at hr
    have hf : E.presheaf.map (homOfLE hVU).op
        (lineTrivializationAt E I (triv i) (U i) le_rfl 1 : E.val.obj (op (U i))) =
        (mV : E.val.obj (op V)) := hr
    exact (congrArg (E.presheaf.germ V x hxV) hf).symm.trans
      (E.presheaf.germ_res_apply (homOfLE hVU) x hxV _)
  have hact := quotientCharacterOfTrivializations_action E I action action_res
    (fun V a b => @mul_comm (X.presheaf.obj V) _ a b)
    action_smul_right habelian U hcover triv i V hVU s mV
  have hg := congrArg (fun b : Γ(E, V) => e (E.presheaf.germ V x hxV b)) hact
  rw [he, schemeModule_germ_smul, map_smul, hmV] at hg
  change ⁅e (schemeModuleStalkMap (Nₛ).ι x
    ((Scheme.Modules.presheaf (Nₛ).toSheafOfModules).germ V x hxV s)), e mₓ⁆ = _
  rw [schemeModuleStalkMap_germ, schemeModuleStalkMap_germ]
  have hc := schemeStalkFunctional_germ ψₛ x V hxV ((cokernel.π iₛ).val.app (op V) s)
  exact hg.trans (congrArg (fun a : X.presheaf.stalk x => a • e mₓ) hc).symm

end Normalizer
