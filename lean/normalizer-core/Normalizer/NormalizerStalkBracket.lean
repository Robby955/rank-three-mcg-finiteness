import Normalizer.NormalizerQuotientStalk

/-! The actual quotient-stalk comparison preserves the sheaf bracket on
all germs, using simultaneous local representatives of quotient sections. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u
variable {X : Scheme.{u}} (E : X.Modules) (I : E.Submodule)
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
  (x : X) {L : Type u} [LieRing L] [LieAlgebra (X.presheaf.stalk x) L]
  (e : E.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] L)
  (he : ∀ (V : X.Opens) (hxV : x ∈ V) (m s : Γ(E, V)),
    e (E.presheaf.germ V x hxV (action (op V) m s)) =
      ⁅e (E.presheaf.germ V x hxV s), e (E.presheaf.germ V x hxV m)⁆)
  (U : X.Opens) (hxU : x ∈ U)
  (t : (SheafOfModules.unit X.ringCatSheaf).over U ≅ I.toSheafOfModules.over U)

private abbrev N := (normalizerSubsheaf E I action action_res).toSheafOfModules
private abbrev Q := normalizerQuotientSheaf E I action action_res habelian
local notation "π" => cokernel.π (normalizerLineInclusion E I action action_res habelian)
local notation "θ" => schemeNormalizerQuotientStalkEquiv E I action action_res
  action_smul_right habelian x e he U hxU t
local notation "br" => normalizerQuotientBracket E I action action_res habelian jacobi skew

private theorem bracket_on_lifts (V : X.Opens) (hxV : x ∈ V)
    (a b : (N E I action action_res).val.obj (op V)) :
    θ ((Scheme.Modules.presheaf (Q E I action action_res habelian)).germ V x hxV
      (br V ((π).val.app (op V) a) ((π).val.app (op V) b))) =
    ⁅θ ((Scheme.Modules.presheaf (Q E I action action_res habelian)).germ V x hxV
      ((π).val.app (op V) a)),
     θ ((Scheme.Modules.presheaf (Q E I action action_res habelian)).germ V x hxV
      ((π).val.app (op V) b))⁆ := by
  rw [normalizerQuotientBracket_projection]
  have hp (s : (N E I action action_res).val.obj (op V)) :
      θ ((Scheme.Modules.presheaf (Q E I action action_res habelian)).germ V x hxV
        ((π).val.app (op V) s)) =
      (frameIdeal (e (schemeLineFrameGerm E I x U hxU t))).toSubmodule.mkQ
        (schemeNormalizerStalkEquiv E I action action_res action_smul_right x e he U hxU t
          ((Scheme.Modules.presheaf (N E I action action_res)).germ V x hxV s)) := by
    exact (congrArg θ (schemeModuleStalkMap_germ π x V hxV s)).symm.trans
      (schemeNormalizerQuotientStalkEquiv_projection E I action action_res action_smul_right
        habelian x e he U hxU t _)
  rw [hp, hp, hp]
  change (frameIdeal (e (schemeLineFrameGerm E I x U hxU t))).toSubmodule.mkQ _ =
    (frameIdeal (e (schemeLineFrameGerm E I x U hxU t))).toSubmodule.mkQ _
  congr 1
  apply Subtype.ext
  change e (schemeModuleStalkMap (normalizerSubsheaf E I action action_res).ι x
    ((Scheme.Modules.presheaf (N E I action action_res)).germ V x hxV
      (normalizerSectionBracket E I action action_res jacobi (op V) a b))) =
    ⁅e (schemeModuleStalkMap (normalizerSubsheaf E I action action_res).ι x
      ((Scheme.Modules.presheaf (N E I action action_res)).germ V x hxV a)),
     e (schemeModuleStalkMap (normalizerSubsheaf E I action action_res).ι x
      ((Scheme.Modules.presheaf (N E I action action_res)).germ V x hxV b))⁆
  rw [schemeModuleStalkMap_germ, schemeModuleStalkMap_germ, schemeModuleStalkMap_germ]
  exact he V hxV b.val a.val

/-- The quotient comparison preserves the actual sheaf bracket on germs
of arbitrary quotient sections. Local lifts are constructed around the
point; no surjectivity on sections of the original open is assumed. -/
theorem schemeNormalizerQuotientStalkEquiv_bracket (V : X.Opens) (hxV : x ∈ V)
    (a b : (Q E I action action_res habelian).val.obj (op V)) :
    θ ((Scheme.Modules.presheaf (Q E I action action_res habelian)).germ V x hxV (br V a b)) =
    ⁅θ ((Scheme.Modules.presheaf (Q E I action action_res habelian)).germ V x hxV a),
     θ ((Scheme.Modules.presheaf (Q E I action action_res habelian)).germ V x hxV b)⁆ := by
  have hq := sheaf_cokernel_locallySurjective
    (normalizerLineInclusion E I action action_res habelian)
  have hc := (Opens.grothendieckTopology X).intersection_covering
    (hq.imageSieve_mem a) (hq.imageSieve_mem b)
  obtain ⟨W, j, ⟨⟨a', ha⟩, ⟨b', hb⟩⟩, hxW⟩ := hc x hxV
  let Qp := Scheme.Modules.presheaf (Q E I action action_res habelian)
  have hga : Qp.germ W x hxW ((π).val.app (op W) a') = Qp.germ V x hxV a :=
    (congrArg (Qp.germ W x hxW) ha).trans (Qp.germ_res_apply j x hxW a)
  have hgb : Qp.germ W x hxW ((π).val.app (op W) b') = Qp.germ V x hxV b :=
    (congrArg (Qp.germ W x hxW) hb).trans (Qp.germ_res_apply j x hxW b)
  have hgr : Qp.germ V x hxV (br V a b) =
      Qp.germ W x hxW (br W ((π).val.app (op W) a') ((π).val.app (op W) b')) := by
    have hr := normalizerQuotientBracket_restrict E I action action_res habelian jacobi skew
      V W j.le a b
    have hl : (Q E I action action_res habelian).val.map j.op (br V a b) =
        br W ((π).val.app (op W) a') ((π).val.app (op W) b') := by
      exact hr.trans (congrArg₂ (br W) ha.symm hb.symm)
    exact (Qp.germ_res_apply j x hxW (br V a b)).symm.trans
      (congrArg (Qp.germ W x hxW) hl)
  change θ (Qp.germ V x hxV (br V a b)) = ⁅θ (Qp.germ V x hxV a), θ (Qp.germ V x hxV b)⁆
  rw [hgr, ← hga, ← hgb]
  exact bracket_on_lifts E I action action_res action_smul_right habelian jacobi skew
    x e he U hxU t W hxW a' b'

end Normalizer
