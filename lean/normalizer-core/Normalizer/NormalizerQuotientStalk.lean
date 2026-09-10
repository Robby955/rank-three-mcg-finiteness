import Normalizer.LineStalk

/-! The actual sheaf normalizer quotient at a point, compared with the
actual algebraic normalizer quotient in an identified ambient Lie algebra. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry Opposite

universe u
variable {X : Scheme.{u}} (E : X.Modules) (I : E.Submodule)
  (action : ∀ V, E.val.obj V → E.val.obj V →ₗ[X.ringCatSheaf.obj.obj V] E.val.obj V)
  (action_res : ∀ {V W} (f : V ⟶ W) (m s : E.val.obj V),
    E.val.map f (action V m s) = action W (E.val.map f m) (E.val.map f s))
  (action_smul_right : ∀ V (a : X.ringCatSheaf.obj.obj V) (m s : E.val.obj V),
    action V (a • m) s = a • action V m s)
  (habelian : ∀ V (s m : E.val.obj V), s ∈ I.obj V → m ∈ I.obj V →
    action V m s = 0)
  (x : X) {L : Type u} [LieRing L] [LieAlgebra (X.presheaf.stalk x) L]
  (e : E.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] L)
  (he : ∀ (V : X.Opens) (hxV : x ∈ V) (m s : Γ(E, V)),
    e (E.presheaf.germ V x hxV (action (op V) m s)) =
      ⁅e (E.presheaf.germ V x hxV s), e (E.presheaf.germ V x hxV m)⁆)
  (U : X.Opens) (hxU : x ∈ U)
  (t : (SheafOfModules.unit X.ringCatSheaf).over U ≅ I.toSheafOfModules.over U)

local notation "Nₛ" => normalizerSubsheaf E I action action_res
local notation "iₛ" => normalizerLineInclusion E I action action_res habelian
local notation "mₓ" => schemeLineFrameGerm E I x U hxU t
local notation "nₓ" => schemeNormalizerStalkEquiv E I action action_res action_smul_right
  x e he U hxU t

private theorem stalk_inclusion_comp
    (a : (Scheme.Modules.presheaf I.toSheafOfModules).stalk x) :
    schemeModuleStalkMap (Nₛ).ι x (schemeModuleStalkMap iₛ x a) =
      schemeModuleStalkMap I.ι x a := by
  obtain ⟨V, hxV, s, rfl⟩ :=
    (Scheme.Modules.presheaf I.toSheafOfModules).exists_germ_eq a
  rw [schemeModuleStalkMap_germ, schemeModuleStalkMap_germ,
    schemeModuleStalkMap_germ]
  rfl

/-- The constructed normalizer-stalk equivalence sends the actual line
inclusion image onto the actual frame ideal. -/
theorem schemeNormalizerStalkEquiv_line :
    (LinearMap.range (schemeModuleStalkMap iₛ x)).map (nₓ).toLinearMap =
      (frameIdeal (R := X.presheaf.stalk x) (e mₓ)).toSubmodule := by
  ext z
  constructor
  · rintro ⟨b, ⟨a, rfl⟩, rfl⟩
    change (nₓ (schemeModuleStalkMap iₛ x a) : L) ∈
      Submodule.span (X.presheaf.stalk x) {e mₓ}
    rw [schemeNormalizerStalkEquiv_apply, stalk_inclusion_comp]
    have ha : schemeModuleStalkMap I.ι x a ∈
        Submodule.span (X.presheaf.stalk x) {mₓ} := by
      rw [← schemeLineStalk_range E I x U hxU t]
      exact ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
    apply Submodule.mem_span_singleton.mpr
    exact ⟨c, (e.map_smul c mₓ).symm.trans (congrArg e hc)⟩
  · intro hz
    change (z : L) ∈ Submodule.span (X.presheaf.stalk x) {e mₓ} at hz
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
    have ha : c • mₓ ∈ LinearMap.range (schemeModuleStalkMap I.ι x) := by
      rw [schemeLineStalk_range E I x U hxU t]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self mₓ)
    obtain ⟨a, ha⟩ := ha
    refine ⟨schemeModuleStalkMap iₛ x a, ⟨a, rfl⟩, Subtype.ext ?_⟩
    change e (schemeModuleStalkMap (Nₛ).ι x (schemeModuleStalkMap iₛ x a)) = z.val
    rw [stalk_inclusion_comp, ha, map_smul]
    exact hc

/-- The stalk of the actual sheaf normalizer cokernel is equivalent to
the algebraic normalizer quotient. The line image and all intermediate
quotient comparisons are constructed from the genuine local frame. -/
def schemeNormalizerQuotientStalkEquiv :
    (Scheme.Modules.presheaf (normalizerQuotientSheaf E I action action_res habelian)).stalk x
      ≃ₗ[X.presheaf.stalk x]
        (frameLine (R := X.presheaf.stalk x) (e mₓ)).normalizer ⧸ frameIdeal (e mₓ) := by
  let : Mono iₛ := normalizerLineInclusion_mono E I action action_res habelian
  exact (schemeCokernelStalkEquiv iₛ x).symm.trans
    (Submodule.Quotient.equiv _ _ nₓ
      (schemeNormalizerStalkEquiv_line E I action action_res action_smul_right
        habelian x e he U hxU t))

/-- On actual projected stalk representatives, the quotient comparison
is the quotient of the constructed normalizer comparison. -/
theorem schemeNormalizerQuotientStalkEquiv_projection
    (a : (Scheme.Modules.presheaf (Nₛ).toSheafOfModules).stalk x) :
    schemeNormalizerQuotientStalkEquiv E I action action_res action_smul_right
        habelian x e he U hxU t (schemeModuleStalkMap (cokernel.π iₛ) x a) =
      (frameIdeal (e mₓ)).toSubmodule.mkQ (nₓ a) := by
  let : Mono iₛ := normalizerLineInclusion_mono E I action action_res habelian
  have h := (schemeCokernelStalkEquiv iₛ x).symm_apply_apply
    (Submodule.Quotient.mk a)
  rw [schemeCokernelStalkEquiv_mk] at h
  exact congrArg
    (Submodule.Quotient.equiv _ _ nₓ
      (schemeNormalizerStalkEquiv_line E I action action_res action_smul_right
        habelian x e he U hxU t)) h

end Normalizer
