import Normalizer.SheafStalkCokernel
import Normalizer.TrivializedCharacter
import Normalizer.FrameCharacter

/-! Actual normalizer stalks, tested using a genuine local frame.
No saturation, degree, or local freeness of the ambient sheaf is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u
variable {X : Scheme.{u}} (E : X.Modules) (I : E.Submodule)

/-- An actual subsheaf inclusion is injective on actual stalks. -/
theorem schemeSubmoduleStalk_injective (x : X) :
    Function.Injective (schemeModuleStalkMap I.ι x) := by
  exact TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
    (f := Scheme.Modules.Hom.mapPresheaf I.ι) (fun _ => Subtype.val_injective) x

/-- Stalk membership in an actual subsheaf means having a local
representative in that subsheaf. -/
theorem schemeSubmoduleStalk_mem_range (x : X) (b : E.presheaf.stalk x) :
    b ∈ LinearMap.range (schemeModuleStalkMap I.ι x) ↔
      ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(E, U)),
        s ∈ I.obj (op U) ∧ E.presheaf.germ U x hx s = b := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨U, hx, s, rfl⟩ := (Scheme.Modules.presheaf I.toSheafOfModules).exists_germ_eq a
    refine ⟨U, hx, s.val, s.property, ?_⟩
    exact (schemeModuleStalkMap_germ I.ι x U hx s).symm
  · rintro ⟨U, hx, s, hs, rfl⟩
    refine ⟨(Scheme.Modules.presheaf I.toSheafOfModules).germ U x hx ⟨s, hs⟩, ?_⟩
    exact schemeModuleStalkMap_germ I.ι x U hx ⟨s, hs⟩

/-- A genuine restricted-sheaf line trivialization supplies one frame
that generates the line on every smaller open. -/
theorem lineTrivializationAt_span {U : X.Opens}
    (t : (SheafOfModules.unit X.ringCatSheaf).over U ≅ I.toSheafOfModules.over U)
    {V : X.Opens} (h : V ≤ U) :
    I.obj (op V) = Submodule.span (X.presheaf.obj (op V))
      {E.presheaf.map (homOfLE h).op
        (lineTrivializationAt E I t U le_rfl 1 : E.val.obj (op U))} := by
  have ht := congrArg Subtype.val (lineTrivializationAt_restrict E I t V U h le_rfl 1)
  have hf : E.presheaf.map (homOfLE h).op
      (lineTrivializationAt E I t U le_rfl 1 : E.val.obj (op U)) =
      (lineTrivializationAt E I t V h 1 : E.val.obj (op V)) := by
    simp only [map_one] at ht
    exact ht
  rw [hf]
  ext s
  constructor
  · intro hs
    apply Submodule.mem_span_singleton.mpr
    let a := (lineTrivializationAt E I t V h).symm ⟨s, hs⟩
    refine ⟨a, ?_⟩
    have ha := (lineTrivializationAt E I t V h).map_smul a
      (1 : X.presheaf.obj (op V))
    have he : lineTrivializationAt E I t V h a = ⟨s, hs⟩ :=
      (lineTrivializationAt E I t V h).apply_symm_apply ⟨s, hs⟩
    exact (congrArg Subtype.val (by simpa only [smul_eq_mul, mul_one] using ha)).symm.trans
      (congrArg Subtype.val he)
  · rintro hs
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs
    exact (I.obj (op V)).smul_mem a (lineTrivializationAt E I t V h 1).property

variable
  (action : ∀ V, E.val.obj V → E.val.obj V →ₗ[X.ringCatSheaf.obj.obj V] E.val.obj V)
  (action_res : ∀ {V W} (f : V ⟶ W) (m s : E.val.obj V),
    E.val.map f (action V m s) = action W (E.val.map f m) (E.val.map f s))
  (action_smul_right : ∀ V (a : X.ringCatSheaf.obj.obj V) (m s : E.val.obj V),
    action V (a • m) s = a • action V m s)

include action_smul_right in
/-- Given an ambient stalk identification preserving the actual bracket
on germs, the actual normalizer stalk is exactly the line normalizer.
The frame is required to generate on every smaller open. -/
theorem schemeNormalizerStalk_mem_iff
    (x : X) {L : Type u} [LieRing L] [LieAlgebra (X.presheaf.stalk x) L]
    (e : E.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] L)
    (he : ∀ (V : X.Opens) (hxV : x ∈ V) (m s : Γ(E, V)),
      e (E.presheaf.germ V x hxV (action (op V) m s)) =
        ⁅e (E.presheaf.germ V x hxV s), e (E.presheaf.germ V x hxV m)⁆)
    (U : X.Opens) (hxU : x ∈ U) (m : Γ(E, U))
    (hframe : ∀ (V : X.Opens) (h : V ≤ U), I.obj (op V) =
      Submodule.span (X.presheaf.obj (op V)) {E.presheaf.map (homOfLE h).op m})
    (b : E.presheaf.stalk x) :
    b ∈ LinearMap.range (schemeModuleStalkMap
      (normalizerSubsheaf E I action action_res).ι x) ↔
      e b ∈ (frameLine (R := X.presheaf.stalk x) (e (E.presheaf.germ U x hxU m))).normalizer := by
  let N := normalizerSubsheaf E I action action_res
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨V, hVU, hxV, s, rfl⟩ :=
      (Scheme.Modules.presheaf N.toSheafOfModules).exists_le_germ_eq a hxU
    rw [schemeModuleStalkMap_germ]
    apply (mem_frameNormalizer _ _).mpr
    let j : V ⟶ U := homOfLE hVU
    have hm : E.presheaf.map j.op m ∈ I.obj (op V) := by
      rw [hframe V hVU]
      exact Submodule.subset_span (Set.mem_singleton _)
    have hs := normalizerSubsheaf_action E I action action_res (op V) s.val
      (E.presheaf.map j.op m) s.property hm
    rw [hframe V hVU, Submodule.mem_span_singleton] at hs
    obtain ⟨c, hc⟩ := hs
    refine ⟨X.presheaf.germ V x hxV c, ?_⟩
    have hg := E.presheaf.germ_res_apply j x hxV m
    have heq := congrArg (fun z : Γ(E, V) => e (E.presheaf.germ V x hxV z)) hc
    rw [he, schemeModule_germ_smul, map_smul, hg] at heq
    exact heq.symm
  · intro hb
    obtain ⟨a, ha⟩ := (mem_frameNormalizer _ _).mp hb
    obtain ⟨V, hVU, hxV, s, hs⟩ := E.presheaf.exists_le_germ_eq b hxU
    obtain ⟨W, hWV, hxW, c, hc⟩ := X.presheaf.exists_le_germ_eq a hxV
    let j : W ⟶ V := homOfLE hWV
    let k : W ⟶ U := homOfLE (hWV.trans hVU)
    let sW := E.presheaf.map j.op s
    let mW := E.presheaf.map k.op m
    have hsg : E.presheaf.germ W x hxW sW = b :=
      (E.presheaf.germ_res_apply j x hxW s).trans hs
    have hmg : E.presheaf.germ W x hxW mW = E.presheaf.germ U x hxU m :=
      E.presheaf.germ_res_apply k x hxW m
    have hz : E.presheaf.germ W x hxW (action (op W) mW sW) =
        E.presheaf.germ W x hxW (c • mW) := by
      apply e.injective
      rw [he, schemeModule_germ_smul, map_smul, hsg, hmg, hc]
      exact ha
    obtain ⟨T, hxT, l, l', hl⟩ := E.presheaf.germ_eq x hxW hxW
      (action (op W) mW sW) (c • mW) hz
    have hll : l' = l := Subsingleton.elim _ _
    subst l'
    let sT := E.presheaf.map l.op sW
    let mT := E.presheaf.map l.op mW
    have hmT : mT ∈ I.obj (op T) := by
      have hmW : mW ∈ I.obj (op W) := by
        rw [hframe W (hWV.trans hVU)]
        exact Submodule.subset_span (Set.mem_singleton _)
      exact I.map_mem l.op hmW
    have hsT : sT ∈ N.obj (op T) := by
      apply (normalizerSubsheaf_frame_criterion E I action action_res
        action_smul_right (op T) mT sT ?_).mpr
      · have hact : action (op T) mT sT =
            X.presheaf.map l.op c • mT := by
          have hres := action_res l.op mW sW
          have hsmul := E.val.map_smul l.op c mW
          exact hres.symm.trans (hl.trans hsmul)
        rw [hact]
        exact (I.obj (op T)).smul_mem _ hmT
      · intro Z f
        have hZ : Z.unop ≤ U := f.unop.le.trans (l.le.trans (hWV.trans hVU))
        rw [hframe Z.unop hZ]
        congr 2
        change E.presheaf.map (homOfLE hZ).op m =
          E.presheaf.map f (E.presheaf.map l.op (E.presheaf.map k.op m))
        simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
          congrArg (fun q : op U ⟶ Z => E.presheaf.map q m)
            (Subsingleton.elim (homOfLE hZ).op (k.op ≫ l.op ≫ f))
    apply (schemeSubmoduleStalk_mem_range E N x b).mpr
    refine ⟨T, hxT, sT, hsT, ?_⟩
    exact (E.presheaf.germ_res_apply l x hxT sW).trans hsg

section Trivialized
variable
    (x : X) {L : Type u} [LieRing L] [LieAlgebra (X.presheaf.stalk x) L]
    (e : E.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] L)
    (he : ∀ (V : X.Opens) (hxV : x ∈ V) (m s : Γ(E, V)),
      e (E.presheaf.germ V x hxV (action (op V) m s)) =
        ⁅e (E.presheaf.germ V x hxV s), e (E.presheaf.germ V x hxV m)⁆)
    (U : X.Opens) (hxU : x ∈ U)
    (t : (SheafOfModules.unit X.ringCatSheaf).over U ≅ I.toSheafOfModules.over U)

local notation "mₜ" => (lineTrivializationAt E I t U le_rfl 1 : E.val.obj (op U))
local notation "Nₛ" => normalizerSubsheaf E I action action_res
local notation "Nₘ" => LieSubalgebra.normalizer (frameLine (R := X.presheaf.stalk x)
  (e (E.presheaf.germ U x hxU mₜ)))

include action_smul_right he in
/-- With a genuine local sheaf trivialization, stalk normalizer
membership follows without a supplied frame-generation hypothesis. -/
theorem schemeNormalizerStalk_mem_iff_trivialization (b : E.presheaf.stalk x) :
    b ∈ LinearMap.range (schemeModuleStalkMap (Nₛ).ι x) ↔ e b ∈ Nₘ :=
  schemeNormalizerStalk_mem_iff E I action action_res action_smul_right x e he U hxU mₜ
    (fun _ h => lineTrivializationAt_span E I t h) b

/-- The actual normalizer stalk is linearly equivalent to the normalizer
in the supplied ambient Lie algebra. Surjectivity is proved by shrinking
representatives, not assumed. -/
def schemeNormalizerStalkEquiv :
    (Scheme.Modules.presheaf (Nₛ).toSheafOfModules).stalk x ≃ₗ[X.presheaf.stalk x] Nₘ := by
  let n := e.toLinearMap.comp (schemeModuleStalkMap (Nₛ).ι x)
  let q : (Scheme.Modules.presheaf (Nₛ).toSheafOfModules).stalk x →ₗ[X.presheaf.stalk x] Nₘ :=
    n.codRestrict (Nₘ).toSubmodule (fun a =>
      (schemeNormalizerStalk_mem_iff_trivialization E I action action_res action_smul_right
        x e he U hxU t _).mp ⟨a, rfl⟩)
  apply LinearEquiv.ofBijective q
  constructor
  · intro a b hab
    apply schemeSubmoduleStalk_injective E Nₛ x
    apply e.injective
    exact congrArg Subtype.val hab
  · intro b
    have hb : e.symm b ∈ LinearMap.range (schemeModuleStalkMap (Nₛ).ι x) := by
      apply (schemeNormalizerStalk_mem_iff_trivialization E I action action_res action_smul_right
        x e he U hxU t _).mpr
      simpa only [e.apply_symm_apply] using b.property
    obtain ⟨a, ha⟩ := hb
    refine ⟨a, Subtype.ext ?_⟩
    change e (schemeModuleStalkMap (Nₛ).ι x a) = b.val
    rw [ha, e.apply_symm_apply]

/-- The constructed comparison is the supplied ambient map applied to
the actual inclusion on stalks. -/
theorem schemeNormalizerStalkEquiv_apply
    (a : (Scheme.Modules.presheaf (Nₛ).toSheafOfModules).stalk x) :
    (schemeNormalizerStalkEquiv E I action action_res action_smul_right x e he U hxU t a : L) =
      e (schemeModuleStalkMap (Nₛ).ι x a) := rfl

end Trivialized

end Normalizer
