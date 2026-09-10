import Normalizer.NormalizerStalk

/-! A genuine line-sheaf frame supplies a faithful frame of its actual
stalk image. The proofs use local representatives and equalities of germs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u
variable {X : Scheme.{u}} (E : X.Modules) (I : E.Submodule)
  (x : X) (U : X.Opens) (hxU : x ∈ U)
  (t : (SheafOfModules.unit X.ringCatSheaf).over U ≅ I.toSheafOfModules.over U)

/-- The germ in the actual ambient stalk of the genuine local line frame. -/
def schemeLineFrameGerm : E.presheaf.stalk x :=
  E.presheaf.germ U x hxU (lineTrivializationAt E I t U le_rfl 1 : E.val.obj (op U))

private theorem lineFrame_restrict {V : X.Opens} (h : V ≤ U) :
    E.presheaf.map (homOfLE h).op
      (lineTrivializationAt E I t U le_rfl 1 : E.val.obj (op U)) =
      (lineTrivializationAt E I t V h 1 : E.val.obj (op V)) := by
  have ht := congrArg Subtype.val (lineTrivializationAt_restrict E I t V U h le_rfl 1)
  simp only [map_one] at ht
  exact ht

private theorem lineFrame_scalar_injective {V : X.Opens} (h : V ≤ U) :
    Function.Injective (fun a : X.presheaf.obj (op V) =>
      a • (lineTrivializationAt E I t V h 1 : E.val.obj (op V))) := by
  have hf (a : X.presheaf.obj (op V)) :
      (lineTrivializationAt E I t V h a : E.val.obj (op V)) =
        a • (lineTrivializationAt E I t V h 1 : E.val.obj (op V)) := by
    have ha := (lineTrivializationAt E I t V h).map_smul a
      (1 : X.presheaf.obj (op V))
    have he : lineTrivializationAt E I t V h a =
        a • lineTrivializationAt E I t V h 1 := by
      simpa only [smul_eq_mul, mul_one] using ha
    exact congrArg Subtype.val he
  intro a b hab
  apply (lineTrivializationAt E I t V h).injective
  apply Subtype.ext
  exact (hf a).trans (hab.trans (hf b).symm)

/-- The range of the actual line inclusion on stalks is precisely the
span of the germ of its genuine local frame. -/
theorem schemeLineStalk_range :
    LinearMap.range (schemeModuleStalkMap I.ι x) =
      Submodule.span (X.presheaf.stalk x) {schemeLineFrameGerm E I x U hxU t} := by
  apply le_antisymm
  · rintro b ⟨a, rfl⟩
    obtain ⟨V, hVU, hxV, s, rfl⟩ :=
      (Scheme.Modules.presheaf I.toSheafOfModules).exists_le_germ_eq a hxU
    rw [schemeModuleStalkMap_germ]
    let sE : Γ(E, V) := s.val
    have hs : sE ∈ I.obj (op V) := s.property
    rw [lineTrivializationAt_span E I t hVU, Submodule.mem_span_singleton] at hs
    obtain ⟨c, hc⟩ := hs
    apply Submodule.mem_span_singleton.mpr
    refine ⟨X.presheaf.germ V x hxV c, ?_⟩
    change X.presheaf.germ V x hxV c • E.presheaf.germ U x hxU _ =
      E.presheaf.germ V x hxV sE
    rw [← E.presheaf.germ_res_apply (homOfLE hVU) x hxV,
      ← schemeModule_germ_smul, hc]
  · apply Submodule.span_le.mpr
    intro b hb
    obtain rfl := Set.mem_singleton_iff.mp hb
    refine ⟨(Scheme.Modules.presheaf I.toSheafOfModules).germ U x hxU
      (lineTrivializationAt E I t U le_rfl 1), ?_⟩
    exact schemeModuleStalkMap_germ I.ι x U hxU _

private theorem lineFrameGerm_smul_eq_zero (a : X.presheaf.stalk x)
    (ha : a • schemeLineFrameGerm E I x U hxU t = 0) : a = 0 := by
  obtain ⟨V, hVU, hxV, c, rfl⟩ := X.presheaf.exists_le_germ_eq a hxU
  let m := (lineTrivializationAt E I t U le_rfl 1 : E.val.obj (op U))
  let mV := E.presheaf.map (homOfLE hVU).op m
  have hmg : E.presheaf.germ V x hxV mV = E.presheaf.germ U x hxU m :=
    E.presheaf.germ_res_apply (homOfLE hVU) x hxV m
  change X.presheaf.germ V x hxV c • E.presheaf.germ U x hxU m = 0 at ha
  rw [← hmg, ← schemeModule_germ_smul] at ha
  have hz : E.presheaf.germ V x hxV (c • mV) = E.presheaf.germ V x hxV 0 := by
    simpa only [map_zero] using ha
  obtain ⟨T, hxT, l, l', hl⟩ := E.presheaf.germ_eq x hxV hxV (c • mV) 0 hz
  have hll : l' = l := Subsingleton.elim _ _
  subst l'
  have hres : X.presheaf.map l.op c • E.presheaf.map l.op mV = 0 := by
    exact (E.val.map_smul l.op c mV).symm.trans (hl.trans (map_zero _))
  have hf : E.presheaf.map l.op mV =
      (lineTrivializationAt E I t T (l.le.trans hVU) 1 : E.val.obj (op T)) := by
    have he : E.presheaf.map l.op mV =
        E.presheaf.map (homOfLE (l.le.trans hVU)).op m := by
      change E.presheaf.map l.op (E.presheaf.map (homOfLE hVU).op m) = _
      simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
        congrArg (fun q : op U ⟶ op T => E.presheaf.map q m)
          (Subsingleton.elim ((homOfLE hVU).op ≫ l.op)
            (homOfLE (l.le.trans hVU)).op)
    exact he.trans (lineFrame_restrict E I U t (l.le.trans hVU))
  have hc : X.presheaf.map l.op c = 0 := by
    apply lineFrame_scalar_injective E I U t (l.le.trans hVU)
    change X.presheaf.map l.op c •
      (lineTrivializationAt E I t T (l.le.trans hVU) 1 : E.val.obj (op T)) =
      (0 : X.presheaf.obj (op T)) • _
    rw [zero_smul]
    exact (congrArg (fun z : Γ(E, T) => X.presheaf.map l.op c • z) hf).symm.trans hres
  rw [← X.presheaf.germ_res_apply l x hxT c, hc, map_zero]

/-- Multiplication by the actual frame germ is injective. This follows
from the sheaf trivialization after shrinking an equality of germs. -/
theorem schemeLineFrameGerm_smul_injective :
    Function.Injective (fun a : X.presheaf.stalk x =>
      a • schemeLineFrameGerm E I x U hxU t) := by
  intro a b hab
  change a • schemeLineFrameGerm E I x U hxU t =
    b • schemeLineFrameGerm E I x U hxU t at hab
  apply sub_eq_zero.mp
  apply lineFrameGerm_smul_eq_zero E I x U hxU t
  rw [sub_smul, hab, sub_self]

/-- A genuine line frame has nonzero image in the actual ambient stalk. -/
theorem schemeLineFrameGerm_ne_zero : schemeLineFrameGerm E I x U hxU t ≠ 0 := by
  intro h
  have h10 : (1 : X.presheaf.stalk x) = 0 :=
    schemeLineFrameGerm_smul_injective E I x U hxU t (by rw [h]; simp)
  exact one_ne_zero h10

end Normalizer
