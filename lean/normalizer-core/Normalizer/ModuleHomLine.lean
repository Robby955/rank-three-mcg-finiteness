import Normalizer.ModuleSheafHom

/-! Internal Hom on an open where its source is a genuinely trivialized
line sheaf. Evaluation at the frame gives an equivalence for any target
module sheaf; the target need not be locally free. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Opposite TopologicalSpace

universe u
variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  (M G : SheafOfModules.{u} R)
  (ring_comm : ∀ V (a b : R.obj.obj V), a * b = b * a)

/-- The sectionwise frame obtained by evaluating a restricted-sheaf isomorphism. -/
def moduleLineFrameAt {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ M.over U)
    (V : Opens X) (h : V ≤ U) :
    R.obj.obj (op V) ≃ₗ[R.obj.obj (op V)] M.val.obj (op V) :=
  ((SheafOfModules.evaluation (R.over U) (op (Over.mk (homOfLE h)))).mapIso e).toLinearEquiv

/-- The frame commutes with restrictions because it comes from a sheaf morphism. -/
theorem moduleLineFrameAt_restrict {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ M.over U)
    (V W : Opens X) (h : V ≤ W) (k : W ≤ U) (r : R.obj.obj (op W)) :
    M.val.map (homOfLE h).op (moduleLineFrameAt M e W k r) =
      moduleLineFrameAt M e V (h.trans k) (R.obj.map (homOfLE h).op r) := by
  let f : Over.mk (homOfLE (h.trans k)) ⟶ Over.mk (homOfLE k) :=
    Over.homMk (homOfLE h)
  exact (PresheafOfModules.naturality_apply e.hom.val f.op r).symm

/-- Coordinates in the frame also commute with restriction. -/
theorem moduleLineFrameAt_symm_restrict {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ M.over U)
    (V W : Opens X) (h : V ≤ W) (k : W ≤ U) (m : M.val.obj (op W)) :
    R.obj.map (homOfLE h).op ((moduleLineFrameAt M e W k).symm m) =
      (moduleLineFrameAt M e V (h.trans k)).symm (M.val.map (homOfLE h).op m) := by
  apply (moduleLineFrameAt M e V (h.trans k)).injective
  rw [← moduleLineFrameAt_restrict M e V W h k, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

private def frameHomLocal {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ M.over U)
    (V W : Opens X) (h : V ≤ U) (k : W ≤ V) (g : G.val.obj (op V)) :
    M.val.obj (op W) →ₗ[R.obj.obj (op W)] G.val.obj (op W) where
  toFun m := (moduleLineFrameAt M e W (k.trans h)).symm m • G.val.map (homOfLE k).op g
  map_add' := by intro m n; simp only [map_add, add_smul]
  map_smul' := by intro r m; simp only [map_smul, RingHom.id_apply, smul_eq_mul, mul_smul]

private def frameHomSection {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ M.over U)
    (V : Opens X) (h : V ≤ U) (g : G.val.obj (op V)) :
    (moduleHomSheaf M G ring_comm).val.obj (op V) :=
  moduleHomMk M G ring_comm V (fun W k => frameHomLocal M G e V W h k g) (by
    intro W Z k l m
    change G.val.map (homOfLE l).op
      ((moduleLineFrameAt M e W (k.trans h)).symm m • G.val.map (homOfLE k).op g) = _
    rw [G.val.map_smul, moduleLineFrameAt_symm_restrict, ← G.val.map_comp_apply]
    rfl)

private theorem frameHomSection_eval {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ M.over U)
    (V W : Opens X) (h : V ≤ U) (k : W ≤ V) (g : G.val.obj (op V))
    (m : M.val.obj (op W)) :
    moduleHomEval M G ring_comm V W k (frameHomSection M G ring_comm e V h g) m =
      (moduleLineFrameAt M e W (k.trans h)).symm m • G.val.map (homOfLE k).op g := rfl

/-- An internal-Hom section over a trivializing open is determined by the
image of the frame. This uses naturality on all smaller opens. -/
theorem moduleHom_eval_frame {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ M.over U)
    (V W : Opens X) (h : V ≤ U) (k : W ≤ V)
    (f : (moduleHomSheaf M G ring_comm).val.obj (op V)) (m : M.val.obj (op W)) :
    moduleHomEval M G ring_comm V W k f m =
      (moduleLineFrameAt M e W (k.trans h)).symm m •
        G.val.map (homOfLE k).op
          (moduleHomEval M G ring_comm V V le_rfl f (moduleLineFrameAt M e V h 1)) := by
  have hm : m = (moduleLineFrameAt M e W (k.trans h)).symm m •
      moduleLineFrameAt M e W (k.trans h) 1 := by
    rw [← map_smul]
    simp
  conv_lhs => rw [hm]
  rw [map_smul]
  congr 1
  have hn := moduleHomEval_natural M G ring_comm V V W le_rfl k f
    (moduleLineFrameAt M e V h 1)
  rw [moduleLineFrameAt_restrict M e W V k h] at hn
  simpa only [map_one] using hn.symm

/-- Evaluation at a genuine line frame identifies local internal Hom with
the target section module. No local freeness of the target is assumed. -/
def moduleHomFrameEquiv {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ M.over U)
    (V : Opens X) (h : V ≤ U) :
    (moduleHomSheaf M G ring_comm).val.obj (op V) ≃ₗ[R.obj.obj (op V)]
      G.val.obj (op V) where
  toFun f := moduleHomEval M G ring_comm V V le_rfl f (moduleLineFrameAt M e V h 1)
  invFun := frameHomSection M G ring_comm e V h
  left_inv f := by
    apply moduleHom_ext M G ring_comm V
    intro W k m
    rw [frameHomSection_eval, moduleHom_eval_frame M G ring_comm e V W h k f m]
  right_inv g := by
    dsimp only
    rw [frameHomSection_eval, LinearEquiv.symm_apply_apply, one_smul]
    change G.val.map (𝟙 (op V)) g = g
    simp
  map_add' := by intro f g; rfl
  map_smul' := by
    intro r f
    rw [moduleHomEval_smul]
    change R.obj.map (𝟙 (op V)) r • _ = r • _
    simp

/-- The equivalence is the actual evaluation map at the frame. -/
theorem moduleHomFrameEquiv_apply {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ M.over U)
    (V : Opens X) (h : V ≤ U)
    (f : (moduleHomSheaf M G ring_comm).val.obj (op V)) :
    moduleHomFrameEquiv M G ring_comm e V h f =
      moduleHomEval M G ring_comm V V le_rfl f (moduleLineFrameAt M e V h 1) := rfl

end Normalizer
