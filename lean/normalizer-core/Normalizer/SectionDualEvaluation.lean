import Normalizer.ModuleHomLine
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! The actual dual module sheaf and evaluation at a prescribed global section. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u
variable {X : Scheme.{u}} (L : X.Modules)

local instance sectionDualEvaluationCommRing (V : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.obj.obj V) :=
  inferInstanceAs (CommRing (X.presheaf.obj V))

private theorem schemeDualRingComm (V : X.Opensᵒᵖ)
    (a b : X.ringCatSheaf.obj.obj V) : a * b = b * a :=
  @mul_comm (X.presheaf.obj V) _ a b

/-- The actual sheaf of local module morphisms into the structure sheaf. -/
def schemeDualSheaf : X.Modules :=
  moduleHomSheaf L (SheafOfModules.unit X.ringCatSheaf) schemeDualRingComm

/-- Evaluation of a local dual section at the restriction of the prescribed
global section, linear over the actual section ring. -/
def schemeSectionDualEvaluationAt (s : Γ(L, ⊤)) (V : X.Opens) :
    Γ(schemeDualSheaf L, V) →ₗ[Γ(X, V)] Γ(X, V) where
  toFun φ := moduleHomEval L (SheafOfModules.unit X.ringCatSheaf) schemeDualRingComm
    V V le_rfl φ (L.presheaf.map (homOfLE le_top).op s)
  map_add' φ ψ := rfl
  map_smul' a φ := by
    rw [moduleHomEval_smul]
    change X.presheaf.map (𝟙 (op V)) a * _ = a * _
    simp

/-- Evaluation at a specified global section is an actual morphism from the
constructed dual sheaf to the structure sheaf. -/
def schemeSectionDualEvaluation (s : Γ(L, ⊤)) :
    schemeDualSheaf L ⟶ SheafOfModules.unit X.ringCatSheaf where
  val := {
    app := fun V ↦ ModuleCat.ofHom (schemeSectionDualEvaluationAt L s V.unop)
    naturality := by
      intro V W f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      change schemeSectionDualEvaluationAt L s W.unop
        ((schemeDualSheaf L).val.map f φ) =
          X.presheaf.map f (schemeSectionDualEvaluationAt L s V.unop φ)
      have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
      rw [hf]
      dsimp only [schemeSectionDualEvaluationAt, schemeDualSheaf, LinearMap.coe_mk, AddHom.coe_mk]
      rw [moduleHom_restrict]
      have hn := moduleHomEval_natural L (SheafOfModules.unit X.ringCatSheaf)
        schemeDualRingComm V.unop V.unop W.unop le_rfl (leOfHom f.unop) φ
          (L.presheaf.map (homOfLE le_top).op s)
      change X.presheaf.map (homOfLE (leOfHom f.unop)).op _ = _ at hn
      rw [hn]
      congr 1
      exact (L.presheaf.map_comp_apply (homOfLE le_top).op
        (homOfLE (leOfHom f.unop)).op s) }

/-- The sheaf evaluation has its prescribed sectionwise value. -/
theorem schemeSectionDualEvaluation_app (s : Γ(L, ⊤)) (V : X.Opens)
    (φ : Γ(schemeDualSheaf L, V)) :
    (schemeSectionDualEvaluation L s).val.app (op V) φ =
      schemeSectionDualEvaluationAt L s V φ := rfl

/-- A genuine local line chart gives coordinates of actual dual sections,
by their evaluation on the actual line frame. -/
def schemeDualFrameCoordinate {U : X.Opens}
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (V : X.Opens) (h : V ≤ U) :
    Γ(schemeDualSheaf L, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  moduleHomFrameEquiv L (SheafOfModules.unit X.ringCatSheaf) schemeDualRingComm e V h

/-- The actual dual coordinates commute with restriction. -/
theorem schemeDualFrameCoordinate_restrict {U : X.Opens}
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (V W : X.Opens) (h : W ≤ V) (k : V ≤ U)
    (φ : Γ(schemeDualSheaf L, V)) :
    X.presheaf.map (homOfLE h).op (schemeDualFrameCoordinate L e V k φ) =
      schemeDualFrameCoordinate L e W (h.trans k)
        ((schemeDualSheaf L).val.map (homOfLE h).op φ) := by
  change X.presheaf.map (homOfLE h).op
    (moduleHomEval L (SheafOfModules.unit X.ringCatSheaf) schemeDualRingComm
      V V le_rfl φ (moduleLineFrameAt L e V k 1)) = _
  have hn := moduleHomEval_natural L (SheafOfModules.unit X.ringCatSheaf)
    schemeDualRingComm V V W le_rfl h φ (moduleLineFrameAt L e V k 1)
  rw [moduleLineFrameAt_restrict L e W V h k] at hn
  simp only [map_one] at hn
  change _ = moduleHomEval L (SheafOfModules.unit X.ringCatSheaf) schemeDualRingComm
    W W le_rfl ((moduleHomSheaf L _ schemeDualRingComm).val.map (homOfLE h).op φ)
      (moduleLineFrameAt L e W (h.trans k) 1)
  rw [moduleHom_restrict]
  exact hn

private def schemeDualCoordinatePresheafIso {U : X.Opens}
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U) :
    ((schemeDualSheaf L).over U).val ≅
      ((SheafOfModules.unit X.ringCatSheaf).over U).val := by
  refine PresheafOfModules.isoMk
    (fun V ↦ (schemeDualFrameCoordinate L e V.unop.left
      (leOfHom V.unop.hom)).toModuleIso) ?_
  intro V W f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  exact (schemeDualFrameCoordinate_restrict L e V.unop.left W.unop.left
    (leOfHom f.unop.left) (leOfHom V.unop.hom) φ).symm

/-- A genuine local line chart constructs a genuine chart of the actual dual sheaf. -/
def schemeDualLineFrameIso {U : X.Opens}
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U) :
    (SheafOfModules.unit X.ringCatSheaf).over U ≅ (schemeDualSheaf L).over U :=
  ((SheafOfModules.fullyFaithfulForget (X.ringCatSheaf.over U)).preimageIso
    (X := (schemeDualSheaf L).over U)
    (Y := (SheafOfModules.unit X.ringCatSheaf).over U)
    (schemeDualCoordinatePresheafIso L e)).symm

/-- Coordinates of the constructed dual frame are exactly the supplied scalar. -/
theorem schemeDualLineFrameIso_coordinate {U : X.Opens}
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (V : X.Opens) (h : V ≤ U) (r : Γ(X, V)) :
    schemeDualFrameCoordinate L e V h
      (moduleLineFrameAt (schemeDualSheaf L) (schemeDualLineFrameIso L e) V h r) = r :=
  (schemeDualFrameCoordinate L e V h).apply_symm_apply r

/-- In a genuine line chart, evaluation is multiplication by the prescribed
section's coordinate, with the dual coordinate derived from evaluation on the frame. -/
theorem schemeSectionDualEvaluation_frame (s : Γ(L, ⊤)) {U : X.Opens}
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (V : X.Opens) (h : V ≤ U) (φ : Γ(schemeDualSheaf L, V)) :
    schemeSectionDualEvaluationAt L s V φ =
      HMul.hMul (α := Γ(X, V)) (β := Γ(X, V)) (γ := Γ(X, V))
        ((moduleLineFrameAt L e V h).symm (L.presheaf.map (homOfLE le_top).op s))
        (schemeDualFrameCoordinate L e V h φ) := by
  change moduleHomEval L (SheafOfModules.unit X.ringCatSheaf) schemeDualRingComm
    V V le_rfl φ _ = _
  rw [moduleHom_eval_frame L (SheafOfModules.unit X.ringCatSheaf) schemeDualRingComm e
    V V h le_rfl]
  change _ * X.presheaf.map (𝟙 (op V)) _ = _
  rw [X.presheaf.map_id]
  rfl

/-- The image of the constructed dual frame is the actual local equation
of the specified global section in the original chart. -/
theorem schemeSectionDualEvaluation_frame_one (s : Γ(L, ⊤)) {U : X.Opens}
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (V : X.Opens) (h : V ≤ U) :
    (schemeSectionDualEvaluation L s).val.app (op V)
      (moduleLineFrameAt (schemeDualSheaf L) (schemeDualLineFrameIso L e) V h 1) =
        e.inv.val.app (op (Over.mk (homOfLE h)))
          (L.presheaf.map (homOfLE le_top).op s) := by
  rw [schemeSectionDualEvaluation_app, schemeSectionDualEvaluation_frame,
    schemeDualLineFrameIso_coordinate, mul_one]
  rfl

end Normalizer
