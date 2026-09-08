import Normalizer.ModuleHomLine
import Normalizer.ModuleSheafTensor
import Normalizer.LineTensor
import Normalizer.SheafifyLocalIso

/-! The canonical tensor evaluation into internal Hom. The map is defined
without a frame. Rank-one local trivializations are used to prove its
local bijectivity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Opposite TopologicalSpace TensorProduct

universe u
variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  (M G : SheafOfModules.{u} R)
  (ring_comm : ∀ V (a b : R.obj.obj V), a * b = b * a)

private def pureHomLocal (V W : Opens X) (h : W ≤ V)
    (g : G.val.obj (op V))
    (φ : (moduleHomSheaf M (SheafOfModules.unit R) ring_comm).val.obj (op V)) :
    M.val.obj (op W) →ₗ[R.obj.obj (op W)] G.val.obj (op W) where
  toFun m := (moduleHomEval M (SheafOfModules.unit R) ring_comm V W h φ m : R.obj.obj (op W)) •
    G.val.restrictₛₗ (homOfLE h).op g
  map_add' := by intro m n; simp only [map_add, add_smul]
  map_smul' := by
    intro r m
    simp only [map_smul, RingHom.id_apply, smul_eq_mul]
    exact mul_smul r
      (moduleHomEval M (SheafOfModules.unit R) ring_comm V W h φ m : R.obj.obj (op W))
      (G.val.restrictₛₗ (homOfLE h).op g : G.val.obj (op W))

private def pureHomSection (V : Opens X) (g : G.val.obj (op V))
    (φ : (moduleHomSheaf M (SheafOfModules.unit R) ring_comm).val.obj (op V)) :
    (moduleHomSheaf M G ring_comm).val.obj (op V) :=
  moduleHomMk M G ring_comm V (fun W h => pureHomLocal M G ring_comm V W h g φ) (by
    intro W Z h k m
    change G.val.restrictₛₗ (homOfLE k).op
      ((moduleHomEval M (SheafOfModules.unit R) ring_comm V W h φ m : R.obj.obj (op W)) •
        G.val.restrictₛₗ (homOfLE h).op g) = _
    simp only [PresheafOfModules.restrictₛₗ_apply]
    rw [G.val.map_smul, ← G.val.map_comp_apply]
    have hn := moduleHomEval_natural M (SheafOfModules.unit R) ring_comm V W Z h k φ m
    change R.obj.map (homOfLE k).op _ = _ at hn
    rw [hn]
    rfl)

private theorem pureHomSection_eval (V W : Opens X) (h : W ≤ V)
    (g : G.val.obj (op V))
    (φ : (moduleHomSheaf M (SheafOfModules.unit R) ring_comm).val.obj (op V))
    (m : M.val.obj (op W)) :
    moduleHomEval M G ring_comm V W h (pureHomSection M G ring_comm V g φ) m =
      (moduleHomEval M (SheafOfModules.unit R) ring_comm V W h φ m : R.obj.obj (op W)) •
        G.val.restrictₛₗ (homOfLE h).op g := rfl

private def tensorEvalBilinear (V : Opens X) :
    letI := moduleSectionCommRing ring_comm (op V)
    G.val.obj (op V) →ₗ[R.obj.obj (op V)]
      (moduleHomSheaf M (SheafOfModules.unit R) ring_comm).val.obj (op V) →ₗ[R.obj.obj (op V)]
        (moduleHomSheaf M G ring_comm).val.obj (op V) := by
  letI := moduleSectionCommRing ring_comm (op V)
  exact {
  toFun g := {
    toFun := pureHomSection M G ring_comm V g
    map_add' := by
      intro φ ψ
      apply moduleHom_ext M G ring_comm V
      intro W h m
      simp only [pureHomSection_eval, moduleHomEval_add, LinearMap.add_apply, add_smul]
    map_smul' := by
      intro r φ
      apply moduleHom_ext M G ring_comm V
      intro W h m
      simp only [pureHomSection_eval, moduleHomEval_smul, RingHom.id_apply, smul_eq_mul]
      exact mul_smul (R.obj.map (homOfLE h).op r)
        (moduleHomEval M (SheafOfModules.unit R) ring_comm V W h φ m : R.obj.obj (op W))
        (G.val.restrictₛₗ (homOfLE h).op g : G.val.obj (op W)) }
  map_add' := by
    intro g k
    ext φ
    apply moduleHom_ext M G ring_comm V
    intro W h m
    change moduleHomEval M G ring_comm V W h (pureHomSection M G ring_comm V (g + k) φ) m =
      moduleHomEval M G ring_comm V W h (pureHomSection M G ring_comm V g φ) m +
        moduleHomEval M G ring_comm V W h (pureHomSection M G ring_comm V k φ) m
    simp only [pureHomSection_eval, map_add]
    exact @smul_add (R.obj.obj (op W)) (G.val.obj (op W)) _ _
      (moduleHomEval M (SheafOfModules.unit R) ring_comm V W h φ m : R.obj.obj (op W))
      (G.val.restrictₛₗ (homOfLE h).op g : G.val.obj (op W))
      (G.val.restrictₛₗ (homOfLE h).op k : G.val.obj (op W))
  map_smul' := by
    intro r g
    ext φ
    apply moduleHom_ext M G ring_comm V
    intro W h m
    change moduleHomEval M G ring_comm V W h (pureHomSection M G ring_comm V (r • g) φ) m =
      moduleHomEval M G ring_comm V W h (r • pureHomSection M G ring_comm V g φ) m
    simp only [pureHomSection_eval, moduleHomEval_smul, map_smulₛₗ, smul_smul]
    rw [ring_comm] }

/-- Canonical tensor evaluation on the presheaf section module. -/
def lineSheafTensorEvalAt (V : Opens X) :
    (moduleTensorPresheaf G (moduleHomSheaf M (SheafOfModules.unit R) ring_comm)
      ring_comm).obj (op V) →ₗ[R.obj.obj (op V)]
        (moduleHomSheaf M G ring_comm).val.obj (op V) := by
  letI := moduleSectionCommRing ring_comm (op V)
  exact TensorProduct.lift (tensorEvalBilinear M G ring_comm V)

/-- Evaluation has the intended value on every pure tensor and every smaller open. -/
theorem lineSheafTensorEvalAt_tmul (V W : Opens X) (h : W ≤ V)
    (g : G.val.obj (op V))
    (φ : (moduleHomSheaf M (SheafOfModules.unit R) ring_comm).val.obj (op V))
    (m : M.val.obj (op W)) :
    letI := moduleSectionCommRing ring_comm (op V)
    moduleHomEval M G ring_comm V W h
      (lineSheafTensorEvalAt M G ring_comm V (g ⊗ₜ[R.obj.obj (op V)] φ)) m =
        (moduleHomEval M (SheafOfModules.unit R) ring_comm V W h φ m : R.obj.obj (op W)) •
          G.val.restrictₛₗ (homOfLE h).op g := rfl

/-- Evaluation of a local morphism on the whole open, as a linear map. -/
def moduleHomSectionEval (V : Opens X) :
    letI := moduleSectionCommRing ring_comm (op V)
    (moduleHomSheaf M G ring_comm).val.obj (op V) →ₗ[R.obj.obj (op V)]
      (M.val.obj (op V) →ₗ[R.obj.obj (op V)] G.val.obj (op V)) := by
  letI := moduleSectionCommRing ring_comm (op V)
  exact {
  toFun := moduleHomEval M G ring_comm V V le_rfl
  map_add' := by intro f g; rfl
  map_smul' := by
    intro r f
    ext m
    rw [moduleHomEval_smul]
    change R.obj.map (𝟙 (op V)) r • moduleHomEval M G ring_comm V V le_rfl f m =
      r • moduleHomEval M G ring_comm V V le_rfl f m
    simp }

/-- For a genuinely trivialized source line, evaluation on the whole open
recovers all linear maps, with no extension assumption on the target. -/
def moduleHomSectionEquiv {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ M.over U)
    (V : Opens X) (h : V ≤ U) :
    letI := moduleSectionCommRing ring_comm (op V)
    (moduleHomSheaf M G ring_comm).val.obj (op V) ≃ₗ[R.obj.obj (op V)]
      (M.val.obj (op V) →ₗ[R.obj.obj (op V)] G.val.obj (op V)) := by
  letI := moduleSectionCommRing ring_comm (op V)
  exact LinearEquiv.ofBijective (moduleHomSectionEval M G ring_comm V) (by
    constructor
    · intro f g hfg
      apply (moduleHomFrameEquiv M G ring_comm e V h).injective
      exact congrArg (fun q => q (moduleLineFrameAt M e V h 1)) hfg
    · intro f
      refine ⟨(moduleHomFrameEquiv M G ring_comm e V h).symm
        (f (moduleLineFrameAt M e V h 1)), ?_⟩
      ext m
      change moduleHomEval M G ring_comm V V le_rfl _ m = f m
      rw [moduleHom_eval_frame M G ring_comm e V V h le_rfl]
      change (moduleLineFrameAt M e V h).symm m • G.val.restrictₛₗ (𝟙 (op V))
        ((moduleHomFrameEquiv M G ring_comm e V h)
          ((moduleHomFrameEquiv M G ring_comm e V h).symm _)) = _
      rw [LinearEquiv.apply_symm_apply]
      simp only [PresheafOfModules.restrictₛₗ_apply, PresheafOfModules.map_id]
      change (moduleLineFrameAt M e V h).symm m • f (moduleLineFrameAt M e V h 1) = f m
      rw [← map_smul]
      congr 1
      rw [← map_smul]
      simp)

/-- The canonical evaluation morphism is defined before choosing any frame. -/
def lineSheafTensorEvalPresheaf :
    moduleTensorPresheaf G (moduleHomSheaf M (SheafOfModules.unit R) ring_comm) ring_comm ⟶
      (moduleHomSheaf M G ring_comm).val where
  app V := ModuleCat.ofHom
    (R := R.obj.obj V)
    (X := (moduleTensorPresheaf G
      (moduleHomSheaf M (SheafOfModules.unit R) ring_comm) ring_comm).obj V)
    (Y := (moduleHomSheaf M G ring_comm).val.obj V)
    (lineSheafTensorEvalAt M G ring_comm V.unop)
  naturality {V W} f := by
    let := moduleSectionCommRing ring_comm V
    let := moduleSectionCommRing ring_comm W
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro g φ
    change lineSheafTensorEvalAt M G ring_comm W.unop
      ((moduleTensorPresheaf G (moduleHomSheaf M (SheafOfModules.unit R) ring_comm)
        ring_comm).map f (g ⊗ₜ[R.obj.obj V] φ)) =
      (moduleHomSheaf M G ring_comm).val.map f
        (lineSheafTensorEvalAt M G ring_comm V.unop (g ⊗ₜ[R.obj.obj V] φ))
    rw [moduleTensorPresheaf_map_tmul]
    apply moduleHom_ext M G ring_comm W.unop
    intro Z h m
    change moduleHomEval M G ring_comm W.unop Z h
      (lineSheafTensorEvalAt M G ring_comm W.unop
        (G.val.map f g ⊗ₜ[R.obj.obj W]
          (moduleHomSheaf M (SheafOfModules.unit R) ring_comm).val.map f φ)) m =
      moduleHomEval M G ring_comm W.unop Z h
        ((moduleHomSheaf M G ring_comm).val.map
          (homOfLE (leOfHom f.unop)).op
          (lineSheafTensorEvalAt M G ring_comm V.unop (g ⊗ₜ[R.obj.obj V] φ))) m
    rw [lineSheafTensorEvalAt_tmul, moduleHom_restrict, lineSheafTensorEvalAt_tmul]
    have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
    rw [hf, moduleHom_restrict]
    congr 1
    exact (G.val.map_comp_apply f (homOfLE h).op g).symm

/-- The presheaf evaluation sends a pure tensor to pointwise scalar evaluation. -/
theorem lineSheafTensorEvalPresheaf_pure (V W : Opens X) (h : W ≤ V)
    (g : G.val.obj (op V))
    (φ : (moduleHomSheaf M (SheafOfModules.unit R) ring_comm).val.obj (op V))
    (m : M.val.obj (op W)) :
    moduleHomEval M G ring_comm V W h
      ((lineSheafTensorEvalPresheaf M G ring_comm).app (op V)
        (moduleTensorPresheafPure G (moduleHomSheaf M (SheafOfModules.unit R) ring_comm)
          ring_comm (op V) g φ)) m =
      (moduleHomEval M (SheafOfModules.unit R) ring_comm V W h φ m : R.obj.obj (op W)) •
        G.val.restrictₛₗ (homOfLE h).op g := rfl

private def lineSheafTensorLocalEquiv {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ M.over U)
    (V : Opens X) (h : V ≤ U) :
    (moduleTensorPresheaf G (moduleHomSheaf M (SheafOfModules.unit R) ring_comm)
      ring_comm).obj (op V) ≃ₗ[R.obj.obj (op V)]
        (moduleHomSheaf M G ring_comm).val.obj (op V) := by
  letI := moduleSectionCommRing ring_comm (op V)
  exact ((TensorProduct.congr (LinearEquiv.refl (R.obj.obj (op V)) (G.val.obj (op V)))
    (moduleHomSectionEquiv M (SheafOfModules.unit R) ring_comm e V h)).trans
      (lineTensorHomEquiv (G := G.val.obj (op V)) (moduleLineFrameAt M e V h).symm)).trans
        (moduleHomSectionEquiv M G ring_comm e V h).symm

private theorem lineSheafTensorLocalEquiv_eq {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ M.over U)
    (V : Opens X) (h : V ≤ U) :
    (lineSheafTensorLocalEquiv M G ring_comm e V h).toLinearMap =
      lineSheafTensorEvalAt M G ring_comm V := by
  let := moduleSectionCommRing ring_comm (op V)
  apply TensorProduct.ext
  ext g φ : 2
  apply (moduleHomSectionEquiv M G ring_comm e V h).injective
  change moduleHomSectionEquiv M G ring_comm e V h
    (lineSheafTensorLocalEquiv M G ring_comm e V h (g ⊗ₜ[R.obj.obj (op V)] φ)) = _
  simp only [lineSheafTensorLocalEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  ext m
  change moduleHomEval M (SheafOfModules.unit R) ring_comm V V le_rfl φ m • g =
    moduleHomEval M G ring_comm V V le_rfl
      (lineSheafTensorEvalAt M G ring_comm V (g ⊗ₜ[R.obj.obj (op V)] φ)) m
  rw [lineSheafTensorEvalAt_tmul]
  congr 1
  change g = G.val.restrictₛₗ (𝟙 (op V)) g
  simp

/-- Canonical tensor evaluation is bijective on every subopen of a genuine
rank-one trivialization. The target sheaf is arbitrary. -/
theorem lineSheafTensorEvalAt_bijective {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ M.over U)
    (V : Opens X) (h : V ≤ U) :
    Function.Bijective (lineSheafTensorEvalAt M G ring_comm V) := by
  rw [← lineSheafTensorLocalEquiv_eq M G ring_comm e V h]
  exact (lineSheafTensorLocalEquiv M G ring_comm e V h).bijective

/-- Canonical evaluation extends to the actual tensor sheaf by its universal property. -/
def lineSheafTensorEval :
    moduleTensorSheaf G (moduleHomSheaf M (SheafOfModules.unit R) ring_comm) ring_comm ⟶
      moduleHomSheaf M G ring_comm :=
  moduleTensorLift G (moduleHomSheaf M (SheafOfModules.unit R) ring_comm)
    ring_comm (moduleHomSheaf M G ring_comm)
    (lineSheafTensorEvalPresheaf M G ring_comm)

/-- Evaluation on the tensor sheaf still has the canonical pure-tensor formula. -/
theorem lineSheafTensorEval_pure (V W : Opens X) (h : W ≤ V)
    (g : G.val.obj (op V))
    (φ : (moduleHomSheaf M (SheafOfModules.unit R) ring_comm).val.obj (op V))
    (m : M.val.obj (op W)) :
    moduleHomEval M G ring_comm V W h
      ((lineSheafTensorEval M G ring_comm).val.app (op V)
        (moduleTensorPure G (moduleHomSheaf M (SheafOfModules.unit R) ring_comm)
          ring_comm (op V) g φ)) m =
      (moduleHomEval M (SheafOfModules.unit R) ring_comm V W h φ m : R.obj.obj (op W)) •
        G.val.restrictₛₗ (homOfLE h).op g := by
  rw [lineSheafTensorEval, moduleTensorLift_pure]
  exact lineSheafTensorEvalPresheaf_pure M G ring_comm V W h g φ m

/-- An actual covering family of line trivializations makes tensor evaluation
an isomorphism globally. No target local freeness is required. -/
theorem lineSheafTensorEval_isIso {ι : Type u} (U : ι → Opens X)
    (hcover : iSup U = ⊤)
    (triv : ∀ i, (SheafOfModules.unit R).over (U i) ≅ M.over (U i)) :
    IsIso (lineSheafTensorEval M G ring_comm) := by
  apply sheafificationLift_isIso_of_cover
    (lineSheafTensorEvalPresheaf M G ring_comm) U hcover
  intro i V h
  exact lineSheafTensorEvalAt_bijective M G ring_comm (triv i) V h

/-- The canonical isomorphism `G ⊗ Hom(M,R) ≅ Hom(M,G)` for an actual
locally trivial line sheaf `M`. -/
def lineSheafTensorIso {ι : Type u} (U : ι → Opens X)
    (hcover : iSup U = ⊤)
    (triv : ∀ i, (SheafOfModules.unit R).over (U i) ≅ M.over (U i)) :
    moduleTensorSheaf G (moduleHomSheaf M (SheafOfModules.unit R) ring_comm) ring_comm ≅
      moduleHomSheaf M G ring_comm := by
  have := lineSheafTensorEval_isIso M G ring_comm U hcover triv
  exact asIso (lineSheafTensorEval M G ring_comm)

/-- The isomorphism's forward map is canonical evaluation, independent of the cover. -/
theorem lineSheafTensorIso_hom {ι : Type u} (U : ι → Opens X)
    (hcover : iSup U = ⊤)
    (triv : ∀ i, (SheafOfModules.unit R).over (U i) ≅ M.over (U i)) :
    (lineSheafTensorIso M G ring_comm U hcover triv).hom =
      lineSheafTensorEval M G ring_comm := rfl

end Normalizer
