import Normalizer.NormalizerSheaf
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! The internal Hom of actual module sheaves. Its sections on an open
are linear morphisms on all smaller opens. Linearity is a local condition,
so the ordinary sheaf of restricted morphisms supplies the sheaf condition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Opposite TopologicalSpace

universe u
variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  (A B : SheafOfModules.{u} R)

private abbrev rawHom (V : (Opens X)ᵒᵖ) :=
  (Over.forget V.unop).op ⋙ A.val.presheaf ⟶
    (Over.forget V.unop).op ⋙ B.val.presheaf

private def rawHomApp {V : (Opens X)ᵒᵖ} (f : rawHom A B V) (W : Over V.unop) :
    A.val.obj (op W.left) →+ B.val.obj (op W.left) :=
  (f.app (op W)).hom

private def rawHomSmul (V : (Opens X)ᵒᵖ) (r : R.obj.obj V)
    (f : rawHom A B V) : rawHom A B V where
  app W := AddCommGrpCat.ofHom
    { toFun := fun m => R.obj.map W.unop.hom.op r • rawHomApp A B f W.unop m
      map_zero' := by simp
      map_add' := by intro x y; simp [smul_add] }
  naturality := by
    intro W Z h
    ext m
    change R.obj.map Z.unop.hom.op r •
        rawHomApp A B f Z.unop (A.val.map h.unop.left.op m) =
      B.val.map h.unop.left.op (R.obj.map W.unop.hom.op r •
        rawHomApp A B f W.unop m)
    rw [B.val.map_smul]
    have hn := ConcreteCategory.congr_hom (f.naturality h) m
    change rawHomApp A B f Z.unop (A.val.map h.unop.left.op m) =
      B.val.map h.unop.left.op (rawHomApp A B f W.unop m) at hn
    rw [hn]
    congr 1
    have hh : W.unop.hom.op ≫ h.unop.left.op = Z.unop.hom.op :=
      congrArg Quiver.Hom.op (Over.w h.unop)
    simpa only [hh, ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom
      (R.obj.map_comp W.unop.hom.op h.unop.left.op) r

private instance rawHomSMul (V : (Opens X)ᵒᵖ) : SMul (R.obj.obj V) (rawHom A B V) :=
  ⟨rawHomSmul A B V⟩

private instance rawHomModule (V : (Opens X)ᵒᵖ) : Module (R.obj.obj V) (rawHom A B V) where
  one_smul := by
    intro f; ext W m
    change R.obj.map W.unop.hom.op 1 • rawHomApp A B f W.unop m = _
    simp [rawHomApp]
  mul_smul := by
    intro a b f; ext W m
    change R.obj.map W.unop.hom.op (a * b) • rawHomApp A B f W.unop m =
      R.obj.map W.unop.hom.op a • (R.obj.map W.unop.hom.op b • rawHomApp A B f W.unop m)
    simp [smul_smul]
  smul_zero := by
    intro a; ext W m
    change R.obj.map W.unop.hom.op a • (0 : B.val.obj (op W.unop.left)) = 0
    exact smul_zero _
  smul_add := by
    intro a f g; ext W m
    change R.obj.map W.unop.hom.op a •
      (rawHomApp A B f W.unop m + rawHomApp A B g W.unop m) = _
    exact smul_add _ _ _
  add_smul := by
    intro a b f; ext W m
    change R.obj.map W.unop.hom.op (a + b) • rawHomApp A B f W.unop m = _
    rw [map_add]
    exact add_smul _ _ _
  zero_smul := by
    intro f; ext W m
    change R.obj.map W.unop.hom.op 0 • rawHomApp A B f W.unop m = 0
    simp

variable (ring_comm : ∀ V (a b : R.obj.obj V), a * b = b * a)

private def linearHomSubmodule (V : (Opens X)ᵒᵖ) : Submodule (R.obj.obj V) (rawHom A B V) where
  carrier := { f | ∀ (W : Over V.unop) (r : R.obj.obj (op W.left))
    (m : A.val.obj (op W.left)), rawHomApp A B f W (r • m) =
      r • rawHomApp A B f W m }
  zero_mem' := by
    intro W r m
    change (0 : B.val.obj (op W.left)) = r • 0
    exact (smul_zero r).symm
  add_mem' := by
    intro f g hf hg W r m
    change rawHomApp A B f W (r • m) + rawHomApp A B g W (r • m) =
      r • (rawHomApp A B f W m + rawHomApp A B g W m)
    rw [hf, hg, smul_add]
  smul_mem' := by
    intro a f hf W r m
    change R.obj.map W.hom.op a • rawHomApp A B f W (r • m) =
      r • (R.obj.map W.hom.op a • rawHomApp A B f W m)
    rw [hf W r m, smul_smul, smul_smul, ring_comm]

private def linearHomSubfunctor : Subfunctor (presheafHom A.val.presheaf B.val.presheaf) where
  obj V := (linearHomSubmodule A B ring_comm V : Set (rawHom A B V))
  map := by
    intro V W h f hf Z r m
    exact hf ((Over.map h.unop).obj Z) r m

private def linearHomAbPresheaf : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (linearHomSubmodule A B ring_comm V)
  map h := AddCommGrpCat.ofHom
    { toFun := fun f => ⟨(presheafHom A.val.presheaf B.val.presheaf).map h f.val,
        (linearHomSubfunctor A B ring_comm).map h f.property⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id V := by
    ext f : 2
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((presheafHom A.val.presheaf B.val.presheaf).map_id V) f.val
  map_comp h k := by
    ext f : 2
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((presheafHom A.val.presheaf B.val.presheaf).map_comp h k) f.val

private instance linearHomAbModule (V : (Opens X)ᵒᵖ) :
    Module (R.obj.obj V) ((linearHomAbPresheaf A B ring_comm).obj V) :=
  inferInstanceAs (Module (R.obj.obj V) (linearHomSubmodule A B ring_comm V))

private def linearHomPresheaf : PresheafOfModules.{u} R.obj :=
  PresheafOfModules.ofPresheaf (linearHomAbPresheaf A B ring_comm) (by
    intro V W h r f
    apply Subtype.ext
    ext Z m
    change R.obj.map (Z.unop.hom ≫ h.unop).op r •
        rawHomApp A B f.val ((Over.map h.unop).obj Z.unop) m =
      R.obj.map Z.unop.hom.op (R.obj.map h r) •
        rawHomApp A B f.val ((Over.map h.unop).obj Z.unop) m
    congr 1
    exact ConcreteCategory.congr_hom (R.obj.map_comp h Z.unop.hom.op) r)

private theorem linearHomSubfunctor_isSheaf :
    Presieve.IsSheaf (Opens.grothendieckTopology X)
      (linearHomSubfunctor A B ring_comm).toFunctor := by
  let J := Opens.grothendieckTopology X
  have hraw : Presieve.IsSheaf J (presheafHom A.val.presheaf B.val.presheaf) :=
    (isSheaf_iff_isSheaf_of_type J _).mp
      (Presheaf.IsSheaf.hom A.val.presheaf B.val.presheaf B.isSheaf)
  have hB : Presieve.IsSheaf J (B.val.presheaf ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type J _).mp
      ((Presheaf.isSheaf_iff_isSheaf_comp J B.val.presheaf (forget AddCommGrpCat)).mp B.isSheaf)
  apply ((linearHomSubfunctor A B ring_comm).isSheaf_iff hraw).mpr
  intro V f hf W r m
  let S := (linearHomSubfunctor A B ring_comm).sieveOfSection f
  apply (hB (S.pullback W.hom) (J.pullback_stable W.hom hf)).isSeparatedFor.ext
  intro Z g hg
  let k : Over.mk (g ≫ W.hom) ⟶ W := Over.homMk g
  have hn (a : A.val.obj (op W.left)) := f.naturality_apply k.op a
  change ∀ a, rawHomApp A B f (Over.mk (g ≫ W.hom)) (A.val.map g.op a) =
    B.val.map g.op (rawHomApp A B f W a) at hn
  have hl := hg (Over.mk (𝟙 Z)) (R.obj.map g.op r) (A.val.map g.op m)
  change B.val.map g.op (rawHomApp A B f W (r • m)) =
    B.val.map g.op (r • rawHomApp A B f W m)
  rw [← hn, A.val.map_smul, B.val.map_smul, ← hn]
  dsimp only [rawHomApp] at hl ⊢
  rw [presheafHom_map_app (𝟙 Z) (g ≫ W.hom) (g ≫ W.hom) (by simp) f] at hl
  exact hl

/-- The actual sheaf of module morphisms on all smaller opens. -/
def moduleHomSheaf : SheafOfModules.{u} R where
  val := linearHomPresheaf A B ring_comm
  isSheaf := by
    apply Presheaf.isSheaf_of_isSheaf_comp (Opens.grothendieckTopology X) _
      (forget AddCommGrpCat)
    change Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (linearHomSubfunctor A B ring_comm).toFunctor
    exact (isSheaf_iff_isSheaf_of_type (Opens.grothendieckTopology X) _).mpr
      (linearHomSubfunctor_isSheaf A B ring_comm)

/-- Evaluate an internal-Hom section on a smaller open. -/
def moduleHomEval (V W : Opens X) (h : W ≤ V)
    (f : (moduleHomSheaf A B ring_comm).val.obj (op V)) :
    A.val.obj (op W) →ₗ[R.obj.obj (op W)] B.val.obj (op W) where
  toFun := rawHomApp A B f.val (Over.mk (homOfLE h))
  map_add' := (rawHomApp A B f.val (Over.mk (homOfLE h))).map_add
  map_smul' := f.property (Over.mk (homOfLE h))

/-- Compatible linear maps on every smaller open define an internal-Hom section. -/
def moduleHomMk (V : Opens X)
    (app : ∀ (W : Opens X), W ≤ V →
      A.val.obj (op W) →ₗ[R.obj.obj (op W)] B.val.obj (op W))
    (naturality : ∀ (W Z : Opens X) (h : W ≤ V) (k : Z ≤ W)
      (m : A.val.obj (op W)),
      B.val.map (homOfLE k).op (app W h m) =
        app Z (k.trans h) (A.val.map (homOfLE k).op m)) :
    (moduleHomSheaf A B ring_comm).val.obj (op V) := by
  refine ⟨{
    app := fun W => AddCommGrpCat.ofHom
      (app W.unop.left (leOfHom W.unop.hom)).toAddMonoidHom
    naturality := ?_ }, ?_⟩
  · intro W Z k
    ext m
    exact (naturality W.unop.left Z.unop.left (leOfHom W.unop.hom)
      (leOfHom k.unop.left) m).symm
  · intro W r m
    exact (app W.left (leOfHom W.hom)).map_smul r m

/-- The constructor recovers each of the supplied local maps. -/
theorem moduleHomEval_mk (V : Opens X)
    (app : ∀ (W : Opens X), W ≤ V →
      A.val.obj (op W) →ₗ[R.obj.obj (op W)] B.val.obj (op W))
    (naturality : ∀ (W Z : Opens X) (h : W ≤ V) (k : Z ≤ W)
      (m : A.val.obj (op W)),
      B.val.map (homOfLE k).op (app W h m) =
        app Z (k.trans h) (A.val.map (homOfLE k).op m))
    (W : Opens X) (h : W ≤ V) :
    moduleHomEval A B ring_comm V W h (moduleHomMk A B ring_comm V app naturality) =
      app W h := rfl

/-- An internal-Hom section is determined by its action on every smaller open. -/
theorem moduleHom_ext (V : Opens X)
    (f g : (moduleHomSheaf A B ring_comm).val.obj (op V))
    (h : ∀ (W : Opens X) (hWV : W ≤ V) (m : A.val.obj (op W)),
      moduleHomEval A B ring_comm V W hWV f m =
        moduleHomEval A B ring_comm V W hWV g m) : f = g := by
  apply Subtype.ext
  ext W m
  exact h W.unop.left (leOfHom W.unop.hom) m

/-- Evaluation commutes with restriction of the internal-Hom section. -/
theorem moduleHom_restrict (V W Z : Opens X) (h : W ≤ V) (k : Z ≤ W)
    (f : (moduleHomSheaf A B ring_comm).val.obj (op V)) :
    moduleHomEval A B ring_comm W Z k
      ((moduleHomSheaf A B ring_comm).val.map (homOfLE h).op f) =
      moduleHomEval A B ring_comm V Z (k.trans h) f := by
  ext m
  change (rawHomApp A B
    ((presheafHom A.val.presheaf B.val.presheaf).map (homOfLE h).op f.val)
    (Over.mk (homOfLE k))) m =
      rawHomApp A B f.val (Over.mk (homOfLE (k.trans h))) m
  dsimp only [rawHomApp]
  rw [presheafHom_map_app (homOfLE k) (homOfLE h) (homOfLE (k.trans h))
    (Subsingleton.elim _ _) f.val]
  rfl

/-- The component maps of an internal-Hom section are natural. -/
theorem moduleHomEval_natural (V W Z : Opens X) (h : W ≤ V) (k : Z ≤ W)
    (f : (moduleHomSheaf A B ring_comm).val.obj (op V)) (m : A.val.obj (op W)) :
    B.val.map (homOfLE k).op (moduleHomEval A B ring_comm V W h f m) =
      moduleHomEval A B ring_comm V Z (k.trans h) f
        (A.val.map (homOfLE k).op m) := by
  let j : Over.mk (homOfLE (k.trans h)) ⟶ Over.mk (homOfLE h) :=
    Over.homMk (homOfLE k)
  exact (f.val.naturality_apply j.op m).symm

/-- Zero internal-Hom sections act by zero. -/
theorem moduleHomEval_zero (V W : Opens X) (h : W ≤ V) :
    moduleHomEval A B ring_comm V W h 0 = 0 := rfl

/-- Addition of internal-Hom sections is componentwise addition. -/
theorem moduleHomEval_add (V W : Opens X) (h : W ≤ V)
    (f g : (moduleHomSheaf A B ring_comm).val.obj (op V)) :
    moduleHomEval A B ring_comm V W h (f + g) =
      moduleHomEval A B ring_comm V W h f + moduleHomEval A B ring_comm V W h g := rfl

/-- Scalar multiplication restricts the scalar to the smaller open. -/
theorem moduleHomEval_smul (V W : Opens X) (h : W ≤ V)
    (r : R.obj.obj (op V)) (f : (moduleHomSheaf A B ring_comm).val.obj (op V))
    (m : A.val.obj (op W)) :
    moduleHomEval A B ring_comm V W h (r • f) m =
      R.obj.map (homOfLE h).op r • moduleHomEval A B ring_comm V W h f m := rfl

/-- Internal-Hom sections are precisely morphisms of the actual restricted
module sheaves. This identifies the construction with the usual sheaf Hom. -/
def moduleHomOverEquiv (V : Opens X) :
    (moduleHomSheaf A B ring_comm).val.obj (op V) ≃ (A.over V ⟶ B.over V) where
  toFun f := ⟨{
    app := fun W => ModuleCat.ofHom
      (moduleHomEval A B ring_comm V W.unop.left (leOfHom W.unop.hom) f)
    naturality := by
      intro W Z k
      ext m
      exact (moduleHomEval_natural A B ring_comm V W.unop.left Z.unop.left
        (leOfHom W.unop.hom) (leOfHom k.unop.left) f m).symm }⟩
  invFun f := moduleHomMk A B ring_comm V
    (fun W h => (f.val.app (op (Over.mk (homOfLE h)))).hom)
    (by
      intro W Z h k m
      let j : Over.mk (homOfLE (k.trans h)) ⟶ Over.mk (homOfLE h) :=
        Over.homMk (homOfLE k)
      exact (PresheafOfModules.naturality_apply f.val j.op m).symm)
  left_inv f := by
    apply moduleHom_ext A B ring_comm V
    intro W h m
    rfl
  right_inv f := by
    ext W m
    rfl

end Normalizer
