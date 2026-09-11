import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Algebra.Category.Grp.Colimits

/-! The exact left adjoint to restriction of abelian sheaves to a slice site.
The presheaf construction sums over the actual arrows into the sliced object. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits Opposite
attribute [local instance] Classical.propDecidable
universe u
variable {C : Type u} [SmallCategory C] (U : C)

private def extensionMap (P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {Y Z : Cᵒᵖ} (f : Y ⟶ Z) :
    (Π₀ (a : Y.unop ⟶ U), P.obj (op (Over.mk a))) →+
      (Π₀ (a : Z.unop ⟶ U), P.obj (op (Over.mk a))) :=
  DFinsupp.liftAddHom fun a =>
    (DFinsupp.singleAddHom _ (f.unop ≫ a)).comp
      (P.map (Over.homMk f.unop (show f.unop ≫ a = f.unop ≫ a from rfl)).op).hom

private lemma extensionMap_single (P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {Y Z : Cᵒᵖ} (f : Y ⟶ Z) (a : Y.unop ⟶ U) (b : Z.unop ⟶ U)
    (h : f.unop ≫ a = b) (x : P.obj (op (Over.mk a))) :
    extensionMap U P f (DFinsupp.single a x) =
      DFinsupp.single b (P.map (Over.homMk f.unop h).op x) := by
  subst b
  simp [extensionMap]

/-- Extension of an abelian presheaf from the slice, by the direct sum over
all arrows into the sliced object. -/
def overAbelianExtensionObj (P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Cᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj Y := AddCommGrpCat.of (Π₀ (a : Y.unop ⟶ U), P.obj (op (Over.mk a)))
  map f := AddCommGrpCat.ofHom (extensionMap U P f)
  map_id Y := by
    apply AddCommGrpCat.hom_ext
    apply DFinsupp.liftAddHom.symm.injective
    funext a
    apply AddMonoidHom.ext
    intro x
    change extensionMap U P (𝟙 Y) (DFinsupp.single a x) = DFinsupp.single a x
    rw [extensionMap_single U P (𝟙 Y) a a (Category.id_comp a)]
    change DFinsupp.single (β := fun a : Y.unop ⟶ U => P.obj (op (Over.mk a)))
      a (P.map (𝟙 _) x) = _
    simp
  map_comp {Y Z W} f g := by
    apply AddCommGrpCat.hom_ext
    apply DFinsupp.liftAddHom.symm.injective
    funext a
    apply AddMonoidHom.ext
    intro x
    change extensionMap U P (f ≫ g) (DFinsupp.single a x) =
      extensionMap U P g (extensionMap U P f (DFinsupp.single a x))
    rw [extensionMap_single U P (f ≫ g) a ((g.unop ≫ f.unop) ≫ a) rfl,
      extensionMap_single U P f a (f.unop ≫ a) rfl,
      extensionMap_single U P g (f.unop ≫ a) ((g.unop ≫ f.unop) ≫ a)
        (Category.assoc _ _ _).symm]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp]
    rfl

/-- A morphism of slice presheaves acts on each direct-sum coefficient. -/
def overAbelianExtensionMap
    {P Q : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q) :
    overAbelianExtensionObj U P ⟶ overAbelianExtensionObj U Q where
  app Y := AddCommGrpCat.ofHom <| DFinsupp.mapRange.addMonoidHom fun a =>
    (φ.app (op (Over.mk a))).hom
  naturality {Y Z} f := by
    apply AddCommGrpCat.hom_ext
    apply DFinsupp.liftAddHom.symm.injective
    funext a
    apply AddMonoidHom.ext
    intro x
    change DFinsupp.mapRange.addMonoidHom _
      (extensionMap U P f (DFinsupp.single a x)) =
      extensionMap U Q f (DFinsupp.mapRange.addMonoidHom
        (fun a => (φ.app (op (Over.mk a))).hom) (DFinsupp.single a x))
    rw [extensionMap_single U P f a (f.unop ≫ a) rfl]
    simp only [DFinsupp.mapRange.addMonoidHom_apply, DFinsupp.mapRange_single]
    rw [extensionMap_single U Q f a (f.unop ≫ a) rfl]
    congr 1
    exact ConcreteCategory.congr_hom (φ.naturality _) x

/-- The direct-sum extension functor on actual abelian presheaves. -/
def overAbelianExtension : ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
    (Cᵒᵖ ⥤ AddCommGrpCat.{u}) where
  obj := overAbelianExtensionObj U
  map := overAbelianExtensionMap U
  map_id P := by
    ext Y x
    apply DFinsupp.ext
    intro a
    rfl
  map_comp f g := by
    ext Y x
    apply DFinsupp.ext
    intro a
    rfl

private def extensionHomTo {P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    {Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (ψ : overAbelianExtensionObj U P ⟶ Q) :
    P ⟶ (Over.forget U).op ⋙ Q where
  app Y := AddCommGrpCat.ofHom <|
    (ψ.app (op Y.unop.left)).hom.comp (DFinsupp.singleAddHom
      (fun a : Y.unop.left ⟶ U => P.obj (op (Over.mk a))) Y.unop.hom)
  naturality {Y Z} f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    change ψ.app (op Z.unop.left) (DFinsupp.single Z.unop.hom (P.map f x)) =
      Q.map f.unop.left.op (ψ.app (op Y.unop.left) (DFinsupp.single Y.unop.hom x))
    have hn := ConcreteCategory.congr_hom (ψ.naturality f.unop.left.op)
      (DFinsupp.single Y.unop.hom x)
    change ψ.app (op Z.unop.left)
      (extensionMap U P f.unop.left.op (DFinsupp.single Y.unop.hom x)) = _ at hn
    rw [extensionMap_single U P f.unop.left.op Y.unop.hom Z.unop.hom
      (Over.w f.unop)] at hn
    exact hn

private def extensionHomFrom {P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    {Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ (Over.forget U).op ⋙ Q) :
    overAbelianExtensionObj U P ⟶ Q where
  app Y := AddCommGrpCat.ofHom <| DFinsupp.liftAddHom fun a =>
    (φ.app (op (Over.mk a))).hom
  naturality {Y Z} f := by
    apply AddCommGrpCat.hom_ext
    apply DFinsupp.liftAddHom.symm.injective
    funext a
    apply AddMonoidHom.ext
    intro x
    change DFinsupp.liftAddHom (fun a => (φ.app (op (Over.mk a))).hom)
      (extensionMap U P f (DFinsupp.single a x)) =
      Q.map f (DFinsupp.liftAddHom (fun a => (φ.app (op (Over.mk a))).hom)
        (DFinsupp.single a x))
    rw [extensionMap_single U P f a (f.unop ≫ a) rfl]
    simp only [DFinsupp.liftAddHom_apply_single]
    exact ConcreteCategory.congr_hom (φ.naturality
      (Over.homMk (U := Over.mk (f.unop ≫ a)) (V := Over.mk a)
        f.unop (show f.unop ≫ a = f.unop ≫ a from rfl)).op) x

/-- The direct-sum construction is left adjoint to actual slice restriction
of abelian presheaves. -/
def overAbelianExtensionAdjunction : overAbelianExtension U ⊣
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj (Over.forget U).op :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q =>
        { toFun := extensionHomTo U
          invFun := extensionHomFrom U
          left_inv := fun ψ => by
            apply NatTrans.ext
            funext Y
            apply AddCommGrpCat.hom_ext
            apply DFinsupp.liftAddHom.symm.injective
            funext a
            apply AddMonoidHom.ext
            intro x
            change DFinsupp.liftAddHom
              (fun a => (ψ.app Y).hom.comp (DFinsupp.singleAddHom
                (fun a : Y.unop ⟶ U => P.obj (op (Over.mk a))) a))
              (DFinsupp.single a x) = _
            rw [DFinsupp.liftAddHom_apply_single]
            rfl
          right_inv := fun φ => by
            apply NatTrans.ext
            funext Y
            apply AddCommGrpCat.hom_ext
            apply AddMonoidHom.ext
            intro x
            change DFinsupp.liftAddHom (γ := Q.obj (op Y.unop.left))
              (fun a : Y.unop.left ⟶ U =>
              (φ.app (op (Over.mk a))).hom)
              (DFinsupp.single (β := fun a : Y.unop.left ⟶ U =>
                P.obj (op (Over.mk a))) Y.unop.hom x) = _
            rw [DFinsupp.liftAddHom_apply_single]
            rfl }
      homEquiv_naturality_left_symm := fun {P P' Q} f g => by
        apply NatTrans.ext
        funext Y
        apply AddCommGrpCat.hom_ext
        apply DFinsupp.liftAddHom.symm.injective
        funext a
        apply AddMonoidHom.ext
        intro x
        change DFinsupp.liftAddHom (γ := Q.obj Y) (fun a : Y.unop ⟶ U =>
          ((f ≫ g).app (op (Over.mk a))).hom)
          (DFinsupp.single a x) =
          DFinsupp.liftAddHom (γ := Q.obj Y) (fun a : Y.unop ⟶ U => (g.app (op (Over.mk a))).hom) (DFinsupp.mapRange.addMonoidHom
            (fun a => (f.app (op (Over.mk a))).hom) (DFinsupp.single a x))
        simp only [DFinsupp.mapRange.addMonoidHom_apply, DFinsupp.mapRange_single,
          DFinsupp.liftAddHom_apply_single]
        rfl
      homEquiv_naturality_right := fun f g => by
        apply NatTrans.ext
        funext Y
        rfl }

/-- Extension preserves injections because it acts coefficientwise. -/
theorem overAbelianExtension_preservesMonomorphisms :
    (overAbelianExtension U).PreservesMonomorphisms where
  preserves {P Q} φ hφ := by
    let _ := hφ
    have : ∀ Y, Mono (((overAbelianExtension U).map φ).app Y) := by
      intro Y
      apply (AddCommGrpCat.mono_iff_injective _).mpr
      intro x y h
      apply DFinsupp.ext
      intro a
      apply (AddCommGrpCat.mono_iff_injective (φ.app (op (Over.mk a)))).mp
        inferInstance
      exact congrArg (fun z : Π₀ (a : Y.unop ⟶ U), Q.obj (op (Over.mk a)) => z a) h
    exact NatTrans.mono_of_mono_app _

/-- Extension respects addition of presheaf morphisms. -/
theorem overAbelianExtension_additive : (overAbelianExtension U).Additive where
  map_add {P Q} f g := by
    ext Y x
    apply DFinsupp.ext
    intro a
    rfl

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u}]
  [HasSheafify (J.over U) AddCommGrpCat.{u}]

/-- The actual left extension of abelian sheaves on the slice site. -/
def overAbelianSheafExtension : Sheaf (J.over U) AddCommGrpCat.{u} ⥤
    Sheaf J AddCommGrpCat.{u} :=
  sheafToPresheaf (J.over U) AddCommGrpCat.{u} ⋙ overAbelianExtension U ⋙
    presheafToSheaf J AddCommGrpCat.{u}

/-- Sheafification promotes the constructed presheaf adjunction to an
adjunction with mathlib's actual slice restriction functor. -/
def overAbelianSheafExtensionAdjunction :
    overAbelianSheafExtension U J ⊣ J.overPullback AddCommGrpCat.{u} U :=
  ((overAbelianExtensionAdjunction U).comp
    (sheafificationAdjunction J AddCommGrpCat.{u})).restrictFullyFaithful
      (fullyFaithfulSheafToPresheaf (J.over U) AddCommGrpCat.{u})
      (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

omit [HasSheafify (J.over U) AddCommGrpCat.{u}] in
/-- The sheaf extension is additive. -/
theorem overAbelianSheafExtension_additive :
    (overAbelianSheafExtension U J).Additive := by
  have := overAbelianExtension_additive U
  have : (sheafToPresheaf (J.over U) AddCommGrpCat.{u}).Additive :=
    { map_add := by intros; rfl }
  unfold overAbelianSheafExtension
  infer_instance

attribute [local instance] overAbelianSheafExtension_additive

/-- The actual sheaf extension is exact; no exactness hypothesis is imposed. -/
theorem overAbelianSheafExtension_preservesHomology :
    (overAbelianSheafExtension U J).PreservesHomology := by
  have := overAbelianExtension_preservesMonomorphisms U
  have := overAbelianSheafExtension_additive U J
  have := (overAbelianSheafExtensionAdjunction U J).isLeftAdjoint
  have : (overAbelianSheafExtension U J).PreservesMonomorphisms := by
    unfold overAbelianSheafExtension
    infer_instance
  exact (overAbelianSheafExtension U J).preservesHomology_of_preservesMonos_and_cokernels

omit [HasSheafify J AddCommGrpCat.{u}] [HasSheafify (J.over U) AddCommGrpCat.{u}] in
/-- Slice restriction preserves epimorphisms: cocontinuity supplies its
right adjoint by right Kan extension on the small slice site. -/
theorem overAbelianRestriction_preservesEpimorphisms :
    (J.overPullback AddCommGrpCat.{u} U).PreservesEpimorphisms := by
  have := ((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
    (J.over U) J).isLeftAdjoint
  infer_instance

omit [HasSheafify J AddCommGrpCat.{u}] [HasSheafify (J.over U) AddCommGrpCat.{u}] in
/-- Slice restriction is additive. -/
theorem overAbelianRestriction_additive :
    (J.overPullback AddCommGrpCat.{u} U).Additive where
  map_add {_ _} _ _ := rfl

attribute [local instance] overAbelianRestriction_additive

/-- Actual restriction of abelian sheaves to the slice site is exact. -/
theorem overAbelianRestriction_preservesHomology :
    (J.overPullback AddCommGrpCat.{u} U).PreservesHomology := by
  have := overAbelianRestriction_preservesEpimorphisms U J
  have := overAbelianRestriction_additive U J
  have := (overAbelianSheafExtensionAdjunction U J).isRightAdjoint
  exact (J.overPullback AddCommGrpCat.{u} U).preservesHomology_of_preservesEpis_and_kernels

end Normalizer
