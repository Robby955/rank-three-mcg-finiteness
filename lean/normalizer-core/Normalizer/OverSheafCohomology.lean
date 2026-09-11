import Normalizer.OverAbelianExtension
import Normalizer.SheafCohomologyTerminal
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! Actual sheaf cohomology of a slice site agrees with evaluation of the
cohomology presheaf. The extension functors and their exactness are constructed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits Opposite Abelian
universe w₁ w₂ u
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (U : C)
  [HasSheafify J AddCommGrpCat.{u}]

/-- The actual sheafified free representable corepresents evaluation of
abelian sheaves at the specified object. -/
def freeAbelianSheafEvaluation :
    (((sheafSections J AddCommGrpCat.{u}).obj (op U)) ⋙ forget AddCommGrpCat).CorepresentableBy
      ((presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)) where
  homEquiv := ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).trans
    (((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj).homEquiv _ _).trans yonedaEquiv)
  homEquiv_comp g f := by
    change (g.hom.app (op U))
      (f.hom.app (op U) ((toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app
        (op U) (FreeAbelianGroup.of (𝟙 U)))) = _
    rfl

/-- Evaluation of a morphism out of the represented abelian sheaf is its
value on the sheafified identity generator. -/
theorem freeAbelianSheafEvaluation_apply (F : Sheaf J AddCommGrpCat.{u})
    (f : (presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) :
    (freeAbelianSheafEvaluation J U).homEquiv f =
      f.hom.app (op U) ((toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app
        (op U) (FreeAbelianGroup.of (𝟙 U))) := rfl

variable [HasSheafify (J.over U) AddCommGrpCat.{u}]
attribute [local instance] overAbelianSheafExtension_additive overAbelianRestriction_additive

/-- Extending the constant integer sheaf from the slice corepresents the
same evaluation functor, using the actual restriction adjunction. -/
def extendedIntegerSheafEvaluation :
    (((sheafSections J AddCommGrpCat.{u}).obj (op U)) ⋙ forget AddCommGrpCat).CorepresentableBy
      ((overAbelianSheafExtension U J).obj
        ((constantSheaf (J.over U) AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) where
  homEquiv := ((overAbelianSheafExtensionAdjunction U J).homEquiv _ _).trans
    (((constantSheafAdj (J.over U) AddCommGrpCat Over.mkIdTerminal).homEquiv _ _).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv)
  homEquiv_comp g f := by
    change (AddCommGrpCat.uliftZMultiplesAddEquiv _)
      ((constantSheafAdj (J.over U) AddCommGrpCat Over.mkIdTerminal).homEquiv _ _
        ((overAbelianSheafExtensionAdjunction U J).homEquiv _ _ (f ≫ g))) = _
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
    rfl

/-- The extension of the actual constant integer sheaf is canonically the
actual free abelian sheaf represented by the sliced object. -/
def overAbelianExtensionIntegerIso :
    (overAbelianSheafExtension U J).obj
      ((constantSheaf (J.over U) AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ≅
      (presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free) :=
  (extendedIntegerSheafEvaluation J U).uniqueUpToIso (freeAbelianSheafEvaluation J U)

/-- The canonical comparison of representing objects preserves evaluation
on the distinguished generator. -/
theorem overAbelianExtensionIntegerIso_evaluation (F : Sheaf J AddCommGrpCat.{u})
    (f : (presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) :
    (extendedIntegerSheafEvaluation J U).homEquiv
      ((overAbelianExtensionIntegerIso J U).hom ≫ f) =
      (freeAbelianSheafEvaluation J U).homEquiv f := by
  change (extendedIntegerSheafEvaluation J U).homEquiv
    ((extendedIntegerSheafEvaluation J U).homEquiv.symm
      ((freeAbelianSheafEvaluation J U).homEquiv (𝟙 _)) ≫ f) = _
  rw [Functor.CorepresentableBy.homEquiv_comp, Equiv.apply_symm_apply,
    ← Functor.CorepresentableBy.homEquiv_comp, Category.id_comp]

attribute [local instance] overAbelianSheafExtension_preservesHomology
  overAbelianRestriction_preservesHomology

local instance : PreservesFiniteLimits (overAbelianSheafExtension U J) :=
  (overAbelianSheafExtension U J).preservesFiniteLimits_of_preservesHomology
local instance : PreservesFiniteColimits (overAbelianSheafExtension U J) :=
  (overAbelianSheafExtension U J).preservesFiniteColimits_of_preservesHomology
local instance : PreservesFiniteLimits (J.overPullback AddCommGrpCat.{u} U) :=
  (J.overPullback AddCommGrpCat.{u} U).preservesFiniteLimits_of_preservesHomology
local instance : PreservesFiniteColimits (J.overPullback AddCommGrpCat.{u} U) :=
  (J.overPullback AddCommGrpCat.{u} U).preservesFiniteColimits_of_preservesHomology

variable [HasExt.{w₁} (Sheaf J AddCommGrpCat.{u})]
  [HasExt.{w₂} (Sheaf (J.over U) AddCommGrpCat.{u})]

/-- Evaluation of the actual cohomology presheaf at an object agrees, in
every degree, with intrinsic cohomology of the actual restricted sheaf. -/
def overSheafCohomologyEquiv (F : Sheaf J AddCommGrpCat.{u}) (n : ℕ) :
    F.H' n U ≃+ (F.over U).H n :=
  ((((extFunctor n).mapIso (overAbelianExtensionIntegerIso J U).op).app
    F).addCommGroupIsoToAddEquiv).trans
      (overAbelianSheafExtensionAdjunction U J).extEquiv

/-- The slice cohomology comparison commutes with maps of actual sheaves. -/
theorem overSheafCohomologyEquiv_naturality
    {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G) (n : ℕ) (x : F.H' n U) :
    overSheafCohomologyEquiv J U G n
      (((Sheaf.cohomologyPresheafFunctor J n).map f).app (op U) x) =
    Sheaf.H.map ((J.overPullback AddCommGrpCat.{u} U).map f) n
      (overSheafCohomologyEquiv J U F n x) := by
  change (overAbelianSheafExtensionAdjunction U J).extEquiv
    ((Ext.mk₀ _).comp (x.comp (Ext.mk₀ f) (add_zero n)) (zero_add n)) =
      ((overAbelianSheafExtensionAdjunction U J).extEquiv
        ((Ext.mk₀ _).comp x (zero_add n))).comp (Ext.mk₀ _) (add_zero n)
  rw [← Ext.comp_assoc_of_third_deg_zero, Adjunction.extEquiv_naturality_right₀]

/-- In degree zero the slice comparison gives the actual section obtained
by evaluating on the sheafified identity generator at the sliced object. -/
theorem overSheafCohomologyEquiv_equiv₀
    (F : Sheaf J AddCommGrpCat.{u}) (x : F.H' 0 U) :
    Sheaf.H.equiv₀ (F.over U) Over.mkIdTerminal (overSheafCohomologyEquiv J U F 0 x) =
      (Ext.addEquiv₀ x).hom.app (op U)
        ((toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U)
          (FreeAbelianGroup.of (𝟙 U))) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
  change Sheaf.H.equiv₀ (F.over U) Over.mkIdTerminal
    ((overAbelianSheafExtensionAdjunction U J).extEquiv
      ((Ext.mk₀ _).comp (Ext.mk₀ a) (zero_add 0))) = _
  rw [Ext.mk₀_comp_mk₀, Adjunction.extEquiv_mk₀]
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply,
    ← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  exact (overAbelianExtensionIntegerIso_evaluation J U F a).trans
    (freeAbelianSheafEvaluation_apply J U F a)

end Normalizer
