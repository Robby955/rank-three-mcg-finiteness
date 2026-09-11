import Normalizer.AbelianSheafPullbackExact
import Normalizer.ClosedPushforwardExact
import Normalizer.ConstantSheafPullback
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-! Cohomology of the actual direct image along a closed embedding.
Both exact functors and the pullback of the constant integer sheaf are constructed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory Limits TopologicalSpace Topology Opposite Abelian

universe u
variable {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : IsClosedEmbedding f)

/-- Cohomology of an actual closed direct image agrees with intrinsic
cohomology, in every degree. This is an additive equivalence. -/
def closedPushforwardCohomologyEquiv
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    CategoryTheory.Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) n ≃+
      CategoryTheory.Sheaf.H F n := by
  have := abelianSheafPullback_preservesFiniteLimits f
  have := abelianSheafPullback_additive f
  have := abelianSheafPushforward_additive f
  have := closedPushforward_preservesFiniteColimits f hf
  exact (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).extEquiv.symm.trans
    (((extFunctor n).mapIso
      (((abelianSheafPullbackConstantIso f).app (AddCommGrpCat.of (ULift.{u} ℤ))).symm.op)).app F).addCommGroupIsoToAddEquiv

/-- The comparison preserves cohomology maps of actual sheaf morphisms. -/
theorem closedPushforwardCohomologyEquiv_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (a : F ⟶ G) (n : ℕ)
    (x : CategoryTheory.Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) n) :
    closedPushforwardCohomologyEquiv f hf G n
      (CategoryTheory.Sheaf.H.map ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map a) n x) =
    CategoryTheory.Sheaf.H.map a n (closedPushforwardCohomologyEquiv f hf F n x) := by
  have := abelianSheafPullback_preservesFiniteLimits f
  have := abelianSheafPullback_additive f
  have := abelianSheafPushforward_additive f
  have := closedPushforward_preservesFiniteColimits f hf
  change (Ext.mk₀ _).comp
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).extEquiv.symm
      (x.comp (Ext.mk₀ _) (add_zero n))) (zero_add n) =
    ((Ext.mk₀ _).comp
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).extEquiv.symm x)
        (zero_add n)).comp (Ext.mk₀ a) (add_zero n)
  rw [Adjunction.extEquiv_symm_naturality_right₀, Ext.comp_assoc_of_third_deg_zero]

/-- The constructed comparison in degree zero is the actual identification of
global sections of direct image, under mathlib's `H.equiv₀`. -/
theorem closedPushforwardCohomologyEquiv_equiv₀
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (x : CategoryTheory.Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) 0) :
    CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop
      (closedPushforwardCohomologyEquiv f hf F 0 x) =
    CategoryTheory.Sheaf.H.equiv₀
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) isTerminalTop x := by
  have := abelianSheafPullback_preservesFiniteLimits f
  have := abelianSheafPullback_additive f
  have := abelianSheafPushforward_additive f
  have := closedPushforward_preservesFiniteColimits f hf
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
  change CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop
    ((Ext.mk₀ _).comp
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).extEquiv.symm
        (Ext.mk₀ a)) (zero_add 0)) = _
  rw [Adjunction.extEquiv_symm_mk₀, Ext.mk₀_comp_mk₀]
  simp only [CategoryTheory.Sheaf.H.equiv₀, AddEquiv.trans_apply]
  change (AddCommGrpCat.uliftZMultiplesAddEquiv _)
    ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ F
        (Ext.addEquiv₀ (Ext.mk₀ _))) =
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)
      ((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
        isTerminalTop).homEquiv _ _ (Ext.addEquiv₀ (Ext.mk₀ a)))
  simp only [← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  exact congrArg (AddCommGrpCat.uliftZMultiplesAddEquiv _)
    ((abelianSheafPullbackConstant_homEquiv f _ F _).trans
      (congrArg _ (Equiv.apply_symm_apply _ a)))

end Normalizer
