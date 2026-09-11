import Normalizer.OverSheafCohomology
import Mathlib.Topology.Sheaves.Over
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-! Actual cohomology on an open subspace, compared with the ambient
cohomology presheaf through the existing equivalence of open-set sites. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Normalizer
open CategoryTheory Limits TopologicalSpace Opposite Abelian
universe u
variable {X : TopCat.{u}} (U : Opens X)

private theorem overEquivalence_terminal :
    U.overEquivalence.functor.obj (Over.mk (𝟙 U)) = ⊤ := by
  ext x
  simp

/-- Under the actual open-site equivalence, global sections of the inverse
transport are global sections on the open subspace. -/
def openOverInverseSectionsIso :
    (U.sheafEquivOver (A := AddCommGrpCat.{u})).inverse ⋙
      (sheafSections ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}).obj
        (op (Over.mk (𝟙 U))) ≅
    (sheafSections (Opens.grothendieckTopology U) AddCommGrpCat.{u}).obj (op ⊤) :=
  NatIso.ofComponents
    (fun F => F.obj.mapIso (eqToIso (congrArg op (overEquivalence_terminal U))))
    (fun f => (f.hom.naturality _).symm)

/-- The open-site equivalence carries the actual constant integer sheaf to
the constant integer sheaf on the open subspace, via evaluation adjunctions. -/
def openOverConstantIso :
    constantSheaf ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} ⋙
      (U.sheafEquivOver (A := AddCommGrpCat.{u})).functor ≅
    constantSheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u} :=
  (((constantSheafAdj ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}
    Over.mkIdTerminal).comp U.sheafEquivOver.toAdjunction).ofNatIsoRight
      (openOverInverseSectionsIso U)).leftAdjointUniq
        (constantSheafAdj (Opens.grothendieckTopology U) AddCommGrpCat.{u} isTerminalTop)

private instance : (U.sheafEquivOver (A := AddCommGrpCat.{u})).functor.Additive :=
  Functor.additive_of_preserves_binary_products _
private instance : (U.sheafEquivOver (A := AddCommGrpCat.{u})).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Intrinsic cohomology on the slice site equals cohomology after transport
to the actual open subspace, in every degree. -/
def openOverCohomologyEquiv
    (F : Sheaf ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}) (n : ℕ) :
    F.H n ≃+ ((U.sheafEquivOver.functor).obj F).H n :=
  ((((extFunctor n).obj (op ((constantSheaf _ AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))))).mapIso (U.sheafEquivOver.unitIso.app F)).addCommGroupIsoToAddEquiv).trans
    (U.sheafEquivOver.toAdjunction.extEquiv.symm.trans
      ((((extFunctor n).mapIso
        (((openOverConstantIso U).app (AddCommGrpCat.of (ULift.{u} ℤ))).symm.op)).app
          (U.sheafEquivOver.functor.obj F)).addCommGroupIsoToAddEquiv))

set_option maxHeartbeats 800000 in
/-- The comparison through the open-site equivalence commutes with actual
sheaf morphisms. -/
theorem openOverCohomologyEquiv_naturality
    {F G : Sheaf ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}}
    (f : F ⟶ G) (n : ℕ) (x : F.H n) :
    openOverCohomologyEquiv U G n (Sheaf.H.map f n x) =
      Sheaf.H.map (U.sheafEquivOver.functor.map f) n
        (openOverCohomologyEquiv U F n x) := by
  change (Ext.mk₀ _).comp
    (U.sheafEquivOver.toAdjunction.extEquiv.symm
      ((x.comp (Ext.mk₀ f) (add_zero n)).comp
        (Ext.mk₀ (U.sheafEquivOver.unitIso.hom.app G)) (add_zero n))) (zero_add n) =
    ((Ext.mk₀ _).comp (U.sheafEquivOver.toAdjunction.extEquiv.symm
      (x.comp (Ext.mk₀ (U.sheafEquivOver.unitIso.hom.app F)) (add_zero n)))
        (zero_add n)).comp (Ext.mk₀ _) (add_zero n)
  have hn : f ≫ U.sheafEquivOver.unitIso.hom.app G =
      U.sheafEquivOver.unitIso.hom.app F ≫
        U.sheafEquivOver.inverse.map (U.sheafEquivOver.functor.map f) :=
    U.sheafEquivOver.unitIso.hom.naturality f
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hn,
    ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
    Adjunction.extEquiv_symm_naturality_right₀,
    Ext.comp_assoc_of_third_deg_zero]

/-- Evaluation of the ambient cohomology presheaf at an open U is the actual
cohomology of the restriction to the topological subspace U. -/
def openSheafCohomologyEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    F.H' n U ≃+ (U.sheafRestrict.obj F).H n :=
  (overSheafCohomologyEquiv (Opens.grothendieckTopology X) U F n).trans
    (openOverCohomologyEquiv U (F.over U) n)

/-- Restricting cohomology to the actual open subspace commutes with maps
of the original abelian sheaves. -/
theorem openSheafCohomologyEquiv_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ) (x : F.H' n U) :
    openSheafCohomologyEquiv U G n
        (((Sheaf.cohomologyPresheafFunctor _ n).map f).app (op U) x) =
      Sheaf.H.map (U.sheafRestrict.map f) n (openSheafCohomologyEquiv U F n x) := by
  change openOverCohomologyEquiv U (G.over U) n
    (overSheafCohomologyEquiv _ U G n _) = _
  rw [overSheafCohomologyEquiv_naturality, openOverCohomologyEquiv_naturality]
  rfl

end Normalizer
