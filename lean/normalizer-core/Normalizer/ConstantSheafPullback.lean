import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! The actual inverse image of a constant abelian sheaf is constant.
The comparison is obtained from the two adjunctions with global sections. -/

noncomputable section

namespace Normalizer
open CategoryTheory Limits TopologicalSpace Opposite

universe u
variable {X Y : TopCat.{u}}

/-- Global sections of an actual direct image are the original global sections. -/
def abelianSheafPushforwardSectionsIso (f : X ⟶ Y) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
      (sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj (op ⊤) ≅
    (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤) :=
  Iso.refl _

/-- The actual pullback of constant abelian sheaves, naturally in their values. -/
def abelianSheafPullbackConstantIso (f : X ⟶ Y) :
    constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⋙
      TopCat.Sheaf.pullback AddCommGrpCat.{u} f ≅
    constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    isTerminalTop).comp (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)).ofNatIsoRight (abelianSheafPushforwardSectionsIso f)).leftAdjointUniq
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop)

/-- The constant-sheaf comparison agrees with the actual global-section
adjunction, rather than choosing an arbitrary isomorphism of constant sheaves. -/
theorem abelianSheafPullbackConstant_homEquiv (f : X ⟶ Y)
    (A : AddCommGrpCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj
      ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj A) ⟶ F) :
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).homEquiv A F ((abelianSheafPullbackConstantIso f).inv.app A ≫ a) =
    (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u} isTerminalTop).homEquiv A ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv _ F a) := by
  let adj1 := (((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    isTerminalTop).comp (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)).ofNatIsoRight (abelianSheafPushforwardSectionsIso f))
  let adj2 := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop
  change adj2.homEquiv _ _ ((adj1.leftAdjointUniq adj2).inv.app A ≫ a) =
    adj1.homEquiv _ _ a
  let c := adj1.leftAdjointUniq adj2
  calc
    adj2.homEquiv _ _ (c.inv.app A ≫ a) =
        adj2.unit.app A ≫ _ := rfl
    _ = adj1.homEquiv _ _ (c.hom.app A) ≫ _ :=
      congrArg (fun z => z ≫ _) (adj1.homEquiv_leftAdjointUniq_hom_app adj2 A).symm
    _ = adj1.homEquiv _ _ (c.hom.app A ≫ (c.inv.app A ≫ a)) :=
      (adj1.homEquiv_naturality_right _ _).symm
    _ = adj1.homEquiv _ _ a := congrArg _ (c.hom_inv_id_app_assoc A a)

end Normalizer
