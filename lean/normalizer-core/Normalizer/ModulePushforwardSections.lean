import Normalizer.ProperGlobalCharacter

/-! Global sections of actual module-sheaf direct image over the actual base
field. Both scalar actions are induced by the specified scheme morphisms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u
variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (i : Y ⟶ X) (p : X ⟶ Spec (.of k))

/-- Base constants pull back along the actual scheme morphism, agreeing with
the constants induced by the composite structure morphism. -/
theorem schemeConstantMap_comp (a : k) :
    schemeConstantMap (i ≫ p) a = i.appTop (schemeConstantMap p a) := rfl

/-- Actual global sections of direct image agree linearly over the base field
with global sections on the source. No finiteness or integrality is needed. -/
def schemeModulePushforwardGlobalSectionsEquiv (F : Y.Modules) :
    let := schemeGlobalSectionsModuleOfMorphism p ((Scheme.Modules.pushforward i).obj F)
    let := schemeGlobalSectionsModuleOfMorphism (i ≫ p) F
    Γ((Scheme.Modules.pushforward i).obj F, ⊤) ≃ₗ[k] Γ(F, ⊤) := by
  let := schemeGlobalSectionsModuleOfMorphism p ((Scheme.Modules.pushforward i).obj F)
  let := schemeGlobalSectionsModuleOfMorphism (i ≫ p) F
  exact {
    __ := AddEquiv.refl Γ(F, ⊤)
    map_smul' := by intro a s; rfl }

/-- The global comparison is the actual identity on sections over the inverse
image of the top open, which is definitionally the source's top open. -/
theorem schemeModulePushforwardGlobalSectionsEquiv_apply (F : Y.Modules)
    (s : Γ((Scheme.Modules.pushforward i).obj F, ⊤)) :
    schemeModulePushforwardGlobalSectionsEquiv i p F s = s := rfl

/-- The global comparison preserves restrictions to every actual inverse-image
open; it does not replace the sheaf by an abstract isomorphic vector space. -/
theorem schemeModulePushforwardGlobalSectionsEquiv_restrict (F : Y.Modules)
    (U : X.Opens) (s : Γ((Scheme.Modules.pushforward i).obj F, ⊤)) :
    ((Scheme.Modules.pushforward i).obj F).presheaf.map
      (homOfLE (show U ≤ ⊤ from le_top)).op s =
      F.presheaf.map (homOfLE (show i ⁻¹ᵁ U ≤ ⊤ from le_top)).op
        (schemeModulePushforwardGlobalSectionsEquiv i p F s) := rfl

/-- The comparison commutes with actual module-sheaf maps. -/
theorem schemeModulePushforwardGlobalSectionsEquiv_naturality
    {F G : Y.Modules} (q : F ⟶ G) (s : Γ((Scheme.Modules.pushforward i).obj F, ⊤)) :
    schemeModulePushforwardGlobalSectionsEquiv i p G
      (((Scheme.Modules.pushforward i).map q).app ⊤ s) =
      q.app ⊤ (schemeModulePushforwardGlobalSectionsEquiv i p F s) := rfl

end Normalizer
