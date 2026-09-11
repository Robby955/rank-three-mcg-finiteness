import Normalizer.SaturatedStalkQuotient
import Normalizer.GlobalSectionFrame

/-! A canonical cokernel comparison for actual scheme module sheaves.
The hypotheses are exactness and surjectivity on actual stalks; they must
be established separately in each geometric application. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry

universe u
variable {X : Scheme.{u}} {A B C : X.Modules}
  (f : A ⟶ B) (g : B ⟶ C) (hfg : f ≫ g = 0)

/-- The canonical comparison has the prescribed effect on actual stalk
elements represented through the actual cokernel projection. -/
theorem sheaf_cokernel_desc_stalk_comp (x : X) (b : B.presheaf.stalk x) :
    schemeModuleStalkMap (cokernel.desc f g hfg) x
      (schemeModuleStalkMap (cokernel.π f) x b) = schemeModuleStalkMap g x b := by
  obtain ⟨U, hxU, v, rfl⟩ := B.presheaf.exists_germ_eq b
  rw [schemeModuleStalkMap_germ, schemeModuleStalkMap_germ, schemeModuleStalkMap_germ]
  exact congrArg (fun q : B ⟶ C ↦ C.presheaf.germ U x hxU (q.app U v))
    (cokernel.π_desc f g hfg)

/-- Actual stalk exactness and surjectivity make the canonical cokernel
comparison bijective on that stalk. Monicity of the first map is unnecessary. -/
theorem sheaf_cokernel_desc_stalk_bijective (x : X)
    (hsurj : Function.Surjective (schemeModuleStalkMap g x))
    (hker : LinearMap.ker (schemeModuleStalkMap g x) =
      LinearMap.range (schemeModuleStalkMap f x)) :
    Function.Bijective (schemeModuleStalkMap (cokernel.desc f g hfg) x) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro z hz
    obtain ⟨b, rfl⟩ := sheaf_cokernel_stalk_surjective f x z
    have hb : schemeModuleStalkMap g x b = 0 :=
      (sheaf_cokernel_desc_stalk_comp f g hfg x b).symm.trans hz
    have hm : b ∈ LinearMap.range (schemeModuleStalkMap f x) := by
      rw [← hker]
      exact hb
    obtain ⟨a, rfl⟩ := hm
    exact sheaf_cokernel_stalk_comp f x a
  · intro c
    obtain ⟨b, rfl⟩ := hsurj c
    exact ⟨schemeModuleStalkMap (cokernel.π f) x b,
      sheaf_cokernel_desc_stalk_comp f g hfg x b⟩

/-- Exactness and surjectivity on every actual stalk identify the actual
sheaf cokernel with the proposed target by its canonical comparison map. -/
theorem sheaf_cokernel_desc_isIso
    (hsurj : ∀ x : X, Function.Surjective (schemeModuleStalkMap g x))
    (hker : ∀ x : X, LinearMap.ker (schemeModuleStalkMap g x) =
      LinearMap.range (schemeModuleStalkMap f x)) : IsIso (cokernel.desc f g hfg) :=
  schemeModule_isIso_of_stalk_bijective _
    (fun x ↦ sheaf_cokernel_desc_stalk_bijective f g hfg x (hsurj x) (hker x))

/-- The canonical actual sheaf-cokernel isomorphism produced from the
verified stalk conditions. -/
def sheafCokernelComparisonIso
    (hsurj : ∀ x : X, Function.Surjective (schemeModuleStalkMap g x))
    (hker : ∀ x : X, LinearMap.ker (schemeModuleStalkMap g x) =
      LinearMap.range (schemeModuleStalkMap f x)) : cokernel f ≅ C := by
  have := sheaf_cokernel_desc_isIso f g hfg hsurj hker
  exact asIso (cokernel.desc f g hfg)

/-- The comparison preserves the actual quotient map, rather than merely
exhibiting an unspecified isomorphism of the two sheaves. -/
theorem sheafCokernelComparisonIso_π_hom
    (hsurj : ∀ x : X, Function.Surjective (schemeModuleStalkMap g x))
    (hker : ∀ x : X, LinearMap.ker (schemeModuleStalkMap g x) =
      LinearMap.range (schemeModuleStalkMap f x)) :
    cokernel.π f ≫ (sheafCokernelComparisonIso f g hfg hsurj hker).hom = g :=
  cokernel.π_desc f g hfg

end Normalizer
