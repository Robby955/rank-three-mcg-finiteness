import Normalizer.ExteriorStalkComparison
import Normalizer.ExteriorNonzero

/-! Nonzeroness of the exterior product of specified actual global sections,
derived from independence of their actual generic germs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry
universe u

variable {X : Scheme.{u}} [IsIntegral X] (H : X.Modules) (n : ℕ)

/-- The exterior section of the specified sections has nonzero actual
generic germ when their actual generic germs are independent. For a rank-n
bundle, this is its specified determinant section. -/
theorem schemeExteriorGlobalSection_generic_ne_zero (s : Fin n → Γ(H, ⊤))
    (hs : LinearIndependent X.functionField
      (fun i ↦ H.presheaf.germ ⊤ (genericPoint X) (by trivial) (s i))) :
    (schemeExteriorSheaf H n).presheaf.germ ⊤ (genericPoint X) (by trivial)
      (schemeExteriorGlobalSection H n s) ≠ 0 := by
  intro hz
  have he := congrArg (schemeExteriorStalkComparison H n (genericPoint X)) hz
  change schemeExteriorStalkComparison H n (genericPoint X)
      ((schemeExteriorSheaf H n).presheaf.germ ⊤ (genericPoint X) (by trivial)
        (schemeExteriorPure H n ⊤ s)) = _ at he
  rw [schemeExteriorStalkComparison_germ_pure, map_zero] at he
  exact exteriorProduct_ne_zero_of_linearIndependent _ hs he

/-- Nonzeroness concerns the actual specified determinant section, rather
than an unspecified section of an isomorphic line bundle. -/
theorem schemeExteriorGlobalSection_ne_zero (s : Fin n → Γ(H, ⊤))
    (hs : LinearIndependent X.functionField
      (fun i ↦ H.presheaf.germ ⊤ (genericPoint X) (by trivial) (s i))) :
    schemeExteriorGlobalSection H n s ≠ 0 := by
  intro hz
  apply schemeExteriorGlobalSection_generic_ne_zero H n s hs
  rw [hz, map_zero]

end Normalizer
