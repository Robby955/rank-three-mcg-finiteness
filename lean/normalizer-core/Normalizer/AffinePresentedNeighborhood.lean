import Normalizer.AffineFreeNeighborhood
import Normalizer.SheafFinitePresentation
import Normalizer.SheafStalkMap

/-! Free neighborhoods for actual affine sheaves with finite presentations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory AlgebraicGeometry

universe u
variable {R : CommRingCat.{u}} (E : (Spec R).Modules)

/-- An actual finite global sheaf presentation and a free actual stalk give
a principal affine neighborhood with a genuine finite free-sheaf trivialization. -/
theorem affinePresentation_exists_finiteFree_neighborhood
    (P : E.Presentation) [P.IsFinite] (x : PrimeSpectrum R)
    [Module.Free ((Spec R).presheaf.stalk x) (E.presheaf.stalk x)] :
    ∃ r : R, x ∈ (affineLocalizationMap r).opensRange ∧
      ∃ (ι : Type u) (_ : Finite ι),
        Nonempty (E.restrict (affineLocalizationMap r) ≅ SheafOfModules.free ι) := by
  let M := (moduleSpecΓFunctor (R := R)).obj E
  let : Module.FinitePresentation R M := affinePresentation_sections_finitePresentation E P
  let : IsIso E.fromTildeΓ := isIso_fromTildeΓ_of_presentation E P
  let e : tilde M ≅ E := asIso E.fromTildeΓ
  let : Module.Free ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x) :=
    Module.Free.of_equiv (schemeModuleStalkIso e.symm x)
  obtain ⟨r, hr, ι, hι, ⟨eFree⟩⟩ := affineStalk_exists_finiteFree_neighborhood M x
  exact ⟨r, hr, ι, hι, ⟨(Scheme.Modules.restrictFunctor (affineLocalizationMap r)).mapIso
    e.symm ≪≫ eFree⟩⟩

end Normalizer
