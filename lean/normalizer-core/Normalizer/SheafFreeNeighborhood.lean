import Normalizer.AffinePresentedNeighborhood
import Normalizer.RestrictionStalks

/-! Actual finite free neighborhoods for finitely presented module sheaves.

A free stalk is spread to a finite free sheaf on an affine open immersion
whose image contains the specified point. The sheaf finite-presentation
hypothesis is mathlib's local presentation property, not a chosen affine
module presentation or a local trivialization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer

open CategoryTheory AlgebraicGeometry

universe u

/-- For an actual finitely presented module sheaf on any scheme, a free
stalk has a genuine affine neighborhood carrying a finite free-sheaf
trivialization. The neighborhood and its inclusion are constructed. -/
theorem sheafStalk_exists_finiteFree_neighborhood {X : Scheme.{u}}
    (E : X.Modules) [E.IsFinitePresentation] (x : X)
    [Module.Free (X.presheaf.stalk x) (E.presheaf.stalk x)] :
    ∃ (S : CommRingCat.{u}) (f : Spec S ⟶ X) (hf : IsOpenImmersion f),
      letI := hf
      x ∈ f.opensRange ∧ ∃ (ι : Type u) (_ : Finite ι),
        Nonempty (E.restrict f ≅ SheafOfModules.free ι) := by
  obtain ⟨𝒰, h𝒰⟩ := exists_affineOpenCover_finitePresentation E
  obtain ⟨y, hy⟩ := 𝒰.covers x
  have hy' : 𝒰.f (𝒰.idx x) y = x := hy
  obtain ⟨P, hP⟩ := h𝒰 (𝒰.idx x)
  let := hP
  let : Module.Free (X.presheaf.stalk (𝒰.f (𝒰.idx x) y))
      (E.presheaf.stalk (𝒰.f (𝒰.idx x) y)) := by
    exact Eq.mpr (congrArg (fun z : X =>
      Module.Free (X.presheaf.stalk z) (E.presheaf.stalk z)) hy') inferInstance
  let := restrictionStalk_free (𝒰.f (𝒰.idx x)) E y
  obtain ⟨r, hr, ι, hι, ⟨eFree⟩⟩ :=
    affinePresentation_exists_finiteFree_neighborhood (E.restrict (𝒰.f (𝒰.idx x))) P y
  refine ⟨CommRingCat.of (Localization.Away r),
    affineLocalizationMap r ≫ 𝒰.f (𝒰.idx x), inferInstance, ?_, ι, hι, ⟨?_⟩⟩
  · obtain ⟨z, hz⟩ := hr
    exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, hy']⟩
  · exact (Scheme.Modules.restrictFunctorComp
      (affineLocalizationMap r) (𝒰.f (𝒰.idx x))).app E ≪≫ eFree

end Normalizer
