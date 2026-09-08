import Normalizer.IntegralSheafTorsion
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! Actual affine sheaf stalks and the ordinary module free locus. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory AlgebraicGeometry

universe u
variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- The canonical algebra structure on the actual affine local ring. -/
@[instance_reducible]
def affineStalkAlgebra (x : PrimeSpectrum R) :
    Algebra R ((Spec R).presheaf.stalk x) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).presheaf.stalk x))

attribute [instance] affineStalkAlgebra

/-- Compatibility of the ordinary R-action on an affine module stalk with
the action of its actual local ring. -/
theorem affineStalk_isScalarTower (x : PrimeSpectrum R) :
    IsScalarTower R ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x) := by
  exact inferInstanceAs (IsScalarTower R
    ((structurePresheafInCommRingCat R).stalk x)
    ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x))

/-- The free locus of an ordinary module is exactly the free-stalk locus
of its actual associated sheaf, with the actual local-ring action. -/
theorem affineStalk_free_iff (x : PrimeSpectrum R) :
    Module.Free ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x) ↔
      x ∈ Module.freeLocus R M := by
  let := affineStalk_isScalarTower M x
  let : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) x.asIdeal :=
    inferInstanceAs (IsLocalization.AtPrime
      ((Spec.structureSheaf R).presheaf.stalk x) x.asIdeal)
  exact (Module.mem_freeLocus_of_isLocalization x
    ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x)
    (tilde.toStalk M x).hom).symm

/-- The actual stalk of an associated finite module is finite over its
actual local ring. -/
theorem affineStalk_finite [Module.Finite R M] (x : PrimeSpectrum R) :
    Module.Finite ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x) := by
  let := affineStalk_isScalarTower M x
  let : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) x.asIdeal :=
    inferInstanceAs (IsLocalization.AtPrime
      ((Spec.structureSheaf R).presheaf.stalk x) x.asIdeal)
  exact Module.Finite.of_isLocalizedModule x.asIdeal.primeCompl (tilde.toStalk M x).hom

/-- The free-stalk locus of the actual sheaf of a finitely presented module
is open. This uses the existing module free-locus theorem. -/
theorem affineStalk_freeLocus_isOpen [Module.FinitePresentation R M] :
    IsOpen {x : PrimeSpectrum R |
      Module.Free ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x)} := by
  convert Module.isOpen_freeLocus (R := R) (M := M) using 1
  ext x
  exact affineStalk_free_iff M x

/-- A free actual stalk of an associated finitely presented module spreads
to a free localization away from an element outside the prime, with the
same rank. The sheaf trivialization is constructed separately. -/
theorem affineStalk_exists_free_localization [Module.FinitePresentation R M]
    (x : PrimeSpectrum R)
    [Module.Free ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x)] :
    ∃ r : R, r ∉ x.asIdeal ∧
      Module.Free (Localization (.powers r)) (LocalizedModule.Away r M) ∧
      Module.finrank (Localization (.powers r)) (LocalizedModule.Away r M) =
        Module.finrank ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x) := by
  let := affineStalk_isScalarTower M x
  let : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) x.asIdeal :=
    inferInstanceAs (IsLocalization.AtPrime
      ((Spec.structureSheaf R).presheaf.stalk x) x.asIdeal)
  exact Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (tilde.toStalk M x).hom ((Spec R).presheaf.stalk x)

end Normalizer
