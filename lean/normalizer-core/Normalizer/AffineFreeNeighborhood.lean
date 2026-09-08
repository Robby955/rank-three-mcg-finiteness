import Normalizer.AffineLocallyFree
import Normalizer.AffineStalks
import Mathlib.RingTheory.Localization.Free

/-! Actual affine free-sheaf neighborhoods from free localized modules. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry Opposite

universe u
variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (r : R)

/-- The scheme map identifying the principal open with Spec of the localization. -/
def affineLocalizationMap : Spec (CommRingCat.of (Localization.Away r)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))

private instance : IsOpenImmersion (affineLocalizationMap r) := by
  dsimp [affineLocalizationMap]
  infer_instance

/-- The restriction of the actual associated sheaf to the principal affine chart. -/
def affineLocalizationSheaf : (Spec (CommRingCat.of (Localization.Away r))).Modules :=
  (tilde M).restrict (affineLocalizationMap r)

private def localizationSectionsAddIso :
    Γ(affineLocalizationSheaf M r, ⊤) ≅ Γ(tilde M, PrimeSpectrum.basicOpen r) :=
  (tilde M).restrictAppIso (affineLocalizationMap r) ⊤ ≪≫
    (tilde M).presheaf.mapIso (eqToIso (by
      simp [affineLocalizationMap, Scheme.Hom.image_top_eq_opensRange,
        Scheme.Hom.opensRange_localizationAway])).op

/-- The global sections on the actual localization chart, with its localized-ring action. -/
def affineLocalizationSections : ModuleCat (Localization.Away r) :=
  moduleSpecΓFunctor.obj (affineLocalizationSheaf M r)

private instance localizationSectionsModule : Module R (affineLocalizationSections M r) :=
  Module.compHom (affineLocalizationSections M r) (algebraMap R (Localization.Away r))

private instance localizationSectionsTower :
    IsScalarTower R (Localization.Away r) (affineLocalizationSections M r) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

private def localizationSectionsEquiv :
    (affineLocalizationSections M r) ≃ₗ[R] Γ(tilde M, PrimeSpectrum.basicOpen r) := by
  refine { __ := (localizationSectionsAddIso M r).addCommGroupIsoToAddEquiv, map_smul' := ?_ }
  intro a s
  change ((tilde M).presheaf.map _)
      (((tilde M).restrictAppIso (affineLocalizationMap r) ⊤).hom
        ((algebraMap R (Localization.Away r)) a • s)) = _
  have h := Scheme.Modules.restrictAppIso_smul_Spec (M := tilde M)
    (CommRingCat.ofHom (algebraMap R (Localization.Away r))) a s
  change ((tilde M).restrictAppIso (affineLocalizationMap r) ⊤).hom
    ((algebraMap R (Localization.Away r)) a • s) = _ at h
  rw [h]
  exact Scheme.Modules.map_smul_Spec _ _ _


/-- The original module maps canonically to the sections on the actual affine chart. -/
def affineLocalizationToSections : M →ₗ[R] affineLocalizationSections M r :=
  (localizationSectionsEquiv M r).symm.toLinearMap.comp
    (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom

private instance localizationToSections_isLocalized :
    IsLocalizedModule (Submonoid.powers r) (affineLocalizationToSections M r) := by
  unfold affineLocalizationToSections
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers r)
    (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom (localizationSectionsEquiv M r).symm

/-- Global sections on the actual restricted sheaf are the localized module,
with the actual localization-ring scalar action. -/
def affineLocalizationSectionsIso :
    ModuleCat.of (Localization.Away r) (LocalizedModule.Away r M) ≅
      affineLocalizationSections M r :=
  (LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers r) (Localization.Away r)
    (IsLocalizedModule.iso (Submonoid.powers r) (affineLocalizationToSections M r))).toModuleIso

private instance localizationSheaf_isQuasicoherent :
    (affineLocalizationSheaf M r).IsQuasicoherent := by
  dsimp [affineLocalizationSheaf]
  infer_instance

/-- Restricting the associated sheaf to the principal affine chart gives the
actual associated sheaf of the localized module. -/
def affineTildeRestrictionIso :
    affineLocalizationSheaf M r ≅
      tilde (ModuleCat.of (Localization.Away r) (LocalizedModule.Away r M)) :=
  (asIso (affineLocalizationSheaf M r).fromTildeΓ).symm ≪≫
    (tilde.functor (CommRingCat.of (Localization.Away r))).mapIso
      (affineLocalizationSectionsIso M r).symm


/-- The localization chart has exactly the expected principal-open image. -/
theorem affineLocalizationMap_opensRange :
    (affineLocalizationMap r).opensRange = PrimeSpectrum.basicOpen r :=
  Scheme.Hom.opensRange_localizationAway r

/-- A free localized module trivializes the actual restricted sheaf. -/
def affineLocalizationFreeSheafIso
    [Module.Free (Localization.Away r) (LocalizedModule.Away r M)] :
    affineLocalizationSheaf M r ≅
      SheafOfModules.free (Module.Free.ChooseBasisIndex (Localization.Away r)
        (LocalizedModule.Away r M)) :=
  affineTildeRestrictionIso M r ≪≫
    affineFreeSheafIso (R := CommRingCat.of (Localization.Away r))
      (ModuleCat.of (Localization.Away r) (LocalizedModule.Away r M))

/-- Finiteness of the original module gives a finite free-sheaf trivialization
on a nonempty localization chart whenever the localized module is free. -/
theorem affineLocalization_finiteFree_trivialization
    [Nontrivial (Localization.Away r)] [Module.Finite R M]
    [Module.Free (Localization.Away r) (LocalizedModule.Away r M)] :
    ∃ (ι : Type u) (_ : Finite ι),
      Nonempty (affineLocalizationSheaf M r ≅ SheafOfModules.free ι) := by
  exact ⟨Module.Free.ChooseBasisIndex (Localization.Away r) (LocalizedModule.Away r M),
    inferInstance, ⟨affineLocalizationFreeSheafIso M r⟩⟩

/-- A free actual stalk of an associated finitely presented module has a
principal affine neighborhood on which the actual sheaf is finite free. -/
theorem affineStalk_exists_finiteFree_neighborhood [Module.FinitePresentation R M]
    (x : PrimeSpectrum R)
    [Module.Free ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x)] :
    ∃ r : R, x ∈ (affineLocalizationMap r).opensRange ∧
      ∃ (ι : Type u) (_ : Finite ι),
        Nonempty (affineLocalizationSheaf M r ≅ SheafOfModules.free ι) := by
  obtain ⟨r, hr, hfree, _⟩ := affineStalk_exists_free_localization M x
  let := hfree
  let : Nontrivial (Localization.Away r) :=
    (show Localization.Away r →+* Localization.AtPrime x.asIdeal from
      IsLocalization.map (M := Submonoid.powers r) (T := x.asIdeal.primeCompl) _
        (RingHom.id R) (Submonoid.powers_le.mpr hr)).domain_nontrivial
  refine ⟨r, ?_, affineLocalization_finiteFree_trivialization M r⟩
  rw [affineLocalizationMap_opensRange]
  exact hr

end Normalizer
