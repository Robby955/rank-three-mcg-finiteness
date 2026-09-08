import Normalizer.LocallyFreeAssembly
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! Finite stalks and local freeness over actual principal ideal local rings.
The principal ideal and torsion-free conditions are explicit hypotheses;
their derivation from smooth-curve data is outside these theorems. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory AlgebraicGeometry
attribute [local instance] RingHomInvPair.of_ringEquiv

universe u

/-- A regular local domain of Krull dimension at most one is a principal
ideal ring. The field case is included. -/
theorem principalIdealRing_of_regularLocal_dim_le_one (R : Type u)
    [CommRing R] [IsDomain R] [IsRegularLocalRing R] (hdim : ringKrullDim R ≤ 1) :
    IsPrincipalIdealRing R := by
  apply ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 6 1).mp
  have hreg := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp
    (inferInstance : IsRegularLocalRing R)
  rw [← hreg] at hdim
  exact_mod_cast hdim

/-- A finite global presentation on an affine scheme makes each actual
module stalk finite over its actual local ring. -/
theorem affinePresentation_stalk_finite {R : CommRingCat.{u}}
    (E : (Spec R).Modules) (P : E.Presentation) [P.IsFinite] (x : PrimeSpectrum R) :
    Module.Finite ((Spec R).presheaf.stalk x) (E.presheaf.stalk x) := by
  let M := (moduleSpecΓFunctor (R := R)).obj E
  let : Module.FinitePresentation R M := affinePresentation_sections_finitePresentation E P
  let : IsIso E.fromTildeΓ := isIso_fromTildeΓ_of_presentation E P
  let e : tilde M ≅ E := asIso E.fromTildeΓ
  let : Module.Finite ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x) :=
    affineStalk_finite M x
  exact Module.Finite.equiv (schemeModuleStalkIso e x)

/-- A finitely presented actual scheme module sheaf has finite actual
stalks. Finiteness is transported through the actual affine restriction. -/
theorem sheaf_stalk_finite_of_finitePresentation {X : Scheme.{u}}
    (E : X.Modules) [E.IsFinitePresentation] (x : X) :
    Module.Finite (X.presheaf.stalk x) (E.presheaf.stalk x) := by
  obtain ⟨𝒰, h𝒰⟩ := exists_affineOpenCover_finitePresentation E
  obtain ⟨y, hy⟩ := 𝒰.covers x
  have hy' : 𝒰.f (𝒰.idx x) y = x := hy
  obtain ⟨P, hP⟩ := h𝒰 (𝒰.idx x)
  let := hP
  let := affinePresentation_stalk_finite (E.restrict (𝒰.f (𝒰.idx x))) P y
  have hf : Module.Finite (X.presheaf.stalk (𝒰.f (𝒰.idx x) y))
      (E.presheaf.stalk (𝒰.f (𝒰.idx x) y)) :=
    Module.Finite.of_surjective (restrictionStalkEquiv (𝒰.f (𝒰.idx x)) E y).toLinearMap
      (restrictionStalkEquiv (𝒰.f (𝒰.idx x)) E y).surjective
  exact Eq.mp (congrArg (fun z : X =>
    Module.Finite (X.presheaf.stalk z) (E.presheaf.stalk z)) hy') hf

/-- Over an integral scheme whose actual local rings are principal ideal
rings, a finitely presented sheaf with torsion-free actual stalks is locally
free. Finite type already follows from finite presentation. -/
theorem sheaf_isLocallyFree_of_torsionFree_stalks {X : Scheme.{u}} [IsIntegral X]
    (E : X.Modules) [E.IsFinitePresentation]
    (hpid : ∀ x : X, IsPrincipalIdealRing (X.presheaf.stalk x))
    (htf : ∀ x : X, Module.IsTorsionFree (X.presheaf.stalk x) (E.presheaf.stalk x)) :
    E.IsLocallyFree := by
  apply sheaf_isLocallyFree_of_free_stalks E
  intro x
  let := hpid x
  let := htf x
  let := sheaf_stalk_finite_of_finitePresentation E x
  exact Module.free_of_finite_type_torsion_free'

/-- The actual quotient by a sheaf kernel is locally free when it is
finitely presented, the scheme is integral with principal ideal local
rings, and the target has torsion-free actual stalks. -/
theorem kernelCokernel_isLocallyFree {X : Scheme.{u}} [IsIntegral X]
    {E H : X.Modules} (f : E ⟶ H)
    [(Limits.cokernel (Limits.kernel.ι f)).IsFinitePresentation]
    (hpid : ∀ x : X, IsPrincipalIdealRing (X.presheaf.stalk x))
    (hH : ∀ x : X, Module.IsTorsionFree (X.presheaf.stalk x) (H.presheaf.stalk x)) :
    (Limits.cokernel (Limits.kernel.ι f)).IsLocallyFree :=
  sheaf_isLocallyFree_of_torsionFree_stalks _ hpid
    (integralSheaf_kernelCokernel_stalk_isTorsionFree f hH)

/-- On an integral scheme with regular local rings of dimension at most
one, a finitely presented sheaf with torsion-free stalks is locally free.
Regularity and dimension are hypotheses on the actual local rings. -/
theorem sheaf_isLocallyFree_of_regular_stalks {X : Scheme.{u}} [IsIntegral X]
    (E : X.Modules) [E.IsFinitePresentation]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1)
    (htf : ∀ x : X, Module.IsTorsionFree (X.presheaf.stalk x) (E.presheaf.stalk x)) :
    E.IsLocallyFree := by
  apply sheaf_isLocallyFree_of_torsionFree_stalks E _ htf
  intro x
  let := hreg x
  exact principalIdealRing_of_regularLocal_dim_le_one _ (hdim x)

end Normalizer
