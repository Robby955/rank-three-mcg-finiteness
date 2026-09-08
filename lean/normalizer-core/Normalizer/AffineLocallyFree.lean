import Normalizer.AffineQuotient
import Normalizer.LocallyFreeTransport
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! Actual affine sheaf quotients over principal ideal domains.
The cokernel is the categorical sheaf cokernel and its trivialization is
constructed through the tilde functor. This does not assert that a smooth
curve has affine coordinate rings which are principal ideal domains. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry

universe u
variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- A basis of a module induces an actual free-sheaf trivialization on Spec R. -/
def affineFreeSheafIso [Module.Free R M] :
    tilde M ≅ SheafOfModules.free (Module.Free.ChooseBasisIndex R M) :=
  (tilde.functor R).mapIso (Module.Free.chooseBasis R M).repr.toModuleIso ≪≫
    tildeFinsupp _

/-- The sheaf attached to a free module is locally free in mathlib's actual
sheaf sense, witnessed by its genuine free-sheaf isomorphism. -/
theorem affineFreeSheaf_isLocallyFree [Module.Free R M] :
    (tilde M).IsLocallyFree :=
  isLocallyFree_of_iso (affineFreeSheafIso M).symm

/-- Finiteness of a free module gives finite local generating families
for its actual associated sheaf. -/
theorem affineFreeSheaf_isFiniteType [Module.Free R M] [Module.Finite R M] :
    (tilde M).IsFiniteType := by
  have := freeSheaf_isFiniteType (R := (Spec R).ringCatSheaf)
    (Module.Free.ChooseBasisIndex R M)
  exact isFiniteType_of_iso (affineFreeSheafIso M).symm

variable [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R M]
  (S : Submodule R M)
  (hS : ∀ (r : R), r ≠ 0 → ∀ (m : M), r • m ∈ S → m ∈ S)

include hS

/-- Over a PID, the actual affine sheaf quotient of a finite module by a
scalar-saturated submodule has a finite free-sheaf trivialization. -/
theorem affineSaturatedQuotient_trivialization :
    ∃ (ι : Type u) (_ : Finite ι),
      Nonempty (cokernel (tilde.map (ModuleCat.ofHom S.subtype)) ≅
        SheafOfModules.free ι) := by
  let := quotient_free_of_saturated S hS
  exact ⟨Module.Free.ChooseBasisIndex R (M ⧸ S), inferInstance,
    ⟨affineSubmoduleQuotientIso S ≪≫ affineFreeSheafIso (ModuleCat.of R (M ⧸ S))⟩⟩

/-- The actual affine sheaf cokernel is finite locally free. This is the
PID affine case, not the unproved smooth-curve local-to-global bridge. -/
theorem affineSaturatedQuotient_finiteLocallyFree :
    (cokernel (tilde.map (ModuleCat.ofHom S.subtype))).IsLocallyFree ∧
      (cokernel (tilde.map (ModuleCat.ofHom S.subtype))).IsFiniteType := by
  let := quotient_free_of_saturated S hS
  have := affineFreeSheaf_isLocallyFree (ModuleCat.of R (M ⧸ S))
  have := affineFreeSheaf_isFiniteType (ModuleCat.of R (M ⧸ S))
  exact ⟨isLocallyFree_of_iso (affineSubmoduleQuotientIso S).symm,
    isFiniteType_of_iso (affineSubmoduleQuotientIso S).symm⟩

end Normalizer
