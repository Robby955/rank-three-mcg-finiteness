import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.LinearAlgebra.FreeModule.PID

/-! Actual affine sheaf cokernels and quotients by scalar-saturated submodules.

The scalar saturation hypothesis is stated explicitly. No assertion that smooth
curves have affine PID charts is made or used. -/

noncomputable section

namespace Normalizer

open CategoryTheory Limits AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}

/-- The actual affine sheaf cokernel is the tilde of the module cokernel. -/
def affineCokernelIso (i : M ⟶ N) :
    cokernel (tilde.map i) ≅ tilde (cokernel i) :=
  (PreservesCokernel.iso (tilde.functor R) i).symm

/-- The affine cokernel comparison carries the actual projection to tilde of
the module projection. -/
theorem affineCokernelIso_projection (i : M ⟶ N) :
    cokernel.π (tilde.map i) ≫ (affineCokernelIso i).hom = tilde.map (cokernel.π i) := by
  apply (Iso.comp_inv_eq (PreservesCokernel.iso (tilde.functor R) i)).mpr
  exact (PreservesCokernel.π_iso_hom (tilde.functor R) i).symm

/-- The quotient by a scalar-saturated submodule of a module over a domain is
torsion-free. The hypothesis is the usual elementwise saturation condition. -/
theorem quotient_isTorsionFree_of_saturated [IsDomain R] (S : Submodule R M)
    (hS : ∀ (r : R), r ≠ 0 → ∀ (m : M), r • m ∈ S → m ∈ S) :
    Module.IsTorsionFree R (M ⧸ S) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r q hq
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    obtain ⟨m, rfl⟩ := S.mkQ_surjective q
    apply (Submodule.Quotient.mk_eq_zero S).mpr
    apply hS r hr m
    exact (Submodule.Quotient.mk_eq_zero S).mp (by simpa using hq)

/-- Standard finite torsion-free module freeness applies to the actual quotient
over a PID, once scalar saturation has been checked. -/
theorem quotient_free_of_saturated [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Finite R M] (S : Submodule R M)
    (hS : ∀ (r : R), r ≠ 0 → ∀ (m : M), r • m ∈ S → m ∈ S) :
    Module.Free R (M ⧸ S) := by
  let := quotient_isTorsionFree_of_saturated S hS
  exact Module.free_of_finite_type_torsion_free'

/-- The actual affine sheaf cokernel of a submodule inclusion is its usual
module quotient under tilde. -/
def affineSubmoduleQuotientIso (S : Submodule R M) :
    cokernel (tilde.map (ModuleCat.ofHom S.subtype)) ≅ tilde (ModuleCat.of R (M ⧸ S)) :=
  affineCokernelIso (ModuleCat.ofHom S.subtype) ≪≫
    (tilde.functor R).mapIso (ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom S.subtype) ≪≫
      (Submodule.quotEquivOfEq _ S (by simp)).toModuleIso)

set_option backward.isDefEq.respectTransparency false in
/-- The affine submodule comparison identifies the actual cokernel projection
with the sheaf morphism induced by the ordinary quotient projection. -/
theorem affineSubmoduleQuotientIso_projection (S : Submodule R M) :
    cokernel.π (tilde.map (ModuleCat.ofHom S.subtype)) ≫
      (affineSubmoduleQuotientIso S).hom = tilde.map (ModuleCat.ofHom S.mkQ) := by
  simp only [affineSubmoduleQuotientIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, affineCokernelIso_projection]
  change (tilde.functor R).map _ ≫ (tilde.functor R).map _ = (tilde.functor R).map _
  rw [← Functor.map_comp]
  congr 1
  rw [← Category.assoc, ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]
  ext m
  simp

end Normalizer
