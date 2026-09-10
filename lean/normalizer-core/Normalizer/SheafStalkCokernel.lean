import Normalizer.SheafStalkMap
import Normalizer.SheafQuotientBracket
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.LinearAlgebra.Isomorphisms

/-! The stalk of the actual sheaf cokernel is the quotient of the stalks.
Local lifts and equality of germs supply the comparison; surjectivity on
sections of a fixed open is not required. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry Opposite

universe u
variable {X : Scheme.{u}} {A B : X.Modules}

/-- The projection to an actual sheaf cokernel is surjective on every stalk. -/
theorem schemeCokernelStalk_surjective (i : A ⟶ B) (x : X) :
    Function.Surjective (schemeModuleStalkMap (cokernel.π i) x) := by
  have h := sheaf_cokernel_locallySurjective i
  exact (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
    (cokernel.π i).mapPresheaf).mp h x

/-- For a monomorphism of actual module sheaves, the kernel of its cokernel
projection on a stalk is exactly the image of the original stalk map. -/
theorem schemeCokernelStalk_ker (i : A ⟶ B) [Mono i] (x : X) :
    LinearMap.ker (schemeModuleStalkMap (cokernel.π i) x) =
      LinearMap.range (schemeModuleStalkMap i x) := by
  ext b
  constructor
  · intro hb
    obtain ⟨U, hxU, s, rfl⟩ := B.presheaf.exists_germ_eq b
    have hz : (cokernel i).presheaf.germ U x hxU
        ((cokernel.π i).app U s) =
        (cokernel i).presheaf.germ U x hxU 0 := by
      simpa only [LinearMap.mem_ker, schemeModuleStalkMap_germ, map_zero] using hb
    obtain ⟨V, hxV, j, _, hj⟩ := (cokernel i).presheaf.germ_eq
      x hxU hxU ((cokernel.π i).app U s) 0 hz
    have hs : (cokernel.π i).app V (B.presheaf.map j.op s) = 0 := by
      have hn := PresheafOfModules.naturality_apply (cokernel.π i).val j.op s
      change (cokernel.π i).app V (B.presheaf.map j.op s) =
        (cokernel i).presheaf.map j.op ((cokernel.π i).app U s) at hn
      exact hn.trans (by simpa only [map_zero] using hj)
    obtain ⟨a, ha⟩ := sheaf_cokernel_section_exact i (op V)
      (B.presheaf.map j.op s) hs
    refine ⟨A.presheaf.germ V x hxV a, ?_⟩
    rw [schemeModuleStalkMap_germ]
    exact (congrArg (B.presheaf.germ V x hxV) ha).trans
      (B.presheaf.germ_res_apply j x hxV s)
  · rintro ⟨a, rfl⟩
    obtain ⟨U, hxU, s, rfl⟩ := A.presheaf.exists_germ_eq a
    change schemeModuleStalkMap (cokernel.π i) x
      (schemeModuleStalkMap i x (A.presheaf.germ U x hxU s)) = 0
    rw [schemeModuleStalkMap_germ, schemeModuleStalkMap_germ]
    have hz := congrArg (fun f : A ⟶ cokernel i => f.app U s) (cokernel.condition i)
    change (cokernel.π i).app U (i.app U s) = 0 at hz
    rw [hz, map_zero]

/-- Canonical comparison between the module quotient of actual stalks and
the stalk of the actual sheaf cokernel. -/
def schemeCokernelStalkEquiv (i : A ⟶ B) [Mono i] (x : X) :
    (B.presheaf.stalk x ⧸ LinearMap.range (schemeModuleStalkMap i x)) ≃ₗ[
      X.presheaf.stalk x] (cokernel i).presheaf.stalk x :=
  (Submodule.quotEquivOfEq _ _ (schemeCokernelStalk_ker i x).symm).trans
    ((schemeModuleStalkMap (cokernel.π i) x).quotKerEquivOfSurjective
      (schemeCokernelStalk_surjective i x))

/-- The comparison sends the class of an actual stalk element to its
image under the actual cokernel projection. -/
theorem schemeCokernelStalkEquiv_mk (i : A ⟶ B) [Mono i] (x : X)
    (b : B.presheaf.stalk x) :
    schemeCokernelStalkEquiv i x (Submodule.Quotient.mk b) =
      schemeModuleStalkMap (cokernel.π i) x b := by
  rfl

end Normalizer
