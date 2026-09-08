import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Topology.Sheaves.Sheaf

/-! The quotient by a sheaf kernel embeds into the target.

The quotient is the actual sheaf cokernel of the actual kernel inclusion.
Its sections need not be the quotient of sections. Evaluation preserves
monomorphisms, which suffices to transfer torsion-freeness from the target.

Torsion-freeness is asserted at a specified open, using regular scalars over
its section ring. No domain hypothesis is imposed on the empty open. This
file does not identify this sectionwise property with geometric, stalkwise
saturation on an integral scheme, and does not assert local freeness. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer

open CategoryTheory Limits Opposite

universe u

variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  {E H : SheafOfModules.{u} R} (f : E ⟶ H)

/-- The canonical map from the actual quotient sheaf `E / ker f` to `H`. -/
def kernelCokernelToTarget : cokernel (kernel.ι f) ⟶ H :=
  Abelian.factorThruCoimage f

/-- The canonical map composed with the quotient projection is the original
sheaf morphism. -/
theorem kernelCokernelToTarget_projection :
    cokernel.π (kernel.ι f) ≫ kernelCokernelToTarget f = f :=
  Abelian.coimage.fac f

/-- The quotient by a sheaf kernel is a subobject of the target sheaf. -/
theorem kernelCokernelToTarget_mono : Mono (kernelCokernelToTarget f) := by
  dsimp [kernelCokernelToTarget]
  infer_instance

/-- The canonical embedding of the actual quotient sheaf is injective on
sections of each open. This uses left exactness, not right exactness, of
evaluation. -/
theorem kernelCokernelToTarget_app_injective (V) :
    Function.Injective ((kernelCokernelToTarget f).val.app V) := by
  let := kernelCokernelToTarget_mono f
  rw [← ModuleCat.mono_iff_injective]
  exact inferInstanceAs
    (Mono ((SheafOfModules.evaluation R V).map (kernelCokernelToTarget f)))

/-- At an open where the target section module is torsion-free, the section
module of the actual quotient by the kernel is torsion-free as well. -/
theorem kernelCokernel_sections_isTorsionFree (V)
    [Module.IsTorsionFree (R.obj.obj V) (H.val.obj V)] :
    Module.IsTorsionFree (R.obj.obj V) ((cokernel (kernel.ι f)).val.obj V) :=
  (kernelCokernelToTarget_app_injective f V).moduleIsTorsionFree
    ((kernelCokernelToTarget f).val.app V) (fun _ _ => map_smul _ _ _)

/-- A regular scalar can be cancelled when testing membership in the kernel
of a sheaf map with torsion-free target sections. -/
theorem sheaf_kernel_regular_smul_iff (V)
    [Module.IsTorsionFree (R.obj.obj V) (H.val.obj V)]
    (r : R.obj.obj V) (hr : IsRegular r) (x : E.val.obj V) :
    f.val.app V (r • x) = 0 ↔ f.val.app V x = 0 := by
  rw [map_smul, hr.smul_eq_zero_iff_right]

/-- For a supplied actual kernel subsheaf, regular scalar cancellation is
the usual sectionwise saturation criterion. The geometric interpretation
requires a separate comparison with stalks on the scheme in question. -/
theorem subsheafKernel_regular_smul_mem_iff (N : E.Submodule)
    (hN : ∀ W (x : E.val.obj W), f.val.app W x = 0 ↔ x ∈ N.obj W)
    (V) [Module.IsTorsionFree (R.obj.obj V) (H.val.obj V)]
    (r : R.obj.obj V) (hr : IsRegular r) (x : E.val.obj V) :
    r • x ∈ N.obj V ↔ x ∈ N.obj V := by
  rw [← hN, ← hN, sheaf_kernel_regular_smul_iff f V r hr x]

end Normalizer
