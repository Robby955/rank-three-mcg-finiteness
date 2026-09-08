import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! Transport a kernel along a genuine isomorphism of its target while
preserving its canonical inclusion into the source. -/

noncomputable section

namespace Normalizer

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {A B D : C} (f : A ⟶ B) (e : B ≅ D)
  [HasKernel f] [HasKernel (f ≫ e.hom)]

/-- Changing the target by an isomorphism preserves the actual kernel. -/
def kernelTargetIso : kernel f ≅ kernel (f ≫ e.hom) :=
  kernel.mapIso f (f ≫ e.hom) (Iso.refl A) e (by simp)

/-- The forward transport leaves the underlying inclusion unchanged. -/
theorem kernelTargetIso_hom_ι :
    (kernelTargetIso f e).hom ≫ kernel.ι (f ≫ e.hom) = kernel.ι f := by
  simp [kernelTargetIso]

/-- The inverse transport also leaves the underlying inclusion unchanged. -/
theorem kernelTargetIso_inv_ι :
    (kernelTargetIso f e).inv ≫ kernel.ι f = kernel.ι (f ≫ e.hom) := by
  simp [kernelTargetIso]

end Normalizer
