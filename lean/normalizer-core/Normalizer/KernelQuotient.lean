import Mathlib.CategoryTheory.Abelian.Refinements

/-! Kernels after quotienting an object by a subobject of the kernel.

The construction takes place in an arbitrary abelian category. In particular,
its application to sheaves does not require surjectivity on sections. -/

noncomputable section

namespace Normalizer

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  {I E H : C} (i : I ⟶ E) (b : E ⟶ H) (hib : i ≫ b = 0)

/-- The canonical projection from the original kernel to the kernel of the
map induced on the actual cokernel. -/
def kernelQuotientProjection : kernel b ⟶ kernel (cokernel.desc i b hib) :=
  kernel.lift _ (kernel.ι b ≫ cokernel.π i) (by simp)

/-- The kernel projection has the expected underlying map into the quotient. -/
theorem kernelQuotientProjection_fac :
    kernelQuotientProjection i b hib ≫ kernel.ι (cokernel.desc i b hib) =
      kernel.ι b ≫ cokernel.π i := by
  simp [kernelQuotientProjection]

/-- Every section of the new kernel lifts after an epimorphic refinement.
Categorically, the canonical projection of kernels is an epimorphism. -/
theorem kernelQuotientProjection_epi : Epi (kernelQuotientProjection i b hib) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro T z
  obtain ⟨T', p, hp, x, hx⟩ := surjective_up_to_refinements_of_epi
    (cokernel.π i) (z ≫ kernel.ι (cokernel.desc i b hib))
  have hxb : x ≫ b = 0 := by
    have h := hx =≫ cokernel.desc i b hib
    simpa using h.symm
  refine ⟨T', p, hp, kernel.lift b x hxb, ?_⟩
  apply (cancel_mono (kernel.ι (cokernel.desc i b hib))).mp
  simpa [Category.assoc, kernelQuotientProjection] using hx

private theorem kernelQuotient_zero :
    kernel.lift b i hib ≫ kernelQuotientProjection i b hib = 0 := by
  apply (cancel_mono (kernel.ι (cokernel.desc i b hib))).mp
  simp [Category.assoc, kernelQuotientProjection]

private def kernelQuotient_kernel [Mono i] :
    IsLimit (KernelFork.ofι (kernel.lift b i hib) (kernelQuotient_zero i b hib)) := by
  have : Mono (kernel.lift b i hib) := mono_of_mono_fac (kernel.lift_ι b i hib)
  refine KernelFork.IsLimit.ofι' _ _ fun {T} x hx => ?_
  have hxq : (x ≫ kernel.ι b) ≫ cokernel.π i = 0 := by
    have h := hx =≫ kernel.ι (cokernel.desc i b hib)
    simpa [Category.assoc, kernelQuotientProjection] using h
  refine ⟨Abelian.monoLift i (x ≫ kernel.ι b) hxq, ?_⟩
  apply (cancel_mono (kernel.ι b)).mp
  simp [Category.assoc]

private def kernelQuotient_cokernel [Mono i] :
    IsColimit (CokernelCofork.ofπ (kernelQuotientProjection i b hib)
      (kernelQuotient_zero i b hib)) := by
  let : Epi (kernelQuotientProjection i b hib) := kernelQuotientProjection_epi i b hib
  exact Abelian.epiIsCokernelOfKernel _ (kernelQuotient_kernel i b hib)

/-- Quotienting the kernel by a monic subobject gives the kernel of the
induced quotient map. Both sides are actual categorical (co)kernels. -/
def kernelQuotientIso [Mono i] :
    cokernel (kernel.lift b i hib) ≅ kernel (cokernel.desc i b hib) :=
  (cokernelIsCokernel (kernel.lift b i hib)).coconePointUniqueUpToIso
    (kernelQuotient_cokernel i b hib)

/-- The comparison isomorphism is the one induced by the kernel projection. -/
theorem kernelQuotientIso_projection [Mono i] :
    cokernel.π (kernel.lift b i hib) ≫ (kernelQuotientIso i b hib).hom =
      kernelQuotientProjection i b hib := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (kernel.lift b i hib)) (kernelQuotient_cokernel i b hib)
    WalkingParallelPair.one

/-- The isomorphism identifies the two canonical maps to the ambient quotient. -/
theorem kernelQuotientIso_fac [Mono i] :
    cokernel.π (kernel.lift b i hib) ≫ (kernelQuotientIso i b hib).hom ≫
      kernel.ι (cokernel.desc i b hib) = kernel.ι b ≫ cokernel.π i := by
  rw [← Category.assoc, kernelQuotientIso_projection, kernelQuotientProjection_fac]

/-- On the quotient object, the comparison followed by the kernel inclusion
is precisely the cokernel descent of the original inclusion. -/
theorem kernelQuotientIso_hom_ι [Mono i] :
    (kernelQuotientIso i b hib).hom ≫ kernel.ι (cokernel.desc i b hib) =
      cokernel.desc (kernel.lift b i hib) (kernel.ι b ≫ cokernel.π i) (by simp) := by
  apply (cancel_epi (cokernel.π (kernel.lift b i hib))).mp
  rw [kernelQuotientIso_fac, cokernel.π_desc]

variable {N : C} (j : N ⟶ E) (hj : j ≫ b = 0)
  (hker : IsLimit (KernelFork.ofι j hj)) (a : I ⟶ N) (ha : a ≫ j = i)

private def suppliedKernelIso : N ≅ kernel b :=
  hker.conePointUniqueUpToIso (limit.isLimit _)

private theorem suppliedKernelIso_fac :
    (suppliedKernelIso b j hj hker).hom ≫ kernel.ι b = j := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp hker (limit.isLimit _)
    WalkingParallelPair.zero

include ha in
private theorem suppliedKernelIso_comm :
    a ≫ (suppliedKernelIso b j hj hker).hom =
      (Iso.refl I).hom ≫ kernel.lift b i hib := by
  apply (cancel_mono (kernel.ι b)).mp
  simp only [Category.assoc, suppliedKernelIso_fac, Iso.refl_hom, Category.id_comp,
    kernel.lift_ι, ha]

/-- The kernel-quotient comparison for any supplied kernel of the original map.
The compatibility `ha` identifies the given subobject with its inclusion in `E`. -/
def kernelQuotientIsoOfKernel [Mono i] :
    cokernel a ≅ kernel (cokernel.desc i b hib) :=
  cokernel.mapIso a (kernel.lift b i hib) (Iso.refl I)
    (suppliedKernelIso b j hj hker) (suppliedKernelIso_comm i b hib j hj hker a ha) ≪≫
      kernelQuotientIso i b hib

/-- The supplied-kernel comparison commutes with the actual quotient projection. -/
theorem kernelQuotientIsoOfKernel_fac [Mono i] :
    cokernel.π a ≫ (kernelQuotientIsoOfKernel i b hib j hj hker a ha).hom ≫
      kernel.ι (cokernel.desc i b hib) = j ≫ cokernel.π i := by
  simp only [kernelQuotientIsoOfKernel, Iso.trans_hom, cokernel.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc, cokernel.π_desc]
  simp only [Category.assoc, kernelQuotientIso_fac]
  rw [← Category.assoc, suppliedKernelIso_fac]

/-- The underlying map from the supplied kernel quotient is the descent of `j`. -/
theorem kernelQuotientIsoOfKernel_hom_ι [Mono i] :
    (kernelQuotientIsoOfKernel i b hib j hj hker a ha).hom ≫
      kernel.ι (cokernel.desc i b hib) =
      cokernel.desc a (j ≫ cokernel.π i) (by rw [← Category.assoc, ha]; simp) := by
  apply (cancel_epi (cokernel.π a)).mp
  rw [kernelQuotientIsoOfKernel_fac, cokernel.π_desc]

end Normalizer
