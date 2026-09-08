import Normalizer.NormalizerKernel
import Normalizer.LineSheafTensor
import Normalizer.KernelTargetIso

/-! The normalizer kernel with the manuscript's actual tensor target.
The tensor-Hom comparison is proved from a cover of genuine rank-one
trivializations, and the kernel map agrees with the original inclusion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits Opposite TopologicalSpace

universe u
variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  (E : SheafOfModules.{u} R) (I : E.Submodule)
  (action : ∀ V, E.val.obj V → E.val.obj V →ₗ[R.obj.obj V] E.val.obj V)
  (action_res : ∀ {V W} (f : V ⟶ W) (m x : E.val.obj V),
    E.val.map f (action V m x) = action W (E.val.map f m) (E.val.map f x))
  (skew : ∀ V (x y : E.val.obj V), action V y x = -action V x y)
  (ring_comm : ∀ V (a b : R.obj.obj V), a * b = b * a)
  (habelian : ∀ V (x m : E.val.obj V), x ∈ I.obj V → m ∈ I.obj V → action V m x = 0)
  {ι : Type u} (U : ι → Opens X) (hcover : iSup U = ⊤)
  (triv : ∀ i, (SheafOfModules.unit R).over (U i) ≅ I.toSheafOfModules.over (U i))

/-- Bracket with the line on E/I, with the actual tensor target G tensor I-dual. -/
def normalizerTensorBracketMap :
    ambientQuotientSheaf E I ⟶
      moduleTensorSheaf (ambientQuotientSheaf E I)
        (moduleHomSheaf I.toSheafOfModules (SheafOfModules.unit R) ring_comm) ring_comm :=
  ambientQuotientBracketMap E I action action_res skew ring_comm habelian ≫
    (lineSheafTensorIso I.toSheafOfModules (ambientQuotientSheaf E I)
      ring_comm U hcover triv).inv

/-- Canonical tensor evaluation recovers the actual bracket-induced Hom map. -/
theorem normalizerTensorBracketMap_evaluation :
    normalizerTensorBracketMap E I action action_res skew ring_comm habelian U hcover triv ≫
      (lineSheafTensorIso I.toSheafOfModules (ambientQuotientSheaf E I)
        ring_comm U hcover triv).hom =
      ambientQuotientBracketMap E I action action_res skew ring_comm habelian := by
  simp only [normalizerTensorBracketMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Before quotienting, the tensor-valued map is the original bracket map
transported through the proved tensor-Hom isomorphism. -/
theorem normalizerTensorBracketMap_projection :
    ambientQuotientProjection E I ≫
      normalizerTensorBracketMap E I action action_res skew ring_comm habelian U hcover triv =
      normalizerBracketMap E I action action_res skew ring_comm ≫
        (lineSheafTensorIso I.toSheafOfModules (ambientQuotientSheaf E I)
          ring_comm U hcover triv).inv := by
  rw [normalizerTensorBracketMap, ← Category.assoc, ambientQuotientBracketMap_projection]

/-- Contracting the tensor-valued bracket with a local line section gives
the projected commutator, including its original sign. -/
theorem normalizerTensorBracketMap_apply (V W : Opens X) (h : W ≤ V)
    (x : E.val.obj (op V)) (m : I.toSheafOfModules.val.obj (op W)) :
    moduleHomEval I.toSheafOfModules (ambientQuotientSheaf E I) ring_comm V W h
      ((lineSheafTensorIso I.toSheafOfModules (ambientQuotientSheaf E I)
        ring_comm U hcover triv).hom.val.app (op V)
        ((normalizerTensorBracketMap E I action action_res skew ring_comm habelian
          U hcover triv).val.app (op V)
          ((ambientQuotientProjection E I).val.app (op V) x))) m =
      (ambientQuotientProjection E I).val.app (op W)
        (action (op W) m.val (E.val.map (homOfLE h).op x)) := by
  have hp := congrArg (fun f => f.val.app (op V)
    ((ambientQuotientProjection E I).val.app (op V) x))
    (normalizerTensorBracketMap_evaluation E I action action_res skew ring_comm habelian
      U hcover triv)
  change (lineSheafTensorIso I.toSheafOfModules (ambientQuotientSheaf E I)
      ring_comm U hcover triv).hom.val.app (op V)
      ((normalizerTensorBracketMap E I action action_res skew ring_comm habelian
        U hcover triv).val.app (op V)
        ((ambientQuotientProjection E I).val.app (op V) x)) = _ at hp
  rw [hp]
  exact ambientQuotientBracketMap_apply E I action action_res skew ring_comm habelian V W h x m

/-- The actual normalizer quotient is the kernel of the tensor-valued
bracket map. Local trivializations supply the target comparison. -/
def normalizerTensorQuotientKernelIso :
    normalizerQuotientSheaf E I action action_res habelian ≅
      kernel (normalizerTensorBracketMap E I action action_res skew ring_comm habelian
        U hcover triv) :=
  normalizerQuotientKernelIso E I action action_res skew ring_comm habelian ≪≫
    kernelTargetIso
      (ambientQuotientBracketMap E I action action_res skew ring_comm habelian)
      (lineSheafTensorIso I.toSheafOfModules (ambientQuotientSheaf E I)
        ring_comm U hcover triv).symm

/-- The tensor-kernel isomorphism followed by the kernel inclusion is the
canonical normalizer-quotient inclusion into G. -/
theorem normalizerTensorQuotientKernelIso_hom_ι :
    (normalizerTensorQuotientKernelIso E I action action_res skew ring_comm habelian
      U hcover triv).hom ≫
        kernel.ι (normalizerTensorBracketMap E I action action_res skew ring_comm habelian
          U hcover triv) =
      normalizerQuotientToAmbient E I action action_res habelian := by
  rw [normalizerTensorQuotientKernelIso, Iso.trans_hom, Category.assoc]
  exact (congrArg
    (fun f => (normalizerQuotientKernelIso E I action action_res skew ring_comm habelian).hom ≫ f)
    (kernelTargetIso_hom_ι
      (ambientQuotientBracketMap E I action action_res skew ring_comm habelian)
      (lineSheafTensorIso I.toSheafOfModules (ambientQuotientSheaf E I)
        ring_comm U hcover triv).symm)).trans
    (normalizerQuotientKernelIso_hom_ι E I action action_res skew ring_comm habelian)

/-- The tensor-kernel identification commutes with the original normalizer
inclusion and the ambient cokernel projection. -/
theorem normalizerTensorQuotientKernelIso_projection :
    cokernel.π (normalizerLineInclusion E I action action_res habelian) ≫
      (normalizerTensorQuotientKernelIso E I action action_res skew ring_comm habelian
        U hcover triv).hom ≫
        kernel.ι (normalizerTensorBracketMap E I action action_res skew ring_comm habelian
          U hcover triv) =
      (normalizerSubsheaf E I action action_res).ι ≫ ambientQuotientProjection E I := by
  rw [normalizerTensorQuotientKernelIso_hom_ι, normalizerQuotientToAmbient_projection]

end Normalizer
