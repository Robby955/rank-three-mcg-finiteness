import Normalizer.NormalizerSheaf
import Normalizer.SheafOperationDescent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! Local representatives of the actual sheaf cokernel.
Evaluation preserves kernels, so the kernel of a sheaf-quotient projection
on every open is exactly the image of the original subsheaf on that open.
This assertion does not require surjectivity on sections. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}

/-- A monomorphism of actual module sheaves remains the kernel of its
sheaf-cokernel projection after evaluation on any open. -/
theorem sheaf_cokernel_section_exact
    {A B : SheafOfModules.{u} R} (i : A ⟶ B) [Mono i] (V)
    (x : B.val.obj V) (hx : (cokernel.π i).val.app V x = 0) :
    ∃ a : A.val.obj V, i.val.app V a = x := by
  have hm : Mono (ShortComplex.cokernelSequence i).f := inferInstanceAs (Mono i)
  have he := (ShortComplex.cokernelSequence_exact i).map_of_mono_of_preservesKernel
    (SheafOfModules.evaluation R V) hm inferInstance
  exact (ShortComplex.moduleCat_exact_iff _).mp he x hx

private abbrev moduleSheafify := PresheafOfModules.sheafification (𝟙 R.obj)
private abbrev moduleCounit (A : SheafOfModules.{u} R) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app A

private def sheafifiedProjection {A B : SheafOfModules.{u} R} (i : A ⟶ B) :
    B ⟶ moduleSheafify.obj (cokernel i.val) :=
  inv (moduleCounit B) ≫ moduleSheafify.map (cokernel.π i.val)

private theorem sheafifiedProjection_zero {A B : SheafOfModules.{u} R} (i : A ⟶ B) :
    i ≫ sheafifiedProjection i = 0 := by
  have hn := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.naturality i
  change moduleSheafify.map i.val ≫ moduleCounit B = moduleCounit A ≫ i at hn
  have hi : i ≫ inv (moduleCounit B) =
      inv (moduleCounit A) ≫ moduleSheafify.map i.val := by
    apply (cancel_epi (moduleCounit A)).mp
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    rw [← hn]
    simp [Category.assoc]
  dsimp only [sheafifiedProjection]
  rw [← Category.assoc, hi, Category.assoc, ← Functor.map_comp, cokernel.condition,
    Functor.map_zero, comp_zero]

private def sheafifiedCokernel (A B : SheafOfModules.{u} R) (i : A ⟶ B) :
    CokernelCofork i := CokernelCofork.ofπ (sheafifiedProjection i) (sheafifiedProjection_zero i)

private def sheafifiedCokernel_isColimit {A B : SheafOfModules.{u} R} (i : A ⟶ B) :
    IsColimit (sheafifiedCokernel A B i) := by
  let hc := isColimitOfHasCokernelOfPreservesColimit moduleSheafify i.val
  apply IsCokernel.ofIso (moduleSheafify.map i.val) hc (sheafifiedCokernel A B i)
    (asIso (moduleCounit A)) (asIso (moduleCounit B)) (Iso.refl _)
  · exact ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.naturality i).symm
  · simp [sheafifiedCokernel, sheafifiedProjection]

/-- The actual sheaf-cokernel projection is locally surjective. The proof
compares it to sheafification of the pointwise presheaf cokernel; it does
not assert surjectivity on sections of a fixed open. -/
theorem sheaf_cokernel_locallySurjective {A B : SheafOfModules.{u} R} (i : A ⟶ B) :
    Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map (cokernel.π i)) := by
  let L := moduleSheafify (R := R)
  let T := SheafOfModules.toSheaf R
  let e := (sheafifiedCokernel_isColimit i).coconePointUniqueUpToIso (cokernelIsCokernel i)
  have hf := IsColimit.comp_coconePointUniqueUpToIso_hom
    (sheafifiedCokernel_isColimit i) (cokernelIsCokernel i) WalkingParallelPair.one
  change sheafifiedProjection i ≫ e.hom = cokernel.π i at hf
  have hep : Epi (T.map (L.map (cokernel.π i.val))) := by
    change Epi ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf R.obj).map (cokernel.π i.val)))
    let : Epi ((PresheafOfModules.toPresheaf R.obj).map (cokernel.π i.val)) :=
      preserves_epi_of_preservesColimit (PresheafOfModules.toPresheaf R.obj) (cokernel.π i.val)
    exact preserves_epi_of_preservesColimit
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat)
      ((PresheafOfModules.toPresheaf R.obj).map (cokernel.π i.val))
  have hl : Sheaf.IsLocallySurjective (T.map (L.map (cokernel.π i.val))) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).mpr hep
  rw [← hf, Functor.map_comp]
  dsimp only [sheafifiedProjection]
  rw [Functor.map_comp]
  infer_instance

variable (E : SheafOfModules.{u} R) (I : E.Submodule)
  (action : ∀ V, E.val.obj V → E.val.obj V →ₗ[R.obj.obj V] E.val.obj V)
  (action_res : ∀ {V W} (f : V ⟶ W) (m x : E.val.obj V),
    E.val.map f (action V m x) = action W (E.val.map f m) (E.val.map f x))
  (habelian : ∀ V (x m : E.val.obj V), x ∈ I.obj V → m ∈ I.obj V →
    action V m x = 0)

/-- The constructed line inclusion is monic as a morphism of actual sheaves. -/
theorem normalizerLineInclusion_mono :
    Mono (normalizerLineInclusion E I action action_res habelian) := by
  apply (SheafOfModules.forget R).mono_of_mono_map
  change Mono (PresheafOfModules.Submodule.homOfLE
    (abelian_subsheaf_le_normalizer E I action action_res habelian))
  infer_instance

/-- A normalizer section maps to zero in the actual sheaf quotient exactly
when it lies in the line subsheaf on that same open. -/
theorem normalizerQuotient_zero_iff (V)
    (x : (normalizerSubsheaf E I action action_res).toSheafOfModules.val.obj V) :
    (cokernel.π (normalizerLineInclusion E I action action_res habelian)).val.app V x = 0 ↔
      x.val ∈ I.obj V := by
  let i := normalizerLineInclusion E I action action_res habelian
  let : Mono i := normalizerLineInclusion_mono E I action action_res habelian
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := sheaf_cokernel_section_exact i V x hx
    have hv := congrArg (fun y => y.val) ha
    exact hv ▸ a.property
  · intro hx
    have hz := congrArg (fun f => f.val.app V (⟨x.val, hx⟩ : I.toSheafOfModules.val.obj V))
      (cokernel.condition i)
    exact hz

/-- Equality of two local representatives in the actual quotient is
measured by their difference in the line subsheaf. -/
theorem normalizerQuotient_eq_iff (V)
    (x y : (normalizerSubsheaf E I action action_res).toSheafOfModules.val.obj V) :
    (cokernel.π (normalizerLineInclusion E I action action_res habelian)).val.app V x =
      (cokernel.π (normalizerLineInclusion E I action action_res habelian)).val.app V y ↔
      x.val - y.val ∈ I.obj V := by
  rw [← sub_eq_zero, ← map_sub]
  exact normalizerQuotient_zero_iff E I action action_res habelian V (x - y)

variable
  (jacobi : ∀ V (x y m : E.val.obj V),
    action V m (action V y x) =
      action V (action V m y) x - action V (action V m x) y)
  (skew : ∀ V (x y : E.val.obj V), action V y x = -action V x y)

/-- The ambient bracket restricted to the actual normalizer subsheaf. -/
def normalizerSectionBracket (V)
    (x y : (normalizerSubsheaf E I action action_res).toSheafOfModules.val.obj V) :
    (normalizerSubsheaf E I action action_res).toSheafOfModules.val.obj V :=
  ⟨action V y.val x.val,
    normalizerSubsheaf_bracket E I action action_res jacobi V _ _ x.property y.property⟩

/-- Brackets of normalizer sections commute with actual restrictions. -/
theorem normalizerSectionBracket_restrict {V W} (f : V ⟶ W)
    (x y : (normalizerSubsheaf E I action action_res).toSheafOfModules.val.obj V) :
    (normalizerSubsheaf E I action action_res).toSheafOfModules.val.map f
      (normalizerSectionBracket E I action action_res jacobi V x y) =
    normalizerSectionBracket E I action action_res jacobi W
      ((normalizerSubsheaf E I action action_res).toSheafOfModules.val.map f x)
      ((normalizerSubsheaf E I action action_res).toSheafOfModules.val.map f y) := by
  apply Subtype.ext
  exact action_res f y.val x.val

include skew in
/-- The projected bracket is independent of representatives in the actual
sheaf quotient, including on opens where its projection is not surjective. -/
theorem normalizerQuotient_bracket_independent (V)
    (x x' y y' : (normalizerSubsheaf E I action action_res).toSheafOfModules.val.obj V)
    (hx : (cokernel.π (normalizerLineInclusion E I action action_res habelian)).val.app V x =
      (cokernel.π (normalizerLineInclusion E I action action_res habelian)).val.app V x')
    (hy : (cokernel.π (normalizerLineInclusion E I action action_res habelian)).val.app V y =
      (cokernel.π (normalizerLineInclusion E I action action_res habelian)).val.app V y') :
    (cokernel.π (normalizerLineInclusion E I action action_res habelian)).val.app V
      (normalizerSectionBracket E I action action_res jacobi V x y) =
    (cokernel.π (normalizerLineInclusion E I action action_res habelian)).val.app V
      (normalizerSectionBracket E I action action_res jacobi V x' y') := by
  apply (normalizerQuotient_eq_iff E I action action_res habelian V _ _).mpr
  have hxI := (normalizerQuotient_eq_iff E I action action_res habelian V x x').mp hx
  have hyI := (normalizerQuotient_eq_iff E I action action_res habelian V y y').mp hy
  have h₁ := (I.obj V).neg_mem
    (normalizerSubsheaf_action E I action action_res V y.val _ y.property hxI)
  have h₂ := normalizerSubsheaf_action E I action action_res V x'.val _ x'.property hyI
  change action V y.val x.val - action V y'.val x'.val ∈ I.obj V
  have hs : action V (y.val - y'.val) x'.val =
      action V y.val x'.val - action V y'.val x'.val := by
    rw [skew, map_sub, skew V y.val x'.val, skew V y'.val x'.val]
    abel
  have ht : -action V (x.val - x'.val) y.val =
      action V y.val x.val - action V y.val x'.val := by
    rw [← skew, map_sub]
  rw [ht] at h₁
  rw [hs] at h₂
  convert (I.obj V).add_mem h₁ h₂ using 1
  abel

private abbrev quotientProjection :=
  cokernel.π (normalizerLineInclusion E I action action_res habelian)

private def projectedBracket (V : Opens X)
    (x y : (normalizerSubsheaf E I action action_res).toSheafOfModules.val.obj (op V)) :=
  (quotientProjection E I action action_res habelian).val.app (op V)
    (normalizerSectionBracket E I action action_res jacobi (op V) x y)

private theorem projectedBracket_restrict (V W : Opens X) (h : V ≤ W)
    (x y : (normalizerSubsheaf E I action action_res).toSheafOfModules.val.obj (op W)) :
    (normalizerQuotientSheaf E I action action_res habelian).val.map (homOfLE h).op
      (projectedBracket E I action action_res habelian jacobi W x y) =
    projectedBracket E I action action_res habelian jacobi V
      ((normalizerSubsheaf E I action action_res).toSheafOfModules.val.map (homOfLE h).op x)
      ((normalizerSubsheaf E I action action_res).toSheafOfModules.val.map (homOfLE h).op y) := by
  exact (PresheafOfModules.naturality_apply
    (quotientProjection E I action action_res habelian).val (homOfLE h).op _).symm.trans
      (congrArg ((quotientProjection E I action action_res habelian).val.app (op V))
        (normalizerSectionBracket_restrict E I action action_res jacobi (homOfLE h).op x y))

/-- The bracket on arbitrary sections of the actual sheaf quotient,
constructed by gluing projected brackets of local normalizer lifts. -/
def normalizerQuotientBracket (V : Opens X)
    (x y : (normalizerQuotientSheaf E I action action_res habelian).val.obj (op V)) :
    (normalizerQuotientSheaf E I action action_res habelian).val.obj (op V) :=
  descendSheafOperation (quotientProjection E I action action_res habelian)
    (sheaf_cokernel_locallySurjective _) (projectedBracket E I action action_res habelian jacobi)
    (projectedBracket_restrict E I action action_res habelian jacobi)
    (fun V => normalizerQuotient_bracket_independent E I action action_res habelian
      jacobi skew (op V)) V x y

/-- The quotient projection preserves the constructed bracket. -/
theorem normalizerQuotientBracket_projection (V : Opens X)
    (x y : (normalizerSubsheaf E I action action_res).toSheafOfModules.val.obj (op V)) :
    normalizerQuotientBracket E I action action_res habelian jacobi skew V
      ((quotientProjection E I action action_res habelian).val.app (op V) x)
      ((quotientProjection E I action action_res habelian).val.app (op V) y) =
    (quotientProjection E I action action_res habelian).val.app (op V)
      (normalizerSectionBracket E I action action_res jacobi (op V) x y) :=
  descendSheafOperation_projection _ _ _ _ _ V x y

/-- The quotient bracket commutes with restrictions on all quotient sections. -/
theorem normalizerQuotientBracket_restrict (V W : Opens X) (h : W ≤ V)
    (x y : (normalizerQuotientSheaf E I action action_res habelian).val.obj (op V)) :
    (normalizerQuotientSheaf E I action action_res habelian).val.map (homOfLE h).op
      (normalizerQuotientBracket E I action action_res habelian jacobi skew V x y) =
    normalizerQuotientBracket E I action action_res habelian jacobi skew W
      ((normalizerQuotientSheaf E I action action_res habelian).val.map (homOfLE h).op x)
      ((normalizerQuotientSheaf E I action action_res habelian).val.map (homOfLE h).op y) :=
  descendSheafOperation_restrict _ _ _ _ _ V W h x y

end Normalizer
