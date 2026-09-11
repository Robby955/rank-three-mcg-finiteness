import Normalizer.CurveMapSingular
import Normalizer.FiniteMapH1
import Mathlib.Algebra.Field.ZMod
import Normalizer.ProjectiveLineCohomology
import Normalizer.CurveProjectiveLine
import Normalizer.AffineH1Vanishing
import Normalizer.TwoAffineCohomology
import Normalizer.LaurentCechFinite
import Normalizer.OverSheafCohomology
import Normalizer.SheafCohomologyTerminal
import Normalizer.FiniteLineSections
import Normalizer.ClosedPushforwardCohomology
import Normalizer.SheafQuotientLie
import Normalizer.TrivializedCharacter
import Normalizer.NormalizerSheaf
import Normalizer.LocalCharacterGluing
import Normalizer.Flagship
import Normalizer.ModuleSheafHom
import Normalizer.NormalizerKernel
import Normalizer.LineTensor
import Normalizer.AffineLocallyFree
import Normalizer.AffinePresentedNeighborhood
import Normalizer.StalkLocalFreeness
import Normalizer.SheafCokernelFinitePresentation
import Normalizer.SaturatedStalkQuotient
import Normalizer.SmoothSchemeStalks
import Normalizer.ProperConstants
import Normalizer.GenericBoundary
import Normalizer.ExteriorLineTrivialization
import Normalizer.DeterminantGenericNonzero
import Normalizer.SectionZeroDivisor
import Normalizer.SectionZeroFinite
import Normalizer.FiniteSchemeCohomology
import Normalizer.SectionZeroCokernel
import Mathlib.RingTheory.AdjoinRoot

/-! Focused exact matrix tests. These are kernel-checked, symbolic over an
arbitrary characteristic-zero field, rather than floating-point evaluations. -/
namespace Normalizer.Examples
variable {F : Type*} [Field F] [CharZero F]

private def D : Mat F := !![1/2, 0, 0; 0, -1/2, 0; 0, 0, 0]
private def H : Mat F := !![1/2, 0, 0; 0, 1/2, 0; 0, 0, -1]
private def P : Mat F := !![0, 0, 1; 0, 0, 0; 0, 0, 0]
private def Q : Mat F := !![0, 0, 0; 0, 0, 0; 0, 1, 0]
private def E21 : Mat F := !![0, 0, 0; 1, 0, 0; 0, 0, 0]

example : comm (D : Mat F) nilM = nilM := by unfold D; matrix_calc
example : comm (H : Mat F) nilM = 0 := by unfold H; matrix_calc
example : comm (D : Mat F) P = (1/2 : F) • P := by unfold D P; matrix_calc
example : comm (D : Mat F) Q = (1/2 : F) • Q := by unfold D Q; matrix_calc
example : comm (H : Mat F) P = (3/2 : F) • P := by unfold H P; matrix_calc
example : comm (H : Mat F) Q = (-3/2 : F) • Q := by unfold H Q; matrix_calc
example : comm (P : Mat F) Q = nilM := by unfold P Q; matrix_calc
example : comm (nilM : Mat F) E21 = (2 : F) • D := by unfold E21 D; matrix_calc
example : comm (D : Mat F) semM = 0 := by unfold D; matrix_calc
example : comm (nilM : Mat F) semM = 0 := by matrix_calc
example : comm (E21 : Mat F) semM = 0 := by unfold E21; matrix_calc

/-- A sanity check that tests the distinction between the ambient and quotient brackets. -/
example : nilBracket (![0, 0, 1, 0] : Fin 4 → F) ![0, 0, 0, 1] = 0 := by
  ext i; fin_cases i <;> norm_num [nilBracket]

example : ¬ ((1 + 3 * (1/3 : F)) / 2 = 1 ∧ (1 - 3 * (1/3 : F)) / 2 = 1) :=
  nil_eigenvalue_conflict _

example (a b c d : F) : nilBracket ![0, 0, a, b] ![0, 0, c, d] = 0 := by
  ext i; fin_cases i <;> simp [nilBracket]

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

omit [CharZero F] in
private theorem frameInjectAtOne (m : Mat F) (i j : Fin 3) (hij : m i j = 1) :
    Function.Injective (fun a : F => a • m) := by
  intro a b hab
  have h := congrArg (fun A : Mat F => A i j) hab
  simpa [Matrix.smul_apply, hij] using h

private def semFramedLift (v : Fin 3 → F) (z : F) :
    (frameLine (R := F) (semM : Mat F)).normalizer :=
  ⟨semLift v + z • semM, (mem_frameNormalizer _ _).mpr
    ⟨0, by change comm _ _ = _; simpa using sem_action v z⟩⟩

private def nilFramedLift (v : Fin 4 → F) (z : F) :
    (frameLine (R := F) (nilM : Mat F)).normalizer :=
  ⟨nilLift v + z • nilM, (mem_frameNormalizer _ _).mpr ⟨v 0, nil_action v z⟩⟩

/-- The abstract quotient character reproduces the symbolic semisimple model. -/
example (v : Fin 3 → F) (z : F) :
    quotientFrameCharacter semM (frameInjectAtOne semM 0 0 (by simp [semM]))
      ((frameIdeal semM).toSubmodule.mkQ (semFramedLift v z)) = 0 := by
  rw [quotientFrameCharacter_mk]
  exact sem_frameCharacter _ _

/-- The abstract quotient character reproduces every minimal coordinate lift. -/
example (v : Fin 4 → F) (z : F) :
    quotientFrameCharacter nilM (frameInjectAtOne nilM 0 1 (by simp [nilM]))
      ((frameIdeal nilM).toSubmodule.mkQ (nilFramedLift v z)) = v 0 := by
  rw [quotientFrameCharacter_mk, nil_frameCharacter]
  change nilCoordinates (nilLift v + z • nilM) 0 = v 0
  rw [nil_coordinates_lift]

end Normalizer.Examples

-- Gluing identity maps on any cover recovers the actual identity morphism.
example {X : TopCat.{0}} {R : TopCat.Sheaf RingCat.{0} X} (M : SheafOfModules.{0} R)
    {ι : Type} (U : ι → TopologicalSpace.Opens X) (hcover : iSup U = ⊤) :
    Normalizer.glueLocalModuleMorphisms M M U hcover
      (fun _ _ _ => LinearMap.id) (by intros; rfl) (by intros; rfl) =
      (⟨CategoryTheory.CategoryStruct.id M.val⟩ : SheafOfModules.Hom M M) := by
  symm
  apply Normalizer.glueLocalModuleMorphisms_unique
  intros
  rfl

section NormalizerSheafChecks
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite TopologicalSpace
variable {X : TopCat.{0}} {R : TopCat.Sheaf RingCat.{0} X}
  (E : SheafOfModules.{0} R) (I : E.Submodule)

-- Every section preserves every subsheaf for the zero bracket.
example (V) (x : E.val.obj V) :
    x ∈ (Normalizer.normalizerSubsheaf E I (fun _ _ => 0)
      (by intros; simp)).obj V := by
  intro W f m hm
  simp

-- The zero character descends to zero on the actual sheaf cokernel.
example :
    Normalizer.descendNormalizerCharacter E I (fun _ _ => 0)
      (by intros; simp) (by intros; simp) 0 (by simp) = 0 := by
  apply (cancel_epi (Limits.cokernel.π (Normalizer.normalizerLineInclusion E I
    (fun _ _ => 0) (by intros; simp) (by intros; simp)))).mp
  simpa using Normalizer.descendNormalizerCharacter_fac E I (fun _ _ => 0)
    (by intros; simp) (by intros; simp) 0 (by simp)

end NormalizerSheafChecks

section TrivializedCharacterChecks
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite TopologicalSpace
variable {X : TopCat.{0}} {R : TopCat.Sheaf RingCat.{0} X}
  (E : SheafOfModules.{0} R) (I : E.Submodule)

-- A genuine sheaf trivialization produces the zero coefficient for zero action.
example {U : Opens X}
    (e : (SheafOfModules.unit R).over U ≅ I.toSheafOfModules.over U)
    (V : Opens X) (h : V ≤ U)
    (x : (Normalizer.normalizerSubsheaf E I (fun _ _ => 0)
      (by intros; simp)).toSheafOfModules.val.obj (op V)) :
    Normalizer.trivializationCharacter E I (fun _ _ => 0) (by intros; simp) e V h x = 0 := by
  apply Normalizer.sectionFrameCharacter_unique E I (fun _ _ => 0) (by intros; simp)
    (op V) (Normalizer.lineTrivializationAt E I e V h)
  simp

-- The construction from genuine local sheaf isomorphisms also reaches the
-- actual quotient projection, without assuming local characters as input.
example (ring_comm : ∀ V (a b : R.obj.obj V), a * b = b * a)
    {ι : Type} (U : ι → Opens X) (hc : iSup U = ⊤)
    (e : ∀ i, (SheafOfModules.unit R).over (U i) ≅ I.toSheafOfModules.over (U i))
    (i : ι) (V : Opens X) (h : V ≤ U i)
    (x : (Normalizer.normalizerSubsheaf E I (fun _ _ => 0)
      (by intros; simp)).toSheafOfModules.val.obj (op V)) :
    (Normalizer.lineQuotientCharacter E I (fun _ _ => 0)
      (by intros; simp) ring_comm (by intros; simp) U hc e (by intros; simp)).val.app (op V)
        ((Limits.cokernel.π (Normalizer.normalizerLineInclusion E I (fun _ _ => 0)
          (by intros; simp) (by intros; simp))).val.app (op V) x) = 0 := by
  rw [Normalizer.lineQuotientCharacter]
  rw [Normalizer.quotientCharacterOfTrivializations_local E I (fun _ _ => 0)
    (by intros; simp) ring_comm (by intros; simp) (by intros; simp) U hc e i V h x]
  apply Normalizer.sectionFrameCharacter_unique E I (fun _ _ => 0) (by intros; simp)
    (op V) (Normalizer.lineTrivializationAt E I (e i) V h)
  simp

end TrivializedCharacterChecks

section SheafQuotientBracketChecks
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite TopologicalSpace
variable {X : TopCat.{0}} {R : TopCat.Sheaf RingCat.{0} X}
  {A B : SheafOfModules.{0} R} (i : A ⟶ B)

-- Gluing the zero operation gives zero on arbitrary actual quotient sections;
-- no representatives on the full open are supplied in this test.
example (V : Opens X) (x y : (Limits.cokernel i).val.obj (op V)) :
    Normalizer.descendSheafOperation (Limits.cokernel.π i)
      (Normalizer.sheaf_cokernel_locallySurjective i) (fun _ _ _ => 0)
      (by intros; simp) (by intros; rfl) V x y = 0 := by
  symm
  apply Normalizer.descendSheafOperation_unique
  intros
  simp

-- Descent of projected addition recovers addition on every quotient section.
example (V : Opens X) (x y : (Limits.cokernel i).val.obj (op V)) :
    Normalizer.descendSheafOperation (Limits.cokernel.π i)
      (Normalizer.sheaf_cokernel_locallySurjective i)
      (fun W a b => (Limits.cokernel.π i).val.app (op W) (a + b))
      (by
        intro V W h a b
        exact (PresheafOfModules.naturality_apply (Limits.cokernel.π i).val
          (homOfLE h).op (a + b)).symm.trans (by simp))
      (by intro W a a' b b' ha hb; simp only [map_add, ha, hb]) V x y = x + y := by
  symm
  apply Normalizer.descendSheafOperation_unique
  intro W h a b ha hb
  simp only [map_add, ha, hb]

end SheafQuotientBracketChecks

section SheafQuotientLieChecks
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite TopologicalSpace
variable {X : TopCat.{0}} {R : TopCat.Sheaf RingCat.{0} X}
  (E : SheafOfModules.{0} R) (I : E.Submodule)
  (action : ∀ V, E.val.obj V → E.val.obj V →ₗ[R.obj.obj V] E.val.obj V)
  (action_res : ∀ {V W} (f : V ⟶ W) (m x : E.val.obj V),
    E.val.map f (action V m x) = action W (E.val.map f m) (E.val.map f x))
  (habelian : ∀ V (x m : E.val.obj V), x ∈ I.obj V → m ∈ I.obj V → action V m x = 0)
  (jacobi : ∀ V (x y m : E.val.obj V), action V m (action V y x) =
    action V (action V m y) x - action V (action V m x) y)
  (skew : ∀ V (x y : E.val.obj V), action V y x = -action V x y)
  (alternating : ∀ V (x : E.val.obj V), action V x x = 0)
  (ring_comm : ∀ V (a b : R.obj.obj V), a * b = b * a)

-- The constructed instances work with mathlib's existing scalar-bracket API.
include alternating ring_comm in
example (V : Opens X) (r : R.obj.obj (op V))
    (x y : (Normalizer.normalizerQuotientSheaf E I action action_res habelian).val.obj (op V)) :
    Normalizer.normalizerQuotientBracket E I action action_res habelian jacobi skew V (r • x) y =
      r • Normalizer.normalizerQuotientBracket E I action action_res habelian jacobi skew V x y := by
  let : CommRing (R.obj.obj (op V)) :=
    { (inferInstance : Ring (R.obj.obj (op V))) with mul_comm := ring_comm (op V) }
  let := Normalizer.normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating V
  let := Normalizer.normalizerQuotientLieAlgebra E I action action_res habelian jacobi skew
    alternating ring_comm V
  exact smul_lie r x y

-- The bundled character works with mathlib's LieHom API on arbitrary
-- quotient sections. This tests the actual source and target Lie instances.
include alternating in
example (action_smul_right : ∀ V (r : R.obj.obj V) (m x : E.val.obj V),
      action V (r • m) x = r • action V m x)
    {ι : Type} (U : ι → Opens X) (hcover : iSup U = ⊤)
    (triv : ∀ i, (SheafOfModules.unit R).over (U i) ≅ I.toSheafOfModules.over (U i))
    (V : Opens X)
    (x y : (Normalizer.normalizerQuotientSheaf E I action action_res habelian).val.obj (op V)) :
    (Normalizer.quotientCharacterOfTrivializations E I action action_res ring_comm
      action_smul_right habelian U hcover triv).val.app (op V)
      (Normalizer.normalizerQuotientBracket E I action action_res habelian jacobi skew V x y) = 0 := by
  let : CommRing (R.obj.obj (op V)) :=
    { (inferInstance : Ring (R.obj.obj (op V))) with mul_comm := ring_comm (op V) }
  let := Normalizer.normalizerQuotientLieRing E I action action_res habelian jacobi skew alternating V
  let := Normalizer.normalizerQuotientLieAlgebra E I action action_res habelian jacobi skew
    alternating ring_comm V
  let := LieRing.ofAssociativeRing (A := R.obj.obj (op V))
  let f := Normalizer.quotientCharacterLieHom E I action action_res habelian jacobi skew
    alternating ring_comm action_smul_right U hcover triv V
  have h := LieHom.map_lie f x y
  have hz : ⁅f x, f y⁆ = 0 := by
    change f x * f y - f y * f x = 0
    rw [ring_comm, sub_self]
  exact h.trans hz

end SheafQuotientLieChecks

section ModuleSheafHomChecks
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite TopologicalSpace
variable {X : TopCat.{0}} {R : TopCat.Sheaf RingCat.{0} X}
  (A B : SheafOfModules.{0} R)
  (ring_comm : ∀ V (a b : R.obj.obj V), a * b = b * a)

-- The actual restricted identity becomes an internal-Hom section acting
-- by the identity on every smaller open.
example (V W : Opens X) (h : W ≤ V) :
    Normalizer.moduleHomEval A A ring_comm V W h
      ((Normalizer.moduleHomOverEquiv A A ring_comm V).symm (𝟙 (A.over V))) =
      LinearMap.id := rfl

-- Restricting the section associated to a genuine sheaf morphism recovers
-- that morphism's component on a further subopen.
example (V W Z : Opens X) (h : W ≤ V) (k : Z ≤ W)
    (f : A.over V ⟶ B.over V) :
    Normalizer.moduleHomEval A B ring_comm W Z k
      ((Normalizer.moduleHomSheaf A B ring_comm).val.map (homOfLE h).op
        ((Normalizer.moduleHomOverEquiv A B ring_comm V).symm f)) =
      (f.val.app (op (Over.mk (homOfLE (k.trans h))))).hom := by
  rw [Normalizer.moduleHom_restrict]
  rfl

end ModuleSheafHomChecks

section LineTensorChecks
open TensorProduct

-- The canonical map evaluates a symbolic sum of tensors componentwise.
example (a b c d e f x : ℚ) :
    Normalizer.tensorHomEval ℚ ℚ (ℚ × ℚ)
      ((a, b) ⊗ₜ[ℚ] (c • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) +
        (d, e) ⊗ₜ[ℚ] (f • (LinearMap.id : ℚ →ₗ[ℚ] ℚ))) x =
      (c * x * a + f * x * d, c * x * b + f * x * e) := by
  simp [Prod.smul_mk, smul_eq_mul, mul_assoc]

-- Rescaling the rank-one coordinate by two rescales the inverse's vector
-- by one half. The two factors compensate in the actual tensor product.
example (a b : ℚ) :
    (Normalizer.lineTensorHomEquiv
      (LinearEquiv.smulOfNeZero ℚ (M := ℚ) (2 : ℚ) (by norm_num))).symm
      ((LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight (a, b)) =
      (a / 2, b / 2) ⊗ₜ[ℚ] (2 • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) := by
  rw [Normalizer.lineTensorHomEquiv_symm_apply]
  congr 1
  · ext <;> simp [LinearEquiv.smulOfNeZero, LinearEquiv.smulOfUnit,
      Units.smul_def, smul_eq_mul, div_eq_mul_inv, mul_comm]
end LineTensorChecks

section AffineQuotientChecks
open CategoryTheory Limits AlgebraicGeometry

-- A coordinate line over the integers is saturated: cancellation in the
-- second coordinate proves the condition without dividing by the scalar.
-- Its actual affine sheaf cokernel is therefore finite locally free.
example :
    let S : Submodule ℤ (ℤ × ℤ) := (LinearMap.snd ℤ ℤ ℤ).ker
    (cokernel (tilde.map (R := CommRingCat.of ℤ) (ModuleCat.ofHom S.subtype))).IsLocallyFree ∧
      (cokernel (tilde.map (R := CommRingCat.of ℤ) (ModuleCat.ofHom S.subtype))).IsFiniteType := by
  dsimp only
  apply Normalizer.affineSaturatedQuotient_finiteLocallyFree
    (R := CommRingCat.of ℤ) (ModuleCat.of ℤ (ℤ × ℤ))
  intro r hr m hm
  change r * m.2 = 0 at hm
  change m.2 = 0
  exact (mul_eq_zero.mp hm).resolve_left hr

-- The saturation hypothesis excludes 2ℤ in ℤ: multiplying 1 by the
-- nonzero scalar 2 lands in the submodule, while 1 itself does not.
example : ¬ ∀ (r : ℤ), r ≠ 0 → ∀ (m : ℤ),
    r • m ∈ Submodule.span ℤ ({2} : Set ℤ) → m ∈ Submodule.span ℤ ({2} : Set ℤ) := by
  intro h
  have htwo : (2 : ℤ) ∈ Submodule.span ℤ ({2} : Set ℤ) :=
    Submodule.subset_span (by simp)
  have hone := h 2 (by norm_num) 1 htwo
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hone
  simp only [smul_eq_mul] at ha
  omega

end AffineQuotientChecks

section AffineNeighborhoodChecks
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false

-- The integer plane has a finite free-sheaf neighborhood at every prime.
-- Its free-stalk hypothesis is derived from the concrete free module.
example (x : PrimeSpectrum ℤ) :
    ∃ r : ℤ, x ∈ (Normalizer.affineLocalizationMap (R := CommRingCat.of ℤ) r).opensRange ∧
      ∃ (ι : Type) (_ : Finite ι),
        Nonempty (Normalizer.affineLocalizationSheaf (R := CommRingCat.of ℤ)
          (ModuleCat.of ℤ (ℤ × ℤ)) r ≅ SheafOfModules.free ι) := by
  let M := ModuleCat.of ℤ (ℤ × ℤ)
  have hx : x ∈ Module.freeLocus ℤ M := by
    rw [Module.freeLocus_eq_univ]
    trivial
  let : Module.Free ((Spec (CommRingCat.of ℤ)).presheaf.stalk x)
      ((tilde (R := CommRingCat.of ℤ) M).presheaf.stalk x) :=
    (Normalizer.affineStalk_free_iff (R := CommRingCat.of ℤ) M x).mpr hx
  exact Normalizer.affineStalk_exists_finiteFree_neighborhood (R := CommRingCat.of ℤ) M x

-- Adding the identity sheaf map to itself doubles every actual section germ.
example {X : Scheme} (E : X.Modules) (x : X) (U : X.Opens)
    (hx : x ∈ U) (s : Γ(E, U)) :
    Normalizer.schemeModuleStalkMap (𝟙 E + 𝟙 E) x (E.presheaf.germ U x hx s) =
      E.presheaf.germ U x hx s + E.presheaf.germ U x hx s := by
  rw [Normalizer.schemeModuleStalkMap_germ]
  simp

end AffineNeighborhoodChecks

section LocallyFreeAssemblyChecks
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false

-- The integer-plane neighborhoods assemble into mathlib's actual local
-- freeness property, with finite presentation derived from the module.
example :
    (tilde (R := CommRingCat.of ℤ) (ModuleCat.of ℤ (ℤ × ℤ))).IsLocallyFree := by
  let M := ModuleCat.of ℤ (ℤ × ℤ)
  let : (tilde (R := CommRingCat.of ℤ) M).IsFinitePresentation :=
    Normalizer.tilde_isFinitePresentation (A := CommRingCat.of ℤ) M
  apply Normalizer.sheaf_isLocallyFree_of_free_stalks
  intro x
  apply (Normalizer.affineStalk_free_iff (R := CommRingCat.of ℤ) M x).mpr
  rw [Module.freeLocus_eq_univ]
  trivial

-- Dimension zero is included in the regular-local criterion; it does not
-- incorrectly require a nonzero maximal ideal or a non-field DVR.
example : IsPrincipalIdealRing ℚ := by
  apply Normalizer.principalIdealRing_of_regularLocal_dim_le_one ℚ
  rw [ringKrullDim_eq_zero_of_field]
  exact zero_le_one

end LocallyFreeAssemblyChecks

section CokernelPresentationChecks
open CategoryTheory Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false

-- Multiplication by two on the integer structure sheaf has a finitely
-- presented actual cokernel, without requiring its stalks to be free.
example :
    (cokernel ((tilde.functor (CommRingCat.of ℤ)).map
      (ModuleCat.ofHom (2 • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))))).IsFinitePresentation := by
  let M := ModuleCat.of ℤ ℤ
  let : ((tilde.functor (CommRingCat.of ℤ)).obj (ModuleCat.of ℤ ℤ)).IsFinitePresentation :=
    Normalizer.tilde_isFinitePresentation (A := CommRingCat.of ℤ) M
  exact Normalizer.sheaf_cokernel_isFinitePresentation _

end CokernelPresentationChecks

section SaturatedStalkChecks
open CategoryTheory Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false

-- Quotienting any actual sheaf by itself gives torsion-free stalks,
-- even when the original sheaf has torsion. No ambient freeness is used.
example {X : Scheme} [IsIntegral X] (E : X.Modules) (x : X) :
    Module.IsTorsionFree (X.presheaf.stalk x)
      ((cokernel (𝟙 E)).presheaf.stalk x) := by
  apply Normalizer.sheaf_cokernel_stalk_isTorsionFree_of_saturated
  intro r hr v hv
  refine ⟨v, ?_⟩
  obtain ⟨U, hxU, a, rfl⟩ := E.presheaf.exists_germ_eq v
  rw [Normalizer.schemeModuleStalkMap_germ]
  simp

-- The stalk quotient comparison respects actual germs and the actual
-- sheaf projection, rather than only giving an abstract linear equivalence.
example {X : Scheme} {M E : X.Modules} (f : M ⟶ E) [Mono f]
    (x : X) (U : X.Opens) (hxU : x ∈ U) (s : Γ(E, U)) :
    Normalizer.sheafCokernelStalkEquiv f x
        (Submodule.Quotient.mk (E.presheaf.germ U x hxU s)) =
      (cokernel f).presheaf.germ U x hxU ((cokernel.π f).app U s) := by
  rw [Normalizer.sheafCokernelStalkEquiv_mk, Normalizer.schemeModuleStalkMap_germ]

end SaturatedStalkChecks

section SmoothRegularityChecks
open CategoryTheory AlgebraicGeometry

-- The algebra result covers every prime of a polynomial algebra, including
-- non-maximal primes; it imposes no characteristic-zero restriction.
example (k : Type*) [Field k] (p : Ideal (MvPolynomial (Fin 2) k)) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  let : Algebra.Smooth k (MvPolynomial (Fin 2) k) := {}
  exact Normalizer.regularLocal_localization_of_smooth k (MvPolynomial (Fin 2) k) p

-- The geometric result acts on the actual structure-sheaf stalk, including
-- the dimension-zero smooth case.
example (x : Spec (CommRingCat.of ℚ)) :
    IsRegularLocalRing ((Spec (CommRingCat.of ℚ)).presheaf.stalk x) :=
  Normalizer.smoothScheme_stalk_isRegularLocalRing ℚ (𝟙 _) x

end SmoothRegularityChecks

-- The constants map need not be surjective for an affine polynomial
-- algebra. Properness cannot be discarded from the geometric result.
example (k : Type*) [Field k] :
    ¬ Function.Surjective (Polynomial.C : k →+* Polynomial k) := by
  intro h
  obtain ⟨c, hc⟩ := h Polynomial.X
  have he := congrArg (fun p : Polynomial k ↦ p.coeff 1) hc
  simp at he

section GenericFibreChecks
open CategoryTheory AlgebraicGeometry TensorProduct
set_option backward.isDefEq.respectTransparency false

-- Three genuine free-sheaf generators remain independent over the actual
-- function field, without assuming generic independence separately.
example {X : Scheme} [IsIntegral X] :
    LinearIndependent X.functionField (Normalizer.freeSheafGenericGenerators
      (X := X) (I := Fin 3)) :=
  Normalizer.freeSheafGenericGenerators_linearIndependent (Fin 3)

-- Any actual rank-three free-sheaf inclusion has a three-dimensional
-- generic image. This exercises the inclusion-to-dimension interface.
example {X : Scheme} [IsIntegral X] (K : X.Modules)
    (f : (SheafOfModules.free (R := X.ringCatSheaf) (Fin 3) : X.Modules) ⟶ K)
    [Mono f] :
    Module.finrank X.functionField (Submodule.span X.functionField
      (Set.range (fun i : Fin 3 ↦ K.presheaf.germ ⊤ (genericPoint X) (by trivial)
        (f.val.app (Opposite.op ⊤) (Normalizer.freeSheafGenerator i))))) = 3 := by
  simpa only [Fintype.card_fin] using
    Normalizer.freeSheaf_mono_generic_span_finrank (Fin 3) f

-- The scalar-extended character uses the actual tensor construction.
example {F Ω V : Type*} [Field F] [Field Ω] [Algebra F Ω]
    [AddCommGroup V] [Module F V] (χ : V →ₗ[F] F) (v : V) :
    Normalizer.boundaryCharacterBaseChange (Ω := Ω) χ ((1 : Ω) ⊗ₜ[F] v) =
      algebraMap F Ω (χ v) := by
  simp [Normalizer.boundaryCharacterBaseChange_tmul]

end GenericFibreChecks

section ExteriorLineChecks
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false

-- Rank zero is included: the zeroth exterior sheaf of the zero bundle
-- is a line, without a positive-rank assumption.
example {X : Scheme} : Nonempty
    (SheafOfModules.unit X.ringCatSheaf ≅
      Normalizer.schemeExteriorSheaf (Normalizer.schemeTrivialBundle X (Fin 0)) 0) :=
  ⟨Normalizer.bundleTopExteriorSheafIso (Equiv.refl (Fin 0)) (Iso.refl _)⟩

-- A rank-two frame gives the actual exterior line on any open,
-- including the empty open; this checks the restriction construction.
example {X : Scheme} (U : X.Opens) : Nonempty
    ((SheafOfModules.unit X.ringCatSheaf).over U ≅
      (Normalizer.schemeExteriorSheaf (Normalizer.schemeTrivialBundle X (Fin 2)) 2).over U) :=
  ⟨Normalizer.bundleTopExteriorSheafIsoOver (Equiv.refl (Fin 2)) (Iso.refl _)⟩

end ExteriorLineChecks

section ExteriorGenericChecks
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false

-- The empty family has nonzero exterior section on every integral scheme,
-- including for sheaves with no chosen bundle chart.
example {X : Scheme} [IsIntegral X] (H : X.Modules) :
    Normalizer.schemeExteriorGlobalSection H 0 (fun i ↦ Fin.elim0 i) ≠ 0 :=
  Normalizer.schemeExteriorGlobalSection_ne_zero H 0 _ (linearIndependent_empty_type)

-- Repeated actual global sections give zero, so independence is essential.
example {X : Scheme} (H : X.Modules) (s : Γ(H, ⊤)) :
    Normalizer.schemeExteriorGlobalSection H 2 (fun _ ↦ s) = 0 := by
  unfold Normalizer.schemeExteriorGlobalSection Normalizer.schemeExteriorPure
  rw [(exteriorPower.ιMulti _ 2).map_eq_zero_of_eq (fun _ ↦ s)
    (i := 0) (j := 1) rfl (by decide), map_zero]

end ExteriorGenericChecks

section SectionZeroChecks
open CategoryTheory AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false

-- A zero specified section gives the zero ideal, including its scheme structure.
example {X : Scheme} (V : X.Opens) :
    Normalizer.schemeSectionImageIdeal
      (Normalizer.schemeSectionDualEvaluation (SheafOfModules.unit X.ringCatSheaf) 0) V = ⊥ := by
  rw [Normalizer.schemeSectionDualEvaluation_imageIdeal _ _ (Iso.refl
    ((SheafOfModules.unit X.ringCatSheaf).over ⊤)) V le_top]
  simp [Normalizer.sectionLocalEquation]

-- The constant unit section gives the unit ideal, hence has no local zeros.
example {X : Scheme} (V : X.Opens) :
    Normalizer.schemeSectionImageIdeal
      (Normalizer.schemeSectionDualEvaluation (SheafOfModules.unit X.ringCatSheaf)
        (1 : Γ(X, ⊤))) V = ⊤ := by
  rw [Normalizer.schemeSectionDualEvaluation_imageIdeal _ _ (Iso.refl
    ((SheafOfModules.unit X.ringCatSheaf).over ⊤)) V le_top]
  change Ideal.span {X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
    (1 : Γ(X, ⊤))} = ⊤
  simp

-- A regular equation can still vanish: regularity does not assert invertibility.
example : IsRegular (Polynomial.X : Polynomial ℚ) ∧
    ¬ IsUnit (Polynomial.X : Polynomial ℚ) := by
  exact ⟨IsRegular.of_ne_zero Polynomial.X_ne_zero, Polynomial.not_isUnit_X⟩

-- Principal zero ideals retain multiplicity; squaring is not silently reduced.
example : (Polynomial.X : Polynomial ℚ) ∉
    Ideal.span ({Polynomial.X ^ 2} : Set (Polynomial ℚ)) := by
  rw [Ideal.mem_span_singleton]
  intro h
  have hd := Polynomial.natDegree_le_of_dvd h Polynomial.X_ne_zero
  norm_num at hd

end SectionZeroChecks

section FiniteZeroSchemeChecks
open CategoryTheory AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false

-- The doubled point has a nonzero nilpotent. Its scheme structure must survive
-- the finiteness and function-space arguments.
example : ∃ a : AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ 2), a ≠ 0 ∧ a ^ 2 = 0 := by
  refine ⟨AdjoinRoot.root _, ?_, ?_⟩
  · exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      (Polynomial.monic_X.pow 2) Polynomial.X_ne_zero (by norm_num)
  · rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]

-- Apply the actual finite-scheme function theorem to that nonreduced doubled point,
-- with its field action induced by its actual structure morphism.
example :
    let R := AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ 2)
    let p : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of ℚ) :=
      Spec.map (CommRingCat.ofHom (algebraMap ℚ R))
    let := Normalizer.schemeGlobalFunctionsAlgebra p
    0 < Module.finrank ℚ Γ(Spec (CommRingCat.of R), ⊤) := by
  let R := AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ 2)
  let p : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of ℚ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ R))
  have : Nontrivial R := AdjoinRoot.nontrivial _ (by norm_num)
  have : Module.Finite ℚ R := (Polynomial.monic_X.pow 2).finite_adjoinRoot
  have : IsFinite p := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  exact Normalizer.finiteScheme_globalFunctions_finrank_pos p

end FiniteZeroSchemeChecks

noncomputable section ClosedSubschemeQuotientChecks
open CategoryTheory AlgebraicGeometry Opposite Limits
set_option backward.isDefEq.respectTransparency false

-- The actual sheaf cokernel comparison also applies to the zero map;
-- it does not impose the regular-section hypothesis needed for a left injection.
example {X : Scheme} {ι : Type} [Finite ι] (U : ι → X.Opens)
    [∀ i, QuasiCompact (U i).ι] (hU : iSup U = ⊤) :
    cokernel (0 : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) ≅
      Normalizer.closedSubschemeStructureSheaf
        (Normalizer.schemeSectionZeroIdeal
          (0 : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
          U (fun _ ↦ Iso.refl _) hU) :=
  Normalizer.schemeSectionZeroCokernelIso _ U _ hU

-- The actual closed-subscheme structure quotient retains the nonzero
-- square-zero coordinate of the doubled point, rather than reducing it.
example :
    let X := Spec (CommRingCat.of (Polynomial ℚ))
    let e := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℚ))).commRingCatIsoToRingEquiv
    let a : Γ(X, ⊤) := e.symm Polynomial.X
    let I : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop (Ideal.span {a ^ 2})
    (I.subschemeι.app ⊤ a) ≠ 0 ∧ (I.subschemeι.app ⊤ a) ^ 2 = 0 := by
  let X := Spec (CommRingCat.of (Polynomial ℚ))
  let e := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℚ))).commRingCatIsoToRingEquiv
  let a : Γ(X, ⊤) := e.symm Polynomial.X
  let I : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop (Ideal.span {a ^ 2})
  change I.subschemeι.app ⊤ a ≠ 0 ∧ (I.subschemeι.app ⊤ a) ^ 2 = 0
  have hI : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {a ^ 2} := by
    simp [I]
  have hzero (r : Γ(X, ⊤)) : I.subschemeι.app ⊤ r = 0 ↔ r ∈ Ideal.span {a ^ 2} := by
    have h := Normalizer.closedSubschemeStructureMap_affine_eq_zero_iff
      I ⟨⊤, isAffineOpen_top X⟩ r
    change I.subschemeι.app ⊤ r = 0 ↔ r ∈ I.ideal ⟨⊤, isAffineOpen_top X⟩ at h
    rwa [hI] at h
  constructor
  · intro hz
    have ha := (hzero a).mp hz
    rw [Ideal.mem_span_singleton] at ha
    have hd : (Polynomial.X : Polynomial ℚ) ^ 2 ∣ Polynomial.X := by
      have hd := map_dvd e ha
      change e (a ^ 2) ∣ e a at hd
      rw [map_pow] at hd
      have hea : e a = Polynomial.X := e.apply_symm_apply _
      rwa [hea] at hd
    have hn := Polynomial.natDegree_le_of_dvd hd Polynomial.X_ne_zero
    norm_num at hn
  · have hz := (hzero (a ^ 2)).mpr (Ideal.subset_span (by simp))
    exact ((I.subschemeι.app ⊤).hom.map_pow a 2).symm.trans hz

end ClosedSubschemeQuotientChecks

section FiniteSchemeCohomologyChecks
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false

-- Every abelian sheaf on the actual doubled point has zero positive-degree
-- intrinsic cohomology; the nonzero nilpotent checked above is retained.
example
    (F : TopCat.Sheaf AddCommGrpCat
      (Spec (CommRingCat.of (AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ 2)))).toTopCat)
    (n : ℕ) (hn : 0 < n) : Subsingleton (CategoryTheory.Sheaf.H F n) := by
  let R := AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ 2)
  let p : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of ℚ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ R))
  have : Module.Finite ℚ R := (Polynomial.monic_X.pow 2).finite_adjoinRoot
  have : IsFinite p := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n => exact Normalizer.finiteScheme_positiveCohomology_subsingleton p F n

end FiniteSchemeCohomologyChecks

section ClosedPushforwardCohomologyChecks
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false

-- Higher cohomology of the direct image from the doubled point vanishes
-- on the affine line. Both the closed embedding and finiteness are derived
-- from the actual quotient presentation, retaining the nonzero nilpotent.
example
    (F : TopCat.Sheaf AddCommGrpCat
      (Spec (CommRingCat.of (AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ 2)))).toTopCat)
    (n : ℕ) (hn : 0 < n) :
    let i := Spec.map (CommRingCat.ofHom
      (AdjoinRoot.mk ((Polynomial.X : Polynomial ℚ) ^ 2)))
    Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.pushforward AddCommGrpCat i.base).obj F) n) := by
  let R := AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ 2)
  let i := Spec.map (CommRingCat.ofHom
    (AdjoinRoot.mk ((Polynomial.X : Polynomial ℚ) ^ 2)))
  let p : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of ℚ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ R))
  have : IsClosedImmersion i :=
    IsClosedImmersion.spec_of_surjective _ AdjoinRoot.mk_surjective
  have : Module.Finite ℚ R := (Polynomial.monic_X.pow 2).finite_adjoinRoot
  have : IsFinite p := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
    have := Normalizer.finiteScheme_positiveCohomology_subsingleton p F n
    exact (Normalizer.closedPushforwardCohomologyEquiv i.base i.isClosedEmbedding F
      (n + 1)).injective.subsingleton

end ClosedPushforwardCohomologyChecks

section FiniteLineSectionsChecks
open CategoryTheory AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false

private noncomputable def specGlobalFunctionsEquiv (A : Type) [CommRing A] [Algebra ℚ A] :
    let p := Spec.map (CommRingCat.ofHom (algebraMap ℚ A))
    let := Normalizer.schemeGlobalFunctionsAlgebra p
    Γ(Spec (CommRingCat.of A), ⊤) ≃ₗ[ℚ] A := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap ℚ A))
  let := Normalizer.schemeGlobalFunctionsAlgebra p
  let e := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  have he (a : ℚ) : e (Normalizer.schemeConstantMap p a) = algebraMap ℚ A a := by
    change ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫
      p.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) a = _
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    rfl
  exact {
    __ := e.toAddEquiv
    map_smul' := by
      intro a s
      change e (Normalizer.schemeConstantMap p a * s) = a • e s
      rw [map_mul, he, Algebra.smul_def] }

-- An arbitrary genuine line sheaf on the doubled point has a finite space of
-- global sections of dimension two. Its nonreduced scheme structure is retained.
example
    (L : (Spec (CommRingCat.of (AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ 2)))).Modules)
    (hL : ∀ x, ∃ U, x ∈ U ∧
      Nonempty ((SheafOfModules.unit
        (Spec (CommRingCat.of (AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ 2)))).ringCatSheaf).over U ≅
        L.over U)) :
    let R := AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ 2)
    let p := Spec.map (CommRingCat.ofHom (algebraMap ℚ R))
    let := Normalizer.schemeGlobalSectionsModuleOfMorphism p L
    Module.Finite ℚ Γ(L, ⊤) ∧ Module.finrank ℚ Γ(L, ⊤) = 2 := by
  let R := AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ 2)
  let p := Spec.map (CommRingCat.ofHom (algebraMap ℚ R))
  let := Normalizer.schemeGlobalSectionsModuleOfMorphism p L
  have : Module.Finite ℚ R := (Polynomial.monic_X.pow 2).finite_adjoinRoot
  have : IsFinite p := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  let := Normalizer.schemeGlobalFunctionsAlgebra p
  refine ⟨Normalizer.finiteLineSections_finite p L hL, ?_⟩
  rw [Normalizer.finiteLineSections_finrank_eq p L hL,
    (specGlobalFunctionsEquiv R).finrank_eq]
  change Module.finrank ℚ (Polynomial ℚ ⧸ Ideal.span {(Polynomial.X : Polynomial ℚ) ^ 2}) = 2
  rw [finrank_quotient_span_eq_natDegree]
  norm_num

-- The same theorem applies to a disconnected finite scheme: no connectedness
-- or single chosen global frame is an input to this example.
example (L : (Spec (CommRingCat.of (ℚ × ℚ))).Modules)
    (hL : ∀ x, ∃ U, x ∈ U ∧
      Nonempty ((SheafOfModules.unit (Spec (CommRingCat.of (ℚ × ℚ))).ringCatSheaf).over U ≅
        L.over U)) :
    let p := Spec.map (CommRingCat.ofHom (algebraMap ℚ (ℚ × ℚ)))
    let := Normalizer.schemeGlobalSectionsModuleOfMorphism p L
    Module.Finite ℚ Γ(L, ⊤) ∧ Module.finrank ℚ Γ(L, ⊤) = 2 := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap ℚ (ℚ × ℚ)))
  let := Normalizer.schemeGlobalSectionsModuleOfMorphism p L
  have : IsFinite p := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  let := Normalizer.schemeGlobalFunctionsAlgebra p
  refine ⟨Normalizer.finiteLineSections_finite p L hL, ?_⟩
  rw [Normalizer.finiteLineSections_finrank_eq p L hL,
    (specGlobalFunctionsEquiv (ℚ × ℚ)).finrank_eq]
  simp [Module.finrank_prod]

end FiniteLineSectionsChecks

section TerminalCohomologyChecks
open CategoryTheory AlgebraicGeometry Limits
set_option backward.isDefEq.respectTransparency false

-- The alternate cohomology-presheaf API has the same positive-degree
-- vanishing at the whole doubled point. This exercises the terminal
-- comparison on an actual nonreduced scheme and arbitrary abelian sheaf.
example
    (F : TopCat.Sheaf AddCommGrpCat
      (Spec (CommRingCat.of (AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ 2)))).toTopCat)
    (n : ℕ) : Subsingleton (F.H' (n + 1) ⊤) := by
  let R := AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ 2)
  let p : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of ℚ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ R))
  have : Module.Finite ℚ R := (Polynomial.monic_X.pow 2).finite_adjoinRoot
  have : IsFinite p := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  have := Normalizer.finiteScheme_positiveCohomology_subsingleton p F n
  exact (Normalizer.sheafCohomologyTerminalEquiv _ isTerminalTop F (n + 1)).injective.subsingleton

end TerminalCohomologyChecks

section OverCohomologyChecks
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false

-- The slice comparison specializes to every actual open of a scheme;
-- neither a supplied exactness instance nor cohomology vanishing is an input.
noncomputable example (X : Scheme.{u}) (U : X.Opens)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat) (n : ℕ) :
    F.H' n U ≃+ (F.over U).H n :=
  Normalizer.overSheafCohomologyEquiv _ U F n

-- At the whole space, the new slice comparison and the previously checked
-- terminal-object comparison give exactly the same actual section.
example (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : F.H' 0 ⊤) :
    Sheaf.H.equiv₀ (F.over ⊤) Over.mkIdTerminal
      (Normalizer.overSheafCohomologyEquiv _ ⊤ F 0 x) =
    Sheaf.H.equiv₀ F isTerminalTop
      (Normalizer.sheafCohomologyTerminalEquiv _ isTerminalTop F 0 x) := by
  rw [Normalizer.overSheafCohomologyEquiv_equiv₀,
    Normalizer.sheafCohomologyTerminalEquiv_equiv₀]

end OverCohomologyChecks

section AffineH1Checks
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false

-- The affine theorem retains nilpotents and applies in positive characteristic.
example : Subsingleton (Sheaf.H
    ((Normalizer.schemeModulesToAbelianSheaves (Spec (CommRingCat.of (ZMod 4)))).obj
      (tilde (ModuleCat.of (ZMod 4) (ZMod 4)))) 1) :=
  Normalizer.tilde_H1_subsingleton _

-- No finite generation of the module is required.
example : Subsingleton (Sheaf.H
    ((Normalizer.schemeModulesToAbelianSheaves (Spec (CommRingCat.of ℤ))).obj
      (tilde (ModuleCat.of ℤ (ℕ →₀ ℤ)))) 1) :=
  Normalizer.tilde_H1_subsingleton _

-- The actual structure sheaf of an arbitrary affine scheme is covered by
-- the quasicoherent-sheaf corollary, without a supplied localization proof.
example (R : CommRingCat.{u}) : Subsingleton (Sheaf.H
    ((Normalizer.schemeModulesToAbelianSheaves (Spec R)).obj
      (SheafOfModules.unit (Spec R).ringCatSheaf)) 1) :=
  by
    have : (SheafOfModules.unit (Spec R).ringCatSheaf).IsQuasicoherent :=
      (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance
    exact Normalizer.quasicoherent_Spec_H1_subsingleton _

-- The zero ring is allowed; the theorem includes the empty affine scheme.
example : Subsingleton (Sheaf.H
    ((Normalizer.schemeModulesToAbelianSheaves (Spec (CommRingCat.of (ZMod 1)))).obj
      (tilde (ModuleCat.of (ZMod 1) (ZMod 1)))) 1) :=
  Normalizer.tilde_H1_subsingleton _

end AffineH1Checks

section AffineOpenChecks
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false

-- This composes actual cokernel finite presentation with the new affine-open
-- vanishing theorem. No separate quasicoherence of the quotient is supplied.
example (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (E L : X.Modules) [E.IsFinitePresentation] [L.IsFinitePresentation] (f : E ⟶ L) :
    Subsingleton (((Normalizer.schemeModulesToAbelianSheaves X).obj (cokernel f)).H' 1 U) := by
  have := Normalizer.sheaf_cokernel_isFinitePresentation f
  exact Normalizer.quasicoherent_affineOpen_H1_subsingleton U hU (cokernel f)

-- A genuine principal open in a nonreduced ring, with an infinitely generated
-- associated module, exercises the ambient cohomology-presheaf conclusion.
example : Subsingleton
    (((Normalizer.schemeModulesToAbelianSheaves (Spec (CommRingCat.of (ZMod 12)))).obj
      (tilde (ModuleCat.of (ZMod 12) (ℕ →₀ ZMod 12)))).H' 1
        (PrimeSpectrum.basicOpen (3 : ZMod 12))) :=
  Normalizer.quasicoherent_affineOpen_H1_subsingleton _ (IsAffineOpen.Spec_basicOpen _) _

end AffineOpenChecks

section LaurentQuotientChecks
open LaurentPolynomial
open scoped LaurentPolynomial

private theorem monomial_generates (R : Type*) [CommRing R] (m : ℤ) :
    Submodule.span R[T;T⁻¹] (Set.range (fun _ : Unit => (T m : R[T;T⁻¹]))) = ⊤ := by
  rw [Set.range_const, Submodule.span_singleton_eq_top_iff]
  intro p
  refine ⟨p * T (-m), ?_⟩
  simp only [smul_eq_mul, mul_assoc, ← T_add, neg_add_cancel, T_zero, mul_one]

-- The algebraic finiteness result works over a coefficient ring that is
-- not a field, and allows any integer shift between the two chart families.
example (d : ℤ) : Module.Finite ℤ (ℤ[T;T⁻¹] ⧸
    (Normalizer.laurentSpan ℤ (fun _ : Unit => (T 0 : ℤ[T;T⁻¹])) (Set.Ici 0) ⊔
      Normalizer.laurentSpan ℤ (fun _ : Unit => (T d : ℤ[T;T⁻¹])) (Set.Iic 0))) :=
  Normalizer.laurent_twoChart_quotient_finite ℤ _ (monomial_generates ℤ 0)
    _ (monomial_generates ℤ d)

-- Finiteness does not imply vanishing: T^(-1) survives the quotient by
-- nonnegative powers and powers at most -2. Its coefficient detects it.
example : (Submodule.Quotient.mk (T (-1) : ℚ[T;T⁻¹]) : ℚ[T;T⁻¹] ⧸
    (Normalizer.laurentSpan ℚ (fun _ : Unit => (T 0 : ℚ[T;T⁻¹])) (Set.Ici 0) ⊔
      Normalizer.laurentSpan ℚ (fun _ : Unit => (T (-2) : ℚ[T;T⁻¹])) (Set.Iic 0))) ≠ 0 := by
  let c : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ :=
    { toFun := fun p => p.coeff (-1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hleft : Normalizer.laurentSpan ℚ
      (fun _ : Unit => (T 0 : ℚ[T;T⁻¹])) (Set.Ici 0) ≤ c.ker := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, n, hn, rfl⟩
    change ((T n : ℚ[T;T⁻¹]) • T 0).coeff (-1) = 0
    simp only [smul_eq_mul, ← T_add, add_zero, T_apply]
    exact ite_eq_right (by change 0 ≤ n at hn; omega)
  have hright : Normalizer.laurentSpan ℚ
      (fun _ : Unit => (T (-2) : ℚ[T;T⁻¹])) (Set.Iic 0) ≤ c.ker := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, n, hn, rfl⟩
    change ((T n : ℚ[T;T⁻¹]) • T (-2)).coeff (-1) = 0
    simp only [smul_eq_mul, ← T_add, T_apply]
    exact ite_eq_right (by change n ≤ 0 at hn; omega)
  intro hz
  have hm := (Submodule.Quotient.mk_eq_zero _).mp hz
  have hc := sup_le hleft hright hm
  change (T (-1) : ℚ[T;T⁻¹]).coeff (-1) = 0 at hc
  norm_num at hc

end LaurentQuotientChecks


section ProjectiveChartChecks
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Normalizer AlgebraicGeometry CategoryTheory TopologicalSpace

-- The specified zero section gives an empty second chart, so the
-- construction does not accidentally assert every chosen function is nonconstant.
example : projectiveLineOfSection (𝟙 (Spec (.of ℚ))) 0 ⁻¹ᵁ
    projectiveLineChart ℚ 1 = ⊥ := by
  rw [projectiveLineOfSection_preimage_one]
  exact Scheme.basicOpen_zero _ _

-- The unit section lands in both actual homogeneous-coordinate charts.
example : projectiveLineOfSection (𝟙 (Spec (.of ℚ))) 1 ⁻¹ᵁ
    (projectiveLineChart ℚ 0 ⊓ projectiveLineChart ℚ 1) = ⊤ := by
  rw [Scheme.Hom.preimage_inf, projectiveLineOfSection_preimage_zero,
    projectiveLineOfSection_preimage_one]
  simp

-- Actual chart sections give zero cohomology classes on their overlap.
example (F : (projectiveLine ℚ).Modules)
    (s : Γ(F, projectiveLinePullbackChart (𝟙 (projectiveLine ℚ)) 0))
    (t : Γ(F, projectiveLinePullbackChart (𝟙 (projectiveLine ℚ)) 1)) :
    twoOpenSectionδ (projectiveLineToSpec ℚ) _ _
      (projectiveLinePullbackChart_cover (𝟙 (projectiveLine ℚ))) F
      (F.val.map (homOfLE inf_le_left).op s -
        F.val.map (homOfLE inf_le_right).op t) = 0 :=
  (twoOpenSectionδ_eq_zero_iff _ _ _ _ _ _).mpr ⟨s, t, rfl⟩

end ProjectiveChartChecks

section ProjectiveCoordinateChecks
attribute [local instance] MvPolynomial.gradedAlgebra
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
open Normalizer AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- The actual inverse coordinate works over a ring with zero divisors.
example : projectiveOverlapLaurentEquiv (ZMod 4)
    (projectiveChartToOverlap (ZMod 4) 1 (projectiveChartCoordinate (ZMod 4) 1 ^ 3)) =
      LaurentPolynomial.T (-3) := by
  rw [map_pow, map_pow, projectiveOverlapLaurentEquiv_coordinate_one, LaurentPolynomial.T_pow]
  norm_num

-- A polynomial section on the second actual chart acquires negative powers on the overlap.
example : projectiveLineOverlapSectionsLaurentEquiv ℤ
    ((projectiveLine ℤ).presheaf.map (homOfLE (projectiveLineOverlap_le ℤ 1)).op
      ((projectiveLineChartSectionsPolynomialEquiv ℤ 1).symm
        (Polynomial.X ^ 2 + Polynomial.C 3))) =
      LaurentPolynomial.T (-2) + LaurentPolynomial.C 3 := by
  rw [projectiveLineSections_restrict_one, RingEquiv.apply_symm_apply]
  simp only [map_add, map_pow, Polynomial.toLaurent_X, Polynomial.toLaurent_C,
    LaurentPolynomial.invert_C, LaurentPolynomial.invert_T, LaurentPolynomial.T_pow]
  norm_num

-- Actual sheaf cohomology vanishes without assuming it in a comparison interface.
example : Subsingleton (Sheaf.H
    ((schemeModulesToAbelianSheaves (projectiveLine ℚ)).obj
      (SheafOfModules.unit (projectiveLine ℚ).ringCatSheaf)) 1) :=
  projectiveLine_unit_H1_subsingleton ℚ

-- The cohomology result includes positive characteristic with the actual structure-field action.
example :
    letI := schemeModuleCohomologyModule (k := ZMod 5) (projectiveLineToSpec (ZMod 5))
      (SheafOfModules.unit (projectiveLine (ZMod 5)).ringCatSheaf) 1
    Module.Finite (ZMod 5) (Sheaf.H
      ((schemeModulesToAbelianSheaves (projectiveLine (ZMod 5))).obj
        (SheafOfModules.unit (projectiveLine (ZMod 5)).ringCatSheaf)) 1) :=
  projectiveLine_unit_H1_finite (ZMod 5)

end ProjectiveCoordinateChecks

section FiniteMapCohomologyChecks
open Normalizer AlgebraicGeometry CategoryTheory LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Actual Laurent coefficients pull back through the original structure map.
example {X : Scheme} (f : X ⟶ projectiveLine ℚ) :
    finiteMapLaurentHom f (C (3 / 2 : ℚ)) =
      schemeConstantAt (f ≫ projectiveLineToSpec ℚ) (finiteMapOverlap f) (3 / 2) :=
  finiteMapLaurentHom_C f _

-- No reducedness or integrality is required, including for a closed subscheme of P1.
example {X : Scheme} (f : X ⟶ projectiveLine ℚ) [IsClosedImmersion f] :
    letI := schemeModuleCohomologyModule (f ≫ projectiveLineToSpec ℚ)
      (SheafOfModules.unit X.ringCatSheaf) 1
    Module.Finite ℚ (Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (SheafOfModules.unit X.ringCatSheaf)) 1) :=
  finiteMap_projectiveLine_unit_H1_finite f

-- The finite-map argument recovers finiteness on the actual projective line itself.
example :
    letI := schemeModuleCohomologyModule (projectiveLineToSpec ℚ)
      (SheafOfModules.unit (projectiveLine ℚ).ringCatSheaf) 1
    Module.Finite ℚ (Sheaf.H ((schemeModulesToAbelianSheaves (projectiveLine ℚ)).obj
      (SheafOfModules.unit (projectiveLine ℚ).ringCatSheaf)) 1) := by
  simpa only [Category.id_comp] using finiteMap_projectiveLine_unit_H1_finite (𝟙 (projectiveLine ℚ))

end FiniteMapCohomologyChecks

section CurveMapExistenceChecks
open Normalizer AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- The constant finite-map construction retains the doubled point's nilpotent.
example :
    let R := AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ 2)
    let p := Spec.map (CommRingCat.ofHom (algebraMap ℚ R))
    ∃ f : Spec (.of R) ⟶ projectiveLine ℚ,
      f ≫ projectiveLineToSpec ℚ = p ∧ IsFinite f := by
  let R := AdjoinRoot ((Polynomial.X : Polynomial ℚ) ^ 2)
  let p : Spec (.of R) ⟶ Spec (.of ℚ) := Spec.map (CommRingCat.ofHom (algebraMap ℚ R))
  have : Module.Finite ℚ R := (Polynomial.monic_X.pow 2).finite_adjoinRoot
  have : IsFinite p := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  have : DiscreteTopology (Spec (.of R)) := finiteScheme_discreteTopology p
  exact proper_dimZero_exists_finite_projectiveLine p
    (topologicalKrullDim_zero_of_discreteTopology _)

-- The smooth case uses the original scalar action and derives normality;
-- no local-normality, map-existence or H1-finiteness premise is supplied.
example {k : Type} [Field k] {X : Scheme} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [IsProper p] [Smooth p]
    (hdim : topologicalKrullDim X ≤ 1) :
    letI := schemeModuleCohomologyModule p (SheafOfModules.unit X.ringCatSheaf) 1
    Module.Finite k (Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (SheafOfModules.unit X.ringCatSheaf)) 1) :=
  properSmoothCurve_unit_H1_finite p hdim

-- One possibly singular point is allowed; normality at that point is absent.
example {X : Scheme} [IsIntegral X] (p : X ⟶ Spec (.of ℚ)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 1) (x : X)
    (h : ∀ y : X, y ≠ x → IsIntegrallyClosed (X.presheaf.stalk y)) :
    ∃ f : X ⟶ projectiveLine ℚ, f ≫ projectiveLineToSpec ℚ = p ∧ IsFinite f :=
  properCurve_exists_finite_projectiveLine_of_normalAwayPoint p hdim x h

end CurveMapExistenceChecks
