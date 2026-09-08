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
