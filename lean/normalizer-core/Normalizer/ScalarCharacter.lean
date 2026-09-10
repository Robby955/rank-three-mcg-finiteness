import Normalizer.ProperConstants
import Normalizer.TrivializedCharacter

/-! The scalar character induced by the actual structure morphism, with
its compatibility on smaller opens. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u

/-- The actual global character with its codomain exposed as the ring of
global functions. -/
def schemeGlobalCharacter {X : Scheme.{u}} (K : X.Modules)
    (χ : K ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Γ(K, ⊤) →ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
  (χ.val.app (op ⊤)).hom

/-- The base-field action on global sections induced by the structure map. -/
@[instance_reducible]
def schemeGlobalSectionsModule (k : Type u) [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) (K : X.Modules) : Module k Γ(K, ⊤) :=
  Module.compHom Γ(K, ⊤) (schemeConstants k s)

/-- The canonical constants isomorphism, retaining its actual ring map. -/
def properSchemeConstantEquiv (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of k)) [IsProper s] : k ≃+* Γ(X, ⊤) :=
  RingEquiv.ofBijective (schemeConstants k s) (properScheme_constants_bijective k s)

/-- The actual global sheaf character, made linear over the base field.
Its scalar action is the one induced by the same structure morphism. -/
def properSchemeScalarCharacter (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of k)) [IsProper s]
    (K : X.Modules) (χ : K ⟶ SheafOfModules.unit X.ringCatSheaf) :
    letI := schemeGlobalSectionsModule k s K
    Γ(K, ⊤) →ₗ[k] k := by
  letI := schemeGlobalSectionsModule k s K
  let e := properSchemeConstantEquiv k s
  refine { toFun := fun x ↦ e.symm (χ.app ⊤ x), map_add' := ?_, map_smul' := ?_ }
  · intro x y
    simp only [map_add]
  · intro c x
    change e.symm (χ.app ⊤ (schemeConstants k s c • x)) = c * e.symm (χ.app ⊤ x)
    let a : Γ(X, ⊤) := χ.app ⊤ x
    have hχ : (χ.app ⊤ (schemeConstants k s c • x) : Γ(X, ⊤)) =
        schemeConstants k s c * a := Scheme.Modules.Hom.app_smul χ _ _
    rw [hχ]
    change e.symm (e c * a) = c * e.symm a
    rw [map_mul, e.symm_apply_apply]

/-- Mapping the scalar character back to global functions recovers the
original sheaf character, without changing its values. -/
theorem properSchemeScalarCharacter_spec (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of k)) [IsProper s]
    (K : X.Modules) (χ : K ⟶ SheafOfModules.unit X.ringCatSheaf) (x : Γ(K, ⊤)) :
    schemeConstants k s (properSchemeScalarCharacter k s K χ x) = χ.app ⊤ x :=
  (properSchemeConstantEquiv k s).apply_symm_apply _

/-- The scalar character agrees with the actual sheaf character after
restriction to every open, as needed by the local overlap calculation. -/
theorem properSchemeScalarCharacter_restrict (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of k)) [IsProper s]
    (K : X.Modules) (χ : K ⟶ SheafOfModules.unit X.ringCatSheaf)
    (x : Γ(K, ⊤)) (V : X.Opens) :
    χ.app V (K.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op x) =
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (schemeConstants k s (properSchemeScalarCharacter k s K χ x)) := by
  rw [properSchemeScalarCharacter_spec]
  exact (PresheafOfModules.naturality_apply χ.val
    (homOfLE (show V ≤ ⊤ from le_top)).op x)

/-- On any local lift of a global quotient section, the actual character
value is the restriction of its uniquely determined base-field scalar. -/
theorem properSchemeScalarCharacter_local_lift (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of k)) [IsProper s]
    {N K : X.Modules} (π : N ⟶ K) (χ : K ⟶ SheafOfModules.unit X.ringCatSheaf)
    (x : Γ(K, ⊤)) (V : X.Opens) (a : Γ(N, V))
    (ha : π.app V a = K.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op x) :
    (π ≫ χ).app V a = X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
      (schemeConstants k s (properSchemeScalarCharacter k s K χ x)) := by
  change χ.app V (π.app V a) = _
  rw [ha]
  exact properSchemeScalarCharacter_restrict k s K χ x V

section ActualNormalizer

variable (k : Type u) [Field k] [IsAlgClosed k]
  {X : Scheme.{u}} [IsIntegral X]
  (s : X ⟶ Spec (CommRingCat.of k)) [IsProper s]
  (E : X.Modules) (I : E.Submodule)
  (action : ∀ V, E.val.obj V → E.val.obj V →ₗ[X.ringCatSheaf.obj.obj V] E.val.obj V)
  (action_res : ∀ {V W} (f : V ⟶ W) (m x : E.val.obj V),
    E.val.map f (action V m x) = action W (E.val.map f m) (E.val.map f x))
  (ring_comm : ∀ V (a b : X.ringCatSheaf.obj.obj V), a * b = b * a)
  (action_smul_right : ∀ V (a : X.ringCatSheaf.obj.obj V) (m x : E.val.obj V),
    action V (a • m) x = a • action V m x)
  (habelian : ∀ V (x m : E.val.obj V), x ∈ I.obj V → m ∈ I.obj V → action V m x = 0)
  {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
  (triv : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅
    I.toSheafOfModules.over (U i))

local notation "Kq" => normalizerQuotientSheaf E I action action_res habelian
local notation "chiq" => quotientCharacterOfTrivializations E I action action_res
  ring_comm action_smul_right habelian U hcover triv
local notation "piq" => Limits.cokernel.π (normalizerLineInclusion E I action action_res habelian)

/-- For the constructed normalizer quotient itself, a local lift acts on
the line by the restriction of the global base-field scalar character. -/
theorem properNormalizerScalarCharacter_action
    (x : Γ(Kq, ⊤)) (i : ι) (V : X.Opens) (hV : V ≤ U i)
    (a : (normalizerSubsheaf E I action action_res).obj (op V)) (m : I.obj (op V))
    (ha : (piq).val.app (op V) a =
      (Scheme.Modules.presheaf Kq).map (homOfLE (show V ≤ ⊤ from le_top)).op x) :
    action (op V) m a.val =
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (schemeConstants k s (properSchemeScalarCharacter k s Kq chiq x)) •
          (m : E.val.obj (op V)) := by
  have haction := quotientCharacterOfTrivializations_action E I action action_res
    ring_comm action_smul_right habelian U hcover triv i V hV a m
  change action (op V) m a.val = (chiq).val.app (op V) ((piq).val.app (op V) a) •
    (m : E.val.obj (op V)) at haction
  have hc := properSchemeScalarCharacter_restrict k s Kq chiq x V
  change (chiq).val.app (op V) ((Scheme.Modules.presheaf Kq).map
    (homOfLE (show V ≤ ⊤ from le_top)).op x) = _ at hc
  rw [ha, hc] at haction
  exact haction

end ActualNormalizer

end Normalizer
