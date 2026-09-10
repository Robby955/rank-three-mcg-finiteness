import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Constant global functions on integral proper schemes over algebraically
closed fields, using the actual structure morphism and its global sections. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u

/-- The canonical constants map induced by a scheme's structure morphism. -/
def schemeConstants (k : Type u) [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appTop).hom

/-- On an integral proper scheme over an algebraically closed field,
the actual constants map on global functions is bijective. -/
theorem properScheme_constants_bijective (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of k)) [IsProper s] :
    Function.Bijective (schemeConstants k s) := by
  apply IsAlgClosed.ringHom_bijective_of_isIntegral
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed s

/-- Every global function has a unique scalar value in the base field. -/
theorem properScheme_global_function_constant (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of k)) [IsProper s] (a : Γ(X, ⊤)) :
    ∃! c : k, schemeConstants k s c = a := by
  obtain ⟨c, hc⟩ := (properScheme_constants_bijective k s).surjective a
  exact ⟨c, hc, fun d hd ↦ (properScheme_constants_bijective k s).injective (hd.trans hc.symm)⟩

/-- The value of any actual sheaf character on a global section is a
unique scalar, with no scalar-valuedness assumption on the character. -/
theorem properScheme_global_character_constant (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of k)) [IsProper s]
    (K : X.Modules) (χ : K ⟶ SheafOfModules.unit X.ringCatSheaf)
    (x : Γ(K, ⊤)) :
    ∃! c : k, schemeConstants k s c = χ.app ⊤ x :=
  properScheme_global_function_constant k s (χ.app ⊤ x)

end Normalizer


/-! Global functions on actual integral schemes universally closed over
an algebraically closed field. Constancy is proved from the structure
morphism, rather than supplied as an isomorphism of section rings. -/

noncomputable section
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual map from base-field constants to global regular functions. -/
def schemeConstantMap (f : X ⟶ Spec (.of k)) : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

/-- Universal closedness and integrality over an algebraically closed
field make the actual constant-function map bijective. -/
theorem schemeConstantMap_bijective [IsAlgClosed k] [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [UniversallyClosed f] :
    Function.Bijective (schemeConstantMap f) := by
  apply IsAlgClosed.ringHom_bijective_of_isIntegral
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed f

/-- The constant-function ring isomorphism, constructed from geometry. -/
def properConstantEquiv [IsAlgClosed k] [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [UniversallyClosed f] : k ≃+* Γ(X, ⊤) :=
  RingEquiv.ofBijective (schemeConstantMap f) (schemeConstantMap_bijective f)

/-- Every actual global regular function is a unique base-field constant. -/
theorem proper_global_function_constant [IsAlgClosed k] [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [UniversallyClosed f] (s : Γ(X, ⊤)) :
    ∃! a : k, schemeConstantMap f a = s := by
  refine ⟨(properConstantEquiv f).symm s, (properConstantEquiv f).apply_symm_apply s, ?_⟩
  intro a ha
  exact (schemeConstantMap_bijective f).injective
    (ha.trans ((properConstantEquiv f).apply_symm_apply s).symm)

/-- Constants restricted to an actual open subscheme. -/
def schemeConstantAt (f : X ⟶ Spec (.of k)) (U : X.Opens) : k →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp (schemeConstantMap f)

/-- The same global scalar represents the function on every open. -/
theorem proper_global_function_restrict [IsAlgClosed k] [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [UniversallyClosed f] (s : Γ(X, ⊤)) (U : X.Opens) :
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s =
      schemeConstantAt f U ((properConstantEquiv f).symm s) := by
  change _ = X.presheaf.map _ (properConstantEquiv f ((properConstantEquiv f).symm s))
  rw [RingEquiv.apply_symm_apply]

end Normalizer
