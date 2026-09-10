import Normalizer.SmoothRegularity
import Normalizer.SaturatedStalkQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! Regular actual stalks and saturated bundle quotients on smooth curves. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

/-- The actual local rings of a scheme smooth over a field are regular.
An affine neighborhood is chosen and its prime localization is compared
with the actual structure-sheaf stalk. -/
theorem smoothScheme_stalk_isRegularLocalRing
    (k : Type u) [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) [Smooth s] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  let := ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField k)).toField
  let φ := (s.appLE ⊤ U (by simp)).hom
  let : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) := φ.toAlgebra
  have : Algebra.Smooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) :=
    s.smooth_appLE (isAffineOpen_top _) hU (by simp)
  let p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have : IsRegularLocalRing (Localization.AtPrime p) :=
    regularLocal_localization_of_smooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) p
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (X.presheaf.stalk x)).toRingEquiv

/-- A scalar-saturated inclusion of bundles with finite free covers on
an integral smooth scheme of dimension at most one has locally free
actual cokernel. Regularity of the actual stalks is derived from smoothness. -/
theorem smoothCurve_saturatedFiniteBundle_cokernel_isLocallyFree
    (k : Type u) [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) [Smooth s] [IsIntegral X]
    {M E : X.Modules} (f : M ⟶ E) [Mono f]
    {A B : Type u} (U : A → X.Opens) (hU : IsOpenCover U)
    (V : B → X.Opens) (hV : IsOpenCover V)
    (I : A → Type u) (J : B → Type u) [∀ a, Finite (I a)] [∀ b, Finite (J b)]
    (eM : ∀ a, M.over (U a) ≅ SheafOfModules.free (I a))
    (eE : ∀ b, E.over (V b) ≅ SheafOfModules.free (J b))
    (hdim : Order.krullDim X ≤ 1)
    (hsat : ∀ (x : X) (r : X.presheaf.stalk x), r ≠ 0 → ∀ v : E.presheaf.stalk x,
      r • v ∈ LinearMap.range (schemeModuleStalkMap f x) →
      v ∈ LinearMap.range (schemeModuleStalkMap f x)) :
    (cokernel f).IsLocallyFree :=
  saturatedFiniteBundle_cokernel_isLocallyFree f U hU V hV I J eM eE
    (smoothScheme_stalk_isRegularLocalRing k s) hdim hsat

end Normalizer
