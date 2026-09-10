import Normalizer.SheafQuotientLie
import Normalizer.StalkBracket

/-! The constructed normalizer-quotient section bracket and its actual
stalk bracket, bundled over the scheme's section rings and local rings. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Opposite AlgebraicGeometry
universe u
variable {X : Scheme.{u}} (E : X.Modules)
  (I : (E : SheafOfModules X.ringCatSheaf).Submodule)
  (action : ∀ V, E.val.obj V → E.val.obj V →ₗ[X.ringCatSheaf.obj.obj V] E.val.obj V)
  (action_res : ∀ {V W} (f : V ⟶ W) (m x : E.val.obj V),
    E.val.map f (action V m x) = action W (E.val.map f m) (E.val.map f x))
  (habelian : ∀ V (x m : E.val.obj V), x ∈ I.obj V → m ∈ I.obj V →
    action V m x = 0)
  (jacobi : ∀ V (x y m : E.val.obj V),
    action V m (action V y x) =
      action V (action V m y) x - action V (action V m x) y)
  (skew : ∀ V (x y : E.val.obj V), action V y x = -action V x y)

private abbrev quotientModule : X.Modules :=
  normalizerQuotientSheaf E I action action_res habelian
local notation "K" => quotientModule E I action action_res habelian
local notation "br" => normalizerQuotientBracket E I action action_res habelian jacobi skew

/-- The existing bracket on actual normalizer-quotient sections is bilinear
over the actual commutative ring of sections. -/
def normalizerQuotientSectionBilinear (V : X.Opens) :
    Γ(K, V) →ₗ[Γ(X, V)] Γ(K, V) →ₗ[Γ(X, V)] Γ(K, V) where
  toFun a :=
    { toFun := br V a
      map_add' := normalizerQuotientBracket_add_right E I action action_res habelian jacobi skew V a
      map_smul' := fun r b =>
        normalizerQuotientBracket_smul_right E I action action_res habelian jacobi skew V r a b }
  map_add' a b := by
    ext c
    exact normalizerQuotientBracket_add_left E I action action_res habelian jacobi skew V a b c
  map_smul' r a := by
    ext b
    exact normalizerQuotientBracket_smul_left E I action action_res habelian jacobi skew V r a b

/-- Bundling bilinearity preserves the constructed quotient bracket. -/
theorem normalizerQuotientSectionBilinear_apply (V : X.Opens) (a b : Γ(K, V)) :
    normalizerQuotientSectionBilinear E I action action_res habelian jacobi skew V a b =
      br V a b := rfl

/-- The bundled operation commutes with actual sheaf restrictions. -/
theorem normalizerQuotientSectionBilinear_restrict (U V : X.Opens) (h : U ≤ V)
    (a b : Γ(K, V)) :
    (K).presheaf.map (homOfLE h).op
      (normalizerQuotientSectionBilinear E I action action_res habelian jacobi skew V a b) =
      normalizerQuotientSectionBilinear E I action action_res habelian jacobi skew U
        ((K).presheaf.map (homOfLE h).op a) ((K).presheaf.map (homOfLE h).op b) :=
  normalizerQuotientBracket_restrict E I action action_res habelian jacobi skew V U h a b

/-- The bracket on the actual normalizer-quotient stalk, constructed from
the sheaf quotient and its descended section operation. -/
def normalizerQuotientStalkBilinear (x : X) :
    (K).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      (K).presheaf.stalk x →ₗ[X.presheaf.stalk x] (K).presheaf.stalk x :=
  schemeModuleStalkBilinear K
    (normalizerQuotientSectionBilinear E I action action_res habelian jacobi skew)
    (normalizerQuotientSectionBilinear_restrict E I action action_res habelian jacobi skew) x

/-- The actual stalk bracket sends two germs to the germ of their
constructed normalizer-quotient section bracket. -/
theorem normalizerQuotientStalkBilinear_germ (x : X) (V : X.Opens) (hx : x ∈ V)
    (a b : Γ(K, V)) :
    normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew x
      ((K).presheaf.germ V x hx a) ((K).presheaf.germ V x hx b) =
        (K).presheaf.germ V x hx (br V a b) :=
  schemeModuleStalkBilinear_germ K _ _ x V hx a b

/-- Ambient alternation holds for the constructed actual quotient-stalk bracket. -/
theorem normalizerQuotientStalkBilinear_alternating
    (alternating : ∀ V (a : E.val.obj V), action V a a = 0)
    (x : X) (a : (K).presheaf.stalk x) :
    normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew x a a = 0 :=
  schemeModuleStalkBilinear_self_eq_zero K
    (normalizerQuotientSectionBilinear E I action action_res habelian jacobi skew)
    (normalizerQuotientSectionBilinear_restrict E I action action_res habelian jacobi skew)
    (normalizerQuotientBracket_alternating E I action action_res habelian jacobi skew alternating)
    x a

/-- Jacobi holds for the constructed actual quotient-stalk bracket. -/
theorem normalizerQuotientStalkBilinear_leibniz (x : X) (a b c : (K).presheaf.stalk x) :
    normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew x a
      (normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew x b c) =
    normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew x
      (normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew x a b) c +
    normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew x b
      (normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew x a c) := by
  apply schemeModuleStalkBilinear_leibniz K
    (normalizerQuotientSectionBilinear E I action action_res habelian jacobi skew)
    (normalizerQuotientSectionBilinear_restrict E I action action_res habelian jacobi skew) _ x a b c
  intro U s t v
  exact (eq_sub_iff_add_eq.mp
    (normalizerQuotientBracket_jacobi E I action action_res habelian jacobi skew U s t v)).symm

/-- The actual quotient stalk carries the Lie ring structure supplied by
the constructed bilinear bracket and proved section identities. -/
@[instance_reducible]
def normalizerQuotientStalkLieRing
    (alternating : ∀ V (a : E.val.obj V), action V a a = 0) (x : X) :
    LieRing ((K).presheaf.stalk x) where
  bracket a b := normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew x a b
  add_lie a b c := by
    exact congrArg (fun f => f c)
      ((normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew x).map_add a b)
  lie_add a b c :=
    (normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew x a).map_add b c
  lie_self := normalizerQuotientStalkBilinear_alternating
    E I action action_res habelian jacobi skew alternating x
  leibniz_lie := normalizerQuotientStalkBilinear_leibniz E I action action_res habelian jacobi skew x

/-- The constructed stalk Lie ring is a Lie algebra over its actual local ring. -/
@[instance_reducible]
def normalizerQuotientStalkLieAlgebra
    (alternating : ∀ V (a : E.val.obj V), action V a a = 0) (x : X) :
    letI := normalizerQuotientStalkLieRing E I action action_res habelian jacobi skew alternating x
    LieAlgebra (X.presheaf.stalk x) ((K).presheaf.stalk x) := by
  letI := normalizerQuotientStalkLieRing E I action action_res habelian jacobi skew alternating x
  exact { (inferInstance : Module (X.presheaf.stalk x) ((K).presheaf.stalk x)) with
    lie_smul := fun r a b =>
      (normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew x a).map_smul r b }

end Normalizer
