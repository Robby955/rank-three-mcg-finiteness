import Normalizer.NormalizerBilinear
import Normalizer.NormalizerStalkBracket
import Normalizer.NormalizerStalkCharacter
import Normalizer.FanInCompatibility

/-! The intrinsic stalk bracket agrees with the bracket transported through
the actual normalizer-quotient comparison. The two stalk-character
constructions agree with its scalar-action character as well. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}} (E : X.Modules) (I : E.Submodule)
  (action : ∀ V, E.val.obj V → E.val.obj V →ₗ[X.ringCatSheaf.obj.obj V] E.val.obj V)
  (action_res : ∀ {V W} (f : V ⟶ W) (m s : E.val.obj V),
    E.val.map f (action V m s) = action W (E.val.map f m) (E.val.map f s))
  (action_smul_right : ∀ V (a : X.ringCatSheaf.obj.obj V) (m s : E.val.obj V),
    action V (a • m) s = a • action V m s)
  (habelian : ∀ V (s m : E.val.obj V), s ∈ I.obj V → m ∈ I.obj V →
    action V m s = 0)
  (jacobi : ∀ V (a b m : E.val.obj V),
    action V m (action V b a) =
      action V (action V m b) a - action V (action V m a) b)
  (skew : ∀ V (a b : E.val.obj V), action V b a = -action V a b)
  (x : X) {L : Type u} [LieRing L] [LieAlgebra (X.presheaf.stalk x) L]
  (e : E.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] L)
  (he : ∀ (V : X.Opens) (hxV : x ∈ V) (m s : Γ(E, V)),
    e (E.presheaf.germ V x hxV (action (op V) m s)) =
      ⁅e (E.presheaf.germ V x hxV s), e (E.presheaf.germ V x hxV m)⁆)
  (U : X.Opens) (hxU : x ∈ U)
  (t : (SheafOfModules.unit X.ringCatSheaf).over U ≅ I.toSheafOfModules.over U)

private abbrev quotientModule : X.Modules :=
  normalizerQuotientSheaf E I action action_res habelian
local notation "Q" => quotientModule E I action action_res habelian
local notation "θ" => schemeNormalizerQuotientStalkEquiv E I action action_res
  action_smul_right habelian x e he U hxU t

/-- The actual normalizer-quotient comparison preserves the independently
constructed intrinsic bracket on every pair of stalk elements. -/
theorem normalizerQuotientStalkEquiv_intrinsic_bracket (a b : (Q).presheaf.stalk x) :
    θ (normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew x a b) =
      ⁅θ a, θ b⁆ := by
  obtain ⟨V, hxV, s, rfl⟩ := (Q).presheaf.exists_germ_eq a
  obtain ⟨W, hWV, hxW, r, rfl⟩ := (Q).presheaf.exists_le_germ_eq b hxV
  rw [← (Q).presheaf.germ_res_apply (homOfLE hWV) x hxW s,
    normalizerQuotientStalkBilinear_germ]
  exact schemeNormalizerQuotientStalkEquiv_bracket E I action action_res action_smul_right
    habelian jacobi skew x e he U hxU t W hxW _ r

/-- The actual quotient-stalk comparison is a Lie algebra equivalence for
the intrinsic stalk Lie algebra, not just for a transported bracket. -/
def normalizerQuotientStalkLieEquiv
    (alternating : ∀ V (a : E.val.obj V), action V a a = 0) :
    letI := normalizerQuotientStalkLieRing E I action action_res habelian jacobi skew alternating x
    letI := normalizerQuotientStalkLieAlgebra E I action action_res habelian jacobi skew alternating x
    (Q).presheaf.stalk x ≃ₗ⁅X.presheaf.stalk x⁆
      (frameLine (R := X.presheaf.stalk x) (e (schemeLineFrameGerm E I x U hxU t))).normalizer ⧸
        frameIdeal (e (schemeLineFrameGerm E I x U hxU t)) := by
  letI := normalizerQuotientStalkLieRing E I action action_res habelian jacobi skew alternating x
  letI := normalizerQuotientStalkLieAlgebra E I action action_res habelian jacobi skew alternating x
  refine { θ with map_lie' := ?_ }
  intro a b
  exact normalizerQuotientStalkEquiv_intrinsic_bracket E I action action_res action_smul_right
    habelian jacobi skew x e he U hxU t a b

variable {ι : Type u} (V : ι → X.Opens) (hcover : iSup V = ⊤)
  (triv : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (V i) ≅
    I.toSheafOfModules.over (V i)) (i : ι) (hxi : x ∈ V i)

local notation "χ" => quotientCharacterOfTrivializations E I action action_res
  (fun W a b => @mul_comm (X.presheaf.obj W) _ a b)
  action_smul_right habelian V hcover triv
local notation "mₓ" => schemeLineFrameGerm E I x (V i) hxi (triv i)

/-- The intrinsic local-ring-valued stalk character is the actual scalar
action character under the constructed quotient-stalk comparison. -/
theorem normalizerQuotientStalkEquiv_intrinsic_character (z : (Q).presheaf.stalk x) :
    schemeModuleStalkCharacter Q χ x z =
      quotientFrameCharacter (e mₓ)
        (schemeLineFrameGerm_map_smul_injective E I x e (V i) hxi (triv i))
        (schemeNormalizerQuotientStalkEquiv E I action action_res action_smul_right
          habelian x e he (V i) hxi (triv i) z) := by
  rw [schemeModuleStalkCharacter_eq_stalkFunctional]
  exact schemeNormalizerQuotientStalkCharacter E I action action_res action_smul_right
    habelian V hcover triv x i hxi e he z

local notation "θᵢ" => schemeNormalizerQuotientStalkEquiv E I action action_res action_smul_right
  habelian x e he (V i) hxi (triv i)
local notation "λᵢ" => quotientFrameCharacter (e mₓ)
  (schemeLineFrameGerm_map_smul_injective E I x e (V i) hxi (triv i))

/-- A boundary identity for the intrinsic stalk bracket and character
passes through the constructed normalizer equivalence. Bracket and
character compatibility are proved above rather than assumed here. -/
theorem normalizerQuotientStalkEquiv_boundary_identity
    (W : Submodule (X.presheaf.stalk x) ((Q).presheaf.stalk x))
    (hlaw : ∀ a ∈ W, ∀ b ∈ W,
      normalizerQuotientStalkBilinear E I action action_res habelian jacobi skew x a b =
        schemeModuleStalkCharacter Q χ x a • b - schemeModuleStalkCharacter Q χ x b • a) :
    ∀ a ∈ W.map (θᵢ).toLinearMap, ∀ b ∈ W.map (θᵢ).toLinearMap,
      ⁅a, b⁆ = λᵢ a • b - λᵢ b • a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  change ⁅θᵢ a, θᵢ b⁆ = λᵢ (θᵢ a) • θᵢ b - λᵢ (θᵢ b) • θᵢ a
  rw [← normalizerQuotientStalkEquiv_intrinsic_bracket E I action action_res action_smul_right
    habelian jacobi skew x e he (V i) hxi (triv i) a b, hlaw a ha b hb,
    map_sub, map_smul, map_smul,
    normalizerQuotientStalkEquiv_intrinsic_character E I action action_res action_smul_right
      habelian x e he V hcover triv i hxi a,
    normalizerQuotientStalkEquiv_intrinsic_character E I action action_res action_smul_right
      habelian x e he V hcover triv i hxi b]

end Normalizer
