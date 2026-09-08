import Normalizer.LocalCharacterGluing
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! The normalizer subsheaf from actual sectionwise bracket operators.
`action V m x` denotes `[x,m]`. Linearity in x and compatibility with
restriction are explicit inputs. No local frame or normalizer sheaf is
assumed to exist. Testing on every smaller open makes restriction stability
intrinsic; locality is proved from the given subsheaf's sheaf condition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Opposite TopologicalSpace

universe u
variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  (E : SheafOfModules.{u} R) (I : E.Submodule)
  (action : ∀ V, E.val.obj V → E.val.obj V →ₗ[R.obj.obj V] E.val.obj V)
  (action_res : ∀ {V W} (f : V ⟶ W) (m x : E.val.obj V),
    E.val.map f (action V m x) = action W (E.val.map f m) (E.val.map f x))

private def normalizerPresheaf : E.val.Submodule where
  obj V := {
    carrier := {x | ∀ ⦃W⦄ (f : V ⟶ W) (m : E.val.obj W),
      m ∈ I.obj W → action W m (E.val.map f x) ∈ I.obj W}
    zero_mem' := by
      intro W f m hm
      simp
    add_mem' := by
      intro x y hx hy W f m hm
      simpa only [map_add] using (I.obj W).add_mem (hx f m hm) (hy f m hm)
    smul_mem' := by
      intro r x hx W f m hm
      rw [E.val.map_smul, map_smul]
      exact (I.obj W).smul_mem _ (hx f m hm) }
  map := by
    intro V W f x hx T g m hm
    have h := hx (f ≫ g) m hm
    simpa only [E.val.map_comp_apply, PresheafOfModules.restrictₛₗ_apply] using h

/-- The sections preserving a subsheaf on every smaller open form an actual
subsheaf. This is the normalizer when `action V m x = [x,m]`. -/
def normalizerSubsheaf : E.Submodule where
  toSubmodule := normalizerPresheaf E I action
  isSheaf := by
    intro V x hx W f m hm
    apply I.isSheaf (action W m (E.val.map f x))
    refine (Opens.grothendieckTopology X).superset_covering ?_
      ((Opens.grothendieckTopology X).pullback_stable f.unop hx)
    intro T g hg
    change E.val.map g.op (action W m (E.val.map f x)) ∈ I.obj (op T)
    rw [action_res]
    change E.val.map ((g ≫ f.unop).op) x ∈
      (normalizerPresheaf E I action).obj (op T) at hg
    have h := hg (𝟙 (op T)) (E.val.map g.op m) (I.map_mem g.op hm)
    simpa [E.val.map_comp_apply] using h

/-- Membership tests the action on the subsheaf after every restriction. -/
theorem mem_normalizerSubsheaf (V) (x : E.val.obj V) :
    x ∈ (normalizerSubsheaf E I action action_res).obj V ↔
      ∀ ⦃W⦄ (f : V ⟶ W) (m : E.val.obj W), m ∈ I.obj W →
        action W m (E.val.map f x) ∈ I.obj W := Iff.rfl

/-- In particular, normalizer sections act on sections of the subsheaf. -/
theorem normalizerSubsheaf_action (V) (x m : E.val.obj V)
    (hx : x ∈ (normalizerSubsheaf E I action action_res).obj V)
    (hm : m ∈ I.obj V) : action V m x ∈ I.obj V := by
  simpa using hx (𝟙 V) m hm

/-- An abelian subsheaf is contained in its normalizer. -/
theorem abelian_subsheaf_le_normalizer
    (habelian : ∀ V (x m : E.val.obj V), x ∈ I.obj V → m ∈ I.obj V →
      action V m x = 0) : I ≤ normalizerSubsheaf E I action action_res := by
  intro V x hx W f m hm
  rw [habelian W _ m (I.map_mem f hx) hm]
  exact (I.obj W).zero_mem

/-- The Jacobi identity makes the normalizer closed under the bracket.
Here `action V y x` is `[x,y]`, so the stated identity is `[[x,y],m]`. -/
theorem normalizerSubsheaf_bracket
    (jacobi : ∀ V (x y m : E.val.obj V),
      action V m (action V y x) =
        action V (action V m y) x - action V (action V m x) y)
    (V) (x y : E.val.obj V)
    (hx : x ∈ (normalizerSubsheaf E I action action_res).obj V)
    (hy : y ∈ (normalizerSubsheaf E I action action_res).obj V) :
    action V y x ∈ (normalizerSubsheaf E I action action_res).obj V := by
  intro W f m hm
  rw [action_res, jacobi]
  exact (I.obj W).sub_mem (hx f _ (hy f m hm)) (hy f _ (hx f m hm))

/-- On an open where a frame generates the subsheaf after every restriction,
normalizer membership is equivalent to testing that one frame. -/
theorem normalizerSubsheaf_frame_criterion
    (action_smul_right : ∀ V (r : R.obj.obj V) (m x : E.val.obj V),
      action V (r • m) x = r • action V m x)
    (V) (m x : E.val.obj V)
    (hframe : ∀ ⦃W⦄ (f : V ⟶ W),
      I.obj W = Submodule.span (R.obj.obj W) {E.val.map f m}) :
    x ∈ (normalizerSubsheaf E I action action_res).obj V ↔
      action V m x ∈ I.obj V := by
  constructor
  · intro hx
    apply normalizerSubsheaf_action E I action action_res V x m hx
    rw [hframe (𝟙 V)]
    simp
  · intro hx W f n hn
    rw [hframe f, Submodule.mem_span_singleton] at hn
    obtain ⟨a, rfl⟩ := hn
    rw [action_smul_right, ← action_res]
    exact (I.obj W).smul_mem a (I.map_mem f hx)

variable (habelian : ∀ V (x m : E.val.obj V), x ∈ I.obj V → m ∈ I.obj V →
  action V m x = 0)

/-- The actual inclusion of an abelian subsheaf into its normalizer. -/
def normalizerLineInclusion : I.toSheafOfModules ⟶
    (normalizerSubsheaf E I action action_res).toSheafOfModules :=
  ⟨PresheafOfModules.Submodule.homOfLE
    (abelian_subsheaf_le_normalizer E I action action_res habelian)⟩

/-- The quotient in the category of sheaves of modules, constructed as a
cokernel. Its sections are not defined to be quotients of section modules. -/
def normalizerQuotientSheaf : SheafOfModules.{u} R :=
  Limits.cokernel (normalizerLineInclusion E I action action_res habelian)

/-- A sheaf character killing the line descends through the actual sheaf
quotient by the cokernel universal property. -/
def descendNormalizerCharacter
    (χ : (normalizerSubsheaf E I action action_res).toSheafOfModules ⟶
      SheafOfModules.unit R)
    (hχ : normalizerLineInclusion E I action action_res habelian ≫ χ = 0) :
    normalizerQuotientSheaf E I action action_res habelian ⟶ SheafOfModules.unit R :=
  Limits.cokernel.desc _ χ hχ

/-- The descended character recovers the character before quotienting. -/
theorem descendNormalizerCharacter_fac
    (χ : (normalizerSubsheaf E I action action_res).toSheafOfModules ⟶
      SheafOfModules.unit R)
    (hχ : normalizerLineInclusion E I action action_res habelian ≫ χ = 0) :
    Limits.cokernel.π (normalizerLineInclusion E I action action_res habelian) ≫
      descendNormalizerCharacter E I action action_res habelian χ hχ = χ :=
  Limits.cokernel.π_desc _ _ _

/-- Descent is unique as a morphism of actual sheaves of modules. -/
theorem descendNormalizerCharacter_unique
    (χ : (normalizerSubsheaf E I action action_res).toSheafOfModules ⟶
      SheafOfModules.unit R)
    (hχ : normalizerLineInclusion E I action action_res habelian ≫ χ = 0)
    (ψ : normalizerQuotientSheaf E I action action_res habelian ⟶ SheafOfModules.unit R)
    (hψ : Limits.cokernel.π (normalizerLineInclusion E I action action_res habelian) ≫ ψ = χ) :
    ψ = descendNormalizerCharacter E I action action_res habelian χ hχ := by
  apply (cancel_epi (Limits.cokernel.π
    (normalizerLineInclusion E I action action_res habelian))).mp
  exact hψ.trans (descendNormalizerCharacter_fac E I action action_res habelian χ hχ).symm

private theorem sheafModule_zero_of_local
    (A B : SheafOfModules.{u} R) (f : A ⟶ B)
    {ι : Type u} (U : ι → Opens X) (hcover : iSup U = ⊤)
    (hf : ∀ i (V : Opens X) (_ : V ≤ U i) (s : A.val.obj (op V)),
      f.val.app (op V) s = 0) : f = 0 := by
  apply SheafOfModules.Hom.ext
  ext V s
  let BS : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨B.val.presheaf, B.isSheaf⟩
  apply BS.eq_of_locally_eq' (fun i => V.unop ⊓ U i) V.unop
    (fun _ => homOfLE inf_le_left) (by rw [← inf_iSup_eq, hcover, inf_top_eq])
  intro i
  change B.val.map (homOfLE inf_le_left).op (f.val.app V s) =
    B.val.map (homOfLE inf_le_left).op 0
  rw [map_zero, ← PresheafOfModules.naturality_apply]
  exact hf i _ inf_le_right _

variable {ι : Type u} (U : ι → Opens X) (hcover : iSup U = ⊤)
  (localChar : ∀ i (V : Opens X), V ≤ U i →
    (((normalizerSubsheaf E I action action_res).toSheafOfModules)).val.obj (op V) →ₗ[R.obj.obj (op V)] ((SheafOfModules.unit R)).val.obj (op V))
  (char_res : ∀ i (V W : Opens X) (h : V ≤ W) (k : W ≤ U i)
    (s : (((normalizerSubsheaf E I action action_res).toSheafOfModules)).val.obj (op W)),
    ((SheafOfModules.unit R)).val.restrictₛₗ (homOfLE h).op (localChar i W k s) =
      localChar i V (h.trans k) ((((normalizerSubsheaf E I action action_res).toSheafOfModules)).val.restrictₛₗ (homOfLE h).op s))
  (char_agree : ∀ i j (V : Opens X) (hi : V ≤ U i) (hj : V ≤ U j)
    (s : (((normalizerSubsheaf E I action action_res).toSheafOfModules)).val.obj (op V)), localChar i V hi s = localChar j V hj s)

/-- A global character on the constructed normalizer, obtained from
compatible local action maps by actual sheaf gluing. -/
def gluedNormalizerCharacter : ((normalizerSubsheaf E I action action_res).toSheafOfModules) ⟶ (SheafOfModules.unit R) :=
  glueLocalModuleMorphisms ((normalizerSubsheaf E I action action_res).toSheafOfModules) (SheafOfModules.unit R) U hcover localChar char_res char_agree

/-- Vanishing on local line sections implies vanishing on the entire
line subsheaf. No global vanishing condition is assumed. -/
theorem gluedNormalizerCharacter_kills_line
    (local_zero : ∀ i (V : Opens X) (h : V ≤ U i)
      (s : I.toSheafOfModules.val.obj (op V)),
      localChar i V h (((normalizerLineInclusion E I action action_res habelian)).val.app (op V) s) = 0) :
    (normalizerLineInclusion E I action action_res habelian) ≫ gluedNormalizerCharacter E I action action_res U hcover localChar
      char_res char_agree = 0 := by
  apply sheafModule_zero_of_local _ _ _ U hcover
  intro i V h s
  change (gluedNormalizerCharacter E I action action_res U hcover localChar
    char_res char_agree).val.app (op V) (((normalizerLineInclusion E I action action_res habelian)).val.app (op V) s) = 0
  rw [gluedNormalizerCharacter, glueLocalModuleMorphisms_local ((normalizerSubsheaf E I action action_res).toSheafOfModules) (SheafOfModules.unit R) U hcover
    localChar char_res char_agree i V h]
  exact local_zero i V h s

/-- Compatible local normalizer characters that kill the local line
construct a character on the actual sheaf quotient. -/
def gluedNormalizerQuotientCharacter
    (local_zero : ∀ i (V : Opens X) (h : V ≤ U i)
      (s : I.toSheafOfModules.val.obj (op V)),
      localChar i V h (((normalizerLineInclusion E I action action_res habelian)).val.app (op V) s) = 0) :
    normalizerQuotientSheaf E I action action_res habelian ⟶ (SheafOfModules.unit R) :=
  descendNormalizerCharacter E I action action_res habelian
    (gluedNormalizerCharacter E I action action_res U hcover localChar char_res char_agree)
    (gluedNormalizerCharacter_kills_line E I action action_res habelian
      U hcover localChar char_res char_agree local_zero)

/-- The quotient character agrees with the prescribed coefficient on each
local normalizer lift. This uses a genuine sheaf-quotient projection. -/
theorem gluedNormalizerQuotientCharacter_local
    (local_zero : ∀ i (V : Opens X) (h : V ≤ U i)
      (s : I.toSheafOfModules.val.obj (op V)),
      localChar i V h (((normalizerLineInclusion E I action action_res habelian)).val.app (op V) s) = 0)
    (i : ι) (V : Opens X) (h : V ≤ U i) (s : (((normalizerSubsheaf E I action action_res).toSheafOfModules)).val.obj (op V)) :
    (gluedNormalizerQuotientCharacter E I action action_res habelian U hcover
      localChar char_res char_agree local_zero).val.app (op V)
        ((Limits.cokernel.π (normalizerLineInclusion E I action action_res habelian)).val.app (op V) s) = localChar i V h s := by
  have hf := descendNormalizerCharacter_fac E I action action_res habelian
    (gluedNormalizerCharacter E I action action_res U hcover localChar char_res char_agree)
    (gluedNormalizerCharacter_kills_line E I action action_res habelian
      U hcover localChar char_res char_agree local_zero)
  have hs := congrArg (fun f => f.val.app (op V) s) hf
  exact hs.trans (glueLocalModuleMorphisms_local ((normalizerSubsheaf E I action action_res).toSheafOfModules) (SheafOfModules.unit R) U hcover localChar
    char_res char_agree i V h s)

end Normalizer
