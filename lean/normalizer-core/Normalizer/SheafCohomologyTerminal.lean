import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! The cohomology presheaf evaluated at a terminal object agrees with actual
sheaf cohomology, via the canonical free-representable/constant-sheaf comparison. -/

noncomputable section
namespace Normalizer
open CategoryTheory Limits Opposite Abelian
universe w v u
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {T : C} (hT : IsTerminal T)

/-- The free abelian presheaf represented by a terminal object is the constant
integer presheaf. Every representable generator maps to the integer one. -/
def terminalFreeAbelianPresheafIso :
    yoneda.obj T ⋙ AddCommGrpCat.free ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)) := by
  letI (U : C) : Unique (U ⟶ T) :=
    ⟨⟨hT.from U⟩, fun f => hT.hom_ext f (hT.from U)⟩
  refine NatIso.ofComponents (fun U =>
    ((FreeAbelianGroup.uniqueEquiv (U.unop ⟶ T)).trans
      AddEquiv.ulift.symm).toAddCommGrpIso) ?_
  intro U V f
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro g
  change ULift.up (FreeAbelianGroup.lift (fun _ : V.unop ⟶ T => (1 : ℤ))
    (FreeAbelianGroup.map (fun b => f.unop ≫ b) (FreeAbelianGroup.of g))) =
      ULift.up (FreeAbelianGroup.lift (fun _ : U.unop ⟶ T => (1 : ℤ))
        (FreeAbelianGroup.of g))
  simp

variable [HasSheafify J AddCommGrpCat.{v}]

/-- Sheafification identifies the actual free abelian sheaf represented by the
terminal object with the actual constant integer sheaf. -/
def terminalFreeAbelianSheafIso :
    (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj T ⋙ AddCommGrpCat.free) ≅
      (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  (presheafToSheaf J AddCommGrpCat.{v}).mapIso (terminalFreeAbelianPresheafIso hT)

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- The actual cohomology-presheaf group at a terminal object agrees with
actual sheaf cohomology, in every degree. -/
def sheafCohomologyTerminalEquiv (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    F.H' n T ≃+ F.H n :=
  (((extFunctor n).mapIso ((terminalFreeAbelianSheafIso J hT).symm.op)).app F).addCommGroupIsoToAddEquiv

/-- The terminal comparison commutes with cohomology maps of actual sheaf
morphisms. -/
theorem sheafCohomologyTerminalEquiv_naturality
    {F G : Sheaf J AddCommGrpCat.{v}} (q : F ⟶ G) (n : ℕ) (x : F.H' n T) :
    sheafCohomologyTerminalEquiv J hT G n
      (((Sheaf.cohomologyPresheafFunctor J n).map q).app (op T) x) =
    Sheaf.H.map q n (sheafCohomologyTerminalEquiv J hT F n x) := by
  change (Ext.mk₀ _).comp (x.comp (Ext.mk₀ q) (add_zero n)) (zero_add n) =
    ((Ext.mk₀ _).comp x (zero_add n)).comp (Ext.mk₀ q) (add_zero n)
  exact (Ext.comp_assoc_of_third_deg_zero _ x (Ext.mk₀ q) (zero_add n)).symm

/-- The integer one corresponds to the actual identity generator at the
terminal object. -/
theorem terminalFreeAbelianPresheafIso_inv_one :
    (terminalFreeAbelianPresheafIso hT).inv.app (op T) (ULift.up (1 : ℤ)) =
      FreeAbelianGroup.of (𝟙 T) := by
  change (1 : ℤ) • FreeAbelianGroup.of (hT.from T) = _
  rw [one_smul]
  exact congrArg FreeAbelianGroup.of (hT.hom_ext _ _)

/-- In degree zero the comparison agrees with actual evaluation on the
sheafified identity generator of the represented presheaf. -/
theorem sheafCohomologyTerminalEquiv_equiv₀
    (F : Sheaf J AddCommGrpCat.{v}) (x : F.H' 0 T) :
    Sheaf.H.equiv₀ F hT (sheafCohomologyTerminalEquiv J hT F 0 x) =
      (Ext.addEquiv₀ x).hom.app (op T)
        ((toSheafify J (yoneda.obj T ⋙ AddCommGrpCat.free)).app (op T)
          (FreeAbelianGroup.of (𝟙 T))) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
  change Sheaf.H.equiv₀ F hT
    ((Ext.mk₀ _).comp (Ext.mk₀ a) (zero_add 0)) = _
  rw [Ext.mk₀_comp_mk₀]
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply,
    ← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  change a.hom.app (op T)
    ((terminalFreeAbelianSheafIso J hT).inv.hom.app (op T)
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)))).app (op T) (ULift.up (1 : ℤ)))) = _
  have hn := congrArg (fun z => z.app (op T) (ULift.up (1 : ℤ)))
    (toSheafify_naturality J (terminalFreeAbelianPresheafIso hT).inv).symm
  change (terminalFreeAbelianSheafIso J hT).inv.hom.app (op T)
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)))).app (op T) (ULift.up (1 : ℤ))) =
    (toSheafify J (yoneda.obj T ⋙ AddCommGrpCat.free)).app (op T)
      ((terminalFreeAbelianPresheafIso hT).inv.app (op T) (ULift.up (1 : ℤ))) at hn
  rw [terminalFreeAbelianPresheafIso_inv_one] at hn
  exact congrArg (a.hom.app (op T)) hn

end Normalizer
