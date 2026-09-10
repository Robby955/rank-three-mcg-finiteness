import Normalizer.SheafStalkMap
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Independence of actual free-sheaf generators at the generic point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u
variable {X : Scheme.{u}} {E H : X.Modules}

/-- A monomorphism of scheme module sheaves is injective on actual stalks. -/
theorem schemeModuleStalkMap_injective (f : E ⟶ H) [Mono f] (x : X) :
    Function.Injective (schemeModuleStalkMap f x) := by
  change Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    f.mapPresheaf)
  apply TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
  intro U
  have : Mono f.mapPresheaf := (Scheme.Modules.toPresheaf X).map_mono f
  exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp
    ((NatTrans.mono_iff_mono_app f.mapPresheaf).mp inferInstance (op U))

/-- The canonical global generator of a free sheaf, evaluated on the whole scheme. -/
def freeSheafGenerator {I : Type u} (i : I) :
    Γ((SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules), ⊤) :=
  (SheafOfModules.freeSection (R := X.ringCatSheaf) i).val (op ⊤)

/-- The coordinate projection from an actual free sheaf to the structure sheaf. -/
def freeSheafCoordinate {I : Type u} [DecidableEq I] (i : I) :
    SheafOfModules.free (R := X.ringCatSheaf) I ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.freeHomEquiv _).symm (fun j ↦
    (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv
      (if j = i then 𝟙 _ else 0))

/-- The coordinate maps evaluate the canonical generators by the Kronecker rule. -/
theorem freeSheafCoordinate_generator {I : Type u} [DecidableEq I] (i j : I) :
    (freeSheafCoordinate (X := X) i).val.app (op ⊤) (freeSheafGenerator j) =
      if j = i then (1 : Γ(X, ⊤)) else 0 := by
  have h := congrArg (fun s ↦ s.val (op ⊤))
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (R := X.ringCatSheaf)
      (fun j ↦ (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv
        (if j = i then 𝟙 _ else 0)) j)
  split_ifs with hji
  · simpa [freeSheafCoordinate, freeSheafGenerator, hji,
      SheafOfModules.unitHomEquiv_apply_coe] using h
  · simpa [freeSheafCoordinate, freeSheafGenerator, hji,
      SheafOfModules.unitHomEquiv_apply_coe,
      show (0 : SheafOfModules.unit X.ringCatSheaf ⟶
        SheafOfModules.unit X.ringCatSheaf).val = 0 from rfl] using h

/-- The germ of the unit section in the actual structure-module stalk is nonzero. -/
theorem unitSheaf_germ_one_ne_zero (x : X) :
    (Scheme.Modules.presheaf (X := X) (SheafOfModules.unit X.ringCatSheaf)).germ ⊤ x
      (by trivial) (1 : Γ(X, ⊤)) ≠ 0 := by
  intro h
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have h' : O.presheaf.germ ⊤ x (by trivial) (1 : Γ(X, ⊤)) =
      O.presheaf.germ ⊤ x (by trivial) (0 : Γ(X, ⊤)) := by
    simpa using h
  obtain ⟨U, hx, i, j, hij⟩ := O.presheaf.germ_eq x (by trivial) (by trivial)
    (1 : Γ(X, ⊤)) (0 : Γ(X, ⊤)) h'
  have he : (1 : Γ(X, U)) = 0 := by
    change X.presheaf.map i.op (1 : Γ(X, ⊤)) =
      X.presheaf.map j.op (0 : Γ(X, ⊤)) at hij
    simpa using hij
  have hs := congrArg (X.presheaf.germ U x hx) he
  simp at hs

/-- The actual generic germs of the canonical free-sheaf generators. -/
def freeSheafGenericGenerators [IsIntegral X] {I : Type u} (i : I) :
    (Scheme.Modules.presheaf (X := X) (SheafOfModules.free (R := X.ringCatSheaf) I)).stalk
      (genericPoint X) :=
  (Scheme.Modules.presheaf (X := X) (SheafOfModules.free (R := X.ringCatSheaf) I)).germ
    ⊤ (genericPoint X) (by trivial) (freeSheafGenerator i)

/-- A finite trivial sheaf has independent canonical generic germs over the
actual function field. Independence follows from the coordinate projections. -/
theorem freeSheafGenericGenerators_linearIndependent [IsIntegral X]
    (I : Type u) [Fintype I] :
    LinearIndependent X.functionField (freeSheafGenericGenerators (X := X) (I := I)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let p := schemeModuleStalkMap (X := X) (freeSheafCoordinate i) (genericPoint X)
  have hp (j : I) : p (freeSheafGenericGenerators j) =
      if j = i then (Scheme.Modules.presheaf (X := X)
        (SheafOfModules.unit X.ringCatSheaf)).germ ⊤ (genericPoint X)
          (by trivial) (1 : Γ(X, ⊤)) else 0 := by
    dsimp [p, freeSheafGenericGenerators]
    rw [schemeModuleStalkMap_germ]
    change (Scheme.Modules.presheaf (X := X) (SheafOfModules.unit X.ringCatSheaf)).germ
      ⊤ (genericPoint X) (by trivial)
      ((freeSheafCoordinate i).val.app (op ⊤) (freeSheafGenerator j)) = _
    rw [freeSheafCoordinate_generator]
    split_ifs <;> simp
  have he := congrArg p hc
  simp only [map_sum, map_smul, hp, smul_ite, smul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, map_zero] at he
  exact (smul_eq_zero.mp he).resolve_right (unitSheaf_germ_one_ne_zero (genericPoint X))

/-- A genuine inclusion of a finite trivial sheaf produces independent germs
of its global generators in the actual target generic stalk. -/
theorem freeSheaf_mono_generic_linearIndependent [IsIntegral X]
    (I : Type u) [Fintype I]
    (f : (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) ⟶ E) [Mono f] :
    LinearIndependent X.functionField (fun i : I ↦
      E.presheaf.germ ⊤ (genericPoint X) (by trivial) (f.val.app (op ⊤) (freeSheafGenerator i))) := by
  have h : LinearIndependent X.functionField
      ((schemeModuleStalkMap f (genericPoint X)) ∘
        freeSheafGenericGenerators (X := X) (I := I)) :=
    (freeSheafGenericGenerators_linearIndependent (X := X) I).map'
    (schemeModuleStalkMap f (genericPoint X))
    (LinearMap.ker_eq_bot.mpr (schemeModuleStalkMap_injective f (genericPoint X)))
  convert h using 1
  funext i
  exact (schemeModuleStalkMap_germ f (genericPoint X) ⊤ (by trivial)
    (freeSheafGenerator i)).symm

/-- The function-field span of the global generators of a genuine trivial
subsheaf has exactly its prescribed rank. No independence over the function
field is supplied as a hypothesis. -/
theorem freeSheaf_mono_generic_span_finrank [IsIntegral X]
    (I : Type u) [Fintype I]
    (f : (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) ⟶ E) [Mono f] :
    Module.finrank X.functionField (Submodule.span X.functionField (Set.range
      (fun i : I ↦ E.presheaf.germ ⊤ (genericPoint X) (by trivial)
        (f.val.app (op ⊤) (freeSheafGenerator i))))) = Fintype.card I :=
  finrank_span_eq_card (freeSheaf_mono_generic_linearIndependent I f)

end Normalizer
