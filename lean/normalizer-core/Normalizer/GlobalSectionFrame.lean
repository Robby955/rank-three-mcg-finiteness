import Normalizer.TrivialBundleStalk

/-! Actual evaluation from a finite family of global sections and its
stalk formula. Stalk bijectivity constructs a global sheaf isomorphism. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry Opposite
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

universe u
variable {X : Scheme.{u}} (H : X.Modules)

/-- An actual global section determines its compatible family of
restrictions on all opens. -/
def schemeSectionFamily (s : Γ(H, ⊤)) : H.sections :=
  PresheafOfModules.sectionsMk
    (fun U => H.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s)
    (by
      intro U V f
      change H.presheaf.map f
        (H.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)

/-- The actual sheaf map from the unit sheaf represented by a global section. -/
def schemeSectionHom (s : Γ(H, ⊤)) : SheafOfModules.unit X.ringCatSheaf ⟶ H :=
  H.unitHomEquiv.symm (schemeSectionFamily H s)

/-- The constructed unit-sheaf map sends one to the restricted section. -/
theorem schemeSectionHom_one (s : Γ(H, ⊤)) (U : X.Opens) :
    (schemeSectionHom H s).val.app (op U) (1 : Γ(X, U)) =
      H.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s := by
  have h := congrArg (fun a : H.sections => a.val (op U))
    (H.unitHomEquiv.apply_symm_apply (schemeSectionFamily H s))
  exact h

variable (ι : Type u) [Fintype ι] (s : ι → Γ(H, ⊤))

/-- The actual evaluation sheaf map for a finite family of global sections. -/
def schemeSectionFrameMap : schemeTrivialBundle X ι ⟶ H :=
  biproduct.desc (fun i => schemeSectionHom H (s i))

/-- Each actual standard frame section maps to the prescribed section
restricted to that open. -/
theorem schemeSectionFrameMap_standard (U : X.Opens) (i : ι) :
    (schemeSectionFrameMap H ι s).val.app (op U) (schemeTrivialSection X ι U i) =
      H.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (s i) := by
  have h := congrArg (fun q : SheafOfModules.unit X.ringCatSheaf ⟶ H =>
    q.val.app (op U) (1 : Γ(X, U)))
    (biproduct.ι_desc (fun i => schemeSectionHom H (s i)) i)
  exact h.trans (schemeSectionHom_one H (s i) U)

/-- The actual stalk map is linear combination of the germs of the
given sections in the constructed source coordinates. -/
theorem schemeSectionFrameMap_stalk (x : X) (a : ι → X.presheaf.stalk x) :
    schemeModuleStalkMap (schemeSectionFrameMap H ι s) x
      (schemeTrivialStalkFrame X ι x a) =
        ∑ i, a i • H.presheaf.germ ⊤ x trivial (s i) := by
  change schemeModuleStalkMap (schemeSectionFrameMap H ι s) x
    (∑ i, a i • (schemeTrivialBundle X ι).presheaf.germ ⊤ x trivial
      (schemeTrivialSection X ι ⊤ i)) = _
  simp only [map_sum, map_smul, schemeModuleStalkMap_germ]
  congr 1
  ext i
  have hs : (schemeSectionFrameMap H ι s).app ⊤ (schemeTrivialSection X ι ⊤ i) = s i := by
    change (schemeSectionFrameMap H ι s).val.app (op ⊤) (schemeTrivialSection X ι ⊤ i) = s i
    rw [schemeSectionFrameMap_standard]
    exact ConcreteCategory.congr_hom (H.presheaf.map_id (op ⊤)) (s i)
  exact congrArg (fun v => a i • H.presheaf.germ ⊤ x trivial v) hs

variable {H} {G : X.Modules}

/-- Bijectivity of every actual module-stalk map makes the actual sheaf
morphism an isomorphism. This uses the sheaf stalk criterion and reflection
of isomorphisms by the forgetful functor to sheaves of additive groups. -/
theorem schemeModule_isIso_of_stalk_bijective (q : G ⟶ H)
    (h : ∀ x : X, Function.Bijective (schemeModuleStalkMap q x)) : IsIso q := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (F.map q).hom) :=
    fun x => (ConcreteCategory.isIso_iff_bijective _).mpr (h x)
  have : IsIso (F.map q) := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso (F.map q)
  have : IsIso ((Scheme.Modules.toPresheaf X).map q) :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X).map_isIso (F.map q)
  exact isIso_of_reflects_iso q (Scheme.Modules.toPresheaf X)

end Normalizer
