import Normalizer.SectionDualEvaluation

/-! Actual contravariant transport of internal-Hom dual module sheaves. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}} {L M N : X.Modules}

private theorem dualTransportRingComm (V : X.Opensᵒᵖ)
    (a b : X.ringCatSheaf.obj.obj V) : a * b = b * a :=
  @mul_comm (X.presheaf.obj V) _ a b

private def dualTransportSection (f : L ⟶ M) (V : X.Opens)
    (φ : (schemeDualSheaf M).val.obj (op V)) : (schemeDualSheaf L).val.obj (op V) :=
  moduleHomMk L (SheafOfModules.unit X.ringCatSheaf) dualTransportRingComm V
    (fun W h ↦ (moduleHomEval M (SheafOfModules.unit X.ringCatSheaf)
      dualTransportRingComm V W h φ).comp (f.val.app (op W)).hom) (by
        intro W Z h k s
        change (SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE k).op
          (moduleHomEval M _ dualTransportRingComm V W h φ (f.val.app (op W) s)) = _
        rw [moduleHomEval_natural]
        change moduleHomEval M _ dualTransportRingComm V Z (k.trans h) φ
          (M.val.map (homOfLE k).op (f.val.app (op W) s)) =
            moduleHomEval M _ dualTransportRingComm V Z (k.trans h) φ
              (f.val.app (op Z) (L.val.map (homOfLE k).op s))
        rw [PresheafOfModules.naturality_apply])

/-- Contravariant transport on actual dual sections is precomposition. -/
def schemeDualMapAt (f : L ⟶ M) (V : X.Opens) :
    (schemeDualSheaf M).val.obj (op V) →ₗ[X.ringCatSheaf.obj.obj (op V)]
      (schemeDualSheaf L).val.obj (op V) where
  toFun := dualTransportSection f V
  map_add' φ ψ := by
    apply moduleHom_ext L _ dualTransportRingComm V
    intro W h s
    rfl
  map_smul' a φ := by
    apply moduleHom_ext L _ dualTransportRingComm V
    intro W h s
    rw [moduleHomEval_smul]
    change moduleHomEval M _ dualTransportRingComm V W h (a • φ)
      (f.val.app (op W) s) = _
    rw [moduleHomEval_smul]
    rfl

/-- Canonical pullback of functionals along an actual module-sheaf morphism. -/
def schemeDualMap (f : L ⟶ M) : schemeDualSheaf M ⟶ schemeDualSheaf L where
  val := {
    app := fun V ↦ ModuleCat.ofHom (schemeDualMapAt f V.unop)
    naturality := by
      intro V W g
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply moduleHom_ext L (SheafOfModules.unit X.ringCatSheaf) dualTransportRingComm W.unop
      intro Z h s
      have hg : g = (homOfLE (leOfHom g.unop)).op := Subsingleton.elim _ _
      change moduleHomEval L _ dualTransportRingComm W.unop Z h
        (dualTransportSection f W.unop ((schemeDualSheaf M).val.map g φ)) s =
          moduleHomEval L _ dualTransportRingComm W.unop Z h
            ((moduleHomSheaf L _ dualTransportRingComm).val.map g
              (dualTransportSection f V.unop φ)) s
      rw [hg, moduleHom_restrict]
      change moduleHomEval M _ dualTransportRingComm W.unop Z h
        ((moduleHomSheaf M _ dualTransportRingComm).val.map (homOfLE (leOfHom g.unop)).op φ)
          (f.val.app (op Z) s) =
            moduleHomEval M _ dualTransportRingComm V.unop Z _ φ (f.val.app (op Z) s)
      rw [moduleHom_restrict] }

/-- Exact evaluation formula for contravariant dual transport. -/
theorem schemeDualMap_eval (f : L ⟶ M) (V W : X.Opens) (h : W ≤ V)
    (φ : (schemeDualSheaf M).val.obj (op V)) (s : L.val.obj (op W)) :
    moduleHomEval L (SheafOfModules.unit X.ringCatSheaf) dualTransportRingComm V W h
      ((schemeDualMap f).val.app (op V) φ) s =
        moduleHomEval M (SheafOfModules.unit X.ringCatSheaf) dualTransportRingComm V W h φ
          (f.val.app (op W) s) := rfl

/-- Pulling a functional back along the identity leaves it unchanged. -/
theorem schemeDualMap_id : schemeDualMap (𝟙 L) = 𝟙 (schemeDualSheaf L) := by
  apply (SheafOfModules.forget X.ringCatSheaf).map_injective
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply moduleHom_ext L _ dualTransportRingComm V.unop
  intro W h s
  rfl

/-- Dual transport reverses composition. -/
theorem schemeDualMap_comp (f : L ⟶ M) (g : M ⟶ N) :
    schemeDualMap (f ≫ g) = schemeDualMap g ≫ schemeDualMap f := by
  apply (SheafOfModules.forget X.ringCatSheaf).map_injective
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply moduleHom_ext L _ dualTransportRingComm V.unop
  intro W h s
  change moduleHomEval L _ dualTransportRingComm V.unop W h
    ((schemeDualMap (f ≫ g)).val.app V φ) s =
      moduleHomEval L _ dualTransportRingComm V.unop W h
        ((schemeDualMap f).val.app V ((schemeDualMap g).val.app V φ)) s
  rw [schemeDualMap_eval, schemeDualMap_eval, schemeDualMap_eval]
  rfl

/-- An actual sheaf isomorphism induces the actual contravariant dual isomorphism. -/
def schemeDualIso (e : L ≅ M) : schemeDualSheaf M ≅ schemeDualSheaf L where
  hom := schemeDualMap e.hom
  inv := schemeDualMap e.inv
  hom_inv_id := by rw [← schemeDualMap_comp, e.inv_hom_id, schemeDualMap_id]
  inv_hom_id := by rw [← schemeDualMap_comp, e.hom_inv_id, schemeDualMap_id]

/-- A genuine sheaf morphism to the structure sheaf determines an actual global dual section. -/
def schemeDualSectionOfHom (f : L ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Γ(schemeDualSheaf L, ⊤) :=
  moduleHomMk L (SheafOfModules.unit X.ringCatSheaf) dualTransportRingComm ⊤
    (fun W _ ↦ (f.val.app (op W)).hom) (by
      intro W Z h k s
      exact (PresheafOfModules.naturality_apply f.val (homOfLE k).op s).symm)

/-- The global dual section associated to a morphism evaluates by its actual components. -/
theorem schemeDualSectionOfHom_eval (f : L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (W : X.Opens) (s : L.val.obj (op W)) :
    moduleHomEval L (SheafOfModules.unit X.ringCatSheaf) dualTransportRingComm
      ⊤ W le_top (schemeDualSectionOfHom f) s = f.val.app (op W) s := rfl

/-- Contravariant transport of a morphism's dual section is actual precomposition. -/
theorem schemeDualMap_sectionOfHom (g : L ⟶ M)
    (f : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (schemeDualMap g).val.app (op ⊤) (schemeDualSectionOfHom f) =
      schemeDualSectionOfHom (g ≫ f) := by
  apply moduleHom_ext L _ dualTransportRingComm ⊤
  intro W h s
  rw [schemeDualMap_eval]
  rfl

end Normalizer
