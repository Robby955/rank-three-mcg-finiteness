import Normalizer.DualTransport
import Normalizer.SheafifyLocalIso

/-! Canonical biduality for an actual locally trivial line module sheaf. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
variable {X : Scheme.{u}} (L : X.Modules)

private theorem bidualRingComm (V : X.Opensᵒᵖ)
    (a b : X.ringCatSheaf.obj.obj V) : a * b = b * a :=
  @mul_comm (X.presheaf.obj V) _ a b

private def bidualEvalLocal (V W : X.Opens) (h : W ≤ V) (s : Γ(L, V)) :
    (schemeDualSheaf L).val.obj (op W) →ₗ[Γ(X, W)] Γ(X, W) where
  toFun φ := moduleHomEval L (SheafOfModules.unit X.ringCatSheaf) bidualRingComm
    W W le_rfl φ (L.presheaf.map (homOfLE h).op s)
  map_add' _ _ := rfl
  map_smul' a φ := by
    rw [moduleHomEval_smul]
    change X.presheaf.map (𝟙 (op W)) a * _ = a * _
    rw [X.presheaf.map_id]
    rfl

private def bidualSection (V : X.Opens) (s : Γ(L, V)) :
    (schemeDualSheaf (schemeDualSheaf L)).val.obj (op V) :=
  moduleHomMk (schemeDualSheaf L) (SheafOfModules.unit X.ringCatSheaf)
    bidualRingComm V (fun W h ↦ bidualEvalLocal L V W h s) (by
      intro W Z h k φ
      change X.presheaf.map (homOfLE k).op
        (moduleHomEval L (SheafOfModules.unit X.ringCatSheaf) bidualRingComm
          W W le_rfl φ (L.presheaf.map (homOfLE h).op s)) = _
      have hn := moduleHomEval_natural L (SheafOfModules.unit X.ringCatSheaf)
        bidualRingComm W W Z le_rfl k φ (L.presheaf.map (homOfLE h).op s)
      change _ = moduleHomEval L (SheafOfModules.unit X.ringCatSheaf) bidualRingComm
        Z Z le_rfl ((moduleHomSheaf L _ bidualRingComm).val.map (homOfLE k).op φ)
          (L.presheaf.map (homOfLE (k.trans h)).op s)
      rw [moduleHom_restrict]
      change X.presheaf.map (homOfLE k).op _ = _ at hn
      rw [hn]
      congr 1
      exact (L.presheaf.map_comp_apply (homOfLE h).op (homOfLE k).op s).symm)

/-- The canonical bidual map on actual sections. -/
def schemeBidualAt (V : X.Opens) :
    L.val.obj (op V) →ₗ[X.ringCatSheaf.obj.obj (op V)] (schemeDualSheaf (schemeDualSheaf L)).val.obj (op V) where
  toFun := bidualSection L V
  map_add' s t := by
    apply moduleHom_ext (schemeDualSheaf L) (SheafOfModules.unit X.ringCatSheaf) bidualRingComm V
    intro W h φ
    change moduleHomEval L _ bidualRingComm W W le_rfl φ
      (L.presheaf.map (homOfLE h).op (s + t)) =
        moduleHomEval L _ bidualRingComm W W le_rfl φ
          (L.presheaf.map (homOfLE h).op s) +
        moduleHomEval L _ bidualRingComm W W le_rfl φ
          (L.presheaf.map (homOfLE h).op t)
    rw [map_add, map_add]
  map_smul' a s := by
    apply moduleHom_ext (schemeDualSheaf L) (SheafOfModules.unit X.ringCatSheaf) bidualRingComm V
    intro W h φ
    rw [moduleHomEval_smul]
    change moduleHomEval L _ bidualRingComm W W le_rfl φ
      (L.presheaf.map (homOfLE h).op (a • s)) = _
    rw [show L.presheaf.map (homOfLE h).op (a • s) =
      X.presheaf.map (homOfLE h).op a • L.presheaf.map (homOfLE h).op s from
        L.val.map_smul _ _ _, map_smul]
    rfl

private def moduleSheafMapFromSections (A B : X.Modules)
    (app : ∀ V : X.Opensᵒᵖ, A.val.obj V →ₗ[X.ringCatSheaf.obj.obj V] B.val.obj V)
    (nat : ∀ (V W : X.Opensᵒᵖ) (f : V ⟶ W) s,
      app W (A.val.map f s) = B.val.map f (app V s)) : A ⟶ B where
  val := {
    app := fun V ↦ ModuleCat.ofHom (app V)
    naturality := by
      intro V W f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact nat V W f }

set_option backward.isDefEq.respectTransparency true in
/-- The canonical bidual sheaf morphism is evaluation of local functionals. -/
def schemeBidualMap : L ⟶ schemeDualSheaf (schemeDualSheaf L) :=
  moduleSheafMapFromSections L (schemeDualSheaf (schemeDualSheaf L))
    (fun V ↦ schemeBidualAt L V.unop) (by
      intro V W f s
      apply moduleHom_ext (schemeDualSheaf L) (SheafOfModules.unit X.ringCatSheaf) bidualRingComm W.unop
      intro Z h φ
      change moduleHomEval (schemeDualSheaf L) (SheafOfModules.unit X.ringCatSheaf) bidualRingComm W.unop Z h
        (bidualSection L W.unop (L.presheaf.map f s)) φ =
          moduleHomEval (schemeDualSheaf L) (SheafOfModules.unit X.ringCatSheaf) bidualRingComm W.unop Z h
            ((moduleHomSheaf (schemeDualSheaf L) (SheafOfModules.unit X.ringCatSheaf) bidualRingComm).val.map f
              (bidualSection L V.unop s)) φ
      have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
      rw [hf]
      erw [moduleHom_restrict (schemeDualSheaf L)
        (SheafOfModules.unit X.ringCatSheaf) bidualRingComm V.unop W.unop Z
          (leOfHom f.unop) h (bidualSection L V.unop s)]
      change moduleHomEval L _ bidualRingComm Z Z le_rfl φ
        (L.presheaf.map (homOfLE h).op (L.presheaf.map _ s)) =
          moduleHomEval L _ bidualRingComm Z Z le_rfl φ (L.presheaf.map _ s)
      congr 1
      exact (L.presheaf.map_comp_apply (homOfLE (leOfHom f.unop)).op
        (homOfLE h).op s).symm)

/-- Exact evaluation formula for the canonical bidual image, on every smaller open. -/
theorem schemeBidualMap_eval (V W : X.Opens) (h : W ≤ V) (s : Γ(L, V))
    (φ : (schemeDualSheaf L).val.obj (op W)) :
    moduleHomEval (schemeDualSheaf L) (SheafOfModules.unit X.ringCatSheaf)
      bidualRingComm V W h ((schemeBidualMap L).val.app (op V) s) φ =
        moduleHomEval L (SheafOfModules.unit X.ringCatSheaf) bidualRingComm
          W W le_rfl φ (L.presheaf.map (homOfLE h).op s) := rfl

/-- In an actual line chart the bidual coordinate is precisely the original coordinate. -/
theorem schemeBidualMap_coordinate {U : X.Opens}
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (V : X.Opens) (h : V ≤ U) (s : Γ(L, V)) :
    schemeDualFrameCoordinate (schemeDualSheaf L) (schemeDualLineFrameIso L e) V h
      ((schemeBidualMap L).val.app (op V) s) =
        (moduleLineFrameAt L e V h).symm s := by
  change moduleHomEval (schemeDualSheaf L) (SheafOfModules.unit X.ringCatSheaf) bidualRingComm V V le_rfl
    ((schemeBidualMap L).val.app (op V) s)
      (moduleLineFrameAt (schemeDualSheaf L) (schemeDualLineFrameIso L e) V h 1) = _
  rw [schemeBidualMap_eval, moduleHom_eval_frame L _ bidualRingComm e V V h le_rfl]
  change HMul.hMul (α := Γ(X, V)) (β := Γ(X, V)) (γ := Γ(X, V))
    ((moduleLineFrameAt L e V h).symm (L.presheaf.map (𝟙 (op V)) s))
    (X.presheaf.map (𝟙 (op V))
    (schemeDualFrameCoordinate L e V h
      (moduleLineFrameAt (schemeDualSheaf L) (schemeDualLineFrameIso L e) V h 1))) = _
  rw [schemeDualLineFrameIso_coordinate]
  rw [map_one]
  change (moduleLineFrameAt L e V h).symm (L.presheaf.map (𝟙 (op V)) s) * 1 = _
  rw [L.presheaf.map_id]
  exact mul_one _

/-- The canonical bidual map is bijective on every subopen of a genuine line chart. -/
theorem schemeBidualMap_bijective_of_chart {U : X.Opens}
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (V : X.Opens) (h : V ≤ U) :
    Function.Bijective ((schemeBidualMap L).val.app (op V)) := by
  let c := schemeDualFrameCoordinate (schemeDualSheaf L) (schemeDualLineFrameIso L e) V h
  let d := (moduleLineFrameAt L e V h).symm
  have heq : c ∘ (schemeBidualMap L).val.app (op V) = d := by
    funext s
    exact schemeBidualMap_coordinate L e V h s
  have hb : Function.Bijective (c ∘ (schemeBidualMap L).val.app (op V)) := by
    rw [heq]
    exact d.bijective
  exact (Function.Bijective.of_comp_iff' c.bijective _).mp hb

private theorem moduleSheaf_isIso_of_cover {Y : TopCat.{u}}
    {R : TopCat.Sheaf RingCat.{u} Y} {A B : SheafOfModules.{u} R}
    (f : A ⟶ B) {ι : Type u} (U : ι → Opens Y) (hcover : iSup U = ⊤)
    (hbij : ∀ i V, V ≤ U i → Function.Bijective (f.val.app (op V))) : IsIso f := by
  have := modulePresheaf_locallyInjective_of_cover f.val U hcover
    (fun i V h ↦ (hbij i V h).injective)
  have := modulePresheaf_locallySurjective_of_cover f.val U hcover
    (fun i V h ↦ (hbij i V h).surjective)
  let q := (SheafOfModules.toSheaf R).map f
  have hi : Sheaf.IsLocallyInjective q := by
    change PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology Y) f.val
    infer_instance
  have hs : Sheaf.IsLocallySurjective q := by
    change PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology Y) f.val
    infer_instance
  have : IsIso q := (Sheaf.isLocallyBijective_iff_isIso q).mp ⟨hi, hs⟩
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf R)

/-- Genuine line charts covering the scheme prove canonical biduality globally. -/
theorem schemeBidualMap_isIso {ι : Type u} (U : ι → X.Opens)
    (hcover : iSup U = ⊤)
    (triv : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅ L.over (U i)) :
    IsIso (schemeBidualMap L) :=
  moduleSheaf_isIso_of_cover (schemeBidualMap L) U hcover
    (fun i V h ↦ schemeBidualMap_bijective_of_chart L (triv i) V h)

/-- The canonical bidual equivalence of an actually locally trivial line sheaf. -/
def schemeLineBidualIso {ι : Type u} (U : ι → X.Opens)
    (hcover : iSup U = ⊤)
    (triv : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅ L.over (U i)) :
    L ≅ schemeDualSheaf (schemeDualSheaf L) := by
  have := schemeBidualMap_isIso L U hcover triv
  exact asIso (schemeBidualMap L)

/-- The bidual equivalence uses the canonical map, independent of the covering choice. -/
theorem schemeLineBidualIso_hom {ι : Type u} (U : ι → X.Opens)
    (hcover : iSup U = ⊤)
    (triv : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅ L.over (U i)) :
    (schemeLineBidualIso L U hcover triv).hom = schemeBidualMap L := rfl

/-- The bidual image of a global section is the actual dual section of its evaluation morphism. -/
theorem schemeBidualMap_globalSection (s : Γ(L, ⊤)) :
    (schemeBidualMap L).val.app (op ⊤) s =
      schemeDualSectionOfHom (schemeSectionDualEvaluation L s) := by
  apply moduleHom_ext (schemeDualSheaf L) (SheafOfModules.unit X.ringCatSheaf)
    bidualRingComm ⊤
  intro W h φ
  rw [schemeBidualMap_eval]
  rfl

end Normalizer
