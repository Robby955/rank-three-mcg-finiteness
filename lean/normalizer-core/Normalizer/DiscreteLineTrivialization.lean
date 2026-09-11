import Normalizer.LocalCharacterGluing
import Normalizer.ModuleHomLine
import Normalizer.SheafifyLocalIso
import Normalizer.SectionZeroScheme

/-! A genuine locally trivial line sheaf on a discrete scheme admits a global
trivialization. Singleton opens make overlap compatibility automatic. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u
variable {X : Scheme.{u}} [DiscreteTopology X]

private def singletonChart (x : X) : X.Opens := ⟨{x}, isOpen_discrete _⟩

private theorem singletonChart_cover : iSup (singletonChart (X := X)) = ⊤ := by
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, rfl⟩

omit [DiscreteTopology X] in
private theorem module_empty_section_eq (L : X.Modules)
    (V : X.Opens) (hV : V = ⊥) (a b : L.val.obj (op V)) : a = b := by
  subst V
  let F : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat := ⟨L.val.presheaf, L.isSheaf⟩
  apply F.eq_of_locally_eq' (fun _ : PEmpty.{u+1} => ⊥) ⊥
    (fun i => PEmpty.elim i) (by simp) a b
  intro i
  exact PEmpty.elim i

variable (L : X.Modules)
  (e : ∀ x : X, (SheafOfModules.unit X.ringCatSheaf).over (singletonChart x) ≅
    L.over (singletonChart x))

private def singletonLocalMap (x : X) (V : X.Opens) (h : V ≤ singletonChart x) :
    (SheafOfModules.unit X.ringCatSheaf).val.obj (op V) →ₗ[X.ringCatSheaf.obj.obj (op V)]
      L.val.obj (op V) :=
  (moduleLineFrameAt L (e x) V h).toLinearMap

private theorem singletonLocalMap_natural (x : X) (V W : X.Opens)
    (h : V ≤ W) (k : W ≤ singletonChart x)
    (s : (SheafOfModules.unit X.ringCatSheaf).val.obj (op W)) :
    L.val.restrictₛₗ (homOfLE h).op (singletonLocalMap L e x W k s) =
      singletonLocalMap L e x V (h.trans k)
        ((SheafOfModules.unit X.ringCatSheaf).val.restrictₛₗ (homOfLE h).op s) :=
  moduleLineFrameAt_restrict L (e x) V W h k s

private theorem singletonLocalMap_agreement (x y : X) (V : X.Opens)
    (hx : V ≤ singletonChart x) (hy : V ≤ singletonChart y)
    (s : (SheafOfModules.unit X.ringCatSheaf).val.obj (op V)) :
    singletonLocalMap L e x V hx s = singletonLocalMap L e y V hy s := by
  classical
  by_cases hxy : x = y
  · subst y
    rfl
  · apply module_empty_section_eq L V
    apply le_antisymm _ bot_le
    intro z hz
    exact (hxy ((hx hz).symm.trans (hy hz))).elim

private def singletonChartGluedMap : SheafOfModules.unit X.ringCatSheaf ⟶ L :=
  glueLocalModuleMorphisms _ L singletonChart singletonChart_cover
    (singletonLocalMap L e) (singletonLocalMap_natural L e) (singletonLocalMap_agreement L e)

private theorem singletonChartGluedMap_local (x : X) (V : X.Opens)
    (h : V ≤ singletonChart x) (s : (SheafOfModules.unit X.ringCatSheaf).val.obj (op V)) :
    (singletonChartGluedMap L e).val.app (op V) s = moduleLineFrameAt L (e x) V h s :=
  glueLocalModuleMorphisms_local _ L singletonChart singletonChart_cover
    (singletonLocalMap L e) (singletonLocalMap_natural L e)
    (singletonLocalMap_agreement L e) x V h s

private theorem singletonChartGluedMap_isIso : IsIso (singletonChartGluedMap L e) := by
  let q := singletonChartGluedMap L e
  have hbij (x : X) (V : X.Opens) (h : V ≤ singletonChart x) :
      Function.Bijective (q.val.app (op V)) := by
    have heq : (q.val.app (op V) : _ → _) = moduleLineFrameAt L (e x) V h := by
      funext s
      exact singletonChartGluedMap_local L e x V h s
    rw [heq]
    exact (moduleLineFrameAt L (e x) V h).bijective
  have := modulePresheaf_locallyInjective_of_cover q.val singletonChart singletonChart_cover
    (fun x V h => (hbij x V h).injective)
  have := modulePresheaf_locallySurjective_of_cover q.val singletonChart singletonChart_cover
    (fun x V h => (hbij x V h).surjective)
  let a := (SheafOfModules.toSheaf X.ringCatSheaf).map q
  have hi : Sheaf.IsLocallyInjective a := by
    change PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) q.val
    infer_instance
  have hs : Sheaf.IsLocallySurjective a := by
    change PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) q.val
    infer_instance
  have : IsIso a := (Sheaf.isLocallyBijective_iff_isIso a).mp ⟨hi, hs⟩
  exact isIso_of_reflects_iso q (SheafOfModules.toSheaf X.ringCatSheaf)

/-- Genuine pointwise line charts on a discrete scheme construct an actual global
trivialization. Empty and disconnected schemes and nilpotents are allowed. -/
def discreteLineSheafIso
    (hlocal : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)) :
    SheafOfModules.unit X.ringCatSheaf ≅ L := by
  classical
  choose U hx he using hlocal
  let e : ∀ x : X, (SheafOfModules.unit X.ringCatSheaf).over (singletonChart x) ≅
      L.over (singletonChart x) := fun x =>
    schemeLineChartRestrict (show singletonChart x ≤ U x from by
      intro y hy
      have hyx : y = x := hy
      simpa [hyx] using hx x) (he x).some
  have := singletonChartGluedMap_isIso L e
  exact asIso (singletonChartGluedMap L e)

end Normalizer
