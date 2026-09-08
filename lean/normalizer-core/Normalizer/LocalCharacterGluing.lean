import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.Grp.Limits

/-! Gluing compatible local morphisms of actual sheaves of modules.
The input is a family of linear maps on subopens of a cover, with explicit
restriction and overlap compatibility. A global module morphism is constructed,
not assumed. Application to the normalizer character still requires producing
these local data from the actual line bundle. -/

noncomputable section

namespace Normalizer
open CategoryTheory Opposite TopologicalSpace TopologicalSpace.Opens

universe u
variable {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
  (M N : SheafOfModules.{u} R)

private abbrev moduleRestrict {V W : Opens X} (h : V ≤ W) :=
  M.val.restrictₛₗ (homOfLE h).op

private theorem moduleRestrict_comp {V W T : Opens X} (h : V ≤ W) (k : W ≤ T)
    (s : M.val.obj (op T)) :
    moduleRestrict M h (moduleRestrict M k s) = moduleRestrict M (h.trans k) s := by
  exact (M.val.map_comp_apply (homOfLE k).op (homOfLE h).op s).symm

private def additiveSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨N.val.presheaf, N.isSheaf⟩

variable {ι : Type u} (U : ι → Opens X) (hcover : iSup U = ⊤)
  (localMap : ∀ i (V : Opens X), V ≤ U i →
    M.val.obj (op V) →ₗ[R.obj.obj (op V)] N.val.obj (op V))
  (local_naturality : ∀ i (V W : Opens X) (h : V ≤ W) (k : W ≤ U i)
    (s : M.val.obj (op W)),
    moduleRestrict N h (localMap i W k s) =
      localMap i V (h.trans k) (moduleRestrict M h s))
  (local_agreement : ∀ i j (V : Opens X) (hi : V ≤ U i) (hj : V ≤ U j)
    (s : M.val.obj (op V)), localMap i V hi s = localMap j V hj s)

include hcover in
private theorem patchCover (V : Opens X) : V ≤ iSup (fun i => V ⊓ U i) := by
  rw [← inf_iSup_eq, hcover, inf_top_eq]

private def patchSections (V : Opens X) (s : M.val.obj (op V)) :=
  fun i => localMap i (V ⊓ U i) inf_le_right (moduleRestrict M inf_le_left s)

include local_naturality local_agreement in
private theorem patchCompatible (V : Opens X) (s : M.val.obj (op V)) :
    TopCat.Presheaf.IsCompatible (additiveSheaf N).obj (fun i => V ⊓ U i)
      (patchSections M N U localMap V s) := by
  intro i j
  change moduleRestrict N inf_le_left (patchSections M N U localMap V s i) =
    moduleRestrict N inf_le_right (patchSections M N U localMap V s j)
  dsimp only [patchSections]
  rw [local_naturality, local_naturality, moduleRestrict_comp, moduleRestrict_comp]
  exact local_agreement i j _ _ _ _

private noncomputable def gluedSection (V : Opens X) (s : M.val.obj (op V)) :
    N.val.obj (op V) :=
  Classical.choose ((additiveSheaf N).existsUnique_gluing'
    (fun i => V ⊓ U i) V (fun _ => homOfLE inf_le_left) (patchCover U hcover V)
    (patchSections M N U localMap V s)
    (patchCompatible M N U localMap local_naturality local_agreement V s))

private theorem gluedSection_patch (V : Opens X) (s : M.val.obj (op V)) (i : ι) :
    moduleRestrict N inf_le_left
      (gluedSection M N U hcover localMap local_naturality local_agreement V s) =
      localMap i (V ⊓ U i) inf_le_right (moduleRestrict M inf_le_left s) := by
  have hg := Classical.choose_spec ((additiveSheaf N).existsUnique_gluing'
    (fun i => V ⊓ U i) V (fun _ => homOfLE inf_le_left) (patchCover U hcover V)
    (patchSections M N U localMap V s)
    (patchCompatible M N U localMap local_naturality local_agreement V s))
  exact hg.1 i

local notation "glue" =>
  gluedSection M N U hcover localMap local_naturality local_agreement

private theorem gluedSection_local {V W : Opens X} (h : W ≤ V) (i : ι)
    (hi : W ≤ U i) (s : M.val.obj (op V)) :
    moduleRestrict N h (glue V s) = localMap i W hi (moduleRestrict M h s) := by
  have hg := congrArg (moduleRestrict N (le_inf h hi))
    (gluedSection_patch M N U hcover localMap local_naturality local_agreement V s i)
  rw [moduleRestrict_comp, local_naturality, moduleRestrict_comp] at hg
  exact hg

private theorem gluedSection_add (V : Opens X) (s t : M.val.obj (op V)) :
    glue V (s + t) = glue V s + glue V t := by
  apply (additiveSheaf N).eq_of_locally_eq' (fun i => V ⊓ U i) V
    (fun _ => homOfLE inf_le_left) (patchCover U hcover V)
  intro i
  change moduleRestrict N inf_le_left (glue V (s + t)) =
    moduleRestrict N inf_le_left (glue V s + glue V t)
  simp only [map_add, gluedSection_patch]

private theorem gluedSection_smul (V : Opens X) (r : R.obj.obj (op V))
    (s : M.val.obj (op V)) : glue V (r • s) = r • glue V s := by
  apply (additiveSheaf N).eq_of_locally_eq' (fun i => V ⊓ U i) V
    (fun _ => homOfLE inf_le_left) (patchCover U hcover V)
  intro i
  change moduleRestrict N inf_le_left (glue V (r • s)) =
    moduleRestrict N inf_le_left (r • glue V s)
  simp only [map_smulₛₗ, gluedSection_patch, RingHom.id_apply]

private theorem gluedSection_restrict {V W : Opens X} (h : V ≤ W)
    (s : M.val.obj (op W)) :
    moduleRestrict N h (glue W s) = glue V (moduleRestrict M h s) := by
  apply (additiveSheaf N).eq_of_locally_eq' (fun i => V ⊓ U i) V
    (fun _ => homOfLE inf_le_left) (patchCover U hcover V)
  intro i
  change moduleRestrict N inf_le_left (moduleRestrict N h (glue W s)) =
    moduleRestrict N inf_le_left (glue V (moduleRestrict M h s))
  rw [moduleRestrict_comp, gluedSection_local M N U hcover localMap
    local_naturality local_agreement (inf_le_left.trans h) i inf_le_right,
    gluedSection_patch, moduleRestrict_comp]

/-- Compatible linear maps on the subopens of a cover extend to an actual
morphism of sheaves of modules. -/
noncomputable def glueLocalModuleMorphisms : SheafOfModules.Hom M N where
  val := {
    app := fun V => ModuleCat.ofHom {
      toFun := glue V.unop
      map_add' := gluedSection_add M N U hcover localMap local_naturality local_agreement V.unop
      map_smul' := gluedSection_smul M N U hcover localMap local_naturality local_agreement V.unop }
    naturality := fun {V W} f => by
      ext s
      exact (gluedSection_restrict M N U hcover localMap local_naturality
        local_agreement f.unop.le s).symm }

/-- The glued morphism recovers the prescribed map on every subopen of
every member of the cover. -/
theorem glueLocalModuleMorphisms_local (i : ι) (V : Opens X) (h : V ≤ U i)
    (s : M.val.obj (op V)) :
    (glueLocalModuleMorphisms M N U hcover localMap local_naturality
      local_agreement).val.app (op V) s = localMap i V h s := by
  change glue V s = localMap i V h s
  have hg := gluedSection_local M N U hcover localMap local_naturality
    local_agreement (le_refl V) i h s
  simpa [moduleRestrict, PresheafOfModules.restrictₛₗ] using hg

/-- A morphism agreeing with the prescribed local maps is the constructed
morphism. Equality is checked on an open cover using sheaf separatedness. -/
theorem glueLocalModuleMorphisms_unique (f : SheafOfModules.Hom M N)
    (hf : ∀ i (V : Opens X) (h : V ≤ U i) (s : M.val.obj (op V)),
      f.val.app (op V) s = localMap i V h s) :
    f = glueLocalModuleMorphisms M N U hcover localMap local_naturality
      local_agreement := by
  apply SheafOfModules.Hom.ext
  ext V s
  apply (additiveSheaf N).eq_of_locally_eq' (fun i => V.unop ⊓ U i) V.unop
    (fun _ => homOfLE inf_le_left) (patchCover U hcover V.unop)
  intro i
  change moduleRestrict N inf_le_left (f.val.app V s) =
    moduleRestrict N inf_le_left (glue V.unop s)
  rw [gluedSection_patch]
  exact (PresheafOfModules.naturality_apply f.val (homOfLE inf_le_left).op s).symm.trans
    (hf i _ inf_le_right _)

include hcover local_naturality local_agreement in
/-- Local morphisms with restriction and overlap compatibility have exactly
one extension to a morphism of the actual sheaves of modules. -/
theorem existsUnique_localModuleMorphism :
    ∃! f : SheafOfModules.Hom M N,
      ∀ i (V : Opens X) (h : V ≤ U i) (s : M.val.obj (op V)),
        f.val.app (op V) s = localMap i V h s := by
  refine ⟨glueLocalModuleMorphisms M N U hcover localMap local_naturality local_agreement,
    glueLocalModuleMorphisms_local M N U hcover localMap local_naturality local_agreement, ?_⟩
  intro f hf
  exact glueLocalModuleMorphisms_unique M N U hcover localMap local_naturality
    local_agreement f hf

end Normalizer
